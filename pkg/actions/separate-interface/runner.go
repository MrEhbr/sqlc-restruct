package separateinterface

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/build"
	"go/format"
	"go/parser"
	"go/token"
	"os"
	"path"
	"strings"

	"golang.org/x/exp/slices"
	"golang.org/x/tools/imports"

	"github.com/mpyw/sqlc-restruct/pkg/internal/astutil"
)

type runner struct {
	input                   ActionInput
	fset                    *token.FileSet
	exportedSymbolsInModels []string
	extraDecls              []ast.Decl
	extraIfaces             map[string]ast.Decl
}

func (r *runner) Run() error {
	pkg, err := build.Import(".", r.input.ImplDir, build.IgnoreVendor)
	if err != nil {
		return fmt.Errorf("runner.Run() failed: %w", err)
	}
	f, err := parser.ParseFile(r.fset, path.Join(r.input.ImplDir, r.input.ModelsFileName), nil, parser.ParseComments)
	if err != nil {
		return fmt.Errorf("runner.Run() failed: %w", err)
	}
	r.exportedSymbolsInModels = astutil.SymbolNameFromTypeOrValueDecls(astutil.ExportedIndividualTypeOrValueDecls(f.Decls...)...)

	var newModelsContent []byte
	var newQuerierContent []byte
	var newQueriesContents map[string][]byte

	for _, filename := range pkg.GoFiles {
		var err error
		if filename == r.input.ModelsFileName {
			if newModelsContent, err = r.newModelsContent(); err != nil {
				return err
			}
			newModelsContent, err = imports.Process("", newModelsContent, nil)
			if err != nil {
				return err
			}
			continue
		}
		if strings.HasSuffix(filename, r.input.ImplSQLSuffix) {
			var newQueriesContent []byte
			if newQueriesContent, err = r.newQueriesContent(filename); err != nil {
				return err
			}
			newQueriesContent, err = imports.Process("", newQueriesContent, nil)
			if err != nil {
				return err
			}

			if newQueriesContents == nil {
				newQueriesContents = make(map[string][]byte)
			}
			newQueriesContents[filename] = newQueriesContent
			continue
		}

		if filename == r.input.CopyFromFileName {
			var newQueriesContent []byte
			if newQueriesContent, err = r.newQueriesContent(filename); err != nil {
				return err
			}
			newQueriesContent, err = imports.Process("", newQueriesContent, nil)
			if err != nil {
				return err
			}

			if newQueriesContents == nil {
				newQueriesContents = make(map[string][]byte)
			}
			newQueriesContents[filename] = newQueriesContent
			continue
		}

		if filename == r.input.BatchFileName {
			var newQueriesContent []byte
			if newQueriesContent, err = r.newBatchContent(filename); err != nil {
				return err
			}
			newQueriesContent, err = imports.Process("", newQueriesContent, nil)
			if err != nil {
				return err
			}

			if newQueriesContents == nil {
				newQueriesContents = make(map[string][]byte)
			}
			newQueriesContents[filename] = newQueriesContent
			continue
		}

		if filename == r.input.QuerierFileName {
			if newQuerierContent, err = r.newQuerierContent(); err != nil {
				return err
			}
			newQuerierContent, err = imports.Process("", newQuerierContent, nil)
			if err != nil {
				return err
			}
			continue
		}
	}

	if newModelsContent != nil {
		_ = os.Remove(path.Join(r.input.ModelsDir, r.input.ModelsFileName))
		if err := os.WriteFile(path.Join(r.input.ModelsDir, r.input.ModelsFileName), newModelsContent, 0o644); err != nil {
			return fmt.Errorf("runner.Run() failed: %w", err)
		}
		_ = os.Remove(path.Join(r.input.ImplDir, r.input.ModelsFileName))
	}
	if newQuerierContent != nil {
		_ = os.Remove(path.Join(r.input.IfaceDir, r.input.QuerierFileName))
		if err := os.WriteFile(path.Join(r.input.IfaceDir, r.input.QuerierFileName), newQuerierContent, 0o644); err != nil {
			return fmt.Errorf("runner.Run() failed: %w", err)
		}
		_ = os.Remove(path.Join(r.input.ImplDir, r.input.QuerierFileName))
	}
	for filename, content := range newQueriesContents {
		_ = os.Remove(path.Join(r.input.ImplDir, filename))
		if err := os.WriteFile(path.Join(r.input.ImplDir, filename), content, 0o644); err != nil {
			return fmt.Errorf("runner.Run() failed: %w", err)
		}
	}

	return nil
}

func (r *runner) intoBytes(node any) ([]byte, error) {
	buf := &bytes.Buffer{}
	if err := format.Node(buf, r.fset, node); err != nil {
		return nil, err
	}
	return buf.Bytes(), nil
}

func (r *runner) newModelsContent() ([]byte, error) {
	f, err := parser.ParseFile(r.fset, path.Join(r.input.ImplDir, r.input.ModelsFileName), nil, parser.ParseComments)
	if err != nil {
		return nil, fmt.Errorf("runner.newModelsContent() failed: %w", err)
	}

	// Change package name of "models" file
	f.Name = ast.NewIdent(r.input.ModelsPkgName)

	byt, err := r.intoBytes(f)
	if err != nil {
		return nil, fmt.Errorf("runner.newModelsContent() failed: %w", err)
	}
	return byt, nil
}

func (r *runner) newQuerierContent() ([]byte, error) {
	f, err := parser.ParseFile(r.fset, path.Join(r.input.ImplDir, r.input.QuerierFileName), nil, parser.ParseComments)
	if err != nil {
		return nil, fmt.Errorf("runner.newQuerierContent() failed: %w", err)
	}

	// Change package name of "querier" file
	f.Name = ast.NewIdent(r.input.IfacePkgName)

	// Prepend import statement of ModelsPkgURL
	if r.input.ModelsPkgURL != r.input.IfacePkgURL {
		f.Decls = append(append(([]ast.Decl)(nil), &ast.GenDecl{
			Tok: token.IMPORT,
			Specs: []ast.Spec{&ast.ImportSpec{
				Path: &ast.BasicLit{
					Kind:  token.STRING,
					Value: fmt.Sprintf("%#v", r.input.ModelsPkgURL),
				},
			}},
		}), f.Decls...)
	}

	// Remove top level constraint: var _ Querier = (*Querier)(nil)
	for i, decl := range f.Decls {
		if decl, ok := decl.(*ast.GenDecl); ok && decl.Tok == token.VAR {
			for _, spec := range decl.Specs {
				if spec := spec.(*ast.ValueSpec); len(spec.Names) > 0 && spec.Names[0].Name == "_" {
					f.Decls = append(f.Decls[:i], f.Decls[i+1:]...)
					break
				}
			}
		}
	}

	dirEntries, err := os.ReadDir(r.input.ImplDir)
	if err != nil {
		return nil, fmt.Errorf("runner.newQuerierContent() failed: %w", err)
	}

	for _, dirEntry := range dirEntries {
		if !strings.HasSuffix(dirEntry.Name(), r.input.ImplSQLSuffix) {
			continue
		}

		ff, err := parser.ParseFile(r.fset, path.Join(r.input.ImplDir, dirEntry.Name()), nil, parser.ParseComments)
		if err != nil {
			return nil, fmt.Errorf("runner.newQuerierContent() failed: %w", err)
		}

		// Copy top level type definitions: query.*.sql.go -> querier.gen.go
		f.Decls = append(
			append(([]ast.Decl)(nil), f.Decls...),
			astutil.ExportedIndividualTypeOrValueDecls(ff.Decls...)...,
		)
	}
	if len(r.extraDecls) > 0 {
		f.Decls = append(f.Decls, r.extraDecls...)
	}

	if len(r.extraIfaces) > 0 {
		// find interface methods that have results as star expresion and removes star expression
		for name, iface := range r.extraIfaces {
			ast.Inspect(f, func(n ast.Node) bool {
				if fn, ok := n.(*ast.InterfaceType); ok {
					for _, m := range fn.Methods.List {
						if ft, ok := m.Type.(*ast.FuncType); ok {
							if ft.Results == nil {
								continue
							}
							for _, p := range ft.Results.List {
								if se, ok := p.Type.(*ast.StarExpr); ok {
									if sei, ok := se.X.(*ast.Ident); ok && sei.Name == name {
										p.Type = sei
									}
								}
							}
						}
					}
				}
				return true
			})

			f.Decls = append(f.Decls, iface)
		}
	}

	// Qualify exported references
	if r.input.ModelsPkgURL != r.input.IfacePkgURL {
		ast.Walk(
			astutil.NewExportedExprIdentUpdater(func(ident *ast.Ident) ast.Expr {
				if slices.Contains(r.exportedSymbolsInModels, ident.Name) {
					return &ast.SelectorExpr{
						X:   ast.NewIdent(r.input.ModelsPkgName),
						Sel: ident,
					}
				}
				return nil
			}, false),
			f,
		)
	}

	byt, err := r.intoBytes(f)
	if err != nil {
		return nil, fmt.Errorf("runner.newQuerierContent() failed: %w", err)
	}
	return byt, nil
}

func (r *runner) newQueriesContent(filename string) ([]byte, error) {
	f, err := parser.ParseFile(r.fset, path.Join(r.input.ImplDir, filename), nil, parser.ParseComments)
	if err != nil {
		return nil, fmt.Errorf("runner.newQueriesContent() failed: %w", err)
	}

	// Prepend import statement of IfacePkgURL
	f.Decls = append(append(([]ast.Decl)(nil), &ast.GenDecl{
		Tok: token.IMPORT,
		Specs: []ast.Spec{&ast.ImportSpec{
			Path: &ast.BasicLit{
				Kind:  token.STRING,
				Value: fmt.Sprintf("%#v", r.input.IfacePkgURL),
			},
		}},
	}), f.Decls...)

	// Prepend import statement of ModelsPkgURL
	if r.input.ModelsPkgURL != r.input.IfacePkgURL {
		f.Decls = append(append(([]ast.Decl)(nil), &ast.GenDecl{
			Tok: token.IMPORT,
			Specs: []ast.Spec{&ast.ImportSpec{
				Path: &ast.BasicLit{
					Kind:  token.STRING,
					Value: fmt.Sprintf("%#v", r.input.ModelsPkgURL),
				},
			}},
		}), f.Decls...)
	}

	// Qualify exported references
	ast.Walk(
		astutil.NewExportedExprIdentUpdater(func(ident *ast.Ident) ast.Expr {
			pkgName := r.input.IfacePkgName
			if slices.Contains(r.exportedSymbolsInModels, ident.Name) {
				pkgName = r.input.ModelsPkgName
			}
			return &ast.SelectorExpr{
				X:   ast.NewIdent(pkgName),
				Sel: ident,
			}
		}, false),
		f,
	)

	// Add top level constraint: var _ iface.Querier = (*Querier)(nil)
	f.Decls = append(f.Decls, &ast.GenDecl{
		Tok: token.VAR,
		Specs: []ast.Spec{
			&ast.ValueSpec{
				Names: []*ast.Ident{
					{Name: "_"},
				},
				Type: &ast.SelectorExpr{
					X:   &ast.Ident{Name: r.input.IfacePkgName},
					Sel: &ast.Ident{Name: "Querier"},
				},
				Values: []ast.Expr{
					&ast.CallExpr{
						Fun:  &ast.StarExpr{X: &ast.Ident{Name: "Queries"}},
						Args: []ast.Expr{&ast.Ident{Name: "nil"}},
					},
				},
			},
		},
	})

	// Drop top level type definitions which has been already moved: query.*.sql.go -> querier.gen.go
	f.Decls = append(
		append(
			astutil.ExtractImportDecls(f.Decls...),
			astutil.UnexportedIndividualTypeOrValueDecls(f.Decls...)...,
		),
		astutil.FuncDecls(f.Decls...)...,
	)

	byt, err := r.intoBytes(f)
	if err != nil {
		return nil, fmt.Errorf("runner.newQueriesContent() failed: %w", err)
	}
	return byt, nil
}

func (r *runner) newBatchContent(filename string) ([]byte, error) {
	f, err := parser.ParseFile(r.fset, path.Join(r.input.ImplDir, filename), nil, parser.ParseComments)
	if err != nil {
		return nil, fmt.Errorf("runner.newQueriesContent() failed: %w", err)
	}

	// Prepend import statement of IfacePkgURL
	f.Decls = append(append(([]ast.Decl)(nil), &ast.GenDecl{
		Tok: token.IMPORT,
		Specs: []ast.Spec{&ast.ImportSpec{
			Path: &ast.BasicLit{
				Kind:  token.STRING,
				Value: fmt.Sprintf("%#v", r.input.IfacePkgURL),
			},
		}},
	}), f.Decls...)

	// Prepend import statement of ModelsPkgURL
	if r.input.ModelsPkgURL != r.input.IfacePkgURL {
		f.Decls = append(append(([]ast.Decl)(nil), &ast.GenDecl{
			Tok: token.IMPORT,
			Specs: []ast.Spec{&ast.ImportSpec{
				Path: &ast.BasicLit{
					Kind:  token.STRING,
					Value: fmt.Sprintf("%#v", r.input.ModelsPkgURL),
				},
			}},
		}), f.Decls...)
	}

	// Qualify exported references
	ast.Walk(
		astutil.NewExportedExprIdentUpdater(func(ident *ast.Ident) ast.Expr {
			pkgName := r.input.IfacePkgName
			if slices.Contains(r.exportedSymbolsInModels, ident.Name) {
				pkgName = r.input.ModelsPkgName
			}
			return &ast.SelectorExpr{
				X:   ast.NewIdent(pkgName),
				Sel: ident,
			}
		}, true),
		f,
	)

	// Drop top level type definitions which has been already moved: query.*.sql.go -> querier.gen.go
	// Copy f.Decls to avoid modifying the original slice
	r.extraDecls = append(r.extraDecls, astutil.ExportedBatchParamsIndividualTypeOrValueDecls(f.Decls...)...)
	returns := astutil.ExportedResultsIndividualTypeOrValueDecls(f.Decls...)
	for _, ret := range returns {
		structName := astutil.StructNameFromDecl(ret)
		if structName != "" {
			iface := astutil.ExtractInterfaceFromStruct(f, structName)
			if iface != nil {
				r.extraIfaces[structName] = iface
			}
		}
	}
	decls := make([]ast.Decl, 0, len(f.Decls))
	decls = append(decls, astutil.ExtractImportDecls(f.Decls...)...)
	decls = append(decls, astutil.UnexportedIndividualTypeOrValueDecls(f.Decls...)...)
	decls = append(decls, astutil.ExportedResultsIndividualTypeOrValueDecls(f.Decls...)...)
	decls = append(decls, astutil.FuncDecls(f.Decls...)...)
	f.Decls = decls

	if len(r.extraIfaces) > 0 {
		for name := range r.extraIfaces {
			ast.Inspect(f, func(n ast.Node) bool {
				if ft, ok := n.(*ast.FuncDecl); ok {
					if ft.Type.Results == nil {
						return true
					}
					for _, p := range ft.Type.Results.List {
						if se, ok := p.Type.(*ast.StarExpr); ok {
							if sei, ok := se.X.(*ast.Ident); ok && sei.Name == name {
								pkgName := r.input.IfacePkgName
								if slices.Contains(r.exportedSymbolsInModels, sei.Name) {
									pkgName = r.input.ModelsPkgName
								}
								p.Type = &ast.SelectorExpr{
									X:   ast.NewIdent(pkgName),
									Sel: sei,
								}
							}
						}
					}
				}
				return true
			})
		}
	}
	byt, err := r.intoBytes(f)
	if err != nil {
		return nil, fmt.Errorf("runner.newQueriesContent() failed: %w", err)
	}
	return byt, nil
}

func inStrings(s string, slice []string) bool {
	for _, v := range slice {
		if v == s {
			return true
		}
	}
	return false
}
