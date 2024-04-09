// Package separateinterface separates models and the `Querier` interface from the `Queries` struct.
// This is typically done to adhere to the Dependency Inversion Principle (DIP), allowing for more flexible and testable code.
package separateinterface

import (
	"context"
	"go/ast"
	"go/token"
)

type ActionInput struct {
	// IfacePkgName The package name where the separated Querier will be located.
	IfacePkgName string
	// IfacePkgURL The package URL where the separated Querier will be located.
	IfacePkgURL string
	// IfaceDir The directory path where the separated Querier will be located.
	IfaceDir string
	// ModelsPkgName The package name where the separated models will be located.
	ModelsPkgName string
	// ModelsPkgURL The package URL where the separated models will be located.
	ModelsPkgURL string
	// ModelsDir The directory path where the separated models will be located.
	ModelsDir string
	// ImplDir The original directory where the sqlc-generated code is located.
	ImplDir string
	// ImplSQLSuffix The suffix for sqlc-generated files from SQL files.
	ImplSQLSuffix string
	// ModelsFileName The file name for the sqlc-generated models file.
	ModelsFileName string
	// QuerierFileName The file name for the sqlc-generated Querier file.
	QuerierFileName string
	// BatchFileName The file name for the sqlc-generated Batch file.
	BatchFileName string
	// CopyFromFileName The file name for the sqlc-generated CopyFrom file.
	CopyFromFileName string
}

func Action(_ context.Context, input ActionInput) error {
	r := &runner{
		input:       input,
		fset:        token.NewFileSet(),
		extraIfaces: map[string]ast.Decl{},
	}
	return r.Run()
}
