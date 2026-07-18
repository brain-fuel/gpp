package naming

import "go/ast"

// VariantTypeName computes the lowered struct type name for an enum
// variant.
//
//   - override (//gpp:name) wins verbatim.
//   - When the variant name is shared by multiple enums in the package
//     (prefixed=true), the name is the v0.1.0 concat of enum and variant
//     names (OptionNone / listNone), disambiguating deterministically.
//   - Otherwise the variant name is used directly, cased by the combined
//     visibility rule: exported iff both the enum and the variant are
//     exported.
func VariantTypeName(enumName, variantName, override string, prefixed bool) string {
	if override != "" {
		return override
	}
	if prefixed {
		return FuncName(enumName, variantName, "")
	}
	return setFirstCase(variantName, ast.IsExported(enumName) && ast.IsExported(variantName))
}

// FieldName computes the Go struct field name for a constructor parameter:
// capitalized iff the variant struct itself is exported (lowering never
// widens or narrows access).
func FieldName(paramName string, variantExported bool) string {
	return setFirstCase(paramName, variantExported)
}

// MarkerMethodName is the sealed interface's marker method: always
// unexported, tied to the enum name.
func MarkerMethodName(enumName string) string {
	return "is" + capitalize(enumName)
}
