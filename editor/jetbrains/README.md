# Go+ for GoLand / IntelliJ (paid IDEs)

Uses the IntelliJ Platform LSP API (2023.2+; paid IDEs only) to run
`goplus lsp`, plus a Go+ file type. Build with `./gradlew buildPlugin`
(Gradle + JDK 17 required — not build-verified in this repo's release
flow; see editor/PUBLISHING.md). Highlighting via TextMate: import
editor/vscode/syntaxes/goplus.tmLanguage.json under Settings → Editor →
TextMate Bundles until a dedicated lexer lands.
