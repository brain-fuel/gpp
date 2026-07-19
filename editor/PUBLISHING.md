# Publishing the editor clients (manual, account-holder steps)

- **VS Code**: `cd editor/vscode && npm install && npm run compile &&
  npx vsce package` → upload the .vsix to the Marketplace (publisher
  account required), or `npx vsce publish`.
- **Neovim**: publish editor/nvim as a repo (gpp.nvim) or document the
  in-repo path for plugin managers.
- **Zed**: submit editor/zed to zed-industries/extensions (PR adds the
  extension as a submodule).
- **JetBrains**: `cd editor/jetbrains && ./gradlew buildPlugin` (JDK
  17), upload build/distributions/*.zip to the JetBrains Marketplace.
- Version all clients in lockstep with the gpp release they wrap.
