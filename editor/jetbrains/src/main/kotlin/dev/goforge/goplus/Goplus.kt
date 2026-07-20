package dev.goforge.gp

import com.intellij.lang.Language
import com.intellij.openapi.fileTypes.LanguageFileType
import com.intellij.openapi.project.Project
import com.intellij.openapi.vfs.VirtualFile
import com.intellij.platform.lsp.api.LspServerSupportProvider
import com.intellij.platform.lsp.api.ProjectWideLspServerDescriptor
import javax.swing.Icon

object GoplusLanguage : Language("goplus")

class GoplusFileType : LanguageFileType(GoplusLanguage) {
    companion object { @JvmField val INSTANCE = GoplusFileType() }
    override fun getName() = "Go+"
    override fun getDescription() = "Go+ source"
    override fun getDefaultExtension() = "goplus"
    override fun getIcon(): Icon? = null
}

class GoplusLspServerSupportProvider : LspServerSupportProvider {
    override fun fileOpened(project: Project, file: VirtualFile, serverStarter: LspServerSupportProvider.LspServerStarter) {
        if (file.extension == "goplus") {
            serverStarter.ensureServerStarted(GoplusLspServerDescriptor(project))
        }
    }
}

private class GoplusLspServerDescriptor(project: Project) : ProjectWideLspServerDescriptor(project, "goplus") {
    override fun isSupportedFile(file: VirtualFile) = file.extension == "goplus"
    override fun createCommandLine() = com.intellij.execution.configurations.GeneralCommandLine("goplus", "lsp")
}
