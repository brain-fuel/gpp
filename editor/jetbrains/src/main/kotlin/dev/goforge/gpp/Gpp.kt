package dev.goforge.gpp

import com.intellij.lang.Language
import com.intellij.openapi.fileTypes.LanguageFileType
import com.intellij.openapi.project.Project
import com.intellij.openapi.vfs.VirtualFile
import com.intellij.platform.lsp.api.LspServerSupportProvider
import com.intellij.platform.lsp.api.ProjectWideLspServerDescriptor
import javax.swing.Icon

object GppLanguage : Language("gpp")

class GppFileType : LanguageFileType(GppLanguage) {
    companion object { @JvmField val INSTANCE = GppFileType() }
    override fun getName() = "G++"
    override fun getDescription() = "G++ source"
    override fun getDefaultExtension() = "gpp"
    override fun getIcon(): Icon? = null
}

class GppLspServerSupportProvider : LspServerSupportProvider {
    override fun fileOpened(project: Project, file: VirtualFile, serverStarter: LspServerSupportProvider.LspServerStarter) {
        if (file.extension == "gpp") {
            serverStarter.ensureServerStarted(GppLspServerDescriptor(project))
        }
    }
}

private class GppLspServerDescriptor(project: Project) : ProjectWideLspServerDescriptor(project, "gpp") {
    override fun isSupportedFile(file: VirtualFile) = file.extension == "gpp"
    override fun createCommandLine() = com.intellij.execution.configurations.GeneralCommandLine("gpp", "lsp")
}
