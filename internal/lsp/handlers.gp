// The server's dispatch layer, authored in goplus: incoming work is an
// enum, routing is a match, and extending the server means adding a
// variant and an arm — the language serving itself.
package lsp

// Incoming is document-lifecycle work (notifications: no reply).
type Incoming enum {
	Opened(uri string, text string)
	Changed(uri string, text string)
	Closed(uri string)
	Saved(uri string)
}

// Dispatch routes lifecycle work onto the server.
func Dispatch(s *Server, in Incoming) {
	match in {
	case Opened(uri, text):
		s.SetOverlay(uri, text)
		s.ScheduleDiagnostics()
	case Changed(uri, text):
		s.SetOverlay(uri, text)
		s.ScheduleDiagnostics()
	case Closed(uri):
		s.DropOverlay(uri)
	case Saved(uri):
		_ = uri
		s.ScheduleDiagnostics()
	}
}

// Query is position work (requests: a reply is owed).
type Query enum {
	QHover(uri string, line int, ch int)
	QDefinition(uri string, line int, ch int)
	QComplete(uri string, line int, ch int)
}

// QueryReply is what a query yields: raw JSON from the delegate, or a
// reasoned absence (the client renders null).
type QueryReply enum {
	Raw(data []byte)
	NoAnswer(reason string)
}

// Answer resolves one query through the gopls delegate.
func Answer(s *Server, q Query) QueryReply {
	match q {
	case QHover(uri, line, ch):
		return s.Forward("textDocument/hover", uri, line, ch)
	case QDefinition(uri, line, ch):
		return s.Forward("textDocument/definition", uri, line, ch)
	case QComplete(uri, line, ch):
		return s.Forward("textDocument/completion", uri, line, ch)
	}
}
