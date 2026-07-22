package http

import (
	nethttp "net/http"

	"goforge.dev/goplus/std/http/route"
)

// RouteHandler bridges the pattern-indexed std/http/route layer into the
// protocol-negotiating Server. Go+ checks Pattern[p] and Handler[p] before
// erasure; ordinary Go receives the retained runtime boundary guard.
func RouteHandler(pattern route.Pattern, handler route.Handler) nethttp.Handler {
	return route.Adapt(pattern, handler)
}
