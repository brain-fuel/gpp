# Goal 05: typed routes and Chi migration

## Baseline and boundary

The migration target is `github.com/go-chi/chi/v5` v5.3.1, tag commit
`8b258c7bb28f97a5f2a856ff7ef962578fec9215` (MIT). The compatibility facade
lives in sibling module `goforge.dev/chi`; its complete public inventory and
tier decisions live in `API_MANIFEST.csv`.

Mutable route registration remains a migration convenience. The serving
boundary is an immutable `Snapshot`: exact routes use a direct method/path
index, dynamic routes are pre-parsed and sorted by specificity, middleware is
precomposed, and published snapshots never change.

## Routing and conflicts

Tier 1 covers static routes, named parameters, regex parameters, terminal
wildcards, method routing, 404/405 handlers, groups, inline/global middleware,
mounting, matching, traversal, and standard `net/http` serving. Compilation
returns both the snapshot and structured `DuplicateRoute` or `AmbiguousRoute`
diagnostics. The semantic layer rejects ambiguity before publication; the
compatibility `ServeHTTP` path panics if an ambiguous mutable registry is used
without checking `Compile`.

`RouteInfo` exposes method, pattern, parameter names, and handler directly from
the immutable snapshot. Documentation and OpenAPI tooling do not need access to
private radix nodes or runtime request introspection.

`Snapshot.Resolve` is the semantic lookup boundary: its sealed outcome is
`MatchedRoute`, `MethodMismatch`, or `RouteMissing`. The compatibility `Match`
method remains boolean, and `ServeHTTP` maps the latter outcomes to 405 and 404.

## Dependent model

The Go+-authored `std/http/route` package provides:

- `Pattern[p]`, a parsed singleton route identity;
- `Request[p]`, the exact parameter environment produced by that pattern;
- `ParamKey[T,p]`, constructible only from `Pattern[p]` and a declared name;
- sealed `Handler[p]`, which prevents a handler for one route being registered
  under another;
- `RouteSet[s]`, whose collision-free fingerprint changes with each registered
  route identity and whose `AddOutcome` exposes duplicate conflicts;
- `Middleware[c]`, which makes observation, header writes, body reads, or state
  mutation an explicit capability index.

Cross-package Go+ rejects foreign parameter keys, foreign handlers, and a
registration whose route identity disagrees with the route-set transition.
Generated ordinary Go retains pattern and capability IDs and checks erased
boundaries. Existing `net/http` and Chi code remains valid Go+.

Promotion has two production consumers: `goforge.dev/chi` uses the typed
registration bridge, while `std/http.RouteHandler` feeds the same checked
handler into the existing multi-protocol Go+ server surface.

## Performance contract

The paired workload dispatches the same exact `GET /health` request through a
published GoForge snapshot and Chi v5.3.1. Both invoke the same handler and use
the same request and response writer. Completion requires the slowest GoForge
run to be at least twice as fast as the fastest upstream run and at least 50%
fewer allocations.
