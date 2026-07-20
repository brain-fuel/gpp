# Go+ WebSocket

`goforge.dev/goplus/std/websocket` implements RFC 6455 and RFC 7692 for Go+
and Go. The public message vocabulary is a closed Go+ sum type; framing hot
paths remain allocation-free Go so both languages use the same wire code.

## Server

```go
conn, protocol, err := websocket.Upgrade(w, r, websocket.UpgradeOptions{
    Protocols:   []string{"assay.v1"},
    Compression: &websocket.CompressionOptions{},
})
if err != nil { return }
defer conn.Close()

message, err := conn.ReadMessage()
if err == nil {
    err = conn.WriteMessage(message)
}
_ = protocol
```

`Upgrade` does not impose an origin policy. Browser-facing endpoints should set
`CheckOrigin: websocket.SameOrigin`; non-browser clients without an `Origin`
header remain accepted by that helper.

## Client

```go
conn, response, err := websocket.Dial(ctx, "wss://example.test/socket",
    websocket.DialOptions{
        Protocols: []string{"assay.v1"},
        Compression: &websocket.CompressionOptions{
            ClientMaxWindowBits: 15,
        },
    })
if err != nil { return err }
defer conn.Close()
_ = response
return conn.WriteMessage(websocket.TextMessage{Payload: []byte("hello")})
```

For `wss://` URLs, `Dial` first attempts RFC 8441 extended CONNECT over
HTTP/2 and automatically retries with the RFC 6455 HTTP/1.1 Upgrade when the
peer does not advertise `SETTINGS_ENABLE_CONNECT_PROTOCOL`. The same `Upgrade`
handler accepts both forms and `Conn.HandshakeProtocol()` exposes which path
was selected when metrics need it. Cleartext `ws://` remains RFC 6455 by
default; use `HTTP2: websocket.HTTP2Only` for h2c prior knowledge.

```go
conn, response, err := websocket.Dial(ctx, "wss://example.test/events", websocket.DialOptions{})
// conn is identical to use whether response.ProtoMajor is 2 or 1.
```

Go 1.24–1.26 guards server advertisement of RFC 8441 behind the upstream
HTTP/2 compatibility switch. Start server processes with
`GODEBUG=http2xconnect=1`; no handler changes are required. Clients do not
need this setting. The zero-configuration secure client transport is shared,
so concurrent WebSockets multiplex on one HTTP/2 connection. Supplying
`HTTP2Transport` allows the application to own that shared transport when it
needs custom TLS, dialing, or lifecycle policy.

Go callers can use the concise `WriteText`, `WriteBinary`, `WritePing`,
`WritePong`, and `WriteClose` methods. Go+ callers can instead construct and
exhaustively match the closed `Message` enum; indexed `Capability[Phase]`
values make opening and closing transitions explicit in protocol orchestration.

```goplus
capability := websocket.OpenCapability(conn)
capability, err = websocket.Send(capability,
    websocket.TextMessage([]byte("hello")))
attempt := websocket.BeginClose(capability, websocket.CloseNormalClosure, "done")
match attempt {
case CloseStarted(closing):
    closed, err := websocket.FinishClose(closing)
case CloseFailed(open, cause):
    // `open` retains ownership, so the caller can recover or retry.
}
```

The capability is quantity-1: Go+ proves it is consumed exactly once on every
path. Generated Go carries the same guarantee with a use-once `Lin` cell and
runtime index guards. This layer is optional; direct `Conn` calls remain the
idiomatic Go API.

`WriteMessage` preserves caller-owned payload bytes. `WriteMessageOwned`
transfers ownership and avoids the defensive masking copy on clients. One
reader and one writer may operate concurrently; writes are serialized.

## Conformance and performance

The complete Autobahn 25.10.1 server and client gates require Podman. The
runner pins the suite image by digest so the 517-case contract cannot drift:

```sh
./websocket/autobahn/run-podman.sh
./websocket/autobahn/run-client-podman.sh
```

Docker Compose users can run `websocket/autobahn/run.sh`. Reports are written
under `websocket/autobahn/reports/` and the verifier fails on any non-passing
required case.

The comparative gobwas/ws performance contract is:

```sh
go run ./websocket/cmd/benchgate
```

The handwritten implementation is held at complete statement coverage:

```sh
go test -coverprofile=/tmp/websocket.cover ./websocket
go run ./websocket/cmd/covergate -profile /tmp/websocket.cover
```

Protocol, compression, conformance, coverage, and performance requirements live
in `features/*.feature`; normal tests execute behavioral scenarios, while the
coverage and benchmark tags are enforced by their dedicated gates.
