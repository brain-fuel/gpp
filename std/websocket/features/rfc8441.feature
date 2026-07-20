Feature: RFC 8441 WebSockets over HTTP/2
  The ordinary Dial and Upgrade APIs prefer an HTTP/2 extended CONNECT when
  available and preserve RFC 6455 as a transparent compatibility path.

  Scenario: extended CONNECT replaces the HTTP 1.1 upgrade fields
    Given a canonical RFC 8441 opening request
    When I validate the extended CONNECT request
    Then extended CONNECT validation succeeds
    And the request has no RFC 6455 connection fields

  Scenario Outline: forbidden HTTP 1.1 fields are rejected over HTTP/2
    Given a canonical RFC 8441 opening request
    And the extended CONNECT request has forbidden header <header>
    When I validate the extended CONNECT request
    Then opening validation fails

    Examples:
      | header               |
      | Connection           |
      | Upgrade              |
      | Sec-WebSocket-Key    |
      | Sec-WebSocket-Accept |

  Scenario: HTTP 2 uses the websocket protocol pseudo-header
    Given a canonical RFC 8441 opening request
    And the extended CONNECT protocol is not websocket
    When I validate the extended CONNECT request
    Then opening validation fails

  Scenario: secure automatic dialing prefers RFC 8441
    Given a secure WebSocket URL with automatic transport selection
    Then RFC 8441 is attempted before RFC 6455 fallback

  Scenario: cleartext automatic dialing preserves RFC 6455 compatibility
    Given a cleartext WebSocket URL with automatic transport selection
    Then RFC 6455 is used unless HTTP 2 is explicitly requested
