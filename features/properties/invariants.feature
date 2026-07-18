Feature: Generator invariants (property-based)
  These scenarios are properties: each step drives pgregory.net/rapid over
  randomly generated inputs (100 cases by default, minimized on failure).
  They pin the invariants everything else relies on.

  Scenario: Any valid Go file is a valid G++ file
    Then for any plain Go file, parsing as G++ succeeds with no generic methods

  Scenario: Plain Go passes through as exactly header plus source
    Then for any plain Go file, the emitted output is the header plus the source unchanged

  Scenario: Generation is deterministic and idempotent
    Then for any G++ package, generating twice produces identical bytes and no rewrites

  Scenario: Lowered names are independent of declaration order
    Then for any G++ package, permuting declarations preserves the lowered function names

  Scenario: Exhaustiveness matches the coverage oracle (sampled)
    Then for sampled enums, generation succeeds exactly when the match covers every variant
