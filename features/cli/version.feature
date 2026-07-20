Feature: goplus version
  The goplus toolchain reports its own version so users and CI can pin and
  diagnose the generator that produced committed artifacts.

  Scenario: Reporting the toolchain version
    When I run goplus with arguments "version"
    Then the exit code is 0
    And stdout contains "goplus version v0.15.0"

  Scenario: Unknown commands fail with usage guidance
    When I run goplus with arguments "frobnicate"
    Then the exit code is 2
    And stderr contains "unknown command"

  Scenario: Help lists every command
    When I run goplus with arguments "help"
    Then the exit code is 0
    And stdout contains "gen"
    And stdout contains "build"
    And stdout contains "version"
