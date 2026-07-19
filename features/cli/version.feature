Feature: gpp version
  The gpp toolchain reports its own version so users and CI can pin and
  diagnose the generator that produced committed artifacts.

  Scenario: Reporting the toolchain version
    When I run gpp with arguments "version"
    Then the exit code is 0
    And stdout contains "gpp version v0.8.0"

  Scenario: Unknown commands fail with usage guidance
    When I run gpp with arguments "frobnicate"
    Then the exit code is 2
    And stderr contains "unknown command"

  Scenario: Help lists every command
    When I run gpp with arguments "help"
    Then the exit code is 0
    And stdout contains "gen"
    And stdout contains "build"
    And stdout contains "version"
