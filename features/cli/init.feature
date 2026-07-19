Feature: gpp init scaffolds the go generate workflow
  `go generate ./... && go build ./...` is the canonical workflow; the
  gpp wrapper commands are convenience. init writes the //go:generate
  wiring (and, with -hook, a pre-commit config) and refuses to
  overwrite.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: init writes the directive and the module builds plainly
    Given a G++ file "app.gpp":
      """
      package main

      func main() {
      	println("ok" |> func(s string) string { return s })
      }
      """
    When I run gpp with arguments "init -hook"
    Then the exit code is 0
    And stdout contains "wrote gpp_generate.go"
    And stdout contains "wrote .pre-commit-config.yaml"
    And stdout contains "go get -tool goforge.dev/gpp/cmd/gpp@latest"
    And the file "gpp_generate.go" contains:
      """
      //go:generate go tool gpp gen ./...

      package main
      """
    When I run gpp with arguments "gen ./..."
    Then the exit code is 0

  Scenario: init refuses to overwrite its scaffold
    Given a file "gpp_generate.go":
      """
      //go:generate go tool gpp gen ./...

      package main
      """
    When I run gpp with arguments "init"
    Then the exit code is 2
    And stderr contains "gpp_generate.go already exists"
