Feature: goplus init scaffolds the go generate workflow
  `go generate ./... && go build ./...` is the canonical workflow; the
  goplus wrapper commands are convenience. init writes the //go:generate
  wiring (and, with -hook, a pre-commit config) and refuses to
  overwrite.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: init writes the directive and the module builds plainly
    Given a Go+ file "app.gp":
      """
      package main

      func main() {
      	println("ok" |> func(s string) string { return s })
      }
      """
    When I run goplus with arguments "init -hook"
    Then the exit code is 0
    And stdout contains "wrote goplus_generate.go"
    And stdout contains "wrote .pre-commit-config.yaml"
    And stdout contains "go get -tool goforge.dev/goplus/cmd/goplus@latest"
    And the file "goplus_generate.go" contains:
      """
      //go:generate go tool goplus gen ./...

      package main
      """
    When I run goplus with arguments "gen ./..."
    Then the exit code is 0

  Scenario: init refuses to overwrite its scaffold
    Given a file "goplus_generate.go":
      """
      //go:generate go tool goplus gen ./...

      package main
      """
    When I run goplus with arguments "init"
    Then the exit code is 2
    And stderr contains "goplus_generate.go already exists"
