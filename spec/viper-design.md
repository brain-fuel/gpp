# Goal 04: typed configuration and Viper migration

## Baseline and boundary

The migration target is `github.com/spf13/viper` v1.21.0, tag commit
`394040caccbdf5821fa6839386a35f0fb1b1ee9e` (MIT). The compatibility facade
lives in the sibling module `goforge.dev/viper`; the complete upstream public
inventory and tier status live in its `API_MANIFEST.csv`.

Viper's mutable registry remains useful as a migration boundary. It is not the
semantic center. The standard-library center is an immutable resolved snapshot
whose values retain their winning source.

## Precedence and ownership

The canonical low-to-high precedence order is defaults, remote values, file,
environment, flags, and explicit overrides. Repeated layers of the same kind
use declaration order. Resolution copies caller maps and owned slice values.

`std/config.Source` is exhaustive and `Entry` pairs each value with its source.
`Snapshot[s]` is immutable after construction. The facade additionally offers
a lock-free `Snapshot` compiled from its mutable compatibility registry.

## Dependent model

- `Snapshot[s]` ties a resolved configuration to schema identity `s`.
- `Key[T,s]` can read only values of `T` from the same schema.
- `Require` converts a lookup into `Requirement[T,s]`; its `Available` branch
  carries `Present[T,s]` evidence and `RequiredValue` is total.
- `Subset[s,sub]` witnesses a declared projection, and `Project` changes the
  schema index only through that witness.

Go+ rejects a key or subset belonging to another schema. Generated ordinary Go
retains numeric schema IDs and panics at an invalid erased boundary. This is an
opt-in dependent layer: existing Go configuration code remains valid Go+.

Reload is a separate effect boundary in the facade. `ReloadStream` serializes
`Loader` calls and publishes monotonically versioned `ReloadEvent` values. Each
event contains either an owned immutable snapshot or an error; failed attempts
cannot partially mutate a snapshot already visible to readers.

## Compatibility tier

Tier 1 covers the high-use instance and package-global forms for defaults,
overrides, typed reads, environment bindings, aliases, pflag bindings,
map/file ingestion, key enumeration, and settings snapshots. JSON, YAML, and
TOML reader ingestion are supported. Search paths, writes, remote providers,
watch callbacks, codecs, unmarshalling hooks, and legacy global reload policy
remain explicitly deferred.

## Performance contract

The paired workload repeatedly reads a resolved string. GoForge reads an
immutable snapshot; upstream Viper performs its normal dynamic precedence
lookup. Completion requires the slowest GoForge run to be at least twice as
fast as the fastest upstream run and at least 50% fewer allocations. The
snapshot API is deliberately explicit: no speed claim is made for every mutable
compatibility call.
