# Actual pre-caller automation observation

The source and namespace limits in OPACITY-v1.md remain in force. The actual
fresh diagnostic run `supplier-diagnostic-20261004T185446Z-92c086fc` captured
the ordered global automation tables before supplier reconstruction and after
supplier reconstruction, before any C1 loader. These are observations from the
same HOL process, not source grep results.

`ambient-observation-v1.json`, SHA-256
`8473d6720f5cbe66b893aebf1534d62edeec024f1f120c3e962246c780019ef1`,
records that all 34 basic rewrite entries, eight basic congruences and five
named basic conversion patterns were exactly unchanged, including their order.
The three axiom conclusions were exactly unchanged. There were no visible
added or removed entries in these tables during supplier reconstruction.

The stored snapshots contain complete visible conclusions, hypotheses and
constant names for rewrite/congruence entries, plus conversion names/patterns.
The audit also searches those visible entries for crypto/memcmp/cleanse names
and the canonical CRYPTO_memcmp address. These searches describe visible table
membership only. Any concrete instruction statement encoded without those
names is still covered by the exact before/after table comparison, but the
audit does not identify its derivation or enumerate every ambient theorem.

This gives bounded evidence against supplier-specific additions to those
visible global tables in this run. It does not inspect conversion closure
internals, tactic closure internals, mutable data reached by those closures,
all named ML theorem bindings, or kernel proof dependency edges. Supplier body
objects remain in the ambient namespace. Formal dependency and capability
isolation remain unestablished, and prior source/recipe exposure remains
disclosed. H1 must be stated under this source and automation observation scope.

The successor positive driver separately records the same two snapshots in
its own fresh run. Their future hashes and observations must be taken from that
run; this diagnostic snapshot cannot replace positive reconstruction evidence.
The genuine-positive requirement for both inherited integrity controls and the
fresh usable-binding construction probe remains unchanged. No acceptance or
status pointer is changed by this observation.
