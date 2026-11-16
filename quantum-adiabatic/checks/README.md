# Proof checks

Run from the repository root:

```sh
lake --wfail build
python3 checks/check_proofs.py
LEAN_NUM_THREADS=1 lake env leanchecker Adiabatic
```

- The build checks that every imported proof has its declared type and
  treats warnings as errors.
- `check_proofs.py` rejects forbidden proof constructs in project Lean
  sources. Comments and ordinary strings are excluded from that supplementary
  scan; interpolated strings remain visible.
- `Axioms.lean` selects every imported declaration by its originating
  project module. It includes private declarations and declarations in
  other namespaces, rejects unsafe declarations, and traverses the full
  dependency closure. Only `propext`, `Classical.choice`, and `Quot.sound`
  are permitted. It also prints the dependencies of 114 named public results.
- Lean's bundled checker rechecks the compiled project proof declarations.

The public `Adiabatic.lean` entry point imports all project proof modules.
Keep new proof modules reachable from that entry point.

## Choice-reduction audit

```sh
lake env lean checks/ChoiceReductionAxioms.lean
```

This audit selects every declaration originating in
`Adiabatic.ChoiceReduction`, including private and generated declarations.
It checks their complete type and proof dependencies, permitting only
`propext` and `Quot.sound`. CI runs it alongside the original audit.

[foundations-results.json](foundations-results.json) records the current
202 strict declarations, printed types, complete axiom lists, and source hashes.
The [dependency report](choice-dependencies.json) traces uses of choice in
the existing full theorem. Reproduce it with:

```sh
lake env lean checks/TraceChoice.lean
```

These paths describe the implementation; they do not by themselves prove
mathematical necessity of choice. The
[foundations overview](../docs/choice-reduction.md) distinguishes the two claims.

## Foundations diagnostics

```sh
lake env lean checks/FoundationsAxioms.lean
lake env lean checks/FoundationsDependencies.lean
```

These standalone diagnostics export all 92 declarations in the eight
`Adiabatic.Foundations` modules and the two added obstruction modules,
including generated helpers. The first prints checked types and complete
axiom lists. The second separates dependencies reached first through the
checked type from those reached first through the proof or definition body;
subsequent edges traverse both. It checks that their union equals Lean's
combined axiom collector. These diagnostics use the ordinary permitted
axioms and do not replace the stricter `ChoiceReductionAxioms.lean` audit.

## Regression tests

```sh
python3 -m unittest discover -s checks -p 'test_*.py'
```

The tests verify that unfinished proofs, direct or quoted `sorryAx`, unused
added axioms, and unsafe definitions fail the checks. They exercise private
declarations and names outside the project namespace. Separate cases ensure
ordinary comments, strings, and legitimate identifiers are accepted.
The Lean fixtures are compiled in temporary directories and do not change
project proofs or their compiled modules.

The GitHub workflow runs all 15 tests after the proof build and before the
full dependency audit. The eight strict-audit tests include private and imported
choice, choice inherited through a type, and an empty module selection.

## Verification records

[foundations-results.json](foundations-results.json) records the current
verification commands, source hashes, checked types, and axiom dependencies.
[results.json](results.json) and
[choice-reduction-results.json](choice-reduction-results.json) preserve the
September 13 historical records unchanged. Their counts and hashes describe
those earlier versions. Rerun the checks after mathematical changes.
The [verification note](../docs/verification.md) describes the theorem
hypotheses and the current checks.
