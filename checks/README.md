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
  sources. Comments and strings are excluded from that supplementary scan.
- `Axioms.lean` selects every imported declaration by its originating
  project module. It includes private declarations and declarations in
  other namespaces, rejects unsafe declarations, and traverses the full
  dependency closure. Only `propext`, `Classical.choice`, and `Quot.sound`
  are permitted. It also prints the dependencies of 69 named public results.
- Lean's bundled checker rechecks the compiled project proof declarations.

The public `Adiabatic.lean` entry point imports all project proof modules.
Keep new proof modules reachable from that entry point.

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

The GitHub workflow runs these tests after the proof build and before the
full dependency audit.

## Verification record

[results.json](results.json) records completed checks, the pinned toolchain,
public theorem names, and source hashes. Rerun the checks after mathematical
changes.
The [verification note](../docs/verification.md) describes the exact theorem
scope and the separate semantic review.
