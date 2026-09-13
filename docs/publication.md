# Public release preparation

The local repository is prepared for review before publication. Its intended
name is `quantum-adiabatic-lean`. No GitHub repository, public release, or DOI
is claimed by these files.

## Release description

Lean 4 proof of the uniformly gapped quantum adiabatic theorem, including
unbounded self-adjoint Hamiltonians on a fixed dense common domain in an
arbitrary complex Hilbert space. The formalization constructs the spectral
projection of a continuously moving isolated band and the unitary
Schrödinger evolution. It proves operator-norm projection-distance and
leakage bounds $C/T$, uniform in time and runtime. The repository includes
the earlier finite-dimensional theorem, a two-level example, pinned
dependencies, a transitive axiom audit, and a cited research report.

The constant is existential. This version assumes $C^2$ common-domain
regularity and a uniform gap around a bounded spectral band. It does not
claim gapless evolution, changing domains, or worldwide priority.

## Publishing from GitHub Desktop

Add this folder as an existing repository and review the checked commit.
Use **Publish repository** when ready, with the name above and public
visibility. No source files or private notes from the separate research
project are needed.

After publishing, check that the **Lean proofs** workflow passes on GitHub.
Add the actual repository URL to `CITATION.cff`, and create a version tag only
after reviewing that run. Local checks are recorded in
[verification.md](verification.md); a hosted workflow run has not yet occurred.
