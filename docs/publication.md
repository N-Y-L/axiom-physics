# Public release preparation

The local repository is prepared for review before publication. Its intended
name is `quantum-adiabatic-lean`. No GitHub repository, public release, or DOI
is claimed by these files.

## Release description

Lean 4 proof of the finite-dimensional quantum adiabatic theorem for smooth
Hamiltonian and orthogonal spectral-projection paths with a uniform gap.
The formalization constructs Schrödinger evolution and proves an
operator-norm leakage bound $C/T$, uniform in time and runtime. It includes
a two-level example, pinned dependencies, and a transitive axiom audit.

The result assumes a supplied smooth spectral projection and gives an
existential constant. It does not cover infinite-dimensional Hamiltonians
or claim to be the first formalization.

## Publishing from GitHub Desktop

Add this folder as an existing repository and review the files and initial
commit. Use **Publish repository** when ready, with the name above and public
visibility. No source files or private notes from the separate research
project are needed.

After publishing, check that the **Lean proofs** workflow passes on GitHub.
Add the actual repository URL to `CITATION.cff`, and create a version tag only
after reviewing that run. The local build and audit are recorded in
[verification.md](verification.md); a hosted workflow run has not yet occurred.
