# Public release preparation

The local repository is prepared for review before publication. Its intended
name is `quantum-adiabatic-lean`. No GitHub repository, public release, or DOI
is claimed by these files.

## GitHub settings

| Setting | Prepared value |
| --- | --- |
| Owner | `N-Y-L` |
| Repository | `quantum-adiabatic-lean` |
| Visibility | Public |
| Default branch | `main` |
| License | Apache 2.0, already included |
| Topics | `lean4`, `mathlib`, `quantum-mechanics`, `adiabatic-theorem`, `formal-verification`, `mathematical-physics` |

Suggested short description:

> Lean 4 proof of the uniformly gapped quantum adiabatic theorem, including unbounded self-adjoint Hamiltonians on a common domain, with constructed spectral projections and uniform C/T bounds.

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
Open **Publish repository** and use the settings above. Clear **Keep this
code private** for public visibility. The final **Publish repository** button
creates the GitHub repository and pushes the checked history. No source files or private notes from the separate research
project are needed.

After publishing, check that the **Lean proofs** workflow passes on GitHub.
Add the actual repository URL to `CITATION.cff`, and create a version tag only
after reviewing that run. Local checks are recorded in
[verification.md](verification.md); a hosted workflow run has not yet occurred.

## Commit identity

The repository uses the owner's GitHub no-reply commit address. The
unpublished history has been prepared with the same authorship and file
contents, with personal email addresses removed from commit metadata.
A private recovery copy is kept outside the repository. Publish the checked
`main` branch; do not upload private recovery files.

GitHub documents the no-reply address format in its
[email reference](https://docs.github.com/en/account-and-profile/reference/email-addresses-reference)
and explains repository-local author settings in
[Setting your commit email address](https://docs.github.com/en/account-and-profile/how-tos/email-preferences/setting-your-commit-email-address).
