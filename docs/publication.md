# Public release preparation

Publication settings for `N-Y-L/quantum-adiabatic-lean`. The repository has
not yet been published.

## GitHub settings

| Setting | Prepared value |
| --- | --- |
| Owner | `N-Y-L` |
| Repository | `quantum-adiabatic-lean` |
| Visibility | Public |
| Default branch | `main` |
| License | Apache 2.0, already included |
| Topics | `lean4`, `mathlib`, `quantum-mechanics`, `adiabatic-theorem`, `formal-verification`, `mathematical-physics` |

Short description:

> Lean 4 proof of the uniformly gapped quantum adiabatic theorem, including unbounded self-adjoint Hamiltonians on a common domain, with constructed spectral projections and uniform C/T bounds.

## Release description

Lean 4 proof of the uniformly gapped quantum adiabatic theorem, including
unbounded self-adjoint Hamiltonians on a fixed dense common domain in an
arbitrary complex Hilbert space. The formalization constructs the spectral
projection of a continuously moving isolated band and the unitary
Schrödinger evolution. It proves operator-norm projection-distance and
leakage bounds $C/T$ for every $T>0$ and $s\in[0,1]$, with $C$ independent
of $T$ and $s$. The repository includes
the earlier finite-dimensional theorem, a two-level example, pinned
dependencies, a transitive axiom audit, and a cited research report.

The constant is existential. This version assumes $C^2$ common-domain
regularity and a uniform gap around a bounded spectral band. Gapless
evolution and changing domains are outside its scope.

## Publishing from GitHub Desktop

Add this folder as an existing repository and review the checked commit.
Open **Publish repository** and use the settings above. Clear **Keep this
code private** for public visibility. The final **Publish repository** button
creates the GitHub repository and pushes the checked history.

After publishing, check that the **Lean proofs** workflow passes on GitHub.
Add the actual repository URL to `CITATION.cff`, and create a version tag only
after reviewing that run. Local checks are recorded in
[verification.md](verification.md); a hosted workflow run has not yet occurred.

## Commit identity

All commits use the owner's GitHub no-reply address. Replacing the email
metadata preserved authorship and file contents. A private recovery copy
is stored outside the repository. Publish only the checked `main` branch.

GitHub documents the no-reply address format in its
[email reference](https://docs.github.com/en/account-and-profile/reference/email-addresses-reference)
and explains repository-local author settings in
[Setting your commit email address](https://docs.github.com/en/account-and-profile/how-tos/email-preferences/setting-your-commit-email-address).
