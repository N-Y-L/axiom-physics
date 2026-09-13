# Quantum adiabatic theorem in Lean

A Lean 4 formalization of the finite-dimensional quantum adiabatic theorem,
using mathlib. The proof includes existence of Schrödinger evolution,
Kato transport, the spectral-gap argument, and a uniform error bound.

## The result

Let $H(s)$ be a self-adjoint Hamiltonian on a finite-dimensional complex
Hilbert space. Let $P(s)$ be an orthogonal projection commuting with $H(s)$.
Assume both paths are $C^2$, and the spectra selected by $P(s)$ and $I-P(s)$
are separated by a fixed gap $g>0$ for $0\le s\le1$.

With $\hbar=1$, the physical evolution satisfies

$$
U_T'(s)=-iT H(s)U_T(s),\qquad U_T(0)=I.
$$

The formalization proves that this evolution exists and that there is a
constant $C\ge0$, independent of $T$, such that every solution satisfies

$$
\left\|(I-P(s))U_T(s)P(0)\right\|\le\frac{C}{T}
\qquad(T>0,\;0\le s\le1).
$$

The norm is the Hilbert-space operator norm. Degeneracies and crossings within
either spectral sector are allowed. The formal hypotheses use paths defined
on $\mathbb R$; the gap is needed only on $[0,1]$.

The main declaration is
[`Adiabatic.finite_dimensional_adiabatic_theorem`](Adiabatic/MainTheorem.lean).
Its complete hypotheses and conclusion are defined in
[Statement.lean](Adiabatic/Statement.lean).

## Read the proof

| File | Contents |
|---|---|
| [Proof guide](docs/proof-plan.md) | Mathematical argument, conventions, and Lean dependencies |
| [Verification](docs/verification.md) | What is checked and the exact scope |
| [Prior work](docs/prior-art.md) | Literature and formalization search with sources |
| [MainTheorem.lean](Adiabatic/MainTheorem.lean) | Complete theorem assembled from the supporting results |
| [Examples.lean](Adiabatic/Examples.lean) | A two-level Hamiltonian with a proper spectral subspace and gap one |
| [Adiabatic/](Adiabatic/) | Propagator, projection, transport, spectral, and error-bound proofs |

The theorem takes a smooth spectral projection as input. Constructing that
projection from a Hamiltonian alone, explicit constants in terms of the gap,
and infinite-dimensional or gapless versions are outside this result.
The prior-work search found no complete publicly inspectable formalization;
it does not establish priority.

## Check the proofs

Install [Lean through elan](https://lean-lang.org/install/) and Python 3.
From this repository folder, run:

```sh
lake exe cache get
lake build
python3 checks/check_proofs.py
```

On Windows, the last command can be run as `py -3 checks/check_proofs.py`.
The first run downloads the compiler and dependencies. The compiler version
and all dependency revisions are pinned in `lean-toolchain` and
`lake-manifest.json`.

The integrity check rejects unfinished proofs, new axioms, and unapproved
axioms in the transitive dependencies of the audited declarations.
The accepted foundational axioms are Lean's `propext`, `Classical.choice`,
and `Quot.sound`. Compilation and an axiom audit establish the formal
statements; the [verification note](docs/verification.md) explains their
connection to the physical theorem.

## References and license

The argument follows the Kato/commutator approach. Primary mathematical
references include [Kato (1950)](https://doi.org/10.1143/JPSJ.5.435),
[Avron–Elgart (1999)](https://arxiv.org/abs/math-ph/9805022), and
[Jansen–Ruskai–Seiler (2007)](https://arxiv.org/abs/quant-ph/0603175).
The research notes provide detailed citations and scope comparisons.

Licensed under [Apache 2.0](LICENSE). See [NOTICE](NOTICE) for mathlib
attribution, [CONTRIBUTING.md](CONTRIBUTING.md) for editing conventions,
and [UPDATES.md](UPDATES.md) for changes.
