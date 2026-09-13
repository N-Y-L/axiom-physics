# Quantum adiabatic theorem in Lean

A Lean 4 formalization of the uniformly gapped quantum adiabatic theorem,
including unbounded self-adjoint Hamiltonians on a common domain in an
arbitrary complex Hilbert space. The proof constructs the spectral
projection and Schrödinger evolution, then proves uniform error bounds.

## The result

Let $H(s)$ be a self-adjoint Hamiltonian on a fixed dense domain $D$ in a
complex Hilbert space $E$. Assume $H:D\to E$ is $C^2$ in the graph norm for
$0\le s\le1$. Choose continuous real endpoints $a(s)<b(s)$ whose distances
from the spectrum are at least a fixed $g>0$.

The formalization constructs the orthogonal spectral projection $P(s)$ for
the spectrum between these endpoints and proves that it is $C^2$. Neither
the Hilbert space nor the selected spectral subspace needs to have finite
dimension. The Hamiltonian need not be bounded in the physical norm.

With $\hbar=1$, it constructs domain-preserving unitary evolution satisfying

$$
U_T'(s)\psi=-iT H(s)U_T(s)\psi,\qquad U_T(0)=I,\qquad\psi\in D.
$$

There is a constant $C\ge0$, chosen before the runtime $T$, such that for
every $T>0$ and every $s\in[0,1]$,

$$
\left\|U_T(s)P(0)U_T(s)^*-P(s)\right\|\le\frac{C}{T},
\qquad
\left\|(I-P(s))U_T(s)P(0)\right\|\le\frac{C}{T}.
$$

These are Hilbert-space operator norms. The second bound controls departure
from the selected spectral subspace. Degeneracies and crossings inside the
band are allowed. Strong unitary common-domain evolution is unique on the
unit interval.

The main declaration is
[`Adiabatic.Unbounded.common_domain_adiabatic_theorem`](Adiabatic/Unbounded/MainTheorem.lean).
Its complete hypotheses and conclusion are in
[Unbounded/Statement.lean](Adiabatic/Unbounded/Statement.lean).
The original [finite-dimensional theorem](Adiabatic/MainTheorem.lean) remains
available unchanged.

## Read the proof

| File | Contents |
|---|---|
| [Documentation index](docs/README.md) | Reading paths for the theorem, research, verification, and publication |
| [Proof guide](docs/proof-guide.md) | Mathematical argument and Lean dependencies |
| [Common-domain research](docs/unbounded-research.md) | Literature, assumptions, spectral calculus, and evolution construction |
| [Verification](docs/verification.md) | Exact scope and mechanical checks |
| [Prior work](docs/prior-art.md) | Public-source search and its limits |
| [Module map](Adiabatic/README.md) | Source organization and all public proof modules |
| [Unbounded/MainTheorem.lean](Adiabatic/Unbounded/MainTheorem.lean) | Full theorem and evolution uniqueness |
| [Unbounded/Nonautonomous.lean](Adiabatic/Unbounded/Nonautonomous.lean) | Evolution existence from common-domain self-adjointness |
| [Examples.lean](Adiabatic/Examples.lean) | A nontrivial two-level example for the original finite theorem |

The result gives an existential constant. Gapless evolution, changing
operator domains, explicit optimal gap dependence, and higher-order or
exponentially small error estimates are outside this statement. The
prior-work search found no complete publicly inspectable formalization in
the sources searched; it does not establish priority.

## Check the proofs

Install [Lean through elan](https://lean-lang.org/install/) and Python 3.
From this repository folder, run:

```sh
lake exe cache get
lake --wfail build
python3 checks/check_proofs.py
LEAN_NUM_THREADS=1 lake env leanchecker Adiabatic
```

On Windows, the Python command can be run as `py -3 checks/check_proofs.py`;
set `LEAN_NUM_THREADS` using the conventions of your shell for the last
command. The compiler and dependency revisions are pinned in
`lean-toolchain` and `lake-manifest.json`.

The integrity check rejects unfinished proofs and added axioms, and checks
the transitive dependencies of every declaration from a project proof module,
including private declarations and declarations in other namespaces. Only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound` are permitted.
The final command rechecks the compiled project proofs with Lean's bundled
checker. The [verification record](docs/verification.md) distinguishes these
mechanical checks from the review of the mathematical statement.
Regression tests for the integrity checker are documented in [checks/](checks/README.md).

## References and license

The proof follows the Kato/commutator approach. Primary references include
[Kato (1950)](https://doi.org/10.1143/JPSJ.5.435),
[Kato (1953)](https://doi.org/10.2969/jmsj/00520208),
[Avron–Elgart (1999)](https://arxiv.org/abs/math-ph/9805022),
[Jansen–Ruskai–Seiler (2007)](https://arxiv.org/abs/quant-ph/0603175), and
[Schmid–Griesemer (2014)](https://arxiv.org/abs/1203.4700).
The research notes explain how their assumptions relate to this theorem.

Licensed under [Apache 2.0](LICENSE). See [NOTICE](NOTICE) for mathlib
attribution, [CONTRIBUTING.md](CONTRIBUTING.md) for editing conventions,
and [UPDATES.md](UPDATES.md) for changes.
