# axiom-physics

Lean 4 formalizations of theorems in mathematical physics. Each folder is a self-contained Lake package (Lean `v4.28.0`, pinned mathlib).

| Folder | Result |
|---|---|
| [quantum-adiabatic](quantum-adiabatic) | Uniformly gapped quantum adiabatic theorem, including unbounded self-adjoint Hamiltonians on a common domain |
| [quantum-backflow](quantum-backflow) | Quantum backflow for positive-momentum free-particle wave packets |
| [generalized-equipartition](generalized-equipartition) | Generalized canonical equipartition for coupled, nonquadratic Hamiltonians |

```sh
cd <folder>
lake exe cache get && lake --wfail build
python3 checks/check_proofs.py
```

Neil Yuanting Li. Licensed under [Apache 2.0](LICENSE); see [NOTICE](NOTICE).
