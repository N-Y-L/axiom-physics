# Choice and the adiabatic theorem

The usual common-domain proof passes from regularity in a fixed domain norm
to estimates in the physical Hilbert-space norm. It uses the bounded inverse
theorem to compare that domain norm with the graph norm of each Hamiltonian.
These notes examine what happens to this step when choice is removed.

Here ZF means classical set theory without the axiom of choice (AC), and DC
means dependent choice. The questions concern the same uniformly gapped
common-domain theorem and its two uniform $C/T$ estimates.

## Mathematical results

The [necessity proof](foundations/necessity.md) constructs a Hamiltonian that
is $C^2$ in its initial graph norm and has a uniform spectral gap, yet its
physical spectral projection is discontinuous in operator norm. Both
adiabatic errors have supremum at least $1/2$ for every runtime. The
construction uses an infinite Dedekind-finite subset of the reals. Thus the
original theorem implies that every infinite subset of $\mathbb R$ contains
a countably infinite subset, a weak choice principle that can fail in ZF.

The [dependent-choice proof](foundations/dependent-choice.md) derives the
full theorem from ZF + DC, with its original hypotheses. It constructs the
spectral projection, domain-preserving unitary evolution, and both estimates.
Full AC is therefore unnecessary mathematically.

The [graph-control theorem](foundations/graph-control.md) proves the result
in ZF for uniformly complete spaces when graph control at every time is
assumed explicitly. Its spectral-closure lemma preserves the original
algebraic spectral-gap condition. This additional hypothesis excludes the
counterexample; DC derives it from the original assumptions.

These are mathematical proofs, **not Lean formalizations**. The weakest
sufficient choice principle for the original theorem remains undetermined.

## Lean results

The original theorem is Lean-checked with axioms
`[propext, Classical.choice, Quot.sound]`. Its statement and proof are unchanged.
The supporting modules in `Adiabatic/ChoiceReduction/` prove inverse identities,
finite selection, product estimates, and inverse extraction. All 189 new
declarations have complete audited dependencies contained in
`[propext, Quot.sound]`.

The [Lean audit](foundations/lean-audit.md) gives the exact statements,
dependency paths, and verification commands. It distinguishes a mathematical
need for choice from dependencies inherited through Lean's current analytic
types. The supporting lemmas do not constitute a Lean proof of the
foundational results above.

| Reading | Purpose |
| --- | --- |
| [Necessity](foundations/necessity.md) | Counterexample and required weak choice principle |
| [Dependent choice](foundations/dependent-choice.md) | Sufficient foundation for the original theorem |
| [Graph control](foundations/graph-control.md) | ZF proof under the additional graph inequality |
| [Lean audit](foundations/lean-audit.md) | Checked components and transitive axioms |
| [Bounded lifts](foundations/bounded-lifts.md) | Auxiliary obstruction through bounded inverse extraction |
