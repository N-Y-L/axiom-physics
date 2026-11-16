# A necessary choice principle for the initial-graph-norm adiabatic theorem

Without choice, a Hamiltonian can be smooth in its initial graph norm while
its spectral projection is discontinuous in the physical operator norm.
The counterexample below shows that the common-domain adiabatic theorem
implies a weak choice principle. It concerns the physical projection and
both adiabatic estimates, independently of the bounded domain lift.
This is a mathematical proof in classical ZF; it is not formalized in Lean.

## Statement

Let **QAT** denote the following assertion for every uniformly complete complex
Hilbert space E. A self-adjoint Hamiltonian family has a fixed dense domain D.
Equip D with the graph norm of H(0), and assume it is complete and that
H is C² from [0,1] into the bounded operators D → E. A bounded spectral band
has continuous endpoints uniformly separated from the spectrum. Then its
physical spectral projection P is norm-continuous, and normalized strong
unitary Schrödinger evolution has the two uniform C/T estimates in the
repository's intended theorem. Adding C² regularity of P to the conclusion
strengthens this assertion.

**Theorem (ZF).** QAT implies that every infinite subset of the real numbers
contains a countably infinite subset.

The consequence is a weak choice principle, not the full axiom of choice.
It is not provable in ZF, relative to the consistency of ZF. The necessity
result concerns this precise initial-graph-norm formulation.
The separate [sufficiency proof](dependent-choice.md) shows that DC suffices
for the same theorem, so full AC is not required mathematically.

The distinction between an initial graph norm and uniformly equivalent graph
norms at all times matters without choice. The latter is a stronger explicit
hypothesis and excludes the counterexample below.

## The set and Hilbert space

Suppose A is an infinite Dedekind-finite subset of the real numbers: it has no
countably infinite subset. Two established ZF facts give a partition
A = ⋃ₙ Aₙ, indexed by positive integers, into nonempty sets, and imply that
every vector of ℓ²(A) has finite support. Specifically, linear order makes A
Cohen-finite, while second countability makes A weakly Dedekind-infinite;
Cohen-finiteness gives the finite-support property. The space ℓ²(A) is
uniformly complete. These facts, and the relative consistency of such A,
are proved in Blackadar–Farah–Karagila, Theorem 1.0.2, Propositions 3.0.4,
5.2.5, 5.2.8, 6.0.3, and §§5.5.2, 10.
[Hilbert Spaces Without Countable AC](https://arxiv.org/abs/2304.09602)

Set E = ℓ²(A; ℂ³), with its usual inner product. This finite Hilbert direct
sum is uniformly complete. Every vector has finite support in A. Let n(a)
be the unique positive integer with a ∈ Aₙ. No element of each Aₙ is chosen.

On the three-dimensional block at a ∈ Aₙ define

$$
H_n(0)=\operatorname{diag}(0,n^4,2n^4).
$$

Because every vector has finite support, this defines an everywhere-defined
operator H(0) on E, although it is unbounded in the physical norm. Set D = E
as a vector space and use the actual graph norm

$$
\|x\|_D^2=\|x\|_E^2+\|H(0)x\|_E^2.
$$

This is complete: multiplication on block n by

$$
W_n=\operatorname{diag}\bigl(1,\sqrt{1+n^8},\sqrt{1+4n^8}\bigr)
$$

is an explicit isometric bijection D → E. Both it and its inverse preserve
finite support. The inclusion D → E is continuous, injective, and surjective.
In particular, it has dense range.

## A C² Hamiltonian with a fixed gap

Let R₀₁(θ) and R₁₂(θ) be the real rotations through angle θ in the indicated
coordinate planes, regarded as unitary matrices. Use

$$
p(u)=10u^3-15u^4+6u^5\qquad(0\le u\le1).
$$

This increases from zero to one, and its first two derivatives vanish at both
endpoints. Define the Hamiltonian on block n in three stages:

$$
H_n(s)=
\begin{cases}
\operatorname{diag}(0,\lambda_n(s),2\lambda_n(s)),
  &0\le s\le\tfrac13,\\
R_{01}(\theta(s))\operatorname{diag}(0,1,2)R_{01}(\theta(s))^*,
  &\tfrac13\le s\le\tfrac23,\\
R_{12}(n\phi(s))\operatorname{diag}(1,0,2)R_{12}(n\phi(s))^*,
  &\tfrac23\le s\le1,
\end{cases}
$$

where

$$
\lambda_n(s)=(1-p(3s))n^4+p(3s),\qquad
\theta(s)=\frac\pi2 p(3s-1),\qquad
\phi(s)=(3s-2)^3.
$$

The values at the joins agree. Every block is Hermitian. For any v ∈ E,
H(s)v belongs to E, and the identity
⟨v,H(s)x⟩ = ⟨H(s)v,x⟩ holds by a finite sum. Consequently v belongs to the
adjoint domain with adjoint value H(s)v. This proves self-adjointness with
full physical domain E, without appealing to the closed graph theorem.

To check the required operator-norm regularity, weight every block on the
right by Wₙ⁻¹. On the first stage, the n⁴ coefficient is cancelled by this
weight, so the scalar C² bounds are uniform in n. On the second stage all
matrices and their derivatives are independent of n and Wₙ⁻¹ is contractive.

On the third stage, derivatives vanish on coordinate 0. For j = 1,2,3, the
jth derivative on coordinates 1 and 2 has norm at most Kⱼ nʲ, where Kⱼ is
independent of n and s: φ and its first three derivatives are bounded.
The corresponding weights in Wₙ are at least n⁴. For example, φ′ ≤ 9,
φ″ ≤ 54, and φ‴ = 162. Differentiating the two-dimensional rotation gives
a third-derivative bound
8(9n)³ + 12(9n)(54n) + 2(162n) ≤ 11988n³.
Thus the weighted third derivatives are bounded by 11988, as are the first
two derivatives by corresponding uniform constants.
The finite-dimensional Taylor remainder estimates are therefore uniform in
n. Summing their squared bounds over a vector's finite support proves twice
continuous differentiability in the norm of bounded maps D → E.
At s = 2/3, φ, φ′, and φ″ vanish. Together with the endpoint derivatives of
p, this verifies the C² joins as well. Extension to a neighborhood of [0,1]
is possible by keeping the initial stage constant to the left of zero and
continuing the last formula to the right of one.

At each time the block eigenvalues are zero and two numbers at least one.
Choose the fixed band (−1/2,1/2). Both boundaries have distance at least 1/2
from the physical spectrum. To verify this, let Σₛ be the closure of the block
eigenvalues. For z outside Σₛ, the inverse matrices have the uniform bound
1/dist(z, Σₛ), and their blockwise inverse defines a bounded inverse on E.
Conversely, every block eigenvalue belongs to the spectrum, and the spectrum
is closed. Hence the physical spectrum is exactly Σₛ. No D-valued bounded
inverse is used here.

The algebraic spectrum used in the
[Lean hypotheses](../../Adiabatic/Unbounded/Resolvent.lean) is the set of block
eigenvalues itself: away from these values, both the block map and its
algebraic inverse preserve finite support. It is therefore contained in the
physical spectrum just computed and satisfies the same gap condition.

Let P(s) be the orthogonal projection onto the zero eigenspaces. It is also
the physical Riesz projection obtained by integrating the bounded physical
resolvent on |z| = 1/2. The resolvent and its z-derivatives have uniform bounds
on that circle, so ordinary operator-norm Riemann sums justify the integral
and its evaluation block by block.

## The projection is not norm-continuous

Put s₀ = 2/3 and, for integers n ≥ 2, set

$$
s_n=\frac23+\frac13\left(\frac{\pi}{2n}\right)^{1/3}.
$$

Then sₙ → s₀ and nφ(sₙ) = π/2. On every block indexed by Aₙ, the selected
line at s₀ is coordinate 1, while at sₙ it is coordinate 2. Since Aₙ is
nonempty, a unit vector supported at one of its elements proves

$$
\|P(s_n)-P(s_0)\|=1.
$$

This is an individual existential argument for each n. It does not construct
a sequence of chosen elements of Aₙ. The upper bound follows directly from
the norm formula for the difference of rank-one orthogonal projections in
three dimensions, followed by the finite-support sum.

Thus H is C² in the initial graph norm and has a uniform gap, but its band
projection fails operator-norm continuity.

## Both uniform adiabatic estimates fail

Physical evolution still exists. For each n and T > 0, solve the explicit
three-dimensional matrix equation

$$
U_{T,n}'(s)=-iT H_n(s)U_{T,n}(s),\qquad U_{T,n}(0)=I.
$$

Picard iteration, using the specified continuous coefficients and their
Riemann integrals, gives a unique solution by factorial convergence estimates.
Finite-dimensional energy conservation makes it unitary. Unique replacement
assembles these solutions over n; their block action gives a unitary U_T(s)
on E. Every vector has finite support, so differentiation proves the strong
Schrödinger equation for every vector. The full physical domain is preserved.
No choice of a family of nonunique solutions is involved.
Coordinate projections of any other strong solution solve the same finite
equations, so this physical evolution is unique.
This constructs physical strong evolution. Its lift in the initial graph norm
can be unbounded; it is not asserted to satisfy Lean's bundled
`StrongPropagator` definition. The contradiction below concerns the physical
adiabatic estimates independently of that additional requirement.

For s,t ∈ [2/3,1], the physical Hamiltonians have norm at most 2. Integrating
the equation on a finite-support vector and taking the operator bound gives

$$
\|U_T(s)-U_T(t)\|\le2T|s-t|.
$$

Consequently Q_T(s) = U_T(s)P(0)U_T(s)* satisfies

$$
\|Q_T(s)-Q_T(t)\|\le4T|s-t|.
$$

If a constant C independent of T and s gave the projection-distance estimate,
the triangle inequality at sₙ and s₀ would imply

$$
1\le \frac{2C}{T}+4T|s_n-s_0|.
$$

For each fixed T, let n tend to infinity. This gives 1 ≤ 2C/T for every
T > 0, contradicted by T > 2C. In fact, for every T the supremum of the
projection-distance error on the last stage is at least 1/2.

The leakage estimate fails too. On each block, both P(s) and Q_T(s) have
rank one. For unit vectors u,v, direct calculation on their span gives

$$
\|uu^*-vv^*\|=\|(I-vv^*)uu^*\|
 =\sqrt{1-|\langle u,v\rangle|^2}.
$$

Taking the supremum over blocks, and using unitarity on the right, yields

$$
\|Q_T(s)-P(s)\|=\|(I-P(s))U_T(s)P(0)\|.
$$

Hence the same lower bound rules out a uniform C/T leakage estimate.

## The totalized contour formula also fails

The same family contradicts the continuity conclusion for the ZF translation
of the repository's literal projection formula.

[Resolvent.lean](../../Adiabatic/Unbounded/Resolvent.lean) defines the resolvent
set by algebraic bijectivity, but `inverseShift` takes the bounded inverse
$E\to D$ when one exists and zero otherwise.
[RieszProjection.lean](../../Adiabatic/Unbounded/RieszProjection.lean) integrates
its negative, composed with the inclusion. Interpret this convention in ZF
using the unique bounded inverse where it exists. Write $\widetilde P$ for
the resulting contour formula on $|z|=1/2$.

For $s<1/3$, set $c=1-p(3s)>0$. Then $\lambda_n(s)\ge c n^4$.
The weighted inverse blocks on the contour have norms at most

$$
\max\left(2,\frac{2\sqrt2}{c},\frac{\sqrt5}{c}\right).
$$

Indeed $|\lambda_n-z|\ge\lambda_n/2$ and
$|2\lambda_n-z|\ge\lambda_n$, while the two nontrivial graph weights are at
most $\sqrt2 n^4$ and $\sqrt5 n^4$. Thus the inverse is bounded into $D$,
and $\widetilde P(s)$ is the projection onto coordinate 0 on every block.

At $s_*=1/3$, the Hamiltonian is $\operatorname{diag}(0,1,2)$ on every block.
For a coordinate-1 unit vector in $A_n$, the unique algebraic inverse of
$H(s_*)-z$ has graph norm

$$
\frac{\sqrt{1+n^8}}{|1-z|}.
$$

This is unbounded in $n$. Hence no bounded inverse $E\to D$ exists at any
point of the contour. The totalized integrand is zero and
$\widetilde P(s_*)=0$. Consequently

$$
\|\widetilde P(s)-\widetilde P(s_*)\|=1\qquad(0\le s<1/3).
$$

The formula is not continuous, although the algebraic-spectrum gap and all
the input regularity assumptions hold. This argument refutes the ZF
translation of the literal projection conclusion without assuming a
`StrongPropagator`. It is a mathematical interpretation of the definitions,
not a Lean proof of a model of ZF.

## The choice consequence and its limits

If QAT held and some infinite subset of the reals were Dedekind-finite, the
construction above would contradict it. Therefore QAT implies that every
infinite subset of the reals is Dedekind-infinite. This finishes the proof.

The counterexample concerns the physical projection and physical evolution,
even when domain-preservation in the conclusion is read only as preservation
of the domain as a set. Adding bounded graph-norm lifts to the conclusion
cannot repair the failed estimates.

The mechanism remains a failure of graph-norm equivalence at later times.
After the first stage, H(s) is bounded in E, so its graph norm is equivalent
to the physical norm; it is not equivalent to the initial weighted graph
norm. In ZFC that situation is excluded by the bounded inverse theorem.
If equivalence with every later graph norm, or uniform graph-norm control,
is made an explicit hypothesis in ZF, this example is excluded. No necessity
claim for that stronger formulation is made here.
The separate [graph-control proof](graph-control.md) establishes that
stronger formulation in ZF for uniformly complete spaces, retaining the
algebraic-spectrum gap condition.

The physical estimates use the actual spectral projection. The separate
contour argument above shows that interpreting an unavailable bounded
domain-valued inverse as zero also contradicts the projection conclusion.

The existing Lean theorem and its axiom audit are unchanged. This proof
establishes necessity of the stated weak choice principle; it establishes
neither equivalence to that principle nor necessity of full AC.
