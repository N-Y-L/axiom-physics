# Common-domain quantum adiabatic theorem

`Adiabatic.Unbounded.common_domain_adiabatic_theorem` proves the gapped
adiabatic theorem for a possibly unbounded self-adjoint Hamiltonian on an
arbitrary complex Hilbert space. It constructs the spectral projection and
strong evolution from common-domain hypotheses and proves uniform $C/T$
bounds on projection distance and leakage. The declaration is in
[`Unbounded/MainTheorem.lean`](../Adiabatic/Unbounded/MainTheorem.lean).

This report describes the hypotheses, proof, and mathematical sources.

## Checked results

| Result | Status | Principal declaration |
| --- | --- | --- |
| Finite-dimensional theorem with a supplied smooth spectral projection | Proved | `finite_dimensional_adiabatic_theorem` |
| Bounded Hamiltonian in arbitrary dimension with a fixed isolating circle | Proved, including evolution existence | `bounded_adiabatic_theorem_of_resolvent_contour` |
| Unbounded, continuously moving gapped band: smooth orthogonal projection and common-domain lift | Proved | `GappedHamiltonian.spectralProjection_contDiff`, `spectralProjectionLift_contDiff` |
| Global continuously differentiable domain commutator solution | Proved from the actual spectral gap | `GappedHamiltonian.exists_contDiffOn_commutatorLift` |
| Uniform projection-distance and leakage estimates for supplied physical and Kato strong propagators | Proved | `GappedHamiltonian.exists_adiabatic_estimates_of_strong_propagators` |
| Full common-domain spectral theorem reduced to general evolution existence | Proved as an explicit implication | `commonDomainAdiabaticTheorem_of_evolution_existence` |
| General nonautonomous common-domain evolution existence | Proved from C¹ regularity and self-adjointness | `exists_nonautonomous_strongPropagator`, `common_domain_evolution_existence` |
| Full unbounded common-domain adiabatic theorem | Proved, including spectral and evolution constructions | `common_domain_adiabatic_theorem` |
| Uniqueness of physical strong evolution on the unit interval | Proved | `GappedHamiltonian.exists_unique_unitary_evolution` in `Unbounded/MainTheorem.lean` |

The final theorem derives propagator existence and the commutator solution.
Intermediate results state their supplied-propagator hypotheses explicitly.
The build and axiom audit are recorded in [verification.md](verification.md).

## Hypotheses

Let $E$ be a complex Hilbert space and $D$ a complete complex normed space.
A continuous injective map $j:D\to E$ has dense range. Each
$H(s):D\to E$ is bounded in the domain norm; the corresponding operator on
$E$ has domain $j(D)$ and sends $jx$ to $H(s)x$. This operator may be
unbounded in the physical Hilbert-space norm.

Self-adjointness means equality with the unbounded adjoint, including its
domain; the definition uses mathlib's partially defined linear maps.
The proof establishes equivalence of the given norm on $D$ with the graph
norm of each $H(s)$. Boundedness in the physical norm is not assumed.

On $I=[0,1]$, the input supplies $H\in C^2(I,B(D,E))$, continuous real
functions $a<b$, and $g>0$. Every spectral point $\lambda$ satisfies

$$
|\lambda-a(s)|\ge g,
\qquad |\lambda-b(s)|\ge g.
$$

The spectrum here is defined by failure of bounded invertibility of
$H(s)-zj:D\to E$, with invertibility derived from bijectivity by the Banach
inverse theorem. It is the spectrum of the unbounded operator represented
by the common domain. Self-adjointness proves it is real.

The selected region is the bounded interval between $a(s)$ and $b(s)$.
No finite-rank, eigenbasis, compact-resolvent, or discreteness assumption is
made. Crossings and continuous spectrum inside the selected band are
allowed. Empty bands are included; nonzero projections must be established in
applications.
Moving operator domains, unbounded selected half-lines, and gapless
evolution are outside this statement.

The constructed evolution satisfies

$$
\frac{d}{ds}U_T(s)jx=-iT H(s)U_{T,D}(s)x,
\qquad U_T(0)=I,
$$

where $jU_{T,D}(s)x=U_T(s)jx$. Differentiation is strong on domain vectors.
Both forward and inverse evolution preserve $j(D)$, and the domain lift is
strongly continuous in the norm of $D$. Operator-norm differentiation of
$U_T$ is neither required nor asserted.

The adiabatic theorem gives a constant $C\ge0$, independent of $T>0$, the
physical solution, and $s\in[0,1]$, such that

$$
\|U_T(s)P(0)U_T(s)^*-P(s)\|\le C/T,
\qquad
\|(I-P(s))U_T(s)P(0)\|\le C/T.
$$

The estimate concerns amplitudes and operator distance. Squaring its
state-vector consequence yields the familiar transition-probability rate;
a probability interpretation is not an additional formal declaration here.

## Comparison with the literature

Jansen, Ruskai, and Seiler's general assumptions use a fixed self-adjoint
domain, differentiability in its graph norm, and continuous boundaries
isolating a spectral band. Their Theorem 1 gives uniform first-order
adiabatic control on compact time intervals. Their Theorem 3 adds boundedness
and more specific spectral assumptions to obtain explicit constants. The
unbounded formalization follows the general Theorem 1 setting.[^1]

| Feature | Formal theorem compared with the general Jansen–Ruskai–Seiler setting |
| --- | --- |
| Common domain | Same physical condition; graph-norm equivalence is proved |
| Regularity | Twice continuous differentiability in $B(D,E)$ |
| Band boundaries | Continuous, with a uniform positive distance from spectrum |
| Strict versus non-strict gap | Equivalent after decreasing the positive gap |
| Empty band | Included formally; the paper specifies a nonempty band |
| Time interval | Normalized to $[0,1]$ |
| Constant | Existential; no sharp dependence on gap or derivatives claimed |

Kato's 1953 evolution paper constructs evolution from contraction generators
by controlling changes of graph coordinates. Its Theorem 4 gives strong
differentiability under regularity conditions on the relative operators;
the proof controls ordered products and their domain action. It supplies
the analytic strategy used here.[^2]

Schmid and Griesemer prove equivalence between the older Kato and Yosida
regularity conditions and strong continuous differentiability of $A(t)x$
for every domain vector. Their formulation explains why continuously
differentiable common-domain Hamiltonians are sufficient for the evolution
step. The formal theorem uses the stronger, directly usable operator-norm
$C^1$ condition in $B(D,E)$. The Kato-corrected Hamiltonian has this
regularity when the original spectral data are $C^2$.[^3]

Avron and Elgart prove adiabatic convergence without a spectral gap, with
no general rate in the basic conclusion. That theorem has different
hypotheses and is outside this formalization.[^4]

## Spectral construction without an eigenbasis

The fixed-domain resolvent is a map into the stronger space:

$$
R_D(z)=(H-zj)^{-1}:E\to D,
\qquad r(z)=jR_D(z):E\to E.
$$

The code proves the resolvent identities, the adjoint relation, smooth
dependence on $H$ and $z$, and nonreal invertibility from self-adjointness.
Keeping the domain-valued resolvent $R_D$ allows contour operators to be
composed with $H:D\to E$.

For a positively oriented circle $\Gamma$ in the resolvent set, define

$$
P=-\frac{1}{2\pi i}\oint_\Gamma r(z)\,dz,
\qquad
P_D=-\frac{1}{2\pi i}\oint_\Gamma R_D(z)\,dz.
$$

The minus sign corresponds to the convention $(H-zj)^{-1}$. The code proves
$jP_D=P$, $P^2=P=P^*$, and $HP_Dj=PH$.

To use mathlib's continuous functional calculus, the proof works with the
bounded normal operator $b=r(i)$. The rational expression

$$
b\big((z-i)b-I\big)^{-1}=-r(z)
$$

transfers the contour to the bounded algebra. For a nonzero spectral value
$w$ of $b$, the corresponding unbounded spectral value is $i+w^{-1}$.
The normalized scalar contour integral is the indicator of the selected
disk at this value, and is zero at $w=0$. This produces a continuous
functional-calculus description of $P$ and proves its orthogonality.
The argument includes accumulation of bounded-resolvent spectrum at zero.

This bridge is implemented in
[RieszProjection.lean](../Adiabatic/Unbounded/RieszProjection.lean) and
[ResolventSpectrum.lean](../Adiabatic/Unbounded/ResolventSpectrum.lean).
It avoids choosing eigenvectors and remains applicable when the selected
spectral subspace has infinite dimension.

## Moving bands and differentiability

The endpoints $a,b$ need not be differentiable. At each time, choose the
circle with center $(a+b)/2$ and radius $(b-a)/2$. The self-adjoint spectrum
is real, and the only real points on this circle are its two endpoints.
The gap therefore puts the whole circle in the resolvent set.

On a sufficiently small relative neighborhood of a fixed time, each
boundary moves by less than $g$. It cannot cross a spectral point. The
current circle and the fixed circle select the same subset of the current
spectrum. The functional-calculus description proves equality of their
physical projections; injectivity of $j$ proves equality of the domain
lifts.

For a fixed circle, smoothness is proved in the Banach algebra of continuous
operator-valued functions on that circle. Inversion is smooth at invertible
elements, and contour integration is a continuous linear map. This yields
$C^2$ regularity in both $B(E)$ and $B(E,D)$ and then transfers locally to
the moving band without differentiating its endpoints.

## A global commutator solution

Set $K=[P',P]$. On a valid fixed circle, the domain-valued contour operator

$$
X_D=-\frac{1}{2\pi i}\oint_\Gamma R_D(z)P'r(z)\,dz
$$

is continuously differentiable. Let $X=jX_D$. Resolvent cancellation gives
the domain identity

$$
HX_Dj-XH=Kj.
$$

Local circles need not be the same throughout the interval. A finite smooth
partition of unity combines the local solutions. The commutator equation
is real-linear in $X_D$, so weights summing to one preserve it. Smooth
weights have support inside regions where each local construction is
valid. This produces a global $C^1$ domain lift even when no single circle
isolates the band throughout the interval.

Compactness bounds $X$, $X'$, and $K$. They are constructed independently of
$T$, giving a comparison constant uniform in runtime and solution.

## Strong evolution foundations

Symmetric resolvent regularization produces bounded self-adjoint
Hamiltonians. In scalar notation, with $a=n+1$,

$$
H_n=\frac{a^2}{2}\big((H-ia)^{-1}+(H+ia)^{-1}\big).
$$

The definition uses physical resolvents. The $H_n$ commute with each other
and with the resolvent, and $H_njx\to Hx$ for every $x\in D$. Their unitary
exponentials converge strongly. The proof establishes the limit's unitarity,
group law, domain preservation, and strong differential equation.

For time-dependent $H$, freeze $H$ on a fine partition and compose the
autonomous groups in time order. Right derivatives accommodate the partition
boundaries. Estimates use the $B(D,E)$ norm and shifted graph coordinates.

Supporting results include graph-norm equivalence, uniform bounds
for reference resolvents, relative Hamiltonian-change bounds, exponential
graph bounds for ordered products, comparison of right strong propagators,
and strong limits on the physical space. Forward and inverse approximations
must both be controlled: a strong limit of unitary operators alone need not
be surjective. Domain recovery uses self-adjointness and graph bounds.
Domain continuity and strong differentiation complete the construction of
a `StrongPropagator`.

`FrozenApproximation.lean` constructs the full family of time-sliced
evolutions and their uniform estimates from $C^1$ regularity and
self-adjointness. `GraphLimit.lean` transfers the sharp two-time graph
estimate to the limit. Its prefactor tends to one as the two times approach
one another, which upgrades physical continuity to strong continuity in
the common-domain norm.

`Nonautonomous.lean` compares the limiting curve locally with the
autonomous group of the Hamiltonian frozen at the current time. The
remainder is $O(|s-t|^2)$ on each initial domain vector, so both curves have
the same derivative. This proves the strong Schrödinger equation throughout
the closed interval, with one-sided derivatives at its endpoints.

The resulting declaration `exists_nonautonomous_strongPropagator` has only
$C^1$ common-domain regularity, self-adjointness, and a purely imaginary
generator scale as hypotheses. `common_domain_evolution_existence`
specializes it to $-iT$. Both forward and inverse evolution preserve the
full common domain.

## From evolution existence to the adiabatic theorem

The spectral construction proves that $K\in C^1(I,B(E))$ and $K^*=-K$.
For $z=-iT$, define

$$
H_A=H+(z^{-1}K)j=H+\frac{i}{T}Kj.
$$

A bounded-perturbation argument proves self-adjointness of
$H_A$ on the same full domain. Its common-domain regularity is $C^1$.
Consequently, a generic $C^1$ self-adjoint evolution theorem supplies both
the physical propagator and the Kato propagator. Repackaging the latter
gives $V'=(-iTH+K)V$ on domain vectors with unchanged evolution maps.

Strong differentiation on the dense domain proves $P(s)V(s)=V(s)P(0)$.
A corrected comparison curve gives $\|U_T-V_T\|\le C_0/T$. Orthogonal
projection contraction then controls leakage; expanding the difference of
the transported projections gives at most $2C_0/T$. Choosing $C=2C_0$
provides both estimates with the same constant.

The intermediate declaration
[`commonDomainAdiabaticTheorem_of_evolution_existence`](../Adiabatic/Unbounded/GappedReduction.lean)
implements this reduction. `common_domain_adiabatic_theorem` in
[`Unbounded/MainTheorem.lean`](../Adiabatic/Unbounded/MainTheorem.lean)
applies it to `common_domain_evolution_existence`. The same module proves
`GappedHamiltonian.exists_unique_unitary_evolution`, with uniqueness among
strong unitary common-domain propagators on $[0,1]$.

## Verification

The implementation is pinned to Lean `v4.28.0` and mathlib commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. The final mechanical build and
transitive axiom audit are recorded in [verification.md](verification.md).
That record identifies the audited declarations and distinguishes local
verification from external review or a hosted workflow run.

The quantifier order is $\exists C\,\forall T\,\forall U\,\forall s$, with
$T>0$ and $s\in[0,1]$. Existence of the physical evolution is proved, so the
estimate applies to a nonempty class of propagators.

Explicit gap-dependent constants, concrete unbounded examples, unions of
bounded bands, and other adiabatic regimes remain further work.

## Sources

[^1]: Sabine Jansen, Mary-Beth Ruskai, and Ruedi Seiler, [*Bounds for the adiabatic approximation with applications to quantum computation*](https://arxiv.org/pdf/quant-ph/0603175v3), *Journal of Mathematical Physics* 48, 102111 (2007), Sections II–III. Version 3, 8 November 2007. Used for the general common-domain assumptions and distinction between Theorems 1 and 3.

[^2]: Tosio Kato, [*Integration of the equation of evolution in a Banach space*](https://www.jstage.jst.go.jp/article/jmath1948/5/2/5_2_208/_pdf), *Journal of the Mathematical Society of Japan* 5, 208–234 (1953), Theorems 3–4 and Section 3. Original publisher-hosted article.

[^3]: Jochen Schmid and Marcel Griesemer, [*Kato's Theorem on the Integration of Non-Autonomous Linear Evolution Equations*](https://arxiv.org/pdf/1203.4700v3), version 3, 22 June 2014, Introduction, Proposition 2.1, and Theorem 2.2. Used for the equivalence of the classical regularity conditions.

[^4]: J. E. Avron and A. Elgart, [*Adiabatic Theorem without a Gap Condition*](https://arxiv.org/abs/math-ph/9805022v4), *Communications in Mathematical Physics* 203, 445–463 (1999), version 4, 19 April 1999. Used to distinguish the gapless target.

Library sources are pinned in `lake-manifest.json`.
