# Common-domain quantum adiabatic theorem

The extension proves the gapped adiabatic theorem for a possibly unbounded
self-adjoint Hamiltonian on an arbitrary complex Hilbert space. It
constructs the moving spectral projection and the nonautonomous strong
evolution from the common-domain hypotheses, then proves uniform
inverse-runtime estimates for projection distance and leakage. The main
declaration is `Adiabatic.Unbounded.common_domain_adiabatic_theorem` in
[`Unbounded/MainTheorem.lean`](../Adiabatic/Unbounded/MainTheorem.lean).

This report describes the mathematical scope, the relationship to the
literature, and the verified dependencies. The separate
[prior-art assessment](prior-art.md) records the public-source search and its
limits. No claim of worldwide priority follows from that search.

## Results and proof status

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

The intermediate declarations keep their supplied-propagator hypotheses
visible. The final theorem discharges them using the independently proved
nonautonomous existence theorem. The concluding statement assumes neither a
propagator nor a commutator solution. The mechanical build and axiom audit
are recorded in [verification.md](verification.md).

## Mathematical scope

Let $E$ be a complex Hilbert space and $D$ a complete complex normed space.
A continuous injective map $j:D\to E$ has dense range. Each
$H(s):D\to E$ is bounded in the domain norm; the corresponding operator on
$E$ has domain $j(D)$ and sends $jx$ to $H(s)x$. This operator may be
unbounded in the physical Hilbert-space norm.

Self-adjointness means equality with the actual unbounded adjoint, including
equality of domains. The formal definition uses mathlib's partially defined
linear maps. Symmetry of the inner product alone would be insufficient.
The checked graph equivalence identifies the chosen complete norm on $D$
with the graph norm of each self-adjoint $H(s)$, so introducing an abstract
domain space does not silently assume bounded physical Hamiltonians.

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
No finite rank, eigenbasis, compact-resolvent, or discreteness assumption is
made. Crossings and continuous spectrum inside the selected band are
allowed. Empty bands are included; nontrivial applications require an
independent example showing that the constructed projection is nonzero.
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

The spectral theorem chooses a single finite $C\ge0$ before $T$, the physical
solution, and $s$. It bounds both

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

Kato's 1953 evolution paper supplies the historical common-domain route:
construct evolution from contraction generators and control changes of graph
coordinates. Its Theorem 4 gives strong differentiability under regularity
conditions on the relative operators; the proof controls ordered products
and their domain action. This is a source of the analytic strategy, not a
Lean dependency or an imported existence axiom.[^2]

Schmid and Griesemer prove equivalence between the older Kato and Yosida
regularity conditions and strong continuous differentiability of $A(t)x$
for every domain vector. Their formulation explains why continuously
differentiable common-domain Hamiltonians are sufficient for the evolution
step. The formal theorem uses the stronger, directly usable operator-norm
$C^1$ condition in $B(D,E)$. The Kato-corrected Hamiltonian has this
regularity when the original spectral data are $C^2$.[^3]

Avron and Elgart address a different question: adiabatic convergence without
a spectral gap. Their basic conclusion has no general rate without further
information. That result does not justify replacing the uniform gap in the
present theorem with mere smoothness. The common-domain evolution theorem
used here is proved separately in Lean.[^4]

## Spectral construction without an eigenbasis

The fixed-domain resolvent is a map into the stronger space:

$$
R_D(z)=(H-zj)^{-1}:E\to D,
\qquad r(z)=jR_D(z):E\to E.
$$

The code proves the resolvent identities, the adjoint relation, smooth
dependence on $H$ and $z$, and nonreal invertibility directly from genuine
self-adjointness. The distinction between $R_D$ and $r$ is retained
throughout the proof. It ensures that contour operators can subsequently
be composed with the unbounded Hamiltonian.

For a positively oriented circle $\Gamma$ in the resolvent set, define

$$
P=-\frac{1}{2\pi i}\oint_\Gamma r(z)\,dz,
\qquad
P_D=-\frac{1}{2\pi i}\oint_\Gamma R_D(z)\,dz.
$$

The minus sign corresponds to the convention $(H-zj)^{-1}$. The code proves
$jP_D=P$, $P^2=P=P^*$, and $HP_Dj=PH$. These are derived properties of the
integral, not assumptions attached to a projection symbol.

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
circle with center $(a+b)/2$ and radius $(b-a)/2$. A self-adjoint spectrum
meets the real line, and the only real points on this circle are its two
endpoints. The gap therefore puts the whole circle in the resolvent set.

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
the moving band. There is no differentiation of a merely continuous choice
of endpoints.

## A global commutator solution

Set $K=[P',P]$. On a valid fixed circle, the domain-valued contour operator

$$
X_D=-\frac{1}{2\pi i}\oint_\Gamma R_D(z)P'r(z)\,dz
$$

is continuously differentiable. Let $X=jX_D$. Resolvent cancellation gives
the actual domain identity

$$
HX_Dj-XH=Kj.
$$

Local circles need not be the same throughout the interval. A finite smooth
partition of unity combines the local solutions. The commutator equation
is real-linear in $X_D$, so weights summing to one preserve it. Smooth
weights have support inside regions where each local construction is
valid. This produces a global $C^1$ domain lift, with no assumption that
one circle works for all time.

Compactness bounds $X$, $X'$, and $K$ independently of runtime. Their
construction occurs entirely before choosing $T$. The quantitative
comparison argument therefore yields a single constant for all runtimes,
rather than a separately chosen constant for each solution.

## Strong evolution foundations

The autonomous construction is checked. Symmetric resolvent regularization
produces bounded self-adjoint Hamiltonians. In ordinary scalar notation,
with $a=n+1$, the regularization is

$$
H_n=\frac{a^2}{2}\big((H-ia)^{-1}+(H+ia)^{-1}\big).
$$

The formal definition uses physical resolvents and never forms an
unjustified product of unbounded operators. The $H_n$ commute with each
other and with the resolvent; $H_njx\to Hx$ for every $x\in D$. Bounded
unitary exponentials converge strongly to an autonomous unitary group.
The code then proves its group law, domain preservation, and the strong
differential equation. Thus the autonomous group is constructed rather than
assumed through an informal reference to Stone's theorem.

For time-dependent $H$, the construction follows a separate
approximation in time. Freeze $H$ on a fine partition and compose the
autonomous groups in time order. A right-derivative interface accommodates
the partition boundaries. Estimates use the norm $B(D,E)$ and shifted graph
coordinates, not the nonexistent bounded-operator norm of an unbounded
$H$ on $E$.

Supporting results include graph-norm equivalence, uniform bounds
for reference resolvents, relative Hamiltonian-change bounds, exponential
graph bounds for ordered products, comparison of right strong propagators,
and strong limits on the physical space. Forward and inverse approximations
must both be controlled: a strong limit of unitary operators alone need not
be surjective. Domain recovery uses self-adjointness and graph bounds.
The limiting curve's domain continuity and strong derivative are then
established before it inhabits `StrongPropagator`.

`FrozenApproximation.lean` constructs the full family of time-sliced
evolutions and their uniform estimates from $C^1$ regularity and
self-adjointness. `GraphLimit.lean` transfers the sharp two-time graph
estimate to the limit. Its prefactor tends to one as the two times approach
one another, which upgrades physical continuity to strong continuity in
the common-domain norm.

`Nonautonomous.lean` compares the limiting curve locally with the
autonomous group of the Hamiltonian frozen at the current time. The
remainder is $O(|s-t|^2)$ on each initial domain vector, so both curves have
the same derivative. This proves the actual strong Schrödinger equation
throughout the closed interval, with the appropriate one-sided derivatives
at its endpoints. It does not pass an unbounded Hamiltonian through a
physical-space limit without domain control.

The resulting declaration `exists_nonautonomous_strongPropagator` has only
the stated $C^1$ common-domain regularity, genuine self-adjointness, and a
purely imaginary generator scale as hypotheses. `common_domain_evolution_existence`
specializes it to $-iT$. Both forward and inverse evolution preserve the
full common domain.

## From evolution existence to the adiabatic theorem

The spectral part already proves that $K\in C^1(I,B(E))$ and $K^*=-K$.
For $z=-iT$, define

$$
H_A=H+(z^{-1}K)j=H+\frac{i}{T}Kj.
$$

A checked bounded-perturbation argument proves genuine self-adjointness of
$H_A$ on the same full domain. Its common-domain regularity is $C^1$.
Consequently, a generic $C^1$ self-adjoint evolution theorem supplies both
the physical propagator and the Kato propagator. Repackaging the latter
gives $V'=(-iTH+K)V$ on domain vectors with unchanged evolution maps.

Strong differentiation on the dense domain proves $P(s)V(s)=V(s)P(0)$.
A corrected comparison curve gives $\|U_T-V_T\|\le C_0/T$. Orthogonal
projection contraction then controls leakage; expanding the difference of
the transported projections gives at most $2C_0/T$. Choosing $C=2C_0$
provides both advertised estimates with the same constant.

The intermediate declaration
[`commonDomainAdiabaticTheorem_of_evolution_existence`](../Adiabatic/Unbounded/GappedReduction.lean)
implements this reduction. `common_domain_adiabatic_theorem` in
[`Unbounded/MainTheorem.lean`](../Adiabatic/Unbounded/MainTheorem.lean)
applies it to `common_domain_evolution_existence`, completing the proof from
the advertised Hamiltonian and gap assumptions. The same module proves
`GappedHamiltonian.exists_unique_unitary_evolution`, with uniqueness among
strong unitary common-domain propagators on $[0,1]$.

## Verification and scope

The implementation is pinned to Lean `v4.28.0` and mathlib commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. The final mechanical build and
transitive axiom audit are recorded in [verification.md](verification.md).
That record identifies the audited declarations and distinguishes local
verification from external review or a hosted workflow run.

The final theorem retains the order
$\exists C\,\forall T\,\forall U\,\forall s$. Its constant is independent of
runtime, solution, and time. Evolution existence is derived before the
quantitative conclusion, so the universal estimate is not vacuous for lack
of a physical propagator. The regularity and uniform spectral-gap
hypotheses remain explicit mathematical assumptions.

Further mathematical work can add explicit gap-dependent constants,
concrete unbounded examples, unions of bounded spectral bands, or other
adiabatic regimes. Those are separate extensions. They should not be
described as consequences already checked by this theorem.

## Sources

[^1]: Sabine Jansen, Mary-Beth Ruskai, and Ruedi Seiler, [*Bounds for the adiabatic approximation with applications to quantum computation*](https://arxiv.org/pdf/quant-ph/0603175v3), *Journal of Mathematical Physics* 48, 102111 (2007), Sections II–III. Version 3, 8 November 2007. Used for the general common-domain assumptions and distinction between Theorems 1 and 3.

[^2]: Tosio Kato, [*Integration of the equation of evolution in a Banach space*](https://www.jstage.jst.go.jp/article/jmath1948/5/2/5_2_208/_pdf), *Journal of the Mathematical Society of Japan* 5, 208–234 (1953), Theorems 3–4 and Section 3. Original publisher-hosted article.

[^3]: Jochen Schmid and Marcel Griesemer, [*Kato's Theorem on the Integration of Non-Autonomous Linear Evolution Equations*](https://arxiv.org/pdf/1203.4700v3), version 3, 22 June 2014, Introduction, Proposition 2.1, and Theorem 2.2. Used for the equivalence of the classical regularity conditions.

[^4]: J. E. Avron and A. Elgart, [*Adiabatic Theorem without a Gap Condition*](https://arxiv.org/abs/math-ph/9805022v4), *Communications in Mathematical Physics* 203, 445–463 (1999), version 4, 19 April 1999. Used to distinguish the gapless target.

The implementation claims are supported by the linked project declarations,
not by the literature citations. The reusable library sources are pinned in
`lake-manifest.json`; the prior-art report distinguishes its search revision
from the implementation revision.
