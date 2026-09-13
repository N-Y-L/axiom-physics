# Proof architecture: finite-dimensional quantum adiabatic theorem

Research date: 2026-09-13. The finite-dimensional adiabatic theorem is proved
in `Adiabatic/MainTheorem.lean`. This document explains the proof and separates
its checked statements from informal consequences and proposed extensions.
See [verification.md](verification.md) for the exact scope and audit results.

## Proved statement and conventions

Let $E$ be a finite-dimensional complex Hilbert space, and use the
operator norm on $B(E)$. Time is the real variable $s\in[0,1]$; the runtime is
$T>0$. Set $\hbar=1$ and use $[A,B]=AB-BA$. Products are compositions,
with the rightmost operator acting first. The physical equation is

$$
U_T'(s)=-iT H(s)U_T(s),\qquad U_T(0)=I.
$$

The paths $H$ and $P$ are fixed independently of $T$.

**Formalized hypotheses.** Let $H,P:\mathbb R\to B(E)$ be globally $C^2$ paths.
For every real time, assume $H^*=H$, $P^*=P$, $P^2=P$, and $HP=PH$.

On $[0,1]$, assume a fixed $g>0$ separates every eigenvalue of $H$ in
$\operatorname{range}P$ from every eigenvalue in $\ker P$. This eigenvalue
formulation is the definition `HasUniformSpectralGap` in `Statement.lean`.

The selected subspace may have arbitrary rank, with eigenvalue crossings
inside either sector. The eigenvalue condition is vacuous for a trivial
projection, and the theorem includes those cases and the zero-dimensional
space. `MainTheorem.lean` constructs the physical evolution and proves that
there is a constant $C\ge0$, chosen before the runtime and the solution, such
that every physical solution satisfies, for every $T>0$ and $s\in[0,1]$,

$$
\|(I-P(s))U_T(s)P(0)\|\le C/T.
$$

`Schrodinger.lean` separately proves uniqueness on $[0,1]$ and unitarity.
The main theorem's conclusion is the operator leakage estimate above.

**Informal consequences, not additional checked declarations.** A normalized
initial state in $\operatorname{range}P(0)$ has leakage probability at most
$C^2/T^2$. The comparison proof also gives

$$
\|U_T(s)P(0)U_T(s)^*-P(s)\|\le 2C/T.
$$

Here $C$ may be taken to be the comparison constant constructed in the proof;
the factor $2$ is not optimal. Formal probability, projection-distance, and
limit corollaries remain extensions. Construction of the $C^2$ projection
path from the Hamiltonian and an isolated spectral-band selection rule also
remains separate. The current theorem supplies both smooth paths as input.
Its global regularity assumptions are stronger than regularity on a
neighborhood of $[0,1]$.

Jansen–Ruskai–Seiler state quantitative band versions and permit crossings
within the band; their Theorem 3 gives substantially sharper derivative and
gap dependence than the elementary constants proposed here. Their convention
for scaled Schrödinger evolution agrees with the one above.
[Primary source, Sections II–III](https://arxiv.org/pdf/quant-ph/0603175).

## First intermediate theorem: actual evolution plus a commutator solution

The checked comparison estimate in `Comparison.lean` works in a complex
operator algebra without finite dimensionality. Its inputs are:

1. $U,V,X$ have real derivatives within the closed interval, including its
   endpoints.
2. $U,V$ are unitary, $U(0)=V(0)=I$, and
   $U'=-iTHU$, $V'=(-iTH+K)V$.
3. $H^*=H$, $K^*=-K$, and $[H,X]=K$ at each time.
4. Uniform bounds $\|X\|\le M_X$, $\|X'\|\le M_D$, and
   $\|K\|\le M_K$ hold. For a family of runtimes, these data and bounds
   are independent of $T$.

The intermediate conclusion is

$$
\|U(s)-V(s)\|
\le\frac{2M_X+s(M_D+M_KM_X)}{T}
\le\frac{2M_X+M_D+M_KM_X}{T}.
$$

This intermediate theorem assumes the commutator solution and the two
unitary evolutions. In the full theorem, `SpectralGap.lean` and
`Regularity.lean` construct the solution from the gap; `Propagator.lean` and
`Transport.lean` construct the evolutions and derive unitarity. The final
estimate is never assumed.

### Derivation with a corrected wave operator

The following calculation spells out the sign choices and reduces the proof
to ordinary derivative rules and a mean-value inequality. Define

$$
\Omega=V^*U,\qquad B=V^*XU,\qquad F=\Omega-\frac{i}{T}B.
$$

From the equations and the adjoint relations,

$$
(V^*)'=V^*(iTH-K),\qquad
\Omega'=-V^*KU,
$$

and hence

$$
\begin{aligned}
B'&=V^*(iTH-K)XU+V^*X'U-iT V^*XHU\\
  &=iT V^*[H,X]U+V^*(X'-KX)U\\
  &=iT V^*KU+V^*(X'-KX)U.
\end{aligned}
$$

Since $i^2=-1$, cancellation gives

$$
F'=-\frac{i}{T}V^*(X'-KX)U.
$$

Unitary invariance and submultiplicativity imply

$$
\|F'(s)\|\le (M_D+M_KM_X)/T.
$$

The mean-value inequality bounds $\|F(s)-F(0)\|$ by $s$ times this quantity.
Using $\Omega(0)=I$, $\|B(s)\|\le M_X$, and $\|B(0)\|\le M_X$ gives the
estimate for $\Omega-I$; multiplication by $V$ gives the estimate for $U-V$.
This is the implementation in `Evolution.lean` and `Bounds.lean`.

This argument is a mean-value implementation of the commutator method.
Avron–Elgart's Lemma 1 allows an additional commutator residual and uses
integration by parts to estimate the evolution difference. Its gap case has
zero residual and yields inverse-runtime convergence.
[Primary source, Section 4](https://arxiv.org/pdf/math-ph/9805022).

## Second intermediate theorem: Kato transport

Let $P$ be a differentiable orthogonal projection path, and write
$D=P'$, $Q=I-P$, and $K=DP-PD$. Differentiating $P^2=P$ yields

$$
DP+PD=D,\quad PDP=0,\quad QDQ=0,\quad [K,P]=D.
$$

Real differentiation of $P^*=P$ gives $D^*=D$, so $K^*=-K$. If $HP=PH$, the
derivative of $V^*PV$ for the adiabatic evolution is

$$
(V^*PV)'=V^*(D+PK-KP) V=0.
$$

Its initial value is $P(0)$. Thus $P(s)V(s)=V(s)P(0)$, as proved from the
differential equation in `Transport.lean`. It follows that

$$
Q(s)U(s)P(0)=Q(s)(U(s)-V(s))P(0).
$$

Orthogonal projections are contractions, giving the checked leakage bound
in `Leakage.lean`. For the proposed projection-distance corollary, expand the
difference between $UP(0)U^*$ and $VP(0)V^*$ into two terms, each bounded by
$\|U-V\|$.

## Constructing the commutator solution from the gap

### General spectral cluster: an inverse on a fixed operator space

The proof defines superoperators on the fixed vector space $B(E)$:

$$
\begin{aligned}
O_P(A)&=PAQ+QAP,\\
D_P(A)&=PAP+QAQ,\\
\mathcal L_{H,P}(A)&=D_P(A)+[H,O_P(A)].
\end{aligned}
$$

Because $HP=PH$, the commutator preserves diagonal and off-diagonal blocks.
On diagonal blocks $\mathcal L$ is the identity. Its kernel therefore
consists of off-diagonal operators commuting with $H$. In `SpectralGap.lean`,
sector separation shows that such an operator annihilates every vector in
an orthonormal eigenbasis of $H$. Hence the kernel is zero, and finite
dimensionality gives invertibility. This uses an eigenbasis only at a fixed
time; no differentiable eigenvector choice is required. Set

$$
X=\mathcal L_{H,P}^{-1}(K).
$$

Since $K$ is off-diagonal, $X$ is off-diagonal and $[H,X]=K$.
The paths $\mathcal L$ and $K$ are $C^1$ when $H$ is $C^1$ and $P$ is $C^2$.
Smooth inversion gives $X\in C^1$. `Regularity.lean` proves these claims
within the unit interval and obtains finite bounds on $X$, $X'$, and $K$
by compactness. The bounds are independent of $T$.

This construction is part of the checked full theorem. Explicit gap
constants are a proposed extension. Informally, eigenbasis coordinates give
$\|X\|_{\mathrm{HS}}\le\|K\|_{\mathrm{HS}}/g$ in the Hilbert–Schmidt norm;
conversion to the operator norm introduces dimension factors. This estimate
is not formalized here. The proof does not assume an operator-norm estimate
$\|X\|\le\|K\|/g$ for arbitrary separated spectral sets.

### Reduced resolvent: checked algebra and proposed estimates

For one isolated eigenvalue, possibly degenerate, assume $HP=eP$ for a real
$C^2$ function $e$, with the complement at distance at least $g$ from $e$.
Put

$$
A=H-eI+P,\qquad R=A^{-1}-P.
$$

Given the augmented inverse, `ReducedResolvent.lean` proves $RP=PR=0$ and
$(H-eI)R=R(H-eI)=Q$. It also proves that

$$
X=RDP+PDR.
$$

solves $[H,X]=DP-PD$. This algebraic special case is independent of the
general-cluster proof used in the main theorem.

The remaining calculations in this subsection are informal, proposed
extensions. The spectral bound is $\|R\|\le1/g$. Let $r=1/g$ and assume
uniform bounds $\|P'\|\le p_1$, $\|P''\|\le p_2$, $\|H'\|\le h_1$, and
$|e'|\le e_1$. Differentiating the reduced resolvent identities gives

$$
R'=-R(H'-e'I)R-RP'-P'R.
$$

The product rule and norm inequalities then give the nonoptimal bounds

$$
M_X=2rp_1,\qquad M_K=2p_1,
$$

$$
M_D=2r^2(h_1+e_1)p_1+6rp_1^2+2rp_2,
$$

which would specialize the comparison constant to

$$
C=4rp_1+2rp_2+10rp_1^2+2r^2(h_1+e_1)p_1.
$$

The reduced-resolvent derivative formula and these explicit constants are
not checked declarations. They are not the sharper literature constants.

## Lean representation and proved modules

The implementation uses `E →L[ℂ] E` with its operator norm. The example uses
`EuclideanSpace ℂ (Fin 2)`. All time differentiation is over $\mathbb R$,
with the complex scalar action restricted to real scalars.

The following modules are proved and compiled:

| Module | Proved role |
| --- | --- |
| [Projection.lean](../Adiabatic/Projection.lean) | Projection derivative identities and skew-adjointness of the Kato generator. |
| [SpectralGap.lean](../Adiabatic/SpectralGap.lean) | Sector separation implies invertibility of $\mathcal L$ and an algebraic commutator solution. |
| [Regularity.lean](../Adiabatic/Regularity.lean) | The constructed commutator path is $C^1$; compactness bounds it and its derivative. |
| [Propagator.lean](../Adiabatic/Propagator.lean) | A factorial Picard-iterate estimate constructs evolution on the whole unit interval, without a smallness hypothesis. |
| [Transport.lean](../Adiabatic/Transport.lean) | Skew-adjoint evolution is unitary in finite dimension and Kato evolution intertwines projections. |
| [Evolution.lean](../Adiabatic/Evolution.lean), [Bounds.lean](../Adiabatic/Bounds.lean), [Comparison.lean](../Adiabatic/Comparison.lean) | Derivative cancellation and the mean-value inequality give the comparison bound. |
| [Leakage.lean](../Adiabatic/Leakage.lean), [CommutatorTheorem.lean](../Adiabatic/CommutatorTheorem.lean) | Exact transport and contraction bounds give uniform leakage from a smooth commutator solution. |
| [MainTheorem.lean](../Adiabatic/MainTheorem.lean) | The spectral assumptions imply existence of physical evolution and the uniform $C/T$ leakage estimate. |
| [Schrodinger.lean](../Adiabatic/Schrodinger.lean), [Examples.lean](../Adiabatic/Examples.lean) | Explicit existence, uniqueness, and unitarity statements; a nontrivial two-level gapped example. |

The mathlib foundations below were inspected at the pinned commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

Pinned primary sources:
[derivative multiplication](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Analysis/Calculus/Deriv/Mul.lean),
[adjoint differentiation](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Analysis/Calculus/Deriv/Star.lean),
[mean value inequality](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Analysis/Calculus/MeanValue.lean),
[Picard–Lindelöf](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Analysis/ODE/PicardLindelof.lean),
[Gronwall and uniqueness](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Analysis/ODE/Gronwall.lean),
[smooth inversion](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Analysis/Calculus/ContDiff/Operations.lean),
[spectral theorem](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Analysis/InnerProductSpace/Spectrum.lean).

Current online mathlib documentation may describe a later layout, including
`Analysis/ODE/ExistUnique.lean`; that file is absent from this pinned checkout.
The pinned sources and compiled theorem types govern the implementation.
In particular, `exists_contDiffOn_commutator_of_spectral_separation`
constructs a $C^1$ path satisfying $[H,X]=[P',P]$, where $P'$ is
`derivWithin P s`, from $H\in C^1$, $P\in C^2$, and pointwise sector
separation on a domain with unique derivatives.

## Verification and extensions

The completed main proof derives the commutator solution, both evolutions,
unitarity, exact transport, and the leakage estimate. The source and axiom
checks are described in [verification.md](verification.md). Construction of
the projection from the Hamiltonian alone, formal probability and
projection-distance corollaries, weaker regularity assumptions, and explicit
gap-dependent constants remain extensions.
