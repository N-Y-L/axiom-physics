# Analytic constructions under graph control

The full common-domain theorem follows in classical ZF once the supplied
Banach domain norm satisfies the pointwise graph inequality (1) below.
This proof constructs the projection, evolution, domain lifts, and both
uniform adiabatic estimates. It is a written mathematical argument, not
a Lean formalization of ZF. The existing Lean theorem still uses
`Classical.choice`.

The graph inequality follows from [countable choice](countable-choice.md),
from the [Banach-to-Hilbert bounded inverse principle](bounded-inverses.md),
or under the [restriction on the physical space](separable-spaces.md).
It is an additional premise when working over arbitrary spaces in ZF.

## Assumptions and completeness

The physical space $E$ is an arbitrary uniformly complete complex Hilbert
space. $D$ is an arbitrary uniformly complete complex Banach space, with
its original supplied norm. The bounded map $j:D\to E$ is injective and has
dense range. No Hilbert structure or separability is assumed on $D$. If $E$
is zero, injectivity makes $D$ zero and all conclusions are immediate;
subsequent spectral arguments may therefore assume $E$ is nonzero.

$H$ is $C^2$ in the norm of bounded maps $D\to E$ on the closed unit interval; its
physical operator on $j(D)$ is self-adjoint in the maximal adjoint-domain
sense. The band endpoints $a(t)<b(t)$ are continuous, and a fixed $g>0$
bounds both endpoint distances from the algebraic spectrum below at every
time. That spectrum is the complement of algebraic bijectivity of $H-zj$.
The projection uses the repository's totalized inverse of a bounded map.
An algebraic inverse cannot silently be substituted for that inverse.

The required evolution is a bounded physical unitary at each time, with
bounded forward and inverse $D\to D$ lifts, physical strong continuity,
forward strong $D$-continuity, and the strong equation for every initial
vector $jx$ with $x\in D$. The estimates quantify over every such propagator,
with one $C$ independent of positive $T$ and of time. The companion uniqueness
theorem asserts equality on $[0,1]$, not of arbitrary extensions outside that
interval. Curves can be assigned explicit values outside $[0,1]$.

Uniform completeness is retained throughout. Under ZF it must not be
replaced without proof by sequential completeness. The equivalence with
the shrinking-closed-sets formulation, Hilbert projection, and Riesz
representation are the results of Blackadar, Farah, and Karagila,
*Hilbert Spaces Without the Countable Axiom of Choice*, Theorem 1.0.2
and Theorem 2.0.4,
Corollary 2.0.5, and Theorem 2.0.6. Their Proposition 7.0.1 and §7.0.3
give operator completeness and the $C^*$-algebra structure.
[Primary paper, arXiv:2304.09602v3](https://arxiv.org/html/2304.09602v3)

## Elementary complete-space infrastructure

For a bounded linear map $A:V\to Y$ on a dense linear subspace $V$ of $X$, with
$Y$ uniformly complete and $\|Av\|\le M\|v\|$, define for each fixed $x\in X$

$$
C_n(x)=\overline{\{Av:v\in V,\ \|v-x\|<1/n\}},\qquad n\ge1.
$$

These sets are nonempty, closed, decreasing, and have diameter at most
$2M/n$. Their unique common point is the extended value. Finite
approximations verify linearity and the norm estimate. Replacement
assembles these uniquely specified values. This proves the required
bounded extension without selecting a sequence from $V$ for every $x$. For
Hilbert spaces, this is also the bounded-map extension stated immediately
after Blackadar–Farah–Karagila, Proposition 2.0.7.

Similarly, suppose $A_n$ are nonempty nested closed bounded sets of bounded
maps $X\to Y$, with diameters tending to zero. For each $x$ use the closed sets
$\overline{\{Tx:T\in A_n\}}$. Their unique common point defines $Sx$. Finite
approximations from the same $A_n$ prove linearity; a bound on $A_1$ proves
boundedness. For $T\in A_n$,

$$
\|(T-S)x\|\le\operatorname{diam}(A_n)\|x\|.
$$

Thus $S$ belongs to each $A_k$ by taking $n\ge k$ and using closedness. If the
initial sets have not been assumed bounded, discard finitely many until
one has finite diameter and fix one member of that one set. This is a
single existential witness. This verifies the operator-completeness
input without assuming evaluation images are closed.

All integrals needed here are limits of specified dyadic Riemann sums.
Uniform continuity on an interval makes the sums Cauchy and gives their
norm estimate. Operator-valued integrals use the preceding completeness
lemma. Rectangular sums give the double integrals and their interchange.
The fundamental theorem of calculus can be established first after scalar
testing, then tested against the resulting difference vector. No general
Bochner integration, Hahn–Banach theorem, or selection of measurable
representatives is used.

## Graph control and the algebraic spectrum

Assume the pointwise graph inequality:

$$
\forall t\in[0,1]\ \exists c_t\ge0\ \forall x\in D,\qquad
\|x\|_D\le c_t(\|jx\|+\|H(t)x\|).
\tag{1}
$$

No function of graph constants is assumed or selected. For $\operatorname{Im}z\ne0$,
self-adjointness gives

$$
\|(H(t)-zj)x\|\ge |\operatorname{Im}z|\,\|jx\|.
$$

Combining this with (1) gives a lower $D$-norm estimate for $H(t)-zj$.
If $v$ is in the closure of its range, the inverse images of the closed
balls of radius $1/n$ about $v$ are nonempty closed nested subsets of $D$
with diameter tending to zero. Their common point maps to $v$. Thus the
range is closed in ZF without choosing approximate preimages. Its
orthogonal complement is zero by the maximal adjoint-domain condition
and the nonreal parameter. Hilbert projection then gives surjectivity.

Consequently $S_t=H(t)-ij$ has a unique bounded inverse $E\to D$. Replacement
assembles it, and the local Neumann series proves its norm continuity.
Compactness provides finite bounds $R\ge\sup_t\|S_t^{-1}\|$ and $L\ge\sup_t\|H^\prime(t)\|$.
For $\kappa=RL$ and $q_t(x)=\|S_tx\|$ one has

$$
q_t(x)\le(1+\kappa|t-s|)q_s(x),\qquad
q_t(x)^2=\|jx\|^2+\|H(t)x\|^2.
\tag{2}
$$

These $q_t$ are uniformly equivalent to the supplied $D$ norm.

The graph inequality (1) does not itself supply boundedness of every
algebraic real resolvent.
The [spectral-closure lemma](graph-control.md#spectral-closure) establishes

$$
\sigma_{\rm phys}(H)=\overline{\sigma_{\rm alg}(H)}.
\tag{3}
$$

Its restriction argument is as follows. Put $r=j(H-ij)^{-1}$. For one
fixed nonzero $x\in D$, the closed span of $r^m(r^*)^n jx$ is a reducing Hilbert
subspace $F$ with an explicitly enumerated dense set of rational complex
linear combinations. Its orthogonal projection $P_F$ has the domain lift

$$
\widehat P_F=(H-ij)^{-1}P_F(H-ij).
$$

Resolvent commutation gives $j\widehat P_F=P_Fj$ and $H\widehat P_F=P_FH$. The restricted
domain $D_F=\{d:jd\in F\}$ is boundedly isomorphic, through $H-ij$, to $F$. It is
therefore explicitly separable and complete. Testing adjoint identities
against $\widehat P_Fd$ verifies that the restricted physical $H_F$ is self-adjoint.

On an open real interval $I$ of algebraic resolvents, the unique inverse
of $H-\mu j$ preserves $F$: apply $\widehat P_F$ and use injectivity. Thus the restricted
bounded map $D_F\to F$ is bijective. Both spaces are separable Banach spaces,
so their inverse is bounded in ZF. If
$(\lambda-\delta,\lambda+\delta)\subseteq I$, the bounded self-adjoint physical inverse $B=(H_F-\lambda)^{-1}$
satisfies $\|B\|\le1/\delta$. Indeed, for real $w$ with $|w|>1/\delta$, the point
$\lambda+1/w$ belongs to $I$, and elementary inverse algebra shows that $B-wI$ is
invertible. The spectrum of $B$ is real and its norm equals its spectral
radius. Therefore

$$
\|(H-\lambda j)x\|\ge\delta\|jx\|.
$$

The bound is independent of the particular cyclic subspace. The global
algebraic inverse at $\lambda$ is physically bounded; its $D$ norm is bounded by
$c(1+(1+|\lambda|)/\delta)$. This proves (3), using also the Neumann-series closedness
of the physical spectrum. This gives the endpoint-gap transfer needed by the original theorem;
equality of the two spectra is not asserted.

The external results used at this point are the separable open mapping
theorem, Proposition 2.0.1(6), and the self-adjoint spectral-radius result,
Theorem 2.3.2 and Corollary 2.3.3, of Blackadar and Farah,
*Separable $C^*$-algebras Without the Countable Axiom of Choice*.
The latter input is weaker than full continuous functional calculus.
[Primary preprint, arXiv:2602.15812v1](https://arxiv.org/html/2602.15812v1)

## Frozen evolution and passage to a domain-preserving limit

The following construction derives the evolution from (1).

For a fixed $H$, let $R_z$ denote the physical resolvent. For $n\ge1$ set

$$
Q_n=\tfrac12(-inR_{in}+inR_{-in}),\qquad
A_n=\tfrac{n^2}{2}(R_{in}+R_{-in}).
$$

Resolvent identities make $A_n$ mutually commuting bounded self-adjoint
operators and give $\|Q_n\|\le1$. On the physical domain,

$$
\|Q_njx-jx\|\le\|Hx\|/n,\qquad A_njx=Q_nHx.
$$

Define $W_n(u)=\exp(-iTuA_n)$ by its specified power series. Each is unitary.
Differentiating their relative product and using commutation gives

$$
\|(W_n(u)-W_m(u))jx\|
\le T|u|\,\|(A_n-A_m)jx\|.
\tag{4}
$$

Hence the sequence converges uniformly on compact $u$-intervals on the
dense domain, then on every $E$-vector using the bound one and a single
dense approximation for each error estimate. This is not a choice of a
sequence of approximations. The unique limits define $W(u)$. Products
pass to the limit, giving the group law and $W(-u)=W(u)^*$. Passing to the
integrated equation gives its strong derivative on $j(D)$.

Since $W$ commutes with $R_i$, its explicit domain lift is
$(H-ij)^{-1}W(u)(H-ij)$. This proves preservation of $q$, strong $D$-continuity,
and the inverse lift. Frozen groups for all sample times are thus given
by one specified construction.

Use the fixed grids $k/(n+1)$, with $h_n=1/(n+1)$, and the finite chronological
products $U_n(t,s)$ of those groups. Applying (2) at adjacent sample times
gives

$$
q_t(U_n(t,s)x)
 \le e^{\kappa(|t-s|+2h_n)}q_s(x).
\tag{5}
$$

The reverse products satisfy the same estimate. It follows that all
forward and inverse $D$ lifts have a uniform bound $B$ independent of
$n,t,s,T$. Differentiation on the finite common refinement of two grids
then yields

$$
\|(U_n(t,0)-U_m(t,0))j\|_{D\to E}
 \le TLB(h_n+h_m).
\tag{6}
$$

The identity
$U_n^*-U_m^*=U_n^*(U_m-U_n)U_m^*$ and the inverse domain bound give the same
type of estimate for the adjoints. Both sequences therefore converge
strongly, uniformly in $t$ on each $E$-vector. Products pass to the limit,
so the two limits are mutual inverses, not merely isometric embeddings.
Denote them by $U(t)$ and $U(t)^*$.

Physical convergence alone would not retain the domain. The required
additional lemma is this: if $jx_n\to v$ and $\|H(r)x_n\|\le M$, symmetry makes

$$
|\langle v,H(r)y\rangle|\le M\|jy\|\qquad(y\in D).
$$

Bounded extension and Riesz representation put $v$ in the maximal adjoint
domain, hence in $j(D)$, with the same $H(r)$-bound. Its preimage is unique.
Applying this to the explicit sequences of forward and inverse products
constructs the two $D$ lifts. Linearity follows from injectivity of $j$;
boundedness follows from the surviving graph bound and $S_r^{-1}$.

For strong $D$-continuity it is essential to retain the sharp limiting
constant in (5). Testing $S_rx_n$ against the dense set $j(D)$ shows weak
convergence to $S_rx$. A uniform bound extends the assertion to all test
vectors. Testing against $S_rx$ itself gives lower semicontinuity of the
norm, with no weakly convergent subsequence. Consequently

$$
q_t(U(t)U(s)^*x)\le e^{\kappa|t-s|}q_s(x).
\tag{7}
$$

For fixed $x\in D$ and $s$, physical continuity gives weak convergence of
$S_sU(t)x$ to $S_sU(s)x$. Equations (2) and (7) give

$$
q_s(U(t)x)\le(1+\kappa|t-s|)e^{\kappa|t-s|}q_s(U(s)x).
$$

The Hilbert norm identity converts this weak convergence and the sharp
upper norm bound to norm convergence. Applying $S_s^{-1}$ gives the required
$D$-continuity. This argument is an epsilon argument in $t$; it does not
infer general continuity from a choice-dependent sequential criterion.

Finally the finite-grid comparison with the autonomous group $W_t(h)$
gives, for $t,t+h\in[0,1]$,

$$
\|(U_n(t+h,t)-W_t(h))jx\|
\le C_T|h|(|h|+h_n)\|x\|_D.
$$

Passing to the explicit limit leaves an $O(h^2)$ error. The autonomous
derivative therefore proves the required strong equation, including the
one-sided endpoint derivatives. Scalar testing of the norm of the
difference of two domain solutions proves uniqueness; density extends
it to $E$. Only $C^1$ regularity of $H$ was used in the evolution part, which
is needed later for the corrected Hamiltonian.

## Direct projection proof without normal functional calculus

For each time, (3) and the original gap show that the band circle and
nearby circles lie in the physical resolvent. The graph estimate also
bounds every $E\to D$ inverse there. Hence the integrals in this paragraph
use exactly the inverse occurring in the original statement.

Fix $H$. Write $R(z)=j(H-zj)^{-1}$ and $c=1/(2\pi i)$. For the positively
oriented circle $\Gamma$ with diameter equal to the band interval, set
$P=-c\oint_\Gamma R(z)\,dz$. In the resolvent set,

$$
R'(z)=R(z)^2,\quad
R(z)R(w)=\frac{R(z)-R(w)}{z-w},\quad
R(z)^*=R(\overline z).
\tag{8}
$$

For a differentiable homotopy of circles $\gamma_s(\theta)$, all in the resolvent,
the chain rule gives

$$
\partial_s\bigl(R(\gamma_s)\partial_\theta\gamma_s\bigr)
=\partial_\theta\bigl(R(\gamma_s)\partial_s\gamma_s\bigr).
$$

Periodicity makes its $\theta$-integral zero. Thus the resolvent integral is
constant through this homotopy. This proof uses only continuous
derivatives on the compact parameter rectangle and the fixed Riemann
sums described above.

Choose two concentric circles, just inside and outside the band circle.
Their real endpoints remain in the endpoint gaps; their remaining points
are nonreal. The resulting projections $P_-,P,P_+$ are equal by the
homotopy. On the product of inner and outer contours, use (8):

$$
P_-P_+
=c^2\oint_{\Gamma_-}\oint_{\Gamma_+}
       \frac{R(z)-R(w)}{z-w}\,dw\,dz
=-c\oint_{\Gamma_-}R(z)\,dz=P_-.
$$

The first scalar kernel integral is $-2\pi i$ because $z$ is inside the outer
circle. The second is zero after reversing the order because $w$ is
outside the inner circle. These circle integrals follow directly from
geometric series. Thus $P^2=P$. Conjugating the real-centered circle
reverses orientation, and (8), together with the conjugation of $c$,
gives $P^*=P$. No spectral measure, eigenbasis, character, or maximal ideal
is introduced.

The integral without the leading $j$ defines a bounded $E\to D$ lift of $P$.
Multiplication by $H$ under that integral proves $HP=PH$ on $D$. To check
regularity for moving merely continuous endpoints, fix a reference time.
For nearby times both new endpoints differ by less than $g/2$ from their
old values. At the new time, interpolate the two pairs of endpoints
linearly. Every intermediate real endpoint lies in a new endpoint gap,
and every other circle point is nonreal. The homotopy therefore
identifies the moving-circle integral with the fixed-circle integral.
Norm inversion on that fixed circle is $C^2$, so integration gives $C^2$
regularity of $P$ and of its $D$-valued lift. No endpoint derivative is used.

## Commutator construction and both errors

Let $K=P^\prime P-PP^\prime$. It is $C^1$ and skew-adjoint. On a fixed contour define

$$
X=-c\oint R(z)P'R(z)\,dz,\qquad
L_X=-c\oint(H-zj)^{-1}P'R(z)\,dz.
$$

These are $C^1$ in the physical and $E\to D$ operator norms, respectively.
Direct multiplication gives $jL_X=X$ and

$$
HL_Xj-XH=Kj.
\tag{9}
$$

A global $L_X$ can be built from a finite smooth partition of unity. The
cover must be indexed by all admissible contour neighborhoods, rather
than selected one neighborhood per time. Compactness then gives finitely
many witnesses. Shrinking finitely many intervals and using scalar bump
functions gives a partition with supports inside their domains. Zero
extension of the supported products is $C^1$. Equation (9) survives the
weighted sum because it is linear. No infinite choice is hidden here.

For each fixed $T>0$, the physical bounded perturbation $(i/T)K$ is
self-adjoint. Thus $H_T=H+(i/T)Kj$ remains self-adjoint on the same domain;
this follows immediately by subtracting the bounded term in the
maximal adjoint-domain test. Graph control transfers from (1), and $H_T$
is $C^1$. The construction above therefore gives $V_T$ with

$$
V_T'=(-iTH+K)V_T.
$$

Its existence does not require a $C^2$ perturbation. Differentiating $P^2=P$
gives $[K,P]=P^\prime$, so $V_T^*PV_T=P(0)$. All differentiated expressions can
first be evaluated on $j(D)$, using the $D$ lifts where $H$ acts.

Put $M=\sup\|X\|$, $N=\sup\|X^\prime\|$, and $Q=\sup\|K\|$ on $[0,1]$. They are finite
and do not depend on $T$. For an arbitrary original strong propagator $U_T$,
(9) and the strong product rule give

$$
\begin{aligned}
(U_T^*XV_T)'&=iT U_T^*KV_T+U_T^*(X'+XK)V_T,\\
(U_T^*V_T)'&=U_T^*KV_T.
\end{aligned}
$$

Integrating on individual domain vectors, then extending the uniform
bound by density, yields

$$
\|U_T(t)-V_T(t)\|\le\frac{2M+N+MQ}{T}.
\tag{10}
$$

This passage from vector bounds to an operator bound is direct; it uses
no uniform boundedness principle. Intertwining and the projection norm
bound one give leakage at most the right side of (10). Adding and
subtracting $V_TP(0)U_T^*$ bounds the transported-projection error by twice
that quantity. Thus $C=2(2M+N+MQ)$ handles both errors, for all positive $T$,
all times, and every admissible $U_T$. There is no simultaneous selection
of a family of propagators over $T$.

## Scope

The proof retains the original common domain and its supplied Banach norm,
the algebraic spectral gap, the totalized bounded inverse in the contour
definition, and every field of the strong propagator. Its only additional
analytic premise is the pointwise graph inequality (1), with uniform
completeness throughout. It does not select a family of graph constants or
propagators, invoke a general open mapping theorem after (1), or require
dependent choice for the approximation steps.

The foundational inputs cited above and these replacements for library
infrastructure are mathematical arguments. They are not conclusions of
the Lean dependency audit, and no formalization of this ZF proof is claimed.
