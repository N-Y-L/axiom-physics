# Dependent choice suffices for the common-domain theorem

Dependent choice (DC) suffices to construct the evolution, spectral
projection, and graph estimates from the original common-domain hypotheses.
[Countable choice](countable-choice.md) gives a sharper sufficient
assumption; the proof below records the direct route under DC. It is a
mathematical proof in classical ZF + DC, not a Lean formalization. The existing
Lean theorem still uses `Classical.choice`.

## Statement

Let E be a complete complex Hilbert space and D a complete complex Banach
space. Let j : D → E be a bounded injective linear map with dense range.
For 0 ≤ t ≤ 1, let H(t) : D → E be bounded, C² in operator norm, and
self-adjoint as an unbounded operator with physical domain j(D). Let a(t)
and b(t) be continuous, a(t) < b(t), and let g > 0 be a uniform lower bound
for the distances of both endpoints from the spectrum of H(t).

**Theorem (ZF + DC).** The Riesz projection P(t) for the band (a(t),b(t))
is C² and orthogonal. For every T > 0 there is a unique normalized strong
unitary evolution U_T for U_T′ = −iT H(t)U_T. Both U_T and its inverse
preserve j(D), their domain lifts are bounded, and the forward domain lift
is strongly continuous. There is C ≥ 0, independent of T and t, such that

$$
\|U_T(t)P(0)U_T(t)^*-P(t)\|\le C/T,
\qquad
\|(I-P(t))U_T(t)P(0)\|\le C/T.
$$

These are the assumptions and conclusions of
[Unbounded/Statement.lean](../../Adiabatic/Unbounded/Statement.lean).
Under DC, Cauchy, Cantor, and uniform
completeness of metric spaces agree, so this statement also covers the
uniform-completeness convention in the [necessity theorem](necessity.md).
The zero Hilbert space is immediate; suppose E is nonzero below.

## Analytic foundations and where DC enters

DC supplies the usual nested-ball proof of Baire's theorem in an arbitrary
complete metric space: at stage n select a closed ball of radius below 2⁻ⁿ
inside the preceding ball and the nth dense open set. Completeness gives
the common point. The open mapping proof then needs only another dependent
sequence: Baire gives a ball contained in the closure of the image of a
bounded ball, and successive preimages reduce the remaining error by a
factor of two. Their norms form a summable geometric series. Thus bounded
bijective maps between arbitrary Banach spaces have bounded inverses in
ZF + DC. Closed graph follows by applying this to the graph projection.

Hilbert projection and Riesz representation also require no stronger
choice here. Select a sequence in a nonempty closed convex set whose
squared distances approach their infimum. The parallelogram identity makes
it Cauchy; its limit is the unique minimizer. Apply this to the kernel of a
bounded functional to obtain its representing vector. Orthogonal
projections, bounded adjoints, and their norm identities follow.

No general Hahn–Banach theorem or weak compactness is used. For example,
a norm bound for an E-valued differentiable curve follows by applying
scalar calculus to its inner products; testing the final difference
against its normalized value gives the desired vector bound.

Continuous Banach-valued functions on compact intervals are integrated by
the specified dyadic left-endpoint Riemann sums. Uniform continuity makes
these sums Cauchy, with error bounded by interval length times a modulus
of continuity. This proves the norm bound, bounded-linear-map commutation,
the fundamental theorem of calculus, and interchange with uniform limits.
The double integrals used below are limits of finite rectangular sums.
No selection of measurable representatives or general Bochner integration
theorem is needed. Operator spaces are complete by taking the unique
pointwise limits of norm-Cauchy sequences and retaining their uniform
operator bound.

In these arguments, a unique inverse or limit for each parameter defines
a function by ZF Replacement. This remains true when the parameter set is
uncountable. It is not a simultaneous choice of nonunique witnesses.

## Resolvents and uniform graph bounds

Write S_t = H(t) − i j : D → E. Self-adjointness makes the graph of H(t)
closed. The graph map x ↦ (jx,H(t)x) is a bounded bijection from D onto
this closed Hilbert subspace. The bounded inverse theorem therefore gives

$$
\|x\|_D\le c_t\bigl(\|jx\|+\|H(t)x\|\bigr).
$$

The elementary imaginary-part estimate

$$
\|(H(t)-zj)x\|\ge |\operatorname{Im}z|\,\|jx\|
$$

and this graph estimate show that H(t) − zj has closed range for nonreal z.
Its range has trivial orthogonal complement: a perpendicular vector lies
in the adjoint domain and would be an eigenvector at the conjugate
nonreal parameter. Orthogonal projection onto a closed subspace then
shows that the range is E. Thus S_t is bijective with bounded inverse.
The same bounded inverse theorem shows that the repository's algebraic
resolvent set agrees with the physical resolvent set in ZF + DC.

Inversion is locally a norm-convergent Neumann series. Since H is C¹,
t ↦ S_t⁻¹ is continuous into the bounded operators E → D. Compactness gives
finite constants

$$
R\ge\sup_t\|S_t^{-1}\|,\qquad
L\ge\sup_t\|H'(t)\|,\qquad \kappa=RL.
$$

No family of graph constants c_t is selected: only the unique inverses
are assembled. For q_t(x) = ‖S_t x‖,

$$
q_t(x)\le(1+\kappa|t-s|)q_s(x).                                      \tag{1}
$$

All these graph norms are consequently uniformly equivalent to the
original D norm. This is a conclusion under DC, not an added hypothesis.

## Autonomous evolution without a spectral resolution

Fix a self-adjoint H on j(D). Identify domain vectors with their physical
images in this paragraph, and put R_z=(H−z)⁻¹ on E. For integers n ≥ 1 set

$$
Q_n=\frac{-inR_{in}+inR_{-in}}2,
\qquad
A_n=\frac{n^2}{2}(R_{in}+R_{-in}).
$$

The resolvent identity and R_z* = R_conj(z) give mutually commuting
bounded self-adjoint A_n and ‖Q_n‖ ≤ 1. On D,

$$
\|Q_nx-x\|\le\|Hx\|/n,\qquad A_nx=Q_nHx.
$$

Density and the uniform bound show Q_n → I strongly on E, and hence
A_nx → Hx for every x ∈ D. Define the bounded exponentials
W_n(u)=exp(−iTuA_n) by their power series. They are unitary and

$$
\|(W_n(u)-W_m(u))x\|
 \le T|u|\,\|(A_n-A_m)x\|\qquad(x\in D).                       \tag{2}
$$

This follows by differentiating W_n(u−v)W_m(v)x; commutativity moves the
generator difference onto x. Thus W_n(u)x converges uniformly for u in a
compact interval on D, and then on E by density and unitarity. Define W(u)x
to be this unique limit. Passing to limits in finite products gives the
group law, norm preservation, and W(−u)W(u)=I. The group is unitary and
strongly continuous. Passing to the integral of
W_n(u)(−iTA_nx) gives W′(u)x=−iTW(u)Hx on D.

Each W_n commutes with R_i, so W does as well. Its D-valued lift is the
explicit bounded map

$$
\widehat W(u)=S^{-1}W(u)S.
$$

Resolvent commutation proves j Ŵ(u)=W(u)j and H Ŵ(u)=W(u)H. It also gives
q(Ŵ(u)x)=q(x) and strong D-continuity. The inverse lift is Ŵ(−u).
The construction is specified for every H; alternatively its strong
equation and normalization make W unique. Therefore forming the groups
at all frozen sample points requires no arbitrary family choice.

## Nonautonomous evolution and its domain

Use the fixed grids k/(n+1), with mesh h_n=1/(n+1). On each cell evolve by
the autonomous group of its left-endpoint Hamiltonian. Finite chronological
products define U_n(t,s), including negative increments when t<s. They
are unitary, preserve D in both directions, and satisfy the frozen strong
equation on each cell. The coefficient error is at most Lh_n.

Each frozen factor preserves its own q norm. Multiplying (1) at successive
sample times and using 1+v ≤ exp(v) gives

$$
q_t(U_n(t,s)x)
 \le e^{\kappa(|t-s|+2h_n)}q_s(x).                                  \tag{3}
$$

The total variation of the monotone sample times is at most |t−s|+2h_n;
the reverse products give the same bound. Thus the D norms of all forward
and inverse products are bounded uniformly in n,t,s by a finite B.

Compare U_n and U_m by differentiating their relative product on the
finite common refinement of their grids. The strong integral estimate,
unitarity, and the D bound imply

$$
\|(U_n(t,0)-U_m(t,0))j\|_{D\to E}
 \le TLB(h_n+h_m).                                             \tag{4}
$$

The adjoint difference has the same type of bound with an additional
factor B, using U_n*−U_m*=U_n*(U_m−U_n)U_m* and the inverse domain lift.
Density extends both Cauchy properties to every vector of E. Unique
strong limits U(t) and Z(t), uniform in t on each vector, satisfy
U(t)Z(t)=Z(t)U(t)=I and preserve norm. Hence U(t) is unitary with
Z(t)=U(t)*, and U is strongly continuous.

The domain does not follow from physical convergence alone. The following
bounded-form argument supplies the required additional step. If x_n ∈ D,
jx_n → v in E, and ‖H(r)x_n‖ ≤ M, then for every y ∈ D,

$$
|\langle v,H(r)y\rangle|
 =\lim_n|\langle H(r)x_n,jy\rangle|\le M\|jy\|.
$$

The resulting bounded functional on the dense domain extends uniquely to
E and has a Riesz representative. Thus v belongs to the maximal adjoint
domain, which is j(D), and ‖H(r)v‖ ≤ M. The preimage in D is unique.
Apply this to the forward and inverse frozen products, using (3). It
constructs bounded D lifts of U(t) and U(t)*. Linearity follows from the
injectivity of j; the bound follows from S_r⁻¹ and the surviving graph
bound. Replacement assembles the lifts without a choice over (t,x).

More precisely, graph bounds retain their exact limiting constant.
Once x_n converges physically to a domain vector x, testing S_r x_n
against jy and using symmetry proves weak convergence to S_r x on the
dense domain. A uniform bound extends this to all test vectors. Testing
against S_r x shows that q_r(x) ≤ lim b_n whenever q_r(x_n) ≤ b_n and
b_n has a limit. Apply this to U_n(t,s)x and (3) to obtain

$$
q_t(U(t)U(s)^*x)\le e^{\kappa|t-s|}q_s(x).                          \tag{5}
$$

Fix s and x ∈ D. Physical continuity gives weak convergence
S_s U(t)x ⇀ S_s U(s)x. Equations (1) and (5) give

$$
q_s(U(t)x)\le(1+\kappa|t-s|)e^{\kappa|t-s|}q_s(U(s)x).
$$

The Hilbert identity for ‖v_t−v‖² now turns weak convergence and this sharp
limsup norm bound into strong convergence. Applying S_s⁻¹ proves strong
D-continuity of the lift. This replaces any appeal to a weakly convergent
subsequence or compactness of a Hilbert ball.

Finally, compare U_n(t+h,t)x with the autonomous evolution W_t(h)x of
the fixed H(t). The same finite-cell differentiation used for (4) bounds
the coefficient discrepancy by L(|h|+h_n). The local version of (3)
bounds its domain argument. For t,t+h ∈ [0,1], this yields a constant C_T,
independent of n,t,h,x, such that

$$
\|(U_n(t+h,t)-W_t(h))jx\|
 \le C_T|h|(|h|+h_n)\|x\|_D.
$$

Pass to the strong limit to get a quadratic error C_T h²‖x‖_D.
After division by h, the autonomous derivative gives the full strong
Schrödinger equation, with one-sided derivatives at the endpoints.
Differentiating the norm of a difference of two domain solutions gives
uniqueness there; density gives uniqueness on E. Thus every part of the
required strong propagator has been constructed.

## Spectral projection and commutator solution

The physical reference resolvent r(t)=jS_t⁻¹ is a bounded normal operator.
Only continuous functional calculus for this one normal operator is
needed. Blackadar–Farah prove that calculus in ZF for normal elements in
an arbitrary ambient C*-algebra; separability of E is not required.
[Proposition 6.1.4](https://arxiv.org/html/2602.15812v1)
Their result applies to the adjoint-closed tuple (r(t),r(t)*), and
replaces the general character/maximal-ideal construction used by the
current mathlib implementation. An alternative
[direct resolvent integral argument](analytic-constructions.md#direct-projection-proof-without-normal-functional-calculus)
proves the same projection properties without this functional calculus.

Take the positively oriented circle Γ_t with diameter [a(t),b(t)]. The
gap and reality of the spectrum put it in the resolvent set. With
R_t(z)=(H(t)−zj)⁻¹ : E → D and c=1/(2πi), define

$$
P(t)=-c\oint_{\Gamma_t}jR_t(z)\,dz.
$$

The resolvent identity gives

$$
jR_t(z)=r(t)\bigl[I-(z-i)r(t)\bigr]^{-1},\qquad
f_z(w)=\frac{w}{1-(z-i)w},\qquad f_z(0)=0.
$$

Continuous functional calculus applied to f_z identifies the integral
with the real indicator of the selected spectral component. At the possible
spectral point 0 of r(t), corresponding to infinity for H(t), the rational integral
is zero. Thus P²=P=P*. The same integral without j gives a bounded lift
E → D, and the resolvent identity gives HP=PH on D.

Near each fixed t, the same fixed circle selects the band. Indeed,
continuity keeps both new endpoints within g/2 of their old values;
the real intervals between corresponding endpoints therefore contain no
spectrum. The two circle indicators agree, and functional calculus makes
their projections equal. Inversion is C² in the operator argument, so
integration on the fixed contour proves P is C² locally and hence on
[0,1]. This also proves local C² regularity of the D-valued lift.

Put K=P′P−PP′. Then K is C¹ and skew-adjoint. On a neighborhood with a
fixed contour define

$$
X=-c\oint_\Gamma jR_t(z)P'(t)jR_t(z)\,dz,
\qquad
L_X=-c\oint_\Gamma R_t(z)P'(t)jR_t(z)\,dz.
$$

The second operator is a C¹ map E → D and jL_X=X. Direct multiplication
of the two resolvents gives, on D,

$$
H(t)L_X(t)j-X(t)H(t)=P'(t)P(t)j-P(t)P'(t)j=K(t)j.              \tag{6}
$$

For a global solution, use the cover indexed by all admissible local
contour neighborhoods, rather than choosing one for every real t.
Compactness supplies finitely many neighborhoods. Shrink finitely many
intervals and use the usual scalar smooth bump functions, divided by
their sum, to form a finite smooth partition of unity. The weighted sum
of the local L_X is C¹ and retains (6), which is linear in L_X. Only
finitely many witnesses are used. This avoids an uncountable selection
hidden before the compactness step.

## Uniform adiabatic estimates

For each T > 0 the family H(t)+(i/T)K(t)j is C¹ on the same D and
self-adjoint: adding a bounded self-adjoint physical operator leaves
the maximal adjoint domain unchanged. The evolution construction above
therefore supplies V_T satisfying

$$
V_T'=(-iTH+K)V_T.
$$

Differentiating P²=P gives [K,P]=P′. Together with HP=PH, this shows
V_T(t)*P(t)V_T(t)=P(0). Define finite bounds

$$
M=\sup_t\|X(t)\|,\qquad N=\sup_t\|X'(t)\|,
\qquad Q=\sup_t\|K(t)\|.
$$

They depend on the Hamiltonian and band but not T. For
F(t)=U_T(t)*X(t)V_T(t), the domain lift and (6) justify the strong product
rule on D:

$$
F'=iT U_T^*K V_T+U_T^*(X'+XK)V_T.
$$

Also (U_T*V_T)′=U_T*KV_T. Integrating and using unitarity gives

$$
\|U_T(t)-V_T(t)\|\le\frac{2M+t(N+MQ)}T
 \le\frac{2M+N+MQ}T.                                        \tag{7}
$$

The calculation is first made on D; its uniform vector bound extends
to E by density. Intertwining gives leakage at most ‖U_T−V_T‖ and
projection distance at most 2‖U_T−V_T‖. Thus
C=2(2M+N+MQ) proves both asserted estimates. This completes the proof.

## Scope of the conclusion

This argument proves sufficiency of DC, not its necessity or an optimal
choice strength. The separate [countable-choice proof](countable-choice.md)
sharpens the sufficient assumption. Combined with the
[necessity theorem](necessity.md), the argument in this note gives the bounds

$$
\mathrm{DC}\ \Longrightarrow\ \mathrm{QAT}\ \Longrightarrow\
\text{every infinite subset of }\mathbb R
\text{ contains a countably infinite subset}.
$$

Full AC is not required for this mathematical theorem: there are models of
ZF + DC in which AC fails, relative to the consistency of ZFC. For example,
Shelah's Conclusion 7.17 establishes
equiconsistency with ZF + DC plus the assertion that all sets of reals
have the Baire property, an assertion incompatible with AC.
[Can you take Solovay's inaccessible away?, p. 43](https://shelah.logic.at/files/95333/176.pdf)

This does not remove `Classical.choice` from the Lean theorem. The strict
Lean audit concerns elaborated types and proof dependencies and requires
a separate formal implementation of the foundations above.

The proof follows the mathematical constructions of the repository's
`Domain`, `Resolvent`, `Autonomous`, `FrozenGraphBounds`, `Nonautonomous`,
`NonautonomousDomain`, `GraphLimit`, `HilbertGraphConvergence`,
`RieszProjection`, `RieszCommutator`, and comparison modules. The choice
accounting, the replacements for unrestricted library infrastructure,
and the ZF + DC conclusion are mathematical arguments here; they are
not conclusions of the existing Lean axiom audit.
