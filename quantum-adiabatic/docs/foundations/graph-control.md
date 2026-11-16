# Explicit graph control suffices in ZF

Explicit graph-norm control prevents the failure exhibited in the
[counterexample](necessity.md). With this additional hypothesis, the full
adiabatic theorem holds in classical ZF. The proof uses uniform completeness,
retains the algebraic spectral-gap condition, and constructs the projection
and evolution. It is a mathematical proof, not a Lean formalization. The complete
[analytic construction](analytic-constructions.md) makes the extension,
evolution, projection, and commutator steps explicit.

## Spectral closure

Let E be a uniformly complete complex Hilbert space, D a uniformly complete
complex Banach space, and j:D→E a bounded injective complex-linear map with
dense range. Let H:D→E be bounded and complex-linear, representing a
self-adjoint operator on j(D), and suppose

$$
\|x\|_D\le c(\|jx\|+\|Hx\|)\quad(x\in D)
$$

for some finite c≥0. Write σ_alg(H) for the complement of the set of z such
that H−zj:D→E is algebraically bijective. Write σ_phys(H) for the spectrum
using bounded physical inverses on E.

**Lemma (ZF).**

$$
\sigma_{\rm phys}(H)=\overline{\sigma_{\rm alg}(H)}.
$$

In particular, positive distance from σ_alg to a real endpoint transfers
unchanged to σ_phys. The two resolvent sets themselves need not be equal.

**Proof.** The graph bound and the imaginary-part lower estimate give a
lower D-norm bound for H−zj when Im z≠0. Its range is closed without
selecting an approximating sequence. In detail, write A=H−zj and fix d
with ‖x‖_D≤d‖Ax‖. If v is in the closure of its range, the sets

$$
C_n=\{x\in D:\|Ax-v\|\le 1/n\}\qquad(n\ge1)
$$

are nonempty, closed, decreasing, and have diameter at most 2d/n.
Uniform completeness, equivalently Cantor completeness, gives their
unique common point x. Then Ax=v. No point of each C_n was selected.
A vector perpendicular to the range would be an
adjoint eigenvector at a nonreal point. Hence the range has zero orthogonal
complement and equals E. Orthogonal complementation is valid in ZF for
uniformly complete Hilbert spaces. Thus

$$
S=H-ij:D\longrightarrow E
$$

has a bounded inverse, and r=jS⁻¹ is a bounded normal physical operator.

Fix a nonzero x∈D; the norm estimate is immediate for x=0. Let F be the
closed linear span of all r^m(r*)^n jx, m,n≥0.
This space has an explicit countable dense set, using rational complex
coefficients. It is uniformly complete and reduces both r and r*. Let P
be its orthogonal projection, so Pr=rP. The bounded domain map

$$
\widehat P=S^{-1}PS
$$

satisfies jP̂=Pj. Indeed rPS=PrS=Pj. It also satisfies HP̂=PH since
H=S+ij. Let D_F={y∈D:jy∈F}. If y∈D_F, then jP̂y=Pjy=jy, so injectivity
gives P̂y=y and therefore Sy∈F. Conversely S⁻¹ maps F into D_F.
Consequently S restricts to a bounded isomorphism D_F→F with bounded
inverse. D_F is uniformly complete and explicitly separable, since it is
isomorphic to F. The restriction H_F is self-adjoint on D_F in F: its
adjoint-domain condition extends to the full domain by testing against
P̂y, and self-adjointness of H then gives precisely D_F.

Let I be an open real interval disjoint from σ_alg(H). For any μ∈I,
H−μj is bijective on the full domain. If v∈F and (H−μj)y=v, then

$$
(H-\mu j)\widehat P y=P(H-\mu j)y=Pv=v.
$$

Injectivity forces y=P̂y∈D_F. Thus H_F−μj is a bounded bijection from
D_F onto F. Both spaces are separable Banach spaces. The separable open
mapping theorem is a theorem of ZF, so its inverse is bounded. Therefore
I is disjoint from σ_phys(H_F).

Fix λ∈I and δ>0 with (λ−δ,λ+δ)⊂I. The bounded physical inverse
B=(H_F−λ)⁻¹ is self-adjoint. For any nonzero w∈σ(B), the elementary
resolvent identity gives λ+w⁻¹∈σ_phys(H_F). Therefore |w|≤1/δ.
The self-adjoint spectral-radius identity gives ‖B‖≤1/δ. Hence

$$
\|(H-\lambda j)x\|\ge\delta\|jx\|.
$$

Although F was formed from x, this bound is independent of F and x.
The globally defined algebraic inverse at λ is consequently physically
bounded by 1/δ. Moreover its D norm is bounded by
c(1+(1+|λ|)/δ), directly from the graph inequality and
Hy=v+λjy. Thus λ lies in the physical resolvent of H.

Every nonreal parameter is already in both resolvent sets. If a real λ
is outside the closure of σ_alg(H), choose I and δ as above. The argument
proves λ∉σ_phys(H), giving σ_phys⊂closure σ_alg. Conversely a bounded
physical inverse is an algebraic inverse on the physical domain, so
σ_alg⊂σ_phys; σ_phys is closed by the Neumann series. This proves the
lemma. ∎

The completeness and orthogonal-complement facts are
Blackadar–Farah–Karagila, Theorem 1.0.2 and Corollary 2.0.5.
[Hilbert Spaces Without Countable AC](https://arxiv.org/abs/2304.09602)
The separable open mapping theorem and self-adjoint spectral-radius identity
are Blackadar–Farah, Proposition 2.0.1(6), Theorem 2.3.2, and
Corollary 2.3.3.
[Separable C*-algebras Without the Countable Axiom of Choice](https://arxiv.org/html/2602.15812v1)

## The adiabatic theorem with graph control

**Theorem (ZF).** Suppose the hypotheses of the full common-domain adiabatic
theorem hold, E,D are uniformly complete, and additionally

$$
\forall t\in[0,1]\ \exists c_t\ge0\ \forall x\in D,\qquad
\|x\|_D\le c_t(\|jx\|+\|H(t)x\|).
$$

Then all conclusions of the [full theorem](dependent-choice.md) hold,
including the constructed projection and domain-preserving evolution, and
both uniform C/T estimates with one constant independent of T and time.

**Proof.** No function t↦c_t is supplied or selected. Each nonreal shifted
inverse S_t⁻¹ is unique and bounded by the first part of the proof. Replacement
assembles these inverses, and their local Neumann series gives continuous
dependence on t. Compactness of [0,1] supplies a uniform bound R, leading
to the graph-change estimate and the explicit evolution constructions in
the [analytic proof](analytic-constructions.md).

The lemma transfers the original algebraic spectral gap to a physical
gap. For physical real resolvents the graph inequality bounds the D-valued
inverse, so the contour projection and commutator constructions agree with
the repository's totalized inverses on every contour. For the Kato-corrected
Hamiltonian, graph control follows from
‖Hx‖≤‖(H+Bj)x‖+‖B‖‖jx‖ for bounded B.

The remaining Hilbert projection and Riesz steps are the ZF results of
Blackadar–Farah–Karagila, Theorems 2.0.4 and 2.0.6. Bounded operators on
the uniformly complete Hilbert space form a uniformly complete C*-algebra
by their Proposition 7.0.1 and §7.0.3. The bounded-map extension following their Proposition 2.0.7 has the
[direct shrinking-set proof](analytic-constructions.md#elementary-complete-space-infrastructure)
used here; an approximating vector sequence is not selected at every point.
The [resolvent integral proof](analytic-constructions.md#direct-projection-proof-without-normal-functional-calculus)
establishes the projection identities and regularity without normal
functional calculus. All subsequent limits use specified sequences, and
contour gluing uses finitely many witnesses. The commutator estimate in
that proof gives both uniform errors with one constant independent of T.
Thus the full theorem follows in classical ZF with the stated uniform
completeness and graph-control premise. [Countable choice](countable-choice.md)
derives this additional premise from the original hypotheses.
