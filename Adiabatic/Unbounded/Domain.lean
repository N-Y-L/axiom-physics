import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# A common domain for unbounded Hamiltonians

A dense injective map from a Banach space into the physical Hilbert space records
one common operator domain. The Hamiltonian is bounded for the domain norm;
its associated partially defined operator need not be bounded in the physical
norm. Self-adjointness always means equality with the actual unbounded adjoint.
-/

noncomputable section

namespace Adiabatic.Unbounded

open Set

variable (D E : Type*) [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A Banach domain continuously and densely included in the Hilbert space. -/
structure CommonDomain where
  inclusion : D →L[ℂ] E
  injective : Function.Injective inclusion
  dense : DenseRange inclusion

namespace CommonDomain

variable {D E} (domain : CommonDomain D E)

/-- Identification of the abstract domain with its image in the Hilbert space. -/
def rangeEquiv : D ≃ₗ[ℂ] domain.inclusion.range :=
  LinearEquiv.ofInjective domain.inclusion.toLinearMap domain.injective

@[simp] theorem rangeEquiv_coe (x : D) :
    (domain.rangeEquiv x : E) = domain.inclusion x := rfl

@[simp] theorem inclusion_rangeEquiv_symm (x : domain.inclusion.range) :
    domain.inclusion (domain.rangeEquiv.symm x) = x :=
  LinearEquiv.ofInjective_symm_apply domain.inclusion.toLinearMap x

/-- The actual unbounded operator represented by a bounded domain map. -/
def operator (H : D →L[ℂ] E) : E →ₗ.[ℂ] E where
  domain := domain.inclusion.range
  toFun := H.toLinearMap.comp domain.rangeEquiv.symm.toLinearMap

@[simp] theorem operator_domain (H : D →L[ℂ] E) :
    (domain.operator H).domain = domain.inclusion.range := rfl

@[simp] theorem operator_apply (H : D →L[ℂ] E) (x : D) :
    domain.operator H (domain.rangeEquiv x) = H x := by
  simp [operator]

variable [CompleteSpace E]

/-- Self-adjointness of the partially defined operator on the physical space. -/
def IsSelfAdjoint (H : D →L[ℂ] E) : Prop :=
  _root_.IsSelfAdjoint (domain.operator H)

/-- Self-adjointness gives symmetry of the domain Hamiltonian. -/
theorem inner_map (H : D →L[ℂ] E) (hH : domain.IsSelfAdjoint H) (x y : D) :
    inner ℂ (H x) (domain.inclusion y) = inner ℂ (domain.inclusion x) (H y) := by
  have h := (domain.operator H).adjoint_isFormalAdjoint
    (show Dense ((domain.operator H).domain : Set E) from domain.dense)
  have heq : (domain.operator H).adjoint = domain.operator H := hH
  rw [heq] at h
  simpa using h (domain.rangeEquiv x) (domain.rangeEquiv y)

/-- The graph embedding uses both the physical norm and the Hamiltonian norm. -/
def graphMap (H : D →L[ℂ] E) : D →L[ℂ] E × E := domain.inclusion.prod H

omit [CompleteSpace E] in
@[simp] theorem graphMap_apply (H : D →L[ℂ] E) (x : D) :
    domain.graphMap H x = (domain.inclusion x, H x) := rfl

omit [CompleteSpace E] in
theorem graphMap_injective (H : D →L[ℂ] E) : Function.Injective (domain.graphMap H) :=
  fun _ _ h => domain.injective (congrArg Prod.fst h)

omit [CompleteSpace E] in
/-- The range of the graph embedding is exactly the unbounded operator graph. -/
theorem range_graphMap (H : D →L[ℂ] E) :
    Set.range (domain.graphMap H) = (domain.operator H).graph := by
  ext p
  change p ∈ Set.range (domain.graphMap H) ↔ p ∈ (domain.operator H).graph
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨domain.rangeEquiv x, rfl, domain.operator_apply H x⟩
  · rintro ⟨x, hx, hHx⟩
    refine ⟨domain.rangeEquiv.symm x, ?_⟩
    apply Prod.ext
    · simpa using (domain.inclusion_rangeEquiv_symm x).trans hx
    · exact hHx

/-- Self-adjointness closes the graph embedding's range. -/
theorem graphMap_closed (H : D →L[ℂ] E) (hH : domain.IsSelfAdjoint H) :
    IsClosed (Set.range (domain.graphMap H)) := by
  rw [domain.range_graphMap H]
  exact hH.isClosed

variable [CompleteSpace D]

/-- The chosen domain norm is equivalent to the Hamiltonian's graph norm. -/
def graphEquiv (H : D →L[ℂ] E) (hH : domain.IsSelfAdjoint H) :
    D ≃L[ℂ] (domain.graphMap H).range :=
  (domain.graphMap H).equivRange (domain.graphMap_injective H) (domain.graphMap_closed H hH)

@[simp] theorem graphEquiv_coe (H : D →L[ℂ] E) (hH : domain.IsSelfAdjoint H) (x : D) :
    (domain.graphEquiv H hH x : E × E) = (domain.inclusion x, H x) := rfl

/-- A quantitative form of graph norm equivalence. -/
theorem norm_le_graph (H : D →L[ℂ] E) (hH : domain.IsSelfAdjoint H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : D,
      ‖x‖ ≤ C * (‖domain.inclusion x‖ + ‖H x‖) := by
  refine ⟨‖(domain.graphEquiv H hH).symm.toContinuousLinearMap‖, ContinuousLinearMap.opNorm_nonneg _, ?_⟩
  intro x
  have h := (domain.graphEquiv H hH).symm.toContinuousLinearMap.le_opNorm
    (domain.graphEquiv H hH x)
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (ContinuousLinearMap.opNorm_nonneg _))
  change ‖(domain.inclusion x, H x)‖ ≤ _
  rw [Prod.norm_def]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _))
    (le_add_of_nonneg_left (norm_nonneg _))

end CommonDomain
end Adiabatic.Unbounded
