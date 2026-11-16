import Adiabatic.Unbounded.GappedReduction
import Adiabatic.Unbounded.Nonautonomous

/-!
# The common-domain quantum adiabatic theorem

The Hamiltonians may be unbounded on an arbitrary complex Hilbert space.
The proof constructs strong unitary Schrödinger evolution, constructs the
spectral projection of a continuously moving isolated band, and proves
uniform inverse-runtime bounds for projection distance and leakage.
-/

namespace Adiabatic.Unbounded

open Set

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Continuously differentiable self-adjoint common-domain Hamiltonians
have strong unitary Schrödinger evolution for every positive runtime. -/
theorem common_domain_evolution_existence (domain : CommonDomain D E) :
    CommonDomainEvolutionExistence domain := by
  intro H hc hH T _hT
  exact exists_nonautonomous_strongPropagator domain H hc hH
    (-Complex.I * (T : ℂ)) (by simp)

/-- The infinite-dimensional, uniformly gapped adiabatic theorem for
possibly unbounded self-adjoint Hamiltonians on a fixed dense domain.
The band projection, both evolutions, and the runtime-independent error
constant are derived from the stated Hamiltonian and gap assumptions. -/
theorem common_domain_adiabatic_theorem (domain : CommonDomain D E) :
    CommonDomainAdiabaticTheorem domain :=
  commonDomainAdiabaticTheorem_of_evolution_existence
    (common_domain_evolution_existence domain)

/-- The physical evolution supplied by the full theorem is unique on the
unit interval among strong unitary common-domain propagators. -/
theorem GappedHamiltonian.exists_unique_unitary_evolution
    {domain : CommonDomain D E} (data : GappedHamiltonian domain) {T : ℝ} (hT : 0 < T) :
    ∃ U : StrongPropagator domain data.H (fun _ => 0) (-Complex.I * (T : ℂ)),
      ∀ V : StrongPropagator domain data.H (fun _ => 0) (-Complex.I * (T : ℂ)),
        EqOn U.evolution V.evolution (Icc (0 : ℝ) 1) := by
  obtain ⟨U⟩ := common_domain_evolution_existence domain data.H
    (data.smooth.of_le (by norm_num)) data.selfAdjoint T hT
  exact ⟨U, fun V => U.unique V⟩

end Adiabatic.Unbounded
