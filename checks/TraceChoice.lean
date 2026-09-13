import Adiabatic
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Choice dependency paths

Run `lake env lean checks/TraceChoice.lean` after building the library.
The diagnostic searches declaration dependencies in the checked environment.
An edge is labelled `type`, `definition`, `proof`, or `constructor`. The first
edge can be restricted to the statement or body of the starting declaration.
Only the first edge is restricted; subsequent edges follow both types and bodies.
The `definition` label also includes proof fields stored in a definition. A path
reports a dependency of this implementation, not a necessity result for the
corresponding mathematical statement.
-/

open Lean Elab Command

namespace ChoiceDependency

structure Edge where
  source : Name
  target : Name
  kind : String
  deriving Inhabited

def edges (env : Environment) (name : Name) : Array Edge := Id.run do
  let some info := env.checked.get.find? name | return #[]
  let mut result := info.type.getUsedConstants.map fun target => ⟨name, target, "type"⟩
  match info with
  | .defnInfo val =>
    result := result ++ val.value.getUsedConstants.map fun target => ⟨name, target, "definition"⟩
  | .thmInfo val =>
    result := result ++ val.value.getUsedConstants.map fun target => ⟨name, target, "proof"⟩
  | .opaqueInfo val =>
    result := result ++ val.value.getUsedConstants.map fun target => ⟨name, target, "definition"⟩
  | .inductInfo val =>
    result := result ++ val.ctors.toArray.map fun target => ⟨name, target, "constructor"⟩
  | _ => pure ()
  return result

/-- Breadth-first search: the returned chain has the fewest declaration edges. -/
def shortestPath (env : Environment) (start target : Name) (first : String) :
    Option (Array Edge) := Id.run do
  let mut queue : Array (Name × Array Edge) := #[(start, #[])]
  let mut seen : NameSet := ({} : NameSet).insert start
  let mut cursor := 0
  -- Each checked declaration is enqueued at most once.
  let count := env.constants.fold (init := 0) fun count _ _ => count + 1
  for _ in [:count + 1] do
    if cursor ≥ queue.size then return none
    let (current, path) := queue[cursor]!
    cursor := cursor + 1
    if current == target then return some path
    for edge in edges env current do
      if !path.isEmpty || first == "all" ||
          (first == "type" && edge.kind == "type") ||
          (first == "body" && edge.kind != "type") then
        if !seen.contains edge.target then
          seen := seen.insert edge.target
          queue := queue.push (edge.target, path.push edge)
  return none

def renderPath (start target : Name) (first : String) (path : Array Edge) : String :=
  s!"{start} [{first}; {path.size} edges]" ++
    String.join (path.toList.map fun edge => s!"\n  --{edge.kind}--> {edge.target}") ++
    s!"\n  target: {target}"

elab "trace_choice " decl:ident mode:str : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo decl
  let env ← getEnv
  let first := mode.getString
  unless #["all", "type", "body"].contains first do
    throwError "Expected all, type, or body"
  match shortestPath env name ``Classical.choice first with
  | some path => logInfo (renderPath name ``Classical.choice first path)
  | none => logInfo m!"{name} [{first}]: no path to Classical.choice"

elab "trace_dependency " decl:ident " to " dest:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo decl
  let target ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo dest
  match shortestPath (← getEnv) name target "all" with
  | some path => logInfo (renderPath name target "all" path)
  | none => logInfo m!"{name}: no path to {target}"

end ChoiceDependency

/-- Even a reflexivity proof inherits the dependencies of the current real type. -/
theorem ChoiceDependency.real_reflexivity (x : ℝ) : x = x := rfl

#print axioms ChoiceDependency.real_reflexivity

set_option maxRecDepth 100000
set_option maxHeartbeats 0

trace_choice Adiabatic.Unbounded.common_domain_adiabatic_theorem "all"
trace_choice Adiabatic.Unbounded.common_domain_adiabatic_theorem "type"
trace_choice Adiabatic.Unbounded.common_domain_adiabatic_theorem "body"
trace_choice Adiabatic.Unbounded.CommonDomainAdiabaticTheorem "body"
trace_choice Adiabatic.Unbounded.CommonDomain.graphEquiv "body"
trace_choice Adiabatic.Unbounded.CommonDomain.rangeEquiv "body"
trace_choice Adiabatic.Unbounded.CommonDomain.inverseShift "body"
trace_choice Adiabatic.Unbounded.CommonDomain.rieszProjection "body"
trace_choice Adiabatic.Unbounded.GappedHamiltonian.spectralProjection "body"
trace_choice Adiabatic.Unbounded.exists_nonautonomous_strongPropagator "body"
trace_choice Adiabatic.Unbounded.exists_unitary_strong_limit_of_restricted_cauchy "body"
trace_choice Adiabatic.Unbounded.exists_limit_domain_lift "body"
trace_choice Adiabatic.Unbounded.CommonDomain.exists_contDiffOn_commutatorLift_of_local_contours "body"
trace_choice Real "all"
trace_choice CompleteSpace "all"
trace_choice NormedAddCommGroup "all"
trace_choice ContinuousLinearMap.opNorm "body"

trace_choice Real.linearOrder "body"
trace_choice ContinuousLinearMap.inverse "body"
trace_choice cauchySeq_tendsto_of_complete "body"
trace_choice LinearEquiv.ofInjective "body"
trace_choice ContinuousLinearMap.equivRange "body"
trace_choice Adiabatic.Unbounded.exists_frozenApproximation "body"
trace_choice Adiabatic.Unbounded.exists_frozenFamily "body"
trace_dependency Adiabatic.Unbounded.CommonDomain.graphEquiv to LinearEquiv.ofInjective
trace_dependency Adiabatic.Unbounded.CommonDomain.rieszProjection to MeasureTheory.integral
trace_dependency ContinuousLinearMap.opNorm to Real.instSupSet
trace_choice Real.instSupSet "body"
trace_choice MeasureTheory.integral "body"

trace_choice Adiabatic.Unbounded.exists_contDiffOn_linear_solution "body"
trace_choice SmoothPartitionOfUnity.exists_isSubordinate "body"
trace_choice IsCompact.elim_finite_subcover "body"
trace_choice LinearPMap.adjoint "body"
trace_choice cfcHom "body"
trace_choice Real.exists_isLUB "body"
trace_choice ContinuousLinearMap.exists_preimage_norm_le "body"
trace_dependency Adiabatic.Unbounded.CommonDomain.graphEquiv to ContinuousLinearMap.exists_preimage_norm_le
trace_dependency Adiabatic.Unbounded.CommonDomain.rieszProjection_isStarProjection to cfcHom
trace_dependency Adiabatic.Unbounded.CommonDomain.exists_contDiffOn_commutatorLift_of_local_contours to Adiabatic.Unbounded.exists_contDiffOn_linear_solution
trace_dependency Adiabatic.Unbounded.CommonDomain.IsSelfAdjoint to LinearPMap.adjoint
trace_dependency Adiabatic.Unbounded.common_domain_adiabatic_theorem to CompleteSpace
trace_dependency Adiabatic.Unbounded.common_domain_adiabatic_theorem to Real.linearOrder

#print axioms CompleteSpace
#print axioms cauchySeq_tendsto_of_complete
#print axioms Real

trace_dependency Adiabatic.Unbounded.CommonDomain.rieszProjection_isStarProjection to Ideal.exists_le_maximal
trace_dependency Ideal.exists_le_maximal to Classical.choice
trace_dependency Adiabatic.Unbounded.exists_contDiffOn_linear_solution to Classical.choose
trace_dependency Adiabatic.Unbounded.CommonDomain.graphEquiv to Classical.choose
trace_dependency Real.exists_isLUB to Classical.choose
trace_dependency ContinuousLinearMap.exists_preimage_norm_le to Classical.choose

trace_dependency Ideal.exists_le_maximal to zorn_le_nonempty₀
trace_dependency zorn_le_nonempty₀ to Classical.choice
trace_dependency Adiabatic.Unbounded.common_domain_adiabatic_theorem to Ideal.exists_le_maximal
