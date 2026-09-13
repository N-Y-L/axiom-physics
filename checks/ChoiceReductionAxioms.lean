import Adiabatic.ChoiceReduction
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Foundation audit for the choice-reduction results

Select every declaration by its originating module, including private and
generated declarations and names in other namespaces. Lean's axiom collector
traverses declaration types, definitions, and proofs in the checked environment.
The permitted axioms are `propext` and `Quot.sound`; `Classical.choice` is rejected.
The ordinary project audit remains unchanged and must also pass.
-/

open Lean Elab Command

elab "audit_choice_reduction" : command => do
  let env ← getEnv
  let declarations := env.constants.fold (init := #[]) fun declarations name info =>
    match env.getModuleIdxFor? name with
    | some index =>
        if (`Adiabatic.ChoiceReduction).isPrefixOf env.header.moduleNames[index.toNat]! then
          declarations.push (name, info)
        else declarations
    | none => declarations
  if declarations.isEmpty then
    throwError "No declarations from the choice-reduction modules were found"
  let allowed : Array Name := #[``propext, ``Quot.sound]
  let mut union : Array Name := #[]
  for (name, info) in declarations.qsort (fun a b => a.1.toString < b.1.toString) do
    if info.isUnsafe then
      throwError "Unsafe choice-reduction declaration: {name}"
    let some checked := env.checked.get.find? name
      | throwError "Missing checked declaration: {name}"
    if checked.isUnsafe then
      throwError "Unsafe choice-reduction declaration: {name}"
    let actual ← Lean.collectAxioms name
    let unexpected := actual.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "Disallowed foundations in {name}: {unexpected.toList}"
    for ax in actual do
      unless union.contains ax do
        union := union.push ax
    logInfo m!"CHOICE_REDUCTION_AXIOMS|{name}|{actual.toList}"
    let type ← liftTermElabM <| Lean.Meta.ppExpr checked.type
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | _ => "other"
    let record := Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson env.header.moduleNames[(env.getModuleIdxFor? name).get!.toNat]!.toString),
      ("kind", toJson kind),
      ("axioms", toJson (actual.map Name.toString)),
      ("type", toJson type.pretty)]
    logInfo m!"CHOICE_REDUCTION_RECORD|{record.compress}"
  logInfo m!"Audited all {declarations.size} choice-reduction declarations; axioms: {union.toList}"

audit_choice_reduction
