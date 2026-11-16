import Adiabatic
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- The first dependency edge is restricted
to the checked type or body; subsequent edges traverse both types and bodies.
The original project and strict choice audit implementations are unchanged. -/

open Lean Elab Command

def splitAxiomClosure (env : Environment) (roots : Array Name) : Array Name :=
  let (_, state) := ((roots.forM Lean.CollectAxioms.collect).run env).run {}
  state.axioms

elab "export_split_axioms" : command => do
  let env ← getEnv
  let declarations := env.constants.fold (init := #[]) fun declarations name info =>
    match env.getModuleIdxFor? name with
    | some index =>
        if ((`Adiabatic.Foundations).isPrefixOf env.header.moduleNames[index.toNat]! ||
            (`Adiabatic.ChoiceReduction.SymmetryObstruction).isPrefixOf
              env.header.moduleNames[index.toNat]! ||
            (`Adiabatic.ChoiceReduction.InvolutionObstruction).isPrefixOf env.header.moduleNames[index.toNat]!) then
          declarations.push (name, info)
        else declarations
    | none => declarations
  if declarations.isEmpty then
    throwError "No new project declarations selected"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, info) in declarations.qsort (fun a b => a.1.toString < b.1.toString) do
    let some checked := env.checked.get.find? name
      | throwError "Missing checked declaration: {name}"
    if info.isUnsafe || checked.isUnsafe then
      throwError "Unsafe declaration: {name}"
    let typeRoots := checked.type.getUsedConstants
    let (bodyRoots, bodyKind) := match checked with
      | .defnInfo v => (v.value.getUsedConstants, "definition")
      | .thmInfo v => (v.value.getUsedConstants, "proof")
      | .opaqueInfo v => (v.value.getUsedConstants, "opaque body")
      | .inductInfo v => (v.ctors.toArray, "constructors")
      | _ => (#[], "none")
    let typeAxioms := splitAxiomClosure env typeRoots
    let bodyAxioms := splitAxiomClosure env bodyRoots
    let combined ← Lean.collectAxioms name
    unless (combined.all (fun ax => typeAxioms.contains ax || bodyAxioms.contains ax)) &&
        ((typeAxioms ++ bodyAxioms).all combined.contains) do
      throwError "Type/body union differs from combined closure: {name}"
    unless combined.all allowed.contains do
      throwError "Disallowed axiom in {name}: {combined}"
    let type ← liftTermElabM <| Lean.Meta.ppExpr checked.type
    let kind := match checked with
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
      ("type", toJson type.pretty),
      ("axioms", toJson (combined.map Name.toString)),
      ("combinedAxioms", toJson (combined.map Name.toString)),
      ("typeAxioms", toJson (typeAxioms.map Name.toString)),
      ("bodyAxioms", toJson (bodyAxioms.map Name.toString)),
      ("bodyKind", toJson bodyKind),
      ("typeRootCount", toJson typeRoots.size),
      ("bodyRootCount", toJson bodyRoots.size)]
    logInfo m!"SPLIT_AXIOM_RECORD|{record.compress}"
  logInfo m!"Exported type/body/combined dependency records for {declarations.size} declarations"

export_split_axioms
