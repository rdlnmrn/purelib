import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Elab.Command
import Lean.Compiler.MetaAttr
import mathlib.Data.ConstructiveFin
import mathlib.RFAP.CanonicalFractionRegression
import mathlib.RFAP.CanonicalFractionCompatibility
import mathlib.RFAP.CanonicalLCM
import mathlib.RFAP.ConstructiveGaussian
import mathlib.RFAP.NormalizedFraction
import mathlib.RFAP.NormalizedGaussian
import mathlib.RFAP.CanonicalGaussianRegression
import mathlib.RFAP.CanonicalPolynomialRegression
import mathlib.RFAP.CanonicalResidualRegression

/-!
Command used by `check-axioms.sh` after it has generated imports and supplied
the exact project-module list discovered from the active project sources.  The
audited-module list may be a shard of that complete list, allowing independent
Lean processes to audit disjoint parts of the project in parallel without
losing project-boundary provenance.

Declaration provenance, rather than declaration namespaces, determines the
audit surface.  This matters because generated declaration names need not
share the name of the module that defines them.
-/

namespace ProjectAxiomAudit

open Lean Elab Command

private def canonicalFractionModules : Array Lean.Name := #[
  `mathlib.Data.ConstructiveFin,
  `mathlib.RFAP.CanonicalGCD,
  `mathlib.RFAP.CanonicalLCM,
  `mathlib.RFAP.CanonicalFraction,
  `mathlib.RFAP.CanonicalFractionArithmetic,
  `mathlib.RFAP.CanonicalFractionField,
  `mathlib.RFAP.CanonicalFractionOrder,
  `mathlib.RFAP.CanonicalFractionSize,
  `mathlib.RFAP.CanonicalFractionRegression,
  `mathlib.RFAP.CanonicalFractionCompatibility,
  `mathlib.RFAP.ConstructiveGaussian,
  `mathlib.RFAP.NormalizedFraction,
  `mathlib.RFAP.NormalizedGaussian,
  `mathlib.RFAP.CanonicalGaussian,
  `mathlib.RFAP.CanonicalGaussianRegression,
  `mathlib.RFAP.CanonicalPolynomial,
  `mathlib.RFAP.CanonicalPolynomialRegression,
  `mathlib.RFAP.CanonicalResidual,
  `mathlib.RFAP.CanonicalResidualRegression]

elab "#audit_project_axioms "
    "project_modules " "[" projectModules:ident,* "] "
    "audited_modules " "[" auditedModules:ident,* "] "
    "audit_canonical " auditCanonical:ident " results " resultPath:str : command => do
  let environment ← getEnv
  let allProjectModules : Array Lean.Name :=
    projectModules.getElems.map (fun moduleSyntax => moduleSyntax.getId)
  let auditedProjectModules : Array Lean.Name :=
    auditedModules.getElems.map (fun moduleSyntax => moduleSyntax.getId)
  let auditCanonicalId := auditCanonical.getId
  unless auditCanonicalId == `true || auditCanonicalId == `false do
    throwError "audit_canonical must be true or false"
  let auditCanonical := auditCanonicalId == `true
  let allProjectModuleSet : Lean.NameSet :=
    allProjectModules.foldl (init := {}) fun modules moduleName =>
      modules.insert moduleName
  let auditedProjectModuleSet : Lean.NameSet :=
    auditedProjectModules.foldl (init := {}) fun modules moduleName =>
      modules.insert moduleName
  let canonicalFractionModuleSet : Lean.NameSet :=
    canonicalFractionModules.foldl (init := {}) fun modules moduleName =>
      modules.insert moduleName
  let allowed : Lean.NameSet := ({} : Lean.NameSet).insert ``propext
  let importedModules := environment.header.moduleNames
  let nonProjectAuditedModules := auditedProjectModules.filter fun moduleName =>
    !allProjectModuleSet.contains moduleName
  unless nonProjectAuditedModules.isEmpty do
    throwError m!"project axiom audit received non-project modules: \
      {nonProjectAuditedModules.toList}"
  let missingModules := auditedProjectModules.filter fun moduleName =>
    (environment.getModuleIdx? moduleName).isNone
  unless missingModules.isEmpty do
    throwError m!"project axiom audit did not import: {missingModules.toList}"
  if auditCanonical then
    let missingCanonicalModules := canonicalFractionModules.filter fun moduleName =>
      (environment.getModuleIdx? moduleName).isNone
    unless missingCanonicalModules.isEmpty do
      throwError m!"canonical fraction audit did not import: \
        {missingCanonicalModules.toList}"
  /- Audit user-facing declarations.  Private, compiler-generated, and
  generated `congr_simp`, recursion-equation, and induction-unfolding
  declarations are checked transitively whenever a public declaration uses
  them; an unused implementation detail is not part of the active theorem
  closure.  Unsafe and meta declarations likewise cannot occur in a
  kernel-checked theorem term.  In particular, an elaborator may use ordinary
  metaprogramming infrastructure while emitting a proof whose closure is
  independently audited here. -/
  let isUserFacing := fun name info =>
    let generatedCongruence := name.toString.endsWith ".congr_simp"
    let generatedEquation := name.toString.endsWith ".eq_def"
    let generatedInduction := name.toString.endsWith ".induct_unfolding"
    !(name.isInternal || generatedCongruence || generatedEquation ||
        generatedInduction || info.isUnsafe || Lean.isMarkedMeta environment name)
  let mut checked : Nat := 0
  let mut canonicalChecked : Nat := 0
  let mut quotientFailures : Nat := 0
  let mut quotientFailureModules : Lean.NameSet := {}
  let mut quotientBoundary : Lean.NameSet := {}
  let mut quotientBoundaryWitnesses : Lean.NameMap Lean.Name := {}
  let mut quotientTraversal : Array (Lean.Name × Lean.Name) := #[]
  let mut otherFailures : Array (Lean.Name × Array Lean.Name) := #[]
  let mut resultLines : Array String := #[]
  let isProjectDeclaration := fun name =>
    match environment.getModuleIdxFor? name with
    | some moduleIndex =>
        match importedModules[moduleIndex.toNat]? with
        | some moduleName => allProjectModuleSet.contains moduleName
        | none => false
    | none => false
  let mut modulesToScan := auditedProjectModules
  if auditCanonical then
    for moduleName in canonicalFractionModules do
      unless auditedProjectModuleSet.contains moduleName do
        modulesToScan := modulesToScan.push moduleName
  for moduleName in modulesToScan do
    let auditProjectModule := auditedProjectModuleSet.contains moduleName
    let auditCanonicalModule :=
      auditCanonical && canonicalFractionModuleSet.contains moduleName
    let some moduleIndex := environment.getModuleIdx? moduleName
      | throwError m!"axiom audit did not import: {moduleName}"
    let some moduleData := environment.header.moduleData[moduleIndex.toNat]?
      | throwError m!"axiom audit has no module data for: {moduleName}"
    let moduleNames := moduleData.constNames ++ moduleData.extraConstNames
    let mut moduleChecked : Nat := 0
    for name in moduleNames do
      if let some info := environment.constants.find? name then
        let userFacing := isUserFacing name info
        if auditCanonicalModule || (auditProjectModule && userFacing) then
          let axioms ← Lean.collectAxioms name
          let unexpected := axioms.filter fun dependency =>
            !allowed.contains dependency
          if auditProjectModule && userFacing then
            checked := checked + 1
            moduleChecked := moduleChecked + 1
          if auditCanonicalModule then
            canonicalChecked := canonicalChecked + 1
          unless unexpected.isEmpty do
            if unexpected.size == 1 && unexpected.contains ``Quot.sound then
              quotientFailures := quotientFailures + 1
              quotientFailureModules := quotientFailureModules.insert moduleName
              quotientTraversal := quotientTraversal.push (name, name)
            else
              otherFailures := otherFailures.push (name, unexpected)
    if auditProjectModule then
      resultLines := resultLines.push s!"project\t{moduleName}\t{moduleChecked}"
  /- Public declarations can reach a generated project auxiliary before
  reaching the external theorem that introduces `Quot.sound`.  Follow only
  dependency edges whose closure still contains that axiom, stopping at the
  first non-project declaration.  This reports the actionable boundary even
  when it is more than one edge below the public audit surface. -/
  let mut quotientVisited : Lean.NameSet := {}
  let mut traversalIndex : Nat := 0
  while traversalIndex < quotientTraversal.size do
    let (current, witness) := quotientTraversal[traversalIndex]!
    traversalIndex := traversalIndex + 1
    unless quotientVisited.contains current do
      quotientVisited := quotientVisited.insert current
      if let some info := environment.constants.find? current then
        for dependency in info.getUsedConstantsAsSet do
          let dependencyAxioms ← Lean.collectAxioms dependency
          if dependencyAxioms.contains ``Quot.sound then
            if isProjectDeclaration dependency then
              quotientTraversal := quotientTraversal.push (dependency, witness)
            else
              quotientBoundary := quotientBoundary.insert dependency
              unless quotientBoundaryWitnesses.contains dependency do
                quotientBoundaryWitnesses :=
                  quotientBoundaryWitnesses.insert dependency witness
  if quotientFailures == 0 && otherFailures.isEmpty then
    if auditCanonical then
      resultLines := resultLines.push s!"canonical\t@canonical\t{canonicalChecked}"
    let results := String.intercalate "\n" resultLines.toList ++ "\n"
    liftIO <| IO.FS.writeFile resultPath.getString results
    logInfo m!"audited {checked} project declarations from \
      {auditedProjectModules.size} assigned modules and \
      {canonicalChecked} strict canonical declarations; allowed axioms: \
      {[``propext]}"
  else
    let mut message := m!"unexpected project axiom closures"
    if quotientFailures != 0 then
      message := message ++ Format.line ++
        m!"{quotientFailures} declarations depend on Quot.sound across modules:"
      for moduleName in quotientFailureModules.toArray.qsort Name.lt do
        message := message ++ Format.line ++ m!"  {moduleName}"
      message := message ++ Format.line ++
        m!"external Quot.sound boundary declarations:"
      for dependency in quotientBoundary.toArray.qsort Name.lt do
        match quotientBoundaryWitnesses.find? dependency with
        | some witness =>
            message := message ++ Format.line ++
              m!"  {dependency} (first seen from {witness})"
        | none =>
            message := message ++ Format.line ++ m!"  {dependency}"
    unless otherFailures.isEmpty do
      message := message ++ Format.line ++ "other unexpected closures:"
      for (name, unexpected) in
          otherFailures.qsort fun left right => left.1.lt right.1 do
        message := message ++ Format.line ++ m!"  {name}: {unexpected.toList}"
    throwError message

end ProjectAxiomAudit
