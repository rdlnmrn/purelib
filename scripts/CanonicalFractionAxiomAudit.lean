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
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Focused `[propext]`-only audit for the independent canonical-number pilot. -/

namespace CanonicalFractionAxiomAudit

open Lean Elab Command

elab "#audit_canonical_fraction_axioms" : command => do
  let environment ← getEnv
  let auditedModules : Array Lean.Name := #[
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
  let missingModules := auditedModules.filter fun moduleName =>
    (environment.getModuleIdx? moduleName).isNone
  unless missingModules.isEmpty do
    throwError m!"canonical fraction audit did not import: {missingModules.toList}"
  let mut names : Array Lean.Name := #[]
  for moduleName in auditedModules do
    let some moduleIndex := environment.getModuleIdx? moduleName
      | throwError m!"canonical fraction audit did not import: {moduleName}"
    let some moduleData := environment.header.moduleData[moduleIndex.toNat]?
      | throwError m!"canonical fraction audit has no module data for: {moduleName}"
    for name in moduleData.constNames ++ moduleData.extraConstNames do
      if environment.constants.contains name then
        names := names.push name
  let mut checked : Nat := 0
  let mut failures : Array (Lean.Name × Array Lean.Name) := #[]
  for name in names do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun dependency => dependency != ``propext
    checked := checked + 1
    unless unexpected.isEmpty do
      failures := failures.push (name, unexpected)
  if checked == 0 then
    throwError "canonical fraction axiom audit found no declarations"
  if failures.isEmpty then
    logInfo m!"audited {checked} canonical fraction declarations; allowed axioms: [propext]"
  else
    let mut message := m!"unexpected canonical fraction axiom closures:"
    for (name, unexpected) in failures.qsort fun left right => left.1.lt right.1 do
      message := message ++ Format.line ++ m!"{name}: {unexpected.toList}"
    throwError message

end CanonicalFractionAxiomAudit

#audit_canonical_fraction_axioms
