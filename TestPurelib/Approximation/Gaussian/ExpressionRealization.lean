module

import Purelib.Approximation.Gaussian.Acquisition.Expression.Compile
import Purelib.Approximation.Gaussian.Acquisition.Expression.Realization
import Purelib.Riemann.RootContinuation.SquareRootSidecar
meta import Purelib.Approximation.Gaussian.Acquisition.Expression.Compile
meta import Purelib.Approximation.Gaussian.Acquisition.Expression.Realization
meta import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
meta import Purelib.Approximation.Gaussian.Name.Coherent
meta import Purelib.Riemann.RootContinuation.SquareRootSidecar
meta import Purelib.Data.Gaussian.Cast

/-!
# Acquisition from original composite coordinate bindings

The original input is `1+r` on either retained root sheet. Polynomial arithmetic
uses this input's admitted coordinates without asserting a pure-power equation
for it. Cancelled opaque occurrences remain in the original table; active
opaque inputs and nonreal coefficient adapters retain unresolved attempts.
-/

namespace TestPurelib.Approximation.Gaussian.ExpressionRealization

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian
open Purelib.Riemann.RootContinuation

/-- Exercise owner-preserving composite inference and both kinds of unresolved original condition. -/
private meta def checkComposite : IO Unit := do
  for sheet in ([0, 1] : List (Fin 2)) do
    let root := SquareRootSidecar.isolated 2 sheet
    let rootEnvironment : Fin 1 → Annotated := fun _ => ⟨root.1, some (.squareRoot root.2)⟩
    let input := (Expr.add (.rational 1) (.atom 0)).compile rootEnvironment
    let environment : Fin 2 → Annotated := fun index =>
      if index.val = 0 then input else Annotated.opaque (CoherentNamed.Coherence.exact (⟨0, 1⟩ : Basic.Canonical))
    let product : Expr 2 := .mul (.atom 0) (.add (.atom 0) (.rational 1))
    let cancellation : Expr 2 := .sub (.add (.atom 1) (.rational 3)) (.add (.rational 3) (.atom 1))
    let examples := [(product, (4, 3)),
      (.mul (.add (.atom 0) (.rational 1)) (.sub (.atom 0) (.rational 1)), (2, 2)),
      (.add cancellation product, (4, 3))]
    for (expression, expected) in examples do
      let original := expression.retain environment
      let actual := original.infer
      match actual.provenance with
      | some (.quadratic result) =>
          unless result.coordinates.re = expected.1 ∧ result.coordinates.im = expected.2 do
            throw (IO.userError "composite binding evaluation changed the original pair coordinates")
          unless result.admission.parameter = 2 do
            throw (IO.userError "composite binding evaluation changed the original admitted parameter")
      | _ => throw (IO.userError "supported original composite bindings did not receive coordinate evidence")
    let blocked : List (Expr 2) := [.add (.atom 0) (.atom 1), .mul (.rational (⟨0, 1⟩ : Basic.Canonical)) (.atom 0)]
    for expression in blocked do
      let normalized := expression.normalize environment
      let checked := normalized.inspectGenerators
      unless checked.evidence.isNone do
        throw (IO.userError "unsupported original coordinate conditions received admitted evidence")
      let mut retainedAttempt := false
      for attempt in checked.attempts do
        match attempt.2 with
        | .composite _ _ result =>
            match result.outcome with
            | .unresolved _ => retainedAttempt := true
            | .ready _ _ _ _ => throw (IO.userError "an incomplete original-form attempt reported success")
        | _ => pure ()
      unless retainedAttempt do
        throw (IO.userError "the original composite attempt and its unmet conditions were discarded")

#eval checkComposite

end TestPurelib.Approximation.Gaussian.ExpressionRealization
