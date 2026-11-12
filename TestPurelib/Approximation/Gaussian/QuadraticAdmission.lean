module

import Purelib.Algebra.Quadratic.Pair.Gaussian.Realization.Admission
import Purelib.Approximation.Gaussian.Acquisition.Expression.Quadratic
import Purelib.Approximation.Gaussian.Acquisition.Expression.Compile
import Purelib.Riemann.RootContinuation.SquareRootSidecar
meta import Purelib.Approximation.Gaussian.Acquisition.Expression.Compile
meta import Purelib.Approximation.Gaussian.Acquisition.Annotated.Arithmetic
meta import Purelib.Approximation.Gaussian.Provenance.Quadratic
meta import Purelib.Riemann.RootContinuation.SquareRootSidecar
meta import Purelib.Data.Rat.Fraction
meta import Purelib.Data.Gaussian.Cast

/-!
# Admission at either actual root sheet and complete original binding coverage

The executable admission accepts both original sheets at the same positive
nonsquare parameter. Complete generator inspection retains every actual
binding occurrence, including annotations without a supplied root equation.
-/

namespace TestPurelib.Approximation.Gaussian.QuadraticAdmission

open Purelib.Algebra.Quadratic.Pair.Gaussian (Realization)
open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian
open Purelib.Riemann.RootContinuation

example (sheet : Fin 2) :
    let retained := SquareRootSidecar.isolated (Cast.CoordinateTaylor.ofCoordinate 2) sheet
    ∃ accepted, (Realization.inspectRoot retained.2).outcome = .admitted accepted ∧ accepted.parameter = 2 :=
  let retained := SquareRootSidecar.isolated (Cast.CoordinateTaylor.ofCoordinate 2) sheet
  Realization.inspectRoot_positive retained.2 2
    (SquareRootSidecar.isolated_parameter (Cast.CoordinateTaylor.ofCoordinate 2) sheet)
    (by decide +kernel) (by decide +kernel)

/-- An expression with three actual leaf occurrences, including two occurrences of the same atom. -/
private def expression : Expr 2 := .mul (.add (.atom 0) (.atom 1)) (.atom 0)

example (first second : CoherentNamed) :
    let environment : Fin 2 → Annotated := fun index =>
      if index.val = 0 then Annotated.opaque first else Annotated.opaque second
    let normalized := expression.normalize environment
    normalized.inspectGenerators.attempts.map (fun entry => entry.1.val) = [2, 1, 0] :=
  let environment : Fin 2 → Annotated := fun index =>
    if index.val = 0 then Annotated.opaque first else Annotated.opaque second
  let normalized := expression.normalize environment
  normalized.inspectGenerators.indices_eq

/-- Exercise inferred and propagated coordinates at both original generator sheets. -/
private meta def checkCompiler : IO Unit := do
  for sheet in ([0, 1] : List (Fin 2)) do
    let retained := SquareRootSidecar.isolated (Cast.CoordinateTaylor.ofCoordinate 2) sheet
    let environment : Fin 1 → Annotated := fun _ => ⟨retained.1, some (.squareRoot retained.2)⟩
    let input : Expr 1 := .add (.rational 1) (.atom 0)
    let actual := input.compile environment
    match actual.provenance with
    | some (.quadratic admitted) =>
        unless admitted.admission.parameter = 2 ∧ admitted.coordinates.re = 1 ∧ admitted.coordinates.im = 1 do
          throw (IO.userError "inferred original quadratic coordinates differ")
    | _ => throw (IO.userError "the compiler did not attach admitted quadratic provenance")
    match actual.square.provenance with
    | some (.quadratic admitted) =>
        unless admitted.coordinates.re = 3 ∧ admitted.coordinates.im = 2 do
          throw (IO.userError "squaring did not reuse the admitted coordinates")
    | _ => throw (IO.userError "squaring dropped admitted quadratic provenance")
    match actual.neg.provenance with
    | some (.quadratic admitted) =>
        unless admitted.coordinates.re = -1 ∧ admitted.coordinates.im = -1 do
          throw (IO.userError "negation changed the original quadratic coordinates")
    | _ => throw (IO.userError "negation dropped admitted quadratic provenance")
    for shifted in [Annotated.add (Annotated.rational 2) actual, Annotated.add actual (Annotated.rational 2)] do
      match shifted.provenance with
      | some (.quadratic admitted) =>
          unless admitted.coordinates.re = 3 ∧ admitted.coordinates.im = 1 do
            throw (IO.userError "real scalar addition did not retain the admitted coordinates")
      | _ => throw (IO.userError "real scalar addition dropped admitted quadratic provenance")
    for scaled in [Annotated.mul (Annotated.rational 3) actual, Annotated.mul actual (Annotated.rational 3)] do
      match scaled.provenance with
      | some (.quadratic admitted) =>
          unless admitted.coordinates.re = 3 ∧ admitted.coordinates.im = 3 do
            throw (IO.userError "real scalar multiplication did not retain the admitted coordinates")
      | _ => throw (IO.userError "real scalar multiplication dropped admitted quadratic provenance")

/-- Zero-root annotations normalize through their actual rational readings on both original sheet labels. -/
private meta def checkZeroCompiler : IO Unit := do
  for sheet in ([0, 1] : List (Fin 2)) do
    let retained := SquareRootSidecar.isolated 0 sheet
    let environment : Fin 1 → Annotated := fun _ => ⟨retained.1, some (.squareRoot retained.2)⟩
    let examples : List (Expr 1 × Basic.Canonical) :=
      [(.add (.rational 1) (.atom 0), 1),
       (.mul (.add (.rational 1) (.atom 0)) (.sub (.rational 1) (.atom 0)), 1),
       (.neg (.atom 0), 0),
       (.add (.rational 3) (.root 0 sheet), 3)]
    for (expression, expected) in examples do
      unless (expression.compile environment).rationalValue = some expected do
        throw (IO.userError "zero-root expression lost its original exact rational reading")

/-- Rational-square root expressions use their cached signed reading at both original sheets and occurrences. -/
private meta def checkSquareCompiler : IO Unit := do
  let mut signs : List Basic.Canonical := []
  for sheet in ([0, 1] : List (Fin 2)) do
    let retained := SquareRootSidecar.isolated 4 sheet
    let environment : Fin 1 → Annotated := fun _ => ⟨retained.1, some (.squareRoot retained.2)⟩
    let repeated : Expr 1 := .add (.atom 0) (.atom 0)
    let normalized := repeated.normalize environment
    let first := normalized.inspections.get normalized.bindings ⟨0, by change 0 < 2; exact Nat.zero_lt_succ 1⟩
    let second := normalized.inspections.get normalized.bindings ⟨1, by change 1 < 2; exact Nat.lt_succ_self 1⟩
    match first.scalar, second.scalar with
    | some reading, some repeatedReading =>
        unless reading.value = repeatedReading.value ∧ (reading.value = 2 ∨ reading.value = -2) do
          throw (IO.userError "repeated original root occurrences lost their cached signed reading")
        signs := reading.value :: signs
        let examples : List (Expr 1 × Basic.Canonical) :=
          [(.add (.rational 1) (.atom 0), 1 + reading.value),
           (.neg (.atom 0), -reading.value),
           (.mul (.add (.atom 0) (.rational 1)) (.sub (.atom 0) (.rational 1)), 3),
           (repeated, 2 * reading.value),
           (.add (.rational 3) (.root 4 sheet), 3 + reading.value)]
        for (expression, expected) in examples do
          unless (expression.compile environment).rationalValue = some expected do
            throw (IO.userError "rational-square expression did not use its original signed scalar evidence")
    | _, _ => throw (IO.userError "rational-square normalization did not retain both scalar inspections")
  unless signs = [2, -2] ∨ signs = [-2, 2] do
    throw (IO.userError "rational-square normalization identified the original root sheets")

#eval checkSquareCompiler

#eval checkZeroCompiler

#eval checkCompiler

end TestPurelib.Approximation.Gaussian.QuadraticAdmission
