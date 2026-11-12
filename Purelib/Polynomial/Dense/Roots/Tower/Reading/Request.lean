module

public import Purelib.Polynomial.Dense.Roots.Tower.Reading.Parameters
public import Purelib.Algebra.Monogenic.Coordinates.Reading.Request
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Backward sufficient error budgets for an original root tower

The fixed original stage caches are traversed backwards from the final
requested error. Every retained stage request pays the next stage's required
input tolerance before any candidate or residual is observed.
-/

public section

namespace Purelib.Polynomial.Dense.Roots.Tower.Reading

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Algebra.Monogenic
open Purelib.Algebra.Ring (Weight)
open Purelib.Algebra.Monogenic.Cyclic.Element.Reading renaming Request → CyclicRequest
open Purelib.Data.Rat.Fraction (Rational)

universe u

set_option genInjectivity false in
/-- A complete backward budget retaining the actual sufficient request at every original stage.

The final target and initial tolerance remain indices. Each step's request
targets the same retained tail budget's initial tolerance, and its own
positive squared tolerance becomes the preceding stage's requirement.
-/
inductive Budget : {K : Type u} → [ring : CommRing K] → [equality : DecidableEq K] →
    {polynomial : DensePolynomial K} → {tower : Tower K ring equality polynomial} →
    {parent : Weight K} → {gain radius : Rational} →
    Parameters tower parent gain radius → Rational → Rational → Type (u + 1)
  /-- The same original degree-zero endpoint passes its positive target to its input unchanged. -/
  | constant {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {polynomial : DensePolynomial K}
      {parent : Weight K} {gain radius target : Rational} {degreeZero : polynomial.natDegree = 0}
      {gainNonnegative : 0 ≤ gain} {radiusNonnegative : 0 ≤ radius} (targetPositive : 0 < target) :
      Budget (.constant degreeZero gainNonnegative radiusNonnegative :
        Parameters (.constant polynomial degreeZero) parent gain radius) target target
  /-- The same original cyclic request is sufficient for the stored complete tail budget. -/
  | step {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {polynomial : DensePolynomial K}
      {adjunction : Companion.Adjunction polynomial}
      {decreases : adjunction.division.quotient.natDegree + 1 = polynomial.natDegree}
      {remaining : Tower (StageScalar adjunction) inferInstance inferInstance adjunction.division.quotient}
      {parent : Weight K} {gain radius target tolerance : Rational}
      {current : Cyclic.Element.Reading.Parameters adjunction.table parent gain radius}
      {next : Parameters remaining (Cyclic.Element.weight adjunction.table parent) current.gain radius}
      (tail : Budget next target tolerance) (request : CyclicRequest current tolerance) :
      Budget (.step current next : Parameters (.step adjunction decreases remaining) parent gain radius)
        target request.tolerance

constructive_injectivity Budget

namespace Budget

variable {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {polynomial : DensePolynomial K}
variable {tower : Tower K ring equality polynomial} {parent : Weight K} {gain radius target tolerance : Rational}
variable {parameters : Parameters tower parent gain radius}

/-- Every complete original budget has a positive initial tolerance. -/
theorem tolerance_positive (budget : Budget parameters target tolerance) : 0 < tolerance := by
  induction budget with
  | constant targetPositive => exact targetPositive
  | step _ request _ => exact request.tolerance_positive

/-- Every complete original budget retains its positive final requested target. -/
theorem target_positive (budget : Budget parameters target tolerance) : 0 < target := by
  induction budget with
  | constant targetPositive => exact targetPositive
  | step _ _ previous => exact previous

/-- Count the same original sufficient stage requests retained in a complete budget. -/
@[expose] def layers {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
    {parent : Weight K} {gain radius target tolerance : Rational} {parameters : Parameters tower parent gain radius}
    (budget : Budget parameters target tolerance) : Nat :=
  match tower, parameters, target, tolerance, budget with
  | .constant _ _, .constant _ _ _, _, _, .constant _ => 0
  | .step _ _ _, .step _ _, _, _, .step tail _ => layers tail + 1

/-- The complete budget retains one request for every same original cached adjunction. -/
theorem layers_eq_parameters (budget : Budget parameters target tolerance) : budget.layers = parameters.layers := by
  induction budget with
  | constant => rfl
  | step _ _ previous => exact congrArg Nat.succ previous

end Budget

set_option genInjectivity false in
/-- A materialized positive initial tolerance with its complete source-indexed backward budget.

The final target and original parameter chain remain indices. The stored
tolerance is computed by the retained budget rather than supplied as a
separate unexplained refinement budget.
-/
structure Request {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {polynomial : DensePolynomial K}
    {tower : Tower K ring equality polynomial} {parent : Weight K} {gain radius : Rational}
    (parameters : Parameters tower parent gain radius) (target : Rational) where
  /-- The computed initial error tolerance for the same original tower. -/
  tolerance : Rational
  /-- The computed initial tolerance is positive. -/
  positive : 0 < tolerance
  /-- The complete original sufficient stage requests producing this tolerance. -/
  budget : Budget parameters target tolerance

constructive_injectivity Request

namespace Request

/-- Compute a complete backward sufficient budget from the same fixed original stage caches. -/
@[expose] def prepare {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
    {parent : Weight K} {gain radius : Rational} (parameters : Parameters tower parent gain radius)
    (target : Rational) (targetPositive : 0 < target) : Request parameters target :=
  match tower, parameters with
  | .constant _ _, .constant _ _ _ =>
      { tolerance := target, positive := targetPositive, budget := .constant targetPositive }
  | .step _ _ _, .step current next =>
      let tail := prepare next target targetPositive
      let request := CyclicRequest.prepare current tail.tolerance tail.positive
      { tolerance := request.tolerance, positive := request.tolerance_positive, budget := .step tail.budget request }

variable {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {polynomial : DensePolynomial K}
variable {tower : Tower K ring equality polynomial} {parent : Weight K} {gain radius target : Rational}
variable {parameters : Parameters tower parent gain radius}

/-- The computed request budget covers the same original source degree exactly. -/
theorem layers_eq_degree (request : Request parameters target) : request.budget.layers = polynomial.natDegree :=
  request.budget.layers_eq_parameters.trans parameters.layers_eq_degree

end Request

end Purelib.Polynomial.Dense.Roots.Tower.Reading

end
