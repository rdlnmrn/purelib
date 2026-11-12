module

public import Purelib.Polynomial.Dense.Roots.Tower.Reading.Request
public import Purelib.Polynomial.Dense.Roots.Tower.Leading
public import Purelib.Polynomial.Dense.Gaussian.Interpolation.Schedule
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Source-residual requests for the original tower

Each retained generator request becomes a positive source-polynomial target
using one cached original Gaussian inverse norm. A shared positive cap can
also pay the geometric correction at the terminal linear adjunction. One
backward interpolation schedule then prepays every same original quotient.
-/

public section

namespace Purelib.Polynomial.Dense.Roots.Tower.Reading

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Algebra.Ring (Weight)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction

universe u

namespace Budget

/-- Convert every same original stage request to a scaled, capped source-residual target. -/
@[expose] def targets {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
    {parent : Weight K} {gain radius target tolerance : Rational} {parameters : Parameters tower parent gain radius}
    (budget : Budget parameters target tolerance) (scale cap : Rational) : List Rational :=
  match tower, parameters, target, tolerance, budget with
  | .constant _ _, .constant _ _ _, _, _, .constant _ => []
  | .step _ _ _, .step _ _, _, _, .step tail request =>
      min (scale * request.tolerance) cap :: targets tail scale cap

variable {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {polynomial : DensePolynomial K}
variable {tower : Tower K ring equality polynomial} {parent : Weight K} {gain radius target tolerance : Rational}
variable {parameters : Parameters tower parent gain radius}

/-- Positive scale and cap give positive source targets before any original observations. -/
theorem targets_positive (budget : Budget parameters target tolerance) {scale cap : Rational}
    (scalePositive : 0 < scale) (capPositive : 0 < cap) :
    ∀ value ∈ budget.targets scale cap, 0 < value := by
  induction budget with
  | constant => intro value member; cases member
  | step _ request previous =>
      intro value member
      cases member with
      | head =>
          exact Order.Basic.lt_min
            (Order.Arithmetic.mul_pos_direct scalePositive request.tolerance_positive) capPositive
      | tail _ member => exact previous value member

/-- The source-target list retains exactly one entry per original sufficient stage request. -/
theorem targets_length (budget : Budget parameters target tolerance) (scale cap : Rational) :
    (budget.targets scale cap).length = budget.layers := by
  induction budget with
  | constant => rfl
  | step _ _ previous => exact congrArg Nat.succ previous

end Budget

set_option genInjectivity false in
/-- Cached source targets and their sufficient original interpolation schedule.

The original tower budget and its proof-only scalar-leading invariant remain
indices. The Gaussian inverse, its norm, scale, ordered target list and whole
schedule are each computed once before geometric observations. The cap is a
positive source-residual demand, rather than a refinement count.
-/
structure Sources {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
    {parent : Weight K} {gain radius target tolerance : Rational} {parameters : Parameters tower parent gain radius}
    (budget : Budget parameters target tolerance) {embed : Canonical → K} {coefficient : Canonical}
    (leading : Leading tower embed coefficient) (separation cap : Rational) where
  /-- The retained original pair-separation floor is positive. -/
  separationPositive : 0 < separation
  /-- The additional original source-residual demand is positive. -/
  capPositive : 0 < cap
  /-- The once-computed inverse of the original Gaussian leading coefficient. -/
  coefficientInverse : Canonical
  /-- The inverse is the original total Gaussian inverse. -/
  coefficientInverse_eq : coefficientInverse = coefficient⁻¹
  /-- The once-computed quadrance of that same inverse. -/
  inverseNorm : Rational
  /-- The norm belongs to the same retained original inverse. -/
  inverseNorm_eq : inverseNorm = Norm.Basic.normSq coefficientInverse
  /-- The same retained norm is nonnegative. -/
  inverseNormNonnegative : 0 ≤ inverseNorm
  /-- The shared positive denominator computed once from the same retained norm. -/
  denominator : Rational
  /-- The denominator leaves a unit margin above the inverse norm. -/
  denominator_eq : denominator = 1 + inverseNorm
  /-- The same denominator is positive. -/
  denominatorPositive : 0 < denominator
  /-- The sufficient shared source-to-generator scale. -/
  scale : Rational
  /-- The scale is the original rational division computed once. -/
  scale_eq : scale = 1 / denominator
  /-- The same scale is positive. -/
  scalePositive : 0 < scale
  /-- One cached source-residual target per same original budget layer. -/
  targets : List Rational
  /-- Every target uses that original layer's request, shared scale and original cap. -/
  targets_eq : targets = budget.targets scale cap
  /-- Every retained target is positive. -/
  targetsPositive : ∀ value ∈ targets, 0 < value
  /-- The complete original interpolation schedule paying all these targets. -/
  schedule : Interpolation.Schedule.Prepared separation targets
  /-- The schedule is the same original sufficient constructor on these cached targets. -/
  schedule_eq : schedule = Interpolation.Schedule.prepare separation separationPositive targets targetsPositive

constructive_injectivity Sources

namespace Sources

/-- Prepare source targets from the same retained leading inverse and norm before observing any nodes.

Both original cache equalities remain explicit. The denominator, scale,
ordered targets and complete schedule are computed once from those same
retained values, without another Gaussian inverse or norm calculation.
-/
@[expose] def ofInverseNorm {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
    {parent : Weight K} {gain radius target tolerance : Rational} {parameters : Parameters tower parent gain radius}
    (budget : Budget parameters target tolerance) {embed : Canonical → K} {coefficient : Canonical}
    (leading : Leading tower embed coefficient) (separation cap : Rational)
    (separationPositive : 0 < separation) (capPositive : 0 < cap)
    (coefficientInverse : Canonical) (coefficientInverseEq : coefficientInverse = coefficient⁻¹)
    (inverseNorm : Rational) (inverseNormEq : inverseNorm = Norm.Basic.normSq coefficientInverse) :
    Sources budget leading separation cap :=
  have inverseNormNonnegative : 0 ≤ inverseNorm := inverseNormEq.symm ▸ Norm.Basic.normSq_nonneg coefficientInverse
  let denominator := 1 + inverseNorm
  have denominatorPositive : 0 < denominator :=
    Order.Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide) inverseNormNonnegative
  let scale := 1 / denominator
  have scalePositive : 0 < scale := Order.Field.div_pos_direct (by decide) denominatorPositive
  let targets := budget.targets scale cap
  have targetsPositive := budget.targets_positive scalePositive capPositive
  let schedule := Interpolation.Schedule.prepare separation separationPositive targets targetsPositive
  { separationPositive, capPositive, coefficientInverse, coefficientInverse_eq := coefficientInverseEq
    inverseNorm, inverseNorm_eq := inverseNormEq, inverseNormNonnegative, denominator, denominator_eq := rfl
    denominatorPositive, scale, scale_eq := rfl, scalePositive, targets, targets_eq := rfl
    targetsPositive, schedule, schedule_eq := rfl }

/-- Prepare the same original inverse and its norm once, then consume their retained values in source scheduling. -/
@[expose] def prepare {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
    {parent : Weight K} {gain radius target tolerance : Rational} {parameters : Parameters tower parent gain radius}
    (budget : Budget parameters target tolerance) {embed : Canonical → K} {coefficient : Canonical}
    (leading : Leading tower embed coefficient) (separation cap : Rational)
    (separationPositive : 0 < separation) (capPositive : 0 < cap) : Sources budget leading separation cap :=
  let coefficientInverse := coefficient⁻¹
  let inverseNorm := Norm.Basic.normSq coefficientInverse
  ofInverseNorm budget leading separation cap separationPositive capPositive coefficientInverse rfl inverseNorm rfl

/-- The same retained original inverse and norm preserve the complete original source preparation value. -/
theorem ofInverseNorm_eq_prepare {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
    {parent : Weight K} {gain radius target tolerance : Rational} {parameters : Parameters tower parent gain radius}
    (budget : Budget parameters target tolerance) {embed : Canonical → K} {coefficient : Canonical}
    (leading : Leading tower embed coefficient) (separation cap : Rational)
    (separationPositive : 0 < separation) (capPositive : 0 < cap)
    (coefficientInverse : Canonical) (coefficientInverseEq : coefficientInverse = coefficient⁻¹)
    (inverseNorm : Rational) (inverseNormEq : inverseNorm = Norm.Basic.normSq coefficientInverse) :
    ofInverseNorm budget leading separation cap separationPositive capPositive
        coefficientInverse coefficientInverseEq inverseNorm inverseNormEq =
      prepare budget leading separation cap separationPositive capPositive := by
  cases coefficientInverseEq
  cases inverseNormEq
  rfl

variable {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {polynomial : DensePolynomial K}
variable {tower : Tower K ring equality polynomial} {parent : Weight K} {gain radius target tolerance : Rational}
variable {parameters : Parameters tower parent gain radius} {budget : Budget parameters target tolerance}
variable {embed : Canonical → K} {coefficient : Canonical} {leading : Leading tower embed coefficient}
variable {separation cap : Rational}

/-- The same stored schedule supplies a positive initial source-sample tolerance. -/
theorem initial_positive (sources : Sources budget leading separation cap) : 0 < sources.schedule.val.initial :=
  sources.schedule.property.positive

/-- The retained source targets cover every same original adjunction exactly once. -/
theorem targets_length_eq_degree (sources : Sources budget leading separation cap) :
    sources.targets.length = polynomial.natDegree :=
  (congrArg List.length sources.targets_eq).trans
    ((budget.targets_length sources.scale cap).trans
      (budget.layers_eq_parameters.trans parameters.layers_eq_degree))

/-- The cached scaling pays the same original leading-inverse norm without a nonzero-norm premise. -/
theorem scale_mul_norm_le_one (sources : Sources budget leading separation cap) :
    sources.scale * sources.inverseNorm ≤ 1 := by
  have bounded : sources.inverseNorm ≤ sources.denominator := by
    rewrite [sources.denominator_eq]
    have retained := Order.Arithmetic.add_le_add_direct (by decide : (0 : Rational) ≤ 1)
      (le_refl sources.inverseNorm)
    rewrite [zero_add] at retained
    exact retained
  have unit : sources.scale * sources.denominator = 1 := by
    rewrite [sources.scale_eq]
    exact Fraction.Field.div_mul_cancel_of_ne 1 sources.denominator sources.denominatorPositive.ne'
  exact (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded sources.scalePositive.le).trans unit.le

/-- A paid original source residual supplies the generator-column tolerance of its same budget layer. -/
theorem scaled_residual_le (sources : Sources budget leading separation cap) {epsilon residual : Rational}
    (epsilonNonnegative : 0 ≤ epsilon)
    (bounded : residual ≤ min (sources.scale * epsilon) cap) : residual * sources.inverseNorm ≤ epsilon := by
  have sourceBound := bounded.trans (Order.Basic.min_le_left _ _)
  calc
    residual * sources.inverseNorm ≤ (sources.scale * epsilon) * sources.inverseNorm :=
      Order.Arithmetic.mul_le_mul_of_nonneg_right_direct sourceBound sources.inverseNormNonnegative
    _ = (sources.scale * sources.inverseNorm) * epsilon := by
      rewrite [Fraction.mul_assoc, Fraction.mul_comm epsilon sources.inverseNorm, ← Fraction.mul_assoc]
      rfl
    _ ≤ 1 * epsilon :=
      Order.Arithmetic.mul_le_mul_of_nonneg_right_direct sources.scale_mul_norm_le_one epsilonNonnegative
    _ = epsilon := Fraction.one_mul _

/-- The same paid source target also satisfies its original geometric correction demand. -/
theorem capped_residual_le (sources : Sources budget leading separation cap) {epsilon residual : Rational}
    (bounded : residual ≤ min (sources.scale * epsilon) cap) : residual ≤ cap :=
  bounded.trans (Order.Basic.min_le_right _ _)

end Sources

end Purelib.Polynomial.Dense.Roots.Tower.Reading

end
