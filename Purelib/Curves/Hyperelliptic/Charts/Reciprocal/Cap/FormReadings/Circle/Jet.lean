module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Program
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Bounds
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Jet
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Laurent.Program
import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral.Dyadic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Bounds
import Purelib.Integration.Polynomial.Gaussian.Path.Uniform
import Purelib.Integration.Polynomial.Gaussian.Path.Errors
import Purelib.Integration.Polynomial.Gaussian.Path.ConstantComparison
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Approximation.Rational.Request.Common
import Purelib.Tactic.Ring

/-! # Actual finite Laurent observations on the retained total-form circle banks -/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Readings

open Purelib.Approximation.Rational
open Purelib.Polynomial.Dense.Gaussian

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.List
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (ParameterPrimitives)
open Purelib.RationalFunctions.Curve (RationalCurve)
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.RationalFunctions.Curve.Canonical.Circle.Integral
open Purelib.Riemann.Branches.ClearSheetContinuation
open Purelib.Riemann.RootContinuation.CertifiedSquareRoot (Certificate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational.Request
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence.Observation
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Geometry.Gaussian.UnitCircle

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
  {differential : OddPowerDifferential curve.polynomial} {base : Canonical}
  {unitBound : Norm.Basic.normSq base ≤ 1}
  {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
  {actual : { value : RationalCurve // value = circle base }}
  {depth : Nat} {left right : Endpoint} {target : Fraction.Rational}

/-- Original finite expansion caches at every bounded occurrence of the same supplied whole reading bank.

Every entry is indexed by that exact original whole reading, not merely
its coefficient value. The original principal product and primitive are
shared outside the entry family; all actual local error caches remain stored.
-/
abbrev Jets (stored : Readings differential cap base unitBound collarBound actual depth left right target)
    (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (polynomial : { value : Dense.Basic.DensePolynomial Canonical //
      value = Reciprocal.padded differential.numerator (2 * genus) })
    (retained : jet.Principal polynomial.val differential.scale)
    (primitive : Antiderivative.ReciprocalPrimitive retained.val genus)
    (expandedTarget accuracy : Fraction.Rational) :=
  DependentProduct (dyadicEdges depth left right) fun index =>
    Reading.Jet (stored.get index) origin jet remainder polynomial retained primitive expandedTarget accuracy

/-- Map the original actual reading bank linearly to retained finite expansion observations.

The supplied factor handler prepares only the original guarded factor at
the actual stored numerical certificate. The original principal product,
primitive and setup handler remain outside the linear dependent traversal.
Each original whole reading is passed directly to its expansion constructor.
-/
def jets (stored : Readings differential cap base unitBound collarBound actual depth left right target)
    (nonzero : base ≠ 0) (pairs : differential.denominatorPairs = 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus)
    (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (polynomial : { value : Dense.Basic.DensePolynomial Canonical //
      value = Reciprocal.padded differential.numerator (2 * genus) })
    (retained : jet.Principal polynomial.val differential.scale)
    (primitive : Antiderivative.ReciprocalPrimitive retained.val genus)
    (prepareFactor : (index : Fin (dyadicEdges depth left right).length) →
      (reading : Reading differential cap
        (actual.val.point ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter)
        (point_inside base unitBound collarBound actual
          ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter) target) →
      (coefficientCache : { value : Canonical // value = Evaluation.eval jet.val
        (Primitives.point curve
          (actual.val.point ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter)) }) →
      Division.Prepared (origin.certificate.value.add
        (reading.1.1.certificate.value.mul (Coherence.exact coefficientCache.val))))
    (expandedTarget : Fraction.Rational) (expandedPositive : 0 < expandedTarget)
    (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy :=
  DependentProduct.map (dyadicEdges depth left right) stored
    (fun _index reading =>
      Reading.Jet reading origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (fun index reading => reading.jet
      (point_nonzero base nonzero actual ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter)
      pairs bound origin jet remainder polynomial retained primitive (prepareFactor index reading)
      expandedTarget expandedPositive accuracy positive)

namespace Jets

open Purelib.Data.Rat.Fraction.Order

variable {stored : Readings differential cap base unitBound collarBound actual depth left right target}
  {origin : Owners.Point cap 0} {jet : InfinityCoefficients.Jet curve}
  {remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val}
  {polynomial : { value : Dense.Basic.DensePolynomial Canonical //
    value = Reciprocal.padded differential.numerator (2 * genus) }}
  {retained : jet.Principal polynomial.val differential.scale}
  {primitive : Antiderivative.ReciprocalPrimitive retained.val genus}
  {expandedTarget accuracy : Fraction.Rational}

/-- The original guarded root-error setup and one retained Horner cache for the original padded numerator.

Both components keep the same curve, origin, jet and residual parents. The
Horner certificate retains the actual padded polynomial and collar box;
no alternative error channel or successful residue comparison is stored.
-/
abbrev ErrorBounds (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (polynomial : { value : Dense.Basic.DensePolynomial Canonical //
      value = Reciprocal.padded differential.numerator (2 * genus) }) :=
  ((radius : { value : Fraction.Rational // 0 < value }) ×
    (upper : { value : Fraction.Rational // 0 < value }) ×
      RootCoordinates.JetErrorBound origin jet remainder radius.val radius.property.le upper.val) ×
    { value : Polynomial.Bounds.Horner //
      value = Dense.Gaussian.Bounds.Box.denseHornerNormBounds polynomial.val collar.box }

/-- Prepare the original guarded error handler and padded-numerator Horner fold once outside all circle entries. -/
def prepareErrorBound (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (polynomial : { value : Dense.Basic.DensePolynomial Canonical //
      value = Reciprocal.padded differential.numerator (2 * genus) }) :
    ErrorBounds origin jet remainder polynomial :=
  let root := RootCoordinates.prepareJetErrorBound origin jet remainder
  let horner := Dense.Gaussian.Bounds.Box.denseHornerNormBounds polynomial.val collar.box
  (root, ⟨horner, rfl⟩)

/-- The setup retains the complete original root-error radius, ceiling and comparison handler unchanged. -/
theorem prepareErrorBound_root (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (polynomial : { value : Dense.Basic.DensePolynomial Canonical //
      value = Reciprocal.padded differential.numerator (2 * genus) }) :
    (prepareErrorBound origin jet remainder polynomial).1 =
      RootCoordinates.prepareJetErrorBound origin jet remainder := by
  unfold prepareErrorBound
  rfl

/-- The setup retains the actual whole padded-numerator Horner value-and-slope cache. -/
theorem prepareErrorBound_horner (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (polynomial : { value : Dense.Basic.DensePolynomial Canonical //
      value = Reciprocal.padded differential.numerator (2 * genus) }) :
    (prepareErrorBound origin jet remainder polynomial).2 =
      ⟨Dense.Gaussian.Bounds.Box.denseHornerNormBounds polynomial.val collar.box, rfl⟩ := by
  unfold prepareErrorBound
  rfl

namespace ErrorBounds

/-- The retained scalar ceiling bounds the original chart degree, scale and padded-numerator multiplier. -/
def clearedUpper (bounds : ErrorBounds origin jet remainder polynomial) : Fraction.Rational :=
  Norm.Basic.normSq (Primitives.degree curve : Canonical) *
    (Norm.Basic.normSq differential.scale * bounds.2.val.value)

/-- The cleared coefficient ceiling is nonnegative by the same retained Horner fold. -/
theorem clearedUpper_nonnegative (bounds : ErrorBounds origin jet remainder polynomial) :
    0 ≤ bounds.clearedUpper := by
  have hornerNonnegative : 0 ≤ bounds.2.val.value := by
    rewrite [bounds.2.property]
    exact (Dense.Gaussian.Bounds.Box.denseHornerNormBounds_nonneg polynomial.val collar.box).1
  exact Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg _)
    (Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg _) hornerNonnegative)

/-- The actual cleared multiplier at every point of the same collar obeys the cached polynomial ceiling. -/
theorem cleared_normSq_le (bounds : ErrorBounds origin jet remainder polynomial)
    (parameter : Canonical) (inside : collar.box.Contains (Primitives.point curve parameter)) :
    Norm.Basic.normSq ((Primitives.degree curve : Canonical) *
      (-differential.scale * polynomial.val.eval (Primitives.point curve parameter))) ≤ bounds.clearedUpper := by
  have polynomialBound : Norm.Basic.normSq (polynomial.val.eval (Primitives.point curve parameter)) ≤
      bounds.2.val.value := by
    rewrite [bounds.2.property]
    exact Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound polynomial.val inside
  rewrite [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul, Norm.Basic.normSq_neg]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct polynomialBound (Norm.Basic.normSq_nonneg _))
    (Norm.Basic.normSq_nonneg _)

/-- The actual finite error-reading ceiling keeps the bounded root error and separate semantic observation payment. -/
def readingUpper (bounds : ErrorBounds origin jet remainder polynomial) (target : Fraction.Rational) :
    Fraction.Rational :=
  64 * target + 4 * (4 * (bounds.clearedUpper * (bounds.1.2.1.val + target)) + target)

/-- A positive original observation target makes the same retained finite error-reading ceiling nonnegative. -/
theorem readingUpper_nonnegative (bounds : ErrorBounds origin jet remainder polynomial)
    {target : Fraction.Rational} (positive : 0 < target) : 0 ≤ bounds.readingUpper target := by
  unfold readingUpper
  have coefficientNonnegative := clearedUpper_nonnegative bounds
  have sumNonnegative : 0 ≤ bounds.1.2.1.val + target :=
    add_nonneg bounds.1.2.1.property.le positive.le
  have productNonnegative : 0 ≤ bounds.clearedUpper * (bounds.1.2.1.val + target) :=
    Arithmetic.mul_nonneg_direct coefficientNonnegative sumNonnegative
  have scaledNonnegative : 0 ≤ 4 * (bounds.clearedUpper * (bounds.1.2.1.val + target)) :=
    Arithmetic.mul_nonneg_direct (by decide) productNonnegative
  have innerNonnegative : 0 ≤ 4 * (bounds.clearedUpper * (bounds.1.2.1.val + target)) + target :=
    add_nonneg scaledNonnegative positive.le
  have outerNonnegative : 0 ≤ 4 * (4 * (bounds.clearedUpper * (bounds.1.2.1.val + target)) + target) :=
    Arithmetic.mul_nonneg_direct (by decide) innerNonnegative
  have firstNonnegative : 0 ≤ 64 * target :=
    Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 64) (by decide)) positive.le
  exact add_nonneg firstNonnegative outerNonnegative

/-- The actual saved error operand reading is uniformly bounded by the original guarded setup and numerator cache.

The supplied finite square membership pays the original root handler at
this same coordinate. The actual Point view, H/E values, Prepared factor
and full retained quotient chain are passed to that handler unchanged.
The cached numerator ceiling then bounds the same original multiplier.
-/
theorem reading_bound (bounds : ErrorBounds origin jet remainder polynomial)
    {parameter : Canonical} {inside : collar.box.Contains (Primitives.point curve parameter)}
    {reading : Reading differential cap parameter inside target}
    (entry : Reading.Jet reading origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (positive : 0 < expandedTarget)
    (near : (Geometry.Rational.Box.symmetric bounds.1.1.val bounds.1.1.property.le).Contains
      (Primitives.point curve parameter)) :
    Norm.Basic.normSq entry.parts.val.2.value ≤ bounds.readingUpper expandedTarget := by
  let regular := Owners.Point.build cap (Primitives.point curve parameter) inside reading.1.1
  let certificate : { value : Certificate (cap.polynomial.eval (Primitives.point curve parameter)) //
      value = regular.certificate } :=
    ⟨reading.1.1.certificate, (Owners.Point.build_certificate cap _ inside reading.1.1).symm⟩
  let compared := bounds.1.2.2 (Primitives.point curve parameter) regular certificate
    entry.1 entry.2.1 entry.2.2.1 entry.error near 0 0 expandedTarget positive
  have paid := entry.error_normSq_le positive bounds.1.2.1.val compared
  have coefficientBound := bounds.cleared_normSq_le parameter inside
  have productBound := Arithmetic.mul_le_mul_of_nonneg_right_direct coefficientBound
    (add_nonneg bounds.1.2.1.property.le positive.le)
  have inner := Arithmetic.add_le_add_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct productBound (by decide : (0 : Fraction.Rational) ≤ 4))
    (Fraction.Order.Basic.le_refl expandedTarget)
  exact paid.trans (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
    (Arithmetic.mul_le_mul_of_nonneg_left_direct inner (by decide : (0 : Fraction.Rational) ≤ 4)))

end ErrorBounds

/-- Read one complete actual expansion cache at its same bounded original total-form occurrence. -/
@[expose] def get (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (index : Fin (dyadicEdges depth left right).length) :
    Reading.Jet (stored.get index) origin jet remainder polynomial retained primitive expandedTarget accuracy :=
  DependentProduct.get (dyadicEdges depth left right) expanded index

/-- The actual finite expansion cell, or its original observation difference, at one retained dyadic occurrence. -/
private def cell (edge : ParameterEdge) (first last : Canonical)
    (difference : Bool) (allowance : { value : Fraction.Rational // 0 ≤ value }) : CellModel :=
  let value := if difference then first - last else last
  let original := coefficientCell base actual (fun _ => value)
    edge.left.parameter (edge.right.parameter - edge.left.parameter)
  original.weakenAllowance allowance.val (by change 0 ≤ allowance.val; exact allowance.property)

/-- The ordered actual expanded-form cells or their original observed difference, with a supplied local budget.

Both branches consume the same retained observation comparisons. Their
left and right readings are projections of the actual original comparison
cache; no original numerical root, error channel or request is rebuilt.
-/
def model (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (difference : Bool) (allowance : { value : Fraction.Rational // 0 ≤ value }) : PathModel :=
  ⟨DependentProduct.mapToList (dyadicEdges depth left right) expanded fun index entry =>
    cell (base := base) (actual := actual) ((dyadicEdges depth left right)[index.val]'index.isLt)
      entry.comparison.leftObservation.value entry.comparison.rightObservation.value difference allowance⟩

/-- The actual expansion model has the same original bounded dyadic occurrence count. -/
theorem model_count
    (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (difference : Bool) (allowance : { value : Fraction.Rational // 0 ≤ value }) :
    (expanded.model difference allowance).cells.length = 2 ^ depth := by
  unfold model
  exact (DependentProduct.length_mapToList (dyadicEdges depth left right) expanded _).trans
    (dyadicEdges_length depth left right)

/-- The actual mapped cell keeps the original parameter displacement and its same stored coefficient value. -/
private theorem cell_sample (edge : ParameterEdge) (first last : Canonical)
    (difference : Bool) (allowance : { value : Fraction.Rational // 0 ≤ value }) :
    (cell (base := base) (actual := actual) edge first last difference allowance).integralSample =
      Stereographic.Tangent.increment (edge.right.parameter - edge.left.parameter) *
        (velocity base edge.left.parameter * (if difference then first - last else last)) := by
  unfold cell
  rewrite [CellModel.weakenAllowance_integralSample, coefficientCell_integralSample]
  rfl

/-- The same original cell samples retain exact scalar subtraction and its supplied whole reference coefficient. -/
private theorem cell_scalar_difference (edge : ParameterEdge) (first multiplier : Canonical)
    (coefficient : Canonical → Canonical) (allowance payment : { value : Fraction.Rational // 0 ≤ value }) :
    (cell (base := base) (actual := actual) edge first
      (coefficient (actual.val.point edge.left.parameter) * multiplier) true payment).integralSample =
      1 * (cell (base := base) (actual := actual) edge 0 first false allowance).integralSample +
        (-multiplier) * (coefficientCell base actual coefficient edge.left.parameter
          (edge.right.parameter - edge.left.parameter)).integralSample := by
  rewrite [cell_sample, cell_sample, coefficientCell_integralSample]
  let increment := Stereographic.Tangent.increment (edge.right.parameter - edge.left.parameter)
  let rate := velocity base edge.left.parameter
  let value := coefficient (actual.val.point edge.left.parameter)
  change increment * (rate * (first - value * multiplier)) =
    1 * (increment * (rate * first)) + (-multiplier) * (increment * (rate * value))
  ring1

/-- Pointwise linear combinations commute with the ordered original dependent-product cell-sample fold. -/
private theorem mapped_sample_linear {Item : Type u} (firstWeight lastWeight : Canonical) :
    (items : List Item) → {family : Fin items.length → Type v} → (entries : DependentProduct items family) →
    (first last combined : (index : Fin items.length) → family index → CellModel) →
    (∀ index entry, (combined index entry).integralSample =
      firstWeight * (first index entry).integralSample + lastWeight * (last index entry).integralSample) →
    (PathModel.mk (DependentProduct.mapToList items entries combined)).integralSample =
      firstWeight * (PathModel.mk (DependentProduct.mapToList items entries first)).integralSample +
        lastWeight * (PathModel.mk (DependentProduct.mapToList items entries last)).integralSample
  | [], _, _, _, _, _, _ => by change (0 : Canonical) = firstWeight * 0 + lastWeight * 0; ring1
  | _ :: remaining, _, entries, first, last, combined, same => by
      change (combined 0 entries.1).integralSample +
        (PathModel.mk (DependentProduct.mapToList remaining entries.2
          (fun index entry => combined index.succ entry))).integralSample =
        firstWeight * ((first 0 entries.1).integralSample +
          (PathModel.mk (DependentProduct.mapToList remaining entries.2
            (fun index entry => first index.succ entry))).integralSample) +
        lastWeight * ((last 0 entries.1).integralSample +
          (PathModel.mk (DependentProduct.mapToList remaining entries.2
            (fun index entry => last index.succ entry))).integralSample)
      rewrite [same 0 entries.1, mapped_sample_linear firstWeight lastWeight remaining entries.2
        (fun index entry => first index.succ entry) (fun index entry => last index.succ entry)
        (fun index entry => combined index.succ entry) (fun index entry => same index.succ entry)]
      ring1

/-- The actual total-form stage sample splits into its actual expanded sample and the retained observed difference.

Both terms consume the same original dyadic occurrences, observations and
tangent values. The original model allowance may be supplied independently;
no equality of coefficient functions or successful integral comparison is
assumed in this finite exact sample identity.
-/
theorem model_difference
    (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (sourceAllowance : Option { value : Fraction.Rational // 0 ≤ value })
    (targetAllowance errorAllowance : { value : Fraction.Rational // 0 ≤ value }) :
    (expanded.model true errorAllowance).integralSample =
      (stored.model sourceAllowance).integralSample - (expanded.model false targetAllowance).integralSample := by
  let original := fun (index : Fin (dyadicEdges depth left right).length)
      (_entry : Reading.Jet (stored.get index) origin jet remainder polynomial
        retained primitive expandedTarget accuracy) =>
    readingCell differential cap base unitBound collarBound actual target
      ((dyadicEdges depth left right)[index.val]'index.isLt) (stored.get index) none sourceAllowance
  have sourceCells : (stored.model sourceAllowance).cells =
      DependentProduct.mapToList (dyadicEdges depth left right) expanded original := by
    rewrite [Readings.model, cells_eq]
    apply DependentProduct.mapToList_eq_of_get
    intro index
    dsimp only [original]
    rewrite [get_eq]
    rfl
  have same (index : Fin (dyadicEdges depth left right).length)
      (entry : Reading.Jet (stored.get index) origin jet remainder polynomial
        retained primitive expandedTarget accuracy) :
      (cell (base := base) (actual := actual) ((dyadicEdges depth left right)[index.val]'index.isLt)
        entry.comparison.leftObservation.value entry.comparison.rightObservation.value
        true errorAllowance).integralSample =
        (original index entry).integralSample - (cell (base := base) (actual := actual)
          ((dyadicEdges depth left right)[index.val]'index.isLt)
          entry.comparison.leftObservation.value entry.comparison.rightObservation.value
          false targetAllowance).integralSample := by
    let edge := (dyadicEdges depth left right)[index.val]'index.isLt
    let first := entry.comparison.leftObservation.value
    let last := entry.comparison.rightObservation.value
    let increment := Stereographic.Tangent.increment (edge.right.parameter - edge.left.parameter)
    let rate := velocity base edge.left.parameter
    have sourceEq := @Reading.Jet.source_value genus curve collar cap
      (actual.val.point edge.left.parameter) (point_inside base unitBound collarBound actual edge.left.parameter)
      differential target (stored.get index) origin jet remainder polynomial retained primitive
      expandedTarget accuracy entry
    have scalar : increment * (rate * (first - last)) =
        increment * (rate * ((stored.get index).request.reading.value - last)) :=
      congrArg (fun value : Canonical => increment * (rate * (value - last))) sourceEq
    have firstSample := readingCell.integralSample differential base unitBound collarBound actual target edge
      (stored.get index) none sourceAllowance
    have lastSample := cell_sample (base := base) (actual := actual) edge first last false targetAllowance
    have differenceSample := cell_sample (base := base) (actual := actual) edge first last true errorAllowance
    change _ = (original index entry).integralSample - _
    calc
      _ = increment * (rate * (first - last)) := differenceSample
      _ = increment * (rate * ((stored.get index).request.reading.value - last)) := scalar
      _ = increment * (rate * (stored.get index).request.reading.value) - increment * (rate * last) := by ring1
      _ = _ := congrArg₂ (fun first last : Canonical => first - last) firstSample.symm lastSample.symm
  have result := mapped_sample_linear 1 (-1) (dyadicEdges depth left right) expanded original
    (fun index entry => cell (base := base) (actual := actual)
      ((dyadicEdges depth left right)[index.val]'index.isLt)
      entry.comparison.leftObservation.value entry.comparison.rightObservation.value false targetAllowance)
    (fun index entry => cell (base := base) (actual := actual)
      ((dyadicEdges depth left right)[index.val]'index.isLt)
      entry.comparison.leftObservation.value entry.comparison.rightObservation.value true errorAllowance)
    (fun index entry => (same index entry).trans (by ring1))
  change _ = (PathModel.mk (stored.model sourceAllowance).cells).integralSample - _
  rewrite [sourceCells]
  have normalize (first last : Canonical) : 1 * first + (-1) * last = first - last := by ring1
  exact result.trans (normalize _ _)

/-- The ordered principal or error operand cells from the same actual saved expansion readings.

Both branches select the retained operand reading at each original bounded
occurrence. They use the same supplied curve, tangent and displacement;
neither branch rebuilds a channel, witness, request or root preparation.
-/
def partsModel (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (error : Bool) (allowance : { value : Fraction.Rational // 0 ≤ value }) : PathModel :=
  ⟨DependentProduct.mapToList (dyadicEdges depth left right) expanded fun index entry =>
    cell (base := base) (actual := actual) ((dyadicEdges depth left right)[index.val]'index.isLt) 0
      (cond error entry.parts.val.2.value entry.parts.val.1.value) false allowance⟩

/-- The retained operand model keeps the exact original bounded dyadic occurrence count. -/
theorem partsModel_count
    (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (error : Bool) (allowance : { value : Fraction.Rational // 0 ≤ value }) :
    (expanded.partsModel error allowance).cells.length = 2 ^ depth := by
  unfold partsModel
  exact (DependentProduct.length_mapToList (dyadicEdges depth left right) expanded _).trans
    (dyadicEdges_length depth left right)

/-- The actual expansion path sample is the sum of its same-state retained principal and error path samples.

Every coefficient split is the literal sum-witness readback of its actual
original request. The same bounded dependent entries supply both original
operands, and the original tangent/displacement fold preserves that sum.
No independently requested coefficient or successful integral comparison
is substituted for either retained operand.
-/
theorem model_parts_split
    (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (expandedAllowance principalAllowance errorAllowance : { value : Fraction.Rational // 0 ≤ value }) :
    (expanded.model false expandedAllowance).integralSample =
      (expanded.partsModel false principalAllowance).integralSample +
        (expanded.partsModel true errorAllowance).integralSample := by
  let first := fun (index : Fin (dyadicEdges depth left right).length)
      (entry : Reading.Jet (stored.get index) origin jet remainder polynomial
        retained primitive expandedTarget accuracy) =>
    cell (base := base) (actual := actual) ((dyadicEdges depth left right)[index.val]'index.isLt)
      0 entry.parts.val.1.value false principalAllowance
  let last := fun (index : Fin (dyadicEdges depth left right).length)
      (entry : Reading.Jet (stored.get index) origin jet remainder polynomial
        retained primitive expandedTarget accuracy) =>
    cell (base := base) (actual := actual) ((dyadicEdges depth left right)[index.val]'index.isLt)
      0 entry.parts.val.2.value false errorAllowance
  let combined := fun (index : Fin (dyadicEdges depth left right).length)
      (entry : Reading.Jet (stored.get index) origin jet remainder polynomial
        retained primitive expandedTarget accuracy) =>
    cell (base := base) (actual := actual) ((dyadicEdges depth left right)[index.val]'index.isLt)
      entry.comparison.leftObservation.value entry.comparison.rightObservation.value false expandedAllowance
  have same (index) (entry) : (combined index entry).integralSample =
      (first index entry).integralSample + (last index entry).integralSample := by
    let edge := (dyadicEdges depth left right)[index.val]'index.isLt
    let increment := Stereographic.Tangent.increment (edge.right.parameter - edge.left.parameter)
    let rate := velocity base edge.left.parameter
    have valueEq := entry.target_value.trans entry.value_split
    calc
      _ = increment * (rate * entry.comparison.rightObservation.value) :=
        cell_sample (base := base) (actual := actual) edge _ _ false expandedAllowance
      _ = increment * (rate * (entry.parts.val.1.value + entry.parts.val.2.value)) :=
        congrArg (fun value : Canonical => increment * (rate * value)) valueEq
      _ = increment * (rate * entry.parts.val.1.value) +
          increment * (rate * entry.parts.val.2.value) := by ring1
      _ = _ := congrArg₂ (fun first last : Canonical => first + last)
        (cell_sample (base := base) (actual := actual) edge 0 _ false principalAllowance).symm
        (cell_sample (base := base) (actual := actual) edge 0 _ false errorAllowance).symm
  have result := mapped_sample_linear 1 1 (dyadicEdges depth left right) expanded first last combined
    (fun index entry => (same index entry).trans (by ring1))
  have normalize (first last : Canonical) : 1 * first + 1 * last = first + last := by ring1
  exact result.trans (normalize _ _)

/-- Changing only the supplied local budgets preserves the exact same retained operand sample. -/
theorem partsModel_sample_allowance
    (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (error : Bool) (firstAllowance lastAllowance : { value : Fraction.Rational // 0 ≤ value }) :
    (expanded.partsModel error firstAllowance).integralSample =
      (expanded.partsModel error lastAllowance).integralSample := by
  let first := fun (index : Fin (dyadicEdges depth left right).length)
      (entry : Reading.Jet (stored.get index) origin jet remainder polynomial
        retained primitive expandedTarget accuracy) =>
    cell (base := base) (actual := actual) ((dyadicEdges depth left right)[index.val]'index.isLt)
      0 (cond error entry.parts.val.2.value entry.parts.val.1.value) false lastAllowance
  let combined := fun (index : Fin (dyadicEdges depth left right).length)
      (entry : Reading.Jet (stored.get index) origin jet remainder polynomial
        retained primitive expandedTarget accuracy) =>
    cell (base := base) (actual := actual) ((dyadicEdges depth left right)[index.val]'index.isLt)
      0 (cond error entry.parts.val.2.value entry.parts.val.1.value) false firstAllowance
  have same (index) (entry) : (combined index entry).integralSample =
      1 * (first index entry).integralSample + 0 * (first index entry).integralSample := by
    let edge := (dyadicEdges depth left right)[index.val]'index.isLt
    let value := cond error entry.parts.val.2.value entry.parts.val.1.value
    have scalar := (cell_sample (base := base) (actual := actual) edge 0 value false firstAllowance).trans
      (cell_sample (base := base) (actual := actual) edge 0 value false lastAllowance).symm
    exact scalar.trans (by ring1)
  have result := mapped_sample_linear 1 0 (dyadicEdges depth left right) expanded first first combined same
  have normalize (value : Canonical) : 1 * value + 0 * value = value := by ring1
  exact result.trans (normalize _)

/-- Constant polynomial readback of the same actual scalar cell. -/
private theorem cell_polynomial (edge : ParameterEdge) (first last : Canonical)
    (difference : Bool) (allowance : { value : Fraction.Rational // 0 ≤ value }) :
    (cell (base := base) (actual := actual) edge first last difference allowance).polynomial =
      Basic.constant
        (velocity base edge.left.parameter * (if difference then first - last else last)) := rfl

/-- The actual scalar cell retains its original endpoint displacement. -/
private theorem cell_displacement (edge : ParameterEdge) (first last : Canonical)
    (difference : Bool) (allowance : { value : Fraction.Rational // 0 ≤ value }) :
    (cell (base := base) (actual := actual) edge first last difference allowance).displacement =
      Stereographic.Tangent.increment (edge.right.parameter - edge.left.parameter) := by
  unfold cell
  rewrite [CellModel.weakenAllowance_displacement]
  exact coefficientCell_displacement base actual _ edge.left.parameter (edge.right.parameter - edge.left.parameter)

/-- The same original bounded dyadic occurrence pays its actual constant cell displacement. -/
private theorem cell_displacement_le (index : Fin (dyadicEdges depth left right).length)
    (first last : Canonical) (difference : Bool) (allowance : { value : Fraction.Rational // 0 ≤ value }) :
    Norm.Basic.normSq
      (cell (base := base) (actual := actual) ((dyadicEdges depth left right)[index.val]'index.isLt)
        first last difference allowance).displacement ≤
          Geometric.Basic.quarterRadius 1 depth := by
  rewrite [cell_displacement]
  change (((dyadicEdges depth left right)[index.val]'index.isLt).right.parameter -
    ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter) ^ 2 + 0 ^ 2 ≤ _
  rewrite [pow_two (0 : Fraction.Rational), Fraction.Field.mul_zero_direct, _root_.add_zero]
  exact dyadicEdges_parameterSquare_le depth left right _ (List.getElem_mem index.isLt)

/-- A same-curve constant cell's actual tangent scales its retained coefficient quadrance bound. -/
private theorem cell_value_bound (edge : ParameterEdge) (value : Canonical) (upper : Fraction.Rational)
    (bounded : Norm.Basic.normSq value ≤ upper) :
    Canonical.normSq (velocity base edge.left.parameter * value) ≤ (4 * Norm.Basic.normSq base) * upper := by
  rewrite [← Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_mul]
  exact (Arithmetic.mul_le_mul_of_nonneg_right_direct
    (velocity_normSq_le base edge.left.parameter) (Norm.Basic.normSq_nonneg value)).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct bounded
        (Arithmetic.mul_nonneg_direct (by decide) (Norm.Basic.normSq_nonneg base)))

/-- Actual original constant-cell certificates along the supplied dependent-product spine. -/
private def mapped_zero {Item : Type u} :
    (items : List Item) → {family : Fin items.length → Type v} → (entries : DependentProduct items family) →
    (cells : (index : Fin items.length) → family index → CellModel) →
    (values : (index : Fin items.length) → family index → Canonical) →
    (∀ index entry, (cells index entry).polynomial = Basic.constant (values index entry)) →
    (∀ index entry, Canonical.normSq (values index entry) ≤ (cells index entry).localAllowance) →
      PathModel.ConstantComparison 0 (DependentProduct.mapToList items entries cells)
        (DependentProduct.mapToList items entries values)
  | [], _, _, _, _, _, _ => .nil
  | _ :: remaining, _, entries, cells, values, polynomials, bounds =>
      .cons (values 0 entries.1) (values 0 entries.1) (polynomials 0 entries.1)
        (Gaussian.Basic.sub_zero _) (bounds 0 entries.1)
        (mapped_zero remaining entries.2 (fun index entry => cells index.succ entry)
          (fun index entry => values index.succ entry)
          (fun index entry => polynomials index.succ entry) (fun index entry => bounds index.succ entry))

/-- A zero-reference comparison bounds the actual mapped constant path sample by its retained aggregate allowance. -/
private theorem mapped_sample_bound {Item : Type u} (items : List Item)
    {family : Fin items.length → Type v} (entries : DependentProduct items family)
    (cells : (index : Fin items.length) → family index → CellModel)
    (values : (index : Fin items.length) → family index → Canonical)
    (polynomials : ∀ index entry,
      (cells index entry).polynomial = Basic.constant (values index entry))
    (bounds : ∀ index entry, Canonical.normSq (values index entry) ≤ (cells index entry).localAllowance) :
    Norm.Basic.normSq (PathModel.mk (DependentProduct.mapToList items entries cells)).integralSample ≤
      (PathModel.mk (DependentProduct.mapToList items entries cells)).aggregateAllowance := by
  let comparison := mapped_zero items entries cells values polynomials bounds
  have readback := comparison.integralSample_eq_reference_add_error
  rewrite [Gaussian.Basic.mul_zero, Gaussian.Basic.zero_add] at readback
  rewrite [readback, Norm.Basic.normSq_eq_canonical]
  exact PathModel.weightedErrorSum_le _ _ comparison.errorsValid

/-- The original tangent bound pays the actual two observation targets and operational comparison accuracy. -/
def errorAllowance (sourcePositive : 0 < target) (targetPositive : 0 < expandedTarget)
    (accuracyPositive : 0 < accuracy) : { value : Fraction.Rational // 0 ≤ value } :=
  ⟨(4 * Norm.Basic.normSq base) * (16 * (target + expandedTarget) + 4 * accuracy),
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide) (Norm.Basic.normSq_nonneg base))
      (add_nonneg
        (Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg sourcePositive.le targetPositive.le))
        (Arithmetic.mul_nonneg_direct (by decide) accuracyPositive.le))⟩

/-- The same bounded dyadic cell table pays its uniform displacement and local-budget bounds. -/
private theorem mapped_allowance_le {family : Fin (dyadicEdges depth left right).length → Type v}
    (entries : DependentProduct (dyadicEdges depth left right) family)
    (cells : (index : Fin (dyadicEdges depth left right).length) → family index → CellModel)
    (upper : Fraction.Rational)
    (paid : ∀ index entry,
      Norm.Basic.normSq (cells index entry).displacement ≤
        Geometric.Basic.quarterRadius 1 depth ∧
        (cells index entry).localAllowance ≤ upper) :
    (PathModel.mk (DependentProduct.mapToList (dyadicEdges depth left right) entries cells)).aggregateAllowance ≤
      upper := by
  let model := PathModel.mk (DependentProduct.mapToList (dyadicEdges depth left right) entries cells)
  have bounds : ∀ item ∈ model.cells,
      Norm.Basic.normSq item.displacement ≤ Geometric.Basic.quarterRadius 1 depth ∧
        item.localAllowance ≤ upper := by
    apply DependentProduct.mapToList_all
    exact paid
  have count : model.cells.length = 2 ^ depth :=
    (DependentProduct.length_mapToList (dyadicEdges depth left right) entries cells).trans
      (dyadicEdges_length depth left right)
  exact (PathModel.uniform_aggregateAllowance_le model depth 1 upper (by decide) count bounds).trans_eq
    (Fraction.Field.one_mul _)

/-- The actual mapped dyadic path allowance is bounded by its supplied uniform local budget.

The same retained edge count and parameter displacement bounds cancel the
mesh factors. This applies to both expanded observations and their actual
observed differences, independently of either stored coefficient value.
-/
theorem model_allowance_le
    (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (difference : Bool) (allowance : { value : Fraction.Rational // 0 ≤ value }) :
    (expanded.model difference allowance).aggregateAllowance ≤ allowance.val := by
  unfold model
  apply mapped_allowance_le expanded _ allowance.val
  intro index entry
  constructor
  · exact cell_displacement_le (base := base) (actual := actual) index _ _ _ _
  · exact Fraction.Order.Basic.le_refl _

/-- The actual retained operand path pays the same original dyadic displacement and supplied budget. -/
theorem partsModel_allowance_le
    (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (error : Bool) (allowance : { value : Fraction.Rational // 0 ≤ value }) :
    (expanded.partsModel error allowance).aggregateAllowance ≤ allowance.val := by
  unfold partsModel
  apply mapped_allowance_le expanded _ allowance.val
  intro index entry
  constructor
  · exact cell_displacement_le (base := base) (actual := actual) index _ _ _ _
  · exact Fraction.Order.Basic.le_refl _

namespace ErrorBounds

/-- The actual error path sample shrinks with its same circle's velocity despite only bounded coefficient error.

The original root setup and polynomial cache derive every operand reading
bound at the actual dyadic occurrence. The original circle quadrance pays
the coordinate square, its actual tangent supplies the radius factor, and
the original finite weighted-cell comparison bounds the full path sample.
No vanishing of the maximal-even B*E coefficient is assumed.
-/
theorem model_bound (bounds : ErrorBounds origin jet remainder polynomial)
    (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (positive : 0 < expandedTarget)
    (near : Norm.Basic.normSq base ≤ bounds.1.1.val ^ 2)
    (allowance : { value : Fraction.Rational // 0 ≤ value }) :
    Norm.Basic.normSq (expanded.partsModel true allowance).integralSample ≤
      (4 * Norm.Basic.normSq base) * bounds.readingUpper expandedTarget := by
  let paidAllowance : { value : Fraction.Rational // 0 ≤ value } :=
    ⟨(4 * Norm.Basic.normSq base) * bounds.readingUpper expandedTarget,
      Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide) (Norm.Basic.normSq_nonneg base))
        (bounds.readingUpper_nonnegative positive)⟩
  let cells := fun (index : Fin (dyadicEdges depth left right).length)
      (entry : Reading.Jet (stored.get index) origin jet remainder polynomial
        retained primitive expandedTarget accuracy) =>
    cell (base := base) (actual := actual) ((dyadicEdges depth left right)[index.val]'index.isLt)
      0 entry.parts.val.2.value false paidAllowance
  let values := fun (index : Fin (dyadicEdges depth left right).length)
      (entry : Reading.Jet (stored.get index) origin jet remainder polynomial
        retained primitive expandedTarget accuracy) =>
    velocity base ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter * entry.parts.val.2.value
  have polynomials (index) (entry) :
      (cells index entry).polynomial = Basic.constant (values index entry) := rfl
  have coefficientBounds (index) (entry) : Canonical.normSq (values index entry) ≤
      (cells index entry).localAllowance := by
    let time := ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter
    have quadrance : Norm.Basic.normSq (actual.val.point time) = Norm.Basic.normSq base := by
      rewrite [actual.property]
      exact point_normSq base time
    have inside := Primitives.point_in_square curve (actual.val.point time) (quadrance.trans_le unitBound)
      bounds.1.1.val bounds.1.1.property.le (quadrance.trans_le near)
    exact cell_value_bound (base := base) _ _ _ (bounds.reading_bound entry positive inside)
  have sampleBound := mapped_sample_bound (dyadicEdges depth left right) expanded cells values
    polynomials coefficientBounds
  have aggregate := expanded.partsModel_allowance_le true paidAllowance
  have same := expanded.partsModel_sample_allowance true allowance paidAllowance
  exact (congrArg Norm.Basic.normSq same).trans_le (sampleBound.trans aggregate)

/-- The same cached error-reading ceiling is monotone in its separately paid observation target. -/
theorem readingUpper_mono (bounds : ErrorBounds origin jet remainder polynomial)
    {first last : Fraction.Rational} (small : first ≤ last) :
    bounds.readingUpper first ≤ bounds.readingUpper last := by
  unfold readingUpper
  have firstTerm : 64 * first ≤ 64 * last :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct small
      (Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 64) (by decide))
  have inner := Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl bounds.1.2.1.val) small
  have product := Arithmetic.mul_le_mul_of_nonneg_left_direct inner bounds.clearedUpper_nonnegative
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct product
    (by decide : (0 : Fraction.Rational) ≤ 4)
  have added := Arithmetic.add_le_add_direct scaled small
  exact Arithmetic.add_le_add_direct firstTerm
    (Arithmetic.mul_le_mul_of_nonneg_left_direct added (by decide : (0 : Fraction.Rational) ≤ 4))

/-- The finite squared-radius payment uses the original root square and actual error coefficient ceiling. -/
def baseBudget (bounds : ErrorBounds origin jet remainder polynomial) (tolerance : Fraction.Rational) :
    Fraction.Rational :=
  Common.commonTarget (bounds.1.1.val ^ 2) (tolerance / (4 * (1 + bounds.readingUpper 1)))

/-- The actual finite radius-payment denominator is positive without a nonzero error assumption. -/
private theorem baseBudget_denominator_pos (bounds : ErrorBounds origin jet remainder polynomial) :
    0 < 4 * (1 + bounds.readingUpper 1) :=
  Arithmetic.mul_pos_direct (by decide)
    (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide)
      (bounds.readingUpper_nonnegative (by decide : (0 : Fraction.Rational) < 1)))

/-- Both actual requests combined in the radius payment are positive. -/
private theorem baseBudget_inputs_positive (bounds : ErrorBounds origin jet remainder polynomial)
    {tolerance : Fraction.Rational} (positive : 0 < tolerance) :
    0 < bounds.1.1.val ^ 2 ∧ 0 < tolerance / (4 * (1 + bounds.readingUpper 1)) := by
  constructor
  · rewrite [pow_two]
    exact Arithmetic.mul_pos_direct bounds.1.1.property bounds.1.1.property
  · exact Fraction.Order.Field.div_pos_direct positive bounds.baseBudget_denominator_pos

/-- A positive error tolerance gives a computed positive squared-radius budget for the actual circle base. -/
theorem baseBudget_positive (bounds : ErrorBounds origin jet remainder polynomial)
    {tolerance : Fraction.Rational} (positive : 0 < tolerance) : 0 < bounds.baseBudget tolerance :=
  Common.commonTarget_pos (bounds.baseBudget_inputs_positive positive).1 (bounds.baseBudget_inputs_positive positive).2

/-- The original finite base budget pays both its retained root square and velocity-weighted coefficient ceiling.

The actual positive denominator and common-target inequalities give both
bounds for every supplied squared radius below the computed request.
The coefficient ceiling need only be bounded; it need not vanish.
-/
theorem baseBudget_paid (bounds : ErrorBounds origin jet remainder polynomial)
    {quadrance tolerance : Fraction.Rational} (positive : 0 < tolerance)
    (small : quadrance ≤ bounds.baseBudget tolerance) :
    quadrance ≤ bounds.1.1.val ^ 2 ∧ (4 * quadrance) * (1 + bounds.readingUpper 1) < tolerance := by
  have inputs := bounds.baseBudget_inputs_positive positive
  have rootPaid : bounds.baseBudget tolerance < bounds.1.1.val ^ 2 :=
    Common.commonTarget_lt_left inputs.1 inputs.2
  have targetPaid : bounds.baseBudget tolerance < tolerance / (4 * (1 + bounds.readingUpper 1)) :=
    Common.commonTarget_lt_right inputs.1 inputs.2
  have paid := (Fraction.Order.Field.lt_div_iff_pos bounds.baseBudget_denominator_pos).mp
    (small.trans_lt targetPaid)
  have grouped : (4 * quadrance) * (1 + bounds.readingUpper 1) =
      quadrance * (4 * (1 + bounds.readingUpper 1)) := by ring1
  exact ⟨small.trans rootPaid.le, grouped.trans_lt paid⟩

/-- The actual finite error path pays any positive tolerance through its computed squared-radius request.

The original sum observation target is paid independently and bounded by
one. The computed base request itself supplies the root square and the
strict velocity-weighted error payment; no coefficient-error vanishing or
unproved geometric/integral comparison is required.
-/
theorem model_small (bounds : ErrorBounds origin jet remainder polynomial)
    (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (positive : 0 < expandedTarget) (atMostOne : expandedTarget ≤ 1)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (smallBase : Norm.Basic.normSq base ≤ bounds.baseBudget tolerance)
    (allowance : { value : Fraction.Rational // 0 ≤ value }) :
    Norm.Basic.normSq (expanded.partsModel true allowance).integralSample < tolerance := by
  have paid := bounds.baseBudget_paid tolerancePositive smallBase
  have weighted := bounds.model_bound expanded positive paid.1 allowance
  have nonnegative : 0 ≤ 4 * Norm.Basic.normSq base :=
    Arithmetic.mul_nonneg_direct (by decide) (Norm.Basic.normSq_nonneg base)
  have unitBound := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (bounds.readingUpper_mono atMostOne) nonnegative
  have plusOne := Arithmetic.add_le_add_direct (by decide : (0 : Fraction.Rational) ≤ 1)
    (Fraction.Order.Basic.le_refl (bounds.readingUpper 1))
  rewrite [Fraction.Field.zero_add] at plusOne
  have ceiling := Arithmetic.mul_le_mul_of_nonneg_left_direct plusOne nonnegative
  exact ((weighted.trans unitBound).trans ceiling).trans_lt paid.2

end ErrorBounds

/-- The original finite expansion comparison bounds the actual total-form versus expanded stage sample.

The actual coefficient requests supply every local error certificate. The
original circle tangent bounds its exact integrand error, and the same
original dyadic cell count cancels the mesh displacement weights. The
result retains both observation targets and operational accuracy explicitly.
-/
theorem model_distance_le
    (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (sourcePositive : 0 < target) (targetPositive : 0 < expandedTarget) (accuracyPositive : 0 < accuracy)
    (sourceAllowance : Option { value : Fraction.Rational // 0 ≤ value })
    (targetAllowance : { value : Fraction.Rational // 0 ≤ value }) :
    Norm.Basic.normSq ((stored.model sourceAllowance).integralSample -
      (expanded.model false targetAllowance).integralSample) ≤
        (4 * Norm.Basic.normSq base) * (16 * (target + expandedTarget) + 4 * accuracy) := by
  let allowance := errorAllowance (base := base) sourcePositive targetPositive accuracyPositive
  let cells := fun (index : Fin (dyadicEdges depth left right).length)
      (entry : Reading.Jet (stored.get index) origin jet remainder polynomial
        retained primitive expandedTarget accuracy) =>
    cell (base := base) (actual := actual) ((dyadicEdges depth left right)[index.val]'index.isLt)
      entry.comparison.leftObservation.value entry.comparison.rightObservation.value true allowance
  let values := fun (index : Fin (dyadicEdges depth left right).length)
      (entry : Reading.Jet (stored.get index) origin jet remainder polynomial
        retained primitive expandedTarget accuracy) =>
    velocity base ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter *
      (entry.comparison.leftObservation.value - entry.comparison.rightObservation.value)
  have polynomials (index) (entry) :
      (cells index entry).polynomial = Basic.constant (values index entry) := rfl
  have coefficientBounds (index) (entry) : Canonical.normSq (values index entry) ≤
      (cells index entry).localAllowance :=
    cell_value_bound (base := base) _ _ _ entry.observations_distance_le
  have sampleBound := mapped_sample_bound (dyadicEdges depth left right) expanded cells values
    polynomials coefficientBounds
  have aggregate := expanded.model_allowance_le true allowance
  have difference := expanded.model_difference sourceAllowance targetAllowance allowance
  exact (congrArg Norm.Basic.normSq difference.symm).trans_le (sampleBound.trans aggregate)

/-- The actual stage comparison has geometric decay when its three independent targets pay the same quarter radius. -/
theorem model_distance_geometric
    (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (sourceTarget : target = Geometric.Basic.quarterRadius 1 depth)
    (expansionTarget : expandedTarget = Geometric.Basic.quarterRadius 1 depth)
    (comparisonTarget : accuracy = Geometric.Basic.quarterRadius 1 depth)
    (sourceAllowance : Option { value : Fraction.Rational // 0 ≤ value })
    (targetAllowance : { value : Fraction.Rational // 0 ≤ value }) :
    Norm.Basic.normSq ((stored.model sourceAllowance).integralSample -
      (expanded.model false targetAllowance).integralSample) ≤
        Geometric.Basic.quarterRadius (144 * Norm.Basic.normSq base) depth := by
  have precisionPositive := Geometric.Basic.quarterRadius_pos
    (by decide : (0 : Fraction.Rational) < 1) depth
  have paid := expanded.model_distance_le (sourceTarget.symm ▸ precisionPositive)
    (expansionTarget.symm ▸ precisionPositive) (comparisonTarget.symm ▸ precisionPositive)
    sourceAllowance targetAllowance
  have scalar : (4 * Norm.Basic.normSq base) * (16 * (target + expandedTarget) + 4 * accuracy) =
      Geometric.Basic.quarterRadius (144 * Norm.Basic.normSq base) depth := by
    rewrite [sourceTarget, expansionTarget, comparisonTarget,
      Geometric.Basic.quarterRadius_eq_mul_pow,
      Geometric.Basic.quarterRadius_eq_mul_pow]
    ring1
  exact paid.trans_eq scalar

namespace ErrorBounds

/-- The actual original whole-form sample is quantitatively close to the saved principal-operand path sample.

The same dyadic observations give the exact total/expanded and
principal/error splits. Their independently paid observation comparison
and actual weighted error bound supply the two terms of this estimate.
The original origin quotient remains inside the principal operand; this
claim does not replace that quotient by a scalar coefficient integral.
-/
theorem model_principal_distance_le (bounds : ErrorBounds origin jet remainder polynomial)
    (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (sourcePositive : 0 < target) (targetPositive : 0 < expandedTarget) (accuracyPositive : 0 < accuracy)
    (near : Norm.Basic.normSq base ≤ bounds.1.1.val ^ 2)
    (sourceAllowance : Option { value : Fraction.Rational // 0 ≤ value })
    (expandedAllowance principalAllowance errorAllowance : { value : Fraction.Rational // 0 ≤ value }) :
    Norm.Basic.normSq ((stored.model sourceAllowance).integralSample -
      (expanded.partsModel false principalAllowance).integralSample) ≤
      2 * ((4 * Norm.Basic.normSq base) * (16 * (target + expandedTarget) + 4 * accuracy) +
        (4 * Norm.Basic.normSq base) * bounds.readingUpper expandedTarget) := by
  have split := expanded.model_parts_split expandedAllowance principalAllowance errorAllowance
  have decomposition : (stored.model sourceAllowance).integralSample -
      (expanded.partsModel false principalAllowance).integralSample =
      ((stored.model sourceAllowance).integralSample - (expanded.model false expandedAllowance).integralSample) +
        (expanded.partsModel true errorAllowance).integralSample := by
    rewrite [split]
    ring1
  have observed := expanded.model_distance_le sourcePositive targetPositive accuracyPositive
    sourceAllowance expandedAllowance
  have weighted := bounds.model_bound expanded targetPositive near errorAllowance
  rewrite [decomposition]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct observed weighted) (by decide : (0 : Fraction.Rational) ≤ 2))

end ErrorBounds

/-- The original numerator quotient ceiling times the same retained finite jet ceiling bounds the principal scalar. -/
def principalUpper {data : Polynomials differential} (cached : data.Bounds base)
    (jetBounds : jet.Bounds collar.box) : Fraction.Rational :=
  (cached.1.val.value / Polynomials.lower (curve := curve) base) * jetBounds.val.value

/-- An actual rotated quarter uses the same original retained principal scalar ceiling. -/
theorem principalUpper_onQuarter {data : Polynomials differential} (cached : data.Bounds base)
    (jetBounds : jet.Bounds collar.box) (quarter : Quarter.UnitCircuitQuarter) :
    principalUpper (cached.onQuarter quarter) jetBounds = principalUpper cached jetBounds := by
  unfold principalUpper Polynomials.lower
  rewrite [cached.onQuarter_numerator_value, Integral.quarterBase_normSq]
  rfl

/-- A nonzero original circle base makes the actual principal scalar ceiling nonnegative. -/
theorem principalUpper_nonnegative {data : Polynomials differential} (cached : data.Bounds base)
    (jetBounds : jet.Bounds collar.box) (nonzero : base ≠ 0) : 0 ≤ principalUpper cached jetBounds := by
  exact Arithmetic.mul_nonneg_direct (cached.numerator_norm_bound_nonnegative nonzero)
    jetBounds.value_nonnegative

/-- Every actual saved principal scalar obeys the two supplied original cached polynomial ceilings. -/
theorem principal_normSq_le {data : Polynomials differential} (cached : data.Bounds base)
    (jetBounds : jet.Bounds collar.box) (nonzero : base ≠ 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus)
    (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (index : Fin (dyadicEdges depth left right).length) :
    Norm.Basic.normSq (Coefficient.principalValue
      (parameter := actual.val.point ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter)
      retained primitive) ≤ principalUpper cached jetBounds := by
  let time := ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter
  let entry := DependentProduct.get (dyadicEdges depth left right) expanded index
  have value := Coefficient.principalValue_eq (stored.get index).2.1
    (point_nonzero base nonzero actual time) bound polynomial retained primitive entry.1
  rewrite [value, Norm.Basic.normSq_mul, entry.1.property]
  exact Arithmetic.mul_le_mul_direct
    (cached.numerator_norm_le nonzero bound actual time (stored.get index).2.1)
    (jetBounds.value_le (point_inside base unitBound collarBound actual time))
    (Norm.Basic.normSq_nonneg _) (cached.numerator_norm_bound_nonnegative nonzero)

/-- The actual common reciprocal request pays the unit bound and every magnitude-weighted product target. -/
def principalTarget {data : Polynomials differential} (cached : data.Bounds base)
    (jetBounds : jet.Bounds collar.box) (productTarget : Fraction.Rational) : Fraction.Rational :=
  Common.commonTarget 1 (productTarget / (4 * (1 + principalUpper cached jetBounds)))

/-- The actual reciprocal-payment denominator is positive for the same original numerator and jet bounds. -/
private theorem principal_denominator_positive {data : Polynomials differential} (cached : data.Bounds base)
    (jetBounds : jet.Bounds collar.box) (nonzero : base ≠ 0) :
    0 < 4 * (1 + principalUpper cached jetBounds) :=
  Arithmetic.mul_pos_direct (by decide)
    (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide)
      (principalUpper_nonnegative cached jetBounds nonzero))

/-- A positive requested product target yields the computed positive common reciprocal request. -/
theorem principalTarget_positive {data : Polynomials differential} (cached : data.Bounds base)
    (jetBounds : jet.Bounds collar.box) (nonzero : base ≠ 0)
    {productTarget : Fraction.Rational} (positive : 0 < productTarget) :
    0 < principalTarget cached jetBounds productTarget :=
  Common.commonTarget_pos (by decide)
    (Fraction.Order.Field.div_pos_direct positive (principal_denominator_positive cached jetBounds nonzero))

/-- The original principal target pays no more than its same displayed positive product target.

The original nonnegative numerator and jet ceilings make the magnitude
payment denominator at least one. The computed common target therefore
pays the original product budget without an additional observation.
-/
theorem principalTarget_le {data : Polynomials differential} (cached : data.Bounds base)
    (jetBounds : jet.Bounds collar.box) (nonzero : base ≠ 0)
    {productTarget : Fraction.Rational} (positive : 0 < productTarget) :
    principalTarget cached jetBounds productTarget ≤ productTarget := by
  let denominator := 4 * (1 + principalUpper cached jetBounds)
  have denominatorPositive : 0 < denominator := principal_denominator_positive cached jetBounds nonzero
  have unit : (1 : Fraction.Rational) ≤ 1 + principalUpper cached jetBounds :=
    (show (1 : Fraction.Rational) + 0 = 1 by decide +kernel).symm.trans_le
      (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
        (principalUpper_nonnegative cached jetBounds nonzero))
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct unit
    (by decide : (0 : Fraction.Rational) ≤ 4)
  have denominatorLower : (1 : Fraction.Rational) ≤ denominator :=
    (by decide : (1 : Fraction.Rational) ≤ 4).trans ((Fraction.Field.mul_one_direct 4).symm.trans_le scaled)
  have quotientBound : productTarget / denominator ≤ productTarget :=
    (Fraction.Order.Field.div_le_iff_pos denominatorPositive).mpr
      ((Fraction.Field.mul_one_direct productTarget).symm.trans_le
        (Arithmetic.mul_le_mul_of_nonneg_left_direct denominatorLower positive.le))
  have below := Common.commonTarget_lt_right (by decide : (0 : Fraction.Rational) < 1)
    (Fraction.Order.Field.div_pos_direct positive denominatorPositive)
  exact below.le.trans quotientBound

/-- An actual rotated quarter retains the same complete computed common reciprocal target. -/
theorem principalTarget_onQuarter {data : Polynomials differential} (cached : data.Bounds base)
    (jetBounds : jet.Bounds collar.box) (quarter : Quarter.UnitCircuitQuarter) (target : Fraction.Rational) :
    principalTarget (cached.onQuarter quarter) jetBounds target = principalTarget cached jetBounds target := by
  unfold principalTarget
  rewrite [principalUpper_onQuarter]
  rfl

/-- The actual supplied reciprocal request pays every original scalar-product allowance in the same bank. -/
theorem principal_product_paid {data : Polynomials differential} (cached : data.Bounds base)
    (jetBounds : jet.Bounds collar.box) (nonzero : base ≠ 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus)
    (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    {productTarget : Fraction.Rational} (positive : 0 < productTarget)
    (reciprocal : Request (div (Coherence.exact 1) origin.certificate.value origin.certificate.apart)
      (principalTarget cached jetBounds productTarget))
    (index : Fin (dyadicEdges depth left right).length) :
    let coefficient := Coefficient.principalValue
      (parameter := actual.val.point ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter)
      retained primitive
    ((Coherence.exact coefficient).mul
      (div (Coherence.exact 1) origin.certificate.value origin.certificate.apart)).coherent.allowance
        (reciprocal.reading.exact_mul coefficient).state < productTarget := by
  let denominator := 4 * (1 + principalUpper cached jetBounds)
  have denominatorPositive : 0 < denominator := principal_denominator_positive cached jetBounds nonzero
  have quotientPositive : 0 < productTarget / denominator :=
    Fraction.Order.Field.div_pos_direct positive denominatorPositive
  have unit := Common.commonTarget_lt_left (by decide : (0 : Fraction.Rational) < 1) quotientPositive
  have target := Common.commonTarget_lt_right (by decide : (0 : Fraction.Rational) < 1) quotientPositive
  have payment := (Fraction.Order.Field.lt_div_iff_pos denominatorPositive).mp target
  exact reciprocal.reading.exact_mul_paid _ (expanded.principal_normSq_le cached jetBounds nonzero bound index)
    reciprocal.allowance_lt unit.le payment

/-- The actual principal-operand path compares with one supplied reciprocal reading times the same-mesh scalar path.

The same retained reciprocal Request pays every scalar-product allowance.
The actual saved principal readings, original endpoint occurrences and
circle velocity/displacement produce the weighted finite path bound.
The reference is the original Dyadic.model, with no new programme owner
and no equality asserted between independently selected meshes.
-/
theorem principal_model_distance_le {data : Polynomials differential} (cached : data.Bounds base)
    (jetBounds : jet.Bounds collar.box) (nonzero : base ≠ 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus)
    (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (positive : 0 < expandedTarget) {productTarget comparisonTarget : Fraction.Rational}
    (productPositive : 0 < productTarget) (comparisonPositive : 0 < comparisonTarget)
    (reciprocal : Request (div (Coherence.exact 1) origin.certificate.value origin.certificate.apart)
      (principalTarget cached jetBounds productTarget))
    (allowance : { value : Fraction.Rational // 0 ≤ value }) :
    Norm.Basic.normSq ((expanded.partsModel false allowance).integralSample -
      reciprocal.reading.value * (Dyadic.model base actual
        (fun parameter => Coefficient.principalValue (parameter := parameter) retained primitive)
        depth left right).integralSample) ≤
      (4 * Norm.Basic.normSq base) * (32 * (expandedTarget + productTarget) + 4 * comparisonTarget) := by
  let ceiling := 32 * (expandedTarget + productTarget) + 4 * comparisonTarget
  have ceilingNonnegative : 0 ≤ ceiling := add_nonneg
    (Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 32) (by decide))
      (add_nonneg positive.le productPositive.le))
    (Arithmetic.mul_nonneg_direct (by decide) comparisonPositive.le)
  let payment : { value : Fraction.Rational // 0 ≤ value } :=
    ⟨(4 * Norm.Basic.normSq base) * ceiling, Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide) (Norm.Basic.normSq_nonneg base)) ceilingNonnegative⟩
  let first := fun (index : Fin (dyadicEdges depth left right).length)
      (entry : Reading.Jet (stored.get index) origin jet remainder polynomial
        retained primitive expandedTarget accuracy) =>
    cell (base := base) (actual := actual) ((dyadicEdges depth left right)[index.val]'index.isLt)
      0 entry.parts.val.1.value false allowance
  let scalar := fun parameter => Coefficient.principalValue (parameter := parameter) retained primitive
  let reference := fun (index : Fin (dyadicEdges depth left right).length)
      (_entry : Reading.Jet (stored.get index) origin jet remainder polynomial
        retained primitive expandedTarget accuracy) =>
    coefficientCell base actual scalar ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter
      (((dyadicEdges depth left right)[index.val]'index.isLt).right.parameter -
        ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter)
  let cells := fun (index : Fin (dyadicEdges depth left right).length)
      (entry : Reading.Jet (stored.get index) origin jet remainder polynomial
        retained primitive expandedTarget accuracy) =>
    cell (base := base) (actual := actual) ((dyadicEdges depth left right)[index.val]'index.isLt)
      entry.parts.val.1.value
      (scalar (actual.val.point ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter) *
        reciprocal.reading.value) true payment
  let values := fun (index : Fin (dyadicEdges depth left right).length)
      (entry : Reading.Jet (stored.get index) origin jet remainder polynomial
        retained primitive expandedTarget accuracy) =>
    velocity base ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter *
      (entry.parts.val.1.value -
        scalar (actual.val.point ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter) *
          reciprocal.reading.value)
  have polynomials (index) (entry) :
      (cells index entry).polynomial = Basic.constant (values index entry) := rfl
  have coefficients (index) (entry) : Canonical.normSq (values index entry) ≤ (cells index entry).localAllowance :=
    cell_value_bound (base := base) _ _ _ (entry.principal_distance_le reciprocal.reading
      positive productPositive comparisonPositive
      (expanded.principal_product_paid cached jetBounds nonzero bound productPositive reciprocal index))
  have bounded := mapped_sample_bound (dyadicEdges depth left right) expanded cells values polynomials coefficients
  have aggregate := mapped_allowance_le expanded cells payment.val (fun index entry =>
    ⟨cell_displacement_le index _ _ true payment, Fraction.Order.Basic.le_refl _⟩)
  have same (index) (entry) : (cells index entry).integralSample =
      1 * (first index entry).integralSample + (-reciprocal.reading.value) *
        (reference index entry).integralSample := by
    exact cell_scalar_difference ((dyadicEdges depth left right)[index.val]'index.isLt)
      entry.parts.val.1.value reciprocal.reading.value scalar allowance payment
  have difference := mapped_sample_linear 1 (-reciprocal.reading.value)
    (dyadicEdges depth left right) expanded first reference cells same
  have referenceCells := DependentProduct.mapToList_items (dyadicEdges depth left right) expanded
    (fun edge => coefficientCell base actual scalar edge.left.parameter (edge.right.parameter - edge.left.parameter))
  have referenceSample := congrArg (fun table => (PathModel.mk table).integralSample) referenceCells
  have total :
      (PathModel.mk (DependentProduct.mapToList (dyadicEdges depth left right) expanded cells)).integralSample =
      (expanded.partsModel false allowance).integralSample -
        reciprocal.reading.value * (Dyadic.model base actual scalar depth left right).integralSample := by
    change _ =
      (PathModel.mk (DependentProduct.mapToList (dyadicEdges depth left right) expanded first)).integralSample - _
    have moved := congrArg (fun sample : Canonical =>
      1 * (PathModel.mk
        (DependentProduct.mapToList (dyadicEdges depth left right) expanded first)).integralSample +
        (-reciprocal.reading.value) * sample) referenceSample
    have normalize (first last multiplier : Canonical) :
        1 * first + (-multiplier) * last = first - multiplier * last := by ring1
    exact difference.trans (moved.trans (normalize _ _ _))
  exact (congrArg Norm.Basic.normSq total.symm).trans_le (bounded.trans aggregate)

/-- The same saved principal path has geometric distance on its actual dyadic mesh.

The source, scalar-product and comparison targets are independently paid
at the same retained dyadic depth; the original velocity supplies its scale.
-/
theorem principal_model_distance_geometric {data : Polynomials differential} (cached : data.Bounds base)
    (jetBounds : jet.Bounds collar.box) (nonzero : base ≠ 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus)
    (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    (expandedTarget_eq : expandedTarget = Geometric.Basic.quarterRadius 1 depth)
    (reciprocal : Request (div (Coherence.exact 1) origin.certificate.value origin.certificate.apart)
      (principalTarget cached jetBounds (Geometric.Basic.quarterRadius 1 depth)))
    (allowance : { value : Fraction.Rational // 0 ≤ value }) :
    Norm.Basic.normSq ((expanded.partsModel false allowance).integralSample -
      reciprocal.reading.value * (Dyadic.model base actual
        (fun parameter => Coefficient.principalValue (parameter := parameter) retained primitive)
        depth left right).integralSample) ≤
      Geometric.Basic.quarterRadius (272 * Norm.Basic.normSq base) depth := by
  have positive := Geometric.Basic.quarterRadius_pos
    (by decide : (0 : Fraction.Rational) < 1) depth
  have paid := expanded.principal_model_distance_le cached jetBounds nonzero bound
    (expandedTarget_eq.symm ▸ positive) positive positive reciprocal allowance
  have grouped : (4 * Norm.Basic.normSq base) *
      (32 * (expandedTarget + Geometric.Basic.quarterRadius 1 depth) +
        4 * Geometric.Basic.quarterRadius 1 depth) =
      Geometric.Basic.quarterRadius (272 * Norm.Basic.normSq base) depth := by
    rewrite [expandedTarget_eq, Geometric.Basic.quarterRadius_eq_mul_pow,
      Geometric.Basic.quarterRadius_eq_mul_pow]
    ring1
  exact paid.trans_eq grouped

/-- The saved principal scalar equals the actual retained parameter Laurent programme coefficient in both parities.

The same original finite C product, its parameter substitution, literal
polar primitive, pivot and polynomial tail supply this exact scalar law.
No integral comparison or logarithmic normalization is inferred from it.
-/
theorem principal_parameter_coefficient {loopBase : Canonical} {loopNonzero : loopBase ≠ 0}
    {circuit : Integral.Circuit loopBase loopNonzero}
    (cached : ParameterPrimitives retained circuit) {parameter : Canonical}
    (nonzero : parameter ≠ 0) :
    Coefficient.principalValue (parameter := parameter) retained primitive =
      ParameterPrimitives.Program.coefficient cached parameter := by
  have split := Coefficient.principalValue_parameter_split retained primitive cached.table cached.polar nonzero
  rewrite [← cached.tail.property] at split
  exact split.trans ((ParameterPrimitives.Program.coefficient_eq cached parameter).trans
    (cached.coefficient_split parameter nonzero)).symm

/-- The actual saved principal path compares with the retained Laurent programme's scalar coefficient on the same mesh.

The exact original parameter table is consumed in the reference dyadic
model; its same-curve points and independent observation/product/accuracy
payments are unchanged. One supplied whole origin reciprocal Request
serves every original occurrence. This is a quantitative finite programme
sample comparison, before four-quarter output and residue normalization.
-/
theorem principal_parameter_model_distance_le {data : Polynomials differential} (cached : data.Bounds base)
    (jetBounds : jet.Bounds collar.box) (nonzero : base ≠ 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus)
    (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    {loopBase : Canonical} {loopNonzero : loopBase ≠ 0} {circuit : Integral.Circuit loopBase loopNonzero}
    (parameterCached : ParameterPrimitives retained circuit)
    (positive : 0 < expandedTarget) {productTarget comparisonTarget : Fraction.Rational}
    (productPositive : 0 < productTarget) (comparisonPositive : 0 < comparisonTarget)
    (reciprocal : Request (div (Coherence.exact 1) origin.certificate.value origin.certificate.apart)
      (principalTarget cached jetBounds productTarget))
    (allowance : { value : Fraction.Rational // 0 ≤ value }) :
    Norm.Basic.normSq ((expanded.partsModel false allowance).integralSample -
      reciprocal.reading.value * (Dyadic.model base actual
        (ParameterPrimitives.Program.coefficient parameterCached) depth left right).integralSample) ≤
      (4 * Norm.Basic.normSq base) * (32 * (expandedTarget + productTarget) + 4 * comparisonTarget) := by
  have coefficientSamples := Dyadic.model_sample_congr base actual
    (fun parameter => Coefficient.principalValue (parameter := parameter) retained primitive)
    (ParameterPrimitives.Program.coefficient parameterCached)
    (fun time => principal_parameter_coefficient (primitive := primitive) parameterCached
      (point_nonzero base nonzero actual time)) depth left right
  have paid := expanded.principal_model_distance_le cached jetBounds nonzero bound
    positive productPositive comparisonPositive reciprocal allowance
  rewrite [coefficientSamples] at paid
  exact paid

namespace ErrorBounds

/-- The actual total-form sample differs from the reciprocal-weighted principal parameter sample by paid finite bounds.

The same saved expansion supplies its principal and error parts. Original
sample comparisons pay both the total-form observation and reciprocal
product independently, while the retained error setup bounds the actual
velocity-weighted tail. Every displayed target and the original numerical
square remain explicit; no vanishing coefficient error is assumed.
-/
theorem model_parameter_distance_le {data : Polynomials differential} (cached : data.Bounds base)
    (jetBounds : jet.Bounds collar.box) (nonzero : base ≠ 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus)
    (bounds : ErrorBounds origin jet remainder polynomial)
    (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
    {loopBase : Canonical} {loopNonzero : loopBase ≠ 0} {circuit : Integral.Circuit loopBase loopNonzero}
    (parameterCached : ParameterPrimitives retained circuit)
    (sourcePositive : 0 < target) (positive : 0 < expandedTarget) (accuracyPositive : 0 < accuracy)
    (near : Norm.Basic.normSq base ≤ bounds.1.1.val ^ 2)
    {productTarget comparisonTarget : Fraction.Rational}
    (productPositive : 0 < productTarget) (comparisonPositive : 0 < comparisonTarget)
    (reciprocal : Request (div (Coherence.exact 1) origin.certificate.value origin.certificate.apart)
      (principalTarget cached jetBounds productTarget))
    (sourceAllowance : Option { value : Fraction.Rational // 0 ≤ value })
    (allowance : { value : Fraction.Rational // 0 ≤ value }) :
    Norm.Basic.normSq ((stored.model sourceAllowance).integralSample -
      reciprocal.reading.value * (Dyadic.model base actual
        (ParameterPrimitives.Program.coefficient parameterCached) depth left right).integralSample) ≤
      2 * (2 * ((4 * Norm.Basic.normSq base) * (16 * (target + expandedTarget) + 4 * accuracy) +
        (4 * Norm.Basic.normSq base) * bounds.readingUpper expandedTarget) +
        (4 * Norm.Basic.normSq base) * (32 * (expandedTarget + productTarget) + 4 * comparisonTarget)) := by
  have first := bounds.model_principal_distance_le expanded sourcePositive positive accuracyPositive near
    sourceAllowance allowance allowance allowance
  have last := expanded.principal_parameter_model_distance_le cached jetBounds nonzero bound parameterCached
    positive productPositive comparisonPositive reciprocal allowance
  exact (Norm.Bounds.normSq_sub_le_via _ (expanded.partsModel false allowance).integralSample _).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct first last) (by decide))

end ErrorBounds

section PrincipalRequest

variable {data : Polynomials differential} (cached : data.Bounds base) (jetBounds : jet.Bounds collar.box)
  (nonzero : base ≠ 0) (bound : differential.numerator.natDegree ≤ 2 * genus)
  (expanded : Jets stored origin jet remainder polynomial retained primitive expandedTarget accuracy)
  {loopBase : Canonical} {loopNonzero : loopBase ≠ 0} {circuit : Integral.Circuit loopBase loopNonzero}
  (parameterCached : ParameterPrimitives retained circuit) (positive : 0 < expandedTarget)
  {productTarget comparisonTarget : Fraction.Rational}
  (productPositive : 0 < productTarget) (comparisonPositive : 0 < comparisonTarget)
  (allowance : { value : Fraction.Rational // 0 ≤ value })

/-- Compute one original origin reciprocal Request and certify its finite saved-principal path comparison.

The output is the same original Request, indexed by its actual computed
common target, with a derived scalar Laurent path bound. Its original
origin, apartness, observations and payments remain unchanged. The request
is built once before every original bank occurrence; this operation does
not evaluate a large dyadic sample or assert an output integral equality.
-/
def principalRequest :
    { reciprocal : Request (div (Coherence.exact 1) origin.certificate.value origin.certificate.apart)
        (principalTarget cached jetBounds productTarget) //
      Norm.Basic.normSq ((expanded.partsModel false allowance).integralSample -
        reciprocal.reading.value * (Dyadic.model base actual
          (ParameterPrimitives.Program.coefficient parameterCached) depth left right).integralSample) ≤
        (4 * Norm.Basic.normSq base) * (32 * (expandedTarget + productTarget) + 4 * comparisonTarget) } :=
  let reciprocal := Request.build _ _ (principalTarget_positive cached jetBounds nonzero productPositive)
  ⟨reciprocal, expanded.principal_parameter_model_distance_le cached jetBounds nonzero bound parameterCached
    positive productPositive comparisonPositive reciprocal allowance⟩

/-- The finite comparison retains the complete original reciprocal Request and its exact builder procedure. -/
theorem principalRequest_request :
    (principalRequest cached jetBounds nonzero bound expanded parameterCached positive
      productPositive comparisonPositive allowance).val =
        Request.build (div (Coherence.exact 1) origin.certificate.value origin.certificate.apart)
          (principalTarget cached jetBounds productTarget)
          (principalTarget_positive cached jetBounds nonzero productPositive) := by
  unfold principalRequest
  rfl

end PrincipalRequest

end Jets

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Readings

end
