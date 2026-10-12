module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.NormSq.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Basic
public import Purelib.Geometry.Projective.Hermitian.Chart.Basic
public import Purelib.Geometry.Projective.Hermitian.Chart.Source
import Purelib.Geometry.Projective.Hermitian.Comparison
import Purelib.Geometry.Projective.Hermitian.Parametrization.Comparison
import Purelib.Geometry.Projective.Homography.Basic
public import Purelib.Geometry.Projective.Homography.BoxBounds
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.RationalFunctions.Curve.Canonical.Circle.Basic
public import Purelib.RationalFunctions.Curve.Canonical.Circle.Coverage
import Purelib.RationalFunctions.Curve.Canonical.Line
import Purelib.RationalFunctions.Curve.Transform
import Init.Data.List.Lemmas
import Init.Prelude
import Init.SimpLemmas
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.RationalFunctions.Curve.Basic

open Purelib

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Data.Rat.Interval

open Purelib.Geometry

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.LinearAlgebra.Coordinates2.Matrix

open Purelib.RationalFunctions

open Purelib.RationalFunctions.Curve.Canonical

section
@[expose] public section

/-!
# Bounded finite charts for CCL branch boundaries

Circle boundaries use the primary and reciprocal stereographic charts on the
fixed rational cell `[-1,1]`.  Coordinate-line boundaries use one symmetric
cell whose radius is computed from a coefficient majorant for the affine
numerator and an explicitly supplied positive lower bound for the affine
denominator.  Each chart is immediately sent through the finite cleared-gcd
and Sturm event classifier.
-/

namespace Purelib.Geometry.Projective.Hermitian.Chart

/-- A displayed point is reached by one parameter inside a bounded chart. -/
def PointCoverage {form : Hermitian.HermitianForm}
    (value : Data.Gaussian.Basic.Canonical) (chart : Chart.BoundedChart form) : Prop :=
  ∃ parameter,
    chart.cell.interval.Contains parameter ∧
      chart.parameterization.curve.denominatorAt parameter ≠ 0 ∧
      chart.parameterization.curve.point parameter = value

/-- The complete finite chart family: exactly two unit cells for a norm circle, and exactly one coefficient-bounded cell
for a coordinate line. -/
def charts
    {reference : GaussianMatrix} {form : Hermitian.HermitianForm}
    (source : Chart.CurveSource reference form)
    (box : Rational.Box) (denominatorMargin : Fraction.Rational)
    (marginPositive : 0 < denominatorMargin) : List (Chart.BoundedChart form) :=
  match source with
  | .norm matrix determinantNonzero _lowerRow base _baseNonzero form_eq =>
      [{ parameterization :=
          form_eq.symm ▸
            Parametrization.normComparison matrix
              determinantNonzero base
         cell := Proper.unitCell },
       { parameterization :=
          form_eq.symm ▸
            Parametrization.normComparisonReciprocal matrix
              determinantNonzero base
         cell := Proper.unitCell }]
  | .real matrix determinantNonzero _lowerRow threshold form_eq =>
      [{ parameterization :=
          form_eq.symm ▸
            Parametrization.realComparison matrix
              determinantNonzero threshold
         cell := Proper.symmetricCell
           (Homography.lineParameterRadius matrix box denominatorMargin)
           (Homography.lineParameterRadius_pos matrix box marginPositive) }]
  | .imaginary matrix determinantNonzero _lowerRow threshold form_eq =>
      [{ parameterization :=
          form_eq.symm ▸
            Parametrization.imaginaryComparison matrix
              determinantNonzero threshold
         cell := Proper.symmetricCell
           (Homography.lineParameterRadius matrix box denominatorMargin)
           (Homography.lineParameterRadius_pos matrix box marginPositive) }]

/-- Coverage by one member of the finite chart family. -/
def Covered
    {reference : GaussianMatrix} {form : Hermitian.HermitianForm}
    (source : Chart.CurveSource reference form) (box : Rational.Box)
    (denominatorMargin : Fraction.Rational)
    (marginPositive : 0 < denominatorMargin) (value : Data.Gaussian.Basic.Canonical) : Prop :=
  ∃ chart, chart ∈ charts source box denominatorMargin marginPositive ∧
    PointCoverage value chart

set_option genInjectivity false in
/-- Executable proof-bearing form of finite chart coverage. Unlike the propositional `Covered` wrapper, this record can
be consumed by later finite algorithms without eliminating an existential proposition into data. -/
structure Coverage
    {reference : GaussianMatrix} {form : Hermitian.HermitianForm}
    (source : Chart.CurveSource reference form) (box : Rational.Box)
    (denominatorMargin : Fraction.Rational)
    (marginPositive : 0 < denominatorMargin) (value : Data.Gaussian.Basic.Canonical) where
  /-- The selected bounded chart for the retained boundary form. -/ chart : Chart.BoundedChart form
  /-- The chart belongs to the actual finite family produced from this source and box. -/ chartMember : chart ∈
    charts source box denominatorMargin marginPositive
  /-- The retained rational parameter representing the target point. -/ parameter : Fraction.Rational
  /-- The selected parameter lies in the chart's retained interval. -/ parameterInside : chart.cell.interval.Contains
    parameter
  /-- The curve denominator does not vanish at this parameter. -/ curveDenominatorNonzero :
    chart.parameterization.curve.denominatorAt parameter ≠ 0
  /-- The selected chart and parameter evaluate to the exact target point. -/ point_eq :
    chart.parameterization.curve.point parameter = value

constructive_injectivity Coverage

/-- Forget the retained chart and parameter data to obtain propositional coverage. -/
theorem Coverage.covered
    {reference : GaussianMatrix} {form : Hermitian.HermitianForm}
    {source : Chart.CurveSource reference form} {box : Rational.Box}
    {denominatorMargin : Fraction.Rational}
    {marginPositive : 0 < denominatorMargin} {value : Data.Gaussian.Basic.Canonical}
    (coverage : Coverage source box denominatorMargin marginPositive value) :
    Covered source box denominatorMargin marginPositive value :=
  ⟨coverage.chart, coverage.chartMember, coverage.parameter,
    coverage.parameterInside, coverage.curveDenominatorNonzero,
    coverage.point_eq⟩

/-- The bounded vertical-line chart covers every point of the corresponding pulled-back boundary inside the current box.
-/
def realSource_cover
    (reference matrix : GaussianMatrix)
    (determinantNonzero :
      BoundaryAdjugate.determinant matrix ≠ 0)
    (lowerRow : matrix.c = reference.c ∧ matrix.d = reference.d)
    (threshold : Fraction.Rational) (box : Rational.Box)
    {denominatorMargin : Fraction.Rational}
    (marginPositive : 0 < denominatorMargin)
    (value : Data.Gaussian.Basic.Canonical) (inside : box.Contains value)
    (onBoundary :
      (Hermitian.realComparisonForm matrix threshold).eval
        value = 0)
    (referenceLower : denominatorMargin ≤
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator reference value)) :
    Coverage
      (.real matrix determinantNonzero lowerRow threshold rfl)
      box denominatorMargin marginPositive value := by
  let tail := Homography.Basic.homographic matrix value
  have denominatorIdentity :
      Homography.Basic.denominator matrix value =
        Homography.Basic.denominator reference value := by
    rcases lowerRow with ⟨left, right⟩
    simp only [Homography.Basic.denominator, left, right, -eq_self, -iff_self]
    rfl
  have denominatorLower : denominatorMargin ≤
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) := by
    rw [denominatorIdentity]
    exact referenceLower
  have denominatorNonzero :
      Homography.Basic.denominator matrix value ≠ 0 :=
    NormSq.denominator_ne_of_margin marginPositive denominatorLower
  have tailNorm : Data.Gaussian.Norm.Basic.normSq tail ≤
      Homography.decodedNormMajorant matrix box denominatorMargin :=
    Homography.normSq_homographic_le_decodedNormMajorant matrix box marginPositive
      inside denominatorLower
  have bounds := NormSq.coordinate_bounds_of_normSq_le tail tailNorm
  have realEquality : tail.re = threshold :=
    (Hermitian.real_homographic_eq_iff
      matrix value threshold denominatorNonzero).2 onBoundary
  have sourcePoint :
      (Line.realLine threshold).point tail.im =
        tail := by
    rw [Line.realLine_point]
    apply Data.Gaussian.Basic.ext
    · exact realEquality.symm
    · rfl
  have transformed := Curve.inverseTransform_point matrix determinantNonzero
    (Line.realLine threshold) tail.im
    (Line.realLine_denominator_ne threshold tail.im)
    value denominatorNonzero sourcePoint
  let chart : Chart.BoundedChart
      (Hermitian.realComparisonForm matrix threshold) :=
    { parameterization :=
        Parametrization.realComparison matrix
          determinantNonzero threshold
      cell := Proper.symmetricCell
        (Homography.lineParameterRadius matrix box denominatorMargin)
        (Homography.lineParameterRadius_pos matrix box marginPositive) }
  refine ⟨chart, ?_, tail.im, ?_, ?_, ?_⟩
  · simp only [charts, -eq_self, -iff_self]
    exact List.Mem.head []
  · change -Homography.lineParameterRadius matrix box denominatorMargin ≤ tail.im ∧
      tail.im ≤ Homography.lineParameterRadius matrix box denominatorMargin
    simpa only [Homography.lineParameterRadius] using ⟨bounds.2.2.1, bounds.2.2.2⟩
  · change ((Line.realLine threshold).transform
      (BoundaryAdjugate.adjugate matrix)).denominatorAt tail.im ≠ 0
    exact transformed.1
  · change ((Line.realLine threshold).transform
      (BoundaryAdjugate.adjugate matrix)).point tail.im = value
    exact transformed.2

/-- The bounded horizontal-line chart covers every point of the corresponding pulled-back boundary inside the current
box. -/
def imaginarySource_cover
    (reference matrix : GaussianMatrix)
    (determinantNonzero :
      BoundaryAdjugate.determinant matrix ≠ 0)
    (lowerRow : matrix.c = reference.c ∧ matrix.d = reference.d)
    (threshold : Fraction.Rational) (box : Rational.Box)
    {denominatorMargin : Fraction.Rational}
    (marginPositive : 0 < denominatorMargin)
    (value : Data.Gaussian.Basic.Canonical) (inside : box.Contains value)
    (onBoundary :
      (Hermitian.imagComparisonForm matrix threshold).eval
        value = 0)
    (referenceLower : denominatorMargin ≤
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator reference value)) :
    Coverage
      (.imaginary matrix determinantNonzero lowerRow threshold rfl)
      box denominatorMargin marginPositive value := by
  let tail := Homography.Basic.homographic matrix value
  have denominatorIdentity :
      Homography.Basic.denominator matrix value =
        Homography.Basic.denominator reference value := by
    rcases lowerRow with ⟨left, right⟩
    simp only [Homography.Basic.denominator, left, right, -eq_self, -iff_self]
    rfl
  have denominatorLower : denominatorMargin ≤
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) := by
    rw [denominatorIdentity]
    exact referenceLower
  have denominatorNonzero :
      Homography.Basic.denominator matrix value ≠ 0 :=
    NormSq.denominator_ne_of_margin marginPositive denominatorLower
  have tailNorm : Data.Gaussian.Norm.Basic.normSq tail ≤
      Homography.decodedNormMajorant matrix box denominatorMargin :=
    Homography.normSq_homographic_le_decodedNormMajorant matrix box marginPositive
      inside denominatorLower
  have bounds := NormSq.coordinate_bounds_of_normSq_le tail tailNorm
  have imaginaryEquality : tail.im = threshold :=
    (Hermitian.imag_homographic_eq_iff
      matrix value threshold denominatorNonzero).2 onBoundary
  have sourcePoint :
      (Line.imaginaryLine threshold).point tail.re =
        tail := by
    rw [Line.imaginaryLine_point]
    apply Data.Gaussian.Basic.ext
    · rfl
    · exact imaginaryEquality.symm
  have transformed := Curve.inverseTransform_point matrix determinantNonzero
    (Line.imaginaryLine threshold) tail.re
    (Line.imaginaryLine_denominator_ne threshold
      tail.re)
    value denominatorNonzero sourcePoint
  let chart : Chart.BoundedChart
      (Hermitian.imagComparisonForm matrix threshold) :=
    { parameterization :=
        Parametrization.imaginaryComparison matrix
          determinantNonzero threshold
      cell := Proper.symmetricCell
        (Homography.lineParameterRadius matrix box denominatorMargin)
        (Homography.lineParameterRadius_pos matrix box marginPositive) }
  refine ⟨chart, ?_, tail.re, ?_, ?_, ?_⟩
  · exact List.Mem.head []
  · change -Homography.lineParameterRadius matrix box denominatorMargin ≤ tail.re ∧
      tail.re ≤ Homography.lineParameterRadius matrix box denominatorMargin
    simpa only [Homography.lineParameterRadius] using ⟨bounds.1, bounds.2.1⟩
  · change ((Line.imaginaryLine threshold).transform
      (BoundaryAdjugate.adjugate matrix)).denominatorAt tail.re ≠ 0
    exact transformed.1
  · change ((Line.imaginaryLine threshold).transform
      (BoundaryAdjugate.adjugate matrix)).point tail.re = value
    exact transformed.2

/-- The two bounded circle charts cover every point of the corresponding pulled-back norm boundary inside the current
box. -/
def normSource_cover
    (reference matrix : GaussianMatrix)
    (determinantNonzero :
      BoundaryAdjugate.determinant matrix ≠ 0)
    (lowerRow : matrix.c = reference.c ∧ matrix.d = reference.d)
    (base : Data.Gaussian.Basic.Canonical) (baseNonzero : base ≠ 0) (box : Rational.Box)
    {denominatorMargin : Fraction.Rational}
    (marginPositive : 0 < denominatorMargin)
    (value : Data.Gaussian.Basic.Canonical) (_inside : box.Contains value)
    (onBoundary :
      (Hermitian.normComparisonForm matrix (Data.Gaussian.Norm.Basic.normSq base)).eval
        value = 0)
    (referenceLower : denominatorMargin ≤
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator reference value)) :
    Coverage
      (.norm matrix determinantNonzero lowerRow base baseNonzero rfl)
      box denominatorMargin marginPositive value := by
  let tail := Homography.Basic.homographic matrix value
  have denominatorIdentity :
      Homography.Basic.denominator matrix value =
        Homography.Basic.denominator reference value := by
    rcases lowerRow with ⟨left, right⟩
    simp only [Homography.Basic.denominator, left, right, -eq_self, -iff_self]
    rfl
  have denominatorLower : denominatorMargin ≤
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) := by
    rw [denominatorIdentity]
    exact referenceLower
  have denominatorNonzero :
      Homography.Basic.denominator matrix value ≠ 0 :=
    NormSq.denominator_ne_of_margin marginPositive denominatorLower
  have tailNorm : Data.Gaussian.Norm.Basic.normSq tail = Data.Gaussian.Norm.Basic.normSq base :=
    (Hermitian.norm_homographic_eq_iff matrix value
      (Data.Gaussian.Norm.Basic.normSq base) denominatorNonzero).2 onBoundary
  by_cases baseZero : base = 0
  · exact (baseNonzero baseZero).elim
  · let unit := base⁻¹ * tail
    have baseNormNonzero : Data.Gaussian.Norm.Basic.normSq base ≠ 0 :=
      fun zero => baseZero (Data.Gaussian.Norm.Basic.normSq_eq_zero.mp zero)
    have unitNorm : Data.Gaussian.Norm.Basic.normSq unit = 1 := by
      dsimp only [unit]
      rw [Data.Gaussian.Norm.Basic.normSq_mul]
      rw [Data.Gaussian.Field.inv_eq,
        Data.Gaussian.Field.normSq_inv base baseZero, tailNorm,
        Fraction.Field.inv_mul_cancel _ baseNormNonzero]
    have baseUnit : base * unit = tail := by
      dsimp only [unit]
      calc
        base * (base⁻¹ * tail) = (base * base⁻¹) * tail :=
          (Data.Gaussian.Basic.mul_assoc _ _ _).symm
        _ = 1 * tail := by
          rw [Data.Gaussian.Field.inv_eq,
            Data.Gaussian.Field.mul_inv base baseZero]
        _ = tail := Data.Gaussian.Basic.one_mul _
    by_cases realNonnegative : 0 ≤ unit.re
    · let parameter := unit.im / (1 + unit.re)
      have covered := Circle.primaryUnitCircle_covers unit unitNorm realNonnegative
      have sourcePoint :
          (Circle.circle base).point parameter =
            tail := by
        rw [Circle.circle_point_scale]
        calc
          base * (Circle.circle 1).point parameter =
              base * unit := by rw [covered.2.2]
          _ = tail := baseUnit
      have transformed := Curve.inverseTransform_point matrix determinantNonzero
        (Circle.circle base) parameter
        (Circle.circle_denominator_ne base parameter)
        value denominatorNonzero sourcePoint
      let chart : Chart.BoundedChart
          (Hermitian.normComparisonForm matrix
            (Data.Gaussian.Norm.Basic.normSq base)) :=
        { parameterization :=
            Parametrization.normComparison matrix
              determinantNonzero base
          cell := Proper.unitCell }
      refine ⟨chart, ?_, parameter, ?_, ?_, ?_⟩
      · exact List.Mem.head _
      · exact ⟨covered.1, covered.2.1⟩
      · change ((Circle.circle base).transform
          (BoundaryAdjugate.adjugate matrix)).denominatorAt
            parameter ≠ 0
        exact transformed.1
      · change ((Circle.circle base).transform
          (BoundaryAdjugate.adjugate matrix)).point parameter = value
        exact transformed.2
    · have realNonpositive : unit.re ≤ 0 :=
        (lt_of_not_ge realNonnegative).le
      let parameter := unit.im / (1 - unit.re)
      have covered :=
        Circle.reciprocalUnitCircle_covers unit unitNorm realNonpositive
      have sourcePoint :
          (Circle.reciprocalCircle base).point
              parameter = tail := by
        rw [Circle.reciprocalCircle_point_scale]
        calc
          base *
              (Circle.reciprocalCircle 1).point
                parameter = base * unit := by rw [covered.2.2]
          _ = tail := baseUnit
      have transformed := Curve.inverseTransform_point matrix determinantNonzero
        (Circle.reciprocalCircle base) parameter
        (Circle.reciprocalCircle_denominator_ne
          base parameter)
        value denominatorNonzero sourcePoint
      let chart : Chart.BoundedChart
          (Hermitian.normComparisonForm matrix
            (Data.Gaussian.Norm.Basic.normSq base)) :=
        { parameterization :=
            Parametrization.normComparisonReciprocal matrix
              determinantNonzero base
          cell := Proper.unitCell }
      refine ⟨chart, ?_, parameter, ?_, ?_, ?_⟩
      · exact List.Mem.tail _ (List.Mem.head [])
      · exact ⟨covered.1, covered.2.1⟩
      · change
          ((Circle.reciprocalCircle base).transform
            (BoundaryAdjugate.adjugate matrix)).denominatorAt
              parameter ≠ 0
        exact transformed.1
      · change
          ((Circle.reciprocalCircle base).transform
            (BoundaryAdjugate.adjugate matrix)).point parameter =
              value
        exact transformed.2

/-- Every curve-source boundary point in the current box is represented by one of the finite charts that is actually
sent to event analysis. -/
def CurveSource.cover
    {reference : GaussianMatrix} {form : Hermitian.HermitianForm}
    (source : Chart.CurveSource reference form) (box : Rational.Box)
    {denominatorMargin : Fraction.Rational}
    (marginPositive : 0 < denominatorMargin)
    (value : Data.Gaussian.Basic.Canonical) (inside : box.Contains value)
    (onBoundary : form.eval value = 0)
    (referenceLower : denominatorMargin ≤
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator reference value)) :
    Coverage source box denominatorMargin marginPositive value := by
  cases source with
  | norm matrix determinantNonzero lowerRow base baseNonzero form_eq =>
      subst form
      exact normSource_cover reference matrix determinantNonzero lowerRow
        base baseNonzero box marginPositive value inside onBoundary
          referenceLower
  | real matrix determinantNonzero lowerRow threshold form_eq =>
      subst form
      exact realSource_cover reference matrix determinantNonzero lowerRow
        threshold box marginPositive value inside onBoundary referenceLower
  | imaginary matrix determinantNonzero lowerRow threshold form_eq =>
      subst form
      exact imaginarySource_cover reference matrix determinantNonzero lowerRow
        threshold box marginPositive value inside onBoundary referenceLower

/-- Propositional compatibility wrapper around the executable coverage record. -/
theorem CurveSource.covers
    {reference : GaussianMatrix} {form : Hermitian.HermitianForm}
    (source : Chart.CurveSource reference form) (box : Rational.Box)
    {denominatorMargin : Fraction.Rational}
    (marginPositive : 0 < denominatorMargin)
    (value : Data.Gaussian.Basic.Canonical) (inside : box.Contains value)
    (onBoundary : form.eval value = 0)
    (referenceLower : denominatorMargin ≤
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator reference value)) :
    Covered source box denominatorMargin marginPositive value :=
  (source.cover box marginPositive value inside onBoundary
    referenceLower).covered

/-- Every geometric boundary source produces a nonempty bounded chart family. -/
theorem charts_ne_nil
    {reference : GaussianMatrix} {form : Hermitian.HermitianForm}
    (source : Chart.CurveSource reference form)
    (box : Rational.Box) (denominatorMargin : Fraction.Rational)
    (marginPositive : 0 < denominatorMargin) :
    charts source box denominatorMargin marginPositive ≠ [] := by
  cases source <;> intro impossible <;> cases impossible

/-- Every geometric boundary source produces at most two bounded charts. -/
theorem charts_length_le_two
    {reference : GaussianMatrix} {form : Hermitian.HermitianForm}
    (source : Chart.CurveSource reference form)
    (box : Rational.Box) (denominatorMargin : Fraction.Rational)
    (marginPositive : 0 < denominatorMargin) :
    (charts source box denominatorMargin marginPositive).length ≤ 2 := by
  cases source
  · change 2 ≤ 2
    exact Nat.le_refl 2
  · change 1 ≤ 2
    exact Nat.le_succ 1
  · change 1 ≤ 2
    exact Nat.le_succ 1
end Purelib.Geometry.Projective.Hermitian.Chart

end
