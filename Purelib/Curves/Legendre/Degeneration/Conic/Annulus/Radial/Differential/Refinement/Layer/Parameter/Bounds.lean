module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Geometry.Rational.Box.Square.Centered.Norm
import Purelib.Data.Gaussian.Norm.Reciprocal
import Purelib.Polynomial.Quadratic.Split
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Uniform parameter remainders on actual cached parallel samples

The exact original geometric margin readbacks determine source, target
and sum floors shared by every retained physical node. They compute one
original centred square containing every possible source and target
reciprocal reading. The existing finite bank bounds then apply to both
actual arithmetic rows and original physical weights without supplied
root certificates, inverse enclosures or final sample inequalities.

These remain finite weighted parameter samples. Agreement with geometric
integral programs and cancellation of genuine rational primitives are
separate certificates.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter.Samples

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Algebra
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Rational

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter increment : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Radial.Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}
variable {initial : Radial.Differential.Refinement.Piece data actual accuracy} {depth : Nat}
variable {layer : Layer initial depth} {regular : parameter ≠ criticalValue site}
variable {admitted : Radial.Parameter.IncrementBound site parameter increment} {nonzero : increment ≠ 0}

/-- The geometric source-observation margin is shared by every original node of the retained sample cache. -/
@[expose] def sourceMargin (_samples : Samples layer regular increment admitted nonzero) : Fraction.Rational :=
  (9 / Fraction.Cast.fromInt 65536) * Norm.Basic.normSq (halfGap site parameter)

/-- The unchanged geometric target-candidate construction gives its stronger common original margin. -/
@[expose] def targetMargin (_samples : Samples layer regular increment admitted nonzero) : Fraction.Rational :=
  (9 / Fraction.Cast.fromInt 16384) * Norm.Basic.normSq (halfGap site parameter)

/-- The same original source margin also pays paired source-target sums at every retained physical node. -/
@[expose] def sumMargin (samples : Samples layer regular increment admitted nonzero) : Fraction.Rational :=
  samples.sourceMargin

/-- Every actual source clearance floor equals the retained geometric common source margin. -/
theorem sourceMargin_eq (samples : Samples layer regular increment admitted nonzero)
    (node : Fin layer.pieces.length) : (samples.jets.get node).val.clearance.sourceFloor = samples.sourceMargin :=
  samples.sourceFloor_uniform node

/-- Every actual target clearance floor agrees with the stronger common geometric target margin. -/
theorem targetMargin_eq (samples : Samples layer regular increment admitted nonzero)
    (node : Fin layer.pieces.length) : (samples.jets.get node).val.clearance.targetFloor = samples.targetMargin :=
  samples.targetFloor_uniform node

/-- All retained same-pair sum floors agree with the common original geometric sum margin. -/
theorem sumMargin_eq (samples : Samples layer regular increment admitted nonzero)
    (node : Fin layer.pieces.length) : (samples.jets.get node).val.clearance.sumFloor = samples.sumMargin :=
  samples.sumFloor_uniform node

/-- Regularity of the original labelled parameter makes its retained half-gap quadrance positive. -/
private theorem gapPositive (regular : parameter ≠ criticalValue site) :
    0 < Norm.Basic.normSq (halfGap site parameter) :=
  Norm.Basic.normSq_pos (Polynomial.Quadratic.Split.halfGap_ne_zero
    (by decide +kernel : (2 : Canonical) ≠ 0) regular.symm)

/-- The common actual source-candidate margin is strictly positive at the retained regular parameter. -/
theorem sourceMargin_positive (samples : Samples layer regular increment admitted nonzero) :
    0 < samples.sourceMargin :=
  Arithmetic.mul_pos_direct
    (by decide +kernel : (0 : Fraction.Rational) < 9 / Fraction.Cast.fromInt 65536) (gapPositive regular)

/-- The stronger common target-candidate margin is positive on that same regular source geometry. -/
theorem targetMargin_positive (samples : Samples layer regular increment admitted nonzero) :
    0 < samples.targetMargin :=
  Arithmetic.mul_pos_direct
    (by decide +kernel : (0 : Fraction.Rational) < 9 / Fraction.Cast.fromInt 16384) (gapPositive regular)

/-- The exact common sum margin inherits positivity from the identical original source margin. -/
theorem sumMargin_positive (samples : Samples layer regular increment admitted nonzero) : 0 < samples.sumMargin :=
  samples.sourceMargin_positive

/-- The two inverse geometric floors provide a nonnegative common reciprocal-quadrance budget. -/
theorem inverseBudget_nonnegative (samples : Samples layer regular increment admitted nonzero) :
    0 ≤ samples.sourceMargin⁻¹ + samples.targetMargin⁻¹ :=
  Arithmetic.add_le_add_direct
    (Fraction.Order.Field.inv_pos_direct samples.sourceMargin_positive).le
    (Fraction.Order.Field.inv_pos_direct samples.targetMargin_positive).le

/-- Compute one original centred rational square enclosing both actual reciprocal candidate sets uniformly. -/
@[expose] def inverseBox (samples : Samples layer regular increment admitted nonzero) : Box :=
  Box.Square.Centered.normBox (samples.sourceMargin⁻¹ + samples.targetMargin⁻¹) samples.inverseBudget_nonnegative

/-- Every candidate of the same original source observation has its reciprocal in the internally computed common box. -/
theorem sourceInverse_contains (samples : Samples layer regular increment admitted nonzero)
    (node : Fin layer.pieces.length) {candidate : Canonical}
    (possible : (samples.jets.get node).val.sourceSample.observation.Possible candidate) :
    samples.inverseBox.Contains candidate⁻¹ := by
  have lower := (samples.jets.get node).val.clearance.sourceLower possible
  rewrite [samples.sourceMargin_eq node] at lower
  have inverseBound := Norm.Reciprocal.normSq_le samples.sourceMargin_positive lower
  have budgetBound := Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl samples.sourceMargin⁻¹)
    (Fraction.Order.Field.inv_pos_direct samples.targetMargin_positive).le
  rewrite [Fraction.Field.add_comm samples.sourceMargin⁻¹ 0, Fraction.Field.zero_add] at budgetBound
  exact Box.Square.Centered.normBox_contains samples.inverseBudget_nonnegative (inverseBound.trans budgetBound)

/-- Every distinct original target candidate pays the matching reciprocal floor in that identical computed box. -/
theorem targetInverse_contains (samples : Samples layer regular increment admitted nonzero)
    (node : Fin layer.pieces.length) {candidate : Canonical}
    (possible : (samples.jets.get node).val.targetSample.observation.Possible candidate) :
    samples.inverseBox.Contains candidate⁻¹ := by
  have lower := (samples.jets.get node).val.clearance.targetLower possible
  rewrite [samples.targetMargin_eq node] at lower
  have inverseBound := Norm.Reciprocal.normSq_le samples.targetMargin_positive lower
  have budgetBound := Arithmetic.add_le_add_direct
    (Fraction.Order.Field.inv_pos_direct samples.sourceMargin_positive).le
    (Fraction.Order.Basic.le_refl samples.targetMargin⁻¹)
  rewrite [Fraction.Field.zero_add] at budgetBound
  exact Box.Square.Centered.normBox_contains samples.inverseBudget_nonnegative (inverseBound.trans budgetBound)

/-- The exact saved source witness uses the common inverse box without another root request. -/
theorem sourceInverse_inside (samples : Samples layer regular increment admitted nonzero)
    (node : Fin layer.pieces.length) : samples.inverseBox.Contains (samples.jets.get node).val.sourceSample.reading⁻¹ :=
  samples.sourceInverse_contains node (samples.jets.get node).val.sourceSample.observation.witness_possible

/-- The independently selected original target witness lies in that same internally derived reciprocal enclosure. -/
theorem targetInverse_inside (samples : Samples layer regular increment admitted nonzero)
    (node : Fin layer.pieces.length) : samples.inverseBox.Contains (samples.jets.get node).val.targetSample.reading⁻¹ :=
  samples.targetInverse_contains node (samples.jets.get node).val.targetSample.observation.witness_possible

/-- The original spatial patch and common geometric margins compute the actual cached value-row factor ceiling. -/
@[expose] def valueCeiling (samples : Samples layer regular increment admitted nonzero) (coordinate : Fin 2) :
    Fraction.Rational :=
  Variation.Arithmetic.valueCeiling parameter increment coordinate (spatialBox site)
    samples.sourceMargin samples.targetMargin samples.sumMargin

/-- The computed inverse box pays the original cached first-row and independent second-slope factor. -/
@[expose] def firstCeiling (samples : Samples layer regular increment admitted nonzero) (coordinate : Fin 2) :
    Fraction.Rational :=
  Variation.Arithmetic.firstCeiling parameter increment coordinate (spatialBox site) samples.inverseBox
    samples.sourceMargin samples.targetMargin samples.sumMargin

/-- Every original value-row ceiling is nonnegative from the same internally derived three geometric margins. -/
theorem valueCeiling_nonnegative (samples : Samples layer regular increment admitted nonzero) (coordinate : Fin 2) :
    0 ≤ samples.valueCeiling coordinate :=
  Variation.Arithmetic.valueCeiling_nonnegative parameter increment coordinate (spatialBox site)
    samples.sourceMargin_positive samples.targetMargin_positive samples.sumMargin_positive

/-- Both actual first-row ceilings have the matching internal nonnegativity certificate for weighted assembly. -/
theorem firstCeiling_nonnegative (samples : Samples layer regular increment admitted nonzero) (coordinate : Fin 2) :
    0 ≤ samples.firstCeiling coordinate :=
  Variation.Arithmetic.firstCeiling_nonnegative parameter increment coordinate (spatialBox site) samples.inverseBox
    samples.sourceMargin_positive samples.targetMargin_positive samples.sumMargin_positive

/-- The actual saved value bank has a mesh-independent factor bound from its same original physical weights. -/
theorem value_factor_le (samples : Samples layer regular increment admitted nonzero) (coordinate : Fin 2) :
    (samples.bank.value coordinate).factor ≤
      (((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) * initial.span.width ^ 2) *
        samples.valueCeiling coordinate := by
  apply samples.bank.value_factor_le coordinate depth layer.count _ _ (samples.valueCeiling_nonnegative coordinate)
  · intro node
    rewrite [samples.weights_eq]
    exact layer.weights_normSq_le node
  · intro node
    have bound := (samples.rows.get node).val.value_factor_le coordinate (layer.points_inside node)
    rewrite [samples.sourceMargin_eq node, samples.targetMargin_eq node, samples.sumMargin_eq node] at bound
    exact bound

/-- The same original physical weights pay the actual first bank with its internally enclosed inverse/cubic caches. -/
theorem first_factor_le (samples : Samples layer regular increment admitted nonzero) (coordinate : Fin 2) :
    (samples.bank.first coordinate).factor ≤
      (((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) * initial.span.width ^ 2) *
        samples.firstCeiling coordinate := by
  apply samples.bank.first_factor_le coordinate depth layer.count _ _ (samples.firstCeiling_nonnegative coordinate)
  · intro node
    rewrite [samples.weights_eq]
    exact layer.weights_normSq_le node
  · intro node
    have bound := (samples.rows.get node).val.first_factor_le coordinate (layer.points_inside node)
      (samples.sourceInverse_inside node) (samples.targetInverse_inside node)
    rewrite [samples.sourceMargin_eq node, samples.targetMargin_eq node, samples.sumMargin_eq node] at bound
    exact bound

/-- The actual retained value samples and independently observed first slopes pay a uniform fourth-order remainder. -/
theorem value_remainder_le (samples : Samples layer regular increment admitted nonzero) (coordinate : Fin 2) :
    Canonical.normSq
      (FiniteSum.Fin.sumFin (fun node =>
          samples.weights node * ((samples.rows.get node).val.targetValue coordinate).reading) -
        FiniteSum.Fin.sumFin (fun node =>
          samples.weights node * ((samples.rows.get node).val.sourceValue coordinate).reading) -
        increment * FiniteSum.Fin.sumFin (fun node =>
          samples.weights node * ((samples.rows.get node).val.sourceFirst coordinate).reading)) ≤
      ((((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) * initial.span.width ^ 2) *
        samples.valueCeiling coordinate) * Canonical.normSq increment ^ 2 :=
  (samples.bank.value_remainder_le coordinate).trans
    (Arithmetic.mul_le_mul_of_nonneg_right_direct (samples.value_factor_le coordinate)
      (Arithmetic.sq_nonneg_direct _))

/-- The actual retained first samples keep their independent second slopes in the same uniform remainder payment. -/
theorem first_remainder_le (samples : Samples layer regular increment admitted nonzero) (coordinate : Fin 2) :
    Canonical.normSq
      (FiniteSum.Fin.sumFin (fun node =>
          samples.weights node * ((samples.rows.get node).val.targetFirst coordinate).reading) -
        FiniteSum.Fin.sumFin (fun node =>
          samples.weights node * ((samples.rows.get node).val.sourceFirst coordinate).reading) -
        increment * FiniteSum.Fin.sumFin (fun node =>
          samples.weights node * ((samples.rows.get node).val.sourceSecond coordinate).reading)) ≤
      ((((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) * initial.span.width ^ 2) *
        samples.firstCeiling coordinate) * Canonical.normSq increment ^ 2 :=
  (samples.bank.first_remainder_le coordinate).trans
    (Arithmetic.mul_le_mul_of_nonneg_right_direct (samples.first_factor_le coordinate)
      (Arithmetic.sq_nonneg_direct _))

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter.Samples
