module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial.Factor
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Normalization.InverseModelDifferentialResidual
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Product
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Fixed geometric allowances for the retained physical cap coefficient

The original numerator/inverse and differential-residual caches are built
before a primitive stage is selected. Their exact scalar combination
bounds the physical coefficient error of each actual retained sample at
that same stage, without replacing its finite inverse by an exact root.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.PolynomialSample

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse (Gaussian Polynomial Box Coordinate)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.InverseModelDifferentialResidual
    (DifferentialResidualBounds differentialResidual)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model half)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

/-- Retain the two original bound caches and their exact stage-independent coefficient scale.

The Sigma stores complete PrimitiveOverlapBounds and DifferentialResidualBounds
values, followed by the computed scale and its defining equation. It has no
sample, refinement index, duplicated cache fields or supplied error premise.
-/
@[expose] def ResidualBounds {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve}
    (cap : ReciprocalInnerInverse.Data curve collar) (numerator : Polynomial) :=
  (base : PrimitiveOverlapBounds cap.clearance numerator) ×
  (differential : DifferentialResidualBounds cap.model) ×
  { scale : Coordinate // scale = 2 * Norm.Basic.normSq half * collar.box.normSqBound *
        Bounds.Box.denseEvalNormBound cap.polynomial collar.box *
          ((2 * collar.box.normSqBound * base.numeratorUpper * base.inverseUpper) * differential.bound +
            base.numeratorUpper * cap.model.bound) }

namespace ResidualBounds

/-- Build the original numerator/inverse and differential caches once, then retain their fixed combined scale. -/
def build {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve}
    (cap : ReciprocalInnerInverse.Data curve collar) (numerator : Polynomial) : ResidualBounds cap numerator :=
  let base := PrimitiveOverlapBounds.build cap.clearance numerator
  let differential := DifferentialResidualBounds.build cap.model
  let W := collar.box.normSqBound
  let P := Bounds.Box.denseEvalNormBound cap.polynomial collar.box
  let U := 2 * W * base.numeratorUpper * base.inverseUpper
  let K := 2 * Norm.Basic.normSq half * W * P *
    (U * differential.bound + base.numeratorUpper * cap.model.bound)
  ⟨base, differential, ⟨K, rfl⟩⟩

/-- The complete retained cache is the displayed original two factories and scalar combination. -/
private theorem packaged_build_factory {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve}
    (cap : ReciprocalInnerInverse.Data curve collar) (numerator : Polynomial) :
    build cap numerator =
    let base := PrimitiveOverlapBounds.build cap.clearance numerator
    let differential := DifferentialResidualBounds.build cap.model
    let W := collar.box.normSqBound
    let P := Bounds.Box.denseEvalNormBound cap.polynomial collar.box
    let U := 2 * W * base.numeratorUpper * base.inverseUpper
    let K := 2 * Norm.Basic.normSq half * W * P *
      (U * differential.bound + base.numeratorUpper * cap.model.bound)
    ⟨base, differential, ⟨K, rfl⟩⟩ := by rfl

/-- The complete retained cache is the displayed original two factories and scalar combination. -/
theorem build_factory {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve}
    (cap : ReciprocalInnerInverse.Data curve collar) (numerator : Polynomial) :
    build cap numerator =
    let base := PrimitiveOverlapBounds.build cap.clearance numerator
    let differential := DifferentialResidualBounds.build cap.model
    let W := collar.box.normSqBound
    let P := Bounds.Box.denseEvalNormBound cap.polynomial collar.box
    let U := 2 * W * base.numeratorUpper * base.inverseUpper
    let K := 2 * Norm.Basic.normSq half * W * P *
      (U * differential.bound + base.numeratorUpper * cap.model.bound)
    ⟨base, differential, ⟨K, rfl⟩⟩ :=
  packaged_build_factory cap numerator

/-- Read the same complete numerator and inverse-root ceiling cache. -/
def base {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial} (bounds : ResidualBounds cap numerator) :
    PrimitiveOverlapBounds cap.clearance numerator := bounds.1

/-- Read the same complete initial differential-residual cache. -/
def differential {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial} (bounds : ResidualBounds cap numerator) :
    DifferentialResidualBounds cap.model := bounds.2.1

/-- Read the retained stage-independent physical coefficient scale. -/
def scale {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial} (bounds : ResidualBounds cap numerator) : Coordinate := bounds.2.2.val

/-- The retained scale is exactly the fixed combination of the two original caches. -/
private theorem packaged_scale_eq {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial} (bounds : ResidualBounds cap numerator) :
    bounds.scale = 2 * Norm.Basic.normSq half * collar.box.normSqBound *
        Bounds.Box.denseEvalNormBound cap.polynomial collar.box *
          ((2 * collar.box.normSqBound * bounds.base.numeratorUpper * bounds.base.inverseUpper) *
            bounds.differential.bound +
            bounds.base.numeratorUpper * cap.model.bound) := bounds.2.2.property

/-- The retained scale is exactly the fixed combination of the two original caches. -/
theorem scale_eq {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial} (bounds : ResidualBounds cap numerator) :
    bounds.scale = 2 * Norm.Basic.normSq half * collar.box.normSqBound *
        Bounds.Box.denseEvalNormBound cap.polynomial collar.box *
          ((2 * collar.box.normSqBound * bounds.base.numeratorUpper * bounds.base.inverseUpper) *
            bounds.differential.bound +
            bounds.base.numeratorUpper * cap.model.bound) :=
  packaged_scale_eq bounds

/-- The constructed numerator and inverse cache is exactly its original whole factory value. -/
private theorem packaged_base_build {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve}
    (cap : ReciprocalInnerInverse.Data curve collar) (numerator : Polynomial) :
    (build cap numerator).base = PrimitiveOverlapBounds.build cap.clearance numerator := by rfl

/-- The constructed numerator and inverse cache is exactly its original whole factory value. -/
theorem base_build {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve}
    (cap : ReciprocalInnerInverse.Data curve collar) (numerator : Polynomial) :
    (build cap numerator).base = PrimitiveOverlapBounds.build cap.clearance numerator :=
  packaged_base_build cap numerator

/-- The constructed differential cache is exactly its original complete factory value. -/
private theorem packaged_differential_build {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve}
    (cap : ReciprocalInnerInverse.Data curve collar) (numerator : Polynomial) :
    (build cap numerator).differential = DifferentialResidualBounds.build cap.model := by rfl

/-- The constructed differential cache is exactly its original complete factory value. -/
theorem differential_build {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve}
    (cap : ReciprocalInnerInverse.Data curve collar) (numerator : Polynomial) :
    (build cap numerator).differential = DifferentialResidualBounds.build cap.model :=
  packaged_differential_build cap numerator

/-- The fixed physical coefficient scale is nonnegative before any sample stage is selected. -/
theorem scale_nonnegative {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial} (bounds : ResidualBounds cap numerator) : 0 ≤ bounds.scale := by
  have shiftedNonnegative :
      0 ≤ 2 * collar.box.normSqBound * bounds.base.numeratorUpper * bounds.base.inverseUpper :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide +kernel) collar.box.normSqBound_nonneg)
        bounds.base.numeratorUpper_nonnegative) bounds.base.inverseUpper_positive.le
  have firstTerm := Arithmetic.mul_nonneg_direct shiftedNonnegative bounds.differential.bound_nonnegative
  have lastTerm := Arithmetic.mul_nonneg_direct bounds.base.numeratorUpper_nonnegative cap.model.bound_nonnegative
  have sumNonnegative :
      0 ≤ (2 * collar.box.normSqBound * bounds.base.numeratorUpper * bounds.base.inverseUpper) *
        bounds.differential.bound + bounds.base.numeratorUpper * cap.model.bound :=
    (Fraction.zero_add 0).symm.trans_le (Arithmetic.add_le_add_direct firstTerm lastTerm)
  have factorNonnegative :
      0 ≤ 2 * Norm.Basic.normSq half * collar.box.normSqBound *
        Bounds.Box.denseEvalNormBound cap.polynomial collar.box :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg half))
        collar.box.normSqBound_nonneg)
      (Bounds.Box.denseHornerNormBounds_nonneg cap.polynomial collar.box).1
  rewrite [bounds.scale_eq]
  exact Arithmetic.mul_nonneg_direct factorNonnegative sumNonnegative

end ResidualBounds

/-- The actual cached inverse has the original differential-residual quarter allowance at its own sample stage. -/
private theorem sample_differential_le {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial} {index : Nat} {box : Box}
    (sample : PolynomialSample cap numerator index box) (bounds : ResidualBounds cap numerator)
    {point : Gaussian} (inside : collar.box.Contains point) :
    Norm.Basic.normSq (differentialResidual cap.polynomial sample.1.val.value point) ≤
      quarterRadius bounds.differential.bound index := by
  have readback := congrArg (fun model : Model cap.polynomial collar.box =>
    Norm.Basic.normSq (differentialResidual cap.polynomial model.value point)) sample.1.property
  have original := bounds.differential.refine_bound index inside
  have converted := (Norm.Basic.normSq_eq_canonical
    (differentialResidual cap.polynomial (cap.model.refine index).value point)).trans_le original
  exact readback.trans_le converted

/-- The actual cached inverse residual has the original square-residual quarter allowance at its own sample stage. -/
private theorem sample_residual_le {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial} {index : Nat} {box : Box}
    (sample : PolynomialSample cap numerator index box)
    {point : Gaussian} (inside : collar.box.Contains point) :
    Norm.Basic.normSq (sample.1.val.residual.eval point) ≤ quarterRadius cap.model.bound index := by
  have readback := congrArg (fun model : Model cap.polynomial collar.box =>
    Norm.Basic.normSq (model.residual.eval point)) sample.1.property
  have original := (cap.model.refine index).residualBound point inside
  have converted := (Norm.Basic.normSq_eq_canonical ((cap.model.refine index).residual.eval point)).trans_le original
  exact readback.trans_le (converted.trans_eq (cap.model.refine_bound index))

/-- The retained physical coefficient residual decays at the actual sample's original refinement stage.

The fixed cache supplies the two original ceilings and their exact scale.
The same inverse, parity factor, square residual and differential residual
are used in the original coefficient identity and the scalar norm estimate.
-/
theorem physicalCoefficient_residual_le {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial} {index : Nat} {box : Box}
    (sample : PolynomialSample cap numerator index box) (bounds : ResidualBounds cap numerator)
    {point : Gaussian} (inside : collar.box.Contains point) :
    Norm.Basic.normSq
      (point * cap.polynomial.eval point * (Derivative.derivative sample.physicalCoefficient).eval point -
        half * (cap.polynomial.eval point + point * (Derivative.derivative cap.polynomial).eval point) *
          sample.physicalCoefficient.eval point - half * point * numerator.eval point * cap.polynomial.eval point) ≤
      quarterRadius bounds.scale index := by
  have numeratorBound : Norm.Basic.normSq (numerator.eval point) ≤ bounds.base.numeratorUpper :=
    (Bounds.Box.normSq_eval_le_denseEvalNormBound numerator inside).trans_eq bounds.base.numeratorUpper_eq.symm
  have scalar := Norm.Product.scaled_difference_quarter_le half point (cap.polynomial.eval point)
    (sample.shiftedFactor.eval point) (differentialResidual cap.polynomial sample.1.val.value point)
    (numerator.eval point) (sample.1.val.residual.eval point)
    collar.box.normSqBound (Bounds.Box.denseEvalNormBound cap.polynomial collar.box)
    (2 * collar.box.normSqBound * bounds.base.numeratorUpper * bounds.base.inverseUpper)
    bounds.differential.bound bounds.base.numeratorUpper cap.model.bound index
    (collar.box.normSq_le_normSqBound inside)
    (Bounds.Box.normSq_eval_le_denseEvalNormBound cap.polynomial inside)
    (sample.shiftedFactor_le bounds.base inside) (sample_differential_le sample bounds inside)
    numeratorBound (sample_residual_le sample inside)
  have identity := congrArg Norm.Basic.normSq (sample.physicalCoefficient_residual point)
  have scaleReadback := congrArg (fun value : Coordinate => quarterRadius value index) bounds.scale_eq.symm
  exact (identity.trans_le scalar).trans_eq scaleReadback

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.PolynomialSample

end
