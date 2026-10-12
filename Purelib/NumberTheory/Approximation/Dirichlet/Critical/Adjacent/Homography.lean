module

public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Adjacent.Tower
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.DenominatorPerturbation
public import Purelib.NumberTheory.Approximation.Best.Error.Homography
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Stability
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Pair.Matrix
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.NumberTheory.Approximation.Best.Cylinder.Basis
import Purelib.NumberTheory.Approximation.Best.Cylinder.Stability
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Parameter
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Pair
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Transition
import Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound
import Purelib.Tactic.Ring

/-!
# Homographic images of transported critical bases

An integral determinant-one homography retains the normalized error
coordinate. Its denominator coordinate acquires one explicit Gaussian
rational perturbation. The finite denominator clearance certifies the
complete consecutive-best window for the same transported pair owners.
-/

public section

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.GaussianInt.Pair.Basic
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2
open Purelib.NumberTheory.Approximation
open Purelib.NumberTheory.Approximation.Dirichlet.Critical

/-- The homographic source denominator times the retained target upper denominator. -/
@[expose] def homographicDenominatorFactor
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (_normal : TransportedNormalForm source errorStage targetStage)
    (matrix : Matrix GaussianInt) : Gaussian.Basic.Canonical :=
  Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value *
    GaussianInt.toGaussian (Pair.criticalUpperPair targetStage).denominator

/-- The exact normalized denominator correction supplied by the retained lower error. -/
@[expose] def homographicPerturbation
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (matrix : Matrix GaussianInt) : Gaussian.Basic.Canonical :=
  GaussianInt.toGaussian matrix.c * normal.lowerError *
    Gaussian.Field.inv (normal.homographicDenominatorFactor matrix)

/-- Avoiding the source pole makes the retained denominator factor nonzero. -/
theorem homographicDenominatorFactor_ne_zero
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (matrix : Matrix GaussianInt)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value ≠ 0) :
    normal.homographicDenominatorFactor matrix ≠ 0 := by
  apply Gaussian.Field.mul_ne_zero_direct poleExcluded
  intro zero
  exact Pair.criticalUpper_denominator_ne_zero targetStage (GaussianInt.toGaussian_eq_zero.mp zero)

/-- Paying the exact denominator factor recovers the retained lower-error correction. -/
private theorem factor_mul_perturbation
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (matrix : Matrix GaussianInt)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value ≠ 0) :
    normal.homographicDenominatorFactor matrix * normal.homographicPerturbation matrix =
      GaussianInt.toGaussian matrix.c * normal.lowerError := by
  rewrite [Gaussian.Basic.mul_comm, homographicPerturbation, Gaussian.Basic.mul_assoc,
    Gaussian.Field.inv_mul _ (normal.homographicDenominatorFactor_ne_zero matrix poleExcluded),
    Gaussian.Basic.mul_one]
  rfl

/-- Paying the actual affine and upper-denominator quadrances recovers the squared correction numerator. -/
theorem homographicPerturbation_mul_denominator_normSq
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (matrix : Matrix GaussianInt)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value ≠ 0) :
    Gaussian.Norm.Basic.normSq (normal.homographicPerturbation matrix) *
        (Gaussian.Norm.Basic.normSq
          (Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value) *
          Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (Pair.criticalUpperPair targetStage).denominator)) =
      Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian matrix.c) * Gaussian.Norm.Basic.normSq normal.lowerError := by
  have paid := congrArg Gaussian.Norm.Basic.normSq (normal.factor_mul_perturbation matrix poleExcluded)
  rewrite [Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul,
    homographicDenominatorFactor, Gaussian.Norm.Basic.normSq_mul] at paid
  calc
    _ = (Gaussian.Norm.Basic.normSq
          (Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value) *
          Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (Pair.criticalUpperPair targetStage).denominator)) *
        Gaussian.Norm.Basic.normSq (normal.homographicPerturbation matrix) := by ring1
    _ = _ := paid

/-- Compute the affine-denominator quadrance sufficient to pay one normalized perturbation request. -/
def homographicPerturbationDenominatorBound
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (lowerLeftCoefficient : GaussianInt) (perturbationBudget : Fraction.Rational) : Fraction.Rational :=
  Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian lowerLeftCoefficient) *
    Gaussian.Norm.Basic.normSq normal.lowerError /
      (Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (Pair.criticalUpperPair targetStage).denominator) *
        perturbationBudget)

/-- A positive perturbation request produces a nonnegative affine-denominator bound. -/
theorem homographicPerturbationDenominatorBound_nonneg
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (lowerLeftCoefficient : GaussianInt) {perturbationBudget : Fraction.Rational}
    (positive : 0 < perturbationBudget) :
    0 ≤ normal.homographicPerturbationDenominatorBound lowerLeftCoefficient perturbationBudget := by
  apply Fraction.Order.Field.div_nonneg_direct
  · exact Fraction.Order.Arithmetic.mul_nonneg_direct
      (Gaussian.Norm.Basic.normSq_nonneg _) normal.lowerErrorPositive.le
  · exact Fraction.Order.Arithmetic.mul_nonneg_direct (Gaussian.Norm.Basic.normSq_nonneg _) positive.le

/-- Exceeding the computed affine-denominator bound pays the actual normalized homographic perturbation budget. -/
theorem homographicPerturbation_normSq_lt_of_denominator_gt
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (matrix : Matrix GaussianInt)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value ≠ 0)
    {perturbationBudget : Fraction.Rational} (positive : 0 < perturbationBudget)
    (denominatorLarge : normal.homographicPerturbationDenominatorBound matrix.c perturbationBudget <
      Gaussian.Norm.Basic.normSq
        (Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value)) :
    Gaussian.Norm.Basic.normSq (normal.homographicPerturbation matrix) < perturbationBudget := by
  let upperNorm := Gaussian.Norm.Basic.normSq
    (GaussianInt.toGaussian (Pair.criticalUpperPair targetStage).denominator)
  let denominatorNorm := Gaussian.Norm.Basic.normSq
    (Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value)
  have upperNonzero : GaussianInt.toGaussian (Pair.criticalUpperPair targetStage).denominator ≠ 0 := by
    intro zero
    exact Pair.criticalUpper_denominator_ne_zero targetStage (GaussianInt.toGaussian_eq_zero.mp zero)
  have upperPositive : 0 < upperNorm := Gaussian.Norm.Basic.normSq_pos upperNonzero
  have denominatorPositive : 0 < denominatorNorm := Gaussian.Norm.Basic.normSq_pos poleExcluded
  have scaled := (Fraction.Order.Field.div_lt_iff_pos
    (Fraction.Order.Arithmetic.mul_pos_direct upperPositive positive)).mp denominatorLarge
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := denominatorNorm * upperNorm) _
    (Fraction.Order.Arithmetic.mul_pos_direct denominatorPositive upperPositive)
  calc
    Gaussian.Norm.Basic.normSq (normal.homographicPerturbation matrix) * (denominatorNorm * upperNorm) =
        Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian matrix.c) *
          Gaussian.Norm.Basic.normSq normal.lowerError :=
      normal.homographicPerturbation_mul_denominator_normSq matrix poleExcluded
    _ < denominatorNorm * (upperNorm * perturbationBudget) := scaled
    _ = perturbationBudget * (denominatorNorm * upperNorm) := by ring1

/-- The transported lower denominator factors through its original normalized ratio and the exact correction. -/
theorem homographic_lower_denominator
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (matrix : Matrix GaussianInt)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value ≠ 0) :
    GaussianInt.toGaussian ((Pair.criticalLowerPair targetStage).transform matrix).denominator =
      normal.homographicDenominatorFactor matrix *
        (Cylinder.TwoParameter.denominatorRatio (Parameter.pellParameter targetStage) -
          normal.homographicPerturbation matrix) := by
  rewrite [Best.Error.denominator_transform matrix source.value,
    target_denominator_lower, normal.lowerIdentity]
  calc
    Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value *
          (GaussianInt.toGaussian (Pair.criticalUpperPair targetStage).denominator *
            Cylinder.TwoParameter.denominatorRatio (Parameter.pellParameter targetStage)) -
        GaussianInt.toGaussian matrix.c * normal.lowerError =
      normal.homographicDenominatorFactor matrix *
          Cylinder.TwoParameter.denominatorRatio (Parameter.pellParameter targetStage) -
        GaussianInt.toGaussian matrix.c * normal.lowerError := by
      unfold homographicDenominatorFactor
      rewrite [Gaussian.Basic.mul_assoc]
      rfl
    _ = normal.homographicDenominatorFactor matrix *
          Cylinder.TwoParameter.denominatorRatio (Parameter.pellParameter targetStage) -
        normal.homographicDenominatorFactor matrix * normal.homographicPerturbation matrix := by
      rewrite [normal.factor_mul_perturbation matrix poleExcluded]
      rfl
    _ = _ := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- The transported upper denominator factors through one minus the error-ratio correction. -/
theorem homographic_upper_denominator
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (matrix : Matrix GaussianInt)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value ≠ 0) :
    GaussianInt.toGaussian ((Pair.criticalUpperPair targetStage).transform matrix).denominator =
      normal.homographicDenominatorFactor matrix *
        (1 - normal.homographicPerturbation matrix *
          Cylinder.TwoParameter.errorRatio (Parameter.pellParameter errorStage)) := by
  rewrite [Best.Error.denominator_transform matrix source.value, normal.upperIdentity]
  calc
    Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value *
          GaussianInt.toGaussian (Pair.criticalUpperPair targetStage).denominator -
        GaussianInt.toGaussian matrix.c *
          (normal.lowerError * Cylinder.TwoParameter.errorRatio (Parameter.pellParameter errorStage)) =
      normal.homographicDenominatorFactor matrix -
        (GaussianInt.toGaussian matrix.c * normal.lowerError) *
          Cylinder.TwoParameter.errorRatio (Parameter.pellParameter errorStage) := by
      unfold homographicDenominatorFactor
      rewrite [Gaussian.Basic.mul_assoc]
      rfl
    _ = normal.homographicDenominatorFactor matrix -
        (normal.homographicDenominatorFactor matrix * normal.homographicPerturbation matrix) *
          Cylinder.TwoParameter.errorRatio (Parameter.pellParameter errorStage) := by
      rewrite [normal.factor_mul_perturbation matrix poleExcluded]
      rfl
    _ = _ := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Basic.one_re, Gaussian.Basic.one_im] <;> ring1

/-- The transported upper denominator quadrance retains the exact affine factor, original quadrance and correction. -/
theorem homographic_upperDenominatorQuadrance
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (matrix : Matrix GaussianInt)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value ≠ 0) :
    (Best.Error.denominatorQuadrance ((Pair.criticalUpperPair targetStage).transform matrix) : Fraction.Rational) =
      Gaussian.Norm.Basic.normSq
          (Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value) *
        Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (Pair.criticalUpperPair targetStage).denominator) *
        Gaussian.Norm.Basic.normSq (1 - normal.homographicPerturbation matrix *
          Cylinder.TwoParameter.errorRatio (Parameter.pellParameter errorStage)) := by
  change (GaussianInt.normNat ((Pair.criticalUpperPair targetStage).transform matrix).denominator :
    Fraction.Rational) = _
  rewrite [← GaussianInt.normSq_toGaussian,
    normal.homographic_upper_denominator matrix poleExcluded, Gaussian.Norm.Basic.normSq_mul,
    homographicDenominatorFactor, Gaussian.Norm.Basic.normSq_mul]
  rfl

/-- Compute the affine-denominator quadrance sufficient to exceed a prescribed natural upper-denominator scale.

The original requested scale has a direct integer-backed rational reading,
so large earlier window scales do not require repeated rational additions. -/
def homographicScaleDenominatorBound
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (_normal : TransportedNormalForm source errorStage targetStage)
    (requestedScale : Nat) : Fraction.Rational :=
  Fraction.Cast.fromInt (requestedScale : Int) /
    (Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (Pair.criticalUpperPair targetStage).denominator) * (3 / 8))

/-- The direct scale payment equals the expression using the original requested natural cast. -/
theorem homographicScaleDenominatorBound_eq_cast
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage) (requestedScale : Nat) :
    normal.homographicScaleDenominatorBound requestedScale =
      (requestedScale : Fraction.Rational) /
        (Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian (Pair.criticalUpperPair targetStage).denominator) * (3 / 8)) :=
  congrArg (fun scale => scale /
    (Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (Pair.criticalUpperPair targetStage).denominator) * (3 / 8)))
    (Fraction.Cast.natCast_eq_fromInt requestedScale).symm

/-- The scale payment is nonnegative for every requested natural scale. -/
theorem homographicScaleDenominatorBound_nonneg
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage) (requestedScale : Nat) :
    0 ≤ normal.homographicScaleDenominatorBound requestedScale := by
  rewrite [normal.homographicScaleDenominatorBound_eq_cast]
  apply Fraction.Order.Field.div_nonneg_direct
  · exact Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  · exact Fraction.Order.Arithmetic.mul_nonneg_direct (Gaussian.Norm.Basic.normSq_nonneg _) (by decide)

/-- Exceeding the scale payment places the transformed upper pair beyond the requested natural scale.

The finite cylinder budget bounds the normalized upper-denominator
quadrance below by three eighths. The actual affine denominator pays the
remaining original denominator factor and the requested scale.
-/
theorem homographic_beyondScale
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (matrix : Matrix GaussianInt)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value ≠ 0)
    (small : Gaussian.Norm.Basic.normSq (normal.homographicPerturbation matrix) <
      Cylinder.TwoParameter.denominatorPerturbationDistanceSq
        (Parameter.pellParameter errorStage) (Parameter.pellParameter targetStage))
    (requestedScale : Nat)
    (denominatorLarge : normal.homographicScaleDenominatorBound requestedScale <
      Gaussian.Norm.Basic.normSq
        (Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value)) :
    requestedScale < Best.Error.denominatorQuadrance ((Pair.criticalUpperPair targetStage).transform matrix) := by
  rewrite [normal.homographicScaleDenominatorBound_eq_cast] at denominatorLarge
  let upperNorm := Gaussian.Norm.Basic.normSq
    (GaussianInt.toGaussian (Pair.criticalUpperPair targetStage).denominator)
  let denominatorNorm := Gaussian.Norm.Basic.normSq
    (Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value)
  have upperNonzero : GaussianInt.toGaussian (Pair.criticalUpperPair targetStage).denominator ≠ 0 := by
    intro zero
    exact Pair.criticalUpper_denominator_ne_zero targetStage (GaussianInt.toGaussian_eq_zero.mp zero)
  have upperPositive : 0 < upperNorm := Gaussian.Norm.Basic.normSq_pos upperNonzero
  have denominatorPositive : 0 < denominatorNorm := Gaussian.Norm.Basic.normSq_pos poleExcluded
  have scaled := (Fraction.Order.Field.div_lt_iff_pos
    (Fraction.Order.Arithmetic.mul_pos_direct upperPositive (by decide : (0 : Fraction.Rational) < 3 / 8))).mp
      denominatorLarge
  have correctionBound := Cylinder.TwoParameter.threeEighths_le_perturbed_upper_normSq
    (Parameter.pellParameter_isCritical errorStage)
    ((small.trans_le (Cylinder.TwoParameter.denominatorPerturbationDistanceSq_le_oneEighth _ _)).le)
  apply Fraction.Cast.Order.natCast_lt_iff_direct.mp
  calc
    (requestedScale : Fraction.Rational) < denominatorNorm * (upperNorm * (3 / 8)) := scaled
    _ = (denominatorNorm * upperNorm) * (3 / 8) := by ring1
    _ ≤ (denominatorNorm * upperNorm) *
        Gaussian.Norm.Basic.normSq (1 - normal.homographicPerturbation matrix *
          Cylinder.TwoParameter.errorRatio (Parameter.pellParameter errorStage)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct correctionBound
        (Fraction.Order.Arithmetic.mul_nonneg_direct denominatorPositive.le upperPositive.le)
    _ = (Best.Error.denominatorQuadrance ((Pair.criticalUpperPair targetStage).transform matrix) :
        Fraction.Rational) := (normal.homographic_upperDenominatorQuadrance matrix poleExcluded).symm

/-- Every transported coefficient combination uses the same retained denominator factor and correction. -/
theorem homographic_combination_denominator
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (matrix : Matrix GaussianInt)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value ≠ 0)
    (left right : GaussianInt) :
    GaussianInt.toGaussian
        ((GaussianInt.Pair.LinearCombination.linearCombination
          (Pair.criticalLowerPair targetStage) (Pair.criticalUpperPair targetStage) left right).transform
            matrix).denominator =
      normal.homographicDenominatorFactor matrix *
        Cylinder.TwoParameter.perturbedNormalizedDenominator
          (Parameter.pellParameter errorStage) (Parameter.pellParameter targetStage)
          (normal.homographicPerturbation matrix) left right := by
  rewrite [Best.Error.denominator_transform matrix source.value,
    target_denominator_linearCombination, normal.error_linearCombination]
  calc
    Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value *
          (GaussianInt.toGaussian (Pair.criticalUpperPair targetStage).denominator *
            Cylinder.TwoParameter.normalizedDenominator (Parameter.pellParameter targetStage) left right) -
        GaussianInt.toGaussian matrix.c *
          (normal.lowerError *
            Cylinder.TwoParameter.normalizedError (Parameter.pellParameter errorStage) left right) =
      normal.homographicDenominatorFactor matrix *
          Cylinder.TwoParameter.normalizedDenominator (Parameter.pellParameter targetStage) left right -
        (GaussianInt.toGaussian matrix.c * normal.lowerError) *
          Cylinder.TwoParameter.normalizedError (Parameter.pellParameter errorStage) left right := by
      unfold homographicDenominatorFactor
      rewrite [Gaussian.Basic.mul_assoc, Gaussian.Basic.mul_assoc]
      rfl
    _ = normal.homographicDenominatorFactor matrix *
          Cylinder.TwoParameter.normalizedDenominator (Parameter.pellParameter targetStage) left right -
        (normal.homographicDenominatorFactor matrix * normal.homographicPerturbation matrix) *
          Cylinder.TwoParameter.normalizedError (Parameter.pellParameter errorStage) left right := by
      rewrite [normal.factor_mul_perturbation matrix poleExcluded]
      rfl
    _ = _ := by
      unfold Cylinder.TwoParameter.perturbedNormalizedDenominator
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- The homographic window quadrance is the original quadrance times the exact normalized upper-denominator factor. -/
theorem homographic_windowQuadrance
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (matrix : Matrix GaussianInt) (unitDeterminant : matrix.determinant = 1)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value ≠ 0) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance
        (Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix) source.value)
        ((Pair.criticalLowerPair targetStage).transform matrix)
        ((Pair.criticalUpperPair targetStage).transform matrix) =
      Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value
          (Pair.criticalLowerPair targetStage) (Pair.criticalUpperPair targetStage) *
        Gaussian.Norm.Basic.normSq (1 - normal.homographicPerturbation matrix *
          Cylinder.TwoParameter.errorRatio (Parameter.pellParameter errorStage)) := by
  let denominator := Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value
  let correction := 1 - normal.homographicPerturbation matrix *
    Cylinder.TwoParameter.errorRatio (Parameter.pellParameter errorStage)
  have paid := Best.Error.errorQuadrance_transform_of_determinant_one matrix unitDeterminant source.value
    (Pair.criticalLowerPair targetStage) poleExcluded
  have upperNorm :
      (Best.Error.denominatorQuadrance ((Pair.criticalUpperPair targetStage).transform matrix) :
        Fraction.Rational) =
        Gaussian.Norm.Basic.normSq denominator *
          (Best.Error.denominatorQuadrance (Pair.criticalUpperPair targetStage) : Fraction.Rational) *
          Gaussian.Norm.Basic.normSq correction := by
    have exact := normal.homographic_upperDenominatorQuadrance matrix poleExcluded
    rewrite [GaussianInt.normSq_toGaussian] at exact
    exact exact
  rewrite [Dirichlet.Window.SourceBound.dirichletWindowQuadrance_eq_cast,
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance_eq_cast]
  apply Fraction.Field.mul_right_cancel_of_ne (Gaussian.Norm.Basic.normSq_pos poleExcluded).ne'
  calc
    ((Best.Error.denominatorQuadrance ((Pair.criticalUpperPair targetStage).transform matrix) :
          Fraction.Rational) *
        Best.Error.errorQuadrance
          (Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix) source.value)
          ((Pair.criticalLowerPair targetStage).transform matrix)) * Gaussian.Norm.Basic.normSq denominator =
      (Best.Error.denominatorQuadrance ((Pair.criticalUpperPair targetStage).transform matrix) :
          Fraction.Rational) *
        (Best.Error.errorQuadrance
          (Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix) source.value)
          ((Pair.criticalLowerPair targetStage).transform matrix) * Gaussian.Norm.Basic.normSq denominator) :=
      by ring1
    _ = (Best.Error.denominatorQuadrance ((Pair.criticalUpperPair targetStage).transform matrix) :
        Fraction.Rational) * Best.Error.errorQuadrance source.value (Pair.criticalLowerPair targetStage) := by
      rewrite [paid]
      rfl
    _ = (Gaussian.Norm.Basic.normSq denominator *
        (Best.Error.denominatorQuadrance (Pair.criticalUpperPair targetStage) : Fraction.Rational) *
          Gaussian.Norm.Basic.normSq correction) *
        Best.Error.errorQuadrance source.value (Pair.criticalLowerPair targetStage) := by
      rewrite [upperNorm]
      rfl
    _ = _ := by ring1

/-- A denominator correction of quadrance at most one eighth bounds the transformed window quadrance by nine halves. -/
theorem homographic_windowQuadrance_le_nineHalves
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (matrix : Matrix GaussianInt) (unitDeterminant : matrix.determinant = 1)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value ≠ 0)
    (small : Gaussian.Norm.Basic.normSq (normal.homographicPerturbation matrix) ≤ 1 / 8) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance
      (Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix) source.value)
      ((Pair.criticalLowerPair targetStage).transform matrix)
      ((Pair.criticalUpperPair targetStage).transform matrix) ≤ 9 / 2 := by
  rewrite [normal.homographic_windowQuadrance matrix unitDeterminant poleExcluded]
  calc
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value
        (Pair.criticalLowerPair targetStage) (Pair.criticalUpperPair targetStage) *
        Gaussian.Norm.Basic.normSq (1 - normal.homographicPerturbation matrix *
          Cylinder.TwoParameter.errorRatio (Parameter.pellParameter errorStage)) ≤
      2 * Gaussian.Norm.Basic.normSq (1 - normal.homographicPerturbation matrix *
        Cylinder.TwoParameter.errorRatio (Parameter.pellParameter errorStage)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct normal.windowQuadrance_lt_two.le
        (Gaussian.Norm.Basic.normSq_nonneg _)
    _ ≤ 2 * (9 / 4) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Cylinder.TwoParameter.perturbed_upper_normSq_le (Parameter.pellParameter_isCritical errorStage) small)
      (by decide)
    _ = 9 / 2 := by decide

/-- Compute the exact source neighbourhood preserving a homographically transported critical cylinder. -/
def homographicExteriorDistanceSq
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (_normal : TransportedNormalForm source errorStage targetStage)
    (matrix : Matrix GaussianInt) : Fraction.Rational :=
  let value := Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix) source.value
  let lower := (Pair.criticalLowerPair targetStage).transform matrix
  let upper := (Pair.criticalUpperPair targetStage).transform matrix
  Best.Cylinder.Stability.exteriorDistanceSq value lower upper

/-- Compute a perturbation budget retaining one strict threshold violation of the original window. -/
def homographicViolationDistanceSq
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (_normal : TransportedNormalForm source errorStage targetStage)
    (threshold : Fraction.Rational) : Fraction.Rational :=
  let payment := threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value
    (Pair.criticalLowerPair targetStage) (Pair.criticalUpperPair targetStage)
  Gaussian.Norm.Stability.perturbationDistanceSq 1 ((payment - 1) / (2 * payment))

/-- A strict original threshold violation makes the computed homographic budget positive. -/
theorem homographicViolationDistanceSq_pos
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    {threshold : Fraction.Rational}
    (violates : 1 < threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value
      (Pair.criticalLowerPair targetStage) (Pair.criticalUpperPair targetStage)) :
    0 < normal.homographicViolationDistanceSq threshold := by
  apply Gaussian.Norm.Stability.perturbationDistanceSq_pos
  exact Fraction.Order.Field.div_pos_direct (Fraction.Order.Arithmetic.sub_pos_direct violates)
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      ((by decide : (0 : Fraction.Rational) < 1).trans violates))

/-- The explicit violation budget preserves the strict sharpness inequality for the homographic image. -/
theorem homographic_violates
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (matrix : Matrix GaussianInt) (unitDeterminant : matrix.determinant = 1)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value ≠ 0)
    {threshold : Fraction.Rational}
    (violates : 1 < threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value
      (Pair.criticalLowerPair targetStage) (Pair.criticalUpperPair targetStage))
    (small : Gaussian.Norm.Basic.normSq (normal.homographicPerturbation matrix) <
      normal.homographicViolationDistanceSq threshold) :
    1 < threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance
      (Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix) source.value)
      ((Pair.criticalLowerPair targetStage).transform matrix)
      ((Pair.criticalUpperPair targetStage).transform matrix) := by
  let payment := threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value
    (Pair.criticalLowerPair targetStage) (Pair.criticalUpperPair targetStage)
  let margin := (payment - 1) / (2 * payment)
  let perturbation := normal.homographicPerturbation matrix
  let ratio := Cylinder.TwoParameter.errorRatio (Parameter.pellParameter errorStage)
  have paymentPositive : 0 < payment := (by decide : (0 : Fraction.Rational) < 1).trans violates
  have denominatorPositive : 0 < 2 * payment :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) paymentPositive
  have marginPositive : 0 < margin := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.sub_pos_direct violates) denominatorPositive
  have displacementSmall : Gaussian.Norm.Basic.normSq (-(perturbation * ratio)) <
      Gaussian.Norm.Stability.perturbationDistanceSq 1 margin := by
    rewrite [Gaussian.Norm.Basic.normSq_neg, Gaussian.Norm.Basic.normSq_mul]
    calc
      Gaussian.Norm.Basic.normSq perturbation * Gaussian.Norm.Basic.normSq ratio ≤
          Gaussian.Norm.Basic.normSq perturbation * 1 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Cylinder.TwoParameter.normSq_errorRatio_lt_one (Parameter.pellParameter_isCritical errorStage)).le
          (Gaussian.Norm.Basic.normSq_nonneg perturbation)
      _ = Gaussian.Norm.Basic.normSq perturbation := Fraction.Field.mul_one_direct _
      _ < Gaussian.Norm.Stability.perturbationDistanceSq 1 margin := small
  have correctionIdentity : 1 + -(perturbation * ratio) = 1 - perturbation * ratio := by
    exact (Gaussian.Basic.sub_eq_add_neg _ _).symm
  have normBound := Gaussian.Norm.Stability.normSq_lt_add_of_distance marginPositive displacementSmall
  rewrite [Gaussian.Norm.Basic.normSq_one, correctionIdentity] at normBound
  have marginPaid : margin * (2 * payment) = payment - 1 :=
    Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'
  have baseline : 1 < payment - payment * margin := by
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := (2 : Fraction.Rational)) _ (by decide)
    calc
      (1 : Fraction.Rational) * 2 = 1 + 1 := by ring1
      _ < payment + 1 := Fraction.Order.Arithmetic.add_lt_add_right_direct violates _
      _ = 2 * payment - (payment - 1) := by ring1
      _ = 2 * payment - margin * (2 * payment) := by
        rewrite [marginPaid]
        rfl
      _ = (payment - payment * margin) * 2 := by ring1
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct paymentPositive normBound
  have translated := Fraction.Order.Arithmetic.sub_lt_sub_right_direct scaled (payment * margin)
  rewrite [normal.homographic_windowQuadrance matrix unitDeterminant poleExcluded]
  calc
    1 < payment - payment * margin := baseline
    _ = payment * 1 - payment * margin := by ring1
    _ < payment * (Gaussian.Norm.Basic.normSq (1 - perturbation * ratio) + margin) - payment * margin := translated
    _ = payment * Gaussian.Norm.Basic.normSq (1 - perturbation * ratio) := by ring1
    _ = _ := by
      dsimp only [payment, perturbation, ratio]
      ring1

/-- The explicit perturbation clearance preserves the complete strict-exterior certificate under integral homography.

The same matrix acts on the source and on each complete pair. The source
must avoid its affine pole, the matrix determinant must be one, and the
computed denominator correction must lie inside the finite rational budget.
-/
theorem homographic_strictExteriorCertificate
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (matrix : Matrix GaussianInt) (unitDeterminant : matrix.determinant = 1)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value ≠ 0)
    (small : Gaussian.Norm.Basic.normSq (normal.homographicPerturbation matrix) <
      Cylinder.TwoParameter.denominatorPerturbationDistanceSq
        (Parameter.pellParameter errorStage) (Parameter.pellParameter targetStage)) :
    Best.Cylinder.Basis.StrictExteriorCertificate
      (Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix) source.value)
      ((Pair.criticalLowerPair targetStage).transform matrix)
      ((Pair.criticalUpperPair targetStage).transform matrix) := by
  let factor := normal.homographicDenominatorFactor matrix
  have factorNonzero : factor ≠ 0 := normal.homographicDenominatorFactor_ne_zero matrix poleExcluded
  have factorPositive : 0 < Gaussian.Norm.Basic.normSq factor := Gaussian.Norm.Basic.normSq_pos factorNonzero
  have errorCertificate := Parameter.pellParameter_isCritical errorStage
  have denominatorCertificate := Parameter.pellParameter_isCritical targetStage
  have lowerNonzero : ((Pair.criticalLowerPair targetStage).transform matrix).denominator ≠ 0 := by
    intro zero
    have embedded := congrArg GaussianInt.toGaussian zero
    rewrite [normal.homographic_lower_denominator matrix poleExcluded, GaussianInt.toGaussian_zero] at embedded
    exact (Gaussian.Field.mul_ne_zero_direct factorNonzero
      (Cylinder.TwoParameter.perturbedLowerDenominator_ne_zero small)) embedded
  have upperNonzero : ((Pair.criticalUpperPair targetStage).transform matrix).denominator ≠ 0 := by
    intro zero
    have embedded := congrArg GaussianInt.toGaussian zero
    rewrite [normal.homographic_upper_denominator matrix poleExcluded, GaussianInt.toGaussian_zero] at embedded
    exact (Gaussian.Field.mul_ne_zero_direct factorNonzero
      (Cylinder.TwoParameter.perturbedUpperDenominator_ne_zero errorCertificate denominatorCertificate small)) embedded
  refine
    { indexOne := ?_
      lowerDenominatorNonzero := lowerNonzero
      upperDenominatorNonzero := upperNonzero
      errorOrder := Best.Error.errorQuadrance_lt_transform matrix unitDeterminant source.value
        (Pair.criticalLowerPair targetStage) (Pair.criticalUpperPair targetStage) poleExcluded
        normal.strictExteriorCertificate.errorOrder
      denominatorOrder := ?_
      bothNonzeroExterior := ?_ }
  · rewrite [ConvergentPair.coefficientIndexQuadrance_transform, unitDeterminant,
      show GaussianInt.normNat (1 : GaussianInt) = 1 by decide, Nat.one_mul]
    exact Pair.criticalPair_indexOne targetStage
  · apply Fraction.Cast.Order.natCast_lt_iff_direct.mp
    have ordered := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct factorPositive
      (Cylinder.TwoParameter.denominatorOrder_of_perturbation errorCertificate denominatorCertificate small)
    change (GaussianInt.normNat ((Pair.criticalLowerPair targetStage).transform matrix).denominator :
      Fraction.Rational) <
      (GaussianInt.normNat ((Pair.criticalUpperPair targetStage).transform matrix).denominator : Fraction.Rational)
    rewrite [← GaussianInt.normSq_toGaussian, ← GaussianInt.normSq_toGaussian,
      normal.homographic_lower_denominator matrix poleExcluded,
      normal.homographic_upper_denominator matrix poleExcluded,
      Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul]
    exact ordered
  · intro left right leftNonzero rightNonzero
    rcases Cylinder.TwoParameter.strictExterior_of_denominator_perturbation
        errorCertificate denominatorCertificate small left right leftNonzero rightNonzero with
      errorExterior | denominatorExterior
    · left
      have originalErrorExterior : Best.Error.errorQuadrance source.value (Pair.criticalLowerPair targetStage) <
          Best.Error.errorQuadrance source.value
            (GaussianInt.Pair.LinearCombination.linearCombination
              (Pair.criticalLowerPair targetStage) (Pair.criticalUpperPair targetStage) left right) := by
        have ordered := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct normal.lowerErrorPositive
          errorExterior
        unfold Best.Error.errorQuadrance
        rewrite [normal.lowerIdentity, normal.error_linearCombination, Gaussian.Norm.Basic.normSq_mul]
        rewrite [Fraction.Field.mul_one_direct] at ordered
        exact ordered
      have transported := Best.Error.errorQuadrance_lt_transform matrix unitDeterminant source.value
        (GaussianInt.Pair.LinearCombination.linearCombination
          (Pair.criticalLowerPair targetStage) (Pair.criticalUpperPair targetStage) left right)
        (Pair.criticalLowerPair targetStage)
        poleExcluded originalErrorExterior
      rewrite [ConvergentPair.transform_linearCombination] at transported
      exact transported
    · right
      apply Fraction.Cast.Order.natCast_lt_iff_direct.mp
      have ordered := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct factorPositive denominatorExterior
      change (GaussianInt.normNat ((Pair.criticalUpperPair targetStage).transform matrix).denominator :
        Fraction.Rational) <
        (GaussianInt.normNat
          (GaussianInt.Pair.LinearCombination.linearCombination
            ((Pair.criticalLowerPair targetStage).transform matrix)
            ((Pair.criticalUpperPair targetStage).transform matrix) left right).denominator : Fraction.Rational)
      rewrite [← GaussianInt.normSq_toGaussian, ← GaussianInt.normSq_toGaussian,
        ← ConvergentPair.transform_linearCombination,
        normal.homographic_upper_denominator matrix poleExcluded,
        normal.homographic_combination_denominator matrix poleExcluded,
        Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul]
      exact ordered

/-- One shared homography preserves the upper-denominator ordering of two ordered critical target stages.

Original upper quadrances grow by more than a factor of nine. Each retained
denominator correction has normalized quadrance between three eighths
and nine quarters, so the same affine factor preserves strict ordering.
-/
theorem homographic_upperQuadrance_ordered
    {source : GaussianInt.Fraction} {firstError firstTarget secondError secondTarget : Nat}
    (first : TransportedNormalForm source firstError firstTarget)
    (second : TransportedNormalForm source secondError secondTarget)
    (matrix : Matrix GaussianInt)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value ≠ 0)
    (firstSmall : Gaussian.Norm.Basic.normSq (first.homographicPerturbation matrix) ≤ 1 / 8)
    (secondSmall : Gaussian.Norm.Basic.normSq (second.homographicPerturbation matrix) ≤ 1 / 8)
    (stageOrder : firstTarget < secondTarget) :
    Best.Error.denominatorQuadrance ((Pair.criticalUpperPair firstTarget).transform matrix) <
      Best.Error.denominatorQuadrance ((Pair.criticalUpperPair secondTarget).transform matrix) := by
  let denominatorNorm := Gaussian.Norm.Basic.normSq
    (Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value)
  let firstQuadrance : Fraction.Rational := Best.Error.denominatorQuadrance (Pair.criticalUpperPair firstTarget)
  let secondQuadrance : Fraction.Rational := Best.Error.denominatorQuadrance (Pair.criticalUpperPair secondTarget)
  have denominatorPositive : 0 < denominatorNorm := Gaussian.Norm.Basic.normSq_pos poleExcluded
  have firstPositive : 0 < firstQuadrance := Fraction.Cast.Order.natCast_pos_direct
    (GaussianInt.normNat_pos (Pair.criticalUpper_denominator_ne_zero firstTarget))
  have factorPositive : 0 < denominatorNorm * firstQuadrance :=
    Fraction.Order.Arithmetic.mul_pos_direct denominatorPositive firstPositive
  have originalGrowth := Fraction.Cast.Order.natCast_lt_direct (Transition.nine_mul_upperQuadrance_lt_of_lt stageOrder)
  rewrite [Fraction.Cast.natCast_mul_direct] at originalGrowth
  change 9 * firstQuadrance < secondQuadrance at originalGrowth
  have firstIdentity := first.homographic_upperDenominatorQuadrance matrix poleExcluded
  have secondIdentity := second.homographic_upperDenominatorQuadrance matrix poleExcluded
  rewrite [GaussianInt.normSq_toGaussian] at firstIdentity secondIdentity
  have firstCorrection := Cylinder.TwoParameter.perturbed_upper_normSq_le
    (Parameter.pellParameter_isCritical firstError) firstSmall
  have secondCorrection := Cylinder.TwoParameter.threeEighths_le_perturbed_upper_normSq
    (Parameter.pellParameter_isCritical secondError) secondSmall
  apply Fraction.Cast.Order.natCast_lt_iff_direct.mp
  calc
    (Best.Error.denominatorQuadrance ((Pair.criticalUpperPair firstTarget).transform matrix) : Fraction.Rational) =
        (denominatorNorm * firstQuadrance) * Gaussian.Norm.Basic.normSq
          (1 - first.homographicPerturbation matrix *
            Cylinder.TwoParameter.errorRatio (Parameter.pellParameter firstError)) := firstIdentity
    _ ≤ (denominatorNorm * firstQuadrance) * (9 / 4) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct firstCorrection factorPositive.le
    _ < (denominatorNorm * firstQuadrance) * (27 / 8) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct factorPositive (by
        change (((9 : Nat) : Fraction.Rational) / ((4 : Nat) : Fraction.Rational)) <
          (((27 : Nat) : Fraction.Rational) / ((8 : Nat) : Fraction.Rational))
        rewrite [Fraction.Cast.natCast_eq_fromInt 9, Fraction.Cast.natCast_eq_fromInt 4,
          Fraction.Cast.natCast_eq_fromInt 27, Fraction.Cast.natCast_eq_fromInt 8]
        decide)
    _ = (denominatorNorm * (9 * firstQuadrance)) * (3 / 8) := by
      rewrite [show (27 / 8 : Fraction.Rational) = 9 * (3 / 8) by decide]
      ring1
    _ < (denominatorNorm * secondQuadrance) * (3 / 8) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
        (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct denominatorPositive originalGrowth) (by decide)
    _ ≤ (denominatorNorm * secondQuadrance) * Gaussian.Norm.Basic.normSq
        (1 - second.homographicPerturbation matrix *
          Cylinder.TwoParameter.errorRatio (Parameter.pellParameter secondError)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct secondCorrection
        (Fraction.Order.Arithmetic.mul_nonneg_direct denominatorPositive.le
          (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))
    _ = (Best.Error.denominatorQuadrance ((Pair.criticalUpperPair secondTarget).transform matrix) :
        Fraction.Rational) := secondIdentity.symm

/-- The homographic cylinder neighbourhood is positive under the computed denominator correction budget. -/
theorem homographicExteriorDistanceSq_pos
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (matrix : Matrix GaussianInt) (unitDeterminant : matrix.determinant = 1)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value ≠ 0)
    (small : Gaussian.Norm.Basic.normSq (normal.homographicPerturbation matrix) <
      Cylinder.TwoParameter.denominatorPerturbationDistanceSq
        (Parameter.pellParameter errorStage) (Parameter.pellParameter targetStage)) :
    0 < normal.homographicExteriorDistanceSq matrix :=
  Best.Cylinder.Stability.exteriorDistanceSq_pos
    (normal.homographic_strictExteriorCertificate matrix unitDeterminant poleExcluded small)

/-- Every source inside the computed homographic neighbourhood retains the complete transported cylinder certificate. -/
theorem homographic_strictExteriorCertificate_of_distance
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : TransportedNormalForm source errorStage targetStage)
    (matrix : Matrix GaussianInt) (unitDeterminant : matrix.determinant = 1)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source.value ≠ 0)
    (small : Gaussian.Norm.Basic.normSq (normal.homographicPerturbation matrix) <
      Cylinder.TwoParameter.denominatorPerturbationDistanceSq
        (Parameter.pellParameter errorStage) (Parameter.pellParameter targetStage))
    (sample : Gaussian.Basic.Canonical)
    (near : Gaussian.Norm.Basic.normSq
      (sample - Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix) source.value) <
        normal.homographicExteriorDistanceSq matrix) :
    Best.Cylinder.Basis.StrictExteriorCertificate sample
      ((Pair.criticalLowerPair targetStage).transform matrix)
      ((Pair.criticalUpperPair targetStage).transform matrix) := by
  have windowBound := normal.homographic_windowQuadrance_le_nineHalves matrix unitDeterminant poleExcluded
    ((small.trans_le (Cylinder.TwoParameter.denominatorPerturbationDistanceSq_le_oneEighth _ _)).le)
  rewrite [Dirichlet.Window.SourceBound.dirichletWindowQuadrance_eq_cast] at windowBound
  exact Best.Cylinder.Stability.strictExteriorCertificate_of_distance
    (normal.homographic_strictExteriorCertificate matrix unitDeterminant poleExcluded small)
    windowBound near

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm
