module

public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Run
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Adjacent.Homography
public import Purelib.Data.GaussianInt.Fraction.Homography
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.List.OfFn.Pairwise
import Purelib.Tactic.QuotientFreeOmega

/-!
# One shared homographic image of a finite critical run

The original run stages determine one source and one normal form at each
bounded offset. One integral matrix acts on every retained pair and on the
source once. The offset budgets preserve its complete consecutive-best
windows, strict threshold violations and ordered upper-denominator scales.
-/

public section

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.Run

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.GaussianInt.Pair.Basic
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2
open Purelib.NumberTheory.Approximation
open Purelib.NumberTheory.Approximation.Dirichlet.Critical

/-- Read the finite seed run's shared critical source before the homography pays the requested scale. -/
@[expose] def sourceAtCount (threshold : Fraction.Rational) (count : Nat) : GaussianInt.Fraction :=
  Pair.criticalSource (runSourceStage threshold 0 count)

/-- Retain the original transported normal form at one bounded run offset. -/
@[expose] def normalAtIndex (threshold : Fraction.Rational) (count : Nat) (offset : Fin count) :
    Adjacent.Tower.TransportedNormalForm (sourceAtCount threshold count)
      (runSourceStage threshold 0 count - offset.val)
      (runSourceStage threshold 0 count + offset.val) :=
  normalFormAtOffset threshold 0 count offset.val (Nat.le_of_lt offset.isLt)

/-- Compute the common denominator-correction budget preserving one offset's cylinder and threshold violation. -/
def homographicOffsetBudget (threshold : Fraction.Rational) (count : Nat) (offset : Fin count) :
    Fraction.Rational :=
  min (Cylinder.TwoParameter.denominatorPerturbationDistanceSq
    (Parameter.pellParameter (runSourceStage threshold 0 count - offset.val))
    (Parameter.pellParameter (runSourceStage threshold 0 count + offset.val)))
    ((normalAtIndex threshold count offset).homographicViolationDistanceSq threshold)

/-- Every offset of an original sharper-threshold run has a positive shared correction budget. -/
theorem homographicOffsetBudget_pos {threshold : Fraction.Rational}
    (certificate : Sharpness.IsSharperWindowThreshold threshold) (count : Nat) (offset : Fin count) :
    0 < homographicOffsetBudget threshold count offset := by
  let original := (badWindowAtOffset certificate 0 count offset).1
  exact Fraction.Order.Basic.lt_min
    (Cylinder.TwoParameter.denominatorPerturbationDistanceSq_pos
      (Parameter.pellParameter_isCritical _) (Parameter.pellParameter_isCritical _))
    ((normalAtIndex threshold count offset).homographicViolationDistanceSq_pos original.violates)

/-- A single offset budget pays its complete strict-cylinder correction. -/
theorem homographicOffsetBudget_le_cylinder (threshold : Fraction.Rational)
    (count : Nat) (offset : Fin count) :
    homographicOffsetBudget threshold count offset ≤
      Cylinder.TwoParameter.denominatorPerturbationDistanceSq
        (Parameter.pellParameter (runSourceStage threshold 0 count - offset.val))
        (Parameter.pellParameter (runSourceStage threshold 0 count + offset.val)) :=
  Fraction.Order.Basic.min_le_left _ _

/-- A single offset budget pays the original strict-threshold violation correction. -/
theorem homographicOffsetBudget_le_violation (threshold : Fraction.Rational)
    (count : Nat) (offset : Fin count) :
    homographicOffsetBudget threshold count offset ≤
      (normalAtIndex threshold count offset).homographicViolationDistanceSq threshold :=
  Fraction.Order.Basic.min_le_right _ _

/-- Construct one offset window using the exact shared transformed source supplied by its run builder. -/
@[expose] def homographicWindowAtOffset {threshold : Fraction.Rational}
    (certificate : Sharpness.IsSharperWindowThreshold threshold) (requestedScale count : Nat)
    (matrix : Matrix GaussianInt) (unitDeterminant : matrix.determinant = 1)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix)
      (sourceAtCount threshold count).value ≠ 0)
    (image : GaussianInt.Fraction)
    (imageValue : image.value = Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix)
      (sourceAtCount threshold count).value)
    (offset : Fin count)
    (small : Gaussian.Norm.Basic.normSq
      ((normalAtIndex threshold count offset).homographicPerturbation matrix) <
        homographicOffsetBudget threshold count offset)
    (scalePaid : (normalAtIndex threshold count offset).homographicScaleDenominatorBound requestedScale <
      Gaussian.Norm.Basic.normSq (Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix)
        (sourceAtCount threshold count).value)) :
    {window : Sharpness.BadWindow threshold requestedScale // window.source = image} := by
  let normal := normalAtIndex threshold count offset
  let original := (badWindowAtOffset certificate 0 count offset).1
  have cylinderSmall := small.trans_le (homographicOffsetBudget_le_cylinder threshold count offset)
  refine ⟨
    { source := image
      lower := (Pair.criticalLowerPair (runSourceStage threshold 0 count + offset.val)).transform matrix
      upper := (Pair.criticalUpperPair (runSourceStage threshold 0 count + offset.val)).transform matrix
      beyondScale := normal.homographic_beyondScale matrix poleExcluded cylinderSmall requestedScale scalePaid
      consecutive := ?_
      violates := ?_ }, rfl⟩
  · rewrite [imageValue]
    exact (normal.homographic_strictExteriorCertificate
      matrix unitDeterminant poleExcluded cylinderSmall).areConsecutiveBest
  · rewrite [imageValue]
    exact normal.homographic_violates matrix unitDeterminant poleExcluded original.violates
      (small.trans_le (homographicOffsetBudget_le_violation threshold count offset))

/-- Construct a full finite run using one shared exact source and one retained integral homography.

Every supplied offset budget pays the cylinder and violation corrections,
and the affine denominator separately pays the requested scale. The same
transformed fraction is passed to every window constructor and retained
without independent source encoding or repeated matrix selection.
-/
@[expose] def homographicBadWindowRun {threshold : Fraction.Rational}
    (certificate : Sharpness.IsSharperWindowThreshold threshold) (requestedScale count : Nat)
    (matrix : Matrix GaussianInt) (unitDeterminant : matrix.determinant = 1)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix)
      (sourceAtCount threshold count).value ≠ 0)
    (small : ∀ offset : Fin count, Gaussian.Norm.Basic.normSq
      ((normalAtIndex threshold count offset).homographicPerturbation matrix) <
        homographicOffsetBudget threshold count offset)
    (scalePaid : ∀ offset : Fin count,
      (normalAtIndex threshold count offset).homographicScaleDenominatorBound requestedScale <
        Gaussian.Norm.Basic.normSq (Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix)
          (sourceAtCount threshold count).value)) :
    SameSourceBadWindowRun threshold requestedScale count := by
  let originalSource := sourceAtCount threshold count
  let image := originalSource.transform matrix poleExcluded
  have imageValue := originalSource.transform_value matrix poleExcluded
  let windows := fun offset : Fin count => homographicWindowAtOffset certificate requestedScale count
    matrix unitDeterminant poleExcluded image imageValue offset (small offset) (scalePaid offset)
  refine
    { source := image
      windows := List.ofFn windows
      length_eq := Purelib.Data.List.OfFn.Basic.length_ofFn
      scalesStrict := ?_ }
  apply Purelib.Data.List.OfFn.Pairwise.pairwise_ofFn_direct
  intro first second indexOrder
  apply (normalAtIndex threshold count first).homographic_upperQuadrance_ordered
    (normalAtIndex threshold count second) matrix poleExcluded
  · exact ((small first).trans_le
      ((homographicOffsetBudget_le_cylinder threshold count first).trans
        (Cylinder.TwoParameter.denominatorPerturbationDistanceSq_le_oneEighth _ _))).le
  · exact ((small second).trans_le
      ((homographicOffsetBudget_le_cylinder threshold count second).trans
        (Cylinder.TwoParameter.denominatorPerturbationDistanceSq_le_oneEighth _ _))).le
  · exact Nat.add_lt_add_left indexOrder _

/-- The run retains the one transformed fraction used by every offset window. -/
theorem homographicBadWindowRun_source {threshold : Fraction.Rational}
    (certificate : Sharpness.IsSharperWindowThreshold threshold) (requestedScale count : Nat)
    (matrix : Matrix GaussianInt) (unitDeterminant : matrix.determinant = 1)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix)
      (sourceAtCount threshold count).value ≠ 0)
    (small : ∀ offset : Fin count, Gaussian.Norm.Basic.normSq
      ((normalAtIndex threshold count offset).homographicPerturbation matrix) <
        homographicOffsetBudget threshold count offset)
    (scalePaid : ∀ offset : Fin count,
      (normalAtIndex threshold count offset).homographicScaleDenominatorBound requestedScale <
        Gaussian.Norm.Basic.normSq (Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix)
          (sourceAtCount threshold count).value)) :
    (homographicBadWindowRun certificate requestedScale count
      matrix unitDeterminant poleExcluded small scalePaid).source =
      (sourceAtCount threshold count).transform matrix poleExcluded := rfl

/-- The retained run source reads exactly as the shared homographic image of its original source. -/
theorem homographicBadWindowRun_source_value {threshold : Fraction.Rational}
    (certificate : Sharpness.IsSharperWindowThreshold threshold) (requestedScale count : Nat)
    (matrix : Matrix GaussianInt) (unitDeterminant : matrix.determinant = 1)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix)
      (sourceAtCount threshold count).value ≠ 0)
    (small : ∀ offset : Fin count, Gaussian.Norm.Basic.normSq
      ((normalAtIndex threshold count offset).homographicPerturbation matrix) <
        homographicOffsetBudget threshold count offset)
    (scalePaid : ∀ offset : Fin count,
      (normalAtIndex threshold count offset).homographicScaleDenominatorBound requestedScale <
        Gaussian.Norm.Basic.normSq (Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix)
          (sourceAtCount threshold count).value)) :
    (homographicBadWindowRun certificate requestedScale count
      matrix unitDeterminant poleExcluded small scalePaid).source.value =
      Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix)
        (sourceAtCount threshold count).value := by
  rewrite [homographicBadWindowRun_source]
  exact (sourceAtCount threshold count).transform_value matrix poleExcluded

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.Run
