module
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Pair.LinearCombination
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.NumberTheory.Approximation.Best.Error
import Purelib.NumberTheory.Approximation.Best.Error.Bounds
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Adjacent.Tower
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.TwoParameter
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Pair
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Parameter

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Embedding
public import Purelib.Data.GaussianInt.Enumeration
import Purelib.Data.Int.Interval
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Finite coefficient reduction near transported critical sources

At the exact critical source, the two-parameter cylinder theorem controls
every integral coefficient pair.  After perturbing the source, a competitor
inside the displayed mixed cylinder might no longer be exterior by the same
exact identity.  This file proves the required finite reduction: inside an
explicit positive rational squared-distance budget, every such competitor
has both coefficient quadrances `< 32`.
-/

public section

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.CoefficientBound

open Purelib.Data
open Purelib.Data.Rat
open Purelib.NumberTheory.Approximation

/-- A conservative positive squared-distance budget under which an apparent
mixed-cylinder competitor has exact-source normalized error quadrance at
most five. -/
@[expose] def coefficientCutoffDistanceSq
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm
      source errorStage targetStage) : Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq normal.lowerError /
    (6 * Fraction.Cast.fromInt (Best.Error.denominatorQuadrance
      (Dirichlet.Critical.Pair.criticalUpperPair targetStage) : Int))

/-- The direct upper-quadrance reading retains the original coefficient-cutoff distance formula. -/
theorem coefficientCutoffDistanceSq_eq_cast
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm source errorStage targetStage) :
    coefficientCutoffDistanceSq normal = Data.Gaussian.Norm.Basic.normSq normal.lowerError /
      (6 * (Best.Error.denominatorQuadrance (Dirichlet.Critical.Pair.criticalUpperPair targetStage) :
        Fraction.Rational)) := by
  rewrite [Fraction.Cast.natCast_eq_fromInt]
  rfl

/-- The coefficient cutoff distance budget is positive for a transported normal form. -/
theorem coefficientCutoffDistanceSq_pos
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm
      source errorStage targetStage) :
    0 < Dirichlet.Critical.Robust.CoefficientBound.coefficientCutoffDistanceSq normal := by
  rewrite [coefficientCutoffDistanceSq_eq_cast]
  apply Fraction.Order.Field.div_pos_direct normal.lowerErrorPositive
  apply Fraction.Order.Arithmetic.mul_pos_direct (by decide)
  apply Fraction.Cast.Order.natCast_pos_direct
  exact GaussianInt.normNat_pos
    (Dirichlet.Critical.Pair.criticalUpper_denominator_ne_zero
      targetStage)

/-- Recover the central error by subtracting the denominator-scaled displacement from the sampled error. -/
private theorem exact_error_identity
    (center sample : Gaussian.Basic.Canonical) (pair : Purelib.Data.GaussianInt.Pair.Basic.ConvergentPair) :
    Best.Error.error center pair =
      Best.Error.error sample pair -
        (sample - center) * Purelib.Data.GaussianInt.toGaussian pair.denominator := by
  calc
    Best.Error.error center pair =
        (Best.Error.error center pair +
            (sample - center) * GaussianInt.toGaussian pair.denominator) -
          (sample - center) * GaussianInt.toGaussian pair.denominator := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.add_re,
          Gaussian.Basic.add_im] <;>
        ring1
    _ = Best.Error.error sample pair -
        (sample - center) * GaussianInt.toGaussian pair.denominator := by
      exact (congrArg
        (fun value => value -
          (sample - center) * GaussianInt.toGaussian pair.denominator)
        (Best.Error.error_perturbation_identity center sample pair)).symm

/-- The squared error perturbation is the source displacement quadrance times the denominator quadrance. -/
private theorem perturbation_normSq
    (center sample : Gaussian.Basic.Canonical) (pair : Purelib.Data.GaussianInt.Pair.Basic.ConvergentPair) :
    Data.Gaussian.Norm.Basic.normSq
        ((sample - center) * Purelib.Data.GaussianInt.toGaussian pair.denominator) =
      Data.Gaussian.Norm.Basic.normSq (sample - center) *
        (Best.Error.denominatorQuadrance pair : Fraction.Rational) := by
  rw [Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian]
  rfl

/-- A denominator-bounded coefficient combination has normalized target
denominator quadrance at most one. -/
theorem normalizedDenominator_normSq_le_one
    (targetStage : Nat) (left right : GaussianInt)
    (denominatorBound :
      Best.Error.denominatorQuadrance
          (GaussianInt.Pair.LinearCombination.linearCombination
            (Dirichlet.Critical.Pair.criticalLowerPair targetStage)
            (Dirichlet.Critical.Pair.criticalUpperPair targetStage)
            left right) ≤
        Best.Error.denominatorQuadrance
          (Dirichlet.Critical.Pair.criticalUpperPair targetStage)) :
    Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator
          (Dirichlet.Critical.Parameter.pellParameter targetStage)
          left right) ≤ 1 := by
  let upper := Dirichlet.Critical.Pair.criticalUpperPair targetStage
  let candidate := GaussianInt.Pair.LinearCombination.linearCombination
    (Dirichlet.Critical.Pair.criticalLowerPair targetStage) upper left right
  have upperPositive :
      (0 : Fraction.Rational) < Best.Error.denominatorQuadrance upper := by
    apply Fraction.Cast.Order.natCast_pos_direct
    exact GaussianInt.normNat_pos
      (Dirichlet.Critical.Pair.criticalUpper_denominator_ne_zero
        targetStage)
  have castBound :
      (Best.Error.denominatorQuadrance candidate : Fraction.Rational) ≤
        (Best.Error.denominatorQuadrance upper : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct denominatorBound
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
    (c := (Best.Error.denominatorQuadrance upper : Fraction.Rational))
  · calc
      Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator
              (Dirichlet.Critical.Parameter.pellParameter targetStage)
              left right) *
          (Best.Error.denominatorQuadrance upper : Fraction.Rational) =
        Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian upper.denominator *
            Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator
              (Dirichlet.Critical.Parameter.pellParameter targetStage)
              left right) := by
          rw [Gaussian.Norm.Basic.normSq_mul,
            GaussianInt.normSq_toGaussian]
          unfold Best.Error.denominatorQuadrance
          ring1
      _ = Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian candidate.denominator) := by
        rw [Dirichlet.Critical.Adjacent.Tower.target_denominator_linearCombination]
      _ = (Best.Error.denominatorQuadrance candidate : Fraction.Rational) := by
        rw [GaussianInt.normSq_toGaussian]
        rfl
      _ ≤ (Best.Error.denominatorQuadrance upper : Fraction.Rational) := castBound
      _ = (1 : Fraction.Rational) * Best.Error.denominatorQuadrance upper := by ring1
  · exact upperPositive

/-- Within the explicit cutoff budget, any candidate whose sampled error is
no larger than the sampled lower-basis error and whose denominator is no
larger than the upper-basis denominator has exact normalized error quadrance
at most five. -/
theorem normalizedError_normSq_le_five
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm
      source errorStage targetStage)
    (sample : Gaussian.Basic.Canonical) (left right : GaussianInt)
    (sampleErrorBound :
      Best.Error.errorQuadrance sample
          (GaussianInt.Pair.LinearCombination.linearCombination
            (Dirichlet.Critical.Pair.criticalLowerPair targetStage)
            (Dirichlet.Critical.Pair.criticalUpperPair targetStage)
            left right) ≤
        Best.Error.errorQuadrance sample
          (Dirichlet.Critical.Pair.criticalLowerPair targetStage))
    (denominatorBound :
      Best.Error.denominatorQuadrance
          (GaussianInt.Pair.LinearCombination.linearCombination
            (Dirichlet.Critical.Pair.criticalLowerPair targetStage)
            (Dirichlet.Critical.Pair.criticalUpperPair targetStage)
            left right) ≤
        Best.Error.denominatorQuadrance
          (Dirichlet.Critical.Pair.criticalUpperPair targetStage))
    (distanceSmall :
      Data.Gaussian.Norm.Basic.normSq (sample - source.value) ≤
        Dirichlet.Critical.Robust.CoefficientBound.coefficientCutoffDistanceSq normal) :
    Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError
          (Dirichlet.Critical.Parameter.pellParameter errorStage)
          left right) ≤ 5 := by
  rewrite [coefficientCutoffDistanceSq_eq_cast] at distanceSmall
  let lower := Dirichlet.Critical.Pair.criticalLowerPair targetStage
  let upper := Dirichlet.Critical.Pair.criticalUpperPair targetStage
  let candidate := GaussianInt.Pair.LinearCombination.linearCombination lower upper left right
  let distance :=
    Data.Gaussian.Norm.Basic.normSq (sample - source.value)
  let lowerScale : Fraction.Rational := Best.Error.denominatorQuadrance lower
  let upperScale : Fraction.Rational := Best.Error.denominatorQuadrance upper
  let candidateScale : Fraction.Rational := Best.Error.denominatorQuadrance candidate
  let exactScale :=
    Data.Gaussian.Norm.Basic.normSq normal.lowerError
  have distanceNonnegative : 0 ≤ distance :=
    Gaussian.Norm.Basic.normSq_nonneg _
  have upperScalePositive : 0 < upperScale := by
    dsimp only [upperScale, upper]
    apply Fraction.Cast.Order.natCast_pos_direct
    exact GaussianInt.normNat_pos
      (Dirichlet.Critical.Pair.criticalUpper_denominator_ne_zero
        targetStage)
  have lowerScaleLeUpper : lowerScale ≤ upperScale := by
    dsimp only [lowerScale, upperScale, lower, upper]
    exact Fraction.Cast.Order.natCast_le_direct
      (Dirichlet.Critical.Pair.critical_denominatorQuadrance_ordered
        targetStage).le
  have candidateScaleLeUpper : candidateScale ≤ upperScale := by
    dsimp only [candidateScale, upperScale, candidate, lower, upper]
    exact Fraction.Cast.Order.natCast_le_direct denominatorBound
  have scaledDistanceLe : 6 * (distance * upperScale) ≤ exactScale := by
    have denominatorPositive : 0 < 6 * upperScale :=
      Fraction.Order.Arithmetic.mul_pos_direct (by decide)
        upperScalePositive
    have divided :=
      (Fraction.Order.Field.le_div_iff_pos denominatorPositive).1
        (show distance ≤ exactScale / (6 * upperScale) by
          simpa only [distance, exactScale, upperScale, upper] using distanceSmall)
    calc
      6 * (distance * upperScale) = distance * (6 * upperScale) := by ring1
      _ ≤ exactScale := divided
  have lowerPerturbationBound :
      Data.Gaussian.Norm.Basic.normSq
          ((sample - source.value) * GaussianInt.toGaussian lower.denominator) ≤
        distance * upperScale := by
    rw [Dirichlet.Critical.Robust.CoefficientBound.perturbation_normSq]
    dsimp only [distance, lowerScale]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      lowerScaleLeUpper distanceNonnegative
  have candidatePerturbationBound :
      Data.Gaussian.Norm.Basic.normSq
          ((sample - source.value) * GaussianInt.toGaussian candidate.denominator) ≤
        distance * upperScale := by
    rw [Dirichlet.Critical.Robust.CoefficientBound.perturbation_normSq]
    dsimp only [distance, candidateScale]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      candidateScaleLeUpper distanceNonnegative
  have sampleLowerBound :
      Best.Error.errorQuadrance sample lower ≤
        2 * (exactScale + distance * upperScale) := by
    unfold Best.Error.errorQuadrance
    rw [Best.Error.error_perturbation_identity source.value sample lower,
      normal.lowerIdentity]
    exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct (le_refl exactScale)
          lowerPerturbationBound) (by decide))
  have exactCandidateBound :
      Best.Error.errorQuadrance source.value candidate ≤ 5 * exactScale := by
    unfold Best.Error.errorQuadrance
    rw [Dirichlet.Critical.Robust.CoefficientBound.exact_error_identity source.value sample candidate]
    calc
      Data.Gaussian.Norm.Basic.normSq
          (Best.Error.error sample candidate -
            (sample - source.value) * GaussianInt.toGaussian candidate.denominator) ≤
        2 *
          (Data.Gaussian.Norm.Basic.normSq
              (Best.Error.error sample candidate) +
            Data.Gaussian.Norm.Basic.normSq
              ((sample - source.value) *
                GaussianInt.toGaussian candidate.denominator)) :=
        Gaussian.Norm.Bounds.normSq_sub_le_two _ _
      _ ≤ 2 * (Best.Error.errorQuadrance sample lower + distance * upperScale) := by
        apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _
          (by decide)
        exact Fraction.Order.Arithmetic.add_le_add_direct sampleErrorBound
          candidatePerturbationBound
      _ ≤ 2 * (2 * (exactScale + distance * upperScale) +
          distance * upperScale) := by
        apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _
          (by decide)
        exact Fraction.Order.Arithmetic.add_le_add_direct sampleLowerBound
          (le_refl _)
      _ = 4 * exactScale + 6 * (distance * upperScale) := by ring1
      _ ≤ 4 * exactScale + exactScale :=
        Fraction.Order.Arithmetic.add_le_add_direct (le_refl _)
          scaledDistanceLe
      _ = 5 * exactScale := by ring1
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
    (c := exactScale)
  · calc
      Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError
              (Dirichlet.Critical.Parameter.pellParameter errorStage)
              left right) * exactScale =
        Best.Error.errorQuadrance source.value candidate := by
          unfold Best.Error.errorQuadrance
          rw [normal.error_linearCombination,
            Gaussian.Norm.Basic.normSq_mul]
          dsimp only [exactScale]
          ring1
      _ ≤ 5 * exactScale := exactCandidateBound
  · simpa only [exactScale] using normal.lowerErrorPositive

/-- The perturbative mixed-cylinder reduction: every sampled competitor in
the displayed closed cylinder comes from Gaussian-integral coefficient
quadrances `< 32`. -/
theorem coefficient_normNat_lt_thirtyTwo_of_nearby_competitor
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm
      source errorStage targetStage)
    (sample : Gaussian.Basic.Canonical) (left right : GaussianInt)
    (sampleErrorBound :
      Best.Error.errorQuadrance sample
          (GaussianInt.Pair.LinearCombination.linearCombination
            (Dirichlet.Critical.Pair.criticalLowerPair targetStage)
            (Dirichlet.Critical.Pair.criticalUpperPair targetStage)
            left right) ≤
        Best.Error.errorQuadrance sample
          (Dirichlet.Critical.Pair.criticalLowerPair targetStage))
    (denominatorBound :
      Best.Error.denominatorQuadrance
          (GaussianInt.Pair.LinearCombination.linearCombination
            (Dirichlet.Critical.Pair.criticalLowerPair targetStage)
            (Dirichlet.Critical.Pair.criticalUpperPair targetStage)
            left right) ≤
        Best.Error.denominatorQuadrance
          (Dirichlet.Critical.Pair.criticalUpperPair targetStage))
    (distanceSmall :
      Data.Gaussian.Norm.Basic.normSq (sample - source.value) ≤
        Dirichlet.Critical.Robust.CoefficientBound.coefficientCutoffDistanceSq normal) :
    GaussianInt.normNat left < 32 ∧ GaussianInt.normNat right < 32 := by
  apply Dirichlet.Critical.Cylinder.TwoParameter.coefficient_normNat_lt_thirtyTwo
    (Dirichlet.Critical.Parameter.pellParameter_isCritical errorStage)
    (Dirichlet.Critical.Parameter.pellParameter_isCritical targetStage)
  · exact Dirichlet.Critical.Robust.CoefficientBound.normalizedError_normSq_le_five normal sample left right
      sampleErrorBound denominatorBound distanceSmall
  · exact Dirichlet.Critical.Robust.CoefficientBound.normalizedDenominator_normSq_le_one targetStage left right
      denominatorBound

/-! ## Executable bounded coefficient domain -/

/-- A small rectangular over-enumeration of every Gaussian integer with
quadrance `< 32`.  Component magnitude five is sufficient because magnitude
six alone already contributes quadrance thirty-six. -/
@[expose] def boundedCoefficients : List GaussianInt :=
  GaussianInt.componentSquare 5

/-- The executable coefficient over-enumeration has 144 entries. -/
@[simp] theorem boundedCoefficients_length :
    Dirichlet.Critical.Robust.CoefficientBound.boundedCoefficients.length = 144 := by
  unfold Dirichlet.Critical.Robust.CoefficientBound.boundedCoefficients
  rw [GaussianInt.componentSquare_length]

/-- Quadrance below 32 bounds the real integer component magnitude by five. -/
private theorem realComponent_natAbs_le_five_of_normNat_lt_thirtyTwo
    (value : GaussianInt) (bounded : GaussianInt.normNat value < 32) :
    value.re.natAbs ≤ 5 := by
  have squareStrict : Nat.pow value.re.natAbs 2 < 32 := by
    calc
      Nat.pow value.re.natAbs 2 ≤
          Nat.pow value.re.natAbs 2 + Nat.pow value.im.natAbs 2 := Nat.le_add_right _ _
      _ = GaussianInt.normNat value := (GaussianInt.Norm.Basic.normNat_eq_component_squares value).symm
      _ < 32 := bounded
  generalize componentIdentity : value.re.natAbs = magnitude at squareStrict ⊢
  clear componentIdentity bounded value
  by_contra tooLarge
  have sixLe : 6 ≤ magnitude := by omega0
  have squareLower : 36 ≤ Nat.pow magnitude 2 := by
    change 36 ≤ (1 * magnitude) * magnitude
    rw [Nat.one_mul]
    exact Nat.mul_le_mul sixLe sixLe
  omega0

/-- Quadrance below 32 bounds the imaginary integer component magnitude by five. -/
private theorem imaginaryComponent_natAbs_le_five_of_normNat_lt_thirtyTwo
    (value : GaussianInt) (bounded : GaussianInt.normNat value < 32) :
    value.im.natAbs ≤ 5 := by
  have squareStrict : Nat.pow value.im.natAbs 2 < 32 := by
    calc
      Nat.pow value.im.natAbs 2 ≤
          Nat.pow value.re.natAbs 2 + Nat.pow value.im.natAbs 2 := Nat.le_add_left _ _
      _ = GaussianInt.normNat value := (GaussianInt.Norm.Basic.normNat_eq_component_squares value).symm
      _ < 32 := bounded
  generalize componentIdentity : value.im.natAbs = magnitude at squareStrict ⊢
  clear componentIdentity bounded value
  by_contra tooLarge
  have sixLe : 6 ≤ magnitude := by omega0
  have squareLower : 36 ≤ Nat.pow magnitude 2 := by
    change 36 ≤ (1 * magnitude) * magnitude
    rw [Nat.one_mul]
    exact Nat.mul_le_mul sixLe sixLe
  omega0

/-- Every Gaussian integer of quadrance below 32 occurs in the displayed coefficient list. -/
theorem mem_boundedCoefficients_of_normNat_lt_thirtyTwo
    {value : GaussianInt} (bounded : GaussianInt.normNat value < 32) :
    value ∈ Dirichlet.Critical.Robust.CoefficientBound.boundedCoefficients := open Purelib in by
  unfold Dirichlet.Critical.Robust.CoefficientBound.boundedCoefficients GaussianInt.componentSquare
  apply Data.List.Flatten.mem_flatMap.mpr
  refine ⟨value.re,
    Data.Int.Interval.mem_signedComponents
      (Dirichlet.Critical.Robust.CoefficientBound.realComponent_natAbs_le_five_of_normNat_lt_thirtyTwo value bounded),
    ?_⟩
  apply Data.List.Map.mem_map.mpr
  refine ⟨value.im,
    Data.Int.Interval.mem_signedComponents
      (Dirichlet.Critical.Robust.CoefficientBound.imaginaryComponent_natAbs_le_five_of_normNat_lt_thirtyTwo
        value bounded), ?_⟩
  rfl

/-- The executable finite domain of all coefficient pairs requiring robust
error-comparison margins. -/
@[expose] def boundedCoefficientPairs : List (GaussianInt × GaussianInt) :=
  Dirichlet.Critical.Robust.CoefficientBound.boundedCoefficients.flatMap fun left =>
    Dirichlet.Critical.Robust.CoefficientBound.boundedCoefficients.map fun right => (left, right)

/-- The executable list of bounded coefficient pairs has 20,736 entries. -/
@[simp] theorem boundedCoefficientPairs_length :
    Dirichlet.Critical.Robust.CoefficientBound.boundedCoefficientPairs.length = 20736 := by
  unfold Dirichlet.Critical.Robust.CoefficientBound.boundedCoefficientPairs
  rw [List.Flatten.length_flatMap_map, Dirichlet.Critical.Robust.CoefficientBound.boundedCoefficients_length]

/-- Two coefficients of quadrance below 32 occur together in the displayed finite pair domain. -/
theorem mem_boundedCoefficientPairs_of_normNat_lt_thirtyTwo
    {left right : GaussianInt}
    (leftBounded : GaussianInt.normNat left < 32)
    (rightBounded : GaussianInt.normNat right < 32) :
    (left, right) ∈ Dirichlet.Critical.Robust.CoefficientBound.boundedCoefficientPairs := open Purelib in by
  unfold Dirichlet.Critical.Robust.CoefficientBound.boundedCoefficientPairs
  apply Data.List.Flatten.mem_flatMap.mpr
  refine ⟨left,
    Dirichlet.Critical.Robust.CoefficientBound.mem_boundedCoefficients_of_normNat_lt_thirtyTwo leftBounded, ?_⟩
  apply Data.List.Map.mem_map.mpr
  exact ⟨right,
    Dirichlet.Critical.Robust.CoefficientBound.mem_boundedCoefficients_of_normNat_lt_thirtyTwo rightBounded, rfl⟩

-- Keep the 20,736-entry executable value opaque to ordinary elaboration;
-- its exact length and completeness are exposed by the theorems above.
end Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.CoefficientBound
