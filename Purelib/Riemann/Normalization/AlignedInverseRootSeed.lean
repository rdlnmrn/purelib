module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Evaluation

import Purelib.Riemann.Normalization.InverseRootComparison
public import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Power.Gaussian
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Automatic sign-sensitive inverse-root seeds

Prepare a smaller box within the supplied owner, and acquire the root sample
at an explicitly requested residual.  Every candidate in the retained box is
then aligned with the same inverse-root seed.  The construction is total;
neither a small-box premise nor a successful certificate check is required.

Already sufficiently small boxes are reused.  Generated alternatives may
supply the same containment and rational alignment certificates directly.
-/

namespace Purelib.Riemann.Normalization.AlignedInverseRootSeed

open Purelib.Riemann.Normalization.OwnerSeededInverseRoot (Owner Seed OwnerSample seed_residual_le_relative)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical

set_option genInjectivity false in
/-- An inverse-root seed aligned with the original source owner's sheet throughout a refining root box.

The seed retains its own root owner, refinement to the original source box, and a uniform one-two-hundred-fifty-sixth
squared mismatch bound for every point of the retained seed box. -/
structure AlignedSeed {parameter : Gaussian} (source : Owner parameter) where
  /-- The retained inverse-root seed with its original owner and sample. -/ seed : Seed parameter
  /-- The retained owner's initial box refines the original source owner's initial box. -/ refines :
    seed.owner.track.initial.box.Refines source.track.initial.box
  /-- Every point in the retained seed owner's box has squared seed mismatch at most one two-hundred-fifty-sixth. -/
    aligned : forall root, seed.owner.track.initial.box.Contains root ->
    normSq (1 - root * seed.value) <= 1 / 256

constructive_injectivity AlignedSeed

namespace AlignedSeed

set_option genInjectivity false in
/-- A retained root owner refining the original source box at the requested squared-diagonal bound.

The exact source parameter and rational target index the retained owner.
Its box refinement and diagonal certificate refer to that same original owner. -/
structure SmallOwner {parameter : Gaussian} (source : Owner parameter) (target : Coordinate) where
  /-- The retained root owner for the exact original parameter. -/ owner : Owner parameter
  /-- The retained owner's initial box refines the original source owner's initial box. -/ refines :
    owner.track.initial.box.Refines source.track.initial.box
  /-- The retained owner's squared initial-box diagonal is bounded by the requested target. -/ small :
    owner.track.initial.box.diagonalSq <= target

constructive_injectivity SmallOwner

/-- Retain the source owner if its initial box is already small enough; otherwise use its certified preparation at the
positive target.

Both branches retain refinement to the exact original source box and the requested squared-diagonal inequality. -/
def smallOwner {parameter : Gaussian} (source : Owner parameter) (target : Coordinate)
    (positive : 0 < target) : SmallOwner source target :=
  if small : source.track.initial.box.diagonalSq <= target then
    ⟨source, source.track.initial.box.refines_refl, small⟩
  else
    ⟨source.prepare target positive,
      source.prepare_initial_refines target positive,
      (source.prepare_diagonal_lt target positive).le⟩

open Purelib.Data.Rat in
/-- Certify alignment of a retained seed from its small residual and small box-times-seed-norm contribution.

The two one-one-thousand-twenty-fourth bounds combine through the original seed mismatch estimate to the uniform
one-two-hundred-fifty-sixth alignment bound. -/
def ofSeed {parameter : Gaussian} {source : Owner parameter} (seed : Seed parameter)
    (refines : seed.owner.track.initial.box.Refines source.track.initial.box)
    (residualSmall : normSq (1 - parameter * seed.value ^ 2) <= 1 / 1024)
    (boxSmall : seed.owner.track.initial.box.diagonalSq * normSq seed.value <= 1 / 1024) :
    AlignedSeed source where
  seed := seed
  refines := refines
  aligned := fun root inside => (seed.mismatch_le inside).trans (by
    calc
      _ <= 2 * ((1 / 1024 : Coordinate) + 1 / 1024) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add residualSmall boxSmall) (by decide)
      _ = 1 / 256 := by decide +kernel)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
/-- Construct an aligned seed using the retained prepared owner, accurate original sample and source-box norm bound.

The supplied upper-bound equality controls the sample divided by the original parameter; the prepared box diameter and
relative residual together pay the alignment estimate. -/
def fromSmallOwner {parameter : Gaussian} (source prepared : Owner parameter)
    (refines : prepared.track.initial.box.Refines source.track.initial.box)
    (upper : Coordinate)
    (upper_eq : upper = source.track.initial.box.normSqBound * normSq (inv parameter))
    (upperPositive : 0 < upper + 1)
    (small : prepared.track.initial.box.diagonalSq <= (1 / 1024 : Coordinate) / (upper + 1))
    (sample : OwnerSample prepared ((1 / 1024) * normSq parameter)) : AlignedSeed source := by
  have sampleCoarse : normSq (sample.value * sample.value - parameter) <= normSq parameter / 64 := by
    calc
      _ <= (1 / 1024 : Coordinate) * normSq parameter := sample.residualBound
      _ <= (1 / 64 : Coordinate) * normSq parameter :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel) (Basic.Canonical.normSq_nonneg
          _)
      _ = normSq parameter / 64 := by
        simp only [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.one_mul]
        ring1
  let seed := Seed.ofSample prepared sample.value sample.inside sampleCoarse
  have seedNorm : normSq seed.value <= upper := by
    change normSq (sample.value * inv parameter) <= upper
    rw [Basic.Canonical.normSq_mul, upper_eq]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by simpa only [Norm.Basic.normSq_eq_canonical] using Box.normSq_le_normSqBound (refines.contains
        sample.inside)) (Basic.Canonical.normSq_nonneg _)
  let target : Coordinate := (1 / 1024) / (upper + 1)
  have targetPositive : 0 < target :=
    Fraction.Order.Field.div_pos_direct (by decide +kernel) upperPositive
  have boxSmall : seed.owner.track.initial.box.diagonalSq * normSq seed.value <= 1 / 1024 := by
    calc
      _ <= target * upper := Fraction.Order.Arithmetic.mul_le_mul_direct
        small seedNorm (Basic.Canonical.normSq_nonneg _) targetPositive.le
      _ <= target * (upper + 1) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (le_add_of_nonneg_right (by decide)) targetPositive.le
      _ = 1 / 1024 := Fraction.Field.div_mul_cancel_of_ne _ _ upperPositive.ne'
  exact ofSeed seed refines
    (seed_residual_le_relative source.parameterNonzero sample.residualBound) boxSmall

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Prepare an aligned inverse-root seed while retaining refinement to the original source root box.

The source box and parameter determine a positive diameter target and relative residual request; the selected sample
belongs to the retained prepared owner. -/
def ofOwner {parameter : Gaussian} (source : Owner parameter) : AlignedSeed source := by
  let upper := source.track.initial.box.normSqBound * normSq (inv parameter)
  have upperNonnegative : 0 <= upper := Fraction.Order.Arithmetic.mul_nonneg_direct
    source.track.initial.box.normSqBound_nonneg (Basic.Canonical.normSq_nonneg _)
  have upperPositive : 0 < upper + 1 :=
    Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct upperNonnegative (by decide)
  let target : Coordinate := (1 / 1024) / (upper + 1)
  have targetPositive : 0 < target :=
    Fraction.Order.Field.div_pos_direct (by decide +kernel) upperPositive
  let prepared := smallOwner source target targetPositive
  let sample := OwnerSample.acquire prepared.owner ((1 / 1024) * normSq parameter)
    (by
      have positive := Norm.Basic.normSq_pos source.parameterNonzero
      rw [Norm.Basic.normSq_eq_canonical] at positive
      exact Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel) positive)
  exact fromSmallOwner source prepared.owner prepared.refines upper rfl upperPositive prepared.small sample

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Normalization in
open Purelib.Riemann.Readings in
/-- Refining the aligned inverse-root model contracts mismatch with a retained root sample up to its relative residual
error.

At the same neighborhood point and original seed root box, the bound is the indexed quarter-radius of one
two-hundred-fifty-sixth plus sixteen times the supplied root error, assuming that error is at most one
four-thousand-ninety-sixth. -/
theorem refine_mismatch_bound {polynomial : Polynomial} {count : Nat}
    (site : PreparedObservationNeighborhoods.ObservationNeighborhood polynomial count)
    {source : Owner (polynomial.eval site.center)} (aligned : AlignedSeed source)
    (point : Gaussian) (inside : (OwnerSeededInverseRoot.SeededNeighborhood.ofSeed site aligned.seed).box.Contains
      point)
    (root : Gaussian) (rootInside : aligned.seed.owner.track.initial.box.Contains root)
    {rootError : Coordinate} (rootErrorNonnegative : 0 <= rootError)
    (rootErrorSmall : rootError <= 1 / 4096)
    (rootResidual : normSq (root ^ 2 - polynomial.eval point) <= rootError * normSq (polynomial.eval point))
    (index : Nat) :
    normSq (1 - root * ((OwnerSeededInverseRoot.SeededNeighborhood.ofSeed site aligned.seed).refine index).value.eval
      point) <=
      Geometric.Basic.quarterRadius (1 / 256) index + 16 * rootError := by
  rw [← Norm.Basic.normSq_eq_canonical]
  apply InverseRootComparison.Model.refine_mismatch_bound
    _ point inside root rootErrorNonnegative (by simpa only [Norm.Basic.normSq_eq_canonical] using rootResidual)
  · rw [Norm.Basic.normSq_eq_canonical]
    simpa only [OwnerSeededInverseRoot.SeededNeighborhood.ofSeed, OwnerSeededInverseRoot.SeededNeighborhood.ofRadius,
      Model.ofSeed,
      Dense.Basic.DensePolynomial.eval_constant] using aligned.aligned root rootInside
  · calc
      _ <= (1 / 256 : Coordinate) + 16 * (1 / 4096) := add_le_add le_rfl
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rootErrorSmall (by decide))
      _ <= 1 / 64 := by decide +kernel

end AlignedSeed

end Purelib.Riemann.Normalization.AlignedInverseRootSeed
