module

public import Purelib.Calculus.Linear.Euler.Intervals
public import Purelib.Algebra.FiniteSum.Prefix.Blocks
import Purelib.Algebra.NatCast
import Purelib.Algebra.Recurrence.Affine.Constant
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-! # Original Euler traces on computed coarse intervals

A fixed coefficient ceiling computes the number of coarse intervals. Each
coarse interval contains consecutive original fine edges, and the original
trace concatenation identifies its result with the same global executor.
The actual local defects feed interval stability and the original affine
comparison, rather than a unit-duration growth assumption.
-/

public section

namespace Purelib.Calculus.Linear.Euler

open Purelib
open Purelib.Algebra.FiniteSum.Prefix
open Purelib.Algebra.Recurrence
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Vector (zipWith)
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Gaussian

/-- Consecutive execution on shifted original coefficients is the same complete original Euler trace. -/
theorem trace_add {size : Nat} (coefficients : Nat → Matrix Canonical size) (widths : Nat → Rational)
    (initial : Vec Canonical size) (first last : Nat) :
    trace coefficients widths initial (first + last) =
      trace (fun index => coefficients (first + index)) (fun index => widths (first + index))
        (trace coefficients widths initial first) last := by
  induction last with
  | zero => rfl
  | succ last prior =>
      exact congrArg (step (coefficients (first + last)) (widths (first + last))) prior

/-- The reciprocal width of any positive original integer grid is at most one. -/
theorem reciprocalWidth_le_one (count : Nat) (positive : 0 < count) :
    (1 : Rational) / (count : Rational) ≤ 1 := by
  apply (Order.Field.div_le_iff_pos (Cast.Order.natCast_pos_direct positive)).mpr
  exact (Cast.Order.natCast_le_direct (m := 1) (n := count) positive).trans_eq
    (Field.one_mul _).symm

/-- An actual consecutive fine block has exactly the reciprocal coarse width.

The block count and positive refinement are the original natural numbers.
The equality uses
their actual rational casts, not a separately chosen width certificate.
-/
theorem reciprocalWidth_sum (blocks width : Nat) (positiveWidth : 0 < width) :
    coordinateSum (fun _ => (1 : Rational) / ((blocks * width : Nat) : Rational)) width =
      1 / (blocks : Rational) := by
  have scaled := coordinateSum_constant ((1 : Rational) / ((blocks * width : Nat) : Rational)) width
  have widthNonzero := (Cast.Order.natCast_pos_direct positiveWidth).ne'
  have denominator := Algebra.NatCast.mul (R := Rational) blocks width
  have divided : (width : Rational) * (1 / ((blocks * width : Nat) : Rational)) =
      1 / (blocks : Rational) := by
    rewrite [denominator, Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.inv_mul_direct]
    calc
      (width : Rational) * (1 * ((blocks : Rational)⁻¹ * (width : Rational)⁻¹)) =
          ((width : Rational) * (width : Rational)⁻¹) * (blocks : Rational)⁻¹ := by ring1
      _ = 1 * (blocks : Rational)⁻¹ :=
        congrArg (fun value : Rational => value * (blocks : Rational)⁻¹)
          (Fraction.mul_inv_cancel _ widthNonzero)
  exact scaled.trans divided

/-- Original local defects on one fixed fine grid give stability across all computed coarse blocks.

The coarse count is computed from the same fixed matrix ceiling before the
fine subdivision. Each block contains exactly `width` consecutive original
edges. The returned scalar is the original executable affine recurrence
with coefficient two and the actual block forcing. No global growth or
endpoint comparison is supplied; dimension zero and zero factors remain
admitted, while the fine count is positive.
-/
theorem stability_blocks {size : Nat} (coefficients : Nat → Matrix Canonical size)
    (samples : Nat → Vec Canonical size) (initial : Vec Canonical size)
    (ceiling : Rational) (nonnegativeCeiling : 0 ≤ ceiling) (width : Nat) (positiveWidth : 0 < width)
    (factor : Rational) (factorNonnegative : 0 ≤ factor)
    (bounded : ∀ index, index < intervalCount size ceiling nonnegativeCeiling * width →
      Norm.matrix (coefficients index) ≤ ceiling)
    (remainders : ∀ index, index < intervalCount size ceiling nonnegativeCeiling * width →
      Norm.vector (defect (coefficients index)
        (1 / ((intervalCount size ceiling nonnegativeCeiling * width : Nat) : Rational))
        (samples index) (samples (index + 1))) ≤
      factor * (1 / ((intervalCount size ceiling nonnegativeCeiling * width : Nat) : Rational)) ^ 4) :
    Norm.vector (zipWith (fun first last => first - last)
      (samples (intervalCount size ceiling nonnegativeCeiling * width))
      (trace coefficients (fun _ =>
        1 / ((intervalCount size ceiling nonnegativeCeiling * width : Nat) : Rational)) initial
          (intervalCount size ceiling nonnegativeCeiling * width))) ≤
    Affine.iterate (fun _ => 2)
      (fun _ => 2 * ((width : Rational) *
        (factor * ((1 / ((intervalCount size ceiling nonnegativeCeiling * width : Nat) : Rational)) + 1) *
          (1 / ((intervalCount size ceiling nonnegativeCeiling * width : Nat) : Rational)) ^ 3)))
      (Norm.vector (zipWith (fun first last => first - last) (samples 0) initial))
      (intervalCount size ceiling nonnegativeCeiling) := by
  let blocks := intervalCount size ceiling nonnegativeCeiling
  let fineWidth : Rational := 1 / ((blocks * width : Nat) : Rational)
  let approximate := trace coefficients (fun _ => fineWidth) initial
  let errors := fun block => Norm.vector (zipWith (fun first last => first - last)
    (samples (block * width)) (approximate (block * width)))
  let forcing : Rational := 2 * ((width : Rational) * (factor * (fineWidth + 1) * fineWidth ^ 3))
  have positiveCount : 0 < blocks * width := Nat.mul_pos (intervalCount_positive size ceiling nonnegativeCeiling)
    positiveWidth
  have finePositive : 0 < fineWidth := Order.Field.div_pos_direct (by decide)
    (Cast.Order.natCast_pos_direct positiveCount)
  have fineUnit : fineWidth ≤ 1 := reciprocalWidth_le_one (blocks * width) positiveCount
  have steps (block : Nat) (before : block < blocks) : errors (block + 1) ≤ 2 * errors block + forcing := by
    have bound (index : Nat) (inner : index < width) : block * width + index < blocks * width := by
      have outer := Nat.mul_le_mul_right width (Nat.succ_le_of_lt before)
      rewrite [Nat.succ_mul] at outer
      omega0
    have actual := stability_on_interval
      (fun index => coefficients (block * width + index)) (fun _ => fineWidth) (fun _ => factor)
      (approximate (block * width)) (fun index => samples (block * width + index))
      ceiling nonnegativeCeiling width (fun _ _ => finePositive) (fun _ _ => fineUnit)
      (fun index inner => bounded _ (bound index inner)) (fun _ _ => factorNonnegative)
      (reciprocalWidth_sum blocks width positiveWidth)
      (fun index inner => remainders _ (bound index inner))
    have sameTrace : approximate ((block + 1) * width) =
        trace (fun index => coefficients (block * width + index)) (fun _ => fineWidth)
          (approximate (block * width)) width :=
      (congrArg approximate (Nat.succ_mul block width)).trans
        (trace_add coefficients (fun _ => fineWidth) initial (block * width) width)
    have left := congrArg (fun value : Vec Canonical size =>
      Norm.vector (zipWith (fun first last => first - last) (samples ((block + 1) * width)) value)) sameTrace
    have endpoint : samples (block * width + width) = samples ((block + 1) * width) :=
      congrArg samples (Nat.succ_mul block width).symm
    have actualLeft := congrArg (fun value : Vec Canonical size =>
      Norm.vector (zipWith (fun first last => first - last) value
        (trace (fun index => coefficients (block * width + index)) (fun _ => fineWidth)
          (approximate (block * width)) width))) endpoint
    have actualRight := congrArg (fun value : Rational => 2 * (errors block + value))
      (coordinateSum_constant (factor * (fineWidth + 1) * fineWidth ^ 3) width)
    exact (left.trans actualLeft.symm).trans_le
      (actual.trans_eq (actualRight.trans (by ring1)))
  have start : errors 0 = Norm.vector (zipWith (fun first last => first - last) (samples 0) initial) := by
    change Norm.vector (zipWith (fun first last => first - last)
      (samples (0 * width)) (approximate (0 * width))) = _
    rewrite [Nat.zero_mul]
    rfl
  exact Affine.comparison (fun _ => 2) (fun _ => forcing) errors
    (Norm.vector (zipWith (fun first last => first - last) (samples 0) initial)) blocks
    (start.trans_le (Order.Basic.le_refl _)) (fun _ _ => by decide) steps

/-- Two original traces on the same grid differ by at most the computed coarse initial-value amplification.

The coefficient ceiling computes the original coarse count. Each trace
keeps its own initial vector. The first trace has exactly zero local
defects, so the existing block theorem derives this comparison without
an endpoint agreement or growth-bound premise. No trace is redefined.
-/
theorem trace_difference_blocks_le {size : Nat} (coefficients : Nat → Matrix Canonical size)
    (leftInitial rightInitial : Vec Canonical size) (ceiling : Rational) (nonnegativeCeiling : 0 ≤ ceiling)
    (width : Nat) (positiveWidth : 0 < width)
    (bounded : ∀ index, index < intervalCount size ceiling nonnegativeCeiling * width →
      Norm.matrix (coefficients index) ≤ ceiling) :
    let coarse := intervalCount size ceiling nonnegativeCeiling
    let count := coarse * width
    let spacing := 1 / (count : Rational)
    Norm.vector (zipWith (fun first last => first - last)
      (trace coefficients (fun _ => spacing) leftInitial count)
      (trace coefficients (fun _ => spacing) rightInitial count)) ≤
    Affine.iterate (fun _ => 2) (fun _ => 0) 1 coarse *
      Norm.vector (zipWith (fun first last => first - last) leftInitial rightInitial) := by
  let coarse := intervalCount size ceiling nonnegativeCeiling
  let count := coarse * width
  let spacing : Rational := 1 / (count : Rational)
  let error := Norm.vector (zipWith (fun first last => first - last) leftInitial rightInitial)
  let forcing : Rational := 2 * ((width : Rational) * (0 * (spacing + 1) * spacing ^ 3))
  have residual (index : Nat) (_before : index < count) :
      Norm.vector (defect (coefficients index) spacing
        (trace coefficients (fun _ => spacing) leftInitial index)
        (trace coefficients (fun _ => spacing) leftInitial (index + 1))) ≤ 0 * spacing ^ 4 := by
    rewrite [trace_defect_eq_zero coefficients (fun _ => spacing) leftInitial index,
      show (0 : Rational) * spacing ^ 4 = 0 by ring1]
    exact Order.Basic.le_refl _
  have compared := stability_blocks coefficients (trace coefficients (fun _ => spacing) leftInitial)
    rightInitial ceiling nonnegativeCeiling width positiveWidth 0 (by decide +kernel) bounded residual
  have forcingZero : forcing = 0 := by unfold forcing; ring1
  have normalized := congrArg (fun value : Rational =>
    Affine.iterate (fun _ => 2) (fun _ => value) error coarse) forcingZero
  have response := Affine.iterate_initial (fun _ => (2 : Rational)) (fun _ => 0) error coarse
  have zeroed := (Affine.iterate_constant_forcing (2 : Rational) 0 coarse).trans
    (show (0 : Rational) * Affine.iterate (fun _ => 2) (fun _ => 1) 0 coarse = 0 by ring1)
  have homogeneous : Affine.iterate (fun _ => (2 : Rational)) (fun _ => 0) error coarse =
      Affine.iterate (fun _ => 2) (fun _ => 0) 1 coarse * error := response.trans
    ((congrArg (fun value : Rational => Affine.iterate (fun _ => 2) (fun _ => 0) 1 coarse * error + value)
      zeroed).trans (by ring1))
  exact compared.trans_eq (normalized.trans homogeneous)

end Purelib.Calculus.Linear.Euler

end
