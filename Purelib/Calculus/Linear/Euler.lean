module

public import Purelib.LinearAlgebra.Gaussian.Norm
public import Purelib.LinearAlgebra.Matrix.Multiplication.Vector
public import Purelib.Algebra.Recurrence.Affine
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Tactic.Ring

/-! # Finite Euler transport of Gaussian vectors

Each step materializes the original matrix action once before combining
its retained coordinates. The finite trace is constructed independently
of any proposed endpoint value. Its local bounds use the original matrix
coefficients and rational step widths.
-/

public section

namespace Purelib.Calculus.Linear.Euler

open Purelib.Algebra.FiniteSum

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin_congr sumFin_zero)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Scale (scale scale_sub)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Vector (map zipWith)
open Purelib.Data.Vector.Basic (map_apply vector_ext zipWith_apply)
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Gaussian

/-- Advance one original finite vector by its actual coefficient matrix and rational step width.

The complete matrix action is computed once outside the coordinate
combiner. The returned structural vector retains those same input values,
action coordinates and width, without an endpoint or comparison input.
-/
@[expose] def step {size : Nat} (coefficients : Matrix Canonical size) (width : Rational)
    (values : Vec Canonical size) : Vec Canonical size :=
  let derivative := Matrix.Multiplication.matrixVector coefficients values
  zipWith (fun value slope => value + scale width slope) values derivative

/-- Read one actual Euler coordinate from the original vector and its retained matrix action. -/
theorem step_apply {size : Nat} (coefficients : Matrix Canonical size) (width : Rational)
    (values : Vec Canonical size) (row : Fin size) :
    step coefficients width values row =
      values row + scale width (Matrix.Multiplication.matrixVector coefficients values row) :=
  zipWith_apply _ _ _ row

/-- A vanishing original matrix action leaves the complete Euler input vector unchanged.

The width is arbitrary. Only the action on this actual vector must vanish;
the matrix need not be the zero matrix on other vectors.
-/
theorem step_eq_of_action_zero {size : Nat} (coefficients : Matrix Canonical size) (width : Rational)
    (values : Vec Canonical size)
    (zero : ∀ row, Matrix.Multiplication.matrixVector coefficients values row = 0) :
    step coefficients width values = values := by
  have scaledZero : scale width (0 : Canonical) = 0 := by
    apply Data.Gaussian.Basic.ext
    · change width * 0 = 0
      ring1
    · change width * 0 = 0
      ring1
  apply vector_ext
  intro row
  calc
    _ = values row + scale width 0 :=
      (step_apply coefficients width values row).trans
        (congrArg (fun value : Canonical => values row + scale width value) (zero row))
    _ = values row + 0 := congrArg (fun value : Canonical => values row + value) scaledZero
    _ = values row := by ring1

/-- Execute a finite number of original Euler steps from the supplied initial vector.

The successor consumes its own coefficient matrix and width once. No
geometric period, proposed terminal vector or matrix monodromy action is
used to define this independently constructed trace.
-/
@[expose] def trace {size : Nat} (coefficients : Nat → Matrix Canonical size) (widths : Nat → Rational)
    (initial : Vec Canonical size) : Nat → Vec Canonical size
  | 0 => initial
  | count + 1 =>
      let previous := trace coefficients widths initial count
      let matrix := coefficients count
      let width := widths count
      step matrix width previous

/-- The constructed trace retains the original initial vector at count zero. -/
theorem trace_zero {size : Nat} (coefficients : Nat → Matrix Canonical size) (widths : Nat → Rational)
    (initial : Vec Canonical size) : trace coefficients widths initial 0 = initial := rfl

/-- The constructed trace advances its actual preceding vector with the next original coefficient and width. -/
theorem trace_succ {size : Nat} (coefficients : Nat → Matrix Canonical size) (widths : Nat → Rational)
    (initial : Vec Canonical size) (count : Nat) :
    trace coefficients widths initial (count + 1) =
      step (coefficients count) (widths count) (trace coefficients widths initial count) := rfl

/-- A finite trace stays at its original initial vector when every original action annihilates that vector.

Only indices below the displayed finite count are constrained. No bound on
the widths or proposed endpoint is needed, including dimension zero.
-/
theorem trace_eq_of_action_zero {size : Nat} (coefficients : Nat → Matrix Canonical size)
    (widths : Nat → Rational) (initial : Vec Canonical size) (count : Nat)
    (zero : ∀ index, index < count → ∀ row, Matrix.Multiplication.matrixVector (coefficients index) initial row = 0) :
    trace coefficients widths initial count = initial := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have prior := ih (fun index before => zero index (Nat.lt_trans before (Nat.lt_succ_self count)))
    exact (trace_succ coefficients widths initial count).trans
      ((congrArg (step (coefficients count) (widths count)) prior).trans
        (step_eq_of_action_zero (coefficients count) (widths count) initial (zero count (Nat.lt_succ_self count))))

/-- The original homogeneous Euler step preserves the difference of two independent structural vectors. -/
theorem step_sub {size : Nat} (coefficients : Matrix Canonical size) (width : Rational)
    (left right : Vec Canonical size) :
    step coefficients width (zipWith (fun first last => first - last) left right) =
      zipWith (fun first last => first - last) (step coefficients width left) (step coefficients width right) := by
  apply vector_ext
  intro row
  have acted :
      Matrix.Multiplication.matrixVector coefficients (zipWith (fun first last => first - last) left right) row =
        Matrix.Multiplication.matrixVector coefficients left row -
          Matrix.Multiplication.matrixVector coefficients right row :=
    (congrArg (fun values : Vec Canonical size => values row)
      (Matrix.Multiplication.matrixVector_sub coefficients left right)).trans (zipWith_apply _ _ _ row)
  calc
    _ = (left row - right row) + scale width
        (Matrix.Multiplication.matrixVector coefficients left row -
          Matrix.Multiplication.matrixVector coefficients right row) :=
      (step_apply _ _ _ _).trans (congrArg₂ (fun value slope : Canonical => value + scale width slope)
        (zipWith_apply _ left right row) acted)
    _ = (left row + scale width (Matrix.Multiplication.matrixVector coefficients left row)) -
        (right row + scale width (Matrix.Multiplication.matrixVector coefficients right row)) := by
      rewrite [scale_sub]
      ring1
    _ = step coefficients width left row - step coefficients width right row :=
      congrArg₂ (fun first last : Canonical => first - last)
        (step_apply _ _ _ _).symm (step_apply _ _ _ _).symm
    _ = _ := (zipWith_apply _ _ _ row).symm

/-- A positive Euler width gives a squared-norm bound from the actual retained coefficient matrix.

The finite dimension and coefficient quadrance determine the growth
factor. Weighted addition pays the original vector and its one computed
matrix action without introducing a factor depending on the step count.
-/
theorem step_norm_le {size : Nat} (coefficients : Matrix Canonical size) (width : Rational)
    (positive : 0 < width) (values : Vec Canonical size) :
    Norm.vector (step coefficients width values) ≤
      (width + 1) * (1 + width * ((size : Rational) * Norm.matrix coefficients)) * Norm.vector values := by
  let derivative := Matrix.Multiplication.matrixVector coefficients values
  let scaled := map (scale width) derivative
  have same : Norm.vector (step coefficients width values) =
      Norm.vector (zipWith (fun first last => first + last) values scaled) :=
    Norm.vector_congr _ _ (fun row =>
      (step_apply _ _ _ row).trans
        ((congrArg (fun slope : Canonical => values row + slope)
          (map_apply (scale width) derivative row).symm).trans (zipWith_apply _ _ _ row).symm))
  have numeratorPositive : (0 : Rational) < width + 1 :=
    Order.Arithmetic.add_pos_of_pos_of_nonneg_direct positive (by decide +kernel)
  have weightNonnegative : (0 : Rational) ≤ (width + 1) / width :=
    (Order.Field.div_pos_direct numeratorPositive positive).le
  have quotient : ((width + 1) / width) * width ^ 2 = (width + 1) * width := by
    calc
      _ = (((width + 1) / width) * width) * width := by ring1
      _ = _ := congrArg (fun value : Rational => value * width)
        (Field.div_mul_cancel_of_ne (width + 1) width positive.ne')
  have paid := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Norm.matrixVector_le coefficients values)
    (Order.Arithmetic.mul_nonneg_direct weightNonnegative (Order.Arithmetic.sq_nonneg_direct width))
  calc
    _ ≤ (width + 1) * Norm.vector values + ((width + 1) / width) * Norm.vector scaled :=
      same.trans_le (Norm.vector_add_le_parameter width positive values scaled)
    _ = (width + 1) * Norm.vector values +
        (((width + 1) / width) * width ^ 2) * Norm.vector derivative := by
      rewrite [Norm.vector_scale]
      ring1
    _ ≤ (width + 1) * Norm.vector values +
        (((width + 1) / width) * width ^ 2) *
          ((size : Rational) * Norm.matrix coefficients * Norm.vector values) :=
      Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl _) paid
    _ = _ := by rewrite [quotient]; ring1

/-- Compute the actual one-step squared-error growth increment from the original matrix and width. -/
@[expose] def growth {size : Nat} (coefficients : Matrix Canonical size) (width : Rational) : Rational :=
  (width + 1) ^ 2 * (1 + width * ((size : Rational) * Norm.matrix coefficients)) - 1

/-- A nonnegative width gives nonnegative computed Euler growth, including a zero width or empty vector. -/
theorem growth_nonnegative {size : Nat} (coefficients : Matrix Canonical size) (width : Rational)
    (nonnegative : 0 ≤ width) : 0 ≤ growth coefficients width := by
  have cost : (0 : Rational) ≤ (size : Rational) * Norm.matrix coefficients :=
    Order.Arithmetic.mul_nonneg_direct
      (Cast.Order.natCast_le_direct (m := 0) (n := size) (Nat.zero_le size)) (Norm.matrix_nonnegative coefficients)
  have first : (0 : Rational) ≤ width * (2 + width) :=
    Order.Arithmetic.mul_nonneg_direct nonnegative
      ((show (0 : Rational) = 0 + 0 by ring1).trans_le
        (Order.Arithmetic.add_le_add_direct (by decide +kernel) nonnegative))
  have second : (0 : Rational) ≤ width * ((size : Rational) * Norm.matrix coefficients) * (width + 1) ^ 2 :=
    Order.Arithmetic.mul_nonneg_direct (Order.Arithmetic.mul_nonneg_direct nonnegative cost)
      (Order.Arithmetic.sq_nonneg_direct (width + 1))
  exact ((show (0 : Rational) = 0 + 0 by ring1).trans_le
    (Order.Arithmetic.add_le_add_direct first second)).trans_eq (by unfold growth; ring1)

/-- A width at most one gives a linear growth bound from any ceiling on the actual matrix quadrance.

The bound depends on the original finite dimension and coefficient ceiling,
not on a subdivision count. Its proof retains the nonnegative correction
`width * (1 - width) * (1 + cost * (width + 3))`.
-/
theorem growth_le {size : Nat} (coefficients : Matrix Canonical size) (width ceiling : Rational)
    (nonnegative : 0 ≤ width) (unit : width ≤ 1) (bounded : Norm.matrix coefficients ≤ ceiling) :
    growth coefficients width ≤ (3 + 4 * ((size : Rational) * ceiling)) * width := by
  have dimensionNonnegative : (0 : Rational) ≤ (size : Rational) :=
    Cast.Order.natCast_le_direct (m := 0) (n := size) (Nat.zero_le size)
  have costNonnegative : (0 : Rational) ≤ (size : Rational) * Norm.matrix coefficients :=
    Order.Arithmetic.mul_nonneg_direct dimensionNonnegative (Norm.matrix_nonnegative coefficients)
  have translated : (0 : Rational) ≤ width + 3 :=
    (show (0 : Rational) = 0 + 0 by ring1).trans_le
      (Order.Arithmetic.add_le_add_direct nonnegative (by decide +kernel))
  have lastNonnegative : (0 : Rational) ≤ 1 +
      ((size : Rational) * Norm.matrix coefficients) * (width + 3) :=
    (show (0 : Rational) = 0 + 0 by ring1).trans_le
      (Order.Arithmetic.add_le_add_direct (by decide +kernel)
        (Order.Arithmetic.mul_nonneg_direct costNonnegative translated))
  have correction := Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct nonnegative (Order.Arithmetic.sub_nonneg_direct unit)) lastNonnegative
  have linear : growth coefficients width ≤
      (3 + 4 * ((size : Rational) * Norm.matrix coefficients)) * width :=
    Order.Arithmetic.le_of_sub_nonneg_direct (correction.trans_eq (by unfold growth; ring1))
  have costBound := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded dimensionNonnegative
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct costBound (by decide +kernel : (0 : Rational) ≤ 4)
  exact linear.trans (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl _) scaled) nonnegative)

/-- The total computed growth is bounded by a fixed coefficient ceiling times the actual total width.

Every displayed width lies in the unit interval, and every original matrix
obeys the same ceiling. The conclusion is unchanged when more cells divide
that same total width.
-/
theorem growth_sum_le {size : Nat} (coefficients : Nat → Matrix Canonical size) (widths : Nat → Rational)
    (ceiling : Rational) (count : Nat)
    (nonnegative : ∀ index, index < count → 0 ≤ widths index)
    (unit : ∀ index, index < count → widths index ≤ 1)
    (bounded : ∀ index, index < count → Norm.matrix (coefficients index) ≤ ceiling) :
    Prefix.coordinateSum (fun index => growth (coefficients index) (widths index)) count ≤
      (3 + 4 * ((size : Rational) * ceiling)) * Prefix.coordinateSum widths count := by
  induction count with
  | zero =>
    change (0 : Rational) ≤ (3 + 4 * ((size : Rational) * ceiling)) * 0
    rewrite [show (3 + 4 * ((size : Rational) * ceiling)) * 0 = 0 by ring1]
    exact Order.Basic.le_refl _
  | succ count ih =>
    have prior := ih
      (fun index before => nonnegative index (Nat.lt_trans before (Nat.lt_succ_self count)))
      (fun index before => unit index (Nat.lt_trans before (Nat.lt_succ_self count)))
      (fun index before => bounded index (Nat.lt_trans before (Nat.lt_succ_self count)))
    have last := growth_le (coefficients count) (widths count) ceiling
      (nonnegative count (Nat.lt_succ_self count)) (unit count (Nat.lt_succ_self count))
      (bounded count (Nat.lt_succ_self count))
    exact (Order.Arithmetic.add_le_add_direct prior last).trans_eq
      (by rewrite [Prefix.coordinateSum_succ]; ring1)

/-- Compute the local defect of an independently supplied next vector against its own original Euler step. -/
@[expose] def defect {size : Nat} (coefficients : Matrix Canonical size) (width : Rational)
    (current next : Vec Canonical size) : Vec Canonical size :=
  zipWith (fun first last => first - last) next (step coefficients width current)

/-- The actual original trace has zero local defect at every retained step, for arbitrary widths. -/
theorem trace_defect_eq_zero {size : Nat} (coefficients : Nat → Matrix Canonical size)
    (widths : Nat → Rational) (initial : Vec Canonical size) (index : Nat) :
    Norm.vector (defect (coefficients index) (widths index)
      (trace coefficients widths initial index) (trace coefficients widths initial (index + 1))) = 0 := by
  unfold defect
  rewrite [trace_succ]
  unfold Norm.vector
  exact (sumFin_congr (fun row =>
    (congrArg Data.Gaussian.Norm.Basic.normSq ((zipWith_apply _ _ _ row).trans
      (Data.Gaussian.Basic.sub_self _))).trans Data.Gaussian.Norm.Basic.normSq_zero)).trans sumFin_zero

/-- Actual Euler errors satisfy an affine local recurrence with the computed growth and the same local defect. -/
private theorem local_error_le {size : Nat} (coefficients : Matrix Canonical size) (width : Rational)
    (positive : 0 < width) (current next approximate : Vec Canonical size) :
    Norm.vector (zipWith (fun first last => first - last) next (step coefficients width approximate)) ≤
      (1 + growth coefficients width) *
          Norm.vector (zipWith (fun first last => first - last) current approximate) +
        ((width + 1) / width) * Norm.vector (defect coefficients width current next) := by
  let difference := zipWith (fun first last => first - last) current approximate
  let remainder := defect coefficients width current next
  have acted (row : Fin size) : step coefficients width difference row =
      step coefficients width current row - step coefficients width approximate row :=
    (congrArg (fun values : Vec Canonical size => values row) (step_sub coefficients width current approximate)).trans
      (zipWith_apply _ _ _ row)
  have same :
      Norm.vector (zipWith (fun first last => first - last) next (step coefficients width approximate)) =
        Norm.vector (zipWith (fun first last => first + last) (step coefficients width difference) remainder) :=
    Norm.vector_congr _ _ (fun row => by
      calc
        _ = next row - step coefficients width approximate row := zipWith_apply _ _ _ row
        _ = (step coefficients width current row - step coefficients width approximate row) +
            (next row - step coefficients width current row) := by ring1
        _ = step coefficients width difference row + remainder row :=
          congrArg₂ (fun first last : Canonical => first + last) (acted row).symm (zipWith_apply _ _ _ row).symm
        _ = _ := (zipWith_apply _ _ _ row).symm)
  have weightNonnegative : (0 : Rational) ≤ width + 1 :=
    (show (0 : Rational) = 0 + 0 by ring1).trans_le
      (Order.Arithmetic.add_le_add_direct positive.le (by decide +kernel))
  have paid := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (step_norm_le coefficients width positive difference) weightNonnegative
  calc
    _ ≤ (width + 1) * Norm.vector (step coefficients width difference) +
        ((width + 1) / width) * Norm.vector remainder :=
      same.trans_le (Norm.vector_add_le_parameter width positive (step coefficients width difference) remainder)
    _ ≤ (width + 1) * ((width + 1) *
        (1 + width * ((size : Rational) * Norm.matrix coefficients)) * Norm.vector difference) +
        ((width + 1) / width) * Norm.vector remainder :=
      Order.Arithmetic.add_le_add_right_direct paid _
    _ = _ := by unfold growth; ring1

/-- Local fourth-order quadrance defects give a finite whole-trace stability bound independent of the step count.

Both the independent sample trace and the constructed Euler trace retain
their original vectors. Positive widths, nonnegative actual remainder
factors and a total computed growth at most one half suffice. The bound
uses the original initial discrepancy and the sum of the cubic local costs;
no desired endpoint agreement or differential-equation identity is input.
-/
theorem stability {size : Nat} (coefficients : Nat → Matrix Canonical size) (widths factors : Nat → Rational)
    (initial : Vec Canonical size) (samples : Nat → Vec Canonical size) (count : Nat)
    (positive : ∀ index, index < count → 0 < widths index)
    (factorNonnegative : ∀ index, index < count → 0 ≤ factors index)
    (small : Prefix.coordinateSum (fun index => growth (coefficients index) (widths index)) count ≤
      (1 / 2 : Rational))
    (remainders : ∀ index, index < count →
      Norm.vector (defect (coefficients index) (widths index) (samples index) (samples (index + 1))) ≤
        factors index * widths index ^ 4) :
    Norm.vector (zipWith (fun first last => first - last) (samples count) (trace coefficients widths initial count)) ≤
      2 * (Norm.vector (zipWith (fun first last => first - last) (samples 0) initial) +
        Prefix.coordinateSum
          (fun index => factors index * (widths index + 1) * widths index ^ 3) count) := by
  let errors := fun index => Norm.vector
    (zipWith (fun first last => first - last) (samples index) (trace coefficients widths initial index))
  let rates := fun index => growth (coefficients index) (widths index)
  let forcing := fun index => factors index * (widths index + 1) * widths index ^ 3
  let initialError := Norm.vector (zipWith (fun first last => first - last) (samples 0) initial)
  have rateNonnegative (index : Nat) (before : index < count) : (0 : Rational) ≤ rates index :=
    growth_nonnegative (coefficients index) (widths index) (positive index before).le
  have forcingNonnegative (index : Nat) (before : index < count) : (0 : Rational) ≤ forcing index := by
    have widthNonnegative := (positive index before).le
    have cubic : (0 : Rational) ≤ widths index ^ 3 :=
      (Order.Arithmetic.mul_nonneg_direct
        (Order.Arithmetic.mul_nonneg_direct widthNonnegative widthNonnegative) widthNonnegative).trans_eq (by ring1)
    exact Order.Arithmetic.mul_nonneg_direct
      (Order.Arithmetic.mul_nonneg_direct (factorNonnegative index before)
        ((show (0 : Rational) = 0 + 0 by ring1).trans_le
          (Order.Arithmetic.add_le_add_direct widthNonnegative (by decide +kernel)))) cubic
  have steps (index : Nat) (before : index < count) :
      errors (index + 1) ≤ (1 + rates index) * errors index + forcing index := by
    have numeratorPositive : (0 : Rational) < widths index + 1 :=
      Order.Arithmetic.add_pos_of_pos_of_nonneg_direct (positive index before) (by decide +kernel)
    have quotientNonnegative : (0 : Rational) ≤ (widths index + 1) / widths index :=
      (Order.Field.div_pos_direct numeratorPositive (positive index before)).le
    have paid := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (remainders index before) quotientNonnegative
    have cancel : ((widths index + 1) / widths index) * (factors index * widths index ^ 4) = forcing index := by
      calc
        _ = ((((widths index + 1) / widths index) * widths index) * factors index) * widths index ^ 3 := by ring1
        _ = ((widths index + 1) * factors index) * widths index ^ 3 :=
          congrArg (fun value : Rational => (value * factors index) * widths index ^ 3)
            (Field.div_mul_cancel_of_ne (widths index + 1) (widths index) (positive index before).ne')
        _ = _ := by unfold forcing; ring1
    exact (local_error_le (coefficients index) (widths index) (positive index before)
      (samples index) (samples (index + 1)) (trace coefficients widths initial index)).trans
      ((Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl _) paid).trans_eq
        (congrArg (fun value : Rational => (1 + rates index) * errors index + value) cancel))
  exact Algebra.Recurrence.Affine.short_interval_stability rates forcing errors initialError count
    (Norm.vector_nonnegative _) (Order.Basic.le_refl _) rateNonnegative forcingNonnegative small steps

/-- A fixed coefficient ceiling and total-width payment derive the finite Euler stability condition internally.

Local fourth-order defects retain the same actual sample vectors and
factors. The original total width pays the computed growth, so refining
the partition introduces no additional smallness assumption on its count.
-/
theorem stability_of_total_width {size : Nat} (coefficients : Nat → Matrix Canonical size)
    (widths factors : Nat → Rational) (initial : Vec Canonical size) (samples : Nat → Vec Canonical size)
    (ceiling : Rational) (count : Nat)
    (positive : ∀ index, index < count → 0 < widths index)
    (unit : ∀ index, index < count → widths index ≤ 1)
    (bounded : ∀ index, index < count → Norm.matrix (coefficients index) ≤ ceiling)
    (factorNonnegative : ∀ index, index < count → 0 ≤ factors index)
    (small : (3 + 4 * ((size : Rational) * ceiling)) * Prefix.coordinateSum widths count ≤
      (1 / 2 : Rational))
    (remainders : ∀ index, index < count →
      Norm.vector (defect (coefficients index) (widths index) (samples index) (samples (index + 1))) ≤
        factors index * widths index ^ 4) :
    Norm.vector (zipWith (fun first last => first - last) (samples count) (trace coefficients widths initial count)) ≤
      2 * (Norm.vector (zipWith (fun first last => first - last) (samples 0) initial) +
        Prefix.coordinateSum
          (fun index => factors index * (widths index + 1) * widths index ^ 3) count) :=
  stability coefficients widths factors initial samples count positive factorNonnegative
    ((growth_sum_le coefficients widths ceiling count (fun index before => (positive index before).le)
      unit bounded).trans small) remainders

end Purelib.Calculus.Linear.Euler

end
