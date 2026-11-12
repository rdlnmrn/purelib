module

public import Purelib.Curves.Legendre.Periods.Jets.Connection.Euler
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Algebra.FiniteSum.Fin
import Purelib.LinearAlgebra.Gaussian.Norm
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Euler quadrance bounds from stronger estimates on original remainders

The entries keep their original base/output/slope/remainder/factor fields.
Separate proved estimates on those SAME remainders can sharpen the actual
Euler defect. The original sourceSlope_le derives the connection payment
at the same jet, original stage and retained finite selection.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Connection

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin_succ)
open Purelib.Approximation.Rational.Geometric
open Purelib.Calculus.Jet.Quadratic.Basic (Certificate)
open Purelib.Calculus.Linear
open Purelib.Curves.Legendre.PicardFuchs.Clearance (ParameterClearance)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Scale (scale normSq_scale scale_mul_product)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order.Arithmetic
open Purelib.Data.Vector (map)
open Purelib.Data.Vector.Basic (map_apply zipWith_apply)
open Purelib.LinearAlgebra.Gaussian
open Purelib.LinearAlgebra.Matrix.Multiplication

/-- Stronger estimates on the same original Taylor remainders bound their actual local Euler defect.

The actual source jet, two original entries, endpoint vectors and finite
connection selection are retained. The row estimates concern only those
same remainder values; no field is changed and no final Euler or connection
comparison is supplied. Rational width and Gaussian direction keep their
separate norm factors, including zero widths and zero directions whenever
the original entry and selection indices admit those cases.
-/
theorem eulerDefect_le_of_remainders {parameter increment : Canonical} {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) (width : Rational) (direction : Canonical)
    (scaled : increment = scale width direction) (start index : Nat)
    (selection : Search.Selection 1 start
      (width ^ 2 * (ParameterClearance.ofFrame frame).connectionLowerSq))
    (after : selection.stage ≤ index) (entries : Vec (Certificate increment) 2)
    (base_eq : ∀ coordinate, (entries coordinate).base =
      ((jet.value coordinate).integral.model index).integralSample)
    (slope_eq : ∀ coordinate, (entries coordinate).slope =
      ((jet.first coordinate).integral.model index).integralSample)
    (factors : Fin 2 → Rational)
    (remainders : ∀ row, Norm.Basic.normSq (entries row).remainder ≤
      factors row * Norm.Basic.normSq increment ^ 2) :
    Norm.vector (Euler.defect (alongMatrix parameter direction) width
      (map Certificate.base entries) (map Certificate.output entries)) ≤
      2 * ((factors 0 + factors 1) * Norm.Basic.normSq direction ^ 2 +
        2 * Norm.Basic.normSq direction) * width ^ 4 := by
  let values := map Certificate.base entries
  have values_eq (coordinate : Fin 2) : values coordinate =
      ((jet.value coordinate).integral.model index).integralSample :=
    (map_apply Certificate.base entries coordinate).trans (base_eq coordinate)
  have incrementNorm : Norm.Basic.normSq increment = width ^ 2 * Norm.Basic.normSq direction :=
    (congrArg Norm.Basic.normSq scaled).trans (normSq_scale width direction)
  have rows (row : Fin 2) :
      Norm.Basic.normSq (Euler.defect (alongMatrix parameter direction) width values
        (map Certificate.output entries) row) ≤
        2 * (factors row * Norm.Basic.normSq direction ^ 2 + Norm.Basic.normSq direction) * width ^ 4 := by
    let acted := matrixVector (matrix parameter) values row
    have slopeBound := sourceSlope_le jet width start index selection after values (entries row).slope row
      values_eq (slope_eq row)
    have movement : scale width (direction * acted) = increment * acted :=
      (scale_mul_product width direction acted).trans (congrArg (fun value : Canonical => value * acted) scaled.symm)
    have exactRow : Euler.defect (alongMatrix parameter direction) width values
        (map Certificate.output entries) row =
        (entries row).remainder + increment * ((entries row).slope - acted) := by
      unfold Euler.defect
      rewrite [zipWith_apply, map_apply, Euler.step_apply, alongMatrix_vector, movement]
      have original := (entries row).expansion
      change (entries row).output - (values row + increment * acted) = _
      rewrite [show values row = (entries row).base from map_apply Certificate.base entries row]
      exact (show (entries row).output - ((entries row).base + increment * acted) =
        ((entries row).output - (entries row).base - increment * (entries row).slope) +
          increment * ((entries row).slope - acted) by ring1).trans
            (congrArg (fun value : Canonical => value + increment * ((entries row).slope - acted)) original)
    have original : Norm.Basic.normSq (entries row).remainder ≤
        factors row * Norm.Basic.normSq increment ^ 2 := remainders row
    have remainderBound : Norm.Basic.normSq (entries row).remainder ≤
        factors row * Norm.Basic.normSq direction ^ 2 * width ^ 4 :=
      original.trans_eq ((congrArg (fun value : Rational => factors row * value ^ 2)
        incrementNorm).trans (by ring1))
    have slopeContribution : Norm.Basic.normSq (increment * ((entries row).slope - acted)) ≤
        Norm.Basic.normSq direction * width ^ 4 :=
      (Norm.Basic.normSq_mul _ _).trans_le
        ((mul_le_mul_of_nonneg_left_direct slopeBound (Norm.Basic.normSq_nonneg increment)).trans_eq
          ((congrArg (fun value : Rational => value * width ^ 2) incrementNorm).trans (by ring1)))
    exact (congrArg Norm.Basic.normSq exactRow).trans_le
      ((Norm.Bounds.normSq_add_le_two _ _).trans
        ((mul_le_mul_of_nonneg_left_direct (add_le_add_direct remainderBound slopeContribution)
          (by decide : (0 : Rational) ≤ 2)).trans_eq (by ring1)))
  have summed := add_le_add_direct (rows 0) (rows 1)
  have same : Norm.vector (Euler.defect (alongMatrix parameter direction) width values
      (map Certificate.output entries)) =
      Norm.Basic.normSq (Euler.defect (alongMatrix parameter direction) width values
        (map Certificate.output entries) 0) +
      Norm.Basic.normSq (Euler.defect (alongMatrix parameter direction) width values
        (map Certificate.output entries) 1) := by
    unfold Norm.vector
    rewrite [sumFin_succ, sumFin_succ]
    let actual := Euler.defect (alongMatrix parameter direction) width values (map Certificate.output entries)
    change Norm.Basic.normSq (actual 0) + (Norm.Basic.normSq (actual 1) + 0) =
      Norm.Basic.normSq (actual 0) + Norm.Basic.normSq (actual 1)
    ring1
  exact same.trans_le (summed.trans_eq (by ring1))

end Purelib.Curves.Legendre.Periods.Jets.Connection

end
