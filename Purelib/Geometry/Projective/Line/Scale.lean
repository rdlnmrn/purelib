module

public import Purelib.Geometry.Projective.Line.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

/-!
# Common scales for homogeneous coordinate pairs

Valid pairs are related by cross multiplication. A decidable coordinate chart
recovers a nonzero common scale and exact equality of the original pairs.
-/

public section

namespace Purelib.Geometry.Projective.Line.Proj

open Purelib.Algebra.Field (ExplicitField)

/-- A homogeneous coordinate pair is valid when at least one coordinate is nonzero. -/
@[expose] def Nonzero [Zero K] (point : Proj K) : Prop := point.p ≠ 0 ∨ point.q ≠ 0

/-- Multiply both homogeneous coordinates by the same scalar. -/
@[expose] def scale [Mul K] (factor : K) (point : Proj K) : Proj K :=
  ⟨factor * point.p, factor * point.q⟩

/-- A nonzero scalar preserves nonzeroness of the original homogeneous pair. -/
theorem scale_nonzero [ExplicitField K] {point : Proj K} {factor : K}
    (factorNonzero : factor ≠ 0) (pointNonzero : point.Nonzero) : (point.scale factor).Nonzero := by
  rcases pointNonzero with first | second
  · exact Or.inl (ExplicitField.mul_ne_zero factorNonzero first)
  · exact Or.inr (ExplicitField.mul_ne_zero factorNonzero second)

/-- Successive homogeneous-pair scaling multiplies the two supplied coefficients. -/
theorem scale_scale [CommRing K] (point : Proj K) (first second : K) :
    (point.scale first).scale second = point.scale (second * first) := by
  apply Proj.ext <;> unfold scale <;> ring1

/-- Scaling a homogeneous pair by one preserves both original coordinates. -/
theorem scale_one [CommRing K] (point : Proj K) : point.scale 1 = point := by
  apply Proj.ext <;> exact one_mul _

/-- A common coordinate scale preserves projective cross-multiplication equivalence. -/
theorem equivalent_scale [CommRing K] (point : Proj K) (factor : K) :
    point.Equivalent (point.scale factor) := by
  unfold Equivalent scale
  ring1

/-- A scale producing a valid homogeneous pair must itself be nonzero. -/
theorem factor_ne_zero_of_eq_scale [CommRing K] {left right : Proj K} {factor : K}
    (rightNonzero : right.Nonzero) (represents : right = left.scale factor) : factor ≠ 0 := by
  intro factorZero
  rcases rightNonzero with firstNonzero | secondNonzero
  · apply firstNonzero
    have coordinates := congrArg Proj.p represents
    change right.p = factor * left.p at coordinates
    rw [factorZero, zero_mul] at coordinates
    exact coordinates

  · apply secondNonzero
    have coordinates := congrArg Proj.q represents
    change right.q = factor * left.q at coordinates
    rw [factorZero, zero_mul] at coordinates
    exact coordinates

/-- Equal scaled homogeneous pairs have equivalent original coordinates when the left scale is nonzero.

Scalar cancellation proves cross multiplication directly. The right scale
may be zero; no nonzero-coordinate chart or selected witness is needed.
-/
theorem equivalent_of_scale_eq_scale [ExplicitField K] (left right : Proj K)
    (leftScale rightScale : K) (leftNonzero : leftScale ≠ 0)
    (equal : left.scale leftScale = right.scale rightScale) : left.Equivalent right := by
  have first := congrArg Proj.p equal
  have second := congrArg Proj.q equal
  change left.p * right.q = right.p * left.q
  apply ExplicitField.eq_of_mul_eq_mul_left leftNonzero
  calc
    leftScale * (left.p * right.q) = (leftScale * left.p) * right.q := by ring1
    _ = (rightScale * right.p) * right.q := congrArg (fun value => value * right.q) first
    _ = right.p * (rightScale * right.q) := by ring1
    _ = right.p * (leftScale * left.q) := congrArg (fun value => right.p * value) second.symm
    _ = leftScale * (right.p * left.q) := by ring1

/-- A nonzero scale on the first homogeneous pair preserves and reflects cross-multiplication equivalence. -/
theorem equivalent_scale_left_iff [ExplicitField K] (left right : Proj K)
    (factor : K) (factorNonzero : factor ≠ 0) :
    (left.scale factor).Equivalent right ↔ left.Equivalent right := by
  constructor
  · intro equivalent
    change (factor * left.p) * right.q = right.p * (factor * left.q) at equivalent
    change left.p * right.q = right.p * left.q
    apply ExplicitField.eq_of_mul_eq_mul_left factorNonzero
    calc
      factor * (left.p * right.q) = (factor * left.p) * right.q := by ring1
      _ = right.p * (factor * left.q) := equivalent
      _ = factor * (right.p * left.q) := by ring1
  · intro equivalent
    change left.p * right.q = right.p * left.q at equivalent
    change (factor * left.p) * right.q = right.p * (factor * left.q)
    calc
      (factor * left.p) * right.q = factor * (left.p * right.q) := by ring1
      _ = factor * (right.p * left.q) := congrArg (fun value => factor * value) equivalent
      _ = right.p * (factor * left.q) := by ring1

/-- Construct the nonzero common scale between equivalent valid homogeneous pairs.

The first nonzero coordinate of the original left pair determines the chart.
The returned scale and equality relate the two supplied pairs directly.
-/
@[expose] def scaleWitness [ExplicitField K] [DecidableEq K] (left right : Proj K)
    (leftNonzero : left.Nonzero) (rightNonzero : right.Nonzero)
    (equivalent : left.Equivalent right) :
    Σ' factor : K, factor ≠ 0 ∧ right = left.scale factor := by
  change left.p * right.q = right.p * left.q at equivalent
  by_cases firstNonzero : left.p ≠ 0
  · let factor := right.p / left.p
    have firstEqual : right.p = factor * left.p :=
      (ExplicitField.div_mul_cancel right.p firstNonzero).symm
    have secondEqual : right.q = factor * left.q := by
      apply ExplicitField.eq_of_mul_eq_mul_left firstNonzero
      calc
        left.p * right.q = right.p * left.q := equivalent
        _ = left.p * (factor * left.q) := by rw [firstEqual]; ring1
    have represents : right = left.scale factor := by
      apply Proj.ext
      · exact firstEqual
      · exact secondEqual
    exact ⟨factor, factor_ne_zero_of_eq_scale rightNonzero represents, represents⟩
  · have firstZero : left.p = 0 := Decidable.byContradiction firstNonzero
    have secondNonzero : left.q ≠ 0 := by
      rcases leftNonzero with firstNonzero | secondNonzero
      · exact False.elim (firstNonzero firstZero)
      · exact secondNonzero
    have rightFirstZero : right.p = 0 := by
      apply ExplicitField.eq_zero_of_mul_eq_zero_right secondNonzero
      calc
        right.p * left.q = left.p * right.q := equivalent.symm
        _ = 0 := by rw [firstZero, zero_mul]
    let factor := right.q / left.q
    have represents : right = left.scale factor := by
      apply Proj.ext
      · change right.p = factor * left.p
        rw [rightFirstZero, firstZero, mul_zero]
      · exact (ExplicitField.div_mul_cancel right.q secondNonzero).symm
    exact ⟨factor, factor_ne_zero_of_eq_scale rightNonzero represents, represents⟩

end Purelib.Geometry.Projective.Line.Proj

end
