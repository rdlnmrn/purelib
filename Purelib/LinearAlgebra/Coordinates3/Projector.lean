module

import Purelib.Algebra.Field.Characteristic.Nonzero

import Purelib.Algebra.Group.Basic
import Purelib.Algebra.Field.ExplicitField
public import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Algebra.Field.Inverse
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Symmetric rank-one projector rows

The retained matrix supplies symmetry, idempotence, trace one and a vanishing
adjugate. Its diagonal tests select the original first nonzero row and retain
the normalized self-outer-product certificate for that same matrix.
-/

namespace Purelib.LinearAlgebra.Coordinates3.Projector
public section
open Purelib.Algebra
open Purelib.Algebra.Field
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K]

/-- The quadrance of row `t` of a symmetric idempotent equals its diagonal entry. -/
private theorem rowT_quadrance_of_idempotent
    (matrix : Coordinates3.Matrix3 K) (symmetric : matrix.IsSymmetric)
    (idempotent : Coordinates3.Matrix3.mul matrix matrix = matrix) :
    (Coordinates3.Matrix3.rowT matrix).quadrance = matrix.tt := by
  have coordinate := congrArg Coordinates3.Matrix3.tt idempotent
  unfold Coordinates3.Matrix3.mul at coordinate
  rw [Purelib.LinearAlgebra.Coordinates3.Matrix3.symmetric_rt_eq_tr matrix symmetric,
    Purelib.LinearAlgebra.Coordinates3.Matrix3.symmetric_st_eq_ts matrix symmetric] at coordinate
  unfold Coordinates3.Matrix3.rowT Vector3.quadrance Vector3.dot
  exact coordinate

/-- The quadrance of row `r` of a symmetric idempotent equals its diagonal entry. -/
private theorem rowR_quadrance_of_idempotent
    (matrix : Coordinates3.Matrix3 K) (symmetric : matrix.IsSymmetric)
    (idempotent : Coordinates3.Matrix3.mul matrix matrix = matrix) :
    (Coordinates3.Matrix3.rowR matrix).quadrance = matrix.rr := by
  have coordinate := congrArg Coordinates3.Matrix3.rr idempotent
  unfold Coordinates3.Matrix3.mul at coordinate
  rw [← Purelib.LinearAlgebra.Coordinates3.Matrix3.symmetric_rt_eq_tr matrix symmetric,
    Purelib.LinearAlgebra.Coordinates3.Matrix3.symmetric_sr_eq_rs matrix symmetric] at coordinate
  unfold Coordinates3.Matrix3.rowR Vector3.quadrance Vector3.dot
  exact coordinate

/-- The quadrance of row `s` of a symmetric idempotent equals its diagonal entry. -/
private theorem rowS_quadrance_of_idempotent
    (matrix : Coordinates3.Matrix3 K) (symmetric : matrix.IsSymmetric)
    (idempotent : Coordinates3.Matrix3.mul matrix matrix = matrix) :
    (Coordinates3.Matrix3.rowS matrix).quadrance = matrix.ss := by
  have coordinate := congrArg Coordinates3.Matrix3.ss idempotent
  unfold Coordinates3.Matrix3.mul at coordinate
  rw [← Purelib.LinearAlgebra.Coordinates3.Matrix3.symmetric_st_eq_ts matrix symmetric,
    ← Purelib.LinearAlgebra.Coordinates3.Matrix3.symmetric_sr_eq_rs matrix symmetric] at coordinate
  unfold Coordinates3.Matrix3.rowS Vector3.quadrance Vector3.dot
  exact coordinate

/-- Reconstruct a symmetric idempotent from row `t` and its nonzero diagonal entry.

The vanishing adjugate supplies the required rank-one minor identities. -/
private theorem reconstruct_from_rowT (matrix : Coordinates3.Matrix3 K)
    (symmetric : matrix.IsSymmetric)
    (idempotent : Coordinates3.Matrix3.mul matrix matrix = matrix)
    (adjugateZero : Coordinates3.Matrix3.adjugate matrix = Coordinates3.Matrix3.zero)
    (pivotNonzero : matrix.tt ≠ 0) :
    matrix = Coordinates3.Matrix3.scale (1 / (Coordinates3.Matrix3.rowT matrix).quadrance)
      (Coordinates3.Matrix3.outer (Coordinates3.Matrix3.rowT matrix) (Coordinates3.Matrix3.rowT matrix)) := by
  have rtEq := Purelib.LinearAlgebra.Coordinates3.Matrix3.symmetric_rt_eq_tr matrix symmetric
  have stEq := Purelib.LinearAlgebra.Coordinates3.Matrix3.symmetric_st_eq_ts matrix symmetric
  have srEq := Purelib.LinearAlgebra.Coordinates3.Matrix3.symmetric_sr_eq_rs matrix symmetric
  have rrMinor := congrArg Coordinates3.Matrix3.ss adjugateZero
  unfold Coordinates3.Matrix3.adjugate at rrMinor
  unfold Coordinates3.Matrix3.zero at rrMinor
  rw [rtEq] at rrMinor
  have rrRelation : matrix.tt * matrix.rr = matrix.tr * matrix.tr :=
    Group.eq_of_sub_eq_zero rrMinor
  have rsMinor := congrArg Coordinates3.Matrix3.sr adjugateZero
  unfold Coordinates3.Matrix3.adjugate at rsMinor
  unfold Coordinates3.Matrix3.zero at rsMinor
  rw [stEq, srEq] at rsMinor
  have rsRelation : matrix.tt * matrix.rs = matrix.tr * matrix.ts :=
    (Group.eq_of_sub_eq_zero rsMinor).symm
  have ssMinor := congrArg Coordinates3.Matrix3.rr adjugateZero
  unfold Coordinates3.Matrix3.adjugate at ssMinor
  unfold Coordinates3.Matrix3.zero at ssMinor
  rw [stEq] at ssMinor
  have ssRelation : matrix.tt * matrix.ss = matrix.ts * matrix.ts :=
    Group.eq_of_sub_eq_zero ssMinor
  rw [Purelib.LinearAlgebra.Coordinates3.Projector.rowT_quadrance_of_idempotent matrix symmetric idempotent]
  apply Coordinates3.Matrix3.ext
  all_goals
    unfold Coordinates3.Matrix3.scale
    unfold Coordinates3.Matrix3.outer
    unfold Coordinates3.Matrix3.rowT
  · apply Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero
    ring1
  · apply Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero
    ring1
  · apply Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero
    ring1
  · apply Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero
    rw [rtEq]
    ring1
  · exact Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero rrRelation
  · exact Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero rsRelation
  · apply Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero
    rw [stEq]
    ring1
  · apply Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero
    rw [srEq]
    calc
      matrix.tt * matrix.rs = matrix.tr * matrix.ts := rsRelation
      _ = matrix.ts * matrix.tr := by ring1
  · exact Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero ssRelation

/-- Reconstruct a symmetric idempotent from row `r` and its nonzero diagonal entry.

The vanishing adjugate supplies the required rank-one minor identities. -/
private theorem reconstruct_from_rowR (matrix : Coordinates3.Matrix3 K)
    (symmetric : matrix.IsSymmetric)
    (idempotent : Coordinates3.Matrix3.mul matrix matrix = matrix)
    (adjugateZero : Coordinates3.Matrix3.adjugate matrix = Coordinates3.Matrix3.zero)
    (pivotNonzero : matrix.rr ≠ 0) :
    matrix = Coordinates3.Matrix3.scale (1 / (Coordinates3.Matrix3.rowR matrix).quadrance)
      (Coordinates3.Matrix3.outer (Coordinates3.Matrix3.rowR matrix) (Coordinates3.Matrix3.rowR matrix)) := by
  have rtEq := Purelib.LinearAlgebra.Coordinates3.Matrix3.symmetric_rt_eq_tr matrix symmetric
  have stEq := Purelib.LinearAlgebra.Coordinates3.Matrix3.symmetric_st_eq_ts matrix symmetric
  have srEq := Purelib.LinearAlgebra.Coordinates3.Matrix3.symmetric_sr_eq_rs matrix symmetric
  have ttMinor := congrArg Coordinates3.Matrix3.ss adjugateZero
  unfold Coordinates3.Matrix3.adjugate at ttMinor
  unfold Coordinates3.Matrix3.zero at ttMinor
  rw [rtEq] at ttMinor
  have ttRelation : matrix.rr * matrix.tt = matrix.rt * matrix.rt := by
    calc
      matrix.rr * matrix.tt = matrix.tt * matrix.rr := by ring1
      _ = matrix.tr * matrix.tr := Group.eq_of_sub_eq_zero ttMinor
      _ = matrix.rt * matrix.rt := by rw [rtEq]
  have tsMinor := congrArg Coordinates3.Matrix3.ts adjugateZero
  unfold Coordinates3.Matrix3.adjugate at tsMinor
  unfold Coordinates3.Matrix3.zero at tsMinor
  rw [rtEq] at tsMinor
  have tsRelation : matrix.rr * matrix.ts = matrix.rt * matrix.rs := by
    calc
      matrix.rr * matrix.ts = matrix.ts * matrix.rr := by ring1
      _ = matrix.tr * matrix.rs := (Group.eq_of_sub_eq_zero tsMinor).symm
      _ = matrix.rt * matrix.rs := by rw [rtEq]
  have ssMinor := congrArg Coordinates3.Matrix3.tt adjugateZero
  unfold Coordinates3.Matrix3.adjugate at ssMinor
  unfold Coordinates3.Matrix3.zero at ssMinor
  rw [srEq] at ssMinor
  have ssRelation : matrix.rr * matrix.ss = matrix.rs * matrix.rs :=
    Group.eq_of_sub_eq_zero ssMinor
  rw [Purelib.LinearAlgebra.Coordinates3.Projector.rowR_quadrance_of_idempotent matrix symmetric idempotent]
  apply Coordinates3.Matrix3.ext
  all_goals
    unfold Coordinates3.Matrix3.scale
    unfold Coordinates3.Matrix3.outer
    unfold Coordinates3.Matrix3.rowR
  · exact Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero ttRelation
  · apply Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero
    rw [rtEq]
    ring1
  · exact Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero tsRelation
  · apply Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero
    ring1
  · apply Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero
    ring1
  · apply Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero
    ring1
  · apply Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero
    rw [stEq]
    calc
      matrix.rr * matrix.ts = matrix.rt * matrix.rs := tsRelation
      _ = matrix.rs * matrix.rt := by ring1
  · apply Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero
    rw [srEq]
    ring1
  · exact Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero ssRelation

/-- Reconstruct a symmetric idempotent from row `s` and its nonzero diagonal entry.

The vanishing adjugate supplies the required rank-one minor identities. -/
private theorem reconstruct_from_rowS (matrix : Coordinates3.Matrix3 K)
    (symmetric : matrix.IsSymmetric)
    (idempotent : Coordinates3.Matrix3.mul matrix matrix = matrix)
    (adjugateZero : Coordinates3.Matrix3.adjugate matrix = Coordinates3.Matrix3.zero)
    (pivotNonzero : matrix.ss ≠ 0) :
    matrix = Coordinates3.Matrix3.scale (1 / (Coordinates3.Matrix3.rowS matrix).quadrance)
      (Coordinates3.Matrix3.outer (Coordinates3.Matrix3.rowS matrix) (Coordinates3.Matrix3.rowS matrix)) := by
  have rtEq := Purelib.LinearAlgebra.Coordinates3.Matrix3.symmetric_rt_eq_tr matrix symmetric
  have stEq := Purelib.LinearAlgebra.Coordinates3.Matrix3.symmetric_st_eq_ts matrix symmetric
  have srEq := Purelib.LinearAlgebra.Coordinates3.Matrix3.symmetric_sr_eq_rs matrix symmetric
  have ttMinor := congrArg Coordinates3.Matrix3.rr adjugateZero
  unfold Coordinates3.Matrix3.adjugate at ttMinor
  unfold Coordinates3.Matrix3.zero at ttMinor
  rw [stEq] at ttMinor
  have ttRelation : matrix.ss * matrix.tt = matrix.st * matrix.st := by
    calc
      matrix.ss * matrix.tt = matrix.tt * matrix.ss := by ring1
      _ = matrix.ts * matrix.ts := Group.eq_of_sub_eq_zero ttMinor
      _ = matrix.st * matrix.st := by rw [stEq]
  have trMinor := congrArg Coordinates3.Matrix3.tr adjugateZero
  unfold Coordinates3.Matrix3.adjugate at trMinor
  unfold Coordinates3.Matrix3.zero at trMinor
  rw [stEq] at trMinor
  have trRelation : matrix.ss * matrix.tr = matrix.st * matrix.sr := by
    calc
      matrix.ss * matrix.tr = matrix.tr * matrix.ss := by ring1
      _ = matrix.ts * matrix.sr := (Group.eq_of_sub_eq_zero trMinor).symm
      _ = matrix.st * matrix.sr := by rw [stEq]
  have rrMinor := congrArg Coordinates3.Matrix3.tt adjugateZero
  unfold Coordinates3.Matrix3.adjugate at rrMinor
  unfold Coordinates3.Matrix3.zero at rrMinor
  rw [srEq] at rrMinor
  have rrRelation : matrix.ss * matrix.rr = matrix.sr * matrix.sr := by
    calc
      matrix.ss * matrix.rr = matrix.rr * matrix.ss := by ring1
      _ = matrix.rs * matrix.rs := Group.eq_of_sub_eq_zero rrMinor
      _ = matrix.sr * matrix.sr := by rw [srEq]
  rw [Purelib.LinearAlgebra.Coordinates3.Projector.rowS_quadrance_of_idempotent matrix symmetric idempotent]
  apply Coordinates3.Matrix3.ext
  all_goals
    unfold Coordinates3.Matrix3.scale
    unfold Coordinates3.Matrix3.outer
    unfold Coordinates3.Matrix3.rowS
  · exact Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero ttRelation
  · exact Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero trRelation
  · apply Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero
    rw [stEq]
    ring1
  · apply Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero
    rw [rtEq]
    calc
      matrix.ss * matrix.tr = matrix.st * matrix.sr := trRelation
      _ = matrix.sr * matrix.st := by ring1
  · exact Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero rrRelation
  · apply Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero
    rw [srEq]
    ring1
  · apply Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero
    ring1
  · apply Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero
    ring1
  · apply Purelib.Algebra.Field.Inverse.eq_one_div_mul_of_mul_eq pivotNonzero
    ring1

set_option genInjectivity false in
/-- Cached executable data extracted from a displayed symmetric rank-one
projector.

The vector keeps its nonzero quadrance and the exact normalized self-outer-product equation for the supplied matrix.
These proof fields retain the original matrix rather than constructing another projector. -/
structure RankOneProjectorWitness (matrix : Coordinates3.Matrix3 K) where
  /-- The retained vector generating the rank-one projector. -/ vector : Vector3 K
  /-- The retained generating vector has nonzero quadrance. -/ nonNull : vector.quadrance ≠ 0
  /-- The original matrix is the self outer product normalized by the retained vector quadrance. -/ reconstruction :
    matrix = Coordinates3.Matrix3.scale (1 / vector.quadrance)
      (Coordinates3.Matrix3.outer vector vector)

constructive_injectivity RankOneProjectorWitness

/-- The same fixed-order row choice used by the projector witness.

The diagonal tests inspect t before r, and choose s only when the first two diagonals vanish. The returned vector is the
corresponding original matrix row. -/
@[expose]
def rankOneProjectorVector [DecidableEq K] (matrix : Coordinates3.Matrix3 K) : Vector3 K :=
  if matrix.tt = 0 then
    if matrix.rr = 0 then Coordinates3.Matrix3.rowS matrix else Coordinates3.Matrix3.rowR matrix
  else Coordinates3.Matrix3.rowT matrix

/-- The selected row certifies the normalized outer-product formula for a rank-one projector.

Symmetry, idempotence, trace one and vanishing adjugate yield a non-null vector when two is nonzero. -/
theorem rankOneProjectorVector_certificates [DecidableEq K]
    (matrix : Coordinates3.Matrix3 K)
    (symmetric : matrix.IsSymmetric)
    (idempotent : Coordinates3.Matrix3.mul matrix matrix = matrix)
    (traceOne : Coordinates3.Matrix3.trace matrix = 1)
    (adjugateZero : Coordinates3.Matrix3.adjugate matrix = Coordinates3.Matrix3.zero)
    (twoNonzero : (2 : K) ≠ 0) :
    (Coordinates3.Projector.rankOneProjectorVector matrix).quadrance ≠ 0 ∧
      matrix = Coordinates3.Matrix3.scale (1 / (Coordinates3.Projector.rankOneProjectorVector matrix).quadrance)
        (Coordinates3.Matrix3.outer (Coordinates3.Projector.rankOneProjectorVector matrix)
          (Coordinates3.Projector.rankOneProjectorVector matrix)) := open Purelib in by
  unfold Coordinates3.Projector.rankOneProjectorVector
  split_ifs with ttZero rrZero
  · have ssNonzero : matrix.ss ≠ 0 := by
      intro ssZero
      have oneZero : (1 : K) = 0 := by
        calc
          (1 : K) = Coordinates3.Matrix3.trace matrix := traceOne.symm
          _ = 0 := by
            unfold Coordinates3.Matrix3.trace
            rw [ttZero, rrZero, ssZero]
            ring1
      exact (Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero twoNonzero) oneZero
    constructor
    · rw [Purelib.LinearAlgebra.Coordinates3.Projector.rowS_quadrance_of_idempotent matrix symmetric idempotent]
      exact ssNonzero
    · exact Purelib.LinearAlgebra.Coordinates3.Projector.reconstruct_from_rowS matrix symmetric idempotent
        adjugateZero ssNonzero
  · constructor
    · rw [Purelib.LinearAlgebra.Coordinates3.Projector.rowR_quadrance_of_idempotent matrix symmetric idempotent]
      exact rrZero
    · exact Purelib.LinearAlgebra.Coordinates3.Projector.reconstruct_from_rowR matrix symmetric idempotent
        adjugateZero rrZero
  · constructor
    · rw [Purelib.LinearAlgebra.Coordinates3.Projector.rowT_quadrance_of_idempotent matrix symmetric idempotent]
      exact ttZero
    · exact Purelib.LinearAlgebra.Coordinates3.Projector.reconstruct_from_rowT matrix symmetric idempotent
        adjugateZero ttZero

/-- Select a non-null row of a symmetric rank-one projector by testing its
three diagonal entries in order.

Symmetry, idempotence, trace one and zero adjugate certify that same selected row; the nonzero value of two rules out
the degenerate field case. The resulting record retains the original matrix and normalized reconstruction. -/
@[expose]
def rankOneProjectorWitness [DecidableEq K] (matrix : Coordinates3.Matrix3 K)
    (symmetric : matrix.IsSymmetric)
    (idempotent : Coordinates3.Matrix3.mul matrix matrix = matrix)
    (traceOne : Coordinates3.Matrix3.trace matrix = 1)
    (adjugateZero : Coordinates3.Matrix3.adjugate matrix = Coordinates3.Matrix3.zero)
    (twoNonzero : (2 : K) ≠ 0) : Coordinates3.Projector.RankOneProjectorWitness matrix :=
  { vector := Coordinates3.Projector.rankOneProjectorVector matrix
    nonNull := (Coordinates3.Projector.rankOneProjectorVector_certificates matrix symmetric idempotent
      traceOne adjugateZero twoNonzero).1
    reconstruction := (Coordinates3.Projector.rankOneProjectorVector_certificates matrix symmetric idempotent
      traceOne adjugateZero twoNonzero).2 }

namespace RankOneProjectorWitness

/-- A nonzero projected vector has nonzero quadrance for a certified rank-one orthogonal projector.

The retained reconstruction expresses the image as a scalar multiple of the
original non-null axis. Nonzero image forces nonzero scale, so its quadrance
is that axis quadrance multiplied by a nonzero square.
-/
theorem image_nonNull {matrix : Matrix3 K} (witness : RankOneProjectorWitness matrix) (vector : Vector3 K)
    (nonzero : Matrix3.rowMul vector matrix ≠ Vector3.zero) :
    (Matrix3.rowMul vector matrix).quadrance ≠ 0 := by
  let factor := (1 / witness.vector.quadrance) * vector.dot witness.vector
  have readback : Matrix3.rowMul vector matrix = Vector3.scale factor witness.vector := by
    calc
      Matrix3.rowMul vector matrix = Matrix3.rowMul vector
          (Matrix3.scale (1 / witness.vector.quadrance) (Matrix3.outer witness.vector witness.vector)) :=
        congrArg (Matrix3.rowMul vector) witness.reconstruction
      _ = Vector3.scale factor witness.vector := by
        rw [Matrix3.rowMul_scale, Matrix3.rowMul_outer, Vector3.scale_scale]
  have factorNonzero : factor ≠ 0 := by
    intro zero
    apply nonzero
    rw [readback, zero, Vector3.zero_scale]
  rw [readback, Vector3.quadrance_scale]
  have square : factor ^ 2 = factor * factor := by ring1
  rw [square]
  exact ExplicitField.mul_ne_zero (ExplicitField.mul_ne_zero factorNonzero factorNonzero) witness.nonNull

end RankOneProjectorWitness

end
end Purelib.LinearAlgebra.Coordinates3.Projector
