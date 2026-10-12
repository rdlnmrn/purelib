module

import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Chordal.Affine
import Purelib.Geometry.Projective.Chordal.Basic
public import Purelib.Geometry.Projective.Chordal.Transport
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Chordal

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Basic

open Purelib.Geometry.Projective.Line.Gaussian

open Purelib.Geometry.Projective.Line.Proj

open Purelib.LinearAlgebra.Coordinates2.Matrix

section
@[expose] public section

/-!
# Productive unary padding at a projective CCL terminal

An arithmetic transducer cannot in general decide that opaque nonterminating
inputs have combined to an exact Gaussian rational.  The canonical finite
encoder remains unchanged.  This module supplies a separate projective
continuation convention: after a completed sector, an unresolved zero
residual may remain at `omega`, and every further unary `1` fixes that formal
coordinate while strengthening the finite large-tail predicate.
-/

namespace Purelib.Geometry.Projective.Chordal.DyadicTail

set_option genInjectivity false in
/-- Projective meanings admitted by an unresolved loop-unary fragment. The `omega` constructor is the exact
residual-zero case; affine tails retain the ordinary strict unary inequality. -/
inductive LoopTail (count : Nat) where
  /-- The exact projective terminal coordinate. -/ | omega
  /-- Retain an affine tail whose quadrance exceeds the displayed dyadic threshold. -/ | affine (tail :
    Data.Gaussian.Basic.Canonical) (large : (2 : Fraction.Rational) ^ count < Data.Gaussian.Norm.Basic.normSq
    tail)

constructive_injectivity LoopTail

namespace LoopTail

/-- Read the homogeneous point of the terminal or large affine tail. -/
def point {count : Nat} : Geometry.Projective.Chordal.DyadicTail.LoopTail count → GaussianLine
  | .omega => Proj.omega
  | .affine tail _ => Proj.affine tail

/-- Every loop-tail point has a nonzero homogeneous coordinate. -/
theorem valid {count : Nat} (tail : Geometry.Projective.Chordal.DyadicTail.LoopTail count) :
    Proj.HasNonzeroCoordinate tail.point := by
  cases tail with
  | omega => exact Proj.omega_hasNonzeroCoordinate
  | affine value large => exact Proj.affine_hasNonzeroCoordinate value

/-- An unresolved unary tail approaches `omega` with a completely rational dyadic squared-chordal estimate. -/
theorem chordalSq_omega_le {count : Nat} (tail : Geometry.Projective.Chordal.DyadicTail.LoopTail count) :
    Chordal.Basic.chordalSq tail.point Proj.omega ≤
      1 / (1 + (2 : Fraction.Rational) ^ count) := by
  cases tail with
  | omega =>
      change Chordal.Basic.chordalSq (Proj.omega : GaussianLine) Proj.omega ≤ _
      rw [Chordal.Basic.chordalSq_eq_zero_of_equivalent (Equivalent.refl _)]
      exact Fraction.Order.Field.div_nonneg_direct (by decide)
        (add_nonneg (by decide)
          (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) count))
  | affine value large =>
      rw [Geometry.Projective.Chordal.DyadicTail.LoopTail.point, Affine.chordalSq_omega]
      have denominatorPositive :
          0 < 1 + (2 : Fraction.Rational) ^ count :=
        add_pos_of_pos_of_nonneg (by decide)
          (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) count)
      have denominatorOrder :
          1 + (2 : Fraction.Rational) ^ count ≤ 1 + Data.Gaussian.Norm.Basic.normSq value :=
        add_le_add le_rfl large.le
      exact Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        (by decide) denominatorPositive denominatorOrder

end LoopTail

/-! ## The analogous no-return name for exact zero -/

set_option genInjectivity false in
/-- Meanings admitted after the initial low selector followed by `count + 1` unary one bits. The affine predicate is
exactly the parser inequality `2^count * N(value) < 1`; the extra constructor supplies the exact zero which the finite
nonzero encoder deliberately excludes. -/
inductive ZeroTail (count : Nat) where
  /-- The exact affine zero coordinate. -/ | zero
  /-- Retain an affine value satisfying the displayed strict reciprocal-dyadic norm bound. -/ | affine (value :
    Data.Gaussian.Basic.Canonical)
      (small : (2 : Fraction.Rational) ^ count * Data.Gaussian.Norm.Basic.normSq value < 1)

constructive_injectivity ZeroTail

namespace ZeroTail

/-- Read the homogeneous point of the exact-zero or small affine tail. -/
def point {count : Nat} : Geometry.Projective.Chordal.DyadicTail.ZeroTail count → GaussianLine
  | .zero => Proj.affine 0
  | .affine value _ => Proj.affine value

/-- Every zero-tail point has a nonzero homogeneous coordinate. -/
theorem valid {count : Nat} (tail : Geometry.Projective.Chordal.DyadicTail.ZeroTail count) :
    Proj.HasNonzeroCoordinate tail.point := by
  cases tail with
  | zero => exact Proj.affine_hasNonzeroCoordinate 0
  | affine value small => exact Proj.affine_hasNonzeroCoordinate value

/-- Initial low unary padding converges to zero at the reciprocal dyadic rate, again entirely in squared rational
quantities. -/
theorem chordalSq_zero_lt {count : Nat} (tail : Geometry.Projective.Chordal.DyadicTail.ZeroTail count) :
    Chordal.Basic.chordalSq tail.point (Proj.affine 0) <
      1 / (2 : Fraction.Rational) ^ count := by
  cases tail with
  | zero =>
      change Chordal.Basic.chordalSq (Proj.affine 0) (Proj.affine 0) < _
      rw [Chordal.Basic.chordalSq_eq_zero_of_equivalent (Equivalent.refl _)]
      exact Fraction.Order.Field.div_pos_direct (by decide)
        (Fraction.Order.Arithmetic.pow_pos_direct (by decide) count)
  | affine value small =>
      have powerPositive : 0 < (2 : Fraction.Rational) ^ count :=
        Fraction.Order.Arithmetic.pow_pos_direct (by decide) count
      have normSmall : Data.Gaussian.Norm.Basic.normSq value < 1 / (2 : Fraction.Rational) ^ count := by
        apply (Fraction.Order.Field.lt_div_iff_pos powerPositive).2
        calc
          Data.Gaussian.Norm.Basic.normSq value * (2 : Fraction.Rational) ^ count =
              (2 : Fraction.Rational) ^ count * Data.Gaussian.Norm.Basic.normSq value :=
            Fraction.Field.mul_comm _ _
          _ < 1 := small
      have chordalBound := Affine.chordalSq_affine_le_normSq value 0
      have differenceNorm : Data.Gaussian.Norm.Basic.normSq (value - 0) =
        Data.Gaussian.Norm.Basic.normSq value := by
        congr 1
        exact Data.Gaussian.Basic.sub_zero value
      rw [differenceNorm] at chordalBound
      exact chordalBound.trans_lt normSmall

end ZeroTail

/-- Full finite no-return estimate, including the exact `omega` case. -/
theorem chordalSq_act_loopTail_le
    (matrix : GaussianMatrix)
    (determinantNonzero :
      BoundaryAdjugate.determinant matrix ≠ 0)
    {count : Nat} (tail : Geometry.Projective.Chordal.DyadicTail.LoopTail count) :
    Chordal.Basic.chordalSq (Line.Matrix.act matrix tail.point)
        (Line.Matrix.act matrix Proj.omega) ≤
      Transport.terminalCoefficient matrix /
        (1 + (2 : Fraction.Rational) ^ count) := by
  cases tail with
  | omega =>
      change Chordal.Basic.chordalSq
          (Line.Matrix.act matrix (Proj.omega : GaussianLine))
          (Line.Matrix.act matrix Proj.omega) ≤ _
      rw [Chordal.Basic.chordalSq_eq_zero_of_equivalent (Equivalent.refl _)]
      exact Fraction.Order.Field.div_nonneg_direct
        (Transport.terminalCoefficient_pos matrix determinantNonzero).le
        (add_nonneg (by decide)
          (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) count))
  | affine value large =>
      have transported := Transport.chordalSq_act_affine_omega_le matrix
        determinantNonzero value
      have coefficientNonnegative :=
        (Transport.terminalCoefficient_pos matrix determinantNonzero).le
      have smallPositive : 0 < 1 + (2 : Fraction.Rational) ^ count :=
        add_pos_of_pos_of_nonneg (by decide)
          (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) count)
      have denominatorOrder :
          1 + (2 : Fraction.Rational) ^ count ≤ 1 + Data.Gaussian.Norm.Basic.normSq value :=
        add_le_add le_rfl large.le
      exact transported.trans
        (Fraction.Order.Field.div_le_div_of_nonneg_left_direct
          coefficientNonnegative smallPositive denominatorOrder)

end Purelib.Geometry.Projective.Chordal.DyadicTail

end

end
