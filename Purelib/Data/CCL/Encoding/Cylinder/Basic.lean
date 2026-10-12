module
import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
public import Purelib.Geometry.Projective.SectorBlock.Tail

public import Purelib.Data.CCL.Encoding.Block.Matrix
import Purelib.Data.CCL.Encoding.Block.Contraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

/-!
# Finite completed-block cylinders

A cylinder is represented by a finite list of completed raw CCL blocks and a
finite realization trace.  No collection of all compatible points is formed.
The main theorem compares any two supplied realization traces and obtains the
explicit `2⁻ⁿ` squared-chordal bound.
-/

@[expose] public section

namespace Purelib.Data.CCL.Encoding.Cylinder.Basic

set_option genInjectivity false in
open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
/-- Retain a finite block-by-block realization of a projective point using exact compatible sector tails.

An empty block list retains any valid point. A step keeps the block, a tail for its exact sector and a realization of
the remaining blocks at that same tail point, then returns the exact block matrix image. -/
inductive Realizes : (blocks : List Data.CCL.Encoding.Block) →
  Line.GaussianLine → Type where
  /-- Realize an empty block list at the retained point with its nonzero-coordinate witness. -/ | done (point :
    Line.GaussianLine) (valid : Line.Gaussian.Proj.HasNonzeroCoordinate point) :
      Realizes [] point
  /-- Prepend the retained block and sector tail to the exact realization of the remaining blocks. -/ | step {remaining
    : List Data.CCL.Encoding.Block} (block : Data.CCL.Encoding.Block)
      (tail : Geometry.Projective.SectorBlock.Tail block.sector)
      (rest : Realizes remaining tail.point) :
      Realizes (block :: remaining) (Line.Matrix.act block.matrix tail.point)

constructive_injectivity Realizes

namespace Realizes

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Two realizations of the same block list have squared chordal distance at most one half to the list length. -/
theorem chordalSq_le_half_pow
    {blocks : List Data.CCL.Encoding.Block} {left right : Line.GaussianLine}
    (leftRealizes : Realizes blocks left)
    (rightRealizes : Realizes blocks right) :
    Chordal.Basic.chordalSq left right ≤ (1 / 2 : Fraction.Rational) ^ blocks.length := by
  induction leftRealizes generalizing right with
  | done left leftValid =>
      cases rightRealizes with
      | done right rightValid =>
          rw [List.length_nil, pow_zero]
          exact Chordal.Basic.chordalSq_le_one leftValid rightValid
  | @step remaining block leftTail leftRest inductionHypothesis =>
      cases rightRealizes with
      | step _ rightTail rightRest =>
          calc
            Chordal.Basic.chordalSq (Line.Matrix.act block.matrix leftTail.point)
                (Line.Matrix.act block.matrix rightTail.point) ≤
                (1 / 2 : Fraction.Rational) *
                  Chordal.Basic.chordalSq leftTail.point rightTail.point :=
              block.contraction_half leftTail rightTail
            _ ≤ (1 / 2 : Fraction.Rational) *
                (1 / 2 : Fraction.Rational) ^ remaining.length :=
              Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                (inductionHypothesis rightRest) (by decide)
            _ = (1 / 2 : Fraction.Rational) ^ (block :: remaining).length := by
              rw [List.length_cons, pow_succ]
              ring1

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Data.List in
/-- A shared realized block prefix bounds squared chordal distance by one half to that prefix length, regardless of the
retained suffix. -/
theorem chordalSq_le_half_pow_of_append
    {blocksPrefix blocksSuffix : List Data.CCL.Encoding.Block} {left right : Line.GaussianLine}
    (leftRealizes : Realizes (blocksPrefix ++ blocksSuffix) left)
    (rightRealizes : Realizes (blocksPrefix ++ blocksSuffix) right) :
    Chordal.Basic.chordalSq left right ≤
      (1 / 2 : Fraction.Rational) ^ blocksPrefix.length := by
  have fullBound := chordalSq_le_half_pow leftRealizes rightRealizes
  have halfNonnegative : (0 : Fraction.Rational) ≤ 1 / 2 := (by decide)
  have halfPowLeOne : ∀ exponent : Nat,
      (1 / 2 : Fraction.Rational) ^ exponent ≤ 1 := by
    intro exponent
    induction exponent with
    | zero => exact le_rfl
    | succ exponent inductionHypothesis =>
        rw [pow_succ]
        calc
          (1 / 2 : Fraction.Rational) ^ exponent * (1 / 2) ≤
              1 * (1 / 2) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
              inductionHypothesis halfNonnegative
          _ ≤ 1 := by decide
  have suffixFactorLeOne :
      (1 / 2 : Fraction.Rational) ^ blocksSuffix.length ≤ 1 := by
    exact halfPowLeOne blocksSuffix.length
  have powerOrder :
      (1 / 2 : Fraction.Rational) ^ (blocksPrefix ++ blocksSuffix).length ≤
        (1 / 2 : Fraction.Rational) ^ blocksPrefix.length := by
    rw [Append.length_append, pow_add]
    calc
      (1 / 2 : Fraction.Rational) ^ blocksPrefix.length *
          (1 / 2 : Fraction.Rational) ^ blocksSuffix.length ≤
          (1 / 2 : Fraction.Rational) ^ blocksPrefix.length * 1 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          suffixFactorLeOne
          (Fraction.Order.Arithmetic.pow_nonneg_direct halfNonnegative _)
      _ = (1 / 2 : Fraction.Rational) ^ blocksPrefix.length := by ring1
  exact fullBound.trans powerOrder

end Realizes

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Require a rational squared-chordal-distance bound for every pair of realizations of the retained block list. -/
def ChordBound (blocks : List Data.CCL.Encoding.Block) (bound :
  Fraction.Rational) : Prop :=
  ∀ {left right : Line.GaussianLine}, Realizes blocks left →
    Realizes blocks right →
    Chordal.Basic.chordalSq left right ≤ bound

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
/-- A completed block list has chordal bound one half to its retained length. -/
theorem completedPrefix_chordBound (blocks : List
  Data.CCL.Encoding.Block) :
    ChordBound blocks ((1 / 2 : Fraction.Rational) ^ blocks.length) := by
  intro left right leftRealizes rightRealizes
  exact Cylinder.Basic.Realizes.chordalSq_le_half_pow leftRealizes rightRealizes

/-! ## Projectively rescaled finite realizations -/

end Purelib.Data.CCL.Encoding.Cylinder.Basic

end
