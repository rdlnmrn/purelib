module

import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Projective.Line.Matrix.Gaussian
public import Purelib.Geometry.Projective.SectorBlock.Safe.Tail

public import Purelib.Data.CCL.Encoding.Block.Matrix
import Purelib.Data.CCL.Encoding.Block.SafeContraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Completed-block contraction for redundant CCL choices

The canonical contraction theorem stores annulus and disjoint-sector proofs.
For arithmetic output those hypotheses are unnecessarily strong.  A block is
sound and has the same contraction factor whenever its displayed value has
norm at least one and its chosen representative has residual quadrance below
one half.

This parallel structure deliberately leaves the canonical theorem and parser
unchanged.  `ofCanonical` embeds every old compatible block into this wider
arithmetic layer.
-/

namespace Purelib.Data.CCL.Encoding.Cylinder.Safe

open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
set_option genInjectivity false in
/-- Retain a redundant-block realization using exact safe sector tails.

The empty list stores a valid projective point. A step retains the current block, its safe tail and the remaining
realization at that tail point, then takes the exact block matrix image. -/
inductive Realizes : (blocks : List Block.Redundant) → Line.GaussianLine →
  Type where
  /-- Realize an empty redundant block list at the exact retained valid point. -/ | done (point :
    Line.GaussianLine)
      (valid : Line.Gaussian.Proj.HasNonzeroCoordinate point) :
      Purelib.Data.CCL.Encoding.Cylinder.Safe.Realizes [] point
  /-- Prepend the retained redundant block and safe tail to the exact remaining realization. -/ | step {remaining : List
    Block.Redundant} (entry : Block.Redundant)
      (tail : Geometry.Projective.SectorBlock.Safe.Tail entry.sector)
      (rest : Purelib.Data.CCL.Encoding.Cylinder.Safe.Realizes remaining tail.point) :
      Purelib.Data.CCL.Encoding.Cylinder.Safe.Realizes (entry :: remaining) (Line.Matrix.act entry.matrix tail.point)

constructive_injectivity Realizes

namespace Realizes

open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
/-- Every retained safe block realization has a nonzero projective coordinate. -/
theorem valid {blocks : List Block.Redundant} {point : Line.GaussianLine}
    (realizes : Cylinder.Safe.Realizes blocks point) :
    Line.Gaussian.Proj.HasNonzeroCoordinate point := by
  cases realizes with
  | done point pointValid => exact pointValid
  | step entry tail rest =>
      exact Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
        entry.matrix_det_ne tail.point_valid

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Two retained safe realizations of the same redundant blocks have squared chordal distance at most one half to their
length. -/
theorem chordalSq_le_half_pow
    {blocks : List Block.Redundant} {left right : Line.GaussianLine}
    (leftRealizes : Cylinder.Safe.Realizes blocks left)
    (rightRealizes : Cylinder.Safe.Realizes blocks right) :
    Chordal.Basic.chordalSq left right ≤ (1 / 2 : Fraction.Rational) ^ blocks.length := by
  induction leftRealizes generalizing right with
  | done left leftValid =>
      cases rightRealizes with
      | done right rightValid =>
          rw [List.length_nil, pow_zero]
          exact Chordal.Basic.chordalSq_le_one leftValid rightValid
  | @step remaining entry leftTail leftRest inductionHypothesis =>
      cases rightRealizes with
      | step _ rightTail rightRest =>
          calc
            Chordal.Basic.chordalSq (Line.Matrix.act entry.matrix leftTail.point)
                (Line.Matrix.act entry.matrix rightTail.point) ≤
                (1 / 2 : Fraction.Rational) *
                  Chordal.Basic.chordalSq leftTail.point rightTail.point :=
              entry.contraction_half leftTail rightTail
            _ ≤ (1 / 2 : Fraction.Rational) *
                (1 / 2 : Fraction.Rational) ^ remaining.length :=
              Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                (inductionHypothesis rightRest) (by decide)
            _ = (1 / 2 : Fraction.Rational) ^ (entry :: remaining).length := by
              rw [List.length_cons, pow_succ]
              ring1

end Realizes

end Purelib.Data.CCL.Encoding.Cylinder.Safe

end
