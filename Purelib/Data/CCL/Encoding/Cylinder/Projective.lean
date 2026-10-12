module

import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Matrix
public import Purelib.Geometry.Projective.SectorBlock.Tail.Projective

public import Purelib.Data.CCL.Encoding.Block.Matrix
import Purelib.Data.CCL.Encoding.Block.Contraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

section
section
public section
namespace Purelib.Data.CCL.Encoding.Cylinder.Projective

open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
set_option genInjectivity false in
/-- Retain a finite block realization with projective tail representatives and their exact compatible models.

The base case stores a valid point. Each step keeps the tail for the current block's sector and realizes the remaining
list at that exact representative before taking its matrix image. -/
inductive ProjectiveRealizes : (blocks : List Block) → Line.GaussianLine → Type
  where
  /-- Realize an empty block list at the exact retained valid point. -/ | done (point :
    Line.GaussianLine)
      (valid : Line.Gaussian.Proj.HasNonzeroCoordinate point) :
      Purelib.Data.CCL.Encoding.Cylinder.Projective.ProjectiveRealizes [] point
  /-- Prepend the block and its retained projective sector tail to the exact remaining realization. -/ | step {remaining
    : List Block} (block : Block)
      (tail : Geometry.Projective.SectorBlock.Tail.ProjectiveTail block.sector)
      (rest : Purelib.Data.CCL.Encoding.Cylinder.Projective.ProjectiveRealizes remaining tail.point) :
      Purelib.Data.CCL.Encoding.Cylinder.Projective.ProjectiveRealizes (block :: remaining)
        (Line.Matrix.act block.matrix tail.point)

constructive_injectivity ProjectiveRealizes

end Purelib.Data.CCL.Encoding.Cylinder.Projective
end
end

end

section
public section
namespace Purelib.Data.CCL.Encoding.Cylinder.Projective
open Purelib.Data.CCL.Encoding in
/-- The exact projective block-realization carrier retained by the encoder. -/
abbrev SourceEncodingEncoderProjectiveRealizesAlias := Cylinder.Projective.ProjectiveRealizes

end Purelib.Data.CCL.Encoding.Cylinder.Projective

end

section
section
public section
namespace Purelib.Data.CCL.Encoding.Cylinder.Projective
namespace ProjectiveRealizes

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Two projective realizations of the same blocks have squared chordal distance at most one half to their count.

Each retained sector tail contracts the squared distance by one half. Structural
induction composes those finite contractions from the valid terminal points. -/
theorem chordalSq_le_half_pow
    {blocks : List Block} {left right : Line.GaussianLine}
    (leftRealizes : Cylinder.Projective.ProjectiveRealizes blocks left)
    (rightRealizes : Cylinder.Projective.ProjectiveRealizes blocks right) :
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
              block.projective_contraction_half leftTail rightTail
            _ ≤ (1 / 2 : Fraction.Rational) *
                (1 / 2 : Fraction.Rational) ^ remaining.length :=
              Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                (inductionHypothesis rightRest) (by decide)
            _ = (1 / 2 : Fraction.Rational) ^ (block :: remaining).length := by
              rw [List.length_cons, pow_succ]
              ring1

end ProjectiveRealizes
end Purelib.Data.CCL.Encoding.Cylinder.Projective
end
end

end

section
section
public section
namespace Purelib.Data.CCL.Encoding.Cylinder.Projective
namespace ProjectiveRealizes

open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
/-- Every retained projective block realization has a nonzero coordinate. -/
theorem valid {blocks : List Block} {point : Line.GaussianLine}
    (realizes : Cylinder.Projective.ProjectiveRealizes blocks point) :
    Line.Gaussian.Proj.HasNonzeroCoordinate point := by
  cases realizes with
  | done point pointValid => exact pointValid
  | step block tail rest => exact block.act_projectiveTail_valid tail
end ProjectiveRealizes
end Purelib.Data.CCL.Encoding.Cylinder.Projective
end
end

end
