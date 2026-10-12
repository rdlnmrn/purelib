module
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Chordal.Equivalence
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Projective.Line.Matrix.Gaussian
public import Purelib.Geometry.Projective.SectorBlock.Safe.Tail

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Data.CCL.Encoding.Block.Matrix
import Purelib.Data.CCL.Encoding.Block.SafeContraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.Ring

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

namespace Purelib.Data.CCL.Encoding.Cylinder.Safe.Projective

/-! ## Projectively coherent redundant realizations

Progressive arithmetic carries homogeneous residual tails, while the local
contraction proof chooses either an affine reciprocal or `omega`.  The two
are projectively equivalent but generally not definitionally equal.  The
following relation records those finite equivalences explicitly; it is the
trace-friendly counterpart of `Realizes`, not a change to the bitstream. -/

open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
/-- Require a safe redundant-block realization allowing explicit projective equivalences at each step.

Each step retains a valid output point, a safe tail for the exact sector, output equivalence to its matrix image, and
tail equivalence to the inner realized point. The empty list retains point validity. -/
inductive ProjectiveRealizes : (blocks : List
  Data.CCL.Encoding.Block.Redundant) → Line.GaussianLine → Prop where
  /-- Certify an empty redundant block list at the retained valid point. -/ | done (point :
    Line.GaussianLine)
      (valid : Line.Gaussian.Proj.HasNonzeroCoordinate point) :
      ProjectiveRealizes [] point
  /-- Retain the current safe tail, both projective equivalences and the exact inner realization. -/ | step {remaining :
    List Data.CCL.Encoding.Block.Redundant} {point inner : Line.GaussianLine} (entry :
    Data.CCL.Encoding.Block.Redundant)
      (tail : Geometry.Projective.SectorBlock.Safe.Tail entry.sector)
      (pointValid : Line.Gaussian.Proj.HasNonzeroCoordinate point)
      (outputEquivalent : point.Equivalent
        (Line.Matrix.act entry.matrix tail.point))
      (tailEquivalent : tail.point.Equivalent inner)
      (rest : ProjectiveRealizes remaining inner) :
      ProjectiveRealizes (entry :: remaining) point

namespace ProjectiveRealizes

section
open Purelib.Data.CCL.Encoding
open Purelib.Geometry.Projective
/-- Every point with a safe projective realization has a nonzero coordinate. -/
theorem valid {blocks : List
  Data.CCL.Encoding.Block.Redundant} {point : Line.GaussianLine}
    (realizes : ProjectiveRealizes blocks point) :
    Line.Gaussian.Proj.HasNonzeroCoordinate point := by
  cases realizes with
  | done point pointValid => exact pointValid
  | step entry tail pointValid outputEquivalent tailEquivalent rest =>
      exact pointValid

/-- Transport a safe projective realization to a retained valid equivalent point. -/
theorem ofEquivalent {blocks : List
  Data.CCL.Encoding.Block.Redundant} {left right : Line.GaussianLine}
    (leftValid : Line.Gaussian.Proj.HasNonzeroCoordinate left)
    (equivalent : left.Equivalent right)
    (realizes : ProjectiveRealizes blocks right) :
    ProjectiveRealizes blocks left := by
  cases realizes with
  | done point pointValid => exact .done left leftValid
  | @step remaining point inner entry tail pointValid outputEquivalent
      tailEquivalent rest =>
      have imageValid :=
        Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
          entry.matrix_det_ne tail.point_valid
      exact .step entry tail leftValid
        (Line.Gaussian.Proj.equivalent_trans
          equivalent outputEquivalent pointValid imageValid)
        tailEquivalent rest

end

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Two safe projective realizations of the same redundant blocks have squared chordal distance at most one half to the
list length. -/
theorem chordalSq_le_half_pow
    {blocks : List Data.CCL.Encoding.Block.Redundant} {left right : Line.GaussianLine}
    (leftRealizes : ProjectiveRealizes blocks left)
    (rightRealizes : ProjectiveRealizes blocks right) :
    Chordal.Basic.chordalSq left right ≤ (1 / 2 : Fraction.Rational) ^ blocks.length := by
  induction leftRealizes generalizing right with
  | done left leftValid =>
      cases rightRealizes with
      | done right rightValid =>
          rw [List.length_nil, pow_zero]
          exact Chordal.Basic.chordalSq_le_one
            leftValid rightValid
  | @step remaining left inner entry leftTail leftValid leftOutputEquivalent
      leftTailEquivalent leftRest inductionHypothesis =>
      cases rightRealizes with
      | @step _ right rightInner _ rightTail rightValid
          rightOutputEquivalent rightTailEquivalent rightRest =>
          have leftTailValid := leftTail.point_valid
          have rightTailValid := rightTail.point_valid
          have leftImageValid :=
            Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
              entry.matrix_det_ne leftTailValid
          have rightImageValid :=
            Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
              entry.matrix_det_ne rightTailValid
          have inputIdentity :
              Chordal.Basic.chordalSq leftTail.point rightTail.point =
                Chordal.Basic.chordalSq inner rightInner := by
            calc
              Chordal.Basic.chordalSq leftTail.point rightTail.point =
                  Chordal.Basic.chordalSq inner rightTail.point :=
                Chordal.Equivalence.chordalSq_eq_of_equivalent_left
                  leftTailValid leftRest.valid leftTailEquivalent
                    rightTail.point
              _ = Chordal.Basic.chordalSq inner rightInner :=
                Chordal.Equivalence.chordalSq_eq_of_equivalent_right
                  rightTailValid rightRest.valid rightTailEquivalent inner
          have outputIdentity :
              Chordal.Basic.chordalSq left right =
                Chordal.Basic.chordalSq
                  (Line.Matrix.act entry.matrix leftTail.point)
                  (Line.Matrix.act entry.matrix rightTail.point) := by
            calc
              Chordal.Basic.chordalSq left right =
                  Chordal.Basic.chordalSq
                    (Line.Matrix.act entry.matrix leftTail.point) right :=
                Chordal.Equivalence.chordalSq_eq_of_equivalent_left
                  leftValid leftImageValid leftOutputEquivalent right
              _ = Chordal.Basic.chordalSq
                  (Line.Matrix.act entry.matrix leftTail.point)
                  (Line.Matrix.act entry.matrix rightTail.point) :=
                Chordal.Equivalence.chordalSq_eq_of_equivalent_right
                  rightValid rightImageValid rightOutputEquivalent _
          calc
            Chordal.Basic.chordalSq left right =
                Chordal.Basic.chordalSq
                  (Line.Matrix.act entry.matrix leftTail.point)
                  (Line.Matrix.act entry.matrix rightTail.point) := outputIdentity
            _ ≤ (1 / 2 : Fraction.Rational) *
                Chordal.Basic.chordalSq leftTail.point rightTail.point :=
              entry.contraction_half leftTail rightTail
            _ = (1 / 2 : Fraction.Rational) *
                Chordal.Basic.chordalSq inner rightInner := by rw [inputIdentity]
            _ ≤ (1 / 2 : Fraction.Rational) *
                (1 / 2 : Fraction.Rational) ^ remaining.length :=
              Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                (inductionHypothesis rightRest) (by decide)
            _ = (1 / 2 : Fraction.Rational) ^
                (entry :: remaining).length := by
              rw [List.length_cons, pow_succ]
              ring1

end ProjectiveRealizes

end Purelib.Data.CCL.Encoding.Cylinder.Safe.Projective

end

section
@[expose] public section

/-!
# Optional contraction accounting for progressive arithmetic cursors

The canonical encoder, raw parser, and progressive `List Bool` cursor do not
carry an error symbol.  This module is a separate proof sidecar.  It packages
neutral chart changes and normalized sector emissions into finite traces of
projectively coherent redundant blocks, then combines their dyadic
contraction with the explicit coefficient of any already committed decoder
prefix.
-/

namespace Purelib.CCL.Progressive.MachineContraction
end Purelib.CCL.Progressive.MachineContraction

end
