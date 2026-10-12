module
import Purelib.Data.List.Append
import Purelib.Data.CCL.Encoding.Block.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Projective
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
public import Purelib.Geometry.Projective.Line.Matrix.Gaussian

import Purelib.Geometry.Projective.SectorBlock.Tail.Projective
import Purelib.Data.CCL.Encoding.Block.Matrix
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Geometry.Projective.SectorBlock.Tail
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Util.CompileInductive

open Purelib.Data.List

section
public section

/-!
# Joint finite profile of a completed CCL prefix

A completed-block prefix carries two deliberately separate rational data:

* its fair-bit symbolic cylinder weight, calculated from the raw word; and
* its geometric squared-chordal spread, calculated from block contraction.

Both improve under finite extension, but no theorem identifies them.  A
finite realization certificate also turns the prefix into an inhabited
finite observation, without choosing a point from an eventual intersection.
-/

namespace Purelib.Data.CCL.Encoding.Cylinder

section
open Purelib.Data.CCL.Encoding
/-- Concatenating retained block lists concatenates their exact encoded bit words. -/
theorem rawWord_append (stem suffix : List Data.CCL.Encoding.Block) :
    Block.Basic.rawWord (stem ++ suffix) =
      Block.Basic.rawWord stem ++ Block.Basic.rawWord suffix := by
  induction stem with
  | nil => rfl
  | cons block remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self, List.cons_append, Block.Basic.rawWord_cons,
        inductionHypothesis, Append.append_assoc]; try rfl

/-- A retained block list is no longer than its encoded bit word. -/
theorem blocks_length_le_rawWord_length (blocks : List
  Data.CCL.Encoding.Block) :
    blocks.length ≤ (Block.Basic.rawWord blocks).length := by
  induction blocks with
  | nil => exact le_rfl
  | cons block remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self, List.length_cons, Block.Basic.rawWord_cons,
        Append.length_append]; try rfl
      have oneLeWord : 1 ≤ block.word.length :=
        (by decide : 1 ≤ 4).trans block.word_length_ge_four
      calc
        remaining.length + 1 ≤
            (Block.Basic.rawWord remaining).length + block.word.length :=
          Nat.add_le_add inductionHypothesis oneLeWord
        _ = block.word.length +
            (Block.Basic.rawWord remaining).length := Nat.add_comm _ _

end

open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
/-- Restrict an exact block realization to the retained list prefix at the same projective point. -/
@[expose] def realizesPrefix
    {stem suffix : List Data.CCL.Encoding.Block} {point : Line.GaussianLine}
    (realizes : Cylinder.Basic.Realizes (stem ++ suffix) point) :
    Cylinder.Basic.Realizes stem point := by
  induction stem generalizing point with
  | nil =>
      have valid :
          Line.Gaussian.Proj.HasNonzeroCoordinate point := by
        simp only [-eq_self, -iff_self, List.nil_append] at realizes
        induction realizes with
        | done point valid => exact valid
        | step block tail rest inductionHypothesis =>
            exact Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
              block.matrix_det_ne_zero inductionHypothesis
      exact .done point valid
  | cons block remaining inductionHypothesis =>
      cases realizes with
      | step _ tail rest =>
          exact .step block tail (inductionHypothesis rest)
end Purelib.Data.CCL.Encoding.Cylinder

end

section
public section

/-!
# Root-free L2 stability of finite CCL prefix probes

Direct Lipschitz control by `chordalSq` is stronger than is natural for many
nonconstant projective observables.  This module instead accepts the
square-root-free estimate

`rationalSeparation (probe x) (probe y) ^ 2 ≤ factor * chordalSq x y`.

CCL cylinder contraction then controls exact finite powered-L2 distances.
Finite Cauchy--Schwarz transfers that control to squared expectation error,
and a request at the square of a supplied rational tolerance recovers an
ordinary strict expectation-separation theorem.  No square root is selected.
-/

namespace Purelib.Data.CCL.Encoding.Cylinder

open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
/-- Every retained canonical block realization has a nonzero projective coordinate. -/
theorem canonicalRealizes_valid
    {blocks : List Data.CCL.Encoding.Block} {point : Line.GaussianLine}
    (realizes : Cylinder.Basic.Realizes blocks point) :
    Line.Gaussian.Proj.HasNonzeroCoordinate point := by
  induction realizes with
  | done point valid => exact valid
  | step block tail rest inductionHypothesis =>
      exact Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
        block.matrix_det_ne_zero inductionHypothesis

end Purelib.Data.CCL.Encoding.Cylinder

end

section
public section

/-!
# Finite measure bounds for projectively rescaled CCL prefixes

The integral CCL encoder retains arbitrary nonzero homogeneous rescalings at
intermediate decoding stages.  Its certificates therefore use
`ProjectiveRealizes`, rather than the canonical-tail `Realizes` relation used
by the original prefix profile.  This module gives those exact encoder-facing
certificates the same finite observation and rational-enclosure interface.

No projective normalization, representative choice, completed point, or
infinite continuation is introduced.
-/

namespace Purelib.Data.CCL.Encoding.Cylinder

open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
/-- Restrict a projective-tail block realization to the retained prefix at the same point. -/
@[expose] def projectiveRealizesPrefix
    {stem suffix : List Data.CCL.Encoding.Block} {point : Line.GaussianLine}
    (realizes : Cylinder.Projective.ProjectiveRealizes (stem ++ suffix) point) :
    Cylinder.Projective.ProjectiveRealizes stem point := by
  induction stem generalizing point with
  | nil =>
      exact .done point realizes.valid
  | cons block remaining inductionHypothesis =>
      cases realizes with
      | step _ tail rest =>
          exact .step block tail (inductionHypothesis rest)
end Purelib.Data.CCL.Encoding.Cylinder

end
