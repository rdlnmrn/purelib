module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Block.Contraction
import Purelib.Data.CCL.Encoding.Block.Matrix
import Purelib.Data.CCL.Encoding.Block.ParserCorrespondence
public import Purelib.Data.CCL.Encoding.Block.SafeReconstruction
import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Chordal.Equivalence
import Purelib.Geometry.Projective.Chordal.Scale
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Projective.Line.Matrix.Gaussian
import Purelib.Geometry.Projective.SectorBlock.Safe.Tail
import Purelib.Geometry.Rational.Sector.Eight.Safe
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic
import Mathlib.Algebra.GroupWithZero.NeZero

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

namespace Purelib.Data.CCL.Encoding.Block.Redundant
section Block

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- The retained redundant block halves chordal squared distance between safe tails for its exact sector. -/
theorem contraction_half (entry :
  _root_.Purelib.Data.CCL.Encoding.Block.Redundant)
    (left right : Geometry.Projective.SectorBlock.Safe.Tail entry.sector) :
    Chordal.Basic.chordalSq (Line.Matrix.act entry.matrix left.point)
        (Line.Matrix.act entry.matrix right.point) ≤
      (1 / 2 : Fraction.Rational) * Chordal.Basic.chordalSq left.point right.point := by
  cases entry with
  | mk kind exponent sector =>
      cases kind with
      | regular =>
          rw [_root_.Purelib.Data.CCL.Encoding.Block.Redundant.matrix, Block.Contraction.regularBlock_eq_block]
          exact Geometry.Projective.SectorBlock.Safe.Tail.contraction_half (Power.natPow Basic.Canonical.gamma exponent)
            (Power.natPow_ne_zero_direct Basic.Canonical.gamma (by decide) exponent) left right
      | initialLow =>
          rw [_root_.Purelib.Data.CCL.Encoding.Block.Redundant.matrix,
            Block.Contraction.lowBlock_eq_scaledBlock,
            Chordal.Scale.chordalSq_act_scaleMatrix
              (Power.natPow Basic.Canonical.gamma exponent)
              (Power.natPow_ne_zero_direct Basic.Canonical.gamma (by decide) exponent)]
          exact Geometry.Projective.SectorBlock.Safe.Tail.contraction_half (Power.natPow Basic.Canonical.gamma
              exponent)⁻¹
            (Field.inv_ne_zero_direct
              (Power.natPow_ne_zero_direct Basic.Canonical.gamma (by decide) exponent)) left right

end Block

end Purelib.Data.CCL.Encoding.Block.Redundant

end

section
@[expose] public section

/-!
# Exact semantics of redundant progressive CCL blocks

The arithmetic controller is allowed to select an overlapping safe sector
outside the canonical half-open annulus table.  This file proves that doing
so does not alter the represented point.  Local safety alone gives both the
exact inverse chart and the strict lower norm needed by the following loop.

The zero-residual case is kept projective.  It maps exactly to the completed
block's `omega` tail and can therefore emit the productive unary padding of
`TerminalPadding` without deciding equality.
-/

namespace Purelib.Data.CCL.Encoding.Block.SafeContraction

open Purelib.Data.CCL.Encoding
open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Geometry.Rational
/-- Safe tails built from two admissible normalized values satisfy the same block half-contraction bound. -/
theorem safeBlockTail_pair_contraction
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : ComplexContinuedFraction.Encoding.Sector)
    (left right : Basic.Canonical)
    (leftNorm : 1 ≤ Gaussian.Norm.Basic.normSq (Parser.Semantics.Basic.normalizedValue kind exponent left))
    (rightNorm : 1 ≤ Gaussian.Norm.Basic.normSq (Parser.Semantics.Basic.normalizedValue kind exponent right))
    (leftSafe : Geometry.Rational.Sector.Eight.Safe sector
      (Parser.Semantics.Basic.normalizedValue kind exponent left))
    (rightSafe : Geometry.Rational.Sector.Eight.Safe sector
      (Parser.Semantics.Basic.normalizedValue kind exponent right)) :
    Chordal.Basic.chordalSq
        (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector)
          (Block.SafeReconstruction.safeBlockTail kind exponent sector left leftNorm leftSafe).point)
        (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector)
          (Block.SafeReconstruction.safeBlockTail kind exponent sector right rightNorm rightSafe).point) ≤
      (1 / 2 : Fraction.Rational) *
        Chordal.Basic.chordalSq
          (Block.SafeReconstruction.safeBlockTail kind exponent sector left leftNorm leftSafe).point
          (Block.SafeReconstruction.safeBlockTail kind exponent sector right rightNorm rightSafe).point := by
  rw [← Block.ParserCorrespondence.redundantBlock_matrix kind exponent sector]
  exact (Block.ParserCorrespondence.redundantBlock kind exponent sector).contraction_half
    (Block.SafeReconstruction.safeBlockTail kind exponent sector left leftNorm leftSafe)
    (Block.SafeReconstruction.safeBlockTail kind exponent sector right rightNorm rightSafe)

/-- The two retained homogeneous safe residual tails satisfy the block half-contraction bound.

Both normalized values have squared norm at least one and satisfy the same retained safe sector. Their exact homogeneous
coordinates are related to the separately retained safe-tail models, preserving both inputs throughout the estimate. -/
theorem safeBlockHomogeneous_pair_contraction
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : ComplexContinuedFraction.Encoding.Sector)
    (left right : Basic.Canonical)
    (leftNorm : 1 ≤ Gaussian.Norm.Basic.normSq (Parser.Semantics.Basic.normalizedValue kind exponent left))
    (rightNorm : 1 ≤ Gaussian.Norm.Basic.normSq (Parser.Semantics.Basic.normalizedValue kind exponent right))
    (leftSafe : Geometry.Rational.Sector.Eight.Safe sector
      (Parser.Semantics.Basic.normalizedValue kind exponent left))
    (rightSafe : Geometry.Rational.Sector.Eight.Safe sector
      (Parser.Semantics.Basic.normalizedValue kind exponent right)) :
    let leftHomogeneous : Line.GaussianLine :=
      ⟨1, Basic.Canonical.gamma * (Parser.Semantics.Basic.normalizedValue kind exponent left - sector.rep)⟩
    let rightHomogeneous : Line.GaussianLine :=
      ⟨1, Basic.Canonical.gamma * (Parser.Semantics.Basic.normalizedValue kind exponent right - sector.rep)⟩
    Chordal.Basic.chordalSq
        (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector) leftHomogeneous)
        (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector) rightHomogeneous) ≤
      (1 / 2 : Fraction.Rational) *
        Chordal.Basic.chordalSq
          leftHomogeneous rightHomogeneous := by
  dsimp only
  let leftTail :=
    Block.SafeReconstruction.safeBlockTail kind exponent sector left leftNorm leftSafe
  let rightTail :=
    Block.SafeReconstruction.safeBlockTail kind exponent sector right rightNorm rightSafe
  let leftHomogeneous : Line.GaussianLine :=
    ⟨1, Basic.Canonical.gamma * (Parser.Semantics.Basic.normalizedValue kind exponent left - sector.rep)⟩
  let rightHomogeneous : Line.GaussianLine :=
    ⟨1, Basic.Canonical.gamma * (Parser.Semantics.Basic.normalizedValue kind exponent right - sector.rep)⟩
  have leftEquivalent : leftTail.point.Equivalent leftHomogeneous := by
    exact
      Geometry.Projective.SectorBlock.Safe.Tail.ofSafe_point_equivalent_homogeneous sector
          (Parser.Semantics.Basic.normalizedValue kind exponent left) leftNorm leftSafe
  have rightEquivalent : rightTail.point.Equivalent rightHomogeneous := by
    exact
      Geometry.Projective.SectorBlock.Safe.Tail.ofSafe_point_equivalent_homogeneous sector
          (Parser.Semantics.Basic.normalizedValue kind exponent right) rightNorm rightSafe
  have leftTailValid := leftTail.point_valid
  have rightTailValid := rightTail.point_valid
  have leftHomogeneousValid :
      Line.Gaussian.Proj.HasNonzeroCoordinate leftHomogeneous :=
    by
      change (1 : Basic.Canonical) ≠ 0 ∨ _
      exact Or.inl one_ne_zero
  have rightHomogeneousValid :
      Line.Gaussian.Proj.HasNonzeroCoordinate rightHomogeneous :=
    by
      change (1 : Basic.Canonical) ≠ 0 ∨ _
      exact Or.inl one_ne_zero
  have determinantNonzero :=
    Block.Matrix.blockMatrix_det_ne kind exponent sector
  have leftActEquivalent := Line.Matrix.act_respects_equivalent
    (Block.Matrix.blockMatrix kind exponent sector) leftEquivalent
  have rightActEquivalent := Line.Matrix.act_respects_equivalent
    (Block.Matrix.blockMatrix kind exponent sector) rightEquivalent
  have leftTailImageValid :=
    Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
      determinantNonzero leftTailValid
  have rightTailImageValid :=
    Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
      determinantNonzero rightTailValid
  have leftHomogeneousImageValid :=
    Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
      determinantNonzero leftHomogeneousValid
  have rightHomogeneousImageValid :=
    Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
      determinantNonzero rightHomogeneousValid
  have inputIdentity :
      Chordal.Basic.chordalSq leftTail.point rightTail.point =
        Chordal.Basic.chordalSq
          leftHomogeneous rightHomogeneous := by
    calc
      Chordal.Basic.chordalSq leftTail.point rightTail.point =
          Chordal.Basic.chordalSq
            leftHomogeneous rightTail.point :=
        Chordal.Equivalence.chordalSq_eq_of_equivalent_left
          leftTailValid leftHomogeneousValid leftEquivalent rightTail.point
      _ = Chordal.Basic.chordalSq
          leftHomogeneous rightHomogeneous :=
        Chordal.Equivalence.chordalSq_eq_of_equivalent_right
          rightTailValid rightHomogeneousValid rightEquivalent leftHomogeneous
  have outputIdentity :
      Chordal.Basic.chordalSq
          (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector) leftTail.point)
          (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector) rightTail.point) =
        Chordal.Basic.chordalSq
          (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector) leftHomogeneous)
          (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector)
            rightHomogeneous) := by
    calc
      Chordal.Basic.chordalSq
          (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector) leftTail.point)
          (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector) rightTail.point) =
          Chordal.Basic.chordalSq
            (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector) leftHomogeneous)
            (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector) rightTail.point) :=
        Chordal.Equivalence.chordalSq_eq_of_equivalent_left
          leftTailImageValid leftHomogeneousImageValid leftActEquivalent _
      _ = Chordal.Basic.chordalSq
          (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector) leftHomogeneous)
          (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector)
            rightHomogeneous) :=
        Chordal.Equivalence.chordalSq_eq_of_equivalent_right
          rightTailImageValid rightHomogeneousImageValid rightActEquivalent _
  rw [← outputIdentity, ← inputIdentity]
  exact safeBlockTail_pair_contraction kind exponent sector left right
    leftNorm rightNorm leftSafe rightSafe
end Purelib.Data.CCL.Encoding.Block.SafeContraction

end
