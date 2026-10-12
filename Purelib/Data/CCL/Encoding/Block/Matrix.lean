module

public import Purelib.Data.CCL.Encoding.Block.Basic
public import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Power
public import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix

import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
/-!
# Choice-free completed CCL blocks

Raw words, decoder matrices, determinants, and the strict post-inversion norm
estimate are all finite computations over constructive Gaussian fractions.
-/

@[expose] public section

namespace Purelib.Data.CCL.Encoding.Block.Matrix

open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Construct the regular Gaussian decoder matrix from the retained gamma exponent and sector representative. -/
def regularBlock (exponent : Nat) (sector : ComplexContinuedFraction.Encoding.Sector) :
  LinearAlgebra.Coordinates2.Matrix.GaussianMatrix :=
  ⟨Power.natPow Basic.Canonical.gamma (exponent + 1) * sector.rep,
    Power.natPow Basic.Canonical.gamma exponent, Basic.Canonical.gamma, 0⟩

open Purelib.Data.Gaussian in
open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Construct the diagonal Gaussian matrix that retains the initial-low gamma-power denominator scale. -/
def lowScale (exponent : Nat) :
  LinearAlgebra.Coordinates2.Matrix.GaussianMatrix :=
  ⟨1, 0, 0, Power.natPow Basic.Canonical.gamma exponent⟩

open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Construct the initial-low decoder matrix from the retained gamma exponent and sector representative. -/
def lowBlock (exponent : Nat) (sector : ComplexContinuedFraction.Encoding.Sector) :
  LinearAlgebra.Coordinates2.Matrix.GaussianMatrix :=
  ⟨Basic.Canonical.gamma * sector.rep, 1, Power.natPow Basic.Canonical.gamma (exponent + 1), 0⟩

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Data.Gaussian
open Purelib.Geometry.Projective
open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2
/-- The regular decoder matrix factors as gamma-power scaling, sector translation and gamma inversion. -/
theorem regularBlock_factorization (exponent : Nat) (sector :
  ComplexContinuedFraction.Encoding.Sector) :
    Matrix2.mul
        (Matrix2.mul (Line.Matrix.scale (Power.natPow Basic.Canonical.gamma exponent))
          (Line.Matrix.translate sector.rep))
        (Line.Matrix.invert Basic.Canonical.gamma) =
      regularBlock exponent sector := by
  apply Matrix2.ext <;>
    apply Basic.ext <;>
    simp only [Matrix2.mul, Line.Matrix.scale, Line.Matrix.translate,
      Line.Matrix.invert, regularBlock, Power.natPow_succ, Basic.add_re, Basic.add_im,
      Basic.mul_re, Basic.mul_im, Basic.zero_re, Basic.zero_im, Basic.one_re, Basic.one_im, Basic.Canonical.gamma] <;>
    ring1

/-- The initial-low decoder matrix factors as its retained diagonal scale, sector translation and gamma inversion. -/
theorem lowBlock_factorization (exponent : Nat) (sector :
  ComplexContinuedFraction.Encoding.Sector) :
    Matrix2.mul
        (Matrix2.mul (lowScale exponent) (Line.Matrix.translate sector.rep))
        (Line.Matrix.invert Basic.Canonical.gamma) =
      lowBlock exponent sector := by
  apply Matrix2.ext <;>
    apply Basic.ext <;>
    simp only [Matrix2.mul, Line.Matrix.translate, Line.Matrix.invert,
      lowScale, lowBlock, Power.natPow_succ, Basic.add_re, Basic.add_im, Basic.mul_re,
        Basic.mul_im,
      Basic.zero_re, Basic.zero_im, Basic.one_re, Basic.one_im, Basic.Canonical.gamma] <;>
    ring1

end

open Purelib.Data.CCL.Encoding
open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Data.Gaussian
open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2
/-- The regular decoder determinant is minus gamma to the successor retained exponent. -/
theorem regularBlock_det (exponent : Nat) (sector : ComplexContinuedFraction.Encoding.Sector) :
    Matrix2.Matrix2.determinant (regularBlock exponent sector) =
      -Power.natPow Basic.Canonical.gamma (exponent + 1) := by
  apply Basic.ext <;>
    simp only [Matrix2.Matrix2.determinant, regularBlock, Power.natPow_succ,
      Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im, Basic.neg_re, Basic.neg_im, Basic.zero_re, Basic.zero_im,
      Basic.Canonical.gamma] <;>
    ring1

/-- The initial-low decoder determinant is minus gamma to the successor retained exponent. -/
theorem lowBlock_det (exponent : Nat) (sector : ComplexContinuedFraction.Encoding.Sector) :
    Matrix2.Matrix2.determinant (lowBlock exponent sector) =
      -Power.natPow Basic.Canonical.gamma (exponent + 1) := by
  apply Basic.ext <;>
    simp only [Matrix2.Matrix2.determinant, lowBlock, Basic.sub_re, Basic.sub_im,
      Basic.mul_re, Basic.mul_im, Basic.neg_re, Basic.neg_im, Basic.zero_re, Basic.zero_im, Basic.one_re, Basic.one_im]
        <;>
    ring1
end Purelib.Data.CCL.Encoding.Block.Matrix

end

end

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
open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Read the decoder matrix determined by the retained block kind, exponent and sector. -/
def matrix (entry : _root_.Purelib.Data.CCL.Encoding.Block.Redundant) :
  _root_.Purelib.LinearAlgebra.Coordinates2.Matrix.GaussianMatrix :=
  match entry.kind with
  | .regular => Block.Matrix.regularBlock entry.exponent entry.sector
  | .initialLow => Block.Matrix.lowBlock entry.exponent entry.sector

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- The decoder matrix of the retained redundant block has nonzero determinant. -/
theorem matrix_det_ne (entry :
  _root_.Purelib.Data.CCL.Encoding.Block.Redundant) :
    Matrix2.Matrix2.determinant entry.matrix ≠ 0 := by
  cases entry with
  | mk kind exponent sector =>
      cases kind with
      | regular =>
          rw [matrix, Block.Matrix.regularBlock_det]
          exact Field.neg_ne_zero_direct
            (Power.natPow_ne_zero_direct Basic.Canonical.gamma (by decide) (exponent + 1))
      | initialLow =>
          rw [matrix, Block.Matrix.lowBlock_det]
          exact Field.neg_ne_zero_direct
            (Power.natPow_ne_zero_direct Basic.Canonical.gamma (by decide) (exponent + 1))
end Block

end Purelib.Data.CCL.Encoding.Block.Redundant

end

section
/-!
# Finite completed-block cylinders

A cylinder is represented by a finite list of completed raw CCL blocks and a
finite realization trace.  No collection of all compatible points is formed.
The main theorem compares any two supplied realization traces and obtains the
explicit `2⁻ⁿ` squared-chordal bound.
-/

@[expose] public section

namespace Purelib.Data.CCL.Encoding.Block
section Block

open Purelib.Data.CCL.Encoding in
open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Read the decoder matrix determined by the retained block kind, exponent and sector. -/
def matrix (block : Block) :
  LinearAlgebra.Coordinates2.Matrix.GaussianMatrix :=
  match block.kind with
  | .regular => Block.Matrix.regularBlock block.exponent block.sector
  | .initialLow => Block.Matrix.lowBlock block.exponent block.sector
end Block
section Block

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- The decoder matrix of every retained block has nonzero determinant. -/
theorem matrix_det_ne_zero (block : Block) :
    Matrix2.Matrix2.determinant block.matrix ≠ 0 := by
  cases block with
  | mk kind exponent sector =>
      cases kind with
      | regular =>
          rw [matrix, Block.Matrix.regularBlock_det]
          exact Field.neg_ne_zero_direct
            (Power.natPow_ne_zero_direct
              Basic.Canonical.gamma (by decide)
              (exponent + 1))
      | initialLow =>
          rw [matrix, Block.Matrix.lowBlock_det]
          exact Field.neg_ne_zero_direct
            (Power.natPow_ne_zero_direct
              Basic.Canonical.gamma (by decide)
              (exponent + 1))

end Block

end Purelib.Data.CCL.Encoding.Block

end

end

section
@[expose] public section

/-!
# Finite raw-prefix parser over constructive Gaussian fractions

The completed-block encoder is not enough for a persistent root name: a
request may stop inside a unary header or after only one or two sector bits.
This module records exactly that unfinished syntax, the finite decoder
product, and the finite list of already completed block constraints.  It is
the state needed by the box/CCL next-bit controller; no stream, completion,
or collection of compatible points is formed.
-/

namespace Purelib.Data.CCL.Encoding.Block.Matrix

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Choose the exact decoder matrix for an initial-high, initial-low or loop parser block. -/
def blockMatrix (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector
  : ComplexContinuedFraction.Encoding.Sector) : LinearAlgebra.Coordinates2.Matrix.GaussianMatrix :=
  match kind with
  | .initialLow => lowBlock exponent sector
  | .initialHigh | .loop =>
      regularBlock exponent sector

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Every parser block's retained decoder matrix has nonzero determinant. -/
theorem blockMatrix_det_ne
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : ComplexContinuedFraction.Encoding.Sector) :
    Matrix2.Matrix2.determinant
        (blockMatrix kind exponent sector) ≠ 0 := by
  cases kind with
  | initialHigh =>
      rw [blockMatrix, regularBlock_det]
      exact Field.neg_ne_zero_direct
        (Power.natPow_ne_zero_direct Basic.Canonical.gamma (by decide) (exponent + 1))
  | initialLow =>
      rw [blockMatrix, lowBlock_det]
      exact Field.neg_ne_zero_direct
        (Power.natPow_ne_zero_direct Basic.Canonical.gamma (by decide) (exponent + 1))
  | loop =>
      rw [blockMatrix, regularBlock_det]
      exact Field.neg_ne_zero_direct
        (Power.natPow_ne_zero_direct Basic.Canonical.gamma (by decide) (exponent + 1))
end Purelib.Data.CCL.Encoding.Block.Matrix

end
