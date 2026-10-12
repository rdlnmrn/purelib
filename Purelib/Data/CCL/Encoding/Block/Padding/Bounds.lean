module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Enclosure.Residual
public import Purelib.Data.CCL.Encoding.Block.Matrix
import Purelib.Data.CCL.Encoding.Block.Semantics
public import Purelib.Data.CCL.Encoding.Padding.Residual
public import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Chordal.DyadicTail
import Purelib.Geometry.Projective.Homography.Semantics
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.CCL.Encoding.Block.Homogeneous
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic

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

namespace Purelib.Data.CCL.Encoding.Block.Padding.Bounds

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- A terminal block reconstructs the original affine value and its infinity tail meets the requested dyadic chordal
bound. -/
theorem terminalBlock_exact_and_bounded
    (kind : Parser.Syntax.BlockKind) (exponent count : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector)
    (value : Basic.Canonical)
    (residualZero : Parser.Semantics.Basic.normalizedValue kind exponent value - sector.rep = 0) :
    Line.Proj.Equivalent
        (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector) Line.Proj.omega)
        (Line.Proj.affine value) ∧
      Chordal.Basic.chordalSq Line.Proj.omega Line.Proj.omega ≤
        1 / (1 + (2 : Fraction.Rational) ^ count) :=
  And.intro (Block.Homogeneous.terminalBlock_exact kind exponent sector value residualZero)
    (Chordal.DyadicTail.LoopTail.chordalSq_omega_le
      (Chordal.DyadicTail.LoopTail.omega (count := count)))

open Purelib in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- A certified small nonzero residual yields exact block reconstruction and the requested dyadic chordal tail bound.

The retained ball contains the exact normalized residual and meets paddingTarget at the supplied count. Its inverse
gamma-scaled affine tail reconstructs the original value and lies within one divided by one plus two to that count of
infinity in squared chordal distance. -/
theorem affineSmallResidual_exact_and_bounded
    (kind : Parser.Syntax.BlockKind) (exponent count : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector)
    (value : Basic.Canonical) (ball : Approximation.Gaussian.Enclosure.Ball)
    (small : Approximation.Gaussian.Enclosure.Residual.SmallBall ball
      (Padding.Residual.paddingTarget count))
    (inside : ball.Contains
      (Parser.Semantics.Basic.normalizedValue kind exponent value - sector.rep))
    (residualNonzero :
      Parser.Semantics.Basic.normalizedValue kind exponent value - sector.rep ≠ 0) :
    let tail := (Basic.Canonical.gamma *
      (Parser.Semantics.Basic.normalizedValue kind exponent value - sector.rep))⁻¹
    Line.Proj.Equivalent
        (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector)
          (Line.Proj.affine tail))
        (Line.Proj.affine value) ∧
      Chordal.Basic.chordalSq
          (Line.Proj.affine tail) Line.Proj.omega ≤
        1 / (1 + (2 : Fraction.Rational) ^ count) := by
  let residual := Parser.Semantics.Basic.normalizedValue kind exponent value - sector.rep
  let tail := (Basic.Canonical.gamma * residual)⁻¹
  have denominatorNonzero :=
    Block.Semantics.block_inverse_denominator_ne
      kind exponent sector value residualNonzero
  have evaluation := Block.Semantics.block_homographic_inverse
    kind exponent sector value residualNonzero
  have exactAffine := Homography.Semantics.actAffine_equivalent_homographic
    (Block.Matrix.blockMatrix kind exponent sector) tail value denominatorNonzero evaluation
  have large := Padding.Residual.inverseTail_large
    residualNonzero
      (Approximation.Gaussian.Enclosure.Residual.normSq_lt_of_contains small inside)
  exact And.intro exactAffine
    (Chordal.DyadicTail.LoopTail.chordalSq_omega_le
      (Chordal.DyadicTail.LoopTail.affine tail large))

end Purelib.Data.CCL.Encoding.Block.Padding.Bounds

end
