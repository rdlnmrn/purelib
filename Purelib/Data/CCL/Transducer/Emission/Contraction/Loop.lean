module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Sector.Safe
public import Purelib.Approximation.Gaussian.Process.Sector.Residual
import Purelib.Data.CCL.Encoding.Block.Matrix
import Purelib.Data.CCL.Encoding.Block.SafeContraction
import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.CCL.Transducer.Mode.Bounds
public import Purelib.Data.CCL.Transducer.Mode.Parser
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Power
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Rational.Sector.Eight.Safe
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Process.Normalization.Decision
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Enclosure.Sector.Decision
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Exact projective semantics of progressive arithmetic cursors

The raw `Machine` remains the original bit-only cursor.  This module adds a
separate proof wrapper relating its quantitative mode to the ordinary raw
parser matrix.  In particular, residual modes are interpreted homogeneously
as `[1 : γr]`; this is an affine inverse tail when `r ≠ 0` and is exactly
`ω` when `r = 0`.  No equality decision on a completed value is needed.
-/

namespace Purelib.Data.CCL.Transducer.Emission.Contraction.Loop

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Geometry.Rational in
/-- The exact selected loop-sector block contracts two possible residual parser tails by a squared-chordal factor of
one-half.

Both residual values belong to the same based residual process and initial state. Their original sources inherit the
retained loop norm bound and safe-sector certificate, so the contraction uses this same block matrix and homogeneous
tails. -/
theorem loopStep_sector_pair_contraction
    (current : Mode.Basic.LoopState) (sector : Data.ComplexContinuedFraction.Encoding.Sector)
    (certificate : Enclosure.Sector.Safe.SafeBall sector
      (current.process.ball
        (current.domain.refinedState current.state)))
    (_selected : current.domain.decide current.state =
      .sector sector certificate)
    {leftResidual rightResidual : Basic.Canonical}
    (leftPossible :
      (Process.Sector.Residual.residualProcess current.process
        (current.domain.refinedState current.state) sector).Possible
          (Process.Sector.Residual.residualInitial current.process
            (current.domain.refinedState current.state) sector) leftResidual)
    (rightPossible :
      (Process.Sector.Residual.residualProcess current.process
        (current.domain.refinedState current.state) sector).Possible
          (Process.Sector.Residual.residualInitial current.process
            (current.domain.refinedState current.state) sector) rightResidual) :
    let leftTail : Line.GaussianLine := ⟨1, Basic.Canonical.gamma * leftResidual⟩
    let rightTail : Line.GaussianLine := ⟨1, Basic.Canonical.gamma * rightResidual⟩
    Chordal.Basic.chordalSq
        (Line.Matrix.act
          (Block.Matrix.blockMatrix
            (Mode.Parser.regularBlockKind current.kind) current.count sector)
          leftTail)
        (Line.Matrix.act
          (Block.Matrix.blockMatrix
            (Mode.Parser.regularBlockKind current.kind) current.count sector)
          rightTail) ≤
      (1 / 2 : Fraction.Rational) *
        Chordal.Basic.chordalSq leftTail rightTail := by
  dsimp only
  rcases leftPossible with
    ⟨leftSource, leftSourcePossible, leftResidualEqual⟩
  rcases rightPossible with
    ⟨rightSource, rightSourcePossible, rightResidualEqual⟩
  let leftRaw := Power.natPow Basic.Canonical.gamma current.count * leftSource
  let rightRaw := Power.natPow Basic.Canonical.gamma current.count * rightSource
  have leftNormalized :
      Parser.Semantics.Basic.normalizedValue
          (Mode.Parser.regularBlockKind current.kind) current.count leftRaw =
        leftSource :=
    Mode.Parser.regularNormalized_scaled current.kind current.count leftSource
  have rightNormalized :
      Parser.Semantics.Basic.normalizedValue
          (Mode.Parser.regularBlockKind current.kind) current.count rightRaw =
        rightSource :=
    Mode.Parser.regularNormalized_scaled current.kind current.count rightSource
  have leftNorm : 1 ≤ Data.Gaussian.Norm.Basic.normSq leftSource :=
    Mode.Bounds.loop_candidate_norm_lower current
      (current.domain.refinedState current.state) leftSourcePossible
  have rightNorm : 1 ≤ Data.Gaussian.Norm.Basic.normSq rightSource :=
    Mode.Bounds.loop_candidate_norm_lower current
      (current.domain.refinedState current.state) rightSourcePossible
  have leftSafe : Geometry.Rational.Sector.Eight.Safe sector leftSource :=
    Enclosure.Sector.Safe.safe_of_contains certificate
      (current.process.possible_inside leftSourcePossible)
  have rightSafe : Geometry.Rational.Sector.Eight.Safe sector rightSource :=
    Enclosure.Sector.Safe.safe_of_contains certificate
      (current.process.possible_inside rightSourcePossible)
  have leftRawNorm :
      1 ≤ Data.Gaussian.Norm.Basic.normSq (Parser.Semantics.Basic.normalizedValue
        (Mode.Parser.regularBlockKind current.kind) current.count leftRaw) := by
    rw [leftNormalized]
    exact leftNorm
  have rightRawNorm :
      1 ≤ Data.Gaussian.Norm.Basic.normSq (Parser.Semantics.Basic.normalizedValue
        (Mode.Parser.regularBlockKind current.kind) current.count rightRaw) := by
    rw [rightNormalized]
    exact rightNorm
  have leftRawSafe : Geometry.Rational.Sector.Eight.Safe sector
      (Parser.Semantics.Basic.normalizedValue
        (Mode.Parser.regularBlockKind current.kind) current.count leftRaw) := by
    rw [leftNormalized]
    exact leftSafe
  have rightRawSafe : Geometry.Rational.Sector.Eight.Safe sector
      (Parser.Semantics.Basic.normalizedValue
        (Mode.Parser.regularBlockKind current.kind) current.count rightRaw) := by
    rw [rightNormalized]
    exact rightSafe
  have contraction :=
    Block.SafeContraction.safeBlockHomogeneous_pair_contraction
        (Mode.Parser.regularBlockKind current.kind) current.count sector
        leftRaw rightRaw leftRawNorm rightRawNorm leftRawSafe rightRawSafe
  rw [leftNormalized, rightNormalized] at contraction
  rw [leftResidualEqual, rightResidualEqual]
  exact contraction

end Purelib.Data.CCL.Transducer.Emission.Contraction.Loop

end
