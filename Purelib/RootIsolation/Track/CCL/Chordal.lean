module
import Purelib.Data.Rat.Fraction
import Purelib.RootIsolation.Track.CCL.Semantics
public import Purelib.Approximation.Gaussian.Name.CCL.Output
public import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.CCL.Transducer.Machine.Advance
public import Purelib.Data.CCL.Transducer.Machine.Committed
public import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Chordal.Box
import Purelib.Geometry.Projective.Chordal.Equivalence
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Projective.Line.Matrix.Gaussian
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Approximation.Name
import Purelib.RootIsolation.Track.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds

open Purelib.Data.CCL.Transducer (Machine Mode)
open Purelib.Geometry.Projective.Line (Proj)

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Winding-one tracks as progressive arithmetic processes

Paper I supplies independently shrinking rational boxes without asserting a
completed root.  This module exposes each such finite track directly through
the CCL-2 squared-error process interface.  The possibility predicate is
the current box predicate itself; no point is selected from an intersection.
-/

namespace Purelib.RootIsolation.Track.CCL.Chordal

/-- The exact raw-parser images of any two sidecar candidates after the same
finite request have squared chordal separation at most the source winding
box's squared diagonal.  This is the direct finite compatibility between the
box shrinker and the arithmetic CCL cursor. -/
theorem toNamedAt_cursor_chordalSq_le_box_diagonal
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Track.Basic.WindingOneTrack p ambient) (state : State.WindingOne.Basic.WindingOneState p ambient)
    (count : Nat) {leftTail rightTail : Gaussian.Basic.Canonical}
    (leftPossible :
      Mode.Semantics.SemanticMode.possible
        (Machine.Advance.advance
          (Track.Approximation.Name.toNamedAt track state).machine count).mode leftTail)
    (rightPossible :
      Mode.Semantics.SemanticMode.possible
        (Machine.Advance.advance
          (Track.Approximation.Name.toNamedAt track state).machine count).mode rightTail) :
    let machine := Machine.Advance.advance
      (Track.Approximation.Name.toNamedAt track state).machine count
    let parser := Data.CCL.Encoding.Parser.State.parse
      (Machine.committed machine)
    Geometry.Projective.Chordal.Basic.chordalSq
        (Geometry.Projective.Line.Matrix.act parser.matrix
          (Mode.Semantics.SemanticMode.parserTail
            machine.mode leftTail))
        (Geometry.Projective.Line.Matrix.act parser.matrix
          (Mode.Semantics.SemanticMode.parserTail
            machine.mode rightTail)) ≤ state.box.diagonalSq := by
  let machine := Machine.Advance.advance
    (Track.Approximation.Name.toNamedAt track state).machine count
  let parser := Data.CCL.Encoding.Parser.State.parse
    (Machine.committed machine)
  rcases Track.CCL.Semantics.toNamedAt_candidate_exact track state count leftPossible with
    ⟨leftValue, leftInside, leftExact⟩
  rcases Track.CCL.Semantics.toNamedAt_candidate_exact track state count rightPossible with
    ⟨rightValue, rightInside, rightExact⟩
  have parserDeterminant :
      LinearAlgebra.Coordinates2.Matrix.Matrix2.determinant parser.matrix ≠ 0 :=
    Data.CCL.Encoding.Parser.State.parse_det_ne
      (Machine.committed machine)
  have leftValid := Geometry.Projective.Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
    parserDeterminant
    (Mode.Semantics.SemanticMode.parserTail_valid
      machine.mode leftTail)
  have rightValid := Geometry.Projective.Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
    parserDeterminant
    (Mode.Semantics.SemanticMode.parserTail_valid
      machine.mode rightTail)
  dsimp only
  calc
    Geometry.Projective.Chordal.Basic.chordalSq
        (Geometry.Projective.Line.Matrix.act parser.matrix
          (Mode.Semantics.SemanticMode.parserTail
            machine.mode leftTail))
        (Geometry.Projective.Line.Matrix.act parser.matrix
          (Mode.Semantics.SemanticMode.parserTail
            machine.mode rightTail)) =
        Geometry.Projective.Chordal.Basic.chordalSq (Proj.affine leftValue)
          (Geometry.Projective.Line.Matrix.act parser.matrix
            (Mode.Semantics.SemanticMode.parserTail
              machine.mode rightTail)) :=
      Geometry.Projective.Chordal.Equivalence.chordalSq_eq_of_equivalent_left
        leftValid
        (Geometry.Projective.Line.Gaussian.Proj.affine_hasNonzeroCoordinate leftValue)
        leftExact _
    _ = Geometry.Projective.Chordal.Basic.chordalSq (Proj.affine leftValue)
        (Proj.affine rightValue) :=
      Geometry.Projective.Chordal.Equivalence.chordalSq_eq_of_equivalent_right
        rightValid
        (Geometry.Projective.Line.Gaussian.Proj.affine_hasNonzeroCoordinate rightValue)
        rightExact _
    _ ≤ state.box.diagonalSq :=
      Geometry.Projective.Chordal.Box.chordalSq_affine_le_box_diagonal
        leftInside rightInside

/-- At any requested box-descent accuracy, the corresponding arithmetic CCL
cursor has projective diameter at most the same displayed `epsilon^2`, for
every finite output length and every pair of admitted sidecar tails. -/
theorem refinedNamed_cursor_chordalSq_le_requested
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Track.Basic.WindingOneTrack p ambient) (state : State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat)
    {leftTail rightTail : Gaussian.Basic.Canonical}
    (leftPossible :
      Mode.Semantics.SemanticMode.possible
        (Machine.Advance.advance
          (Track.Approximation.Name.refinedNamed track state epsilon positive).machine count).mode
        leftTail)
    (rightPossible :
      Mode.Semantics.SemanticMode.possible
        (Machine.Advance.advance
          (Track.Approximation.Name.refinedNamed track state epsilon positive).machine count).mode
        rightTail) :
    let machine := Machine.Advance.advance
      (Track.Approximation.Name.refinedNamed track state epsilon positive).machine count
    let parser := Data.CCL.Encoding.Parser.State.parse
      (Machine.committed machine)
    Geometry.Projective.Chordal.Basic.chordalSq
        (Geometry.Projective.Line.Matrix.act parser.matrix
          (Mode.Semantics.SemanticMode.parserTail
            machine.mode leftTail))
        (Geometry.Projective.Line.Matrix.act parser.matrix
          (Mode.Semantics.SemanticMode.parserTail
            machine.mode rightTail)) ≤ epsilon ^ 2 :=
  (toNamedAt_cursor_chordalSq_le_box_diagonal track
    (track.refine state epsilon positive) count leftPossible
      rightPossible).trans (track.accurate state epsilon positive)
end Purelib.RootIsolation.Track.CCL.Chordal

end
