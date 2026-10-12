module
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Committed
import Purelib.Data.CCL.Transducer.Machine.Grammar.Basic
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Approximation.Process
import Purelib.RootIsolation.Track.CCL.Chordal
import Purelib.RootIsolation.Track.CCL.Productivity
import Purelib.RootIsolation.Track.CCL.Semantics
public import Purelib.RootIsolation.FTA.Squarefree.Approximation
import Mathlib.Algebra.Ring.Defs
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Data.CCL.Transducer (Machine Mode)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.FTA.Squarefree (AdapterResult)

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free box/CCL finite FTA interface

The winding calculation supplies the exact degree-many family and the total
shrinking box tracks.  Each finite accuracy request computes a nonzero
rational sample of its refined box, converts that sample to a canonical
Gaussian-integer fraction, and runs the terminating CCL encoder.  Thus the box
and projective records are carried together without extracting a quotient
representative or naming a completed root.
-/

namespace Purelib.RootIsolation.FTA.Squarefree.AdapterResult
section Result

/-- Every finite request on the selected original root cursor preserves its prefix and emits exactly the requested
count. -/
theorem arithmeticNameAt_productive
    {p : CoefficientPolynomial} (result :
      AdapterResult p)
    (index : Fin p.natDegree) (count : Nat) :
    (result.arithmeticNameAt index).machine.emitted.IsPrefix
        (Machine.Advance.advance
          (result.arithmeticNameAt index).machine count).emitted ∧
      (Machine.Advance.advance
          (result.arithmeticNameAt index).machine count).emitted.length =
        count :=
  Track.CCL.Productivity.initial_productive (result.trackAt index) count

/-- Every finite advance of the selected original root cursor preserves the parser grammar invariant. -/
theorem arithmeticNameAt_grammar
    {p : CoefficientPolynomial} (result :
      AdapterResult p)
    (index : Fin p.natDegree) (count : Nat) :
    Data.CCL.Transducer.Machine.Grammar.Invariant
      (Machine.Advance.advance
        (result.arithmeticNameAt index).machine count) :=
  Track.CCL.Productivity.initial_grammar (result.trackAt index) count

/-- The productive arithmetic cursor of every degree-indexed RFAP root track
also carries the exact projective semantics of that track's initial box. -/
theorem arithmeticNameAt_exact
    {p : CoefficientPolynomial} (result :
      AdapterResult p)
    (index : Fin p.natDegree) (count : Nat) :
    Data.CCL.Transducer.Machine.Semantics.Basic.ExactCursor
      (Track.Approximation.Process.toProcess (result.trackAt index))
      (result.trackAt index).initial
      (Machine.Advance.advance
        (result.arithmeticNameAt index).machine count) :=
  Track.CCL.Semantics.initial_exact (result.trackAt index) count

/-- Pointwise form: every admitted arithmetic tail after a finite request
reconstructs a rational point inside the corresponding Paper-I initial root
box.  It does not assert the existence of a completed root value. -/
theorem arithmeticNameAt_candidate_exact
    {p : CoefficientPolynomial} (result :
      AdapterResult p)
    (index : Fin p.natDegree) (count : Nat)
    {tail : Canonical}
    (possible :
      Mode.Semantics.SemanticMode.possible
        (Machine.Advance.advance
          (result.arithmeticNameAt index).machine count).mode tail) :
    ∃ value : Canonical,
      (result.trackAt index).initial.box.Contains value ∧
        (Geometry.Projective.Line.Matrix.act
          (Data.CCL.Encoding.Parser.State.parse
            (Machine.committed
              (Machine.Advance.advance
                (result.arithmeticNameAt index).machine count))).matrix
          (Mode.Semantics.SemanticMode.parserTail
            (Machine.Advance.advance
              (result.arithmeticNameAt index).machine count).mode tail)).Equivalent
                (Geometry.Projective.Line.Proj.affine value) :=
  Track.CCL.Semantics.toNamedAt_candidate_exact
    (result.trackAt index) (result.trackAt index).initial count possible

/-- The projective diameter represented by any two quantitative tails of one
RFAP root cursor is bounded by that root track's initial box diagonal. -/
theorem arithmeticNameAt_cursor_chordalSq_le_box_diagonal
    {p : CoefficientPolynomial} (result :
      AdapterResult p)
    (index : Fin p.natDegree) (count : Nat)
    {leftTail rightTail : Canonical}
    (leftPossible :
      Mode.Semantics.SemanticMode.possible
        (Machine.Advance.advance
          (result.arithmeticNameAt index).machine count).mode leftTail)
    (rightPossible :
      Mode.Semantics.SemanticMode.possible
        (Machine.Advance.advance
          (result.arithmeticNameAt index).machine count).mode rightTail) :
    let machine := Machine.Advance.advance
      (result.arithmeticNameAt index).machine count
    let parser := Data.CCL.Encoding.Parser.State.parse
      (Machine.committed machine)
    Geometry.Projective.Chordal.Basic.chordalSq
        (Geometry.Projective.Line.Matrix.act parser.matrix
          (Mode.Semantics.SemanticMode.parserTail
            machine.mode leftTail))
        (Geometry.Projective.Line.Matrix.act parser.matrix
          (Mode.Semantics.SemanticMode.parserTail
            machine.mode rightTail)) ≤
      (result.trackAt index).initial.box.diagonalSq :=
  Track.CCL.Chordal.toNamedAt_cursor_chordalSq_le_box_diagonal
    (result.trackAt index) (result.trackAt index).initial count
      leftPossible rightPossible

/-- The box descent and arithmetic cursor can be coupled at every displayed
accuracy: all admitted parser images lie within squared chordal diameter
`epsilon^2`. -/
theorem refinedArithmeticNameAt_cursor_chordalSq_le_requested
    {p : CoefficientPolynomial} (result :
      AdapterResult p)
    (index : Fin p.natDegree)
    (current : State.WindingOne.Basic.WindingOneState p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p))
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat)
    {leftTail rightTail : Canonical}
    (leftPossible :
      Mode.Semantics.SemanticMode.possible
        (Machine.Advance.advance
          (result.refinedArithmeticNameAt index current epsilon positive).machine
          count).mode leftTail)
    (rightPossible :
      Mode.Semantics.SemanticMode.possible
        (Machine.Advance.advance
          (result.refinedArithmeticNameAt index current epsilon positive).machine
          count).mode rightTail) :
    let machine := Machine.Advance.advance
      (result.refinedArithmeticNameAt index current epsilon positive).machine
      count
    let parser := Data.CCL.Encoding.Parser.State.parse
      (Machine.committed machine)
    Geometry.Projective.Chordal.Basic.chordalSq
        (Geometry.Projective.Line.Matrix.act parser.matrix
          (Mode.Semantics.SemanticMode.parserTail
            machine.mode leftTail))
        (Geometry.Projective.Line.Matrix.act parser.matrix
          (Mode.Semantics.SemanticMode.parserTail
            machine.mode rightTail)) ≤ epsilon ^ 2 :=
  Track.CCL.Chordal.refinedNamed_cursor_chordalSq_le_requested
    (result.trackAt index) current epsilon positive count
      leftPossible rightPossible
end Result
end Purelib.RootIsolation.FTA.Squarefree.AdapterResult

end
