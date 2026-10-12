module

import Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL.History
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Sharpness
import Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound
import Purelib.NumberTheory.Approximation.Best.Error
import Purelib.Data.List.BinaryPrefix.Decision
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.CCL.Encoding.Parser.Next
import Purelib.Data.CCL.Encoding.Parser.Semantics.State
import Purelib.Data.CCL.Encoding.Parser.Semantics.Prefix
import Purelib.Data.CCL.Encoding.Parser.Terminal.Input
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.LinearAlgebra.Coordinates2.Matrix

/-!
# Growth beyond an exposed joint sharpness reserve

The initial reserve exposes one actual window and one raw bit. Its exact
word is retained before a new request adds both a window and a bit. Kernel
certificates check counts, nesting, the saved prefix and complete old window
laws; the compiled runner checks the same actual construction. Separate
closed cases preserve the initial/loop equality boundaries and the exact
affine terminal-input convention.
-/

namespace Test.NumberTheory.Approximation.Unreserved

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.CCL.Encoding
open Purelib.Geometry.Rational
open Purelib.NumberTheory.Approximation
open Purelib.NumberTheory.Approximation.Dirichlet.Critical
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2

/-- The displayed rational threshold is strictly on the sharper side of the window boundary. -/
private theorem sharper : Sharpness.IsSharperWindowThreshold (9 / 10 : Fraction.Rational) := by
  unfold Sharpness.IsSharperWindowThreshold Sharpness.windowBoundaryPolynomial
  decide

/-- The new request pays one additional window and bit beyond the already exposed endpoints. -/
private def request : CCL.History.Request := ⟨0, 1, 1⟩

/-- Retain both original parents while executing the exact reserve and its later extension once. -/
private def computation :
    Σ initial : CCL.History.Initialization (9 / 10 : Fraction.Rational) sharper 0 1 1,
      CCL.History.Extension initial.next request :=
  let initial := CCL.History.reserve sharper 0 1 1
  ⟨initial, initial.next.extend request⟩

/-- Read the original complete initialization receipt without repeating its construction. -/
private def initial := computation.1

/-- Read the actual later joint extension with the same original initial state as its parent. -/
private def grown := computation.2

/-- Retain the exact word exposed before the request goes beyond both initial reserve endpoints. -/
private def savedWord : List Bool := initial.next.word

/-- Both original finite reserve endpoints have been reached before the extension request. -/
private theorem reserveReached : initial.next.robust.windows.length = 1 ∧ savedWord.length = 1 :=
  ⟨initial.windowCount, initial.wordLength⟩

/-- The actual later state pays both additional counts beyond the original reserve. -/
private theorem reserveExceeded : grown.next.robust.windows.length = 2 ∧ grown.next.word.length = 2 := by
  constructor
  · have count := grown.windowCount
    change grown.next.robust.windows.length = initial.next.robust.windows.length + 1 at count
    rewrite [initial.windowCount] at count
    exact count
  · have count := grown.wordLength
    change grown.next.word.length = initial.next.word.length + 1 at count
    rewrite [initial.wordLength] at count
    exact count

/-- The returned word extends the exact saved word rather than a recomputed initial encoding. -/
private theorem savedWordExtended : savedWord.IsPrefix grown.next.word := grown.wordPrefix

/-- The actual later box is proper and lies strictly inside the exact earlier enclosure. -/
private theorem properNested : grown.next.box.Proper ∧ grown.next.box.StrictInterior initial.next.box :=
  ⟨grown.next.proper, grown.nested⟩

/-- The later rational witness satisfies both the exact saved word and the retained earlier enclosure. -/
private theorem savedWitness : Parser.Semantics.Prefix.Represented savedWord grown.next.point ∧
    initial.next.box.Contains grown.next.point :=
  ⟨grown.earlierWordRepresented, (Box.Refinement.StrictInterior.refines grown.nested).contains grown.next.point_inside⟩

/-- Every original window keeps its complete consecutive-best and violation certificates throughout the new box. -/
private theorem earlierCertificates (point : Gaussian.Basic.Canonical) (inside : grown.next.box.Contains point)
    (entry : Robust.WindowHistory.Entry (9 / 10 : Fraction.Rational)) (member : entry ∈ initial.next.robust.windows) :
    Best.Consecutive.Basic.AreConsecutiveBest point entry.2.lower entry.2.upper ∧
      1 < (9 / 10 : Fraction.Rational) *
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance point entry.2.lower entry.2.upper :=
  ⟨grown.next.robust.uniformConsecutive point (grown.next.boxEq ▸ inside) entry (grown.earlier_mem entry member),
    grown.next.robust.uniformViolation point (grown.next.boxEq ▸ inside) entry (grown.earlier_mem entry member)⟩

/-- Actual upper-denominator scales grow strictly across the original/new window join. -/
private theorem scalesStrict : grown.next.robust.windows.Pairwise fun earlier later =>
    Best.Error.denominatorQuadrance earlier.2.upper < Best.Error.denominatorQuadrance later.2.upper :=
  grown.next.robust.scalesStrict

/-- The exact Gaussian equality boundary has squared norm two. -/
private def boundary : Gaussian.Basic.Canonical := Gaussian.Basic.Canonical.gamma

/-- Equality at squared norm two belongs to the original initial high branch. -/
private theorem initialBoundary : Parser.Next.CanAdvanceAt Parser.State.initialState true boundary ∧
    ¬Parser.Next.CanAdvanceAt Parser.State.initialState false boundary := by
  constructor <;> decide

/-- The loop boundary uses its original strict-lower and weak-upper radial convention. -/
private def loopState : Parser.State := ⟨.loopUnary 0, Matrix2.identityMatrix, []⟩

/-- Equality at squared norm two ends the loop unary header under the unchanged boundary convention. -/
private theorem loopBoundary : Parser.Next.CanAdvanceAt loopState false boundary ∧
    ¬Parser.Next.CanAdvanceAt loopState true boundary := by
  constructor <;> decide

/-- The original initial-high word retains exactly two sector bits before its terminal final choice. -/
private def terminalWord : List Bool := [true, false, false, false]

/-- The exact original parser state for the retained terminal fragment. -/
private def terminalState : Parser.State := Parser.State.parse terminalWord

/-- The original rational boundary input is represented before its terminal final sector bit. -/
private theorem terminalRepresents : Parser.Semantics.State.Represents terminalState boundary boundary := by
  refine ⟨?_, ?_, (Parser.State.holdsBool_eq_true terminalState boundary).mp (by decide)⟩
  · decide
  · decide

/-- Neither original final-bit choice has a nonzero normalized residual at the represented terminal input. -/
private theorem terminalNoAdvance : ∀ bit, ¬Parser.Next.CanAdvanceAt terminalState bit boundary := by
  intro bit
  cases bit <;> decide

/-- The original terminal classifier retains this exact input in its finite candidate list. -/
private theorem terminalListed : boundary ∈ Parser.Terminal.inputs terminalState :=
  Parser.Terminal.input_mem_of_no_advance terminalState boundary boundary terminalRepresents terminalNoAdvance

/-- A terminal final sector bit cannot be silently treated as an affine raw-prefix realization at the same input. -/
private theorem terminalNotAffine : ¬Parser.Semantics.Prefix.Represented (terminalWord ++ [false]) boundary := by
  intro represented
  rcases represented with ⟨tail, tailRepresents⟩
  have possible : Parser.Semantics.Prefix.CanStep terminalState boundary false :=
    ⟨tail, Parser.State.parse_append_singleton terminalWord false ▸ tailRepresents⟩
  exact terminalNoAdvance false
    ((Parser.Next.canStep_iff_canAdvanceAt terminalState boundary boundary
      (Parser.State.parse_det_ne terminalWord) terminalRepresents false).mp possible)

/-- Check the actual cached reserve and extension readbacks without evaluating any kernel proof by native decision. -/
public def run : IO Unit := do
  let receipt := computation
  let old := receipt.1.next
  let later := receipt.2.next
  let saved := old.word
  unless old.robust.windows.length == 1 && saved.length == 1 &&
      later.robust.windows.length == 2 && later.word.length == 2 do
    throw (IO.userError "unreserved request counts did not exceed both original reserves")
  unless List.BinaryPrefix.Decision.isWordPrefix saved later.word do
    throw (IO.userError "the exact saved word was not retained")
  unless decide (later.box.xLower < later.box.xUpper ∧ later.box.yLower < later.box.yUpper) &&
      decide (later.box.StrictInterior old.box) do
    throw (IO.userError "the actual returned box is not a proper strict nested box")
  unless later.enclosure.state.holdsBool later.witness.tail do
    throw (IO.userError "the retained rational witness failed the exact raw parser constraints")
  for entry in later.robust.windows do
    unless decide ((1 : Fraction.Rational) < (9 / 10 : Fraction.Rational) *
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance later.point entry.2.lower entry.2.upper) do
      throw (IO.userError "an actual retained window failed its threshold violation")
  IO.print "unreserved: 1 to 2 windows, 1 to 2 raw bits; saved prefix, nested box and witness checked\n"

end Test.NumberTheory.Approximation.Unreserved
