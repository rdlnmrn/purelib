module
import Purelib.Data.Gaussian.Basic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Observation
import Purelib.Data.Rat.Fraction
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Projection
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.CCL.Cursor

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

section
@[expose] public section

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Trace
section Trace

open Purelib.Data
/-- The finite enclosure, quadratic-law and word-growth guarantees for a common-index request.

At the selected refinement index, all five root radii squared are below the positive target and their centers obey the
exact expansion and remainder bound. Requesting count more bits from each initialized cursor increases its emitted
length by exactly count. -/
def RequestContract {increment : Nat →
  Canonical}
    (trace : Trace increment) (current : Nat) (target : Rat.Fraction.Rational)
    (positive : 0 < target) (count : Nat) : Prop :=
    let index := trace.requestIndex current target
    let cursors := trace.cursorTableAt index
    (trace.incrementApproximation.toProcess.ball index).radiusSq < target ∧
      (trace.baseApproximation.toProcess.ball index).radiusSq < target ∧
      (trace.outputApproximation.toProcess.ball index).radiusSq < target ∧
      (trace.slopeApproximation.toProcess.ball index).radiusSq < target ∧
      (trace.remainderApproximation.toProcess.ball index).radiusSq < target ∧
      (trace.outputApproximation.toProcess.ball index).center -
          (trace.baseApproximation.toProcess.ball index).center -
          (trace.incrementApproximation.toProcess.ball index).center *
            (trace.slopeApproximation.toProcess.ball index).center =
        (trace.remainderApproximation.toProcess.ball index).center ∧
      Canonical.normSq (trace.remainderApproximation.toProcess.ball index).center ≤
        (trace.certificate index).factor *
          Canonical.normSq (trace.incrementApproximation.toProcess.ball index).center ^ 2 ∧
      ∀ entry, entry ∈ cursors.entries →
        (entry.request target positive count).cursor.machine.emitted.length =
          entry.cursor.machine.emitted.length + count

/-- Every positive common-index trace request satisfies its finite request contract.

The proof combines the shared geometric accuracy bound, the retained certificate at the selected index, and exact word
growth for each initialized channel cursor. -/
theorem bitstream_and_quadratic_law {increment : Nat
  → Canonical}
    (trace : Trace increment) (current : Nat) (target : Rat.Fraction.Rational)
    (positive : 0 < target) (count : Nat) :
    RequestContract trace current target positive count := by
  let index := trace.requestIndex current target
  let cursors := trace.cursorTableAt index
  have accurate := trace.requestIndex_accurate current positive
  rcases trace.root_radius_eq index with
    ⟨incrementRadius, baseRadius, outputRadius, slopeRadius,
      remainderRadius⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, trace.root_expansion index,
    trace.root_remainder_le index, ?_⟩
  · rw [incrementRadius]
    exact accurate
  · rw [baseRadius]
    exact accurate
  · rw [outputRadius]
    exact accurate
  · rw [slopeRadius]
    exact accurate
  · rw [remainderRadius]
    exact accurate
  · intro entry member
    exact entry.request_word_length target positive count
end Trace

end Purelib.Calculus.Jet.Progressive.Quadratic.Trace

end
