module
public import Purelib.Data.CCL.Transducer.Machine.Grammar.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.CCL.Transducer.Machine.Committed
public import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Data.Gaussian.Field
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Constants

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

namespace Purelib.Data.CCL.Transducer.Machine.Semantics.Basic

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- Certify a retained machine's grammar and exact projective representation relative to the original process state.

For each possible current tail, retain a value possible at that same origin state whose affine point equals the
committed parser-matrix image of the tail projectively. The certificate keeps the original process owner and dependent
state. -/
structure ExactCursor (origin :
    Approximation.Gaussian.Process)
  (originState : origin.State)
    (machine : Data.CCL.Transducer.Machine) : Prop where
  /-- The retained machine's committed word parses to its exact mode phase. -/ grammar :
    Data.CCL.Transducer.Machine.Grammar.Invariant machine
  /-- Each possible current tail has an original-state possible witness with the same committed parser image
    projectively. -/ exact : ∀ {tail : Basic.Canonical}, Mode.Semantics.SemanticMode.possible machine.mode tail →
    ∃ value : Basic.Canonical,
      origin.Possible originState value ∧
        (Line.Matrix.act
          (Parser.State.parse
            (Data.CCL.Transducer.Machine.committed
              machine)).matrix
          (Mode.Semantics.SemanticMode.parserTail machine.mode tail)).Equivalent
            (Line.Proj.affine value)

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- The exact initial machine represents the same process state and satisfies its grammar invariant.

The empty committed word has the identity parser matrix. Its affine action
retains each possible original process value directly. -/
theorem ExactCursor.initial (origin :
    Approximation.Gaussian.Process)
  (originState : origin.State) :
    ExactCursor origin originState (Data.CCL.Transducer.Machine.initial origin originState) :=
  { grammar := Data.CCL.Transducer.Machine.Grammar.initial_invariant origin originState
    exact := by
      intro tail possible
      refine ⟨tail, possible, ?_⟩
      change (1 * tail + 0 * 1) * 1 = tail * (0 * tail + 1 * 1)
      have leftCoordinate : 1 * tail + 0 * 1 = tail := by
        rw [one_mul, zero_mul, add_zero]
      have rightCoordinate : 0 * tail + 1 * 1 = 1 := by
        rw [zero_mul, one_mul, zero_add]
      rw [leftCoordinate, rightCoordinate] }

end Purelib.Data.CCL.Transducer.Machine.Semantics.Basic

end

section
@[expose] public section

/-!
# Persistent finite requests for progressive CCL cursors

The raw arithmetic cursor already extends one finite `List Bool` prefix.  This
module adds the missing accuracy operation: refine the finite enclosure carried
by its current quantitative mode without changing either exposed or buffered
bits.  The refined ball is transported through the exact current projective
chart, giving an arbitrarily small rational squared-chordal cylinder bound.

Everything here is a finite request on an explicit machine.  No stream, limit,
intersection, or completed value is formed.
-/

namespace Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
open Purelib.Data.CCL.Transducer in
/-- The exact cursor certificate retaining the original process, dependent state and machine. -/
abbrev SourcePersistentProgressiveExactCursorAlias :=
  ExactCursor

end Purelib.Data.CCL.Transducer.Machine.Semantics.Basic

end

section
section
@[expose] public section

/-!
# Persistent output after retryable division preflight

Readiness returns an ordinary coherent name unchanged.  Consequently the
existing persistent cursor supplies exact raw-parser semantics, prefix
extension, and finite request lengths without any weakened partial variant.
-/

namespace Purelib.CCL.Progressive.PartialDivision
end Purelib.CCL.Progressive.PartialDivision

end

end
