module
import Purelib.Data.CCL.Encoding.Parser.Syntax
public import Purelib.Data.CCL.Transducer.Emission.Basic
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic

public import Purelib.Data.CCL.Transducer.Mode.Grammar
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code

section
@[expose] public section

/-!
# Raw-grammar certificate for progressive arithmetic output

The progressive arithmetic controller carries quantitative enclosure data,
but its visible output remains the original pure CCL bitstream.  This module
is the one-way bridge: it proves that each buffered controller chunk advances
the unchanged syntax-only raw parser to exactly the phase recorded by the
controller.  Nothing in the canonical parser depends on the sidecar.
-/

namespace Purelib.Data.CCL.Transducer.Emission.Grammar.Basic

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.CCL.Transducer
/-- Require the exact emitted bit chunk to advance the old mode's raw phase to the retained next mode's phase. -/
def EmissionFollows (mode : Data.CCL.Transducer.Mode)
  (emission :
  Data.CCL.Transducer.Emission) : Prop :=
  Parser.Syntax.Phase.consume (Mode.Grammar.modeRawPhase mode) emission.bits =
    Mode.Grammar.modeRawPhase emission.next

/-- A true bit increments the raw unary count of either retained regular block kind. -/
@[simp] theorem consume_regular_unary (kind :
  Mode.Basic.RegularKind) (count : Nat) :
    Parser.Syntax.Phase.consume (Mode.Grammar.regularRawPhase kind count) [true] =
      Mode.Grammar.regularRawPhase kind (count + 1) := by
  cases kind <;> rfl

end

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- A false separator followed by the retained sector code enters loop-unary count zero. -/
@[simp] theorem consume_regular_sector (kind :
  Mode.Basic.RegularKind) (count : Nat)
    (sector : Data.ComplexContinuedFraction.Encoding.Sector) :
    Parser.Syntax.Phase.consume (Mode.Grammar.regularRawPhase kind count) (false :: sector.code) =
      .loopUnary 0 := by
  cases kind <;> cases sector <;> rfl
namespace Machine
end Machine
end Purelib.Data.CCL.Transducer.Emission.Grammar.Basic

end
