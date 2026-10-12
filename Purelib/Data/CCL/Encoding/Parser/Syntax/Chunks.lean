module
public import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
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

namespace Purelib.Data.CCL.Encoding.Parser.Syntax.Chunks

section
open Purelib.Data.CCL.Encoding
/-- The initial true bit selects high-unary count one. -/
@[simp] theorem consume_initial_high :
    Parser.Syntax.Phase.consume .initial [true] = .highUnary 1 := rfl

/-- The initial false-true pair selects low-unary count one. -/
@[simp] theorem consume_initial_low_unary :
    Parser.Syntax.Phase.consume .initial [false, true] = .lowUnary 1 := rfl

end

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- The initial two false bits and retained sector code complete a zero-exponent low block and enter loop-unary zero. -/
@[simp] theorem consume_initial_low_sector
    (sector : Data.ComplexContinuedFraction.Encoding.Sector) :
    Parser.Syntax.Phase.consume .initial (false :: false :: sector.code) =
      .loopUnary 0 := by
  cases sector <;> rfl

open Purelib.Data.CCL.Encoding in
/-- A true bit increments the retained low-unary counter by one. -/
@[simp] theorem consume_low_unary (count : Nat) :
    Parser.Syntax.Phase.consume (.lowUnary count) [true] = .lowUnary (count + 1) := rfl

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- A false separator and retained sector code complete the current low block and enter loop-unary zero. -/
@[simp] theorem consume_low_sector (count : Nat)
    (sector : Data.ComplexContinuedFraction.Encoding.Sector) :
    Parser.Syntax.Phase.consume (.lowUnary count) (false :: sector.code) =
      .loopUnary 0 := by
  cases sector <;> rfl

open Purelib.Data.CCL.Encoding in
/-- A true bit increments the retained loop-unary counter by one. -/
@[simp] theorem consume_residual_unary (count : Nat) :
    Parser.Syntax.Phase.consume (.loopUnary count) [true] = .loopUnary (count + 1) := rfl
namespace Machine
end Machine
end Purelib.Data.CCL.Encoding.Parser.Syntax.Chunks

end
