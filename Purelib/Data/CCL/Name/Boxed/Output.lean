module
import Purelib.Approximation.Gaussian.Name.CCL.Grammar
import Purelib.Data.CCL.Name.Boxed.Apart
public import Purelib.Data.CCL.Name.Boxed.Arithmetic
import Purelib.Data.CCL.Name.Boxed.Process
import Purelib.Data.CCL.Transducer.Machine.Advance
public import Purelib.Data.CCL.Transducer.Machine.Grammar.Basic
import Purelib.Data.CCL.Name.Boxed.Approximation
import Purelib.Data.CCL.Transducer.Machine.Basic
public import Purelib.Approximation.Gaussian.Name.CCL.Output

section
@[expose] public section

/-!
# Boxed CCL names as arithmetic enclosure processes

This is the deliberate one-way bridge from an ordinary raw CCL word plus a
finite rational box sidecar to the generic arithmetic process.  The raw
encoder, parser, and boxed-name definitions do not import this module.
-/

namespace Purelib.Data.CCL.Name.Boxed.Output
namespace ProgressiveName

section
open Purelib.Data.CCL.Name
open Purelib.Data.CCL.Transducer
/-- A finite request from the boxed name's exact initial machine extends its prefix and emits exactly the requested bit
count. -/
theorem output_productive (name :
  Boxed.Process.ProgressiveName) (count : Nat) :
    ((Boxed.Approximation.ProgressiveName.toNamed name).machine).emitted.IsPrefix
        (Machine.Advance.advance
          (Boxed.Approximation.ProgressiveName.toNamed name).machine count).emitted ∧
      (Machine.Advance.advance
          (Boxed.Approximation.ProgressiveName.toNamed name).machine count).emitted.length = count :=
  (Boxed.Approximation.ProgressiveName.toNamed name).productive count

/-- The sum of the two retained boxed-name approximations produces exactly the requested number of prefix-extending
bits. -/
theorem add_output_productive (left right :
  Boxed.Process.ProgressiveName) (count : Nat) :
    (Boxed.Arithmetic.ProgressiveName.addOutput left right).machine.emitted.IsPrefix
        (Machine.Advance.advance
          (Boxed.Arithmetic.ProgressiveName.addOutput left right).machine count).emitted ∧
      (Machine.Advance.advance
          (Boxed.Arithmetic.ProgressiveName.addOutput left right).machine count).emitted.length = count :=
  (Boxed.Arithmetic.ProgressiveName.addOutput left right).productive count

/-- The difference of the two retained boxed-name approximations produces exactly the requested number of
prefix-extending bits. -/
theorem sub_output_productive (left right :
  Boxed.Process.ProgressiveName) (count : Nat) :
    (Boxed.Arithmetic.ProgressiveName.subOutput left right).machine.emitted.IsPrefix
        (Machine.Advance.advance
          (Boxed.Arithmetic.ProgressiveName.subOutput left right).machine count).emitted ∧
      (Machine.Advance.advance
          (Boxed.Arithmetic.ProgressiveName.subOutput left right).machine count).emitted.length = count :=
  (Boxed.Arithmetic.ProgressiveName.subOutput left right).productive count

/-- The product of the two retained boxed-name approximations produces exactly the requested number of prefix-extending
bits. -/
theorem mul_output_productive (left right :
  Boxed.Process.ProgressiveName) (count : Nat) :
    (Boxed.Arithmetic.ProgressiveName.mulOutput left right).machine.emitted.IsPrefix
        (Machine.Advance.advance
          (Boxed.Arithmetic.ProgressiveName.mulOutput left right).machine count).emitted ∧
      (Machine.Advance.advance
          (Boxed.Arithmetic.ProgressiveName.mulOutput left right).machine count).emitted.length = count :=
  (Boxed.Arithmetic.ProgressiveName.mulOutput left right).productive count

/-- Division using apartness of the same right boxed name produces exactly the requested number of prefix-extending
bits. -/
theorem div_output_productive (left right :
  Boxed.Process.ProgressiveName)
    (apart : Data.CCL.Name.Boxed.Apart right) (count : Nat) :
    (Boxed.Arithmetic.ProgressiveName.divOutput left right apart).machine.emitted.IsPrefix
        (Machine.Advance.advance
          (Boxed.Arithmetic.ProgressiveName.divOutput left right apart).machine count).emitted ∧
      (Machine.Advance.advance
          (Boxed.Arithmetic.ProgressiveName.divOutput left right apart).machine count).emitted.length = count :=
  (Boxed.Arithmetic.ProgressiveName.divOutput left right apart).productive count

end

section
open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Name
open Purelib.Data.CCL.Transducer
/-- Every finite advance of the exact boxed-name sum preserves the committed-word parser grammar. -/
theorem add_output_grammar (left right :
  Boxed.Process.ProgressiveName) (count : Nat) :
    Data.CCL.Transducer.Machine.Grammar.Invariant
      (Machine.Advance.advance
        (Boxed.Arithmetic.ProgressiveName.addOutput left right).machine count) :=
  Name.CCL.Grammar.Named.machine_advance_invariant
    (Boxed.Arithmetic.ProgressiveName.addOutput left right) count

/-- Every finite advance of the exact boxed-name difference preserves the committed-word parser grammar. -/
theorem sub_output_grammar (left right :
  Boxed.Process.ProgressiveName) (count : Nat) :
    Data.CCL.Transducer.Machine.Grammar.Invariant
      (Machine.Advance.advance
        (Boxed.Arithmetic.ProgressiveName.subOutput left right).machine count) :=
  Name.CCL.Grammar.Named.machine_advance_invariant
    (Boxed.Arithmetic.ProgressiveName.subOutput left right) count

/-- Every finite advance of the exact boxed-name product preserves the committed-word parser grammar. -/
theorem mul_output_grammar (left right :
  Boxed.Process.ProgressiveName) (count : Nat) :
    Data.CCL.Transducer.Machine.Grammar.Invariant
      (Machine.Advance.advance
        (Boxed.Arithmetic.ProgressiveName.mulOutput left right).machine count) :=
  Name.CCL.Grammar.Named.machine_advance_invariant
    (Boxed.Arithmetic.ProgressiveName.mulOutput left right) count

/-- Every finite advance of the exact boxed-name quotient with retained right apartness preserves the committed-word
parser grammar. -/
theorem div_output_grammar (left right :
  Boxed.Process.ProgressiveName)
    (apart : Data.CCL.Name.Boxed.Apart right) (count : Nat) :
    Data.CCL.Transducer.Machine.Grammar.Invariant
      (Machine.Advance.advance
        (Boxed.Arithmetic.ProgressiveName.divOutput left right apart).machine count) :=
  Name.CCL.Grammar.Named.machine_advance_invariant
    (Boxed.Arithmetic.ProgressiveName.divOutput left right apart) count

end

end ProgressiveName

end Purelib.Data.CCL.Name.Boxed.Output

end
