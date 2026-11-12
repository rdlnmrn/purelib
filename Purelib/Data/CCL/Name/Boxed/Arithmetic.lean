module
public import Purelib.Data.CCL.Name.Boxed.Apart
import Purelib.Data.CCL.Name.Boxed.Process
import Purelib.Data.CCL.Name.Boxed.Approximation
public import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic

section
@[expose] public section

/-!
# Boxed CCL names as arithmetic enclosure processes

This is the deliberate one-way bridge from an ordinary raw CCL word plus a
finite rational box sidecar to the generic arithmetic process.  The raw
encoder, parser, and boxed-name definitions do not import this module.
-/

namespace Purelib.Data.CCL.Name.Boxed.Arithmetic
namespace ProgressiveName

open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Name
/-- Add the exact named approximations of the two retained progressive boxed names. -/
def addOutput (left right : Process.ProgressiveName)
  : Name.Basic.Named :=
  (Approximation.ProgressiveName.toNamed left).add (Approximation.ProgressiveName.toNamed right)

/-- Subtract the right retained boxed-name approximation from the left one. -/
def subOutput (left right : Process.ProgressiveName)
  : Name.Basic.Named :=
  (Approximation.ProgressiveName.toNamed left).sub (Approximation.ProgressiveName.toNamed right)

/-- Multiply the exact named approximations of the two retained progressive boxed names. -/
def mulOutput (left right : Process.ProgressiveName)
  : Name.Basic.Named :=
  (Approximation.ProgressiveName.toNamed left).mul (Approximation.ProgressiveName.toNamed right)

/-- Divide the left retained boxed-name approximation by the right using apartness of that same right name. -/
def divOutput (left right : Process.ProgressiveName)
  (apart : Apart right) : Name.Basic.Named :=
  (Approximation.ProgressiveName.toNamed left).div (Approximation.ProgressiveName.toNamed right)
    apart.toNamedApart
end ProgressiveName

end Purelib.Data.CCL.Name.Boxed.Arithmetic

end
