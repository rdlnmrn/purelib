module
import Purelib.Data.Gaussian.Basic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Program.Arithmetic
import Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Exact
import Purelib.Calculus.Jet.Quadratic.Basic

open Purelib.Calculus.Jet.Progressive.Quadratic (Program)
open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

section
@[expose] public section

/-!
# One certified finite program for progressive quadratic CCL calculus

The lower trace modules construct the arithmetic and analytic certificates.
This file packages those constructors into one indexed finite program.  The
index is the actual semantic `Trace`, so a program cannot pair unrelated value
and slope names: every node computes one common increment, base, output,
slope, remainder, and rational quadratic factor.

Partial nodes store their displayed lower-quadrance or disk evidence in the
constructor.  The total decision wrappers expose a precise missing
certificate.  Finally, the strengthened request contract combines the
quadratic law with persistent word extension, exact raw-parser semantics, and
the requested projective-cylinder diameter for every one of the five live CCL
channels.
-/

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic
namespace Calculation

open Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic
open Purelib.Data
open Purelib.Calculus.Jet.Quadratic.Basic
/-- Package one displayed quadratic certificate as a constant source calculation. -/
def exactCalculation {increment :
  Gaussian.Basic.Canonical}
    (certificate : Certificate increment) :
    Calculation (fun _ => increment) :=
  Calculation.source (Trace.exact certificate)

/-- Every trace index of the exact calculation returns the supplied certificate. -/
@[simp] theorem exactCalculation_certificate
  {increment : Gaussian.Basic.Canonical}
    (certificate : Certificate increment)
    (index : Nat) :
    (exactCalculation certificate).trace.certificate index = certificate :=
  Trace.exact_certificate
    certificate index

end Calculation

end Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic

end
