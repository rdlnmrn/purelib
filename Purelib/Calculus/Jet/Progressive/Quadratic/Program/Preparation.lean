module
import Purelib.Data.Gaussian.Basic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Program.Arithmetic
import Purelib.Calculus.Jet.Preparation.Diagnostic
import Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Preparation.Automatic

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Calculus.Jet.Progressive.Quadratic (Program)

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

/-! ## Explicit decisions for partial constructors -/

section
open Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Preparation
open Purelib.Calculus.Jet.Preparation.Diagnostic
open Purelib.Data
/-- Construct a reciprocal calculation from supplied apartness or report the missing bound.

Supplied evidence contains uniform positive lower bounds for both base and output quadrances. Missing base or output
evidence returns the corresponding diagnostic. -/
def decideReciprocal {increment : Nat →
  Canonical}
    (calculation : Calculation increment) :
    Automatic.AutomaticReciprocalEvidence
        calculation.trace → Decision (Calculation increment)
  | .supplied baseLower outputLower basePositive outputPositive
      baseApart outputApart =>
      .accepted (calculation.reciprocal baseLower outputLower basePositive
        outputPositive baseApart outputApart)
  | .missingBaseApartness => .rejected .denominatorApartness
  | .missingOutputApartness => .rejected .outputApartness

/-- Construct an exponential calculation from supplied unit-disk evidence.

The supplied branch retains bounds for base, movement and increment at every trace index. The missing branch reports the
input-disk obligation. -/
def decideExponential {increment : Nat →
  Canonical}
    (calculation : Calculation increment) :
    Automatic.AutomaticExponentialEvidence
        calculation.trace → Decision (Calculation increment)
  | .supplied baseUnit movementUnit incrementUnit =>
      .accepted
        (calculation.exponential baseUnit movementUnit incrementUnit)
  | .missingDisk => .rejected .inputDisk

/-- Construct a reduced-logarithm calculation from supplied chart evidence.

The supplied branch retains the movement-disk and increment bounds. Missing chart evidence returns the
safe-logarithm-chart diagnostic. -/
def decideReducedLog {increment : Nat →
  Canonical}
    (calculation : Calculation increment) :
    Automatic.AutomaticReducedLogEvidence
        calculation.trace → Decision (Calculation increment)
  | .supplied movementDisk incrementUnit =>
      .accepted (calculation.reducedLog movementDisk incrementUnit)
  | .missingChart => .rejected .safeLogarithmChart

end

open Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic
open Purelib.Data
/-- Missing base apartness reports the denominator-apartness diagnostic. -/
@[simp] theorem
  decideReciprocal_missing_base
    {increment : Nat → Canonical} (calculation : Calculation increment) :
    (decideReciprocal calculation .missingBaseApartness).missing? =
      some .denominatorApartness := rfl

/-- Missing output apartness reports the output-apartness diagnostic. -/
@[simp] theorem
  decideReciprocal_missing_output
    {increment : Nat → Canonical} (calculation : Calculation increment) :
    (decideReciprocal calculation .missingOutputApartness).missing? =
      some .outputApartness := rfl

/-- Missing exponential disk evidence reports the input-disk diagnostic. -/
@[simp] theorem
  decideExponential_missing_disk
    {increment : Nat → Canonical} (calculation : Calculation increment) :
    (decideExponential calculation .missingDisk).missing? =
      some .inputDisk := rfl

/-- Missing reduced-logarithm chart evidence reports the safe-chart diagnostic. -/
@[simp] theorem
  decideReducedLog_missing_chart
    {increment : Nat → Canonical} (calculation : Calculation increment) :
    (decideReducedLog calculation .missingChart).missing? =
      some .safeLogarithmChart := rfl

/-! ## Strengthened persistent request contract -/

end Calculation

end Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic

end
