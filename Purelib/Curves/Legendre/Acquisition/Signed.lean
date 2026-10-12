module
import Purelib.Topology.Knot.Braid.ThreeStrand.Word
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Acquisition.Signed.Certificate
public import Purelib.Approximation.Gaussian.Acquisition.Signed.Requested
public import Purelib.Approximation.Gaussian.Acquisition.Signed.Result
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Legendre.Acquisition.Automatic.Basic
import Purelib.Curves.Legendre.Acquisition.Automatic.Positive
import Purelib.Curves.Legendre.FractionalWords.Periods
public import Purelib.Curves.Legendre.GuaranteedFold
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Enclosure.Signed
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Acquisition.Signed

open Purelib.Approximation.Gaussian.Name

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.Acquisition

open Purelib.Curves.Legendre.Acquisition.Automatic

open Purelib.Curves.Legendre.FractionalWords

open Purelib.Data.Rat

open Purelib.Topology.Knot.Braid

section
@[expose] public section

/-!
# Bounded signed acquisition for Legendre input ratios

Requested-precision inspection always yields one of three mathematical
outcomes. The positive branch feeds the existing guaranteed word evaluators;
negative and near-boundary branches preserve their candidate evidence and
the exact state needed for subsequent work. A negative branch is not a
claim that all fractional transformations are undefined.
-/

namespace Purelib.Curves.Legendre.Acquisition.Signed.Report

open Purelib.Approximation.Gaussian.Acquisition.Signed.Result (OutcomePayload)

/-- Evaluate the retained finite word when signed acquisition proves positivity.

Negative and near-boundary outcomes preserve their certificates at the exact retained acquisition state. -/
def transport {tau : Coherent.CoherentNamed} {start :
  Approximation.Gaussian.Acquisition.State tau} {delta : Fraction.Rational} {positive : 0 < delta}
    (report : Requested.Report tau start delta positive) (word : ThreeStrand.Word) :
    OutcomePayload (Automatic.Basic.Ready tau word)
      (Certificate.Negative tau report.retained delta) (Certificate.Near tau report.retained delta) :=
  match report.2 with
  | .positive high _ => .ready
      (Positive.guaranteed (report.enclosure high) word)
  | .negative _ upper => .negative (report.negative upper)
  | .near bounds => .near (report.near bounds)

/-- Prepare the dependent finite word fold from the retained positive acquisition certificate.

The other branches return their original negative or near-boundary evidence without changing the retained state. -/
def fold {tau : Coherent.CoherentNamed} {start :
    Approximation.Gaussian.Acquisition.State
  tau} {delta : Fraction.Rational} {positive : 0 < delta}
    (report : Requested.Report tau start delta positive) (word : ThreeStrand.Word) :
    OutcomePayload (GuaranteedFold.Prepared tau
        (Periods.periodBraidMatrices word))
      (Certificate.Negative tau report.retained delta) (Certificate.Near tau report.retained delta) :=
  match report.2 with
  | .positive high _ => .ready
      (GuaranteedFold.prepareWord (report.enclosure high) word)
  | .negative _ upper => .negative (report.negative upper)
  | .near bounds => .near (report.near bounds)

end Purelib.Curves.Legendre.Acquisition.Signed.Report

end
