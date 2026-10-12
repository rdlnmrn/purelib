module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Acquisition.Signed.Requested
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Name.Coherent

import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Basic
public import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Decision
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Init.Core
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Enclosure.Signed
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Acquisition.Signed

open Purelib.Approximation.Gaussian.Acquisition.Signed.Gap

open Purelib.Approximation.Gaussian.Name

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Quantitative signed completeness from an unsigned candidate gap

A persistent rational gap removes the near-boundary alternative without
supplying the sign. Both direct requested precision and a coefficient-bounded
canonical refinement schedule construct signed evidence. The canonical
positive result supplies a budget for the original positivity `attempt`.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Requested

namespace Gap
end Gap

/-- Keep the requested-target report, its cached state, and the sharpened two-way result. No sign is supplied by the
caller. -/
def requested (tau : Coherent.CoherentNamed)
  (start : Approximation.Gaussian.Acquisition.State tau) (delta : Fraction.Rational) (positive : 0 < delta)
    (gap : Approximation.Gaussian.Acquisition.Signed.Gap tau start delta) :
    Sigma fun report : Requested.Report tau start delta positive =>
      Decision.Outcome tau report.retained delta :=
  let report := Requested.acquire tau start delta positive
  ⟨report, Decision.certify report.retained delta positive report.1.accurate
    (Approximation.Gaussian.Acquisition.Signed.Gap.after gap report.possible_at_start) report.2⟩
end Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Requested

end
