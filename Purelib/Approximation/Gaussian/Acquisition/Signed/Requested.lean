module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Acquisition.Positive.Enclosure
public import Purelib.Approximation.Gaussian.Acquisition.Signed.Certificate
import Purelib.Approximation.Gaussian.Acquisition.State
public import Purelib.Approximation.Gaussian.Enclosure.Signed
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
import Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic
import Purelib.Data.Rat.Bounds.Quarter
import Init.Core
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

public section

/-!
# Bounded signed acquisition for Legendre input ratios

Requested-precision inspection always yields one of three mathematical
outcomes. The positive branch feeds the existing guaranteed word evaluators;
negative and near-boundary branches preserve their candidate evidence and
the exact state needed for subsequent work. A negative branch is not a
claim that all fractional transformations are undefined.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.Signed.Requested

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Acquisition.Positive
open Purelib.Approximation.Gaussian.Acquisition.Signed
open Purelib.Approximation.Gaussian.Enclosure
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Coherent.Refinement
open Purelib.Approximation.Gaussian.Process.Imaginary
open Purelib.Data.Rat

/-- One cached requested-target inspection, with a whole-ball classification. -/
@[expose] public def Report (tau : Coherent.CoherentNamed) (start : State tau) (delta :
  Fraction.Rational) (positive : 0 < delta) :=
  Sigma fun inspection : Name.Coherent.Refinement.Inspection tau start.retained
      (delta ^ 2 / 16) (Purelib.Data.Rat.Bounds.Quarter.target_positive positive) =>
    Signed.Decision inspection.ball delta

/-- Refine the exact retained source to the requested squared-radius target and classify the cached ball at the
displayed positive margin. -/
@[expose] public def acquire (tau : Coherent.CoherentNamed) (start : State tau) (delta :
  Fraction.Rational) (positive : 0 < delta) :
    Approximation.Gaussian.Acquisition.Signed.Requested.Report tau start delta positive :=
  let inspection := Inspection.request start.retained
    (delta ^ 2 / 16) (Purelib.Data.Rat.Bounds.Quarter.target_positive positive)
  ⟨inspection, Signed.decide inspection.ball delta positive inspection.accurate⟩

namespace Report

/-- Read the acquisition state and cached ball retained by this exact requested inspection. -/
@[expose] public def retained {tau : Coherent.CoherentNamed} {start : State tau} {delta :
  Fraction.Rational} {positive : 0 < delta}
    (report : Approximation.Gaussian.Acquisition.Signed.Requested.Report tau start delta positive) :
      State tau :=
  { retained := report.1.retained
    ball := report.1.ball
    ball_eq := report.1.ball_eq }

/-- Every candidate at the retained requested-inspection state was possible at the original start. -/
theorem possible_at_start {tau : Coherent.CoherentNamed} {start : State tau}
    {delta : Fraction.Rational} {positive : 0 < delta} (report :
      Approximation.Gaussian.Acquisition.Signed.Requested.Report tau start delta positive)
    {value : Data.Gaussian.Basic.Canonical} (possible : tau.name.process.Possible report.retained.retained.source value)
      :
    tau.name.process.Possible start.retained.source value := report.1.possible_at_start possible

/-- Requested inspection preserves the canonical schedule index. -/
theorem nextIndex_eq {tau : Coherent.CoherentNamed} {start : State tau}
    {delta : Fraction.Rational} {positive : 0 < delta} (report :
      Approximation.Gaussian.Acquisition.Signed.Requested.Report tau start delta positive) :
    report.retained.retained.nextIndex = start.retained.nextIndex := report.1.index_eq

/-- The new positive test implies the original test and constructs precisely the existing reusable enclosure, at the
retained source. -/
@[expose] public def enclosure {tau : Coherent.CoherentNamed} {start : State tau} {delta :
  Fraction.Rational} {positive : 0 < delta}
    (report : Approximation.Gaussian.Acquisition.Signed.Requested.Report tau start delta positive) (high : delta / 2 <
      report.1.ball.center.im) :
    Positive.Basic.PositiveEnclosure tau :=
  Enclosure.enclosure report.retained
    (Signed.positive_test positive report.1.accurate high)

/-- The positive enclosure uses exactly the source retained by the requested inspection. -/
@[simp] theorem enclosure_source {tau : Coherent.CoherentNamed} {start : State tau}
    {delta : Fraction.Rational} {positive : 0 < delta} (report :
      Approximation.Gaussian.Acquisition.Signed.Requested.Report tau start delta positive)
    (high : delta / 2 < report.1.ball.center.im) :
    (report.enclosure high).state = report.retained.retained.source := rfl

/-- Turn the cached ball's negative imaginary bound into a certificate for all candidates at the same retained source.
-/
@[expose] public def negative {tau : Coherent.CoherentNamed} {start : State tau} {delta :
  Fraction.Rational} {positive : 0 < delta}
    (report : Approximation.Gaussian.Acquisition.Signed.Requested.Report tau start delta positive)
    (upper : ∀ {value : Data.Gaussian.Basic.Canonical}, report.1.ball.Contains value → value.im ≤ -(delta / 4)) :
    Certificate.Negative tau report.retained delta where
  upper := by
    intro value possible
    apply upper
    rw [report.1.ball_eq]
    exact tau.name.process.possible_inside possible

/-- Turn the cached ball's two-sided near-boundary bounds into a certificate for candidates at the same retained source.
-/
@[expose] public def near {tau : Coherent.CoherentNamed} {start : State tau} {delta :
  Fraction.Rational} {positive : 0 < delta}
    (report : Approximation.Gaussian.Acquisition.Signed.Requested.Report tau start delta positive)
    (bounds : ∀ {value : Data.Gaussian.Basic.Canonical}, report.1.ball.Contains value →
      -delta < value.im ∧ value.im < delta) : Certificate.Near tau report.retained delta where
  bounds := by
    intro value possible
    apply bounds
    rw [report.1.ball_eq]
    exact tau.name.process.possible_inside possible

end Report
end Purelib.Approximation.Gaussian.Acquisition.Signed.Requested

end
