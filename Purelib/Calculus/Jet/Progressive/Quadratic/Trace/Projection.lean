module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Search
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Sequence (ApproximationData)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

section
@[expose] public section

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Trace
section Trace

section
open Purelib.Approximation
open Purelib.Data
/-- Build a progressive approximation from one sequence obeying the trace's common estimates.

The supplied samples share the trace's geometric radius schedule and center bound. Refinement uses firstQuarterBelow at
the retained error scale, with proofs of index extension and accuracy. -/
def projectionApproximation {increment : Nat →
  Canonical}
    (trace : Trace increment) (sample : Nat → Canonical)
    (later_close : ∀ {earlier later : Nat}, earlier ≤ later →
      Canonical.normSq (sample later - sample earlier) ≤
        Rational.Geometric.Basic.quarterRadius trace.errorScale earlier)
    (bounded : ∀ index, Canonical.normSq (sample index) ≤ trace.centerBound) :
    ApproximationData where
  sample := sample
  radiusSq := Rational.Geometric.Basic.quarterRadius trace.errorScale
  radiusSq_nonneg :=
    Rational.Geometric.Basic.quarterRadius_nonneg
      trace.errorScale_nonneg
  later_close := by
    intro earlier later order
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using later_close order
  refineIndex current target _positive :=
    Rational.Geometric.Search.firstQuarterBelow trace.errorScale
      current target
  refineIndex_ge := by
    intro current target _positive
    exact Rational.Geometric.Search.firstQuarterBelow_ge
      trace.errorScale current target
  refineIndex_accurate :=
    Rational.Geometric.Search.firstQuarterBelow_accurate
      trace.errorScale trace.errorScale_nonneg
  centerBound := trace.centerBound
  centerBound_nonneg := trace.centerBound_nonneg
  sample_bounded := by
    intro index
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using bounded index

/-- Project the increment samples with the trace's common geometric schedule and center bound. -/
def incrementApproximation {increment : Nat →
  Canonical}
    (trace : Trace increment) : ApproximationData :=
  trace.projectionApproximation increment trace.increment_later_close
    trace.increment_bounded

/-- Project the base samples with the trace's common geometric schedule and center bound. -/
def baseApproximation {increment : Nat →
  Canonical}
    (trace : Trace increment) : ApproximationData :=
  trace.projectionApproximation (fun index => (trace.certificate index).base)
    trace.base_later_close trace.base_bounded

/-- Project the output samples with the trace's common geometric schedule and center bound. -/
def outputApproximation {increment : Nat →
  Canonical}
    (trace : Trace increment) : ApproximationData :=
  trace.projectionApproximation (fun index => (trace.certificate index).output)
    trace.output_later_close trace.output_bounded

/-- Project the slope samples with the trace's common geometric schedule and center bound. -/
def slopeApproximation {increment : Nat →
  Canonical}
    (trace : Trace increment) : ApproximationData :=
  trace.projectionApproximation (fun index => (trace.certificate index).slope)
    trace.slope_later_close trace.slope_bounded

/-- Project the remainder samples with the trace's common geometric schedule and center bound. -/
def remainderApproximation {increment : Nat →
  Canonical}
    (trace : Trace increment) : ApproximationData :=
  trace.projectionApproximation
    (fun index => (trace.certificate index).remainder)
    trace.remainder_later_close trace.remainder_bounded

/-- Build the coherent name from the retained increment approximation. -/
def incrementChannel {increment : Nat →
  Canonical}
    (trace : Trace increment) : CoherentNamed :=
  CoherentNamed.ofApproximation
    trace.incrementApproximation

/-- Build the coherent name from the retained base approximation. -/
def baseChannel {increment : Nat →
  Canonical}
    (trace : Trace increment) : CoherentNamed :=
  CoherentNamed.ofApproximation
    trace.baseApproximation

/-- Build the coherent name from the retained output approximation. -/
def outputChannel {increment : Nat →
  Canonical}
    (trace : Trace increment) : CoherentNamed :=
  CoherentNamed.ofApproximation
    trace.outputApproximation

/-- Build the coherent name from the retained slope approximation. -/
def slopeChannel {increment : Nat →
  Canonical}
    (trace : Trace increment) : CoherentNamed :=
  CoherentNamed.ofApproximation
    trace.slopeApproximation

/-- Build the coherent name from the retained remainder approximation. -/
def remainderChannel {increment : Nat →
  Canonical}
    (trace : Trace increment) : CoherentNamed :=
  CoherentNamed.ofApproximation
    trace.remainderApproximation

/-- List the five coherent channels in increment, base, output, slope and remainder order. -/
def channels {increment : Nat →
  Canonical}
    (trace : Trace increment) : List CoherentNamed :=
  [trace.incrementChannel, trace.baseChannel, trace.outputChannel,
    trace.slopeChannel, trace.remainderChannel]

/-- Select a geometric refinement index at or after the current index.

The search uses the trace's common error scale and the displayed rational target. A positive target gives the separately
proved strict accuracy guarantee. -/
def requestIndex {increment : Nat →
  Canonical} (trace : Trace increment)
    (current : Nat) (target : Rat.Fraction.Rational) : Nat :=
  Rational.Geometric.Search.firstQuarterBelow trace.errorScale
    current target

/-- The selected common index never precedes the requested current index. -/
theorem requestIndex_ge {increment : Nat →
  Canonical}
    (trace : Trace increment) (current : Nat) (target : Rat.Fraction.Rational) :
    current ≤ trace.requestIndex current target :=
  Rational.Geometric.Search.firstQuarterBelow_ge
    trace.errorScale current target

/-- At a positive target, the selected common geometric allowance is strictly smaller. -/
theorem requestIndex_accurate {increment : Nat →
  Canonical}
    (trace : Trace increment) (current : Nat) {target : Rat.Fraction.Rational}
    (positive : 0 < target) :
    Rational.Geometric.Basic.quarterRadius trace.errorScale
      (trace.requestIndex current target) < target :=
  Rational.Geometric.Search.firstQuarterBelow_accurate
    trace.errorScale trace.errorScale_nonneg current target positive

end

section
open Purelib.Data
/-- Use the displayed natural index as the increment channel's process state. -/
def incrementState {increment : Nat →
  Canonical} (trace : Trace increment)
    (index : Nat) : trace.incrementChannel.name.process.State := by
  change Nat
  exact index

/-- Use the displayed natural index as the base channel's process state. -/
def baseState {increment : Nat →
  Canonical} (trace : Trace increment)
    (index : Nat) : trace.baseChannel.name.process.State := by
  change Nat
  exact index

/-- Use the displayed natural index as the output channel's process state. -/
def outputState {increment : Nat →
  Canonical} (trace : Trace increment)
    (index : Nat) : trace.outputChannel.name.process.State := by
  change Nat
  exact index

/-- Use the displayed natural index as the slope channel's process state. -/
def slopeState {increment : Nat →
  Canonical} (trace : Trace increment)
    (index : Nat) : trace.slopeChannel.name.process.State := by
  change Nat
  exact index

/-- Use the displayed natural index as the remainder channel's process state. -/
def remainderState {increment : Nat →
  Canonical} (trace : Trace increment)
    (index : Nat) : trace.remainderChannel.name.process.State := by
  change Nat
  exact index
end

end Trace

end Purelib.Calculus.Jet.Progressive.Quadratic.Trace

end
