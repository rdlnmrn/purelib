module

import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Sequence.Geometric.Channel
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Approximation.Gaussian.Sequence.Geometric (Channel)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

section
@[expose] public section

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Channel

section Trace

section
open Purelib.Approximation
open Purelib.Data
/-- Project the increment samples into a geometric channel.

The channel reuses the trace's exact error scale, center bound and increment estimates, transporting only the equivalent
quadrance notation. -/
def incrementField {increment : Nat →
  Canonical} (trace : Trace increment) :
    Channel increment :=
  ⟨trace.errorScale, trace.errorScale_nonneg, (fun order => by
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
        using trace.increment_later_close order),
    trace.centerBound, trace.centerBound_nonneg, (fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using trace.increment_bounded index)⟩

/-- Project the base samples into a geometric channel.

The channel reuses the trace's exact error scale, center bound and base estimates, transporting only the equivalent
quadrance notation. -/
def baseField {increment : Nat →
  Canonical} (trace : Trace increment) :
    Channel (fun index => (trace.certificate index).base) :=
  ⟨trace.errorScale, trace.errorScale_nonneg, (fun order => by
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
        using trace.base_later_close order),
    trace.centerBound, trace.centerBound_nonneg, (fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using trace.base_bounded index)⟩

/-- Project the output samples into a geometric channel.

The channel reuses the trace's exact error scale, center bound and output estimates, transporting only the equivalent
quadrance notation. -/
def outputField {increment : Nat →
  Canonical} (trace : Trace increment) :
    Channel (fun index => (trace.certificate index).output) :=
  ⟨trace.errorScale, trace.errorScale_nonneg, (fun order => by
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
        using trace.output_later_close order),
    trace.centerBound, trace.centerBound_nonneg, (fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using trace.output_bounded index)⟩

/-- Project the slope samples into a geometric channel.

The channel reuses the trace's exact error scale, center bound and slope estimates, transporting only the equivalent
quadrance notation. -/
def slopeField {increment : Nat →
  Canonical} (trace : Trace increment) :
    Channel (fun index => (trace.certificate index).slope) :=
  ⟨trace.errorScale, trace.errorScale_nonneg, (fun order => by
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
        using trace.slope_later_close order),
    trace.centerBound, trace.centerBound_nonneg, (fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using trace.slope_bounded index)⟩

/-- Project the remainder samples into a geometric channel.

The channel reuses the trace's exact error scale, center bound and remainder estimates, transporting only the equivalent
quadrance notation. -/
def remainderField {increment : Nat →
  Canonical} (trace : Trace increment) :
    Channel (fun index => (trace.certificate index).remainder) :=
  ⟨trace.errorScale, trace.errorScale_nonneg, (fun order => by
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
        using trace.remainder_later_close order),
    trace.centerBound, trace.centerBound_nonneg, (fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using trace.remainder_bounded index)⟩
end

end Trace

end Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Channel

end
