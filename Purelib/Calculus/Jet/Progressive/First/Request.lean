module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Refinement
import Purelib.Approximation.Rational.Request.Common
public import Purelib.Calculus.Jet.Progressive.First.Provenance

open Purelib.Approximation.Gaussian.Process.Coherence.Basic (Coherent)
open Purelib.Data.Rat.Fraction (Rational)

section
@[expose] public section

/-!
# Synchronized first jets over progressive CCL inputs

The displayed-input evaluator in `JetData` computes two rational
coordinates.  This module lifts the same algebra to arbitrary coherent
progressive inputs.  A jet contains two coherent names, one for the value
channel and one for the slope channel, together with an indexed finite program
which proves that the channels were produced by the same differentiation
calculation.  Thus an arbitrary unrelated pair of names is not a jet.  A joint
request computes one positive rational budget below the requested value error,
the requested slope error, and both semantic-coherence moduli.

No derivative is represented as a function.  Every observation consists of
two finite process states and two finite raw CCL prefixes.
-/

namespace Purelib.Calculus.Jet.Progressive.First.Provenance
namespace JetData

section
open Purelib.Approximation
open Purelib.Data
open Purelib.Calculus.Jet.Progressive.First
/-- Compute one rational request below the target and both channel accuracy requests.

The formula applies commonRequest twice to the displayed target and the two semantic accuracy requests. Its positivity
and strict bounds require a positive target. -/
def requestTarget (jet : Provenance.JetData) (target :
  Rational) : Rational :=
  Coherent.commonRequest target
    (Coherent.commonRequest
      (jet.value.coherent.accuracyRequest target)
      (jet.slope.coherent.accuracyRequest target))

/-- A positive target gives a positive common request for both jet channels. -/
theorem requestTarget_pos (jet : Provenance.JetData)
  {target : Rational}
    (positive : 0 < target) : 0 < jet.requestTarget target := by
  apply Coherent.commonRequest_pos positive
  exact Coherent.commonRequest_pos
    (jet.value.coherent.accuracyRequest_pos positive)
    (jet.slope.coherent.accuracyRequest_pos positive)

/-- The common request is strictly below its positive displayed target. -/
theorem requestTarget_lt_target (jet :
  Provenance.JetData) {target : Rational}
    (positive : 0 < target) : jet.requestTarget target < target := by
  exact Coherent.commonRequest_lt_left
    positive
    (Coherent.commonRequest_pos
      (jet.value.coherent.accuracyRequest_pos positive)
      (jet.slope.coherent.accuracyRequest_pos positive))

/-- The common request is strictly below the value channel's accuracy request. -/
theorem requestTarget_lt_valueAllowance (jet :
  Provenance.JetData)
    {target : Rational} (positive : 0 < target) :
    jet.requestTarget target < jet.value.coherent.accuracyRequest target := by
  have innerPositive :=
    Coherent.commonRequest_pos
      (jet.value.coherent.accuracyRequest_pos positive)
      (jet.slope.coherent.accuracyRequest_pos positive)
  exact (Coherent.commonRequest_lt_right
    positive innerPositive).trans
      (Coherent.commonRequest_lt_left
        (jet.value.coherent.accuracyRequest_pos positive)
        (jet.slope.coherent.accuracyRequest_pos positive))

/-- The common request is strictly below the slope channel's accuracy request. -/
theorem requestTarget_lt_slopeAllowance (jet :
  Provenance.JetData)
    {target : Rational} (positive : 0 < target) :
    jet.requestTarget target < jet.slope.coherent.accuracyRequest target := by
  have innerPositive :=
    Coherent.commonRequest_pos
      (jet.value.coherent.accuracyRequest_pos positive)
      (jet.slope.coherent.accuracyRequest_pos positive)
  exact (Coherent.commonRequest_lt_right
    positive innerPositive).trans
      (Coherent.commonRequest_lt_right
        (jet.value.coherent.accuracyRequest_pos positive)
        (jet.slope.coherent.accuracyRequest_pos positive))

/-- Refine the retained value name at the positive common request.

The request uses both channels' accuracy moduli, while the returned Named record retains the value channel's refinement
state and process. -/
def valueRequest (jet : Provenance.JetData) (target :
  Rational)
    (positive : 0 < target) : Gaussian.Name.Basic.Named :=
  Gaussian.Name.Refinement.refined jet.value.name
    (jet.requestTarget target) (jet.requestTarget_pos positive)

/-- Refine the retained slope name at the positive common request.

The request uses both channels' accuracy moduli, while the returned Named record retains the slope channel's refinement
state and process. -/
def slopeRequest (jet : Provenance.JetData) (target :
  Rational)
    (positive : 0 < target) : Gaussian.Name.Basic.Named :=
  Gaussian.Name.Refinement.refined jet.slope.name
    (jet.requestTarget target) (jet.requestTarget_pos positive)

/-- The refined value name's enclosure radius squared is below the positive target. -/
theorem valueRequest_radius_lt (jet :
  Provenance.JetData) {target : Rational}
    (positive : 0 < target) :
    ((jet.valueRequest target positive).process.ball
      (jet.valueRequest target positive).state).radiusSq < target :=
  (Gaussian.Name.Refinement.refined_error jet.value.name
    (jet.requestTarget target) (jet.requestTarget_pos positive)).trans
      (jet.requestTarget_lt_target positive)

/-- The refined slope name's enclosure radius squared is below the positive target. -/
theorem slopeRequest_radius_lt (jet :
  Provenance.JetData) {target : Rational}
    (positive : 0 < target) :
    ((jet.slopeRequest target positive).process.ball
      (jet.slopeRequest target positive).state).radiusSq < target :=
  (Gaussian.Name.Refinement.refined_error jet.slope.name
    (jet.requestTarget target) (jet.requestTarget_pos positive)).trans
      (jet.requestTarget_lt_target positive)

end

open Purelib.Data
open Purelib.Calculus.Jet.Progressive.First
/-- The value channel's semantic allowance at its refined state is below the target.

The common request lies below the value accuracy request, so the original coherence certificate transports the allowance
at the actual returned state. -/
theorem valueRequest_allowance_lt (jet :
  Provenance.JetData) {target : Rational}
    (positive : 0 < target) :
    jet.value.coherent.allowance (jet.valueRequest target positive).state <
      target :=
  jet.value.coherent.refine_accurate jet.value.name.state target positive
    (jet.requestTarget target) (jet.requestTarget_pos positive)
      (jet.requestTarget_lt_valueAllowance positive)

/-- The slope channel's semantic allowance at its refined state is below the target.

The common request lies below the slope accuracy request, so the original coherence certificate transports the allowance
at the actual returned state. -/
theorem slopeRequest_allowance_lt (jet :
  Provenance.JetData) {target : Rational}
    (positive : 0 < target) :
    jet.slope.coherent.allowance (jet.slopeRequest target positive).state <
      target :=
  jet.slope.coherent.refine_accurate jet.slope.name.state target positive
    (jet.requestTarget target) (jet.requestTarget_pos positive)
      (jet.requestTarget_lt_slopeAllowance positive)
end JetData

end Purelib.Calculus.Jet.Progressive.First.Provenance

end
