module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Bound.Operational
public import Purelib.Approximation.Bound.Process
import Purelib.Approximation.RationalGap.Basic
import Purelib.Approximation.RationalGap.SqrtThree
import Purelib.Data.Rat.Interval.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Approximation.Bound.Process.WorkedExamples

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation

open Purelib
open Purelib.Examples
open Purelib.Data.Rat

/-- The exact bound process at the rational number one. -/
def exactOneProcess : Approximation.BoundProcess :=
  Approximation.BoundProcess.exact 1

/-- A positive accuracy request with tolerance one half. -/
def halfRequest : Approximation.AccuracyRequest := ⟨1
  / 2, by decide⟩

/-- A positive accuracy request with tolerance one eighth. -/
def eighthRequest : Approximation.AccuracyRequest :=
  ⟨1 / 8, by decide⟩

/-- The ordered half- and eighth-tolerance request list. -/
def twoAccuracyRequests : List
  Approximation.AccuracyRequest :=
  [halfRequest, eighthRequest]

/-- Running the retained request list attains the half-tolerance bound. -/
example :
    (exactOneProcess.bound
      (exactOneProcess.runRequests ()
        twoAccuracyRequests)).width < 1 / 2 := by
  apply exactOneProcess.runRequests_width_lt_of_mem ()
    twoAccuracyRequests
    halfRequest
  exact List.mem_cons_self

/-- Running the same retained request list attains the eighth-tolerance bound. -/
example :
    (exactOneProcess.bound
      (exactOneProcess.runRequests ()
        twoAccuracyRequests)).width < 1 / 8 := by
  apply exactOneProcess.runRequests_width_lt_of_mem ()
    twoAccuracyRequests
    eighthRequest
  exact List.mem_cons_of_mem halfRequest List.mem_cons_self

/-- The exact-one process is operationally equivalent to itself. -/
example : Approximation.OperationallyEquivalent exactOneProcess
  exactOneProcess :=
  Approximation.operationallyEquivalent_refl exactOneProcess

/-- Transitivity preserves self-equivalence for the coherent exact-one process. -/
example : Approximation.OperationallyEquivalent exactOneProcess
  exactOneProcess := by
  apply Approximation.operationallyEquivalent_trans
    (Approximation.operationallyEquivalent_refl exactOneProcess)
    (Approximation.operationallyEquivalent_refl exactOneProcess)
  exact Approximation.BoundProcess.exact_coherent 1

/-- Finite gap inspection both excludes each candidate and meets each requested tolerance.

Retains the actual input state, candidate/request lists and their membership witnesses in the resulting inspection
bound. -/
example (gap : Approximation.RationalGapProcess) (state : gap.process.State)
    (candidates : List Rational) (requests : List Approximation.AccuracyRequest)
    (candidate : Rational) (candidateMember : candidate ∈ candidates)
    (request : Approximation.AccuracyRequest) (requestMember : request ∈ requests) :
    (gap.process.bound (gap.inspect state candidates requests)).Excludes candidate ∧
      (gap.process.bound (gap.inspect state candidates requests)).width <
        request.tolerance :=
  ⟨gap.inspect_excludes_of_mem state candidates requests candidate
      candidateMember,
    gap.inspect_width_lt_of_mem state candidates requests request
      requestMember⟩

/-- The square-root-of-three process meets every positive rational tolerance. -/
example (epsilon : Rational) (positive : 0 < epsilon) :
    (SqrtThree.process.bound
      (SqrtThree.process.request SqrtThree.process.initial epsilon positive)).width <
        epsilon :=
  SqrtThree.process.accurate SqrtThree.process.initial epsilon positive

/-- No square-root-of-three state bound is an exact rational singleton interval. -/
example (state : SqrtThree.State) (candidate : Rational) :
    SqrtThree.process.bound state ≠ Interval.exact candidate :=
  SqrtThree.state_bound_ne_exact state candidate

/-- Separating a rational candidate yields a square-root-of-three bound excluding it. -/
example (candidate : Rational) :
    (SqrtThree.process.bound
      (SqrtThree.gapProcess.separate SqrtThree.process.initial candidate)).Excludes
        candidate :=
  SqrtThree.gapProcess.separate_excludes SqrtThree.process.initial candidate

end Purelib.Examples.Approximation.Bound.Process.WorkedExamples

end
