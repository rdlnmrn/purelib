module
public import Purelib.Approximation.Rational.Budget.Square
public import Purelib.Approximation.Observation.Schedule
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Observation.Basic
import Purelib.Approximation.Observation.Process
import Purelib.Data.CCL.Name.Boxed.Basic
public import Purelib.Data.CCL.Name.Boxed.Process
import Purelib.Data.CCL.Name.Boxed.Refinement
public import Purelib.Geometry.Affine.Gaussian.Distance
import Init.Prelude
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.CCL.Encoding.Parser.Semantics.Prefix
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Rational.Budget.Square

open Purelib.Data.CCL.Name

open Purelib.Data.CCL.Name.Boxed

open Purelib.Geometry

section
@[expose] public section

/-!
# Finite measure observations of boxed CCL names

This module turns each boxed CCL certificate into a generic finite
observation and supplies arbitrarily small rational-area observations of a
progressive site.  The possible predicate is deliberately allowed to refine:
no intersection of all cylinders and no completed point is asserted.
-/

namespace Purelib.Approximation.CCL.BoxedName
namespace Certificate

/-- A boxed CCL certificate is a finitely satisfiable pairwise-small observation. -/
def toObservation (certificate : Boxed.Basic.Certificate) :
    Approximation.Observation Canonical Affine.Gaussian.affineDistance where
  Possible := certificate.Possible
  witness := certificate.witness
  witness_possible :=
    ⟨certificate.witness_nonzero, certificate.witness_represented⟩
  spread := certificate.box.diagonalSq
  spread_nonnegative := certificate.box.diagonalSq_nonneg
  pairwise := by
    intro left right leftPossible rightPossible
    exact certificate.box.normSq_sub_le_diagonalSq
      (certificate.possible_inside leftPossible)
      (certificate.possible_inside rightPossible)

/-- Refinement of boxed CCL certificates induces refinement of their admitted finite observations. -/
theorem observation_refines {inner outer :
  Boxed.Basic.Certificate}
    (refines : Refinement.Refines inner outer) :
    Observation.Refines (toObservation inner)
      (toObservation outer) :=
  ⟨fun possible => refines.possible_persists possible⟩

end Certificate

namespace ProgressiveName

/-- Generic finite-request observation protocol underlying one boxed CCL name. Its accuracy request is expressed
directly as a squared-distance budget, and every returned state remains finite. -/
def toObservation (name : Process.ProgressiveName) :
    Approximation.ProgressiveObservation Canonical
      Affine.Gaussian.affineDistance where
  State := name.State
  observation state := Approximation.CCL.BoxedName.Certificate.toObservation (name.certificate state)
  initial := name.initial
  request state epsilon positive :=
    name.request state (radius epsilon) (radius_pos positive)
  request_refines state epsilon positive :=
    Approximation.CCL.BoxedName.Certificate.observation_refines
      (name.request_refines state (radius epsilon)
        (radius_pos positive))
  accurate state epsilon positive :=
    (name.accurate state (radius epsilon)
      (radius_pos positive)).trans_lt (radius_sq_lt positive)
  refinesInitial state :=
    Approximation.CCL.BoxedName.Certificate.observation_refines (name.refinesInitial state)

/-- Execute a displayed finite batch of squared-distance requests on a boxed name. The result is still one finite CCL
state. -/
def runAccuracyRequests (name : Process.ProgressiveName)
  (state : name.State)
    (requests : List Approximation.AccuracyRequest) : name.State :=
  (toObservation name).runRequests state requests

/-- Candidates at the end of a displayed finite CCL request batch meet every tolerance that occurred in that batch. -/
theorem runAccuracyRequests_pairwise_lt_of_mem
    (name : Process.ProgressiveName) (state : name.State)
    (requests : List Approximation.AccuracyRequest)
    (request : Approximation.AccuracyRequest)
    (member : request ∈ requests) {left right : Canonical}
    (leftPossible :
      (name.certificate ((runAccuracyRequests name state
        requests))).Possible left)
    (rightPossible :
      (name.certificate ((runAccuracyRequests name state
        requests))).Possible right) :
    Affine.Gaussian.affineDistance left right < request.tolerance := by
  exact (toObservation name).runRequests_pairwise_lt_of_mem
    state requests request member leftPossible rightPossible

/-- The explicit witness after a finite CCL request batch remains possible at the distinguished initial certificate. -/
theorem runAccuracyRequests_witness_possible_initial
    (name : Process.ProgressiveName) (state : name.State)
    (requests : List Approximation.AccuracyRequest) :
    (name.certificate name.initial).Possible
      (name.certificate
        ((runAccuracyRequests name state requests))).witness := by
  exact (toObservation name).runRequests_witness_possible_initial state
    requests
end ProgressiveName
end Purelib.Approximation.CCL.BoxedName

end
