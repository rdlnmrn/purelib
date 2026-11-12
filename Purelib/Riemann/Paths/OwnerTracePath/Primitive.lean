module

public import Purelib.Riemann.Paths.OwnerTracePath.Stationary
import Purelib.Approximation.AccuracyRequest
import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian
import Purelib.Approximation.Gaussian.Equivalence.Observation
import Purelib.Approximation.Gaussian.Provenance.Power
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Original primitive observations at retained owner-path vertices

A vertex cache contains the original coefficient Denotation and the actual
Observation.Request on that channel. The original winding root Owner remains
an index, not a substitute owner. Completed caches can enter unchanged. The
automatic constructor selects its primitive observation once, before any
stationary comparison. One common original expression supplies genuine
coefficient normalization; arbitrary local primitive constants are not
identified by a common coordinate or sheet label.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Algebra.Quadratic.Pair.Polynomial.Expression (Denotation)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner ownerName)

variable {polynomial : Coefficients} (expression : Expression polynomial)

/-- The original vertex-channel radius request pays one sixty-fourth of the local stationary-error target. -/
@[expose] def vertexRequest (accuracy : AccuracyRequest) : AccuracyRequest :=
  ⟨accuracy.tolerance / ((64 : Nat) : Rational), Fraction.Order.Field.div_pos_direct accuracy.positive
    (Fraction.Cast.Order.natCast_pos_direct (n := 64) (by decide +kernel))⟩

/-- The actual operational tail comparison pays one eighth of the same local stationary-error target. -/
@[expose] def tailRequest (accuracy : AccuracyRequest) : AccuracyRequest :=
  ⟨accuracy.tolerance / 8, Fraction.Order.Field.div_pos_direct accuracy.positive
    (of_decide_eq_true rfl : (0 : Rational) < 8)⟩

/-- The two original vertex radii and actual tail allowance pay exactly the local stationary-error target. -/
theorem comparison_payment (accuracy : AccuracyRequest) :
    16 * ((vertexRequest accuracy).tolerance + (vertexRequest accuracy).tolerance) +
      4 * (tailRequest accuracy).tolerance = accuracy.tolerance := by
  change 16 * (accuracy.tolerance / ((64 : Nat) : Rational) +
    accuracy.tolerance / ((64 : Nat) : Rational)) + 4 * (accuracy.tolerance / 8) = accuracy.tolerance
  have scalar : (16 : Rational) * (((64 : Nat) : Rational)⁻¹ + ((64 : Nat) : Rational)⁻¹) +
      4 * (8 : Rational)⁻¹ = 1 := by
    rewrite [Fraction.Cast.natCast_eq_fromInt 64]
    decide +kernel
  calc
    _ = accuracy.tolerance * (16 * (((64 : Nat) : Rational)⁻¹ + ((64 : Nat) : Rational)⁻¹) +
      4 * (8 : Rational)⁻¹) := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ = accuracy.tolerance := by rewrite [scalar, Fraction.Field.mul_one_direct]; rfl

/-- One actual original coefficient denotation and its already selected primitive observation at this exact Owner.

The cached denotation retains its domain, original coefficient pair and
generator equation. The actual original Request retains its channel,
chosen state, value, visible radius and request payment. Both whole parents
are stored directly, with their original nominal indices unchanged.
-/
@[expose] def Vertex (point : Canonical) (owner : Owner (polynomial.eval point)) (accuracy : AccuracyRequest) :=
  Σ original : Denotation expression point (owner.certificate owner.parameterNonzero).value,
    Observation.Request original.channel (vertexRequest accuracy).tolerance

namespace Vertex

variable {expression} {point : Canonical} {owner : Owner (polynomial.eval point)} {accuracy : AccuracyRequest}

/-- Retain the exact supplied original denotation and old request without reinterpreting or resampling either. -/
@[expose] def ofCompleted
    (original : Denotation expression point (owner.certificate owner.parameterNonzero).value)
    (requested : Observation.Request original.channel (vertexRequest accuracy).tolerance) :
    Vertex expression point owner accuracy := ⟨original, requested⟩

/-- Construct one original coefficient interpretation and one actual primitive request at this retained vertex Owner.

The original Owner supplies its own operational square certificate. The
admitted denominator guard belongs to this same coefficient expression and
physical coordinate. No trace, root owner or polynomial continuation is run.
-/
def build (expression : Expression polynomial) (point : Canonical) (owner : Owner (polynomial.eval point))
    (accuracy : AccuracyRequest) (defined : expression.Defined point) : Vertex expression point owner accuracy :=
  let certificate := owner.certificate owner.parameterNonzero
  let original := Expression.retain expression point certificate.value defined
    (PowerIdentity.ofSquare certificate.square)
  let requested := Observation.Request.build original.channel (vertexRequest accuracy).tolerance
    (vertexRequest accuracy).positive
  ofCompleted original requested

variable (vertex : Vertex expression point owner accuracy)

/-- Read the entire original coefficient denotation without recomputing its pair or generator interpretation. -/
@[expose] def original : Denotation expression point (owner.certificate owner.parameterNonzero).value := vertex.1

/-- Read the whole actual old primitive request, including its exact selected observation state and radius. -/
@[expose] def requested : Observation.Request vertex.original.channel (vertexRequest accuracy).tolerance := vertex.2

/-- Read the original selected possible observation unchanged. -/
@[expose] def observation : Observation.Reading vertex.original.channel := vertex.requested.reading

/-- The unchanged actual old primitive value at this original owner-path vertex. -/
@[expose] def value : Canonical := vertex.observation.value

/-- A finite coefficient equality normalizes the same old denotation and request without selecting new observations.

The original reinterpretation preserves its complete cached coefficient
pair and channel. Its old Request is reused literally. Both original and
target denominator-domain conditions remain available in the denotations.
-/
@[expose] def reinterpret (target : Expression polynomial) (equal : target.Equal vertex.original.source)
    (defined : target.Defined point) : Vertex target point owner accuracy :=
  let original := vertex.original.reinterpret target equal defined
  ofCompleted original vertex.requested

/-- Coefficient normalization preserves the complete actual old request and all its chosen states and values. -/
theorem reinterpret_requested (target : Expression polynomial) (equal : target.Equal vertex.original.source)
    (defined : target.Defined point) :
    (vertex.reinterpret target equal defined).requested = vertex.requested := rfl

/-- Compare the unchanged primitive observations at exactly identified points and signed original roots.

Each original Vertex retains its own coefficient denotation, accuracy
request, selected state, value and radius. Only the endpoint index is
transported. The original denotation comparison consumes the supplied
operational root agreement and charges both old radii and its independent
tail request without reinterpreting or selecting either observation.
-/
def compare {firstPoint lastPoint : Canonical}
    {left : Owner (polynomial.eval firstPoint)} {right : Owner (polynomial.eval lastPoint)}
    {firstAccuracy lastAccuracy : AccuracyRequest}
    (first : Vertex expression firstPoint left firstAccuracy)
    (last : Vertex expression lastPoint right lastAccuracy)
    (same : firstPoint = lastPoint) (roots : NamedEquivalent (ownerName left) (ownerName right))
    (request : AccuracyRequest) : Observation.Comparison first.observation last.observation request.tolerance := by
  cases same
  exact first.original.compare last.original roots first.observation last.observation request

end Vertex

namespace Stationary

variable {expression} {start finish : Canonical}
variable {left : Owner (polynomial.eval start)} {right : Owner (polynomial.eval finish)}
variable {accuracy : AccuracyRequest}

/-- Compare unchanged vertex requests across the SAME stored link at coincident original base endpoints.

Base equality only identifies the original polynomial evaluation. The
signed root relation comes from that exact link's actual realize operation;
no OwnerJoin or trace factory is reconstructed.
-/
def compare (link : OwnerLink polynomial start finish left right) (same : start = finish)
    (first : Vertex expression start left accuracy) (last : Vertex expression finish right accuracy) :
    Observation.Comparison first.observation last.observation (tailRequest accuracy).tolerance := by
  cases same
  exact first.compare last rfl link.equivalentStationary (tailRequest accuracy)

/-- Both unchanged original requests and the derived stationary comparison pay the actual signed primitive jump. -/
theorem jump_lt (first : Vertex expression start left accuracy) (last : Vertex expression finish right accuracy)
    (comparison : Observation.Comparison first.observation last.observation (tailRequest accuracy).tolerance) :
    Norm.Basic.normSq (last.value - first.value) < accuracy.tolerance := by
  have scalar := (Observation.Comparison.requested_error_lt first.requested last.requested comparison).trans_eq
    (comparison_payment accuracy)
  rewrite [Norm.Bounds.normSq_sub_symm]
  exact scalar

end Stationary

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive

end
