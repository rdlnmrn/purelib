module

public import Purelib.Riemann.Paths.OwnerTracePath.Primitive
public import Purelib.Riemann.Paths.OwnerTracePath.Join
import Purelib.Riemann.Paths.OwnerTraceReadings.Observation
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian.Comparison
import Purelib.Approximation.Gaussian.Equivalence.Observation
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Unchanged primitive vertices at exactly corresponding endpoints

Actual root-name comparisons and exact point identities compare the
original observation requests. No vertex is observed again. Two such
retained comparisons pay the finite discrepancy of oriented increments.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive.Vertex

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner OwnerJoin ownerName)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter)

variable {polynomial : Coefficients} {expression : Expression polynomial} {accuracy : AccuracyRequest}

/-- Reindex the complete original vertex only through exact point and whole-Owner identities. -/
def castOwner {point nextPoint : Canonical} {owner : Owner (polynomial.eval point)}
    {nextOwner : Owner (polynomial.eval nextPoint)} (equal : point = nextPoint) (same : HEq owner nextOwner)
    (original : Vertex expression point owner accuracy) : Vertex expression nextPoint nextOwner accuracy := by
  cases equal
  cases eq_of_heq same
  exact original

/-- Exact point/Owner transport retains the complete original vertex cache heterogeneously. -/
private theorem packaged_castOwner_heq {point nextPoint : Canonical} {owner : Owner (polynomial.eval point)}
    {nextOwner : Owner (polynomial.eval nextPoint)} (equal : point = nextPoint) (same : HEq owner nextOwner)
    (original : Vertex expression point owner accuracy) : HEq (castOwner equal same original) original := by
  cases equal
  cases eq_of_heq same
  rfl

/-- Exact point/Owner transport retains the complete original vertex cache heterogeneously. -/
theorem castOwner_heq {point nextPoint : Canonical} {owner : Owner (polynomial.eval point)}
    {nextOwner : Owner (polynomial.eval nextPoint)} (equal : point = nextPoint) (same : HEq owner nextOwner)
    (original : Vertex expression point owner accuracy) : HEq (castOwner equal same original) original :=
  packaged_castOwner_heq equal same original

/-- Exact point/Owner transport retains the same cached original observation value. -/
private theorem packaged_castOwner_value {point nextPoint : Canonical} {owner : Owner (polynomial.eval point)}
    {nextOwner : Owner (polynomial.eval nextPoint)} (equal : point = nextPoint) (same : HEq owner nextOwner)
    (original : Vertex expression point owner accuracy) : (castOwner equal same original).value = original.value := by
  cases equal
  cases eq_of_heq same
  rfl

/-- Exact point/Owner transport retains the same cached original observation value. -/
theorem castOwner_value {point nextPoint : Canonical} {owner : Owner (polynomial.eval point)}
    {nextOwner : Owner (polynomial.eval nextPoint)} (equal : point = nextPoint) (same : HEq owner nextOwner)
    (original : Vertex expression point owner accuracy) : (castOwner equal same original).value = original.value :=
  packaged_castOwner_value equal same original

/-- Compare two actual original vertex requests at the same point and their certified original root generators.

Point equality only reindexes the common expression's coordinate. The
supplied operational relation retains both actual root names. Their
existing denotations and observation requests are consumed unchanged.
-/
def compareAt {point nextPoint : Canonical} {owner : Owner (polynomial.eval point)}
    {nextOwner : Owner (polynomial.eval nextPoint)}
    (original : Vertex expression point owner accuracy) (next : Vertex expression nextPoint nextOwner accuracy)
    (equal : point = nextPoint) (roots : NamedEquivalent (ownerName owner) (ownerName nextOwner)) :
    Observation.Comparison original.observation next.observation (tailRequest accuracy).tolerance := by
  cases equal
  exact original.original.compare next.original roots original.observation next.observation (tailRequest accuracy)

/-- Compare two actual primitive requests of independent accuracies through their retained equal-point OwnerJoin.

The exact coordinate identity changes only nominal point indices. The
supplied actual join supplies signed root evidence. Both whole original
Vertices, denotations, selected observation states and requests are
consumed unchanged; no reading is selected again or retagged.
-/
def compareRequestedAt {point nextPoint : Canonical}
    {owner : Owner (polynomial.eval point)} {nextOwner : Owner (polynomial.eval nextPoint)}
    {firstAccuracy lastAccuracy : AccuracyRequest}
    (first : Vertex expression point owner firstAccuracy) (last : Vertex expression nextPoint nextOwner lastAccuracy)
    (equal : point = nextPoint)
    (join : OwnerJoin (castOwnerParameter (congrArg polynomial.eval equal) owner) nextOwner)
    (request : AccuracyRequest) : Observation.Comparison first.observation last.observation request.tolerance := by
  cases equal
  exact join.compareRequestedDenotations first.original last.original first.requested last.requested request

/-- Each independent original request pays its own actual radius in the SAME mixed-accuracy comparison. -/
theorem requested_error_lt_at {point nextPoint : Canonical}
    {owner : Owner (polynomial.eval point)} {nextOwner : Owner (polynomial.eval nextPoint)}
    {firstAccuracy lastAccuracy : AccuracyRequest}
    (first : Vertex expression point owner firstAccuracy) (last : Vertex expression nextPoint nextOwner lastAccuracy)
    (request : AccuracyRequest)
    (compared : Observation.Comparison first.observation last.observation request.tolerance) :
    Norm.Basic.normSq (first.value - last.value) <
      16 * ((vertexRequest firstAccuracy).tolerance + (vertexRequest lastAccuracy).tolerance) +
        4 * request.tolerance :=
  Observation.Comparison.requested_error_lt first.requested last.requested compared

variable {firstPoint lastPoint nextFirstPoint nextLastPoint : Canonical}
variable {firstOwner : Owner (polynomial.eval firstPoint)} {lastOwner : Owner (polynomial.eval lastPoint)}
variable {nextFirstOwner : Owner (polynomial.eval nextFirstPoint)}
variable {nextLastOwner : Owner (polynomial.eval nextLastPoint)}
variable (first : Vertex expression firstPoint firstOwner accuracy)
variable (last : Vertex expression lastPoint lastOwner accuracy)
variable (nextFirst : Vertex expression nextFirstPoint nextFirstOwner accuracy)
variable (nextLast : Vertex expression nextLastPoint nextLastOwner accuracy)

/-- The two actual original endpoint-reading comparisons for one oriented increment. -/
@[expose] def EndpointComparisons :=
  Observation.Comparison first.observation nextFirst.observation (tailRequest accuracy).tolerance ×
    Observation.Comparison last.observation nextLast.observation (tailRequest accuracy).tolerance

/-- Construct both endpoint comparisons once from their exact point and actual root-generator relations. -/
def compareEndpointsAt (firstEq : firstPoint = nextFirstPoint) (lastEq : lastPoint = nextLastPoint)
    (firstRoots : NamedEquivalent (ownerName firstOwner) (ownerName nextFirstOwner))
    (lastRoots : NamedEquivalent (ownerName lastOwner) (ownerName nextLastOwner)) :
    EndpointComparisons first last nextFirst nextLast :=
  let starting := compareAt first nextFirst firstEq firstRoots
  let finishing := compareAt last nextLast lastEq lastRoots
  ⟨starting, finishing⟩

namespace EndpointComparisons

variable {first last nextFirst nextLast}

/-- The two retained endpoint comparisons pay the actual change of oriented primitive increments. -/
theorem increment_le (compared : EndpointComparisons first last nextFirst nextLast) :
    Norm.Basic.normSq ((nextLast.value - nextFirst.value) - (last.value - first.value)) ≤
      4 * accuracy.tolerance := by
  have start := (Stationary.jump_lt first nextFirst compared.1).le
  have finish := (Stationary.jump_lt last nextLast compared.2).le
  have difference : (nextLast.value - nextFirst.value) - (last.value - first.value) =
      (nextLast.value - last.value) - (nextFirst.value - first.value) := by ring1
  rewrite [difference]
  exact (Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct finish start)
      (of_decide_eq_true rfl : (0 : Rational) ≤ 2)).trans_eq (by ring1))

end EndpointComparisons

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive.Vertex

end
