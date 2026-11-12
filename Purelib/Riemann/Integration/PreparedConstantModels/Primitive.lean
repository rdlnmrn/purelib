module

public import Purelib.Riemann.Integration.PreparedConstantModels.Query
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Sewing
public import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
public import Purelib.Data.List.DependentProduct
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.List.Membership
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Tactic.Ring
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Tactic.QuotientFreeOmega

/-! # Root-attached primitive Spines on the original prepared-edge fractions

The two actual endpoint Owners remain distinct from the original root
queries. Their operational comparisons attach a supplied real sewn Spine
to those exact query generators. An original interval walk appends the
actual child Spines and constructs every new stationary handoff internally.
-/

public section

namespace Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Algebra.FiniteSum
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Polynomial.Geometry.Grid.AxisWalks (IncreasingWalk)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive (Vertex)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive.Spine (Sewing)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner ownerName)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable (edge : PreparedEdge curve differential) (expression : Expression curve.polynomial)
variable (accuracy : AccuracyRequest)

/-- Actual endpoint Owners and observations on one original fractional edge, with its paid sewing and signed roots. -/
@[expose] def RootedSpine (lower upper : Rational)
    (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1) (sample : Canonical) :=
  Σ left : Owner (curve.polynomial.eval (edge.point lower)),
  Σ right : Owner (curve.polynomial.eval (edge.point upper)),
  Σ first : Vertex expression (edge.point lower) left accuracy,
  Σ last : Vertex expression (edge.point upper) right accuracy,
    Sewing first last sample ×
      (NamedEquivalent (edge.rootName lower lowerInside) (ownerName left) ×
        NamedEquivalent (edge.rootName upper upperInside) (ownerName right))

namespace RootedSpine

variable {edge expression accuracy}
variable {lower upper : Rational} {lowerInside : 0 ≤ lower ∧ lower ≤ 1} {upperInside : 0 ≤ upper ∧ upper ≤ 1}
variable {sample : Canonical}
variable (actual : RootedSpine edge expression accuracy lower upper lowerInside upperInside sample)

/-- Read the actual original source Owner of this rooted primitive Spine. -/
@[expose] def left : Owner (curve.polynomial.eval (edge.point lower)) := actual.1

/-- Read the distinct actual original target Owner. -/
@[expose] def right : Owner (curve.polynomial.eval (edge.point upper)) := actual.2.1

/-- Read the complete original source Vertex with its unchanged request. -/
@[expose] def first : Vertex expression (edge.point lower) actual.left accuracy := actual.2.2.1

/-- Read the complete original target Vertex with its separate unchanged request. -/
@[expose] def last : Vertex expression (edge.point upper) actual.right accuracy := actual.2.2.2.1

/-- Read the actual path/Spine and every internally paid new handoff. -/
@[expose] def sewn : Sewing (polynomial := curve.polynomial) (expression := expression) (accuracy := accuracy)
    actual.first actual.last sample := actual.2.2.2.2.1

/-- Read the exact number of stored new handoffs without exposing dependent endpoint observation types. -/
@[expose] def junctionCount : Nat := actual.2.2.2.2.1.2.val.length

/-- The scalar handoff getter reads the original stored Sewing junctions exactly. -/
theorem junctionCount_eq : actual.junctionCount = actual.sewn.junctions.length := rfl

/-- Read its original signed lower-query attachment without a new root or sheet choice. -/
@[expose] def firstRoot : NamedEquivalent (edge.rootName lower lowerInside) (ownerName actual.left) :=
  actual.2.2.2.2.2.1

/-- Read its original signed upper-query attachment. -/
@[expose] def lastRoot : NamedEquivalent (edge.rootName upper upperInside) (ownerName actual.right) :=
  actual.2.2.2.2.2.2

/-- Exact fraction-index transport preserves the whole original rooted Spine and its unchanged requests. -/
def castFractions {nextLower nextUpper : Rational}
    {nextLowerInside : 0 ≤ nextLower ∧ nextLower ≤ 1} {nextUpperInside : 0 ≤ nextUpper ∧ nextUpper ≤ 1}
    (firstEq : lower = nextLower) (lastEq : upper = nextUpper) :
    RootedSpine edge expression accuracy nextLower nextUpper nextLowerInside nextUpperInside sample := by
  cases firstEq
  cases lastEq
  exact actual

/-- Exact fraction-index transport retains the entire original rooted Spine heterogeneously. -/
theorem castFractions_heq {nextLower nextUpper : Rational}
    {nextLowerInside : 0 ≤ nextLower ∧ nextLower ≤ 1} {nextUpperInside : 0 ≤ nextUpper ∧ nextUpper ≤ 1}
    (firstEq : lower = nextLower) (lastEq : upper = nextUpper) :
    HEq (actual.castFractions (nextLowerInside := nextLowerInside) (nextUpperInside := nextUpperInside)
      firstEq lastEq) actual := by
  cases firstEq
  cases lastEq
  unfold castFractions
  rfl

/-- Exact fraction transport preserves the number of already retained new handoffs. -/
theorem castFractions_count {nextLower nextUpper : Rational}
    {nextLowerInside : 0 ≤ nextLower ∧ nextLower ≤ 1} {nextUpperInside : 0 ≤ nextUpper ∧ nextUpper ≤ 1}
    (firstEq : lower = nextLower) (lastEq : upper = nextUpper) :
    (actual.castFractions (nextLowerInside := nextLowerInside) (nextUpperInside := nextUpperInside)
      firstEq lastEq).sewn.junctions.length = actual.sewn.junctions.length := by
  cases firstEq
  cases lastEq
  unfold castFractions
  rfl

end RootedSpine

namespace Primitive

/-- The original admitted fractions of every interval, without requiring a physical segment to be nonstationary. -/
@[expose] def Bounds (intervals : List Interval) :=
  ∀ interval ∈ intervals,
    (0 ≤ interval.lower ∧ interval.lower ≤ 1) ∧ (0 ≤ interval.upper ∧ interval.upper ≤ 1)

/-- Store one actual root-attached primitive child per original interval-walk occurrence. -/
@[expose] def Pieces {intervals : List Interval} (bounded : Bounds intervals)
    {first last : Rational} (walk : IncreasingWalk intervals first last)
    (samples : Fin walk.edges.length → Canonical) :=
  DependentProduct walk.edges (fun index =>
    let interval := walk.edges[index.val]'index.isLt
    let inside := bounded interval (walk.edge_mem interval (List.getElem_mem index.isLt))
    RootedSpine edge expression accuracy interval.lower interval.upper inside.1 inside.2 (samples index))

/-- The exact admitted-owner and endpoint-observation inputs of one original interval walk's primitive sewing.

The stored piece bank, original fractions, signed generator relations and
both actual endpoint Vertices keep their original indices. This names the
function type only; it introduces no owner, cache or preparation record.
-/
@[expose] def WalkFamily {intervals : List Interval} (bounded : Bounds intervals)
    {first last : Rational} (walk : IncreasingWalk intervals first last)
    (samples : Fin walk.edges.length → Canonical) :=
  Pieces edge expression accuracy bounded walk samples →
    (firstInside : 0 ≤ first ∧ first ≤ 1) → (lastInside : 0 ≤ last ∧ last ≤ 1) →
    (source : Owner (curve.polynomial.eval (edge.point first))) →
    (target : Owner (curve.polynomial.eval (edge.point last))) →
    NamedEquivalent (ownerName source) (edge.rootName first firstInside) →
    NamedEquivalent (edge.rootName last lastInside) (ownerName target) →
    (initial : Vertex expression (edge.point first) source accuracy) →
    (terminal : Vertex expression (edge.point last) target accuracy) →
    Sewing (polynomial := curve.polynomial) (expression := expression) (accuracy := accuracy)
      initial terminal (sumFin samples)

/-- Construct one original nonempty walk step from its actual head and a delayed unchanged-tail consumer. -/
private def sewCons {intervals : List Interval} (bounded : Bounds intervals)
    (interval : Interval) (member : interval ∈ intervals) {finish : Rational}
    (tail : IncreasingWalk intervals interval.upper finish)
    (samples : Fin (IncreasingWalk.cons interval member tail).edges.length → Canonical)
    (remaining : WalkFamily edge expression accuracy bounded tail (fun index => samples index.succ)) :
    WalkFamily edge expression accuracy bounded (IncreasingWalk.cons interval member tail) samples :=
  fun pieces _firstInside lastInside _source target incoming outgoing initial terminal =>
    let inside := bounded interval member
    let firstIndex : Fin (tail.edges.length + 1) := ⟨0, Nat.zero_lt_succ _⟩
    let head : RootedSpine (curve := curve) (differential := differential) edge expression accuracy
        interval.lower interval.upper inside.1 inside.2 (samples firstIndex) := pieces.1
    let first := RootedSpine.first (curve := curve) (differential := differential)
      (edge := edge) (expression := expression) (accuracy := accuracy)
      (lower := interval.lower) (upper := interval.upper) (lowerInside := inside.1) (upperInside := inside.2)
      (sample := samples firstIndex) head
    let last := RootedSpine.last (curve := curve) (differential := differential)
      (edge := edge) (expression := expression) (accuracy := accuracy)
      (lower := interval.lower) (upper := interval.upper) (lowerInside := inside.1) (upperInside := inside.2)
      (sample := samples firstIndex) head
    let right := RootedSpine.right (curve := curve) (differential := differential)
      (edge := edge) (expression := expression) (accuracy := accuracy)
      (lower := interval.lower) (upper := interval.upper) (lowerInside := inside.1) (upperInside := inside.2)
      (sample := samples firstIndex) head
    let piece := RootedSpine.sewn (curve := curve) (differential := differential)
      (edge := edge) (expression := expression) (accuracy := accuracy)
      (lower := interval.lower) (upper := interval.upper) (lowerInside := inside.1) (upperInside := inside.2)
      (sample := samples firstIndex) head
    let firstRoot := RootedSpine.firstRoot (curve := curve) (differential := differential)
      (edge := edge) (expression := expression) (accuracy := accuracy)
      (lower := interval.lower) (upper := interval.upper) (lowerInside := inside.1) (upperInside := inside.2)
      (sample := samples firstIndex) head
    let lastRoot := RootedSpine.lastRoot (curve := curve) (differential := differential)
      (edge := edge) (expression := expression) (accuracy := accuracy)
      (lower := interval.lower) (upper := interval.upper) (lowerInside := inside.1) (upperInside := inside.2)
      (sample := samples firstIndex) head
    let opening := Sewing.stationary (polynomial := curve.polynomial) (expression := expression)
      (accuracy := accuracy) initial first rfl (incoming.trans firstRoot)
    let before := Sewing.append (polynomial := curve.polynomial) (expression := expression)
      (accuracy := accuracy) opening piece
    let front := Sewing.castSample (polynomial := curve.polynomial) (expression := expression)
      (accuracy := accuracy) (Canonical.zero_add (samples firstIndex)) before
    let following := remaining pieces.2 inside.2 lastInside right target lastRoot.symm outgoing last terminal
    let combined := Sewing.append (polynomial := curve.polynomial) (expression := expression)
      (accuracy := accuracy) front following
    Sewing.castSample (polynomial := curve.polynomial) (expression := expression)
      (accuracy := accuracy) (Fin.sumFin_succ samples).symm combined

/-- Sew the actual original fractional children in their exact retained increasing-walk order.

The input and terminal Vertices are supplied at the SAME original local
accuracy. Every actual child Spine remains unchanged. Incoming root evidence
and the retained child roots construct each real stationary handoff; the
empty tail keeps its own final comparison rather than erasing it.
-/
def sewWalk {intervals : List Interval} (bounded : Bounds intervals) :
    {first last : Rational} → (walk : IncreasingWalk intervals first last) →
    (samples : Fin walk.edges.length → Canonical) → WalkFamily edge expression accuracy bounded walk samples
  | _, _, .nil _, _ =>
      fun _pieces _firstInside _lastInside _source _target incoming outgoing initial terminal =>
        Sewing.stationary (polynomial := curve.polynomial) (expression := expression)
          (accuracy := accuracy) initial terminal rfl (incoming.trans outgoing)
  | _, _, .cons interval member tail, samples =>
      sewCons edge expression accuracy bounded interval member tail samples
        (fun pieces firstInside lastInside source target incoming outgoing initial terminal =>
          sewWalk bounded tail (fun index => samples index.succ) pieces firstInside lastInside
            source target incoming outgoing initial terminal)
termination_by structural _ _ walk _ => walk

/-- Count only the handoffs already stored in the SAME original walk pieces, in their retained order. -/
@[expose] def pieceCount {intervals : List Interval} (bounded : Bounds intervals) :
    {first last : Rational} → (walk : IncreasingWalk intervals first last) →
    (samples : Fin walk.edges.length → Canonical) → Pieces edge expression accuracy bounded walk samples → Nat
  | _, _, .nil _, _, _ => 0
  | _, _, .cons interval member tail, samples, pieces =>
      let inside := bounded interval member
      let head : RootedSpine (curve := curve) (differential := differential) edge expression accuracy
          interval.lower interval.upper inside.1 inside.2
          (samples (0 : Fin (tail.edges.length + 1))) := pieces.1
      (RootedSpine.sewn (curve := curve) (differential := differential) (edge := edge)
        (expression := expression) (accuracy := accuracy) head).junctions.length +
          pieceCount bounded tail (fun index => samples index.succ) pieces.2
termination_by structural _ _ walk _ _ => walk

/-- A retained walk bank whose actual entries have no new handoffs has zero existing-piece charge. -/
theorem pieceCount_eq_zero {intervals : List Interval} (bounded : Bounds intervals) :
    {first last : Rational} → (walk : IncreasingWalk intervals first last) →
    (samples : Fin walk.edges.length → Canonical) →
    (pieces : Pieces edge expression accuracy bounded walk samples) →
    (∀ index, (RootedSpine.sewn (curve := curve) (differential := differential) (edge := edge)
      (expression := expression) (accuracy := accuracy)
      (DependentProduct.get walk.edges pieces index)).junctions.length = 0) →
    pieceCount edge expression accuracy bounded walk samples pieces = 0
  | _, _, .nil _, _, _, _ => rfl
  | _, _, .cons interval member tail, samples, pieces, zero => by
      have firstZero := zero (0 : Fin (tail.edges.length + 1))
      have lastZero := pieceCount_eq_zero bounded tail (fun index => samples index.succ) pieces.2
        (fun index => zero index.succ)
      change (RootedSpine.sewn (curve := curve) (differential := differential) (edge := edge)
        (expression := expression) (accuracy := accuracy) pieces.1).junctions.length +
          pieceCount edge expression accuracy bounded tail (fun index => samples index.succ) pieces.2 = 0
      exact congrArg₂ Nat.add firstZero lastZero
termination_by structural _ _ walk _ _ _ => walk

/-- The exact pointwise handoff-count claim for one supplied original walk sewing function.

This names only the full proposition: the SAME pieces, original fractions,
endpoint Owners, admitted bounds and signed root relations remain quantified.
No input cache or observation is copied or replaced.
-/
@[expose] def WalkCount {intervals : List Interval} (bounded : Bounds intervals)
    {first last : Rational} (walk : IncreasingWalk intervals first last)
    (samples : Fin walk.edges.length → Canonical)
    (run : WalkFamily edge expression accuracy bounded walk samples) : Prop :=
  ∀ (pieces : Pieces edge expression accuracy bounded walk samples)
    (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1)
    (source : Owner (curve.polynomial.eval (edge.point first)))
    (target : Owner (curve.polynomial.eval (edge.point last)))
    (incoming : NamedEquivalent (ownerName source) (edge.rootName first firstInside))
    (outgoing : NamedEquivalent (edge.rootName last lastInside) (ownerName target))
    (initial : Vertex expression (edge.point first) source accuracy)
    (terminal : Vertex expression (edge.point last) target accuracy),
    (run pieces firstInside lastInside source target incoming outgoing initial terminal).junctions.length =
      pieceCount edge expression accuracy bounded walk samples pieces + walk.edges.length + 1

/-- The opening and final comparisons give the scalar count for one retained walk step. -/
private theorem countStep (head tail edges : Nat) :
    (1 + head) + (tail + edges + 1) = (head + tail) + (edges + 1) + 1 := by
  omega0

/-- One original cons step adds its actual opening charge and unchanged head/tail counts. -/
private theorem sewCons_count {intervals : List Interval} (bounded : Bounds intervals)
    (interval : Interval) (member : interval ∈ intervals) {finish : Rational}
    (tail : IncreasingWalk intervals interval.upper finish)
    (samples : Fin (IncreasingWalk.cons interval member tail).edges.length → Canonical)
    (remaining : WalkFamily edge expression accuracy bounded tail (fun index => samples index.succ))
    (counted : WalkCount edge expression accuracy bounded tail (fun index => samples index.succ) remaining) :
    WalkCount edge expression accuracy bounded (IncreasingWalk.cons interval member tail) samples
      (sewCons edge expression accuracy bounded interval member tail samples remaining) := by
  intro pieces firstInside lastInside source target incoming outgoing initial terminal
  let inside := bounded interval member
  let firstIndex : Fin (tail.edges.length + 1) := ⟨0, Nat.zero_lt_succ _⟩
  let head : RootedSpine (curve := curve) (differential := differential) edge expression accuracy
      interval.lower interval.upper inside.1 inside.2 (samples firstIndex) := pieces.1
  let first := RootedSpine.first (curve := curve) (differential := differential)
    (edge := edge) (expression := expression) (accuracy := accuracy)
    (lower := interval.lower) (upper := interval.upper) (lowerInside := inside.1) (upperInside := inside.2)
    (sample := samples firstIndex) head
  let last := RootedSpine.last (curve := curve) (differential := differential)
    (edge := edge) (expression := expression) (accuracy := accuracy)
    (lower := interval.lower) (upper := interval.upper) (lowerInside := inside.1) (upperInside := inside.2)
    (sample := samples firstIndex) head
  let right := RootedSpine.right (curve := curve) (differential := differential)
    (edge := edge) (expression := expression) (accuracy := accuracy)
    (lower := interval.lower) (upper := interval.upper) (lowerInside := inside.1) (upperInside := inside.2)
    (sample := samples firstIndex) head
  let piece := RootedSpine.sewn (curve := curve) (differential := differential)
    (edge := edge) (expression := expression) (accuracy := accuracy)
    (lower := interval.lower) (upper := interval.upper) (lowerInside := inside.1) (upperInside := inside.2)
    (sample := samples firstIndex) head
  let firstRoot := RootedSpine.firstRoot (curve := curve) (differential := differential)
    (edge := edge) (expression := expression) (accuracy := accuracy)
    (lower := interval.lower) (upper := interval.upper) (lowerInside := inside.1) (upperInside := inside.2)
    (sample := samples firstIndex) head
  let lastRoot := RootedSpine.lastRoot (curve := curve) (differential := differential)
    (edge := edge) (expression := expression) (accuracy := accuracy)
    (lower := interval.lower) (upper := interval.upper) (lowerInside := inside.1) (upperInside := inside.2)
    (sample := samples firstIndex) head
  let opening := Sewing.stationary (polynomial := curve.polynomial) (expression := expression)
    (accuracy := accuracy) initial first rfl (incoming.trans firstRoot)
  let before := Sewing.append (polynomial := curve.polynomial) (expression := expression)
    (accuracy := accuracy) opening piece
  let front := Sewing.castSample (polynomial := curve.polynomial) (expression := expression)
    (accuracy := accuracy) (Canonical.zero_add (samples firstIndex)) before
  let following := remaining pieces.2 inside.2 lastInside right target lastRoot.symm outgoing last terminal
  have followingCount := counted pieces.2 inside.2 lastInside right target lastRoot.symm outgoing last terminal
  have frontCount : front.junctions.length = 1 + piece.junctions.length := by
    change (Sewing.castSample (polynomial := curve.polynomial) (expression := expression)
      (accuracy := accuracy) (Canonical.zero_add (samples firstIndex))
      (Sewing.append (polynomial := curve.polynomial) (expression := expression) (accuracy := accuracy)
        opening piece)).junctions.length = _
    rewrite [Sewing.castSample_count, Sewing.append_count]
    exact congrArg (fun count : Nat => count + piece.junctions.length)
      (Sewing.stationary_count (polynomial := curve.polynomial) (expression := expression)
        (accuracy := accuracy) initial first rfl (incoming.trans firstRoot))
  change (Sewing.castSample (polynomial := curve.polynomial) (expression := expression)
    (accuracy := accuracy) (Fin.sumFin_succ samples).symm
    (Sewing.append (polynomial := curve.polynomial) (expression := expression) (accuracy := accuracy)
      front following)).junctions.length = _
  exact ((Sewing.castSample_count (polynomial := curve.polynomial) (expression := expression)
    (accuracy := accuracy) (Fin.sumFin_succ samples).symm
    (Sewing.append (polynomial := curve.polynomial) (expression := expression) (accuracy := accuracy)
      front following)).trans
    (Sewing.append_count (polynomial := curve.polynomial) (expression := expression)
      (accuracy := accuracy) front following)).trans
    ((congrArg₂ Nat.add frontCount followingCount).trans
      (countStep piece.junctions.length
        (pieceCount edge expression accuracy bounded tail (fun index => samples index.succ) pieces.2)
        tail.edges.length))

/-- An original walk adds one handoff per interval and its final comparison to the old pieces. -/
theorem sewWalk_count {intervals : List Interval} (bounded : Bounds intervals) :
    {first last : Rational} → (walk : IncreasingWalk intervals first last) →
    (samples : Fin walk.edges.length → Canonical) →
    WalkCount edge expression accuracy bounded walk samples
      (sewWalk edge expression accuracy bounded walk samples)
  | _, _, .nil _, _ => by
      intro _pieces _firstInside _lastInside _source _target incoming outgoing initial terminal
      change (Sewing.stationary (polynomial := curve.polynomial) (expression := expression)
        (accuracy := accuracy) initial terminal rfl (incoming.trans outgoing)).junctions.length = 1
      exact Sewing.stationary_count (polynomial := curve.polynomial) (expression := expression)
        (accuracy := accuracy) initial terminal rfl (incoming.trans outgoing)
  | _, _, .cons interval member tail, samples =>
      sewCons_count edge expression accuracy bounded interval member tail samples
        (fun pieces firstInside lastInside source target incoming outgoing initial terminal =>
          sewWalk edge expression accuracy bounded tail (fun index => samples index.succ)
            pieces firstInside lastInside source target incoming outgoing initial terminal)
        (fun pieces firstInside lastInside source target incoming outgoing initial terminal =>
          sewWalk_count bounded tail (fun index => samples index.succ)
            pieces firstInside lastInside source target incoming outgoing initial terminal)
termination_by structural _ _ walk _ => walk

/-- Zero existing piece charges imply an actual walk has exactly its interval count plus one new handoffs. -/
theorem sewWalk_count_of_pieceCount_zero {intervals : List Interval} (bounded : Bounds intervals)
    {first last : Rational} (walk : IncreasingWalk intervals first last)
    (samples : Fin walk.edges.length → Canonical) (pieces : Pieces edge expression accuracy bounded walk samples)
    (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1)
    (source : Owner (curve.polynomial.eval (edge.point first)))
    (target : Owner (curve.polynomial.eval (edge.point last)))
    (incoming : NamedEquivalent (ownerName source) (edge.rootName first firstInside))
    (outgoing : NamedEquivalent (edge.rootName last lastInside) (ownerName target))
    (initial : Vertex expression (edge.point first) source accuracy)
    (terminal : Vertex expression (edge.point last) target accuracy)
    (zero : pieceCount edge expression accuracy bounded walk samples pieces = 0) :
    (sewWalk edge expression accuracy bounded walk samples pieces firstInside lastInside source target
      incoming outgoing initial terminal).junctions.length = walk.edges.length + 1 := by
  have actual := sewWalk_count edge expression accuracy bounded walk samples pieces firstInside lastInside
    source target incoming outgoing initial terminal
  rewrite [zero, Nat.zero_add] at actual
  exact actual

end Primitive

end Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge

end
