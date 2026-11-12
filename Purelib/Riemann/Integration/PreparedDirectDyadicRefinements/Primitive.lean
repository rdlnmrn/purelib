module

public import Purelib.Riemann.Integration.PreparedConstantModels.Primitive
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
public import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.DependentProduct
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Tactic.QuotientFreeOmega

/-! # Paid primitive sewing along an original geometric and root chain

The same retained centered parents supply geometry, while their independent
RootChain supplies every signed boundary comparison. Actual rooted primitive
pieces remain unchanged. Exact endpoint/whole-Owner transports retain the
old observations, and every new handoff contributes its real local payment.
-/

public section

namespace Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain.Primitive

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
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge (RootedSpine)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive (Vertex)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive.Spine (Sewing)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner ownerName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter castOwnerParameter_heq)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName_castOwnerParameter)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable (expression : Expression curve.polynomial) (accuracy : AccuracyRequest)

/-- One actual root-attached primitive assembly per original centered-parent occurrence. -/
@[expose] def Pieces (parents : List (CenteredEdge curve differential))
    (samples : Fin parents.length → Canonical) :=
  DependentProduct parents (fun index =>
    RootedSpine (parents[index.val]'index.isLt).edge expression accuracy
      0 1 (parents[index.val]'index.isLt).edge.baseInside (of_decide_eq_true rfl) (samples index))

/-- Continue from the actual preceding Point Owner, retaining the original next comparison and literal root tail. -/
private def followingRoots {parent : CenteredEdge curve differential} :
    {parents : List (CenteredEdge curve differential)} → {first last current : Named} →
    RootChain (parent :: parents) first last →
    NamedEquivalent current (parent.edge.rootName 1 (of_decide_eq_true rfl)) → RootChain parents current last
  | [], _, _, _, roots, incoming => .nil (incoming.trans roots.finishEquivalent)
  | next :: _, _, _, _, roots, incoming =>
      .cons next (incoming.trans roots.nextEquivalent) roots.remaining.remaining

/-- Construct the actual whole owner path and primitive Spine through every original root-attached parent.

The empty list retains its actual source-to-paid-finish root comparison and
geometric endpoint identity. A nonempty step uses the original incoming
comparison, keeps the complete head Spine, and passes the exact transported
old final Vertex to the unchanged tail. Across parent or Segment boundaries,
followingRoots consumes the SAME original RootChain.nextEquivalent.
-/
def sewParents :
    {parents : List (CenteredEdge curve differential)} → {start finish : LiftedPoint 2} →
    (geometry : CenteredPathChain parents (start := start) (finish := finish)) →
    (source : Owner (curve.polynomial.eval start.coordinate)) →
    (target : Owner (curve.polynomial.eval finish.coordinate)) →
    RootChain parents (ownerName source) (ownerName target) →
    (samples : Fin parents.length → Canonical) → Pieces expression accuracy parents samples →
    (initial : Vertex expression start.coordinate source accuracy) →
    (terminal : Vertex expression finish.coordinate target accuracy) →
    Sewing initial terminal (sumFin samples)
  | [], _, _, geometry, _source, _target, .nil equivalent, _, _, initial, terminal =>
      Sewing.stationary (polynomial := curve.polynomial)
        (expression := expression) (accuracy := accuracy) initial terminal
        (congrArg LiftedPoint.coordinate geometry.empty_eq) equivalent
  | parent :: _, _, _, geometry, _source, target, roots, samples, pieces, initial, terminal =>
      let head := pieces.1
      let starting := (congrArg LiftedPoint.coordinate geometry.start_eq).symm.trans parent.edge.point_zero.symm
      let equivalent := roots.firstEquivalent.trans head.firstRoot
      let opening := Sewing.stationary (polynomial := curve.polynomial)
        (expression := expression) (accuracy := accuracy) initial head.first starting equivalent
      let front := Sewing.castSample (polynomial := curve.polynomial)
        (expression := expression) (accuracy := accuracy) (Canonical.zero_add (samples 0))
        (Sewing.append (polynomial := curve.polynomial)
          (expression := expression) (accuracy := accuracy) opening head.sewn)
      let ending := parent.edge.point_one
      let parameterEq := congrArg curve.polynomial.eval ending
      let nextOwner := castOwnerParameter parameterEq head.right
      let shifted := Sewing.castFinish (polynomial := curve.polynomial)
        (expression := expression) (accuracy := accuracy)
        ending (castOwnerParameter_heq parameterEq head.right).symm front
      let sameName := ownerRootName_castOwnerParameter parameterEq head.right
      let incoming := NamedEquivalent.transport sameName.symm rfl head.lastRoot.symm
      let tailRoots := followingRoots roots incoming
      let following := sewParents geometry.remaining nextOwner target tailRoots
        (fun index => samples index.succ) pieces.2 shifted.1 terminal
      let combined := Sewing.append (polynomial := curve.polynomial) (expression := expression)
        (accuracy := accuracy) shifted.2 following
      Sewing.castSample (polynomial := curve.polynomial) (expression := expression)
        (accuracy := accuracy) (Fin.sumFin_succ samples).symm combined
termination_by structural parents => parents

/-- Count exactly the existing new handoffs retained inside the SAME ordered parent primitive pieces. -/
@[expose] def pieceCount : (parents : List (CenteredEdge curve differential)) →
    (samples : Fin parents.length → Canonical) → Pieces expression accuracy parents samples → Nat
  | [], _, _ => 0
  | parent :: parents, samples, pieces =>
      let head : RootedSpine (curve := curve) (differential := differential) parent.edge expression accuracy
          0 1 parent.edge.baseInside (of_decide_eq_true rfl) (samples 0) := pieces.1
      (RootedSpine.sewn (curve := curve) (differential := differential) (edge := parent.edge)
        (expression := expression) (accuracy := accuracy) head).junctions.length +
          pieceCount parents (fun index => samples index.succ) pieces.2

/-- Reading each SAME retained parent cache into the sample/piece views preserves its exact stored handoff sum. -/
theorem pieceCount_ofFn : (parents : List (CenteredEdge curve differential)) →
    (entries : DependentProduct parents (fun index =>
      Σ sample : Canonical,
        RootedSpine (parents[index.val]'index.isLt).edge expression accuracy
          0 1 (parents[index.val]'index.isLt).edge.baseInside (of_decide_eq_true rfl) sample)) →
    pieceCount expression accuracy parents
      (fun index => (DependentProduct.get parents entries index).1)
      (DependentProduct.ofFn parents (fun index => (DependentProduct.get parents entries index).2)) =
        DependentProduct.sum parents (fun _index actual => actual.2.junctionCount) entries
  | [], _ => rfl
  | _parent :: parents, entries => by
      change entries.1.2.sewn.junctions.length +
          pieceCount expression accuracy parents (fun index => (DependentProduct.get parents entries.2 index).1)
            (DependentProduct.ofFn parents (fun index => (DependentProduct.get parents entries.2 index).2)) =
        entries.1.2.junctionCount +
          DependentProduct.sum parents (fun _index actual => actual.2.junctionCount) entries.2
      exact congrArg₂ Nat.add (entries.1.2.junctionCount_eq.symm) (pieceCount_ofFn parents entries.2)

/-- The original parent chain adds exactly one handoff per parent plus its actual final comparison.

Every old child charge remains counted through its SAME stored primitive
Spine. Endpoint and whole-Owner transports change no count; the original
nil comparison is included even when the parent word is empty.
-/
theorem sewParents_count :
    {parents : List (CenteredEdge curve differential)} → {start finish : LiftedPoint 2} →
    (geometry : CenteredPathChain parents (start := start) (finish := finish)) →
    (source : Owner (curve.polynomial.eval start.coordinate)) →
    (target : Owner (curve.polynomial.eval finish.coordinate)) →
    (roots : RootChain parents (ownerName source) (ownerName target)) →
    (samples : Fin parents.length → Canonical) → (pieces : Pieces expression accuracy parents samples) →
    (initial : Vertex expression start.coordinate source accuracy) →
    (terminal : Vertex expression finish.coordinate target accuracy) →
    (sewParents expression accuracy geometry source target roots samples pieces initial terminal).junctions.length =
      pieceCount expression accuracy parents samples pieces + parents.length + 1
  | [], _, _, geometry, _source, _target, .nil equivalent, _, _, initial, terminal => by
      change (Sewing.stationary (polynomial := curve.polynomial) (expression := expression)
        (accuracy := accuracy) initial terminal (congrArg LiftedPoint.coordinate geometry.empty_eq)
        equivalent).junctions.length = 1
      exact Sewing.stationary_count (polynomial := curve.polynomial) (expression := expression)
        (accuracy := accuracy) initial terminal (congrArg LiftedPoint.coordinate geometry.empty_eq) equivalent
  | parent :: parents, _, _, geometry, source, target, roots, samples, pieces, initial, terminal => by
      let head : RootedSpine (curve := curve) (differential := differential) parent.edge expression accuracy
          0 1 parent.edge.baseInside (of_decide_eq_true rfl) (samples 0) := pieces.1
      let starting := (congrArg LiftedPoint.coordinate geometry.start_eq).symm.trans parent.edge.point_zero.symm
      let opening := Sewing.stationary (polynomial := curve.polynomial) (expression := expression)
        (accuracy := accuracy) initial head.first starting (roots.firstEquivalent.trans head.firstRoot)
      let front := Sewing.castSample (polynomial := curve.polynomial) (expression := expression)
        (accuracy := accuracy) (Canonical.zero_add (samples 0))
        (Sewing.append (polynomial := curve.polynomial) (expression := expression) (accuracy := accuracy)
          opening head.sewn)
      let ending := parent.edge.point_one
      let parameterEq := congrArg curve.polynomial.eval ending
      let nextOwner := castOwnerParameter parameterEq head.right
      let shifted := Sewing.castFinish (polynomial := curve.polynomial) (expression := expression)
        (accuracy := accuracy) ending (castOwnerParameter_heq parameterEq head.right).symm front
      let incoming := NamedEquivalent.transport
        (ownerRootName_castOwnerParameter parameterEq head.right).symm rfl head.lastRoot.symm
      let tailRoots := followingRoots roots incoming
      let following := sewParents expression accuracy geometry.remaining nextOwner target tailRoots
        (fun index => samples index.succ) pieces.2 shifted.1 terminal
      have tailCount := sewParents_count geometry.remaining nextOwner target tailRoots
        (fun index => samples index.succ) pieces.2 shifted.1 terminal
      have headCount : shifted.2.junctions.length = 1 + head.sewn.junctions.length := by
        change (Sewing.castFinish (polynomial := curve.polynomial) (expression := expression)
          (accuracy := accuracy) ending (castOwnerParameter_heq parameterEq head.right).symm
          front).2.junctions.length = _
        rewrite [Sewing.castFinish_count]
        change (Sewing.castSample (polynomial := curve.polynomial) (expression := expression)
          (accuracy := accuracy) (Canonical.zero_add (samples 0))
          (Sewing.append (polynomial := curve.polynomial) (expression := expression) (accuracy := accuracy)
            opening head.sewn)).junctions.length = _
        rewrite [Sewing.castSample_count, Sewing.append_count]
        exact congrArg (fun count : Nat => count + head.sewn.junctions.length)
          (Sewing.stationary_count (polynomial := curve.polynomial) (expression := expression)
            (accuracy := accuracy) initial head.first starting (roots.firstEquivalent.trans head.firstRoot))
      change (Sewing.castSample (polynomial := curve.polynomial) (expression := expression)
        (accuracy := accuracy) (Fin.sumFin_succ samples).symm
        (Sewing.append (polynomial := curve.polynomial) (expression := expression) (accuracy := accuracy)
          shifted.2 following)).junctions.length = _
      rewrite [Sewing.castSample_count, Sewing.append_count, headCount, tailCount]
      change (1 + head.sewn.junctions.length) +
        (pieceCount expression accuracy parents (fun index => samples index.succ) pieces.2 + parents.length + 1) =
          (head.sewn.junctions.length +
            pieceCount expression accuracy parents (fun index => samples index.succ) pieces.2) +
              (parents.length + 1) + 1
      omega0
termination_by structural parents => parents

end Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain.Primitive

end
