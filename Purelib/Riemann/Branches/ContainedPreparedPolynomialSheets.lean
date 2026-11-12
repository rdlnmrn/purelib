module
public import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
public import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Branches.PreparedPolynomialSheetReadings
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Tactic.Ring
import Purelib.Riemann.Normalization.InverseModelRefinementSigns
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Branches.RectangularSheetGauge
public import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Data.Fin
import Purelib.Riemann.Branches.PreparedPrimitiveSheets
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.ContinuedInverseRoot
public import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RegularFaceInverseModels
public import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Paths.PreparedPathGluing
public import Purelib.Riemann.RootContinuation.ClearBoxRootTransport
public import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedConstantModels
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Topology.PreparedBankRootChains

public import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Riemann.Integration.PreparedCoveredParentLists
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
public import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Riemann.Normalization.InverseRootPrimitive

@[expose] public section

/-!
# Automatic sheet propagation inside one inverse-model cell

Every endpoint of a retained preparation lies in its original ambient box.
The actual covered trace therefore supplies both spines and all containment
needed to propagate a fixed inverse model to an arbitrary terminal point.
The model is not reacquired or reoriented along the path.
-/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint Subdivision)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge CenterStates centeredEdges)
open Purelib.Riemann.Paths.PreparedClearPathModels (CompleteSegment PreparedPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial (OverlapReady)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial (RootAligned)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation (EndpointsIn alongChain)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}

namespace Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- Every retained prepared path lies in its original ambient box. -/
theorem prepared_within {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} :
    ∀ {start finish : Basic.Canonical} {path : Geometry.ClearPath polynomial ambient start finish}
      {owner : Owner (polynomial.eval start)}, PreparedPath path owner → path.WithinAmbient
  | _, _, _, _, .nil point _ => .nil point
  | _, _, _, _, .cons _ _ _ within _ rest => .cons within (prepared_within rest)

end Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation

namespace Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation.EndpointsIn

open Purelib.Geometry.Rational in
/-- Concatenation preserves containment of every original centered-parent endpoint in the same box. -/
private theorem append {box : Box} {first second : List (CenteredEdge curve
  differential)}
    (left : EndpointsIn box first) (right : EndpointsIn box second) : EndpointsIn box (first ++ second) := by
  induction first with
  | nil => exact right
  | cons head tail ih => exact ⟨left.1, left.2.1, ih left.2.2⟩

end Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation.EndpointsIn

namespace Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Integration in
/-- The original centered edges of a prepared subdivision have both endpoints in its retained ambient box. -/
private theorem subdivision_endpoints (curve : HyperellipticCurve genus) (differential :
  Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish) (within : segment.WithinAmbient)
    (sheet : Fin 2) :
    ∀ {left : Endpoint} {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
      (subdivision : Subdivision segment within left owner) (centers : CenterStates curve differential sheet
        subdivision),
      EndpointsIn ambient (centeredEdges curve differential sheet subdivision centers)
  | _, _, .stop _ _, _ => trivial
  | _, _, .next left _ request _ _ _ remaining, centers => by
      refine ⟨?_, ?_, subdivision_endpoints curve differential segment within sheet remaining centers.2⟩
      · rw [PreparedConstantModels.PreparedEdge.point_zero]
        exact segment.pointAt_contains within left.parameter left.inside
      · rw [PreparedConstantModels.PreparedEdge.point_one]
        exact segment.pointAt_contains within request.endpoint.parameter request.endpoint.inside

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- All original centered parent edges of a prepared path have endpoints in its retained ambient box. -/
theorem prepared_endpoints (curve : HyperellipticCurve genus) (differential : Differential
  genus)
    (sheet : Fin 2) {ambient : Box} :
    ∀ {start finish : Basic.Canonical} {path : Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)} (prepared : PreparedPath path owner),
      EndpointsIn ambient (CenteredPathChain.ofPreparedPath curve differential sheet prepared).parents
  | _, _, _, _, .nil _ _ => trivial
  | _, _, _, _, .cons head _ _ within first rest => by
      change EndpointsIn ambient ((CenteredPathChain.dataOfCompleteSegment curve differential sheet first).parents ++ _)
      apply EndpointsIn.append _ (prepared_endpoints curve differential sheet rest)
      rw [CenteredPathChain.dataOfCompleteSegment_parents]
      exact subdivision_endpoints curve differential head within sheet first.subdivision _

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- A prepared path starting inside its original ambient box also finishes inside it. -/
theorem prepared_finish_inside {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient :
  Box} :
    ∀ {start finish : Basic.Canonical} {path : Geometry.ClearPath polynomial ambient start finish}
      {owner : Owner (polynomial.eval start)} (_prepared : PreparedPath path owner),
      ambient.Contains start → ambient.Contains finish
  | _, _, _, _, .nil _ _, inside => inside
  | _, _, _, _, .cons head _ _ within _ rest, _ => by
      apply prepared_finish_inside rest
      have inside := head.pointAt_contains within 1 (by decide)
      rw [Geometry.ClearPath.ClearSegment.pointAt_one] at inside
      exact inside

section CoveredTrace

open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Paths
open Purelib.Riemann.Topology

/-- The original covered preparation propagates one model along its exact retained complete-segment spine.

Each head consumes its actual primitive mesh equation and original
complete segment. Its literal tail begins with that segment's actual
finish owner, so no independently selected endpoint or new preparation
enters the induction.
-/
private theorem prepared_aligned {polynomial : Geometry.ClearPath.GaussianPolynomial} {box : Box}
    {model : OverlapReady polynomial box} {start finish : Basic.Canonical}
    {path : Geometry.ClearPath polynomial box start finish}
    {owner : Owner (polynomial.eval start)} {prepared : PreparedPath path owner}
    (cover : PreparedPathPrimitiveCover.PreparedClearPathModels.PreparedPath.PrimitiveCover prepared)
    (initial : RootAligned model start (ownerName owner)) :
    RootAligned model finish (ownerName (PreparedPathGluing.finishOwner prepared)) := by
  revert initial
  induction cover with
  | nil point owner =>
      intro initial
      exact initial
  | @cons start middle finish head tail owner within first rest bounds mesh meshEq remaining inductionHypothesis =>
      intro initial
      apply inductionHypothesis
      exact RootAligned.completeSegment head within (Box.refines_refl box)
        first bounds mesh meshEq initial

/-- Continue the same inverse model along an actual primitive-covered trace of its original polynomial.

The supplied trace and cover retain every original subdivision, request,
owner and mesh. Their complete-segment spine propagates alignment without
assuming a hyperelliptic curve presentation or selecting another sheet.
The exact cached finish-owner equation then identifies the traced result.
-/
theorem coveredTrace_aligned {polynomial : Geometry.ClearPath.GaussianPolynomial}
    {box : Box} {start finish : Basic.Canonical}
    {path : Geometry.ClearPath polynomial box start finish}
    {owner : Owner (polynomial.eval start)} (prepared : CoveredTracedPath path owner)
    {model : OverlapReady polynomial box} (initial : RootAligned model start (ownerName owner)) :
    RootAligned model finish (ownerName prepared.traced.finishOwner) := by
  have final : RootAligned model finish (ownerName (PreparedPathGluing.finishOwner prepared.traced.prepared)) := by
    apply prepared_aligned prepared.cover
    exact initial
  intro count patch inside sample equivalent index
  apply final patch inside sample _ index
  rewrite [← prepared.traced.finishOwner_eq]
  exact equivalent

end CoveredTrace

end Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation

end

section

open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)
open Purelib.Riemann.Normalization.RegularFaceInverseModels (Clearance Bounds)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial (RootAligned)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)

namespace Purelib.Riemann.Normalization.TransportedFaceInverseModels.TransportedCell

open Purelib.Geometry.Rational in
open Purelib.Riemann.Branches in
/-- The transported cell model is aligned at its anchor with its exact traced terminal owner.

The retained aligned-seed refinement compares the original root names and establishes nearestness for the indexed
overlap refinement. -/
theorem rootAligned {polynomial :
  Polynomial} {box inner : Geometry.Rational.Box}
    {clearance : Clearance polynomial box} {bounds : Bounds clearance}
    {source : Owner (polynomial.eval box.anchor)} (cell : TransportedCell bounds source inner) (index : Nat) :
    RootAligned ((PreparedPolynomialSheetPropagation.InverseRootPolynomial.Model.overlapRefine cell.model) index)
      inner.anchor (ownerName cell.traced.finishOwner) := by
  intro count patch inside sample roots rightIndex
  have seedEquivalent := (PreparedPrimitiveSheets.rootEquivalent_of_initial_refines
    cell.traced.finishOwner.parameterNonzero cell.traced.finishOwner.track
    cell.aligned.seed.owner.track cell.aligned.refines).symm
  exact cell.anchor_nearest sample inside (seedEquivalent.trans roots) (index + 2) (rightIndex + 2)

end Purelib.Riemann.Normalization.TransportedFaceInverseModels.TransportedCell

section
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial

namespace Purelib.Riemann.Normalization.TransportedFaceInverseModels.TransportedCell

open Purelib.Riemann.Branches in
open Purelib.Riemann.Paths in
/-- A transported cell model remains root-aligned along an original primitive-covered path inside its cell. -/
theorem continuedAligned {genus : Nat}
  {curve : HyperellipticCurve genus} {box inner : Geometry.Rational.Box}
    {clearance : Clearance curve.polynomial box} {bounds : Bounds clearance}
    {source : Owner (curve.polynomial.eval box.anchor)} (cell : TransportedCell bounds source inner)
    (_differential : Differential genus) {finish : Basic.Canonical}
    {path : Geometry.ClearPath curve.polynomial inner inner.anchor finish}
    (prepared : PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath path cell.traced.finishOwner)
      (index : Nat) :
    RootAligned ((PreparedPolynomialSheetPropagation.InverseRootPolynomial.Model.overlapRefine cell.model) index) finish
      (ownerName prepared.traced.finishOwner) :=
  ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation.coveredTrace_aligned
    prepared (cell.rootAligned index)

open Purelib.Riemann.Paths
/-- The transported cell model and terminal continued neighborhood choose compatible nearest signs at the original path
endpoint.

The original covered trace supplies root alignment, and its retained neighborhood reading supplies the exact comparison
of endpoint root names. -/
theorem continued_nearest {genus :
  Nat} {curve : HyperellipticCurve genus} {box inner : Geometry.Rational.Box}
    {clearance : Clearance curve.polynomial box} {bounds : Bounds clearance}
    {source : Owner (curve.polynomial.eval box.anchor)} (cell : TransportedCell bounds source inner)
    (differential : Differential genus) {point : Basic.Canonical}
    {path : Geometry.ClearPath curve.polynomial inner inner.anchor point}
    (prepared : PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath path cell.traced.finishOwner)
      {count : Nat}
    (neighborhood : TracedPrimitiveNeighborhood.Neighborhood prepared.traced count) (leftIndex rightIndex : Nat) :
    Norm.Basic.normSq
      ((cell.model.refine (leftIndex + 2)).value.eval point - (neighborhood.patch.base.refine (rightIndex +
        2)).value.eval point) ≤
    Norm.Basic.normSq
      ((cell.model.refine (leftIndex + 2)).value.eval point + (neighborhood.patch.base.refine (rightIndex +
        2)).value.eval point) := by
  let sample := ContinuedNeighborhood.Point.acquire neighborhood.patch point neighborhood.center_inside
  exact cell.continuedAligned differential prepared leftIndex neighborhood.patch neighborhood.center_inside sample
    (neighborhood.pointEquivalent sample) rightIndex

/-- Build an unflipped edge transition between the transported cell model and its terminal continued neighborhood.

The supplied endpoint value equations identify the exact model refinements. Original cell and neighborhood containments
are retained, and continued nearestness certifies the unchanged second value. -/
def continuedTransition {genus : Nat}
  {curve : HyperellipticCurve genus} {box inner : Geometry.Rational.Box}
    {clearance : Clearance curve.polynomial box} {bounds : Bounds clearance}
    {source : Owner (curve.polynomial.eval box.anchor)} (cell : TransportedCell bounds source inner)
    (differential : Differential genus) {point : Basic.Canonical}
    {path : Geometry.ClearPath curve.polynomial inner inner.anchor point}
    (prepared : PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath path cell.traced.finishOwner)
      {count : Nat}
    (neighborhood : TracedPrimitiveNeighborhood.Neighborhood prepared.traced count) (leftIndex rightIndex : Nat)
    (left : Model curve.polynomial inner) (right : Model curve.polynomial neighborhood.patch.base.box)
    (leftEq : left.value.eval point = (cell.model.refine (leftIndex + 2)).value.eval point)
    (rightEq : right.value.eval point = (neighborhood.patch.base.refine (rightIndex + 2)).value.eval point)
    (finish : Basic.Canonical) (leftFinish : inner.Contains finish) (rightFinish : neighborhood.patch.box.Contains
      finish) :
    EdgeTransition left right point finish where
  leftStart := Branches.ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation.prepared_finish_inside
    prepared.traced.prepared inner.contains_anchor
  leftFinish := leftFinish
  rightStart := neighborhood.patch.box_refines.contains neighborhood.center_inside
  rightFinish := neighborhood.patch.box_refines.contains rightFinish
  sample :=
    let first := left.value.eval point
    let second := right.value.eval point
    ⟨first, rfl, second, rfl, ⟨false, second, rfl, by
      dsimp only [first, second]
      rw [leftEq, rightEq]
      have scalar := cell.continued_nearest differential prepared neighborhood leftIndex rightIndex
      simpa only [Norm.Basic.normSq_eq_canonical] using scalar⟩⟩

section

open Purelib
open Purelib.Data.Gaussian.Norm
open Purelib.Riemann.Paths
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseModelOverlap
open Purelib.Riemann.Normalization.InverseModelRefinementSigns
open Purelib.Riemann.Normalization.OwnerSeededInverseRoot (SeededNeighborhood)
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial (OverlapReady)
open Purelib.Riemann.Paths.ClearBoxPaths (Route)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.RootContinuation.RootPathTransport
open Purelib.Riemann.RootContinuation.ClearBoxRootTransport
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation (prepared_within)
open Purelib.Polynomial.Geometry.ClearPath (InBox)
open Purelib.Polynomial.Winding
open Purelib.Riemann.Comparison
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (DensePrimitive PrimitiveEdgeAccuracy PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

variable {genus : Nat} {curve : HyperellipticCurve genus}
    {box inner ambient : Geometry.Rational.Box} {clearance : Clearance curve.polynomial box}
    {bounds : Bounds clearance} {start point : Data.Gaussian.Basic.Canonical}
    {source : Owner (curve.polynomial.eval start)} {prefixAmbient : Geometry.Rational.Box}
    {prefixPath : Polynomial.Geometry.ClearPath curve.polynomial prefixAmbient start box.anchor}
    {entered : TracedPath prefixPath source}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start point}

/-- Compare the actual two-piece continuation with a global face trace. Both original preparations and their owners are
retained. The winding equality is obtained by telescoping the face potential, not assumed. -/
def compareContinuedTrace (cell : TransportedCell bounds entered.finishOwner inner)
    (prefixInside : InBox box prefixPath)
    (degreePositive : 0 < curve.polynomial.natDegree)
    (reference : WindingOneLoop curve.polynomial start)
    {localPath : Polynomial.Geometry.ClearPath curve.polynomial inner inner.anchor point}
    (prepared : CoveredTracedPath localPath cell.traced.finishOwner)
    (traced : PreparedPathTrace.TracedPath path source) (inside : InBox box
      path)
    (frame : OwnerFrame (curve.polynomial.eval point)) :
    NamedEquivalent (OwnerTraceReadings.ownerName prepared.traced.finishOwner)
      (OwnerTraceReadings.ownerName traced.finishOwner) := by
  let joined := entered.trace.get.append (cell.traced.trace.get.append prepared.traced.trace.get)
  have localInside : localPath.InBox box :=
    (InBox.ofWithin localPath (prepared_within
      prepared.traced.prepared)
      inner.contains_anchor).mono cell.geometry.refines
  have winding : PreparedPathWinding.ClearPath.rawWinding path = Polygon.Basic.chainRaw curve.polynomial start
    joined.vertices := by
    rw [RootContinuation.RootPathTransport.OwnerPath.append_winding,
      RootContinuation.RootPathTransport.OwnerPath.append_winding,
      PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original entered,
      PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original cell.traced,
      PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original prepared.traced,
      ClearBoxPathWinding.ClearPath.rawWinding_eq_potential clearance degreePositive prefixPath prefixInside,
      ClearBoxPathWinding.Route.winding clearance
        degreePositive cell.route box.contains_anchor,
      ClearBoxPathWinding.ClearPath.rawWinding_eq_potential clearance
        degreePositive localPath localInside,
      ClearBoxPathWinding.ClearPath.rawWinding_eq_potential clearance
        degreePositive path inside]
    omega
  exact (TracedPath.equivalentOfOwnerPathSelections
    reference
    (prepared_within traced.prepared) traced
    joined frame (frame.select traced.finishOwner) (frame.select prepared.traced.finishOwner) winding).symm

/-- The internal connector and its coverage are constructed inside the proof. At an arbitrary reached point, no local
path, coverage, root sign, or same-occurrence certificate is required by the caller. -/
theorem trace_aligned (cell : TransportedCell bounds entered.finishOwner inner)
    (prefixInside : InBox box prefixPath)
    (differential : Differential genus)
    (degreePositive : 0 < curve.polynomial.natDegree)
    (reference : WindingOneLoop curve.polynomial start) (traced : PreparedPathTrace.TracedPath path
      source)
    (inside : InBox box path) (frame : OwnerFrame (curve.polynomial.eval point))
    (pointInside : inner.Contains point) (index : Nat) :
    RootAligned ((Model.overlapRefine cell.model) index) point (OwnerTraceReadings.ownerName
      traced.finishOwner) := by
  let route := Route.build (clearance.restrict cell.geometry.refines)
    inner.anchor point inner.contains_anchor pointInside
  let prepared := CoveredTracedPath.build route.path route.within cell.traced.finishOwner
  intro count patch patchInside sample roots otherIndex
  exact cell.continuedAligned differential prepared index patch patchInside sample
    ((compareContinuedTrace cell prefixInside degreePositive reference prepared traced
      inside frame).trans roots) otherIndex

/-- The fixed cell polynomial and the actual endpoint neighborhood agree at independently requested indices beyond the
fixed two-step cocycle floor. -/
theorem trace_nearest (cell : TransportedCell bounds entered.finishOwner inner)
    (prefixInside : InBox box prefixPath)
    (differential : Differential genus)
    (degreePositive : 0 < curve.polynomial.natDegree)
    (reference : WindingOneLoop curve.polynomial start) (traced : PreparedPathTrace.TracedPath path
      source)
    (inside : InBox box path) (frame : OwnerFrame (curve.polynomial.eval point))
    (pointInside : inner.Contains point) {count : Nat} (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced
      count)
    (leftIndex rightIndex : Nat) :
    Basic.normSq ((cell.model.refine (leftIndex + 2)).value.eval point -
      (neighborhood.patch.base.refine (rightIndex + 2)).value.eval point) ≤
    Basic.normSq ((cell.model.refine (leftIndex + 2)).value.eval point +
      (neighborhood.patch.base.refine (rightIndex + 2)).value.eval point) := by
  let sample := ContinuedNeighborhood.Point.acquire neighborhood.patch point neighborhood.center_inside
  exact trace_aligned cell prefixInside differential degreePositive reference traced inside
    frame pointInside leftIndex neighborhood.patch
    neighborhood.center_inside sample (neighborhood.pointEquivalent sample) rightIndex

/-- A shared edge beginning anywhere in the cell has the actual unflipped transition. Generated caches use pointwise
semantic equations; no root transport, auxiliary preparation, or classification runs in this value. -/
def traceTransition (cell : TransportedCell bounds entered.finishOwner inner)
    (prefixInside : InBox box prefixPath)
    (differential : Differential genus)
    (degreePositive : 0 < curve.polynomial.natDegree)
    (reference : WindingOneLoop curve.polynomial start) (traced : PreparedPathTrace.TracedPath path
      source)
    (inside : InBox box path) (frame : OwnerFrame (curve.polynomial.eval point))
    (pointInside : inner.Contains point) {count : Nat} (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced
      count)
    (leftIndex rightIndex : Nat)
    (left : InverseRootPolynomial.Model curve.polynomial inner) (right : InverseRootPolynomial.Model curve.polynomial
      neighborhood.patch.base.box)
    (leftEq : left.value.eval point = (cell.model.refine (leftIndex + 2)).value.eval point)
    (rightEq : right.value.eval point = (neighborhood.patch.base.refine (rightIndex + 2)).value.eval point)
    (finish : InverseRootPolynomial.Gaussian) (leftFinish : inner.Contains finish) (rightFinish :
      neighborhood.patch.box.Contains finish) :
    InverseModelEdgeTransition.EdgeTransition left right point finish where
  leftStart := pointInside
  leftFinish := leftFinish
  rightStart := neighborhood.patch.box_refines.contains neighborhood.center_inside
  rightFinish := neighborhood.patch.box_refines.contains rightFinish
  sample :=
    let first := left.value.eval point
    let second := right.value.eval point
    ⟨first, rfl, second, rfl, ⟨false, second, rfl, by
      dsimp only [first, second]
      rw [leftEq, rightEq]
      have scalar := trace_nearest cell prefixInside differential degreePositive reference
        traced inside frame pointInside neighborhood leftIndex rightIndex
      simpa only [Basic.normSq_eq_canonical] using scalar⟩⟩

/-- Bound two retained primitive increments using the actual source-to-anchor trace and the original odd-power weight.

Both original models, coefficient caches and independent indices remain in
this comparison. The unflipped transition is certified from the retained
source, prefix and winding reference, with no new root acquisition.
-/
theorem trace_primitive_increment_le (cell : TransportedCell bounds entered.finishOwner inner)
    (prefixInside : InBox box prefixPath) (differential : Differential genus)
    (degreePositive : 0 < curve.polynomial.natDegree)
    (reference : WindingOneLoop curve.polynomial start) (traced : TracedPath path source)
    (inside : InBox box path) (frame : OwnerFrame (curve.polynomial.eval point))
    (pointInside : inner.Contains point) {count : Nat}
    (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced count)
    (leftIndex rightIndex : Nat) {numerator coefficient : InverseRootPolynomial.Polynomial}
    {pairs : optParam Nat 0} (first : DensePrimitive coefficient inner)
    (firstEq : ∀ query, coefficient.eval query = match (generalizing := false) pairs with
      | 0 => numerator.eval query * (cell.model.refine (leftIndex + 2)).value.eval query
      | remaining + 1 => numerator.eval query *
          (cell.model.refine (leftIndex + 2)).value.eval query ^ (2 * (remaining + 1) + 1))
    (second : PrimitiveModel neighborhood.patch (rightIndex + 2) numerator pairs)
    (overlap : PrimitiveOverlapBounds (clearance.restrict cell.geometry.refines) numerator)
    (finish : InverseRootPolynomial.Gaussian) (leftFinish : inner.Contains finish)
    (rightFinish : neighborhood.patch.box.Contains finish) :
    Basic.normSq ((first.value.eval finish - first.value.eval point) -
      (second.primitive.value.eval finish - second.primitive.value.eval point)) ≤
      12 * ((cell.model.refine (leftIndex + 2)).bound +
        (neighborhood.patch.base.refine (rightIndex + 2)).bound) *
          overlap.weight pairs * Basic.normSq (finish - point) := by
  let edge := cell.traceTransition prefixInside differential degreePositive reference traced inside frame pointInside
    neighborhood leftIndex rightIndex (cell.model.refine (leftIndex + 2))
    (neighborhood.patch.base.refine (rightIndex + 2)) rfl rfl finish leftFinish rightFinish
  have estimate := PrimitiveEdgeComparison.EdgeTransition.primitive_increment_le edge overlap first
    (second.primitive.onBox neighborhood.patch.base.box) (pairs := pairs) firstEq
    (fun query => by
      cases pairs with
      | zero => exact second.coefficient_eq query
      | succ remaining => exact second.coefficient_eq query)
    (first := 1) (last := 0) ⟨by decide, le_rfl⟩ ⟨le_rfl, by decide⟩
  have sign : edge.sign = 1 := rfl
  rw [sign, Data.Gaussian.Basic.one_mul, InverseModelEdgeTransition.line_one, InverseModelEdgeTransition.line_zero]
    at estimate
  have scalar := estimate.trans_eq (by rw [(show (1 : Fraction.Rational) - 0 = 1 from by decide), one_pow,
    Fraction.Field.mul_one_direct])
  simpa only [Basic.normSq_eq_canonical, Polynomial.Dense.Gaussian.Primitive.Certificate.DensePrimitive.onBox]
    using scalar

/-- One actual accuracy request pays the primitive comparison at two independently retained later indices.

Both later-floor inequalities refer to the same request. The original
quarter-radius decrease and odd-power weight pay the bound; neither model,
primitive, source observation nor selection is reacquired.
-/
theorem trace_primitive_increment_lt (cell : TransportedCell bounds entered.finishOwner inner)
    (prefixInside : InBox box prefixPath) (differential : Differential genus)
    (degreePositive : 0 < curve.polynomial.natDegree)
    (reference : WindingOneLoop curve.polynomial start) (traced : TracedPath path source)
    (inside : InBox box path) (frame : OwnerFrame (curve.polynomial.eval point))
    (pointInside : inner.Contains point) {count : Nat}
    (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced count)
    {numerator coefficient : InverseRootPolynomial.Polynomial} {pairs : optParam Nat 0}
    {overlap : PrimitiveOverlapBounds (clearance.restrict cell.geometry.refines) numerator}
    {finish : InverseRootPolynomial.Gaussian} {target : InverseRootPolynomial.Coordinate}
    (request : PrimitiveEdgeAccuracy overlap cell.model neighborhood.patch.base.model point finish target pairs)
    (leftIndex rightIndex : Nat) (leftLater : request.index ≤ leftIndex) (rightLater : request.index ≤ rightIndex)
    (first : DensePrimitive coefficient inner)
    (firstEq : ∀ query, coefficient.eval query = match (generalizing := false) pairs with
      | 0 => numerator.eval query * (cell.model.refine (leftIndex + 2)).value.eval query
      | remaining + 1 => numerator.eval query *
          (cell.model.refine (leftIndex + 2)).value.eval query ^ (2 * (remaining + 1) + 1))
    (second : PrimitiveModel neighborhood.patch (rightIndex + 2) numerator pairs)
    (leftFinish : inner.Contains finish) (rightFinish : neighborhood.patch.box.Contains finish) :
    Basic.normSq ((first.value.eval finish - first.value.eval point) -
      (second.primitive.value.eval finish - second.primitive.value.eval point)) < target := by
  have leftDecrease : (cell.model.refine (leftIndex + 2)).bound ≤
      (cell.model.refine request.index).bound := by
    rw [Model.refine_bound, Model.refine_bound]
    exact quarterRadius_antitone cell.model.bound_nonnegative (leftLater.trans (Nat.le_add_right _ _))
  have rightDecrease : (neighborhood.patch.base.refine (rightIndex + 2)).bound ≤
      (neighborhood.patch.base.refine request.index).bound := by
    rw [SeededNeighborhood.refine, SeededNeighborhood.refine, Model.refine_bound, Model.refine_bound]
    exact quarterRadius_antitone neighborhood.patch.base.model.bound_nonnegative
      (rightLater.trans (Nat.le_add_right _ _))
  have bound := trace_primitive_increment_le cell prefixInside differential degreePositive reference traced inside
    frame pointInside neighborhood leftIndex rightIndex first firstEq second overlap finish leftFinish rightFinish
  simp only [Basic.normSq_eq_canonical, SeededNeighborhood.refine] at bound
  rw [Basic.normSq_eq_canonical]
  apply bound.trans_lt
  apply lt_of_le_of_lt _ request.refined_scale_lt
  exact Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct leftDecrease rightDecrease) (by decide)) (overlap.weight_nonnegative pairs))
    (Data.Gaussian.Basic.Canonical.normSq_nonneg (finish - point))

/-- Two retained cells transported from the same actual source have the unflipped overlap reading.

The original source-to-anchor prefix and a common proof-only contained
route compare both retained models through the same actual endpoint
neighborhood at their independent indices.
-/
theorem cells_nearest {leftBox rightBox : InverseRootPolynomial.Box}
    (left : TransportedCell bounds entered.finishOwner leftBox)
    (right : TransportedCell bounds entered.finishOwner rightBox)
    (prefixInside : InBox box prefixPath)
    (differential : Differential genus) (degreePositive : 0 < curve.polynomial.natDegree)
    (reference : WindingOneLoop curve.polynomial start)
    {point : InverseRootPolynomial.Gaussian}
    (leftInside : leftBox.Contains point) (rightInside : rightBox.Contains point) (leftIndex rightIndex : Nat) :
    Basic.normSq ((left.model.refine (leftIndex + 2)).value.eval point - (right.model.refine
      (rightIndex + 2)).value.eval point) ≤
      Basic.normSq ((left.model.refine (leftIndex + 2)).value.eval point +
        (right.model.refine (rightIndex + 2)).value.eval point) := by
  let route := Route.build clearance start point prefixInside.start
    (left.geometry.refines.contains leftInside)
  let traced := TracedPath.build route.path route.within source
  have inside := InBox.ofWithin route.path route.within prefixInside.start
  let frame := OwnerFrame.build traced.finishOwner.parameterNonzero
  let neighborhood := TracedPrimitiveNeighborhood.Neighborhood.build traced 0
  have first := left.trace_nearest (entered := entered) prefixInside differential degreePositive reference
    traced inside frame leftInside neighborhood leftIndex 0
  have second := right.trace_nearest (entered := entered) prefixInside differential degreePositive reference
    traced inside frame rightInside neighborhood rightIndex 0
  let reversed : InverseModelOverlap.SignAlignment ((right.model.refine (rightIndex + 2)).value.eval point)
      ((neighborhood.patch.base.refine 2).value.eval point) :=
    ⟨false, (neighborhood.patch.base.refine 2).value.eval point, rfl, by
      simpa only [Basic.normSq_eq_canonical] using second⟩
  have back : Basic.normSq
      ((neighborhood.patch.base.refine 2).value.eval point - (right.model.refine (rightIndex + 2)).value.eval point) ≤
      Basic.normSq
      ((neighborhood.patch.base.refine 2).value.eval point + (right.model.refine (rightIndex + 2)).value.eval point) :=
        by
    have scalar := (SignAlignment.reverse reversed).nearest
    dsimp only [SignAlignment.reverse, reversed] at scalar
    simp only [Basic.normSq_eq_canonical] at scalar ⊢
    exact scalar
  have scalar := OverlapReady.nearest_trans
    ((Model.overlapRefine left.model) leftIndex)
    ((Model.overlapRefine neighborhood.patch.base.model) 0)
    ((Model.overlapRefine right.model) rightIndex) leftInside
    (neighborhood.patch.box_refines.contains neighborhood.center_inside) rightInside
    (by simpa only [SeededNeighborhood.refine, Model.overlapRefine] using first)
    (by simpa only [SeededNeighborhood.refine, Model.overlapRefine] using back)
  simpa only [SeededNeighborhood.refine, Model.overlapRefine] using scalar

end

end Purelib.Riemann.Normalization.TransportedFaceInverseModels.TransportedCell

namespace Purelib.Riemann.Meshes.RectangularFaceModels.RectangularPatch

open Purelib
open Purelib.Data.Gaussian.Norm
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.RectangularSheetGauge
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseModelOverlap
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Polynomial.Geometry.ClearPath (InBox)

variable {genus : Nat} {curve : HyperellipticCurve genus} {box : Geometry.Rational.Box}
    {clearance : Clearance curve.polynomial box} {bounds : Bounds clearance}
    {start : Data.Gaussian.Basic.Canonical} {source : Owner (curve.polynomial.eval start)}
    {prefixAmbient : Geometry.Rational.Box}
    {prefixPath : Polynomial.Geometry.ClearPath curve.polynomial prefixAmbient start box.anchor}
    {entered : TracedPath prefixPath source}
    {columns rows : Nat} {geometry : Geometry columns rows}

/-- The stored horizontal transition, not just a freshly recomputed bit, is unflipped on the common physical occurrence.

Both adjacent cells read the shared physical grid vertex. Their retained nearestness certificate selects the unflipped
horizontal transition stored by the patch. -/
theorem horizontal_false (patch : RectangularPatch bounds entered.finishOwner
  geometry)
    (prefixInside : InBox box prefixPath) (differential : Differential genus)
    (degreePositive : 0 < curve.polynomial.natDegree) (reference : WindingOneLoop curve.polynomial start)
    (column : Fin columns) (row : Fin (rows + 1)) :
    patch.sheets.transitions.horizontal column row = false := by
  let point := geometry.vertex column.castSucc.succ row.castSucc
  have nearest : Basic.normSq ((patch.models.ready column.castSucc row).model.value.eval
    point -
      (patch.models.ready column.succ row).model.value.eval point) ≤
    Basic.normSq ((patch.models.ready column.castSucc row).model.value.eval point +
      (patch.models.ready column.succ row).model.value.eval point) := by
    rw [patch.value_eq, patch.value_eq]
    exact TransportedCell.cells_nearest (entered := entered) _ _ prefixInside differential
      degreePositive reference
      (geometry.lowerRight_mem column.castSucc row)
      (geometry.lowerLeft_mem column.succ row) 0 0
  rw [patch.sheets.transitions.horizontal_eq]
  change (SignAlignment.build ((patch.models.ready column.castSucc row).model.value.eval point)
    ((patch.models.ready column.succ row).model.value.eval point)).flip = false
  unfold SignAlignment.build
  simp only [Basic.normSq_eq_canonical] at nearest
  rw [dif_pos nearest]

/-- The same identification holds for vertical transitions, including those not used by the spanning-tree gauge
constructor.

The shared grid vertex identifies the two retained cell models. Their actual nearestness certificate selects the
unflipped stored vertical transition. -/
theorem vertical_false (patch : RectangularPatch bounds entered.finishOwner
  geometry)
    (prefixInside : InBox box prefixPath) (differential : Differential genus)
    (degreePositive : 0 < curve.polynomial.natDegree) (reference : WindingOneLoop curve.polynomial start)
    (column : Fin (columns + 1)) (row : Fin rows) :
    patch.sheets.transitions.vertical column row = false := by
  let point := geometry.vertex column.castSucc row.castSucc.succ
  have nearest : Basic.normSq ((patch.models.ready column row.castSucc).model.value.eval
    point -
      (patch.models.ready column row.succ).model.value.eval point) ≤
    Basic.normSq ((patch.models.ready column row.castSucc).model.value.eval point +
      (patch.models.ready column row.succ).model.value.eval point) := by
    rw [patch.value_eq, patch.value_eq]
    exact TransportedCell.cells_nearest (entered := entered) _ _ prefixInside differential
      degreePositive reference
      (geometry.upperLeft_mem column row.castSucc)
      (geometry.lowerLeft_mem column row.succ) 0 0
  rw [patch.sheets.transitions.vertical_eq]
  change (SignAlignment.build ((patch.models.ready column row.castSucc).model.value.eval point)
    ((patch.models.ready column row.succ).model.value.eval point)).flip = false
  unfold SignAlignment.build
  simp only [Basic.normSq_eq_canonical] at nearest
  rw [dif_pos nearest]

/-- Every checked gauge with the retained origin agrees with the actual source occurrence throughout the rectangle. No
canonical scan equality is required, and zero-row or zero-column grids are covered by the same proof.

Fixed-bound finite induction follows the stored vertical transitions in the first column, then the stored horizontal
transitions in each row. The argument includes empty-row and empty-column rectangles. -/
theorem gauge_false (patch : RectangularPatch bounds entered.finishOwner geometry)
    (prefixInside : InBox box prefixPath) (differential : Differential genus)
    (degreePositive : 0 < curve.polynomial.natDegree) (reference : WindingOneLoop curve.polynomial start)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    patch.sheets.gauge.values column row = false := by
  have firstColumn (row : Fin (rows + 1)) : patch.sheets.gauge.values 0 row = false := by
    induction row using Data.Fin.induction with
    | zero => exact patch.origin
    | succ row ih =>
        rw [patch.sheets.gauge.vertical]
        change (patch.sheets.gauge.values 0 row.castSucc ^^ patch.sheets.transitions.vertical 0 row) = false
        rw [ih, vertical_false patch prefixInside differential degreePositive reference]
        rfl
  induction column using Data.Fin.induction with
  | zero => exact firstColumn row
  | succ column ih =>
      rw [patch.sheets.gauge.horizontal]
      change (patch.sheets.gauge.values column.castSucc row ^^ patch.sheets.transitions.horizontal column row) = false
      rw [ih, horizontal_false patch prefixInside differential degreePositive reference]
      rfl

/-- Every oriented request reads the actual transported model at every cell, not merely the origin. The equation remains
pointwise, so generated coefficient representations and noncanonical gauge caches are admissible.

The gauge equation is specialized to the displayed cell before applying the retained refinement readback. Every point
and refinement index uses the same transported cell cache. -/
theorem oriented_value (patch : RectangularPatch bounds entered.finishOwner
  geometry)
    (prefixInside : InBox box prefixPath) (differential : Differential genus)
    (degreePositive : 0 < curve.polynomial.natDegree) (reference : WindingOneLoop curve.polynomial start)
    (index : Nat) (column : Fin (columns + 1)) (row : Fin (rows
      + 1))
    (point : InverseRootPolynomial.Gaussian) :
    ((Transitions.oriented
      (patch.sheets.refine index).transitions (patch.sheets.refine index).gauge).ready column row).model.value.eval
        point =
      ((patch.transported.cell column row).model.refine (index + 2)).value.eval point := by
  rw [Transitions.oriented,
    Bank.orient_value]
  change RectangularSheetGauge.signedValue (patch.sheets.gauge.values column row)
    (((patch.models.refine index).ready column row).model.value.eval point) = _
  rw [gauge_false patch prefixInside differential degreePositive reference]
  exact patch.refine_value index column row point

end Purelib.Riemann.Meshes.RectangularFaceModels.RectangularPatch

end

end

public section

namespace Purelib.Riemann.Normalization.TransportedFaceInverseModels.TransportedCell

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached ParentReached)
open Purelib.Riemann.Comparison
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat
open Purelib.Polynomial.Geometry.ClearPath (InBox)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (DensePrimitive PrimitiveOverlapBounds)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.RegularFaceInverseModels (Clearance Bounds)
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.ClearBoxPaths (Route)
open Purelib.Riemann.Paths.ClearBoxPathWinding
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.RootContinuation.ClearBoxRootTransport
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {box inner prefixAmbient : Box}
    {clearance : Clearance curve.polynomial box} {bounds : Bounds clearance} {start : Gaussian}
    {source : Owner (curve.polynomial.eval start)}
    {prefixPath : Polynomial.Geometry.ClearPath curve.polynomial prefixAmbient start box.anchor}
    {entered : TracedPath prefixPath source}

/-- An Owner reached in the source clear box is aligned with the retained transported cell at its cocycle stage.

The actual source-to-anchor prefix fixes the cell's original anchor Owner.
The retained reachability path and winding potential derive the endpoint
comparison inside that same clear box.
-/
private theorem reached_aligned (cell : TransportedCell bounds entered.finishOwner inner)
    (prefixInside : InBox box prefixPath) (differential : Differential genus)
    (degreePositive : 0 < curve.polynomial.natDegree) (reference : WindingOneLoop curve.polynomial start)
    {point : InverseRootPolynomial.Gaussian} {owner :
      Owner (curve.polynomial.eval point)}
    (pointInside : inner.Contains point) (reached : Reached box source owner)
    (index : Nat) : RootAligned ((Model.overlapRefine cell.model) index) point
      (OwnerTraceReadings.ownerName owner) := by
  obtain ⟨ownerTrace, winding⟩ := reached
  let route := Route.build clearance start point prefixInside.start (cell.geometry.refines.contains pointInside)
  let traced := TracedPath.build route.path route.within source
  let frame := OwnerFrame.build owner.parameterNonzero
  have equivalent := TracedPath.equivalentOfOwnerPathSelections
    reference route.within traced ownerTrace frame
    (frame.select traced.finishOwner) (frame.select owner)
    ((Route.winding clearance degreePositive route prefixInside.start).trans winding.symm)
  intro count patch inside sample roots otherIndex
  exact cell.trace_aligned prefixInside differential degreePositive reference traced
    (InBox.ofWithin route.path route.within prefixInside.start) frame
      pointInside index
    patch inside sample (equivalent.trans roots) otherIndex

/-- Every rational query of an actual retained parent is aligned with its containing transported cell.

Reachability retains the inherited query owner and lineage witnesses.
The comparison is evaluated at the same point and cocycle index. -/
theorem prepared_query_aligned (cell : TransportedCell bounds entered.finishOwner inner)
    (prefixInside : InBox box prefixPath) (differential : Differential genus)
    (degreePositive : 0 < curve.polynomial.natDegree) (reference : WindingOneLoop curve.polynomial start)
    (parent : CenteredEdge curve
      differential)
    (reached : ParentReached box source parent)
    (fraction : InverseRootPolynomial.Coordinate) (fractionInside : 0 ≤ fraction ∧ fraction ≤ 1)
    (pointInside : inner.Contains (parent.edge.point fraction)) (index : Nat) :
    RootAligned ((Model.overlapRefine cell.model) index) (parent.edge.point fraction)
      (parent.edge.rootName fraction fractionInside) := by
  have pointEq : parent.edge.point fraction = parent.edge.segment.pointAt
      (PreparedSheetContinuation.parameterAt parent.edge.left parent.edge.request fraction) :=
    (PreparedSheetContinuation.pointAt_parameterAt parent.edge.segment parent.edge.within parent.edge.left
      parent.edge.request fraction).symm
  have initial : RootAligned ((Model.overlapRefine cell.model) index)
      (parent.edge.segment.pointAt (PreparedSheetContinuation.parameterAt parent.edge.left parent.edge.request
        fraction))
      (OwnerTraceReadings.ownerName (parent.edge.directQueryOwner fraction fractionInside)) :=
    reached_aligned cell prefixInside differential degreePositive reference (pointEq ▸
      pointInside) (reached.query_reached fraction fractionInside) index
  rw [pointEq, parent.edge.rootName_eq_directQueryOwnerRootName]
  intro count patch patchInside sample roots otherIndex
  exact initial patch patchInside sample roots otherIndex

/-- The actual uniform integration patch and the containing cell have the unflipped comparison.

The patch keeps its retained index, including zero or one. The cell
alone requires the fixed cocycle-accuracy floor. -/
theorem prepared_query_nearest (cell : TransportedCell bounds entered.finishOwner inner)
    (prefixInside : InBox box prefixPath) (differential : Differential genus)
    (degreePositive : 0 < curve.polynomial.natDegree) (reference : WindingOneLoop curve.polynomial start)
    (parent : CenteredEdge curve
      differential)
    (reached : ParentReached box source parent)
    (fraction : InverseRootPolynomial.Coordinate) (fractionInside : 0 ≤ fraction ∧ fraction ≤ 1)
    (pointInside : inner.Contains (parent.edge.point fraction)) (patch :
      PreparedPatch parent)
    (count leftIndex rightIndex : Nat) (patchInside : (patch.neighborhood count).box.Contains (parent.edge.point
      fraction)) :
    Basic.normSq ((cell.model.refine (leftIndex + 2)).value.eval (parent.edge.point
      fraction) -
      ((patch.neighborhood count).base.refine rightIndex).value.eval (parent.edge.point fraction)) ≤
    Basic.normSq ((cell.model.refine (leftIndex + 2)).value.eval (parent.edge.point
      fraction) +
      ((patch.neighborhood count).base.refine rightIndex).value.eval (parent.edge.point fraction)) := by
  let sample := ContinuedNeighborhood.Point.acquire (patch.neighborhood count) (parent.edge.point fraction) patchInside
  have aligned : RootAligned ((Model.overlapRefine cell.model) leftIndex) (parent.edge.point
    fraction)
      (parent.edge.rootName fraction fractionInside) :=
    prepared_query_aligned cell prefixInside differential degreePositive reference parent
      reached fraction fractionInside pointInside leftIndex
  exact PreparedPolynomialSheetReadings.nearest_at_index aligned pointInside (patch.neighborhood count) patchInside
    sample
    (patch.point_equivalent count fraction fractionInside patchInside sample) rightIndex

/-- Compare an odd-power cell primitive with the retained primitive on an actual prepared parent's patch.

Both actual primitives retain their numerator, pair count, indices and
endpoint containments. Operational root alignment at the first endpoint
fixes their sign relation, independently of how that endpoint was reached.
The same overlap weight pays both inverse residuals and the actual squared
endpoint movement.
-/
theorem prepared_subedge_primitive_increment_le
    {anchorOwner : Owner (curve.polynomial.eval box.anchor)}
    (cell : TransportedCell bounds anchorOwner inner) (differential : Differential genus)
    (parent : CenteredEdge curve
      differential)
    (firstFraction lastFraction : InverseRootPolynomial.Coordinate)
    (firstInside : 0 ≤ firstFraction ∧ firstFraction ≤ 1)
    (pointInside : inner.Contains (parent.edge.point firstFraction)) (patch :
      PreparedPatch parent)
    (count leftIndex rightIndex : Nat)
    (aligned : RootAligned ((Model.overlapRefine cell.model) leftIndex) (parent.edge.point firstFraction)
      (parent.edge.rootName firstFraction firstInside))
    {numerator coefficient : InverseRootPolynomial.Polynomial}
    {pairs : optParam Nat 0} (first : DensePrimitive coefficient inner)
    (firstEq : ∀ query, coefficient.eval query = match (generalizing := false) pairs with
      | 0 => numerator.eval query * (cell.model.refine (leftIndex + 2)).value.eval query
      | remaining + 1 => numerator.eval query *
          (cell.model.refine (leftIndex + 2)).value.eval query ^ (2 * (remaining + 1) + 1))
    (second : PrimitiveModel (patch.neighborhood count) rightIndex numerator pairs)
    (overlap : PrimitiveOverlapBounds (clearance.restrict cell.geometry.refines) numerator)
    (leftFinish : inner.Contains (parent.edge.point lastFraction))
    (rightStart : (patch.neighborhood count).box.Contains (parent.edge.point firstFraction))
    (rightFinish : (patch.neighborhood count).box.Contains (parent.edge.point lastFraction)) :
    Basic.normSq ((first.value.eval (parent.edge.point lastFraction) - first.value.eval
      (parent.edge.point firstFraction)) -
      (second.primitive.value.eval (parent.edge.point lastFraction) - second.primitive.value.eval (parent.edge.point
        firstFraction))) ≤
      12 * ((cell.model.refine (leftIndex + 2)).bound + ((patch.neighborhood count).base.refine rightIndex).bound) *
        overlap.weight pairs * Basic.normSq (parent.edge.point
          lastFraction - parent.edge.point firstFraction) := by
  let left := cell.model.refine (leftIndex + 2)
  let right := (patch.neighborhood count).base.refine rightIndex
  let sample := ContinuedNeighborhood.Point.acquire (patch.neighborhood count)
    (parent.edge.point firstFraction) rightStart
  have nearest : Basic.normSq ((cell.model.refine (leftIndex + 2)).value.eval (parent.edge.point firstFraction) -
      ((patch.neighborhood count).base.refine rightIndex).value.eval (parent.edge.point firstFraction)) ≤
      Basic.normSq ((cell.model.refine (leftIndex + 2)).value.eval (parent.edge.point firstFraction) +
        ((patch.neighborhood count).base.refine rightIndex).value.eval (parent.edge.point firstFraction)) := by
    exact PreparedPolynomialSheetReadings.nearest_at_index aligned pointInside
      (patch.neighborhood count) rightStart sample
      (patch.point_equivalent count firstFraction firstInside rightStart sample) rightIndex
  let edge : InverseModelEdgeTransition.EdgeTransition left right (parent.edge.point firstFraction) (parent.edge.point
    lastFraction) :=
    ⟨pointInside, leftFinish, (patch.neighborhood count).box_refines.contains rightStart,
      (patch.neighborhood count).box_refines.contains rightFinish,
      ⟨left.value.eval (parent.edge.point firstFraction), rfl, right.value.eval (parent.edge.point firstFraction), rfl,
        ⟨false, right.value.eval (parent.edge.point firstFraction), rfl,
          by
            simpa only [Basic.normSq_eq_canonical] using nearest⟩⟩⟩
  have estimate := PrimitiveEdgeComparison.EdgeTransition.primitive_increment_le (pairs := pairs)
    edge overlap first (second.primitive.onBox (patch.neighborhood count).base.box) firstEq
    (fun query => by
      cases pairs with
      | zero => exact second.coefficient_eq query
      | succ remaining => exact second.coefficient_eq query)
    (first := 1) (last := 0) ⟨by decide, le_rfl⟩ ⟨le_rfl, by decide⟩
  have sign : edge.sign = 1 := rfl
  rw [sign, Data.Gaussian.Basic.one_mul, InverseModelEdgeTransition.line_one, InverseModelEdgeTransition.line_zero]
    at estimate
  have unitDifference : (1 - 0 : InverseRootPolynomial.Coordinate) = 1 := by decide +kernel
  have scalar := estimate.trans_eq (by rw [unitDifference, one_pow, Fraction.Field.mul_one_direct])
  simpa only [Basic.normSq_eq_canonical,
    Polynomial.Dense.Gaussian.Primitive.Certificate.DensePrimitive.onBox] using scalar

end Purelib.Riemann.Normalization.TransportedFaceInverseModels.TransportedCell

end
