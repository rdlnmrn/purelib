module
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison

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
theorem prepared_within {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box} :
    ∀ {start finish : Basic.Canonical} {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
      {owner : Owner (polynomial.eval start)}, PreparedPath path owner → path.WithinAmbient
  | _, _, _, _, .nil point _ => .nil point
  | _, _, _, _, .cons _ _ _ within _ rest => .cons within (prepared_within rest)

end Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation

namespace Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation.EndpointsIn

open Purelib.Geometry.Rational in
/-- Concatenation preserves containment of every original centered-parent endpoint in the same box. -/
private theorem append {box : Purelib.Geometry.Rational.Box} {first second : List (CenteredEdge curve
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
private theorem subdivision_endpoints (curve : Basic.HyperellipticCurve genus) (differential :
  Differentials.Basic.Differential genus)
    {ambient : Purelib.Geometry.Rational.Box} {start finish : Basic.Canonical}
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
theorem prepared_endpoints (curve : Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential
  genus)
    (sheet : Fin 2) {ambient : Purelib.Geometry.Rational.Box} :
    ∀ {start finish : Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
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
  Purelib.Geometry.Rational.Box} :
    ∀ {start finish : Basic.Canonical} {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
      {owner : Owner (polynomial.eval start)} (_prepared : PreparedPath path owner),
      ambient.Contains start → ambient.Contains finish
  | _, _, _, _, .nil _ _, inside => inside
  | _, _, _, _, .cons head _ _ within _ rest, _ => by
      apply prepared_finish_inside rest
      have inside := head.pointAt_contains within 1 (by decide)
      rw [Geometry.ClearPath.ClearSegment.pointAt_one] at inside
      exact inside

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
open Purelib.Riemann.Topology in
/-- Continue a fixed inverse model's root alignment along an original primitive-covered traced path.

The exact centered parent chain, retained primitive cover and endpoint containment transport the initial alignment to
the original traced terminal owner. -/
theorem coveredTrace_aligned (curve : Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential
  genus)
    {box : Purelib.Geometry.Rational.Box} {start finish : Basic.Canonical} {path : Polynomial.Geometry.ClearPath
      curve.polynomial
      box start finish}
    {owner : Owner (curve.polynomial.eval start)} (prepared : CoveredTracedPath path owner)
    {model : OverlapReady curve.polynomial box} (initial : RootAligned model start (ownerName owner)) :
    RootAligned model finish (ownerName prepared.traced.finishOwner) := by
  let data := CenteredPathChain.ofPreparedPath curve differential 0 prepared.traced.prepared
  have roots := PreparedBankRootChains.preparedPathRootChain curve differential 0 prepared.traced.prepared
  have final : RootAligned model finish (ownerName (PreparedPathGluing.finishOwner prepared.traced.prepared)) :=
    alongChain data.chain.toDirectPathChain roots (PreparedCoveredParentLists.PrimitiveCover.coveredParents curve
      differential 0 0 prepared.cover)
      (prepared_endpoints curve differential 0 prepared.traced.prepared) initial
  intro count patch inside sample equivalent index
  apply final patch inside sample _ index
  rw [← prepared.traced.finishOwner_eq]
  exact equivalent

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
  Polynomial} {box inner : Purelib.Geometry.Rational.Box}
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
  {curve : Basic.HyperellipticCurve genus} {box inner : Purelib.Geometry.Rational.Box}
    {clearance : Clearance curve.polynomial box} {bounds : Bounds clearance}
    {source : Owner (curve.polynomial.eval box.anchor)} (cell : TransportedCell bounds source inner)
    (differential : Differentials.Basic.Differential genus) {finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial inner inner.anchor finish}
    (prepared : PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath path cell.traced.finishOwner)
      (index : Nat) :
    RootAligned ((PreparedPolynomialSheetPropagation.InverseRootPolynomial.Model.overlapRefine cell.model) index) finish
      (ownerName prepared.traced.finishOwner) :=
  Branches.ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation.coveredTrace_aligned curve differential
    prepared (cell.rootAligned index)

open Purelib.Riemann.Paths
/-- The transported cell model and terminal continued neighborhood choose compatible nearest signs at the original path
endpoint.

The original covered trace supplies root alignment, and its retained neighborhood reading supplies the exact comparison
of endpoint root names. -/
theorem continued_nearest {genus :
  Nat} {curve : Basic.HyperellipticCurve genus} {box inner : Purelib.Geometry.Rational.Box}
    {clearance : Clearance curve.polynomial box} {bounds : Bounds clearance}
    {source : Owner (curve.polynomial.eval box.anchor)} (cell : TransportedCell bounds source inner)
    (differential : Differentials.Basic.Differential genus) {point : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial inner inner.anchor point}
    (prepared : PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath path cell.traced.finishOwner)
      {count : Nat}
    (neighborhood : TracedPrimitiveNeighborhood.Neighborhood prepared.traced count) (leftIndex rightIndex : Nat) :
    Data.Gaussian.Norm.Basic.normSq
      ((cell.model.refine (leftIndex + 2)).value.eval point - (neighborhood.patch.base.refine (rightIndex +
        2)).value.eval point) ≤
    Data.Gaussian.Norm.Basic.normSq
      ((cell.model.refine (leftIndex + 2)).value.eval point + (neighborhood.patch.base.refine (rightIndex +
        2)).value.eval point) := by
  let sample := ContinuedNeighborhood.Point.acquire neighborhood.patch point neighborhood.center_inside
  exact cell.continuedAligned differential prepared leftIndex neighborhood.patch neighborhood.center_inside sample
    (neighborhood.pointEquivalent sample) rightIndex

/-- Build an unflipped edge transition between the transported cell model and its terminal continued neighborhood.

The supplied endpoint value equations identify the exact model refinements. Original cell and neighborhood containments
are retained, and continued nearestness certifies the unchanged second value. -/
def continuedTransition {genus : Nat}
  {curve : Basic.HyperellipticCurve genus} {box inner : Purelib.Geometry.Rational.Box}
    {clearance : Clearance curve.polynomial box} {bounds : Bounds clearance}
    {source : Owner (curve.polynomial.eval box.anchor)} (cell : TransportedCell bounds source inner)
    (differential : Differentials.Basic.Differential genus) {point : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial inner inner.anchor point}
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

end Purelib.Riemann.Normalization.TransportedFaceInverseModels.TransportedCell

end

end
