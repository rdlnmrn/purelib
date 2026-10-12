module
import Purelib.Data.Int.Arithmetic
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Scale
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Affine.Axis
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides
import Purelib.Polynomial.Dense.Gaussian.Path.Pair
import Purelib.Polynomial.Dense.Gaussian.Path.Segment
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Polynomial.Winding.Polygon.Subdivision
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
public import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.RootIsolation.Track.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.RootIsolation.Exact.Ownership.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Data.Gaussian.Field
import Purelib.RootIsolation.Residual.Global.Assignment
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.Exact.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

/-!
# Winding of actual prepared paths and branch-boundary nonreturn

Every accepted subdivision has exactly the Cauchy index of its original
clear segment.  This uses the actual retained request list and its dependent
endpoint thread, not a claim about a geometrically similar polygon.  The
four-side branch boundary consequently has raw winding four after automatic
trace preparation, and cannot return operationally to its initial square root.
-/

namespace Purelib.Riemann.Paths.PreparedPathWinding

open Purelib.Data

public section

namespace ClearSegment

open Purelib.Geometry.Rational.Affine (line)
open Purelib.Data.Gaussian.Cast (ofCoordinate_re ofCoordinate_im)
open Purelib.RootIsolation.Winding
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Polynomial.Geometry.ClearPath.ClearSegment (pointAt)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- The original cleared segment parameterization equals its affine line with the same start and displacement. -/
theorem pointAt_eq_line {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Purelib.Geometry.Rational.Box} {start finish :
  Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (parameter : Fraction.Rational) :
    segment.pointAt parameter = Affine.line start (finish - start) parameter := by
  apply Basic.ext <;>
    simp only [Geometry.ClearPath.ClearSegment.pointAt, Affine.line, Scale.scale_re, Scale.scale_im,
      Cast.ofCoordinate_re, Cast.ofCoordinate_im, Basic.add_re,
      Basic.add_im, Basic.mul_re,
      Basic.mul_im] <;> ring1

open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
/-- The raw integer winding of the polynomial along the original cleared segment. -/
@[expose] def rawWinding {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Purelib.Geometry.Rational.Box} {start finish :
  Basic.Canonical}
    (_segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : Int :=
  (Path.Segment.segment polynomial start finish).doubledWinding

/-- The original cleared segment's raw winding computed from its horizontal or vertical polynomial edge. -/
@[expose] def coordinateWinding {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
    Purelib.Geometry.Rational.Box} {start finish :
  Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : Int :=
  match segment with
  | .horizontal left right y _ _ _ _ _ => (Path.Box.Sides.horizontalEdge polynomial y left right).doubledWinding
  | .vertical x left right _ _ _ _ _ => (Path.Box.Sides.verticalEdge polynomial x left right).doubledWinding

/-- Affine-segment and axis-edge formulas give the same original cleared-segment winding. -/
theorem rawWinding_eq_coordinateWinding {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
    Purelib.Geometry.Rational.Box} {start
  finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : rawWinding segment = coordinateWinding
      segment := by
  cases segment with
  | horizontal left right y leftLower leftUpper _ _ clearance =>
      have nonzero := Geometry.ClearPath.ClearSegment.horizontal_eval_ne_zero clearance left leftLower leftUpper
      have formula := Winding.Polygon.Subdivision.segmentRaw_eq_ofLine polynomial (Cast.Imaginary.horizontalBase y)
        Constants.horizontalDirection left right
        (by simpa only [Affine.Axis.line_horizontal] using nonzero)
      simpa only [rawWinding, coordinateWinding, Path.Box.Sides.horizontalEdge, Affine.Axis.line_horizontal] using
        formula
  | vertical x left right leftLower leftUpper _ _ clearance =>
      have nonzero := Geometry.ClearPath.ClearSegment.vertical_eval_ne_zero clearance left leftLower leftUpper
      have formula := Winding.Polygon.Subdivision.segmentRaw_eq_ofLine polynomial (Cast.Winding.verticalBase x)
        Constants.imaginaryUnit left right
        (by simpa only [Affine.Axis.line_vertical] using nonzero)
      simpa only [rawWinding, coordinateWinding, Path.Box.Sides.verticalEdge, Affine.Axis.line_vertical] using formula

end ClearSegment

namespace ClearPath

open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
/-- Sum the original cleared segments' raw integer windings in path order.

The empty path contributes zero, and each step retains its original segment and exact tail. -/
@[expose] def rawWinding {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Purelib.Geometry.Rational.Box} :
    {start finish : Basic.Canonical} → Polynomial.Geometry.ClearPath polynomial ambient start finish → Int
  | _, _, .nil _ => 0
  | _, _, .cons head tail => PreparedPathWinding.ClearSegment.rawWinding head + rawWinding tail

end ClearPath

namespace Subdivision

open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint Owner Subdivision)
open Purelib.RootIsolation.Winding

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  {segment : ClearSegment polynomial ambient start finish} {within :
    segment.WithinAmbient}

open Purelib.Geometry.Rational in
/-- The ordered original subdivision request endpoints terminate at its exact stored endpoint. -/
theorem requests_terminal : ∀ {current : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current owner),
    Polygon.Chain.terminal (segment.pointAt current.parameter)
      (subdivision.requests.map fun request => segment.pointAt request.endpoint.parameter) =
        segment.pointAt subdivision.endpoint.parameter
  | _, _, .stop _ _ => rfl
  | _, _, .next _ _ _ _ _ _ remaining => requests_terminal remaining

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
/-- The original subdivision request polygon has the same raw winding as its unsplit affine polynomial edge.

Each retained request splits the original parameter interval, and finite Cauchy-index additivity combines the exact
remaining edges. -/
theorem requests_winding : ∀ {current : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current owner),
    Winding.Polygon.Basic.chainRaw polynomial (segment.pointAt current.parameter)
      (subdivision.requests.map fun request => segment.pointAt request.endpoint.parameter) =
        (Dense.Rational.Pair.Path.Basic.PolynomialEdge.ofLine polynomial start (finish - start)
          current.parameter subdivision.endpoint.parameter).doubledWinding
  | _, _, .stop _ _ => (Int.Arithmetic.sub_eq_zero_of_eq (Eq.refl _)).symm
  | current, _owner, .next _ _ request _cached _ordered _safe remaining => by
      have nonzero := segment.pointAt_eval_ne_zero current.parameter current.inside
      rw [PreparedPathWinding.ClearSegment.pointAt_eq_line segment] at nonzero
      have edge := Winding.Polygon.Subdivision.segmentRaw_eq_ofLine polynomial start (finish - start)
        current.parameter request.endpoint.parameter nonzero
      rw [← PreparedPathWinding.ClearSegment.pointAt_eq_line segment, ← PreparedPathWinding.ClearSegment.pointAt_eq_line
        segment] at edge
      change (Path.Segment.segment polynomial (segment.pointAt current.parameter)
        (segment.pointAt request.endpoint.parameter)).doubledWinding +
          Winding.Polygon.Basic.chainRaw polynomial (segment.pointAt request.endpoint.parameter)
            (remaining.requests.map fun next => segment.pointAt next.endpoint.parameter) = _
      rw [edge, requests_winding remaining]
      exact (Dense.Rational.CauchyIndex.Basic.cauchyIndex2_add _ _ _ _ _).symm

end Subdivision

namespace PreparedClearPathModels

open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.PreparedClearPathModels
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)

namespace CompleteSegment

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  {segment : ClearSegment polynomial ambient start finish} {within :
    segment.WithinAmbient}
  {owner : Owner (polynomial.eval start)}

open Purelib.Geometry.Rational in
open Purelib.Riemann.Paths in
/-- The original complete segment's moving request vertices terminate at its exact finish point. -/
theorem moving_terminal (prepared : CompleteSegment segment within owner) :
    Polygon.Chain.terminal start
      (PreparedPathTrace.CompleteSegment.movingVertices prepared) = finish := by
  have equality := PreparedPathWinding.Subdivision.requests_terminal prepared.subdivision
  rw [prepared.start_eq, prepared.finish_eq] at equality
  exact equality

open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- The original complete segment's moving request polygon has exactly the original segment's raw winding. -/
theorem moving_winding (prepared : CompleteSegment segment within owner) :
    Winding.Polygon.Basic.chainRaw polynomial start
      (PreparedPathTrace.CompleteSegment.movingVertices prepared) =
        PreparedPathWinding.ClearSegment.rawWinding segment := by
  have equality := PreparedPathWinding.Subdivision.requests_winding prepared.subdivision
  rw [prepared.start_eq, prepared.endpoint_eq] at equality
  exact equality

end CompleteSegment

namespace PreparedPath

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
/-- The original prepared path's concatenated moving vertices have exactly the raw winding of its cleared path.

The proof retains each segment's endpoint equation and combines the original finite chain windings in order. -/
theorem moving_winding {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Purelib.Geometry.Rational.Box} :
    ∀ {start finish : Basic.Canonical} {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
      {owner : Owner (polynomial.eval start)} (prepared : PreparedPath path owner),
      Winding.Polygon.Basic.chainRaw polynomial start
        (PreparedPathTrace.PreparedPath.movingVertices prepared) =
          PreparedPathWinding.ClearPath.rawWinding path
  | _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, .cons _ _ _ _ head tail => by
      change Winding.Polygon.Basic.chainRaw polynomial _
        (PreparedPathTrace.CompleteSegment.movingVertices head ++
          PreparedPathTrace.PreparedPath.movingVertices tail) = _
      rw [Winding.Polygon.Basic.chainRaw_append,
        CompleteSegment.moving_terminal head, CompleteSegment.moving_winding head,
        moving_winding tail]
      rfl

end PreparedPath

namespace TracedPath

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
/-- The retained traced path has exactly the raw winding of its original cleared path. -/
theorem winding_original {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Purelib.Geometry.Rational.Box} {start finish :
  Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} {owner : Owner (polynomial.eval start)}
    (traced : TracedPath path owner) :
    Winding.Polygon.Basic.chainRaw polynomial start traced.trace.get.vertices =
      PreparedPathWinding.ClearPath.rawWinding path :=
  traced.winding_eq.trans (PreparedPath.moving_winding traced.prepared)

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
/-- Odd original loop winding excludes equivalence of its initial and retained terminal root names. -/
theorem root_not_equivalent_of_original_odd {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
    Purelib.Geometry.Rational.Box} {base :
  Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath polynomial ambient base base} {owner : Owner (polynomial.eval base)}
    (traced : TracedPath path owner) (turns : Int)
    (odd : PreparedPathWinding.ClearPath.rawWinding path =
      4 * (2 * turns + 1)) :
    Equivalence.NamedEquivalent
      (OwnerTraceReadings.ownerName traced.finishOwner)
      (OwnerTraceReadings.ownerName owner) → False :=
  PreparedPathTrace.TracedPath.root_not_equivalent_of_odd
    traced turns ((PreparedPath.moving_winding traced.prepared).trans odd)

end TracedPath

end PreparedClearPathModels

namespace BranchCutLifts

open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts (ownerBoundaryPath)

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
open Purelib.RootIsolation in
/-- The original cleared boundary path of a winding-one isolation state has raw winding four. -/
theorem ownerBoundaryPath_rawWinding
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
      Purelib.Geometry.Rational.Box}
    (state : State.WindingOne.Basic.WindingOneState polynomial ambient) :
    PreparedPathWinding.ClearPath.rawWinding
      (BranchCutLifts.ownerBoundaryPath state) = 4 := by
  have equality : PreparedPathWinding.ClearPath.rawWinding
      (BranchCutLifts.ownerBoundaryPath state) =
        Winding.Box.Basic.quadrupledBoxWinding polynomial state.box := by
    unfold BranchCutLifts.ownerBoundaryPath
    simp only [PreparedPathWinding.ClearPath.rawWinding,
      PreparedPathWinding.ClearSegment.rawWinding_eq_coordinateWinding,
      PreparedPathWinding.ClearSegment.coordinateWinding]
    rw [Winding.Box.Basic.quadrupledBoxWinding_eq]
    ring1
  exact equality.trans state.rawWindingFour

end BranchCutLifts

namespace TracedPath

open Purelib.Riemann.Paths.PreparedClearPathModels (GaussianPolynomial Box Owner)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
open Purelib.RootIsolation in
/-- Trace the original winding-one state's boundary starting at the supplied anchor root owner.

The retained boundary containment supplies the exact original path preparation and owner trace. -/
@[expose] def ownerBoundary {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Purelib.Geometry.Rational.Box}
    (state : State.WindingOne.Basic.WindingOneState polynomial ambient)
    (owner : Owner (polynomial.eval state.box.anchor)) :
    TracedPath (BranchCutLifts.ownerBoundaryPath state) owner :=
  PreparedPathTrace.TracedPath.build
    (BranchCutLifts.ownerBoundaryPath state)
    (BranchCutLifts.ownerBoundaryPath_withinAmbient state) owner

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
open Purelib.RootIsolation in
/-- Following the original winding-one boundary cannot return an equivalent root name. -/
theorem ownerBoundary_not_return {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Purelib.Geometry.Rational.Box}
    (state : State.WindingOne.Basic.WindingOneState polynomial ambient)
    (owner : Owner (polynomial.eval state.box.anchor)) :
    Equivalence.NamedEquivalent
      (OwnerTraceReadings.ownerName (ownerBoundary state owner).finishOwner)
      (OwnerTraceReadings.ownerName owner) → False := by
  apply PreparedPathWinding.PreparedClearPathModels.TracedPath.root_not_equivalent_of_original_odd
    (ownerBoundary state owner) 0
  change PreparedPathWinding.ClearPath.rawWinding
    (BranchCutLifts.ownerBoundaryPath state) = 4
  exact PreparedPathWinding.BranchCutLifts.ownerBoundaryPath_rawWinding state

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation in
/-- The original winding-one boundary swaps the two retained canonical root assignments.

An equal assignment would compare the original endpoint root names through their exact reconditioning bridges,
contradicting the boundary's odd winding. -/
theorem ownerBoundary_assignment_swaps {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Purelib.Geometry.Rational.Box}
    (state : State.WindingOne.Basic.WindingOneState polynomial ambient)
    (owner : Owner (polynomial.eval state.box.anchor)) :
    (SquareRootReconditioning.assignment owner.parameterNonzero
      (ownerBoundary state owner).finishOwner).owner.owner =
        BranchCutLifts.otherSheet
          (SquareRootReconditioning.assignment owner.parameterNonzero owner).owner.owner := by
  let finish := (ownerBoundary state owner).finishOwner
  let firstIndex : Fin 2 := (SquareRootReconditioning.assignment owner.parameterNonzero owner).owner.owner
  let lastIndex : Fin 2 := (SquareRootReconditioning.assignment owner.parameterNonzero finish).owner.owner
  have different : lastIndex ≠ firstIndex := by
    intro equal
    have freshEqual : SquareRootReconditioning.freshOwner owner.parameterNonzero finish =
        SquareRootReconditioning.freshOwner owner.parameterNonzero owner := by
      rw [SquareRootReconditioning.freshOwner_eq_canonicalOwner,
        SquareRootReconditioning.freshOwner_eq_canonicalOwner]
      exact congrArg (SquareRootReconditioning.canonicalOwner owner.parameterNonzero) equal
    let firstEquivalent := SquareRootTrackEquivalence.rootEquivalent_of_bridge
      owner.parameterNonzero owner (SquareRootReconditioning.bridge owner.parameterNonzero owner)
    let lastEquivalent := SquareRootTrackEquivalence.rootEquivalent_of_bridge
      owner.parameterNonzero finish (SquareRootReconditioning.bridge owner.parameterNonzero finish)
    rw [freshEqual] at lastEquivalent
    exact ownerBoundary_not_return state owner
      (Equivalence.NamedEquivalent.trans lastEquivalent firstEquivalent.symm)
  have valueDifferent : lastIndex.val ≠ firstIndex.val := by
    intro equal
    exact different (Fin.ext equal)
  apply Fin.ext
  change lastIndex.val = 1 - firstIndex.val
  have firstBound : firstIndex.val < 2 := firstIndex.isLt
  have lastBound : lastIndex.val < 2 := lastIndex.isLt
  omega

end TracedPath

end

end Purelib.Riemann.Paths.PreparedPathWinding
