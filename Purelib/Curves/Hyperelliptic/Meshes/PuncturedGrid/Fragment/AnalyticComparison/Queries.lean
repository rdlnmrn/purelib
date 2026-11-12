module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison
public import Purelib.Riemann.Integration.PreparedConstantModels.Query
public import Purelib.Riemann.Paths.RectangularSegmentSplitting.ParameterLocation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Readings.UniformPreparedRequests.Query
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.CheckedPrimitiveNeighborhoods
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Fraction
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Geometry.Rational.Affine
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! # Actual interior query cuts in the same retained primitive fragment

A finite lookup reads one original analytic piece. Its sample-derived
transition and both primitive polynomials are unchanged. One genuinely new
original patch Point and its operational query comparison are retained;
no old query, source, frame, observation or path producer is rerun.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings (FragmentBounds)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Branches.RectangularSheetGauge
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentSplit)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Readings
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {differential : Differential genus}
variable {axes : PrimitiveAxes base.bank.grid} {parent : CenteredEdge curve differential}
variable {cuts : List Rational} {partition : AxisPartition 0 1 cuts}
variable {interval : PreparedAxisPartitions.Interval}
variable {fragment : RegularPrimitiveFragment axes parent partition interval}
variable {domains : FaceDomainBank frames base.faces.regulars} {count : Nat} {target : Rational}
variable {request : LocalRequest parent count target}
variable (assigned : SheetEntry fragment domains request)
variable {index : Nat}
variable (primitives : Primitives (Transitions.oriented (assigned.domain.patch.sheets.refine index).transitions
  (assigned.domain.patch.sheets.refine index).gauge) (PreparedPrimitiveSamples.differentialNumerator differential))
variable {time : Rational} {timeInside : 0 ≤ time ∧ time ≤ 1}
variable (query : PreparedEdge.Query parent.edge time timeInside)

namespace QueryCut

/-- The original parent's query lies in this SAME retained fragment's exact closed parameter interval. -/
@[expose] def InFragment : Prop := interval.lower ≤ time ∧ time ≤ interval.upper

/-- Normalize the original parent query within its actual retained fragment interval. -/
@[expose] def parameter : Rational := interval.fraction time

/-- A query in this original fragment gives a bounded fragment-local parameter. -/
theorem parameter_inside (inside : InFragment (interval := interval) (time := time)) :
    0 ≤ parameter (interval := interval) (time := time) ∧ parameter (interval := interval) (time := time) ≤ 1 :=
  interval.fraction_inside inside

/-- The same actual query point is the exact interpolation of the original fragment endpoints. -/
theorem query_point : parent.edge.point time =
    PreparedSegmentCuts.point fragment.located.first fragment.located.last
      (parameter (interval := interval) (time := time)) := by
  have first := (PreparedParentSplitting.prepared_point_eq parent interval.lower).symm.trans
    fragment.located.first_eq.symm
  have last := (PreparedParentSplitting.prepared_point_eq parent interval.upper).symm.trans
    fragment.located.last_eq.symm
  have normalized := congrArg
    (PreparedSegmentCuts.point (parent.edge.point 0) (parent.edge.point 1)) (interval.fraction_eq time).symm
  have affine := PreparedSegmentCuts.point_affine (parent.edge.point 0) (parent.edge.point 1)
    interval.lower interval.upper (parameter (interval := interval) (time := time))
  exact (PreparedParentSplitting.prepared_point_eq parent time).trans
    (normalized.trans (affine.trans (congrArg₂
      (fun a b => PreparedSegmentCuts.point a b (parameter (interval := interval) (time := time))) first last)))

include assigned in
/-- Derive original neighborhood containment without claiming the direct query Owner refines the uniform seed box. -/
theorem neighborhood_inside (inside : InFragment (interval := interval) (time := time)) :
    request.neighborhood.box.Contains (parent.edge.point time) := by
  have ends := AnalyticComparison.neighborhood_endpoints assigned
  have line := Box.contains_line ends.1 ends.2 (parameter_inside inside)
  have same := (query_point (fragment := fragment) (time := time)).trans
    (PreparedSegmentCuts.point_eq_line _ _ _)
  exact same.symm ▸ line

/-- Compare both actual query and uniform-patch Owners through the original common-seed sheet machinery. -/
def comparePoint (inside : request.neighborhood.box.Contains (parent.edge.point time))
    (point : ContinuedNeighborhood.Point request.neighborhood (parent.edge.point time)) :
    NamedEquivalent (ownerName query.owner) point.certificate.value.name :=
  NamedEquivalent.transport query.name_eq rfl
    (request.retainedQueryEquivalent time timeInside query rfl inside point)

/-- The SAME stored analytic-piece lookup on this original fragment and actual query. -/
@[expose] def Location : Type :=
  SegmentSplit.Located assigned.split (parameter (interval := interval) (time := time))

/-- Retain the lookup, original transition, one patch Point, its signed comparison and two exact polynomial values.

The original direct query and both primitive owners remain inputs. The
patch Point is genuinely new work because its uniform seed need not be the
prepared query seed; neither owner is replaced or inferred equal.
-/
@[expose] def Cache (inside : InFragment (interval := interval) (time := time)) : Type :=
  Σ located : {value : Location (time := time) assigned //
    value = assigned.split.locate (parameter (interval := interval) (time := time)) (parameter_inside inside)},
  Σ _transition : {value : AnalyticComparison.TransitionCache assigned located.val.piece located.val.member index //
    value = AnalyticComparison.buildPieceTransition assigned located.val.piece located.val.member index},
  Σ point : {value : ContinuedNeighborhood.Point request.neighborhood (parent.edge.point time) //
    value = ContinuedNeighborhood.Point.acquire request.neighborhood (parent.edge.point time)
      (neighborhood_inside assigned inside)},
  Σ _compared : {value : NamedEquivalent (ownerName query.owner) point.val.certificate.value.name //
    value = comparePoint query (neighborhood_inside assigned inside) point.val},
  {values : Canonical × Canonical // values =
    (primitives.value located.val.piece.column located.val.piece.row (parent.edge.point time),
      request.request.model.primitive.value.eval (parent.edge.point time))}

/-- Compute the new cut work once, after reading the SAME cached fragment and primitive banks. -/
def build (inside : InFragment (interval := interval) (time := time)) : Cache assigned primitives query inside :=
  let located := assigned.split.locate (parameter (interval := interval) (time := time)) (parameter_inside inside)
  let transition := AnalyticComparison.buildPieceTransition assigned located.piece located.member index
  let point := ContinuedNeighborhood.Point.acquire request.neighborhood (parent.edge.point time)
    (neighborhood_inside assigned inside)
  let compared := comparePoint query (neighborhood_inside assigned inside) point
  let values := (primitives.value located.piece.column located.piece.row (parent.edge.point time),
    request.request.model.primitive.value.eval (parent.edge.point time))
  ⟨⟨located, rfl⟩, ⟨transition, rfl⟩, ⟨point, rfl⟩, ⟨compared, rfl⟩, ⟨values, rfl⟩⟩

namespace Cache

variable {assigned primitives query} {inside : InFragment (interval := interval) (time := time)}
variable (retained : Cache assigned primitives query inside)

/-- Read the complete original selected piece lookup and its original membership. -/
@[expose] def location : Location (time := time) assigned := retained.1.val

/-- Read the SAME original sample-derived model transition with its entire factory certificate. -/
@[expose] def transition : AnalyticComparison.TransitionCache assigned retained.location.piece
    retained.location.member index := retained.2.1.val

/-- Read the whole once-built uniform-patch Point without replacing the distinct input query Owner. -/
@[expose] def point : ContinuedNeighborhood.Point request.neighborhood (parent.edge.point time) :=
  retained.2.2.1.val

/-- Read the actual operational query-to-patch comparison on both retained Owners. -/
@[expose] def compared : NamedEquivalent (ownerName query.owner) retained.point.certificate.value.name :=
  retained.2.2.2.1.val

/-- Read both exact finite polynomial evaluations cached once at the literal query point. -/
@[expose] def values : Canonical × Canonical := retained.2.2.2.2.val

/-- The lookup is the SAME original finite selector on the old split, not a new classification. -/
theorem location_eq : retained.location = assigned.split.locate
    (parameter (interval := interval) (time := time)) (parameter_inside inside) := retained.1.property

/-- The whole model-transition cache is its original single factory result. -/
theorem transition_eq : retained.transition =
    AnalyticComparison.buildPieceTransition assigned retained.location.piece retained.location.member index :=
  retained.2.1.property

/-- The retained new uniform-patch Point is the complete original acquisition result. -/
theorem point_eq : retained.point =
    ContinuedNeighborhood.Point.acquire request.neighborhood (parent.edge.point time)
    (neighborhood_inside assigned inside) := retained.2.2.1.property

/-- The actual signed relation is the original common-seed comparison on these SAME two Owners. -/
theorem compared_eq : retained.compared = comparePoint query (neighborhood_inside assigned inside) retained.point :=
  retained.2.2.2.1.property

/-- Both cached values are evaluations of the original two primitive polynomials at the actual query point. -/
theorem values_eq : retained.values =
    (primitives.value retained.location.piece.column retained.location.piece.row (parent.edge.point time),
      request.request.model.primitive.value.eval (parent.edge.point time)) := retained.2.2.2.2.property

/-- The selected-piece interpolation is the literal physical point owned by the retained direct query. -/
theorem query_point : Affine.line retained.location.piece.firstPoint
    (retained.location.piece.lastPoint - retained.location.piece.firstPoint) retained.location.fraction =
      parent.edge.point time :=
  (SegmentSplit.Located.point_eq retained.location).trans
    (QueryCut.query_point (fragment := fragment) (time := time)).symm

/-- Read the actual two-polynomial mismatch on the first oriented half of the selected original piece. -/
@[expose] def beforeError : Canonical :=
  (retained.values.1 - primitives.value retained.location.piece.column retained.location.piece.row
    retained.location.piece.firstPoint) -
  (retained.values.2 - request.request.model.primitive.value.eval retained.location.piece.firstPoint)

/-- Read the actual two-polynomial mismatch on the second oriented half of the SAME original piece. -/
@[expose] def afterError : Canonical :=
  (primitives.value retained.location.piece.column retained.location.piece.row retained.location.piece.lastPoint -
    retained.values.1) -
  (request.request.model.primitive.value.eval retained.location.piece.lastPoint - retained.values.2)

/-- Both partial mismatches telescope to the original full-piece mismatch; arbitrary primitive constants cancel. -/
theorem telescope : retained.beforeError + retained.afterError =
    (primitives.value retained.location.piece.column retained.location.piece.row retained.location.piece.lastPoint -
      primitives.value retained.location.piece.column retained.location.piece.row retained.location.piece.firstPoint) -
    (request.request.model.primitive.value.eval retained.location.piece.lastPoint -
      request.request.model.primitive.value.eval retained.location.piece.firstPoint) := by
  have scalar (a b c d e f : Canonical) :
      ((b - a) - (e - d)) + ((c - b) - (f - e)) = (c - a) - (f - d) := by ring1
  exact scalar _ _ _ _ _ _

/-- The first partial mismatch pays both original residual bounds and its exact squared parameter width. -/
theorem before_le (bounds : FragmentBounds assigned.domain.patch differential) :
    normSq retained.beforeError ≤ AnalyticComparison.pieceCharge assigned bounds retained.location.piece index *
      retained.location.fraction ^ 2 := by
  have estimate := AnalyticComparison.piece_partial_increment_le assigned bounds retained.location.piece
    retained.location.member retained.transition primitives retained.location.fraction_inside
    (show (0 : Rational) ≤ 0 ∧ (0 : Rational) ≤ 1 by decide)
  rewrite [retained.query_point, InverseModelEdgeTransition.line_zero] at estimate
  have scalar : (retained.location.fraction - (0 : Rational)) ^ 2 = retained.location.fraction ^ 2 := by ring1
  have paid := estimate.trans_eq (congrArg
    (fun weight => AnalyticComparison.pieceCharge assigned bounds retained.location.piece index * weight) scalar)
  have values := retained.values_eq
  have firstValue := congrArg Prod.fst values
  have secondValue := congrArg Prod.snd values
  have errorEq : retained.beforeError =
      (primitives.value retained.location.piece.column retained.location.piece.row (parent.edge.point time) -
        primitives.value retained.location.piece.column retained.location.piece.row
          retained.location.piece.firstPoint) -
      (request.request.model.primitive.value.eval (parent.edge.point time) -
        request.request.model.primitive.value.eval retained.location.piece.firstPoint) :=
    congrArg₂ (fun a b =>
      (a - primitives.value retained.location.piece.column retained.location.piece.row
        retained.location.piece.firstPoint) -
      (b - request.request.model.primitive.value.eval retained.location.piece.firstPoint)) firstValue secondValue
  exact (congrArg (fun error => normSq error ≤
    AnalyticComparison.pieceCharge assigned bounds retained.location.piece index * retained.location.fraction ^ 2)
    errorEq.symm).mp paid

/-- The second partial mismatch pays the SAME original residual bounds and complementary oriented width. -/
theorem after_le (bounds : FragmentBounds assigned.domain.patch differential) :
    normSq retained.afterError ≤ AnalyticComparison.pieceCharge assigned bounds retained.location.piece index *
      (1 - retained.location.fraction) ^ 2 := by
  have estimate := AnalyticComparison.piece_partial_increment_le assigned bounds retained.location.piece
    retained.location.member retained.transition primitives
    (show (0 : Rational) ≤ 1 ∧ (1 : Rational) ≤ 1 by decide) retained.location.fraction_inside
  rewrite [InverseModelEdgeTransition.line_one, retained.query_point] at estimate
  have firstValue := congrArg Prod.fst retained.values_eq
  have secondValue := congrArg Prod.snd retained.values_eq
  have errorEq : retained.afterError =
      (primitives.value retained.location.piece.column retained.location.piece.row retained.location.piece.lastPoint -
        primitives.value retained.location.piece.column retained.location.piece.row (parent.edge.point time)) -
      (request.request.model.primitive.value.eval retained.location.piece.lastPoint -
        request.request.model.primitive.value.eval (parent.edge.point time)) :=
    congrArg₂ (fun a b =>
      (primitives.value retained.location.piece.column retained.location.piece.row
        retained.location.piece.lastPoint - a) -
      (request.request.model.primitive.value.eval retained.location.piece.lastPoint - b)) firstValue secondValue
  exact (congrArg (fun error => normSq error ≤
    AnalyticComparison.pieceCharge assigned bounds retained.location.piece index *
      (1 - retained.location.fraction) ^ 2) errorEq.symm).mp estimate

end Cache

/-- Finish the original query-cut cache with one supplied complete Point acquisition.

The lookup, transition, operational comparison and polynomial pair are
computed once. The original Point factory equality pays its existing cache
field; the returned subtype retains literal identity to the supplied Point.
No query, Point, source request or face acquisition is executed again.
-/
def ofPoint (inside : InFragment (interval := interval) (time := time))
    (point : ContinuedNeighborhood.Point request.neighborhood (parent.edge.point time))
    (factory : point = ContinuedNeighborhood.Point.acquire request.neighborhood (parent.edge.point time)
      (neighborhood_inside assigned inside)) :
    {retained : Cache assigned primitives query inside // retained.point = point} :=
  let located : Location (time := time) assigned :=
    assigned.split.locate (parameter (interval := interval) (time := time)) (parameter_inside inside)
  let transition : AnalyticComparison.TransitionCache assigned located.piece located.member index :=
    AnalyticComparison.buildPieceTransition assigned located.piece located.member index
  let compared : NamedEquivalent (ownerName query.owner) point.certificate.value.name :=
    comparePoint query (neighborhood_inside assigned inside) point
  let values : Canonical × Canonical :=
    (primitives.value located.piece.column located.piece.row (parent.edge.point time),
      request.request.model.primitive.value.eval (parent.edge.point time))
  let retained : Cache assigned primitives query inside :=
    ⟨⟨located, rfl⟩, ⟨transition, rfl⟩, ⟨point, factory⟩, ⟨compared, rfl⟩, ⟨values, rfl⟩⟩
  ⟨retained, rfl⟩

/-- Inspect this actual fragment and either retain its genuine query cut or the exact failed containment test. -/
def inspect : PSum (¬ InFragment (interval := interval) (time := time))
    (Σ inside : {_value : Unit // InFragment (interval := interval) (time := time)},
      Cache assigned primitives query inside.property) :=
  if inside : interval.lower ≤ time ∧ time ≤ interval.upper then
    .inr ⟨⟨(), inside⟩, build assigned primitives query inside⟩
  else .inl inside

end QueryCut
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry

end
