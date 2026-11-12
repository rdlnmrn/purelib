module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.FineOrigin
public import Purelib.Riemann.Integration.PreparedConstantModels.Query.Transport
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query
import Purelib.Curves.Legendre.Periods.Fibre

/-! # Direct query transport on retained global fine-source occurrences

The literal original SourceOrigin and whole centered-parent equality
transport a supplied direct Query to the same physical occurrence. Both
coordinate and sheet remain in the original lifted key. The original
query, source allocation, preparation and paid geometry stay unchanged.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources

open Purelib
open Purelib.Riemann.RootContinuation
open Purelib.Curves.Legendre.Periods
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Steps.Acquisition

variable {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
variable {firstFine : Input.Fine circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstFine.numerical.initial.lowerEndpoint}
variable {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint firstFine.numerical.initial.source
  sourceOwner}
variable {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
variable {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
variable {fourthFine : Input.Fine circuit.fourth}
variable {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
variable {frame : Paths.Frame parameter} {basis : Differential 1}
variable {modelCount floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage}
variable (sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
  (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution)

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Requested.SourceOrigin

variable {sources} {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    {sourceIndex : Fin (requested.shape.val.1 :: requested.shape.val.2).length}
    (retained : SourceOrigin requested sourceIndex)

/-- Exact equality of the original prepared query key and the same retained fine-occurrence key.

This proposition names the unchanged coordinate/sheet equation. Its exposed
body permits consumers to use the literal equality without expanding the
whole original source-request interface during declaration processing.
-/
@[expose] def QueryKeyEquality (fraction : Fraction.Rational) : Prop :=
    (⟨(requested.attempt.2.1.entry sourceIndex).preparation.cell.models.coordinate.point fraction,
      ((requested.shape.val.1 :: requested.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge.sheet⟩ :
        LiftedPoint 2) =
      ⟨retained.origin.parent.edge.point fraction, retained.origin.parent.edge.sheet⟩

/-- The literal old global model query and its SAME original fine parent have identical WHOLE lifted keys.

The original global preparation's own coordinate law and the retained
whole centered-parent equation derive both coordinate and sheet equality.
Local numerical models, source samples and factor channels remain distinct;
this geometric readback supplies no signed-root conclusion by itself.
-/
theorem queryKey_eq (fraction : Fraction.Rational) : QueryKeyEquality retained fraction :=
  congrArg₂ (fun coordinate sheet => (⟨coordinate, sheet⟩ : LiftedPoint 2))
    ((PreparedParent.coordinate_point_eq (parameter := parameter) (frame := frame) (basis := basis)
      (parent := (requested.shape.val.1 :: requested.shape.val.2)[sourceIndex.val]'sourceIndex.isLt)
      (requested.attempt.2.1.entry sourceIndex).preparation.cell.models.coordinate fraction).trans
      (congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => parent.edge.point fraction)
        (parent_eq (parameter := parameter) (frame := frame) (basis := basis) (modelCount := modelCount)
        (firstFine := firstFine) (secondFine := secondFine) (thirdFine := thirdFine) (fourthFine := fourthFine)
        (sources := sources) (requested := requested) (sourceIndex := sourceIndex) retained)).symm)
    (congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => parent.edge.sheet)
      (parent_eq (parameter := parameter) (frame := frame) (basis := basis) (modelCount := modelCount)
        (firstFine := firstFine) (secondFine := secondFine) (thirdFine := thirdFine) (fourthFine := fourthFine)
        (sources := sources) (requested := requested) (sourceIndex := sourceIndex) retained)).symm

/-- Reindex one whole actual global direct Query to its SAME retained original fine parent without rebuilding it. -/
@[expose] def directQuery (fraction : Fraction.Rational) (inside : FixedRootBoxPath.Inside fraction)
    (query : PreparedEdge.Query
      ((requested.shape.val.1 :: requested.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge fraction inside) :
    PreparedEdge.Query retained.origin.parent.edge fraction inside :=
  PreparedEdge.Query.castEdge (curve := Fibre.frameCurve frame) (differential := basis)
    (congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => parent.edge)
      (parent_eq (parameter := parameter) (frame := frame) (basis := basis) (modelCount := modelCount)
        (firstFine := firstFine) (secondFine := secondFine) (thirdFine := thirdFine) (fourthFine := fourthFine)
        (sources := sources) (requested := requested) (sourceIndex := sourceIndex) retained).symm)
    query

/-- Global-origin transport retains the SAME whole direct Query and complete original factory certificate. -/
theorem directQuery_heq (fraction : Fraction.Rational) (inside : FixedRootBoxPath.Inside fraction)
    (query : PreparedEdge.Query
      ((requested.shape.val.1 :: requested.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge fraction inside) :
    HEq (retained.directQuery fraction inside query) query :=
  PreparedEdge.Query.castEdge_heq (curve := Fibre.frameCurve frame) (differential := basis)
    (congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => parent.edge)
      (parent_eq (parameter := parameter) (frame := frame) (basis := basis) (modelCount := modelCount)
        (firstFine := firstFine) (secondFine := secondFine) (thirdFine := thirdFine) (fourthFine := fourthFine)
        (sources := sources) (requested := requested) (sourceIndex := sourceIndex) retained).symm)
    query

end Requested.SourceOrigin

end Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
