module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Children
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Restriction.Axis
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Uniform
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Uniform.Prefix
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Polynomial.Geometry.Grid.AxisWalks.Parameters
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Crop
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Approximation.Gaussian.Equivalence

/-! # Original strict-piece source cells on their retained axis words

The actual source cell's cached endpoint laws and original parent's axis
supply the geometric inputs. Only finite polynomial restrictions are new.
A supplied original complete PieceReadings answer can then be transported
without executing its query, selector, Entry or numerical preparation.
These are source-polynomial and same-observation certificates; attaching
the existing internal row traces to those models remains separate.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points.UniformPiece

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Face.Entries.FaceModels (Entry)
open Face.Periods (PeriodDomain)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets (UniformObservation)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.RectangularInverseModels (Bank)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentSplit)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.Polynomial.Geometry.Grid

universe u v

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {originalPath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets originalPath stage} {row : Row} {accuracy : AccuracyRequest}
    {prepared : PreparedParent patch count floor covered targets} {lower upper : Rational}
    {lowerInside : 0 ≤ lower ∧ lower ≤ 1} {upperInside : 0 ≤ upper ∧ upper ≤ 1}
    {operation : PreparedSubdivisionTrace.PreparedTraceBudget.Trace.CropComparisons
      parent lower upper lowerInside upperInside}
    {cropped : Crop (frame := frame) (basis := basis) (row := row)
      prepared lower upper lowerInside upperInside operation}
    {comparisonRequest requested : AccuracyRequest}
    {observed : cropped.Observation (accuracy := accuracy) comparisonRequest}
    {points : observed.Points requested}
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {bank : BranchCellBank (Fibre.frameCurve frame) branches higher}
    {rootFrames : RootFrames bank.grid} {face : RegularFace bank}
    {shared : Face.DomainBanks.FaceDomains rootFrames face}
    {firstInside : face.cell.box.Contains (parent.edge.point lower)}
    {acquired : Entry.Acquisition shared.models firstInside points.samples.1.val.owner}
    {domain : PeriodDomain shared.models acquired.entry.sheet}
    {split : SegmentSplit domain.cuts (parent.edge.point lower) (parent.edge.point upper)}
    {position : Fin split.pieces.length}
    {channel : Fin 6} {targetIndex exponent : Nat}
    {oldBank : Bank (Paths.polynomial parameter) domain.geometry} {numerator targetSource : Polynomial}
    {gap : AccuracyRequest}
    (data : UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (position := position)
      channel oldBank numerator targetSource exponent targetIndex gap)

variable {AlphaH AlphaV : Type u} {keyH : AlphaH → Rational} {keyV : AlphaV → Rational}
    {intervalsH : List (ClearGrid.Interval keyH)} {intervalsV : List (ClearGrid.Interval keyV)}
    (horizontal : AxisWalks.Walk intervalsH (auxiliaryPiece split position).firstPoint.re
      (auxiliaryPiece split position).lastPoint.re)
    (vertical : AxisWalks.Walk intervalsV (auxiliaryPiece split position).firstPoint.im
      (auxiliaryPiece split position).lastPoint.im)
    {Edge : Type} (horizontalSources verticalSources : List Edge) (coordinates : Edge → Canonical × Canonical)

/-- Restrict the SAME actual source cell on both retained axis-word roles and derive exact integral reassembly.

Both endpoint identities and the source axis are derived internally from
its original caches. The original source-edge lists and their complete
ordered coordinate readbacks remain supplied owners; no new query or
numerical bank is prepared, and no integral equality is an input.
-/
def withAxisRestrictions
    (horizontalCoordinates : horizontalSources.map coordinates = horizontal.steps.map (fun step =>
      ((⟨step.1, (auxiliaryPiece split position).firstPoint.im⟩ : Canonical),
        (⟨step.2, (auxiliaryPiece split position).firstPoint.im⟩ : Canonical))))
    (verticalCoordinates : verticalSources.map coordinates = vertical.steps.map (fun step =>
      ((⟨(auxiliaryPiece split position).lastPoint.re, step.1⟩ : Canonical),
        (⟨(auxiliaryPiece split position).lastPoint.re, step.2⟩ : Canonical))))
    {Result : Type v}
    (consume : Cell.Restriction.Axis.AxesConsumer data.source
      (auxiliaryPiece split position).firstPoint (auxiliaryPiece split position).lastPoint
      horizontal vertical horizontalSources verticalSources coordinates Result) : Result :=
  Cell.Restriction.Axis.withAxes data.source
    (auxiliaryPiece split position).firstPoint (auxiliaryPiece split position).lastPoint
    horizontal vertical horizontalSources verticalSources
    (piece_start (cropped := cropped) split position channel data.restricted)
    (piece_finish (cropped := cropped) split position channel data.restricted)
    coordinates horizontalCoordinates verticalCoordinates
    (piece_axis (cropped := cropped) (points := points) (shared := shared) (firstInside := firstInside)
      (acquired := acquired) (domain := domain) (split := split) position) consume

variable {Alpha : Type u} {key : Alpha → Rational} {intervals : List (ClearGrid.Interval key)}
    {first last : Rational} (walk : AxisWalks.Walk intervals first last)
    (sources : List Edge) (read : Edge → Rational × Rational)
    (cached : Cell.Restriction.Axis.Caches walk sources read data.source)
    (index : Fin sources.length) (different : first ≠ last)
    (sourceCoordinates : sources.map read = walk.steps)
    (input : Rational) (inputInside : 0 ≤ input ∧ input ≤ 1)

/-- The exact original PieceReadings owner at the mapped parameter of one retained axis restriction.

The complete original RootedQuery, prefix path and paired observations
remain in their original family. Entry evidence is local to the producer;
future-model selections remain in the supplied UniformPiece.requests.
-/
@[expose] def AxisQuery :=
  let interval := Cell.Restriction.Axis.interval walk read (sources[index.val]'index.isLt)
  let bounds := Cell.Restriction.Axis.inside walk sources read different sourceCoordinates index
  let inside := Cell.Restriction.parameter_inside bounds.1 bounds.2 inputInside
  PieceReadings (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (position := position)
    channel data.restricted data.target.model (Cell.Restriction.parameter interval.start interval.finish input) inside

/-- Retain the exact factory equation of the same supplied full original query answer. -/
@[expose] def AxisQueryFactory
    (original : AxisQuery data walk sources read index different sourceCoordinates input inputInside) : Prop :=
  let interval := Cell.Restriction.Axis.interval walk read (sources[index.val]'index.isLt)
  let bounds := Cell.Restriction.Axis.inside walk sources read different sourceCoordinates index
  let inside := Cell.Restriction.parameter_inside bounds.1 bounds.2 inputInside
  original = UniformPiece.query (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (position := position) data
    (Cell.Restriction.parameter interval.start interval.finish input) inside

/-- Transport one GIVEN complete original query answer to the same stored axis restriction.

The caller's complete answer and actual query factory equation are retained
before the generic same-observation operation. No original query is called
again. The child observation preserves its full original root name and
coefficient/reading caches; it does not assert agreement with a different
internal row model or normalize any primitive constants.
-/
def withRestrictedQuery {ambient : Box}
    (segment : ClearSegment (Fibre.frameCurve frame).polynomial ambient
      (Cell.Restriction.Axis.model walk sources read data.source cached index).start
      (Cell.Restriction.Axis.model walk sources read data.source cached index).finish)
    (original : AxisQuery data walk sources read index different sourceCoordinates input inputInside)
    (factory : AxisQueryFactory data walk sources read index different sourceCoordinates input inputInside original)
    {Result : Type v}
    (consume :
      (kept : AxisQuery data walk sources read index different sourceCoordinates input inputInside) →
      kept = original →
      AxisQueryFactory data walk sources read index different sourceCoordinates input inputInside kept →
      UniformObservation.AxisConsumer (lifted := auxiliaryLift parent (auxiliaryPiece split position))
        walk sources read cached index
        (BranchCutLifts.ClearSegment.liftOnSheet parent.edge.sheet segment) rfl input
        kept.2.2.1.val Result) : Result :=
  let childLifted := BranchCutLifts.ClearSegment.liftOnSheet parent.edge.sheet segment
  UniformObservation.withAxisRestriction (lifted := auxiliaryLift parent (auxiliaryPiece split position))
    walk sources read cached index childLifted rfl input
    original.2.2.1.val (consume original rfl factory)

/-- Derive the original source Point, face Entry and signed root evidence at one actual restricted query.

The supplied complete query and its factory precede the existing
same-observation restriction. Its retained prefix derives the Entry, while
exact point and root readbacks transport the SAME sample to the returned
observation. No query, Point acquisition, face selection or source model
is executed again; both the original differential and entered sheet remain
the supplied owners.
-/
def sourceQuery {ambient : Box}
    (segment : ClearSegment (Fibre.frameCurve frame).polynomial ambient
      (Cell.Restriction.Axis.model walk sources read data.source cached index).start
      (Cell.Restriction.Axis.model walk sources read data.source cached index).finish)
    (original : AxisQuery data walk sources read index different sourceCoordinates input inputInside)
    (factory : AxisQueryFactory data walk sources read index different sourceCoordinates input inputInside original) :
    Σ observed : UniformObservation (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
      (BranchCutLifts.ClearSegment.liftOnSheet parent.edge.sheet segment)
      (Cell.Restriction.Axis.model walk sources read data.source cached index) input,
    Σ sample : ContinuedNeighborhood.Point prepared.preparation.cell.patch observed.algebraic.point,
    Σ _entered : { entry : Entry shared.models observed.algebraic.point sample.owner //
      acquired.entry.sheet = entry.sheet },
    NamedEquivalent (ownerName sample.owner) observed.algebraic.sheetValue.value.name :=
  withRestrictedQuery data walk sources read cached index different sourceCoordinates input inputInside
    segment original factory
    (fun kept _keptEq _queryFactory _parentObservation observationEq _restriction restrictionEq restricted
      _restrictedEq _readingEq _errorEq pointEq rootEq _sheetValue _interpretation _asReading => by
      cases restrictionEq
      have point : restricted.algebraic.point = parent.edge.point
          (Cell.Restriction.parameter lower upper
            (Cell.Restriction.parameter (auxiliaryPiece split position).interval.lower
              (auxiliaryPiece split position).interval.upper
              (Cell.Restriction.parameter
                (Cell.Restriction.Axis.interval walk read (sources[index.val]'index.isLt)).start
                (Cell.Restriction.Axis.interval walk read (sources[index.val]'index.isLt)).finish input))) :=
        pointEq.trans ((congrArg (fun observed => observed.algebraic.point) observationEq).trans
          (PieceReadings.point_eq data kept))
      let sample := ContinuedNeighborhood.Point.castPoint point kept.1.sample
      let entered := castPointEntry point kept.1.sample (PieceReadings.entry data kept)
      have sheet : acquired.entry.sheet = entered.sheet :=
        ((castPointEntry_sheet point kept.1.sample (PieceReadings.entry data kept)).trans
          (PieceReadings.entry_sheet data kept)).symm
      have sampleName : ownerName sample.owner = ownerName kept.1.sample.owner :=
        ContinuedNeighborhood.Point.castPoint_name point kept.1.sample
      have observedName : restricted.algebraic.sheetValue.value.name =
          kept.2.2.1.val.algebraic.sheetValue.value.name :=
        rootEq.trans (congrArg (fun observed => observed.algebraic.sheetValue.value.name) observationEq)
      exact ⟨restricted, sample, ⟨entered, sheet⟩,
        NamedEquivalent.transport sampleName.symm observedName.symm (PieceReadings.roots data kept)⟩)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points.UniformPiece

end
