module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Polynomial.Rectangle.JoinedSampleBlocks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularSegmentRefinement
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CertifiedSideFragments
import Purelib.Approximation.Budget.RequestedLengthBudget
import Init.Data.Fin.Basic
import Init.GetElem
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularAxisParameterRange
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

public section

/-! Retain a complete certified fragment family and its computed source
path, area and aggregate error. Factories run only while filling the finite
banks; later comparisons read the cached family data. -/
section

open Purelib.Data.List

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CertifiedSideFragments
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Geometry
open Purelib.Geometry.Rectangle
open Purelib.Geometry.Rectangle.Partition
open Purelib.Integration.Path
open Purelib.Integration.Path.JoinedTrace
open Purelib.Integration.Polynomial.Rectangle
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths
open Purelib.Riemann.Periods
open Purelib.Riemann.Readings
open Purelib.Riemann.Readings.RectangularMatchedObservationSides
open Purelib.Topology.Polygon

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits (indexedEntry indexedEntry_member
  sourceSplit)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData sourceValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest (OwnerRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (OwnedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments (ownedValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence AllSurfacePreparation)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Paths.RectangularPairedSegments (PairedSegmentPiece)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison (SampledFragment
  interleaveFragments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (OwnedFragment fragmentBlockError
  fragmentBlockError_lt FragmentAreaBudget)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (sourceDensity)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea (traceDensity traceError)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters (sourceBlockParameters signedAxis
  signedInterval blockMidpoint)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights)

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Coordinate} {minimum
    stage fine index : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : PairedSourcePlan occurrence
    other target minimum}
  {evaluated :
    ParentEvaluation
    plan sample otherSample fine}
  {data : FirstData occurrence index}
    {otherData : SecondData occurrence
    other index}
  {Vertex : Type} {count : Nat}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies

/-- A certified sampled fragment on one original retained physical trace piece. -/
@[expose] def PieceFragmentType (values : Vertex → Stokes.PrimitivePoint) (traces : Fin (count + 1) →
  JoinedTrace.VertexTrace Vertex)
    (position : Fin (count + 1)) :=
  JoinedFragmentComparison.SampledFragment (evaluated := evaluated) (data := data) (otherData := otherData)
    (fun vertex => values ((traces position).indexed vertex))

/-- A certified sampled fragment on the actual owner junction between consecutive retained trace pieces. -/
@[expose] def JunctionFragmentType (values : Vertex → Stokes.PrimitivePoint) (traces : Fin (count + 1) →
  JoinedTrace.VertexTrace Vertex)
    (position : Fin count) :=
  JoinedFragmentComparison.SampledFragment (evaluated := evaluated) (data := data) (otherData := otherData)
    (JoinedSampleBlocks.JunctionValues values (traces position.castSucc) (traces position.succ))

/-- The complete dependent bank of sampled fragments on the original physical trace pieces. -/
@[expose] def PieceFragmentBank (values : Vertex → Stokes.PrimitivePoint) (traces : Fin (count + 1) →
  JoinedTrace.VertexTrace Vertex) :=
  Data.Vector.DependentVector (PieceFragmentType
    (evaluated := evaluated) (data := data) (otherData := otherData) values traces)

/-- The complete dependent bank of sampled fragments on the original inter-piece owner junctions. -/
@[expose] def JunctionFragmentBank (values : Vertex → Stokes.PrimitivePoint) (traces : Fin (count + 1) →
  JoinedTrace.VertexTrace Vertex) :=
  Data.Vector.DependentVector (JunctionFragmentType
    (evaluated := evaluated) (data := data) (otherData := otherData) values traces)

/-- Interleave the original cached piece and junction fragments in their physical traversal order. -/
@[expose] def fragmentFamilyOrder {values : Vertex → Stokes.PrimitivePoint} {traces : Fin (count + 1) →
  JoinedTrace.VertexTrace Vertex}
    (pieces : PieceFragmentBank (evaluated :=
      evaluated) (data := data) (otherData := otherData) values traces)
    (junctions : JunctionFragmentBank (evaluated :=
      evaluated) (data := data) (otherData := otherData) values traces) :
    List (PairedFragmentBlocks.OwnedFragment evaluated data otherData) :=
  JoinedFragmentComparison.interleaveFragments (fun position => (pieces.get position).fragment) (fun position =>
    (junctions.get position).fragment)

/-- The exact concatenated source increment list of the retained fragment family. -/
@[expose] def fragmentSourcePath (fragments : List (PairedFragmentBlocks.OwnedFragment evaluated data otherData)) : List
  PrimitivePoint :=
  ((fragments.map OwnedFragment.pair).map Prod.snd).flatten

set_option genInjectivity false in
/-- A retained parent and its selected source piece, shared by a physical piece and the owner junction immediately
following it. -/
structure LocatedSourceBlock (evaluated : PairedSourcePlan.ParentEvaluation plan sample otherSample fine)
    (vertical forward : Bool) (physical : PreparedAxisPartitions.Interval) where
  /-- The retained source parent and parameter block for this physical axis interval. -/ block :
    SourceBlockParameters evaluated vertical forward physical
  /-- The certified original split subinterval for the retained source parameter range. -/ located :
    RectangularSegmentRefinement.Subinterval
    (IndexedSourceSplits.sourceSplit evaluated block.index).split block.parameters.range

constructive_injectivity LocatedSourceBlock

/-- One retained and located source block for every original mesh interval on the selected oriented axis. -/
@[expose] def AxisSourceBank (evaluated : PairedSourcePlan.ParentEvaluation plan sample otherSample fine)
    {columns rows : Nat} {geometry : RectangularInverseModels.Geometry columns rows}
    {cuts : RectangularSegmentSplitting.GridCuts geometry} {meshBox : Rational.Box}
    (mesh : RectangularObservationMesh.ObservationMesh cuts meshBox) (vertical forward : Bool) :=
  Data.Vector.DependentVector (fun i : Fin (SourceIntervals.axisIntervals mesh vertical).length =>
    LocatedSourceBlock evaluated vertical forward
      ((SourceIntervals.axisIntervals mesh vertical)[i.val]'i.isLt))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.AxisSourceBank

/-- Transport only the axis tag; the retained source data are unchanged. -/
@[expose] def castAxis {columns rows : Nat} {geometry : RectangularInverseModels.Geometry columns rows}
    {cuts : RectangularSegmentSplitting.GridCuts geometry} {meshBox : Rational.Box}
    {mesh : RectangularObservationMesh.ObservationMesh cuts meshBox} {first last forward : Bool}
    (equal : first = last) (bank : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.AxisSourceBank
      evaluated mesh first forward) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.AxisSourceBank evaluated mesh last forward :=
      equal ▸ bank

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.AxisSourceBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.LocatedSourceBlock

/-- Build both original dependent fragment banks once and cache their ordered source path, area and aggregate error. -/
@[expose] def build
    {prepared : ExteriorProgram.AllSurfacePreparation regular domains differential} {previous : RegularMeshes.CommonCuts
      domains}
    (selected : SourceCuts prepared previous) (member : occurrence ∈ prepared.occurrences)
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) → RegularMeshes.Preflights domains sheet} {meshTarget :
      InverseRootPolynomial.Coordinate}
    (request : TwoSheetBilinearRequest.TwoSheetRequest
      (fun sheet => RegularMeshes.build domains selected.cuts sheet coarseDepth) fixed meshTarget)
    (sheet : Fin 2) (position : Fin base.faces.regulars.length)
    (evaluated : PairedSourcePlan.ParentEvaluation plan sample otherSample fine) (vertical forward : Bool)
    (physical : PreparedAxisPartitions.Interval)
    (present : physical ∈ SourceIntervals.axisIntervals ((request.entries.get sheet).meshes.entries.get position)
      vertical)
    (lower : SourceBlockParameters.signedAxis vertical forward occurrence.start ≤ SourceBlockParameters.blockMidpoint
      forward physical)
    (upper : SourceBlockParameters.blockMidpoint forward physical < SourceBlockParameters.signedAxis vertical forward
      occurrence.finish) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.LocatedSourceBlock evaluated vertical forward
      physical :=
  let block := SourceBlockParameters.sourceBlockParameters selected member request sheet position evaluated vertical
    forward physical present lower upper
  ⟨block, SourceBlockParameters.locate block selected member request sheet position present⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.LocatedSourceBlock

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies

/-- The original mesh axis interval expressed in the retained traversal orientation. -/
@[expose] def signedMeshSpan {columns rows : Nat} {geometry : RectangularInverseModels.Geometry columns rows}
    {cuts : RectangularSegmentSplitting.GridCuts geometry} {meshBox : Rational.Box}
    (mesh : RectangularObservationMesh.ObservationMesh cuts meshBox) (vertical forward : Bool) :
    PreparedAxisPartitions.Interval :=
  SourceBlockParameters.signedInterval forward (if vertical then ⟨meshBox.yLower, meshBox.yUpper,
    mesh.partition.y.proper⟩
    else ⟨meshBox.xLower, meshBox.xUpper, mesh.partition.x.proper⟩)

/-- The midpoint of every original physical axis interval lies strictly inside the signed mesh span. -/
theorem blockMidpoint_mesh_bounds
    {columns rows : Nat} {geometry : RectangularInverseModels.Geometry columns rows}
    {cuts : RectangularSegmentSplitting.GridCuts geometry} {meshBox : Rational.Box}
    (mesh : RectangularObservationMesh.ObservationMesh cuts meshBox) (vertical forward : Bool)
    {physical : PreparedAxisPartitions.Interval} (present : physical ∈ SourceIntervals.axisIntervals mesh vertical) :
    (signedMeshSpan mesh vertical forward).lower <
      SourceBlockParameters.blockMidpoint forward physical ∧
      SourceBlockParameters.blockMidpoint forward physical <
        (signedMeshSpan mesh vertical forward).upper
        := by
  have inside : (signedMeshSpan mesh vertical
    forward).lower ≤ (SourceBlockParameters.signedInterval forward physical).lower ∧
      (SourceBlockParameters.signedInterval forward physical).upper ≤
        (signedMeshSpan mesh vertical forward).upper
        := by
    cases vertical with
    | false =>
      have bounds := mesh.partition.x.interval_bounds present
      cases forward with
      | true => exact bounds
      | false => exact ⟨Fraction.Order.Arithmetic.neg_le_neg_direct bounds.2,
          Fraction.Order.Arithmetic.neg_le_neg_direct bounds.1⟩
    | true =>
      have bounds := mesh.partition.y.interval_bounds present
      cases forward with
      | true => exact bounds
      | false => exact ⟨Fraction.Order.Arithmetic.neg_le_neg_direct bounds.2,
          Fraction.Order.Arithmetic.neg_le_neg_direct bounds.1⟩
  have middle := PreparedSegmentCuts.midpoint_bounds (SourceBlockParameters.signedInterval forward physical)
  exact ⟨inside.1.trans_lt middle.1, middle.2.trans_le inside.2⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.LocatedSourceBlock

/-- All intervals use one occurrence-span comparison. Each source search and source-piece selection is performed once,
while constructing the bank. -/
@[expose] def buildBank
    {prepared : ExteriorProgram.AllSurfacePreparation regular domains differential} {previous : RegularMeshes.CommonCuts
      domains}
    (selected : SourceCuts prepared previous) (member : occurrence ∈ prepared.occurrences)
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) → RegularMeshes.Preflights domains sheet} {meshTarget :
      InverseRootPolynomial.Coordinate}
    (request : TwoSheetBilinearRequest.TwoSheetRequest
      (fun sheet => RegularMeshes.build domains selected.cuts sheet coarseDepth) fixed meshTarget)
    (sheet : Fin 2) (position : Fin base.faces.regulars.length)
    (evaluated : PairedSourcePlan.ParentEvaluation plan sample otherSample fine) (vertical forward : Bool)
    (lower : SourceBlockParameters.signedAxis vertical forward occurrence.start ≤
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.signedMeshSpan ((request.entries.get
        sheet).meshes.entries.get position) vertical forward).lower)
    (upper : (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.signedMeshSpan ((request.entries.get
      sheet).meshes.entries.get position) vertical forward).upper ≤
      SourceBlockParameters.signedAxis vertical forward occurrence.finish) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.AxisSourceBank evaluated ((request.entries.get
      sheet).meshes.entries.get position) vertical forward :=
  DependentVector.ofFn (fun i =>
    let mesh := (request.entries.get sheet).meshes.entries.get position
    let physical := (SourceIntervals.axisIntervals mesh vertical)[i.val]'i.isLt
    have present : physical ∈ SourceIntervals.axisIntervals mesh vertical := List.getElem_mem i.isLt
    have bounds := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.blockMidpoint_mesh_bounds mesh
      vertical forward present
    build selected member request
      sheet position evaluated vertical forward physical present
      (lower.trans bounds.1.le) (bounds.2.trans_le upper))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.LocatedSourceBlock

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies

set_option genInjectivity false in
/-- The original certified piece and junction banks with cached ordered fragments, source increments, source area and
aggregate error.

Every cache has an equality to the exact retained construction, so subsequent comparisons reuse the original family. -/
structure JoinedFragmentFamily (values : Vertex → Stokes.PrimitivePoint) (traces : Fin (count + 1) →
  JoinedTrace.VertexTrace Vertex) where
  /-- The cached sampled fragments on the original physical pieces. -/ pieces :
    PieceFragmentBank (evaluated := evaluated) (data
    := data) (otherData := otherData) values traces
  /-- The cached sampled fragments on their original owner junctions. -/ junctions :
    JunctionFragmentBank (evaluated := evaluated)
    (data := data) (otherData := otherData) values traces
  /-- The complete retained fragment list in physical traversal order. -/ fragments : List
    (PairedFragmentBlocks.OwnedFragment evaluated data otherData)
  /-- The cached fragments are exactly the interleaving of the retained piece and junction banks. -/ fragments_eq :
    fragments = fragmentFamilyOrder pieces junctions
  /-- The cached concatenation of the actual retained source increments. -/ sourceIncrements : List
    Stokes.PrimitivePoint
  /-- The source-increment cache equals the retained fragments' exact source path. -/ source_eq : sourceIncrements =
    fragmentSourcePath fragments
  /-- The cached polygon area of the original retained source increments. -/ sourceArea : InverseRootPolynomial.Gaussian
  /-- The area cache equals the exact source-increment polygon area. -/ sourceArea_eq : sourceArea =
    PairedIncrementArea.area sourceIncrements
  /-- The cached aggregate error of the actual retained fragment family. -/ error : InverseRootPolynomial.Coordinate
  /-- The error cache equals the full original fragment-block error. -/ error_eq : error =
    PairedFragmentBlocks.fragmentBlockError fragments

constructive_injectivity JoinedFragmentFamily

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.JoinedFragmentFamily

/-- Interleaving n junctions and n+1 pieces gives exactly 2n+1 retained fragments. -/
private theorem interleave_length {n : Nat}
    (pieces : Fin (n + 1) → PairedFragmentBlocks.OwnedFragment evaluated data otherData)
    (junctions : Fin n → PairedFragmentBlocks.OwnedFragment evaluated data otherData) :
    (JoinedFragmentComparison.interleaveFragments pieces junctions).length = n + n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (JoinedFragmentComparison.interleaveFragments (fun i => pieces i.succ) (fun i => junctions i.succ)).length +
      1 + 1 = _
    rw [ih]
    simp only [Nat.add_succ, Nat.succ_add, -eq_self, -iff_self]
    rfl

/-- The retained family contains exactly one fragment per original piece and owner junction. -/
theorem fragments_length {values : Vertex → Stokes.PrimitivePoint} {traces : Fin (count + 1) → JoinedTrace.VertexTrace
  Vertex}
    (family : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.JoinedFragmentFamily (evaluated :=
      evaluated) (data := data) (otherData := otherData) values traces) :
    family.fragments.length = count + count + 1 :=
  (congrArg List.length family.fragments_eq).trans
    (interleave_length _ _)

/-- A property of every original piece and junction holds for every fragment of their interleaving. -/
private theorem interleave_property (property : PairedFragmentBlocks.OwnedFragment evaluated data otherData → Prop)
    {n : Nat} (pieces : Fin (n + 1) → PairedFragmentBlocks.OwnedFragment evaluated data otherData)
    (junctions : Fin n → PairedFragmentBlocks.OwnedFragment evaluated data otherData)
    (piece : ∀ i, property (pieces i)) (junction : ∀ i, property (junctions i)) :
    ∀ fragment ∈ JoinedFragmentComparison.interleaveFragments pieces junctions, property fragment := by
  induction n with
  | zero =>
    intro fragment member
    have equal := Membership.mem_singleton.mp member
    exact equal ▸ piece 0
  | succ n ih =>
    intro fragment member
    rcases Membership.mem_cons.mp member with equal | member
    · exact equal ▸ piece 0
    rcases Membership.mem_cons.mp member with equal | member
    · exact equal ▸ junction 0
    exact ih (fun i => pieces i.succ) (fun i => junctions i.succ)
      (fun i => piece i.succ) (fun i => junction i.succ) fragment member

/-- Build both original dependent fragment banks once and cache their ordered source path, area and aggregate error. -/
@[expose] def build (values : Vertex → Stokes.PrimitivePoint) (traces : Fin (count + 1) → JoinedTrace.VertexTrace
  Vertex)
    (piece : (position : Fin (count + 1)) →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.PieceFragmentType (evaluated := evaluated)
      (data := data) (otherData := otherData) values traces position)
    (junction : (position : Fin count) →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.JunctionFragmentType (evaluated := evaluated)
      (data := data) (otherData := otherData) values traces position) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated)
      (data := data) (otherData := otherData) values traces :=
  let pieces := DependentVector.ofFn piece
  let junctions := DependentVector.ofFn junction
  let fragments := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.fragmentFamilyOrder pieces
    junctions
  let sourceIncrements := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.fragmentSourcePath
    fragments
  ⟨pieces, junctions, fragments, rfl, sourceIncrements, rfl,
    PairedIncrementArea.area sourceIncrements, rfl, PairedFragmentBlocks.fragmentBlockError fragments, rfl⟩

/-- Transfer construction-time obligations to every retained piece and junction without asking callers to inspect the
assembled fragment list. -/
theorem build_property (values : Vertex → Stokes.PrimitivePoint) (traces : Fin (count + 1) → JoinedTrace.VertexTrace
  Vertex)
    (piece : (position : Fin (count + 1)) →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.PieceFragmentType (evaluated := evaluated)
      (data := data) (otherData := otherData) values traces position)
    (junction : (position : Fin count) →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.JunctionFragmentType (evaluated := evaluated)
      (data := data) (otherData := otherData) values traces position)
    (property : PairedFragmentBlocks.OwnedFragment evaluated data otherData → Prop)
    (pieces : ∀ i, property (piece i).fragment) (junctions : ∀ i, property (junction i).fragment) :
    ∀ fragment ∈ (build values
      traces piece junction).fragments, property fragment := by
  apply interleave_property
    property
  · intro i
    rw [DependentVector.ofFn_get]
    exact pieces i
  · intro i
    rw [DependentVector.ofFn_get]
    exact junctions i

/-- The original centered trace area approximates the retained source-area cache within the exact family error. -/
theorem area_bound {values : Vertex → Stokes.PrimitivePoint} {traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex}
    (family : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.JoinedFragmentFamily (evaluated :=
      evaluated) (data := data) (otherData := otherData) values traces)
    {whole : JoinedTrace.VertexTrace Vertex} (original : CenteredBilinearPath.Sample (fun vertex => values
      (whole.indexed vertex)))
    (traceEq : whole = VertexTrace.concatenate traces) :
    Data.Gaussian.Norm.Basic.normSq (original.centeredArea - family.sourceArea) ≤ family.error := by
  have bound := JoinedFragmentComparison.joined_fragments_area_bound values traces (fun position => family.pieces.get
    position)
    (fun position => family.junctions.get position) original traceEq
  change Data.Gaussian.Norm.Basic.normSq (original.centeredArea - PairedIncrementArea.area
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.fragmentSourcePath
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.fragmentFamilyOrder family.pieces
      family.junctions))) ≤ PairedFragmentBlocks.fragmentBlockError
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.fragmentFamilyOrder family.pieces
      family.junctions) at bound
  rw [← family.fragments_eq, ← family.source_eq, ← family.sourceArea_eq] at bound
  exact bound.trans_eq family.error_eq.symm

/-- Consume local bounds on the retained fragments, paying their full count-dependent polygon contribution before
comparing the original sample. -/
theorem area_lt {values : Vertex → Stokes.PrimitivePoint} {traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex}
    (family : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.JoinedFragmentFamily (evaluated :=
      evaluated) (data := data) (otherData := otherData) values traces)
    {whole : JoinedTrace.VertexTrace Vertex} (original : CenteredBilinearPath.Sample (fun vertex => values
      (whole.indexed vertex)))
    (traceEq : whole = VertexTrace.concatenate traces) {bound target : InverseRootPolynomial.Coordinate}
    (nonnegative : 0 ≤ bound) (positive : 0 < target)
    (areas : ∀ fragment ∈ family.fragments,
      fragment.areaError ≤ PairedFragmentBlocks.fragmentLocalTolerance family.fragments.length bound target)
    (errors : ∀ fragment ∈ family.fragments,
      fragment.totalError ≤ PairedFragmentBlocks.fragmentLocalTolerance family.fragments.length bound target)
    (totals : ∀ fragment ∈ family.fragments, fragment.totalBound ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq (original.centeredArea - family.sourceArea) < target :=
  (family.area_bound original traceEq).trans_lt
    (family.error_eq.trans_lt (PairedFragmentBlocks.fragmentBlockError_lt family.fragments nonnegative positive areas
      errors totals))

/-- The count-weighted local fragment target clamped at one to retain a uniform magnitude bound. -/
@[expose] def familyLocalTarget (count : Nat) (source target : InverseRootPolynomial.Coordinate) : Coordinate :=
  min 1 (PairedFragmentBlocks.fragmentLocalTolerance count (2 * (1 + source)) target)

/-- Prepare the original density-based area budget for the clamped local fragment target. -/
@[expose] def familyAreaBudget (count : Nat) (source density target : InverseRootPolynomial.Coordinate)
    (sourceNonnegative : 0 ≤ source) (densityNonnegative : 0 ≤ density) (positive : 0 < target) :
    PairedFragmentBlocks.FragmentAreaBudget density
      (familyLocalTarget count
      source target) :=
  FragmentAreaBudget.build density _ densityNonnegative
    (Fraction.Order.Basic.lt_min (by decide) (PairedFragmentBlocks.fragmentLocalTolerance_positive count
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg (by decide) sourceNonnegative)) positive))

/-- Pay the cached full-family error itself, so the same retained budget can be consumed by either orientation of the
conjugate cap comparison. -/
theorem error_lt_of_cap {values : Vertex → Stokes.PrimitivePoint} {traces : Fin (count + 1) → JoinedTrace.VertexTrace
  Vertex}
    (family : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.JoinedFragmentFamily (evaluated :=
      evaluated) (data := data) (otherData := otherData) values traces)
    {source density target : InverseRootPolynomial.Coordinate}
    (sourceNonnegative : 0 ≤ source) (positive : 0 < target)
    {fragmentCount : Nat} (cap : PairedFragmentBlocks.FragmentAreaBudget density
      (familyLocalTarget
      fragmentCount source target))
    (count_eq : family.fragments.length = fragmentCount)
    (allowances : ∀ fragment ∈ family.fragments, fragment.allowance ≤ 1)
    (sources : ∀ fragment ∈ family.fragments, PairedFragmentValues.sourceDensity fragment.entry ≤ source)
    (densities : ∀ fragment ∈ family.fragments, PairedFragmentArea.traceDensity fragment.entry fragment.piece index ≤
      density)
    (owners : ∀ fragment ∈ family.fragments, fragment.budget.tolerance ≤ cap.tolerance)
    (queries : ∀ fragment ∈ family.fragments, PairedFragmentArea.traceError fragment.entry fragment.piece index ≤
      cap.tolerance) :
    family.error < target := by
  subst fragmentCount
  have localLe :
    familyLocalTarget
    family.fragments.length source target ≤
      PairedFragmentBlocks.fragmentLocalTolerance family.fragments.length (2 * (1 + source)) target :=
        Fraction.Order.Basic.min_le_right ..
  have unitLe :
    familyLocalTarget
    family.fragments.length source target ≤ 1 := Fraction.Order.Basic.min_le_left ..
  apply family.error_eq.trans_lt
  apply PairedFragmentBlocks.fragmentBlockError_lt family.fragments
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
      (add_nonneg (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1) sourceNonnegative)) positive
  · intro fragment member
    exact (fragment.areaError_paid cap (allowances fragment member) (densities fragment member)
      (owners fragment member) (queries fragment member)).trans localLe
  · intro fragment member
    exact (fragment.totalError_paid cap (owners fragment member) (queries fragment member)).trans localLe
  · intro fragment member
    have totalLe := fragment.totalError_paid cap (owners fragment member) (queries fragment member)
    exact (fragment.totalBound_uniform totalLe).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct unitLe (sources fragment member)) (by decide))

/-- One computed cap pays both local area and total errors. Its unit clamp also supplies the common magnitude bound
required by the cross-fragment terms. -/
theorem area_lt_of_cap {values : Vertex → Stokes.PrimitivePoint} {traces : Fin (count + 1) → JoinedTrace.VertexTrace
  Vertex}
    (family : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.JoinedFragmentFamily (evaluated :=
      evaluated) (data := data) (otherData := otherData) values traces)
    {whole : JoinedTrace.VertexTrace Vertex} (original : CenteredBilinearPath.Sample (fun vertex => values
      (whole.indexed vertex)))
    (traceEq : whole = VertexTrace.concatenate traces) {source density target : InverseRootPolynomial.Coordinate}
    (sourceNonnegative : 0 ≤ source) (positive : 0 < target)
    {fragmentCount : Nat} (cap : PairedFragmentBlocks.FragmentAreaBudget density
      (familyLocalTarget
      fragmentCount source target))
    (count_eq : family.fragments.length = fragmentCount)
    (allowances : ∀ fragment ∈ family.fragments, fragment.allowance ≤ 1)
    (sources : ∀ fragment ∈ family.fragments, PairedFragmentValues.sourceDensity fragment.entry ≤ source)
    (densities : ∀ fragment ∈ family.fragments, PairedFragmentArea.traceDensity fragment.entry fragment.piece index ≤
      density)
    (owners : ∀ fragment ∈ family.fragments, fragment.budget.tolerance ≤ cap.tolerance)
    (queries : ∀ fragment ∈ family.fragments, PairedFragmentArea.traceError fragment.entry fragment.piece index ≤
      cap.tolerance) :
    Data.Gaussian.Norm.Basic.normSq (original.centeredArea - family.sourceArea) < target :=
  (family.area_bound original traceEq).trans_lt
    (family.error_lt_of_cap sourceNonnegative positive cap count_eq allowances sources densities owners queries)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.JoinedFragmentFamily

section MatchedSides
open RectangularInverseModels Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh
variable {lc lr rc rr depth : Nat} {lg : Geometry lc lr} {rg :
  Geometry rc rr}
  {leftCuts : GridCuts lg} {rightCuts :
    GridCuts rg} {leftBox rightBox :
    Purelib.Geometry.Rational.Box}
  {left : ObservationMesh leftCuts leftBox} {right :
    ObservationMesh rightCuts rightBox}

open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.JoinedFragmentFamily

/-- Build the complete horizontal fragment family from the retained source bank and original sampled owner values.

Each physical piece and following junction reuse the same located source block, with their separately paid requests. -/
@[expose] def buildHorizontal
    {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length}
    {height : InverseRootPolynomial.Coordinate} {side : ObservationMesh.MatchedHorizontalSide left right leftRow
      rightRow height}
    (trace : side.Trace depth) {forward : Bool}
    (sources : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.AxisSourceBank evaluated left false
      forward)
    (sourceFirst : occurrence.start.im = height) (sourceLast : occurrence.finish.im = height)
    {allowance junctionAllowance : InverseRootPolynomial.Coordinate}
    (budget : NoisyPathArea.LengthErrorBudget (RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (junctionBudget : NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
    (owners : PairedOwnerRequest.OwnerRequest occurrence other budget.tolerance) (later : owners.index ≤ index)
    (junctionOwners : PairedOwnerRequest.OwnerRequest occurrence other junctionBudget.tolerance) (junctionLater :
      junctionOwners.index ≤ index)
    (first : RectangularPointReadings.PointReadings data.anchors data.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (second : RectangularPointReadings.PointReadings otherData.anchors otherData.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (leftValues rightValues : side.Vertex depth → InverseRootPolynomial.Gaussian)
    (leftEq : ∀ vertex, first.values vertex = leftValues (trace.vertices.indexed vertex))
    (rightEq : ∀ vertex, second.values vertex = rightValues (trace.vertices.indexed vertex)) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated)
      (data := data) (otherData := otherData)
      (fun vertex => ⟨leftValues vertex, rightValues vertex⟩) (side.pieceVertices depth) :=
  build _ _
    (fun column =>
      let source := sources.get (Fin.cast left.boundaryColumns_eq column)
      SourceBlockParameters.certifiedHorizontalPiece trace column source.block source.located sourceFirst sourceLast
        budget owners later
        first second leftValues rightValues leftEq rightEq)
    (fun column =>
      let source := sources.get (Fin.cast left.boundaryColumns_eq column.castSucc)
      SourceBlockParameters.certifiedHorizontalJunction trace column source.block source.located sourceFirst sourceLast
        junctionBudget junctionOwners junctionLater
        first second leftValues rightValues leftEq rightEq)

/-- Build the complete vertical fragment family from the retained source bank and original sampled owner values.

Each physical piece and following junction reuse the same located source block, with their separately paid requests. -/
@[expose] def buildVertical
    {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
    {horizontal : InverseRootPolynomial.Coordinate} {side : ObservationMesh.MatchedVerticalSide left right leftColumn
      rightColumn horizontal}
    (trace : side.Trace depth) {forward : Bool}
    (sources : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.AxisSourceBank evaluated left true
      forward)
    (sourceFirst : occurrence.start.re = horizontal) (sourceLast : occurrence.finish.re = horizontal)
    {allowance junctionAllowance : InverseRootPolynomial.Coordinate}
    (budget : NoisyPathArea.LengthErrorBudget (RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (junctionBudget : NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
    (owners : PairedOwnerRequest.OwnerRequest occurrence other budget.tolerance) (later : owners.index ≤ index)
    (junctionOwners : PairedOwnerRequest.OwnerRequest occurrence other junctionBudget.tolerance) (junctionLater :
      junctionOwners.index ≤ index)
    (first : RectangularPointReadings.PointReadings data.anchors data.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (second : RectangularPointReadings.PointReadings otherData.anchors otherData.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (leftValues rightValues : side.Vertex depth → InverseRootPolynomial.Gaussian)
    (leftEq : ∀ vertex, first.values vertex = leftValues (trace.vertices.indexed vertex))
    (rightEq : ∀ vertex, second.values vertex = rightValues (trace.vertices.indexed vertex)) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated)
      (data := data) (otherData := otherData)
      (fun vertex => ⟨leftValues vertex, rightValues vertex⟩) (side.pieceVertices depth) :=
  build _ _
    (fun row =>
      let source := sources.get (Fin.cast left.boundaryRows_eq row)
      SourceBlockParameters.certifiedVerticalPiece trace row source.block source.located sourceFirst sourceLast budget
        owners later
        first second leftValues rightValues leftEq rightEq)
    (fun row =>
      let source := sources.get (Fin.cast left.boundaryRows_eq row.castSucc)
      SourceBlockParameters.certifiedVerticalJunction trace row source.block source.located sourceFirst sourceLast
        junctionBudget junctionOwners junctionLater
        first second leftValues rightValues leftEq rightEq)

/-- The actual horizontal centered trace area satisfies the cached family's source-area error bound. -/
theorem horizontal_bound
    {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length}
    {height : InverseRootPolynomial.Coordinate} {side : ObservationMesh.MatchedHorizontalSide left right leftRow
      rightRow height}
    (trace : side.Trace depth) (values : Fin (lc + 1) → Fin (lr + 1) → InverseRootPolynomial.Gaussian →
      Stokes.PrimitivePoint)
    (family : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.JoinedFragmentFamily (evaluated :=
      evaluated) (data := data) (otherData := otherData)
      (trace.leftValue values) (side.pieceVertices depth))
    (original : CenteredBilinearPath.Sample (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))) :
    Data.Gaussian.Norm.Basic.normSq (original.centeredArea - family.sourceArea) ≤ family.error :=
  family.area_bound original trace.vertices_eq

/-- The actual vertical centered trace area satisfies the cached family's source-area error bound. -/
theorem vertical_bound
    {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
    {horizontal : InverseRootPolynomial.Coordinate} {side : ObservationMesh.MatchedVerticalSide left right leftColumn
      rightColumn horizontal}
    (trace : side.Trace depth) (values : Fin (lc + 1) → Fin (lr + 1) → InverseRootPolynomial.Gaussian →
      Stokes.PrimitivePoint)
    (family : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.JoinedFragmentFamily (evaluated :=
      evaluated) (data := data) (otherData := otherData)
      (trace.leftValue values) (side.pieceVertices depth))
    (original : CenteredBilinearPath.Sample (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))) :
    Data.Gaussian.Norm.Basic.normSq (original.centeredArea - family.sourceArea) ≤ family.error :=
  family.area_bound original trace.vertices_eq

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.JoinedFragmentFamily

end MatchedSides

end
