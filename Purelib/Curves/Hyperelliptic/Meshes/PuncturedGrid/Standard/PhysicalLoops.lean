module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Chord.PhysicalBoundary
import Purelib.Topology.Surface.Cut.BoundaryPairs
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.CutPhysicalCycles
import Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Approximation.Budget.SynchronizedSamples
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyLateRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.FamilyReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.WeightedPair
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Surface.Chord.Spanning
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann

public section

/-! The physical correction of the actual standard A/B comparison is a
computed integer combination of the original exterior and two-lap hole
loops. Both rows share one boundary decomposition. No loop weights or
boundary matching are supplied by the caller. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard

open Purelib.Topology.Polygon.Stokes

open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank

open Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : Meshes.FramedPuncturedGrid curve (Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve
    branches).branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {index differential : Fin genus} {row : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow
    lifted integral index} {source : Hyperelliptic.Differentials.Basic.Differential genus}
  {prepared : Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutChordPrograms lifted source}
  {components : Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ComponentSamples prepared.programs differential}

namespace PhysicalLoops

/-- The original sewn cut boundary has distinct projected oriented edge occurrences. -/
theorem cut_unique :
    (lifted.cutPolygon.patch.cut.boundary.map (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
      lifted.cutPolygon.patch.cut.vertexLabels)).Nodup := by
  rw [lifted.cutPolygon.patch.cut.boundary_eq]
  exact Topology.Surface.Cut.BoundaryPairs.SewnPatch.boundary_unique lifted.cutPolygon.patch
    (Topology.Surface.Cut.BoundaryPairs.SewingForest.SinglePolygon.originalEdges_unique lifted.cutPolygon
      lifted.mesh.orientedEdges_unique)

/-- The original A-row physical correction has zero integer boundary at every retained vertex. -/
theorem a_physical_closed
    (periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared components)
    (vertex : Fin lifted.vertices.count) :
    FiniteSum.Fin.sumFin (fun column => periods.aGeometry.physical column *
      Topology.Chain.PathBoundary.edgeBoundaryAt Topology.Polygon.Stokes.OrientedEdge.start
        Topology.Polygon.Stokes.OrientedEdge.finish
        (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
          (lifted.cutBoundaryWord.alphabet.generators column)) vertex) = 0 :=
  Topology.Surface.Chord.PhysicalBoundary.IntegralPairing.SpanningCoordinates.OnChords.physical_boundary_zero
    periods.aGeometry lifted.cutPolygon.patch.cut.closed
    row.coordinates.a_boundary_zero vertex

/-- The original B-row physical correction has zero integer boundary at every retained vertex. -/
theorem b_physical_closed
    (periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared components)
    (vertex : Fin lifted.vertices.count) :
    FiniteSum.Fin.sumFin (fun column => periods.bGeometry.physical column *
      Topology.Chain.PathBoundary.edgeBoundaryAt Topology.Polygon.Stokes.OrientedEdge.start
        Topology.Polygon.Stokes.OrientedEdge.finish
        (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
          (lifted.cutBoundaryWord.alphabet.generators column)) vertex) = 0 :=
  Topology.Surface.Chord.PhysicalBoundary.IntegralPairing.SpanningCoordinates.OnChords.physical_boundary_zero
    periods.bGeometry lifted.cutPolygon.patch.cut.closed
    row.coordinates.b_boundary_zero vertex

end PhysicalLoops

set_option genInjectivity false in
/-- The computed physical boundary-loop corrections for both original standard period rows.

Both integer rows share one retained canonical boundary decomposition, with their exterior and two-lap hole
contributions kept separately. -/
structure PhysicalLoops
    (periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared components)
      where
  /-- The retained simple cycle decomposition of the original triangulated boundary. -/ boundary :
    Topology.Surface.Sewing.SimpleBoundaryCycles.PolygonStokes.BoundaryCycleDecomposition
    (Topology.Polygon.Stokes.triangleEdgeOccurrences lifted.mesh.triangulation.faces)
  /-- The decomposition uses exactly the original lifted boundary loops. -/ canonical : boundary.cycles =
    lifted.boundaryLoops
  /-- The original A-row integer coordinates on that boundary decomposition. -/ a :
    Topology.Surface.Sewing.PhysicalCycleCoordinates.Data boundary
    (fun column => Topology.Surface.Sewing.VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
      (lifted.cutBoundaryWord.alphabet.generators column))
    periods.aGeometry.physical
  /-- The original B-row integer coordinates on that same boundary decomposition. -/ b :
    Topology.Surface.Sewing.PhysicalCycleCoordinates.Data boundary
    (fun column => Topology.Surface.Sewing.VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
      (lifted.cutBoundaryWord.alphabet.generators column))
    periods.bGeometry.physical
  /-- The actual exterior and two-lap hole split of the retained A-row loops. -/ aSplit :
    PhysicalLoopSplit lifted a.rows
  /-- The actual exterior and two-lap hole split of the retained B-row loops. -/ bSplit :
    PhysicalLoopSplit lifted b.rows

constructive_injectivity PhysicalLoops

namespace PhysicalLoops

variable {periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared
  components}

/-- Compute both original physical rows on one shared canonical boundary decomposition and retain their exterior and
hole splits. -/
@[expose] def build (periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span
  prepared components) : PhysicalLoops periods :=
  let boundary := lifted.boundaryComponents
  let a := Topology.Surface.Sewing.CutPhysicalCycles.ProjectedEdgePairing.physicalCycles lifted.cutBoundaryPairs
    Hyperelliptic.Meshes.PuncturedGrid.Standard.PhysicalLoops.cut_unique boundary
    lifted.cut_boundary_iff_boundaryComponents
    periods.aGeometry.physical periods.aGeometry.physical_paired_zero
      (Hyperelliptic.Meshes.PuncturedGrid.Standard.PhysicalLoops.a_physical_closed periods)
  let b := Topology.Surface.Sewing.CutPhysicalCycles.ProjectedEdgePairing.physicalCycles lifted.cutBoundaryPairs
    Hyperelliptic.Meshes.PuncturedGrid.Standard.PhysicalLoops.cut_unique boundary
    lifted.cut_boundary_iff_boundaryComponents
    periods.bGeometry.physical periods.bGeometry.physical_paired_zero
      (Hyperelliptic.Meshes.PuncturedGrid.Standard.PhysicalLoops.b_physical_closed periods)
  ⟨boundary, rfl, a, b, PhysicalLoopSplit.build lifted a.rows
    a.words_eq,
    PhysicalLoopSplit.build lifted b.rows b.words_eq⟩

/-- The A-row physical value is its actual weighted exterior-loop sum plus the retained weighted two-lap hole values. -/
theorem a_value (loops : PhysicalLoops periods) (value :
  Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) :
    Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine periods.aGeometry.physical
        (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (loops.aSplit.exterior.map (fun entry => (entry.1 :
        Gaussian.Basic.Canonical) * Topology.Surface.Sewing.SewingRetraction.wordValue value entry.2)) +
        loops.aSplit.coefficients.combine (fun hole : Fin base.faces.holes.length =>
          Topology.Surface.Sewing.SewingRetraction.wordValue value (base.faces.holes[hole.val].liftedBoundary
            lifted.vertices lifted.edges)) :=
  (loops.a.value_eq value).trans (loops.aSplit.value_eq value)

/-- The B-row physical value is its actual weighted exterior-loop sum plus the retained weighted two-lap hole values. -/
theorem b_value (loops : PhysicalLoops periods) (value :
  Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) :
    Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine periods.bGeometry.physical
        (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (loops.bSplit.exterior.map (fun entry => (entry.1 :
        Gaussian.Basic.Canonical) * Topology.Surface.Sewing.SewingRetraction.wordValue value entry.2)) +
        loops.bSplit.coefficients.combine (fun hole : Fin base.faces.holes.length =>
          Topology.Surface.Sewing.SewingRetraction.wordValue value (base.faces.holes[hole.val].liftedBoundary
            lifted.vertices lifted.edges)) :=
  (loops.b.value_eq value).trans (loops.bSplit.value_eq value)

/-- Replace an exactly equal physical correction in the same cached period comparison. -/
private theorem replace_correction {standard cached correction replacement : Gaussian.Basic.Canonical}
    {target : Fraction.Rational} (equal : correction = replacement)
    (bound : Data.Gaussian.Norm.Basic.normSq (standard - (cached + correction)) < target) :
    Data.Gaussian.Norm.Basic.normSq (standard - (cached + replacement)) < target :=
  (congrArg (fun value => Data.Gaussian.Norm.Basic.normSq (standard - (cached + value))) equal).symm.trans_lt bound

variable
  {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)}
  (normal : LinearAlgebra.Alternating.NormalForm integral.paired raw)
  (period : Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodRow curve)
  (periodEq : period = (Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofData curve
    branches).rows index)
  {periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow.ofPeriod lifted integral normal index
      period periodEq).span prepared components}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {segments : Data.Vector.DependentVector (fun entry =>
    Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (prepared.programs.programs entry).period)}
  {minimum numericalFloor : Nat} {target : Fraction.Rational} {extraPoints : List Gaussian.Basic.Canonical}

/-- The actual standard A sample retains precisely the computed original
exterior and hole corrections. No physical term is declared negligible. -/
@[expose] def AStandardAccurate (loops : PhysicalLoops
  periods)
    (request : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments
      domains minimum numericalFloor target extraPoints)
    (values : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.Values request) : Prop
      :=
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      request.readings.standard.triangles.values
    let exterior := Data.Gaussian.Norm.Sum.Basic.gaussianSum (loops.aSplit.exterior.map (fun entry => (entry.1 :
      Gaussian.Basic.Canonical) * Topology.Surface.Sewing.SewingRetraction.wordValue value entry.2))
    let holes := loops.aSplit.coefficients.combine (fun hole : Fin base.faces.holes.length =>
      Topology.Surface.Sewing.SewingRetraction.wordValue value (base.faces.holes[hole.val].liftedBoundary
        lifted.vertices lifted.edges))
    Data.Gaussian.Norm.Basic.normSq
      ((((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve branches).aProgram differential
        index).integral.model
        request.common.common.stage).integralSample - (values.aValue + (exterior + holes))) < target

/-- The original standard A-period meets the target with its cached value and computed exterior and hole corrections. -/
theorem a_standard_accurate (loops : PhysicalLoops periods)
    (request : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments
      domains minimum numericalFloor target extraPoints)
    (values : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.Values request) :
    AStandardAccurate normal period periodEq
      loops request values :=
  replace_correction (loops.a_value _)
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.a_cached_accurate normal period
      periodEq request values)

/-- The actual standard B sample retains precisely the computed original
exterior and hole corrections. No physical term is declared negligible. -/
@[expose] def BStandardAccurate (loops : PhysicalLoops
  periods)
    (request : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments
      domains minimum numericalFloor target extraPoints)
    (values : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.Values request) : Prop
      :=
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      request.readings.standard.triangles.values
    let exterior := Data.Gaussian.Norm.Sum.Basic.gaussianSum (loops.bSplit.exterior.map (fun entry => (entry.1 :
      Gaussian.Basic.Canonical) * Topology.Surface.Sewing.SewingRetraction.wordValue value entry.2))
    let holes := loops.bSplit.coefficients.combine (fun hole : Fin base.faces.holes.length =>
      Topology.Surface.Sewing.SewingRetraction.wordValue value (base.faces.holes[hole.val].liftedBoundary
        lifted.vertices lifted.edges))
    Data.Gaussian.Norm.Basic.normSq
      ((((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve branches).bProgram differential
        index).integral.model
        request.common.common.stage).integralSample - (values.bValue + (exterior + holes))) < target

/-- The original standard B-period meets the target with its cached value and computed exterior and hole corrections. -/
theorem b_standard_accurate (loops : PhysicalLoops periods)
    (request : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments
      domains minimum numericalFloor target extraPoints)
    (values : Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.Values request) :
    BStandardAccurate normal period periodEq
      loops request values :=
  replace_correction (loops.b_value _)
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.b_cached_accurate normal period
      periodEq request values)

end PhysicalLoops
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard
