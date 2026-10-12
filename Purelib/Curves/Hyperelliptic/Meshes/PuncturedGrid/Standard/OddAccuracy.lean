module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PhysicalLoops
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.OddReadings
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Budget.SynchronizedSamples
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyLateRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.FamilyReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.HoleReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoExteriorBudget
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
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
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Chord.Spanning
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann

public section

/-! The actual odd-degree standard A/B samples approximate the cached
chord-period values after both original physical boundary corrections. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.OddAccuracy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Integration

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
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared components}
  {segments : Data.Vector.DependentVector (fun entry =>
    Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (prepared.programs.programs entry).period)}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
    {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {minimum floor depthFloor energyFloor : Nat} {target energyTarget : Fraction.Rational} {extraPoints : List
    Gaussian.Basic.Canonical}

/-- Both original weighted exterior row values meet their quarter-target allocations on the retained numerical bank. -/
@[expose] def ExteriorSmall
    (request : OddReadings periods segments domains regular
      minimum floor target energyTarget depthFloor energyFloor extraPoints) : Prop :=
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      request.payload.fst.comparison.readings.standard.triangles.values
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (request.payload.fst.preparation.loops.aSplit.exterior.map
      (fun entry => (entry.1 : Gaussian.Basic.Canonical) * Topology.Surface.Sewing.SewingRetraction.wordValue value
        entry.2))) < target / 4 ∧
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (request.payload.fst.preparation.loops.bSplit.exterior.map
      (fun entry => (entry.1 : Gaussian.Basic.Canonical) * Topology.Surface.Sewing.SewingRetraction.wordValue value
        entry.2))) < target / 4

/-- The retained odd exterior budget turns its paid canonical boundary into small original weighted A/B exterior values.
-/
theorem exterior_small
    (request : OddReadings periods segments domains regular
      minimum floor target energyTarget depthFloor energyFloor extraPoints)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.OddAccuracy.ExteriorSmall request := by
  let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
    request.payload.fst.comparison.readings.standard.triangles.values
  have paid := request.preparation.allocation.accurate branch value request.payload.snd.val.boundary_small
  have aEq := congrArg (fun loops : PhysicalLoops periods =>
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (loops.aSplit.exterior.map (fun entry => (entry.1 : Gaussian.Basic.Canonical) *
      Topology.Surface.Sewing.SewingRetraction.wordValue value entry.2)))) request.payload.snd.property
  have bEq := congrArg (fun loops : PhysicalLoops periods =>
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (loops.bSplit.exterior.map (fun entry => (entry.1 : Gaussian.Basic.Canonical) *
      Topology.Surface.Sewing.SewingRetraction.wordValue value entry.2)))) request.payload.snd.property
  exact ⟨aEq.trans_lt paid.1, bEq.trans_lt paid.2⟩

/-- A quarter-target comparison and quarter-target exterior bound pay the original standard-to-cached comparison. -/
private theorem pay_exterior {standard cached exterior : Gaussian.Basic.Canonical} {target : Fraction.Rational}
    (comparison : Data.Gaussian.Norm.Basic.normSq (standard - (cached + exterior)) < target / 4)
    (small : Data.Gaussian.Norm.Basic.normSq exterior < target / 4) : Data.Gaussian.Norm.Basic.normSq (standard
      - cached) < target := by
  have bound := (Gaussian.Norm.Bounds.normSq_add_le_two
    (standard - (cached + exterior)) exterior).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct comparison small))
  have equal : standard - (cached + exterior) + exterior = standard - cached := by ring1
  exact (congrArg Data.Gaussian.Norm.Basic.normSq equal).symm.trans_lt
    (bound.trans_eq ((by ring1 : 2 * (target / 4 + target / 4) = (target / 4) * 4).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))

variable
  {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)}
  (normal : LinearAlgebra.Alternating.NormalForm integral.paired raw)
  (period : Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodRow curve)
  (periodEq : period = (Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofData curve
    branches).rows index)
  {periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow.ofPeriod lifted integral normal index
      period periodEq).span prepared components}

/-- The cached A/B values of the exact retained original period-relation readings. -/
@[expose] def AccuracyValues
    (request : OddReadings periods segments domains regular
      minimum floor target energyTarget depthFloor energyFloor extraPoints) :=
      Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.Values
      request.payload.fst.comparison

/-- The original standard A-period sample approximates its retained cached value within the requested target. -/
@[expose] def AAccurate
    (request : OddReadings periods segments domains regular
      minimum floor target energyTarget depthFloor energyFloor extraPoints)
    (values : Hyperelliptic.Meshes.PuncturedGrid.Standard.OddAccuracy.AccuracyValues normal period periodEq request) :
      Prop :=
    Data.Gaussian.Norm.Basic.normSq ((((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve
      branches).aProgram differential index).integral.model
      request.payload.fst.comparison.common.common.stage).integralSample - values.aValue) < target

/-- The original standard A-period sample meets its target after paying the retained hole and exterior corrections. -/
theorem a_accurate
    (request : OddReadings periods segments domains regular
      minimum floor target energyTarget depthFloor energyFloor extraPoints)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (values : Hyperelliptic.Meshes.PuncturedGrid.Standard.OddAccuracy.AccuracyValues normal period periodEq request) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.OddAccuracy.AAccurate normal period periodEq request values :=
  Hyperelliptic.Meshes.PuncturedGrid.Standard.OddAccuracy.pay_exterior (request.payload.fst.a_exterior_accurate normal
    period periodEq values) (Hyperelliptic.Meshes.PuncturedGrid.Standard.OddAccuracy.exterior_small request branch).1

/-- The original standard B-period sample approximates its retained cached value within the requested target. -/
@[expose] def BAccurate
    (request : OddReadings periods segments domains regular
      minimum floor target energyTarget depthFloor energyFloor extraPoints)
    (values : Hyperelliptic.Meshes.PuncturedGrid.Standard.OddAccuracy.AccuracyValues normal period periodEq request) :
      Prop :=
    Data.Gaussian.Norm.Basic.normSq ((((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve
      branches).bProgram differential index).integral.model
      request.payload.fst.comparison.common.common.stage).integralSample - values.bValue) < target

/-- The original standard B-period sample meets its target after paying the retained hole and exterior corrections. -/
theorem b_accurate
    (request : OddReadings periods segments domains regular
      minimum floor target energyTarget depthFloor energyFloor extraPoints)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (values : Hyperelliptic.Meshes.PuncturedGrid.Standard.OddAccuracy.AccuracyValues normal period periodEq request) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.OddAccuracy.BAccurate normal period periodEq request values :=
  Hyperelliptic.Meshes.PuncturedGrid.Standard.OddAccuracy.pay_exterior (request.payload.fst.b_exterior_accurate normal
    period periodEq values) (Hyperelliptic.Meshes.PuncturedGrid.Standard.OddAccuracy.exterior_small request branch).2

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.OddAccuracy
