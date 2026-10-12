module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PhysicalLoops
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.HoleReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoExteriorBudget
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Approximation.Budget.SynchronizedSamples
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.FamilyReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.WeightedPair
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathParentCaches
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalExteriorPeriods

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Riemann

public section

/-! Original standard A/B readings with both physical corrections paid on
one numerical bank. The odd exterior reuses the cached physical loop rows. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard

open Purelib.Riemann.Normalization

open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

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

namespace OddReadings

set_option genInjectivity false in
/-- Original odd-degree physical loops with a shared exterior budget and one retained exterior component. -/
structure OddPreparation
    (periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared components)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (floor : Nat) (target : Fraction.Rational) : Type 3 where
  /-- The original shared physical-loop decomposition for both period rows. -/ loops :
    PhysicalLoops periods
  /-- The common exterior allowance computed from both original row splits. -/ allocation :
    TwoExteriorBudget loops.aSplit loops.bSplit target
  /-- The original exterior surface preparation for the retained standard differential. -/ exterior :
    Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains (Periods.PeriodMatrix.standardDifferential differential)
  /-- The actual retained odd exterior surface component. -/ component :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
    regular domains (Periods.PeriodMatrix.standardDifferential differential)
  /-- The original odd energy preparation at the shared allowance and stage floor. -/ ready :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.AllSurfacePreparation.RequestedOddEnergy.Preparation
    exterior component allocation.allowance floor

constructive_injectivity OddPreparation

end OddReadings

namespace OddReadings.OddPreparation

/-- Exact acquired-exterior type, keeping structure-generated theorem parameters compact. -/
@[expose] def Acquired
    {periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared components}
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
      {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
    {floor : Nat} {target : Fraction.Rational}
    (preparation : Hyperelliptic.Meshes.PuncturedGrid.Standard.OddReadings.OddPreparation periods domains regular floor
      target)
    (energyTarget : Fraction.Rational) (depthFloor energyFloor : Nat) :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.AllSurfacePreparation.RequestedOddEnergy
    preparation.exterior preparation.component preparation.allocation.allowance
    energyTarget floor depthFloor energyFloor

/-- The acquired odd exterior control uses exactly the supplied original numerical bank. -/
@[expose] def SharedEq
    {periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared components}
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
      {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
    {floor : Nat} {target : Fraction.Rational}
    (preparation : Hyperelliptic.Meshes.PuncturedGrid.Standard.OddReadings.OddPreparation periods domains regular floor
      target)
    (energyTarget : Fraction.Rational) (depthFloor energyFloor numericalIndex : Nat)
    (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains)
    (acquired : preparation.Acquired energyTarget depthFloor energyFloor) : Prop :=
  HEq acquired.acquired.shared shared

/-- The flattened original exterior boundary value meets the retained shared allowance. -/
@[expose] def BoundarySmall
    {periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared components}
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
      {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
    {floor : Nat} {target : Fraction.Rational}
    (preparation : Hyperelliptic.Meshes.PuncturedGrid.Standard.OddReadings.OddPreparation periods domains regular floor
      target)
    (numericalIndex : Nat)
    (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains)
    (triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) :
      Prop :=
  Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh triangles.values)
    lifted.exteriorBoundaries.flatten) < preparation.allocation.allowance

end OddReadings.OddPreparation

namespace OddReadings

set_option genInjectivity false in
/-- The acquired odd exterior energy and small canonical boundary on the same original numerical bank. -/
structure OddExteriorReadings
    {periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared components}
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
      {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
    {floor : Nat} {target : Fraction.Rational}
    (preparation : Hyperelliptic.Meshes.PuncturedGrid.Standard.OddReadings.OddPreparation periods domains regular floor
      target)
    (energyTarget : Fraction.Rational) (depthFloor energyFloor numericalIndex : Nat)
    (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains)
    (triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) :
      Type 3 where
  /-- The acquired exterior energy request at the retained energy and depth floors. -/ acquired : preparation.Acquired
    energyTarget depthFloor energyFloor
  /-- The acquired exterior request uses the supplied original shared numerics. -/ shared_eq : preparation.SharedEq
    energyTarget depthFloor energyFloor numericalIndex shared acquired
  /-- The original flattened exterior word meets the shared allowance on these triangle readings. -/ boundary_small :
    preparation.BoundarySmall numericalIndex shared triangles

constructive_injectivity OddExteriorReadings

/-- The original hole readings and odd exterior control with exact identity of the retained physical loops. -/
@[expose] def OddPayload
    {periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared components}
    (segments : Data.Vector.DependentVector (fun entry =>
      Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (prepared.programs.programs entry).period))
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
      {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
    {floor : Nat} {target : Fraction.Rational}
    (preparation : Hyperelliptic.Meshes.PuncturedGrid.Standard.OddReadings.OddPreparation periods domains regular floor
      target)
    (minimum : Nat) (energyTarget : Fraction.Rational) (depthFloor energyFloor : Nat) (extraPoints : List
      Gaussian.Basic.Canonical) : Type 3 :=
  (holes : HoleReadings periods segments domains minimum (max
    floor preparation.ready.charts.index) (target / 4) extraPoints) ×
    { _exterior : Hyperelliptic.Meshes.PuncturedGrid.Standard.OddReadings.OddExteriorReadings preparation energyTarget
      depthFloor energyFloor
        holes.comparison.readings.standard.original.shared.numericalIndex
        holes.comparison.readings.standard.original.shared.numerics holes.comparison.readings.standard.triangles //
      holes.preparation.loops = preparation.loops }

end OddReadings

set_option genInjectivity false in
/-- The original odd-degree A/B readings with weighted holes and exterior energy paid on one shared bank. -/
structure OddReadings
    (periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared components)
    (segments : Data.Vector.DependentVector (fun entry =>
      Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (prepared.programs.programs entry).period))
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (minimum floor : Nat) (target energyTarget : Fraction.Rational) (depthFloor energyFloor : Nat) (extraPoints : List
      Gaussian.Basic.Canonical) : Type 3 where
  /-- The retained original loop rows, exterior budget and odd component request. -/ preparation :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.OddReadings.OddPreparation periods domains regular floor target
  /-- The original hole and exterior readings sharing their numerical bank and physical loops. -/ payload :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.OddReadings.OddPayload segments preparation minimum energyTarget
    depthFloor energyFloor extraPoints

constructive_injectivity OddReadings

namespace OddReadings

variable {periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared
  components}
  {segments : Data.Vector.DependentVector (fun entry =>
    Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (prepared.programs.programs entry).period)}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
    {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {minimum floor depthFloor energyFloor : Nat} {target energyTarget : Fraction.Rational} {extraPoints : List
    Gaussian.Basic.Canonical}

/-- Acquire the original odd-degree period rows after paying both physical corrections.

The construction retains the actual odd exterior component, cached row budget and requested depth/energy floors, then
evaluates all corrections on the same numerical bank. -/
@[expose] def build (periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span
  prepared components)
    (segments : Data.Vector.DependentVector (fun entry =>
      Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (prepared.programs.programs entry).period))
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (minimum floor : Nat) (target energyTarget : Fraction.Rational) (positive : 0 < target) (energyPositive : 0 <
      energyTarget)
    (depthFloor energyFloor : Nat) (extraPoints : List Gaussian := []) :
    OddReadings periods segments domains regular minimum floor
      target energyTarget depthFloor energyFloor extraPoints := by
  let loops := PhysicalLoops.build periods
  let allocation := TwoExteriorBudget.build loops.aSplit
    loops.bSplit target positive
  let exterior :=
    Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
    regular domains (Periods.PeriodMatrix.standardDifferential differential)
  let component := Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy.singleComponent exterior
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy.build_odd_component_count regular domains _ branch)
  let ready :=
    Exterior.EnergyTolerance.AllSurfacePreparation.RequestedOddEnergy.Preparation.build
    exterior component.val component.property allocation.allowance allocation.positive floor
  let contacts := Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations.build
    lifted.cutPolygon.patch lifted.cutBoundaryPairs
    (Periods.PeriodMatrix.standardDifferential differential) domains
  have quarterPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
  have holePositive := Fraction.Order.Field.div_pos_direct quarterPositive (by decide : (0 : Fraction.Rational) < 4)
  let preparation : Hyperelliptic.Meshes.PuncturedGrid.Standard.HoleReadings.HolePreparation periods domains (target /
    4) (max floor ready.charts.index) :=
    ⟨loops, contacts,
      Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection.HolePhysicalRequest.build contacts
        loops.aSplit.coefficients ((target / 4) / 4) holePositive (max floor ready.charts.index),
      Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection.HolePhysicalRequest.build contacts
        loops.bSplit.coefficients ((target / 4) / 4) holePositive (max floor ready.charts.index)⟩
  let comparison := Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.build periods
    segments domains minimum
    (max preparation.a.index preparation.b.index) ((target / 4) / 4) holePositive extraPoints
  let holes : HoleReadings periods segments domains minimum
    (max floor ready.charts.index) (target / 4) extraPoints :=
    ⟨preparation, comparison⟩
  have later : ready.charts.index ≤ holes.comparison.readings.standard.original.shared.numericalIndex :=
    (Data.Nat.Order.le_max_right _ _).trans (preparation.a.floor_le.trans ((Data.Nat.Order.le_max_left _ _).trans
      holes.numerical_later))
  let sample := Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample.build cap
    (Periods.PeriodMatrix.standardDifferential differential)
    holes.comparison.readings.standard.original.shared.numericalIndex collar.box
  let acquired := ready.evaluate branch energyTarget energyPositive depthFloor energyFloor sample
    holes.comparison.readings.standard.original.shared.numerics later
  let initial : Hyperelliptic.Meshes.PuncturedGrid.Standard.OddReadings.OddPreparation periods domains regular floor
    target := ⟨loops, allocation, exterior, component.val, ready⟩
  exact ⟨initial, ⟨holes, ⟨⟨acquired, HEq.rfl,
    acquired.canonical_period_small branch holes.comparison.readings.standard.triangles⟩, rfl⟩⟩⟩

end OddReadings
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard
