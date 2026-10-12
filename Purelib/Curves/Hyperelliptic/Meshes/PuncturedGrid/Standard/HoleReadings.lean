module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PhysicalLoops
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalHoleCorrection
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Budget.SynchronizedSamples
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyLateRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit
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
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
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
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann

public section

/-! Original standard A/B readings with every weighted branch-hole period
correction paid before the common numerical bank is sampled. The original
exterior loops remain explicit, with their computed integer coefficients. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard

open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank

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

namespace HoleReadings

set_option genInjectivity false in
/-- The original physical-loop decomposition and paid weighted hole requests for both period rows.

Both requests retain the same boundary contacts and the computed integer hole coefficients. -/
structure HolePreparation
    (periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared components)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (target : Fraction.Rational) (floor : Nat) where
  /-- The original shared physical-loop decomposition for both period rows. -/ loops :
    PhysicalLoops periods
  /-- The retained boundary contact preparations on the same domain bank. -/ contacts :
    Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch
    lifted.cutBoundaryPairs
    (Periods.PeriodMatrix.standardDifferential differential) domains
  /-- The quarter-target hole request using the actual A-row coefficients. -/ a :
    Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection.HolePhysicalRequest contacts loops.aSplit.coefficients
    (target / 4) floor
  /-- The quarter-target hole request using the actual B-row coefficients. -/ b :
    Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection.HolePhysicalRequest contacts loops.bSplit.coefficients
    (target / 4) floor

constructive_injectivity HolePreparation

end HoleReadings

namespace HoleReadings.HolePreparation

/-- Compute the original physical-loop split and prepare both weighted hole corrections before acquiring numerical
readings. -/
@[expose] def build (periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span
  prepared components)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (target : Fraction.Rational) (positive : 0 < target) (floor : Nat) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.HoleReadings.HolePreparation periods domains target floor :=
  let loops := PhysicalLoops.build periods
  let contacts := Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations.build
    lifted.cutPolygon.patch lifted.cutBoundaryPairs
    (Periods.PeriodMatrix.standardDifferential differential) domains
  let positiveQuarter := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
  ⟨loops, contacts, Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection.HolePhysicalRequest.build contacts
    loops.aSplit.coefficients (target / 4) positiveQuarter floor,
    Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection.HolePhysicalRequest.build contacts
      loops.bSplit.coefficients (target / 4) positiveQuarter floor⟩

end HoleReadings.HolePreparation

set_option genInjectivity false in
/-- The original period-relation readings acquired after both weighted hole requests are paid. -/
structure HoleReadings
    (periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared components)
    (segments : Data.Vector.DependentVector (fun entry =>
      Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (prepared.programs.programs entry).period))
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (minimum floor : Nat) (target : Fraction.Rational) (extraPoints : List Gaussian.Basic.Canonical) where
  /-- The retained original loop, contact and weighted-hole preparation. -/ preparation :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.HoleReadings.HolePreparation periods domains target floor
  /-- The period comparison whose numerical floor includes both original hole requests. -/ comparison :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings periods segments domains minimum
    (max preparation.a.index preparation.b.index) (target / 4) extraPoints

constructive_injectivity HoleReadings

namespace HoleReadings

variable {periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared
  components}
  {segments : Data.Vector.DependentVector (fun entry =>
    Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (prepared.programs.programs entry).period)}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {minimum floor : Nat} {target : Fraction.Rational} {extraPoints : List Gaussian.Basic.Canonical}

/-- Prepare both original weighted hole requests and acquire the period comparison at their common numerical floor. -/
@[expose] def build (periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span
  prepared components)
    (segments : Data.Vector.DependentVector (fun entry =>
      Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (prepared.programs.programs entry).period))
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (minimum floor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (extraPoints : List Gaussian := []) :
    HoleReadings periods segments domains minimum floor target
      extraPoints :=
  let preparation := Hyperelliptic.Meshes.PuncturedGrid.Standard.HoleReadings.HolePreparation.build periods domains
    target positive floor
  let readings := Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.build periods
    segments domains minimum
    (max preparation.a.index preparation.b.index) (target / 4)
    (Fraction.Order.Field.div_pos_direct positive (by decide)) extraPoints
  ⟨preparation, readings⟩

/-- The shared original numerical stage covers both retained weighted-hole thresholds. -/
@[expose] def NumericalLater
    (request : HoleReadings periods segments domains minimum
      floor target extraPoints) : Prop :=
    max request.preparation.a.index request.preparation.b.index ≤
      request.comparison.readings.standard.original.shared.numericalIndex

/-- The acquired shared numerical bank is sufficiently late for both original hole requests. -/
theorem numerical_later
    (request : HoleReadings periods segments domains minimum
      floor target extraPoints) :
    NumericalLater request :=
  request.comparison.preparation.budget.surface_later.trans request.comparison.readings.later

/-- The original weighted A-row two-lap hole correction meets its quarter-target allocation. -/
@[expose] def AHolesAccurate
    (request : HoleReadings periods segments domains minimum
      floor target extraPoints) : Prop :=
    Data.Gaussian.Norm.Basic.normSq (request.preparation.loops.aSplit.coefficients.combine (fun hole : Fin
      base.faces.holes.length =>
      Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
        request.comparison.readings.standard.triangles.values)
        (base.faces.holes[hole.val].liftedBoundary lifted.vertices lifted.edges))) < target / 4

/-- The retained A-row hole request pays its actual canonical hole correction. -/
theorem a_holes_accurate
    (request : HoleReadings periods segments domains minimum
      floor target extraPoints) :
    AHolesAccurate request :=
  Hyperelliptic.Meshes.PuncturedGrid.CanonicalHoleCorrection.canonical_accurate request.preparation.a
    ((Data.Nat.Order.le_max_left _ _).trans request.numerical_later)
    request.comparison.readings.standard.triangles

/-- The original weighted B-row two-lap hole correction meets its quarter-target allocation. -/
@[expose] def BHolesAccurate
    (request : HoleReadings periods segments domains minimum
      floor target extraPoints) : Prop :=
    Data.Gaussian.Norm.Basic.normSq (request.preparation.loops.bSplit.coefficients.combine (fun hole : Fin
      base.faces.holes.length =>
      Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
        request.comparison.readings.standard.triangles.values)
        (base.faces.holes[hole.val].liftedBoundary lifted.vertices lifted.edges))) < target / 4

/-- The retained B-row hole request pays its actual canonical hole correction. -/
theorem b_holes_accurate
    (request : HoleReadings periods segments domains minimum
      floor target extraPoints) :
    BHolesAccurate request :=
  Hyperelliptic.Meshes.PuncturedGrid.CanonicalHoleCorrection.canonical_accurate request.preparation.b
    ((Data.Nat.Order.le_max_right _ _).trans request.numerical_later)
    request.comparison.readings.standard.triangles

/-- A quarter-target comparison and quarter-target hole estimate pay the corrected comparison with the physical exterior
retained. -/
private theorem pay_holes {standard cached exterior holes : Gaussian.Basic.Canonical} {target : Fraction.Rational}
    (comparison : Data.Gaussian.Norm.Basic.normSq (standard - (cached + (exterior + holes))) < target / 4)
    (small : Data.Gaussian.Norm.Basic.normSq holes < target / 4) : Data.Gaussian.Norm.Basic.normSq (standard -
      (cached + exterior)) < target := by
  have bound := (Gaussian.Norm.Bounds.normSq_add_le_two
    (standard - (cached + (exterior + holes))) holes).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct comparison small))
  have equal : standard - (cached + (exterior + holes)) + holes = standard - (cached + exterior) := by ring1
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

/-- Exact cached-value type; keep the dependent comparison behind a named boundary. -/
@[expose] def AccuracyValues
    (request : HoleReadings periods segments domains minimum
      floor target extraPoints) :=
  Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.Values request.comparison

/-- Every original hole correction is paid; the original exterior remains. -/
@[expose] def AExteriorAccurate
    (request : HoleReadings periods segments domains minimum
      floor target extraPoints)
    (values : AccuracyValues normal period
      periodEq request) : Prop :=
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      request.comparison.readings.standard.triangles.values
    let exterior := Data.Gaussian.Norm.Sum.Basic.gaussianSum (request.preparation.loops.aSplit.exterior.map
      (fun entry => (entry.1 : Gaussian.Basic.Canonical) * Topology.Surface.Sewing.SewingRetraction.wordValue value
        entry.2))
    Data.Gaussian.Norm.Basic.normSq ((((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve
      branches).aProgram differential index).integral.model
      request.comparison.common.common.stage).integralSample - (values.aValue + exterior)) < target

/-- The original standard A-period comparison meets its target after paying the weighted holes while retaining the exact
exterior contribution. -/
theorem a_exterior_accurate
    (request : HoleReadings periods segments domains minimum
      floor target extraPoints)
    (values : AccuracyValues normal period
      periodEq request) :
    AExteriorAccurate normal period periodEq
      request values :=
  pay_holes
    (PhysicalLoops.a_standard_accurate normal period periodEq
    request.preparation.loops request.comparison values)
    request.a_holes_accurate

/-- Every original hole correction is paid; the original exterior remains. -/
@[expose] def BExteriorAccurate
    (request : HoleReadings periods segments domains minimum
      floor target extraPoints)
    (values : AccuracyValues normal period
      periodEq request) : Prop :=
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      request.comparison.readings.standard.triangles.values
    let exterior := Data.Gaussian.Norm.Sum.Basic.gaussianSum (request.preparation.loops.bSplit.exterior.map
      (fun entry => (entry.1 : Gaussian.Basic.Canonical) * Topology.Surface.Sewing.SewingRetraction.wordValue value
        entry.2))
    Data.Gaussian.Norm.Basic.normSq ((((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve
      branches).bProgram differential index).integral.model
      request.comparison.common.common.stage).integralSample - (values.bValue + exterior)) < target

/-- The original standard B-period comparison meets its target after paying the weighted holes while retaining the exact
exterior contribution. -/
theorem b_exterior_accurate
    (request : HoleReadings periods segments domains minimum
      floor target extraPoints)
    (values : AccuracyValues normal period
      periodEq request) :
    BExteriorAccurate normal period periodEq
      request values :=
  pay_holes
    (PhysicalLoops.b_standard_accurate normal period periodEq
    request.preparation.loops request.comparison values)
    request.b_holes_accurate

end HoleReadings
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard
