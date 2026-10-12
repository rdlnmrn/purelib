module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RowCoefficients
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularBoundaryControl
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EvenExteriorCorrection
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Approximation.Budget.SynchronizedSamples
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalExteriorComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularEnergyCompletion
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

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Original even-degree standard A/B readings with both physical corrections
paid on the same numerical bank and the original cached coefficient rows. -/

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

namespace EvenReadings

set_option genInjectivity false in
/-- Original even-degree physical loops with paid exterior requests for both period rows.

The cached row coefficients determine one positive component allowance, while the retained request also pays the
prescribed squared loss. -/
structure EvenPreparation
    (periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared components)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (floor : Nat) (target loss : Fraction.Rational) : Type 3 where
  /-- The original shared physical-loop decomposition for both period rows. -/ loops :
    PhysicalLoops periods
  /-- The cached exterior coefficients of the original A-row split. -/ a :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.RowCoefficients.ExteriorRowCoefficients loops.aSplit
  /-- The cached exterior coefficients of the original B-row split. -/ b :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.RowCoefficients.ExteriorRowCoefficients loops.bSplit
  /-- The cached A-row per-component quarter-target allowance. -/ aTarget : Fraction.Rational
  /-- The A-row allowance is computed from its retained coefficients. -/ aTarget_eq : aTarget =
    a.coefficients.perComponent (target / 4)
  /-- The cached B-row per-component quarter-target allowance. -/ bTarget : Fraction.Rational
  /-- The B-row allowance is computed from its retained coefficients. -/ bTarget_eq : bTarget =
    b.coefficients.perComponent (target / 4)
  /-- The shared exterior component allowance. -/ allowance : Fraction.Rational
  /-- The shared allowance is the minimum of both cached row allowances. -/ allowance_eq : allowance = min aTarget
    bTarget
  /-- The shared component allowance is positive. -/ positive : 0 < allowance
  /-- The original exterior surface preparation for the retained standard differential. -/ exterior :
    Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains (Periods.PeriodMatrix.standardDifferential differential)
  /-- The paid exterior request at the original allowance, squared loss and stage floor. -/ ready :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request exterior allowance (loss ^
    2) floor

constructive_injectivity EvenPreparation

set_option genInjectivity false in
/-- The even exterior control on the same original numerical bank and triangle readings, with every retained exterior
word small. -/
structure EvenExteriorReadings
    {periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared components}
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
      {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
    {floor : Nat} {target loss : Fraction.Rational}
    (preparation : Hyperelliptic.Meshes.PuncturedGrid.Standard.EvenReadings.EvenPreparation periods domains regular
      floor target loss)
    (numericalIndex : Nat)
    (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains)
    (triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) :
      Type 3 where
  /-- The evaluated exterior control at the retained allowance and loss. -/ control :
    RegularBoundaryControl
    preparation.exterior preparation.allowance loss floor
  /-- The acquired exterior control uses exactly the supplied original numerical bank. -/ shared_eq : HEq
    control.acquired.shared shared
  /-- Every original exterior word meets the shared component allowance on these triangle readings. -/ boundary_small :
    ∀ word ∈ lifted.exteriorBoundaries, Data.Gaussian.Norm.Basic.normSq
    (Topology.Surface.Sewing.SewingRetraction.wordValue
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh triangles.values) word) <
      preparation.allowance

constructive_injectivity EvenExteriorReadings

/-- The original hole readings and matching even exterior control, retaining exact identity of the prepared physical
loops. -/
def EvenPayload
    {periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared components}
    (segments : Data.Vector.DependentVector (fun entry =>
      Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (prepared.programs.programs entry).period))
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
      {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
    {floor : Nat} {target loss : Fraction.Rational}
    (preparation : Hyperelliptic.Meshes.PuncturedGrid.Standard.EvenReadings.EvenPreparation periods domains regular
      floor target loss)
    (minimum : Nat) (extraPoints : List Gaussian.Basic.Canonical) : Type 3 :=
  (holes : HoleReadings periods segments domains minimum (max
    floor preparation.ready.index) (target / 4) extraPoints) ×
    { _exterior : Hyperelliptic.Meshes.PuncturedGrid.Standard.EvenReadings.EvenExteriorReadings preparation
      holes.comparison.readings.standard.original.shared.numericalIndex
        holes.comparison.readings.standard.original.shared.numerics holes.comparison.readings.standard.triangles //
      holes.preparation.loops = preparation.loops }

end EvenReadings

set_option genInjectivity false in
/-- The original even-degree A/B period readings with both physical corrections paid on a shared numerical bank. -/
structure EvenReadings
    (periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared components)
    (segments : Data.Vector.DependentVector (fun entry =>
      Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (prepared.programs.programs entry).period))
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (minimum floor : Nat) (target loss : Fraction.Rational) (extraPoints : List Gaussian.Basic.Canonical) : Type 3 where
  /-- The retained original loop rows, component allowance and exterior request. -/ preparation :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.EvenReadings.EvenPreparation periods domains regular floor target loss
  /-- The hole and exterior readings on the same original bank and physical loops. -/ payload :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.EvenReadings.EvenPayload segments preparation minimum extraPoints

constructive_injectivity EvenReadings

namespace EvenReadings

/-- Prepare the original even-degree loop corrections and acquire both rows on one sufficiently late bank.

The construction reuses the cached coefficient rows, pays weighted hole requests and evaluates the exterior control on
the exact same shared numerics. -/
def build (periods : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods.ChordPeriods row.span prepared
  components)
    (segments : Data.Vector.DependentVector (fun entry =>
      Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (prepared.programs.programs entry).period))
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (degree : curve.polynomial.natDegree = 2 * genus + 2)
    (minimum floor : Nat) (target loss : Fraction.Rational) (positive : 0 < target) (lossPositive : 0 < loss)
    (extraPoints : List Gaussian := []) :
    EvenReadings periods segments domains regular minimum floor
      target loss extraPoints := by
  let loops := PhysicalLoops.build periods
  let a := Hyperelliptic.Meshes.PuncturedGrid.Exterior.RowCoefficients.ExteriorRowCoefficients.build loops.aSplit
  let b := Hyperelliptic.Meshes.PuncturedGrid.Exterior.RowCoefficients.ExteriorRowCoefficients.build loops.bSplit
  let aTarget := a.coefficients.perComponent (target / 4)
  let bTarget := b.coefficients.perComponent (target / 4)
  let allowance := min aTarget bTarget
  have quarterPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
  have allowancePositive : 0 < allowance := Fraction.Order.Basic.lt_min
    (a.coefficients.perComponent_positive quarterPositive) (b.coefficients.perComponent_positive quarterPositive)
  have squarePositive : 0 < loss ^ 2 := by
    rw [pow_two]
    exact Fraction.Order.Arithmetic.mul_pos_direct lossPositive lossPositive
  let exterior :=
    Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
    regular domains (Periods.PeriodMatrix.standardDifferential differential)
  let ready := Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.build exterior
    allowance (loss ^ 2) allowancePositive squarePositive floor
  let contacts := Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations.build
    lifted.cutPolygon.patch lifted.cutBoundaryPairs
    (Periods.PeriodMatrix.standardDifferential differential) domains
  have holePositive := Fraction.Order.Field.div_pos_direct quarterPositive (by decide : (0 : Fraction.Rational) < 4)
  let preparation : Hyperelliptic.Meshes.PuncturedGrid.Standard.HoleReadings.HolePreparation periods domains (target /
    4) (max floor ready.index) :=
    ⟨loops, contacts,
      Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection.HolePhysicalRequest.build contacts
        loops.aSplit.coefficients ((target / 4) / 4) holePositive (max floor ready.index),
      Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection.HolePhysicalRequest.build contacts
        loops.bSplit.coefficients ((target / 4) / 4) holePositive (max floor ready.index)⟩
  let comparison := Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation.PeriodRelationReadings.build periods
    segments domains minimum
    (max preparation.a.index preparation.b.index) ((target / 4) / 4) holePositive extraPoints
  let holes : HoleReadings periods segments domains minimum
    (max floor ready.index) (target / 4) extraPoints :=
    ⟨preparation, comparison⟩
  have later : ready.index ≤ holes.comparison.readings.standard.original.shared.numericalIndex :=
    (Data.Nat.Order.le_max_right _ _).trans (preparation.a.floor_le.trans ((Data.Nat.Order.le_max_left _ _).trans
      holes.numerical_later))
  let sample := Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample.build cap
    (Periods.PeriodMatrix.standardDifferential differential)
    holes.comparison.readings.standard.original.shared.numericalIndex collar.box
  let control :=
    RegularBoundaryControl.evaluate
    ready degree lossPositive sample
    holes.comparison.readings.standard.original.shared.numerics later
  let initial : Hyperelliptic.Meshes.PuncturedGrid.Standard.EvenReadings.EvenPreparation periods domains regular floor
    target loss :=
    ⟨loops, a, b, aTarget, rfl, bTarget, rfl, allowance, rfl, allowancePositive, exterior, ready⟩
  exact ⟨initial, ⟨holes, ⟨⟨control, HEq.rfl,
    control.boundary_words_small holes.comparison.readings.standard.triangles⟩, rfl⟩⟩⟩

end EvenReadings
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard
