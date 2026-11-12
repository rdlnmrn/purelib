module
import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningValues
public import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourRoutes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

open Purelib.Topology.Surface.Sewing

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry

open Purelib.Integration

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-!
# Corrected period programs on the shared surface edge valuation

Face-corner and chart-change errors are paid separately. The resulting
antisymmetric valuation reads the actual corrected A/B words, so the ordered
area formula applies with all physical and signed-face residuals retained.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SurfacePeriods.AssignedSegments

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Branches.BranchCellBank curve branches higher}
  {frames : SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
    {ambient : Rational.Box}

/-- Retain each assigned face occurrence instead of choosing a replacement
route from the projected endpoints. -/
@[expose] def cornerRoutes : ∀ {start finish : Gaussian.Basic.Canonical} {path : Geometry.ClearPath
  curve.polynomial ambient start finish}
    {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
      Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
      Paths.PreparedPathDecomposition.PreparedPath.CoveredSegments prepared}
    (assigned : PreparedFaceSegments.AssignedSegments mesh pieces),
      MeshPathWalks.RouteSpine mesh assigned.indexed
  | _, _, _, _, _, _, .nil _ _ => .nil
  | _, _, _, _, _, _, .cons placement remaining => .cons placement.location
    (AssignedSegments.cornerRoutes remaining)

/-- The original assigned corner route values are exactly the retained face-corner increments. -/
theorem cornerRoutes_values {domains : Face.DomainBanks.FaceDomainBank frames
  faces.regulars} {differential : Differentials.Basic.Differential genus} {index : Nat}
    {shared : Face.PrimitiveData.FacePrimitiveBank differential index domains}
      (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    ∀ {start finish : Gaussian.Basic.Canonical} {path : Geometry.ClearPath curve.polynomial ambient start
      finish}
      {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
        Paths.PreparedPathDecomposition.PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces),
      (AssignedSegments.cornerRoutes assigned).values (fun _
        route => route.sourceEdge.increment readings.values) =
        Cut.CornerRequests.AssignedSegments.cornerIncrements shared assigned
  | _, _, _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, _, _, .cons placement remaining =>
      congrArg₂ List.cons (readings.route_increment placement.location)
        (AssignedSegments.cornerRoutes_values
        readings remaining)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SurfacePeriods.AssignedSegments

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SurfacePeriods.Prepared

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests (RouteChartRequest)

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : OrderedBranchPairs.Ordered.Paired ordered}

/-- Select the original corrected A or B word for the retained period row. -/
@[expose] def cornerWord (prepared : PeriodPrograms.Prepared paired) (index :
  Fin genus) (bSide : Bool) :=
  if bSide then prepared.bWord index else prepared.aWord index

/-- The original assigned corner segments index exactly the selected corrected A or B word. -/
theorem cornerAssigned_indexed (prepared : PeriodPrograms.Prepared paired)
  (index : Fin genus) (bSide : Bool) :
    (prepared.cornerAssigned index bSide).indexed =
      Prepared.cornerWord prepared index bSide := by
  have same := (prepared.cornerGeometry index bSide).assign_indexed (prepared.cornerSegments index bSide).pieces
  cases bSide
  · exact same
  · exact same

/-- The chart comparison on the exact original assigned corner route for one standard differential and period side. -/
@[expose] def CornerChartRequest (prepared : PeriodPrograms.Prepared paired)
  (domains : Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (differential : Fin genus) (target : Fraction.Rational) (index : Fin genus) (bSide : Bool) :=
  RouteChartRequest
    (AssignedSegments.cornerRoutes (prepared.cornerAssigned
    index bSide))
    (Periods.PeriodMatrix.standardDifferential differential) domains target

set_option genInjectivity false in
/-- The two retained chart comparisons for the original A and B corner words. -/
structure CornerChartRow (prepared : PeriodPrograms.Prepared paired) (domains
  : Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (differential : Fin genus) (target : Fraction.Rational) (index : Fin genus) where
  /-- The actual original A-word chart comparison. -/ a :
    CornerChartRequest prepared domains differential
    target index false
  /-- The actual original B-word chart comparison. -/ b :
    CornerChartRequest prepared domains differential
    target index true

constructive_injectivity CornerChartRow

/-- Prepare both original A/B corner route chart requests at the shared positive target. -/
@[expose] def CornerChartRow.build (prepared : PeriodPrograms.Prepared paired)
  (domains : Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (differential : Fin genus) (target : Fraction.Rational) (positive : 0 < target) (index : Fin genus) :
    CornerChartRow prepared domains differential
      target index :=
  ⟨RouteChartRequest.build _ _ domains target positive,
    RouteChartRequest.build _ _ domains target positive⟩

/-- The maximum sufficient stage of the retained A and B chart requests. -/
@[expose] def CornerChartRow.minimum {prepared : PeriodPrograms.Prepared
  paired} {domains : Face.DomainBanks.FaceDomainBank lifted.frames
  base.faces.regulars}
    {differential : Fin genus} {target : Fraction.Rational} {index : Fin genus}
    (row : CornerChartRow prepared domains
      differential target index) : Nat := max row.a.index row.b.index

set_option genInjectivity false in
/-- The original corrected period family and chart comparisons on one actual shared numerical surface bank.

The retained chart floor and triangle readings certify the same original numerical owner used by both A and B programs.
-/
structure SurfaceRequest (prepared : PeriodPrograms.Prepared paired) (domains
  : Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (differential : Fin genus) (target : Fraction.Rational) (minimumStage : Nat) where
  /-- The retained local corner and chart allowance. -/ pieceTarget : Fraction.Rational
  /-- The local allowance is one quarter of the original whole target. -/ pieceTarget_eq : pieceTarget = target / 4
  /-- The actual retained A/B corner chart requests for every original period row. -/ charts :
    Vector.DependentVector (fun index : Fin genus =>
    CornerChartRow prepared domains differential
    pieceTarget index)
  /-- The cached common sufficient chart stage. -/ chartIndex : Nat
  /-- The chart stage is exactly the maximum of the retained row requirements. -/ chartIndex_eq : chartIndex =
    charts.maximum (fun _ row => row.minimum)
  /-- The retained floor for the actual shared numerical surface bank. -/ numericalFloor : Nat
  /-- The retained chart stage is at most the numerical floor. -/ chartIndex_le_floor : chartIndex ≤ numericalFloor
  /-- The actual original corner family using the retained numerical bank. -/ family :
    CornerFamily prepared domains differential pieceTarget
    numericalFloor minimumStage
  /-- The original triangle primitive readings on that same numerical bank. -/ triangles :
    TrianglePrimitiveReadings.TriangleReadings family.numerics lifted.mesh

constructive_injectivity SurfaceRequest

set_option genInjectivity false in
/-- Cache both scalar selection phases before constructing any numerical
primitive. Different differentials can then share the same surface index. -/
structure SurfaceBudget (prepared : PeriodPrograms.Prepared paired) (domains :
  Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (differential : Fin genus) (target : Fraction.Rational) where
  /-- The retained local corner and chart allowance. -/ pieceTarget : Fraction.Rational
  /-- The local allowance is one quarter of the original whole target. -/ pieceTarget_eq : pieceTarget = target / 4
  /-- The actual retained A/B corner chart requests for every original period row. -/ charts :
    Vector.DependentVector (fun index : Fin genus =>
    CornerChartRow prepared domains differential
    pieceTarget index)
  /-- The cached common sufficient chart stage. -/ chartIndex : Nat
  /-- The chart stage is exactly the maximum of the retained row requirements. -/ chartIndex_eq : chartIndex =
    charts.maximum (fun _ row => row.minimum)
  /-- The actual original corner scalar requests prepared before numerical sampling. -/ scalars :
    CornerFamily.CornerScalars prepared domains differential pieceTarget
  /-- The cached stage sufficient for both chart and scalar requirements. -/ minimum : Nat
  /-- The sufficient stage is exactly the maximum of the retained chart and scalar minima. -/ minimum_eq : minimum = max
    chartIndex scalars.minimum

constructive_injectivity SurfaceBudget

namespace SurfaceBudget

/-- Cache the original chart and corner scalar selections with a shared sufficient numerical stage. -/
@[expose] def build (prepared : PeriodPrograms.Prepared paired) (domains :
  Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (differential : Fin genus) (target : Fraction.Rational) (positive : 0 < target) :
    SurfaceBudget prepared domains differential target
      :=
  let pieceTarget := target / 4
  have piecePositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
  let charts := Vector.DependentVector.ofFn
    (CornerChartRow.build prepared domains
    differential pieceTarget piecePositive)
  let chartIndex := charts.maximum (fun _ row => row.minimum)
  let scalars := CornerFamily.CornerScalars.build prepared domains
    differential pieceTarget piecePositive
  ⟨pieceTarget, rfl, charts, chartIndex, rfl, scalars, max chartIndex scalars.minimum, rfl⟩

variable {prepared : PeriodPrograms.Prepared paired} {domains :
  Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {differential : Fin genus} {target : Fraction.Rational}

/-- Reuse the supplied original numerical bank at a sufficient stage to construct the retained A/B surface request. -/
@[expose] def requestWith (budget : SurfaceBudget
  prepared domains differential target) {numericalIndex : Nat}
    (later : budget.minimum ≤ numericalIndex)
    (numerics : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains)
    (minimumStage : Nat) : SurfaceRequest prepared
      domains differential target minimumStage := by
  have bounds := budget.minimum_eq ▸ later
  have scalarLater : budget.scalars.minimum ≤ numericalIndex := (Nat.Order.le_max_right _ _).trans bounds
  let family : CornerFamily prepared domains differential
    budget.pieceTarget numericalIndex minimumStage :=
    ⟨budget.scalars, numericalIndex, (Nat.le_antisymm (Nat.Order.max_le (Nat.le_refl _) scalarLater)
      (Nat.Order.le_max_left _ _)).symm,
      numerics, budget.scalars.requestWith scalarLater numerics minimumStage⟩
  exact ⟨budget.pieceTarget, budget.pieceTarget_eq, budget.charts, budget.chartIndex, budget.chartIndex_eq,
    numericalIndex, (Nat.Order.le_max_left _ _).trans bounds, family,
      TrianglePrimitiveReadings.TriangleReadings.build numerics lifted.mesh⟩

/-- Reusing a numerical bank preserves its exact original stage. -/
theorem requestWith_index (budget : SurfaceBudget
  prepared domains differential target) {numericalIndex : Nat}
    (later : budget.minimum ≤ numericalIndex)
    (numerics : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains)
    (minimumStage : Nat) : (budget.requestWith later numerics minimumStage).family.numericalIndex = numericalIndex :=
      rfl

/-- The constructed surface request retains the very same supplied numerical bank. -/
theorem requestWith_numerics (budget : SurfaceBudget
  prepared domains differential target) {numericalIndex : Nat}
    (later : budget.minimum ≤ numericalIndex)
    (numerics : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains)
    (minimumStage : Nat) : HEq (budget.requestWith later numerics minimumStage).family.numerics numerics := HEq.rfl

end SurfaceBudget

namespace SurfaceRequest

variable {prepared : PeriodPrograms.Prepared paired} {domains :
  Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {differential : Fin genus} {target : Fraction.Rational} {minimumStage : Nat}

/-- Prepare the original scalar budget and one shared numerical primitive bank, then retain both A/B surface
comparisons. -/
@[expose] def build (prepared : PeriodPrograms.Prepared paired) (domains :
  Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (differential : Fin genus) (target : Fraction.Rational) (positive : 0 < target) (minimumStage : Nat) :
    SurfaceRequest prepared domains differential
      target minimumStage :=
  let budget := SurfaceBudget.build prepared domains
    differential target positive
  let numerics := Face.PrimitiveData.FacePrimitiveBank.build
    (Periods.PeriodMatrix.standardDifferential differential) budget.minimum domains
  budget.requestWith (Nat.le_refl _) numerics minimumStage

/-- The canonical antisymmetric edge valuation from the actual retained triangle readings. -/
@[expose] def value (request : SurfaceRequest prepared
  domains differential target minimumStage) :
    Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical :=
      CanonicalEdgeValues.edgeValuation lifted.mesh request.triangles.values

/-- The original retained edge valuation changes sign under edge reversal. -/
theorem value_reverse (request : SurfaceRequest
  prepared domains differential target minimumStage)
    (edge : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count) : request.value edge.reverse = -request.value
      edge :=
  CanonicalEdgeValues.edgeValuation_reverse _ _ edge

/-- The actual retained family numerical stage is sufficient for every chart request. -/
private theorem chartIndex_le (request :
  SurfaceRequest prepared domains differential target
  minimumStage) :
    request.chartIndex ≤ request.family.numericalIndex := by
  rw [request.family.numericalIndex_eq]
  exact request.chartIndex_le_floor.trans (Nat.Order.le_max_left _ _)

/-- Two squared-norm comparison errors below one quarter of the same target give a combined error below the whole
target. -/
private theorem pay {x y z : Gaussian.Basic.Canonical} {pieceTarget target : Fraction.Rational}
    (same : pieceTarget = target / 4) (first : Gaussian.Norm.Basic.normSq (x - y) < pieceTarget) (second :
      Gaussian.Norm.Basic.normSq (y - z) < pieceTarget) :
    Gaussian.Norm.Basic.normSq (x - z) < target := by
  rw [show x - z = (x - y) + (y - z) by ring1]
  have paid := Fraction.Order.Arithmetic.add_lt_add_direct
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2) first)
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2) second)
  have total : 2 * pieceTarget + 2 * pieceTarget = target := by
    rw [same, show 2 * (target / 4) + 2 * (target / 4) = (target / 4) * 4 by ring1]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  apply (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
  calc
    2 * (Gaussian.Norm.Basic.normSq (x - y) + Gaussian.Norm.Basic.normSq (y - z)) = 2 *
      Gaussian.Norm.Basic.normSq (x - y) + 2 * Gaussian.Norm.Basic.normSq (y - z) := by ring1
    _ < target := paid.trans_eq total

/-- The actual canonical A-word value approximates the original A-period program at every sufficient later model stage.
-/
theorem a_accurate (request : SurfaceRequest prepared
  domains differential target minimumStage)
    (index : Fin genus) (stage : Nat) (later : request.family.requested.stage ≤ stage) :
    Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue request.value
      (prepared.aWord index) -
      ((prepared.periodData.aProgram differential index).integral.model stage).integralSample) < target := by
  have chartLater : (request.charts.get index).a.index ≤ request.family.numericalIndex :=
    (Nat.Order.le_max_left _ _).trans ((request.charts.get_le_maximum (fun _ row => row.minimum) index).trans
      (request.chartIndex_eq ▸ request.chartIndex_le))
  have chart := (request.charts.get index).a.accurate chartLater request.triangles
  rw [AssignedSegments.cornerRoutes_values,
    Prepared.cornerAssigned_indexed prepared] at chart
  change Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue request.value
    (prepared.aWord index) - _) < request.pieceTarget at chart
  rw [← (request.family.requested.rows.get index).a.value_eq] at chart
  exact SurfaceRequest.pay request.pieceTarget_eq
    chart (request.family.requested.a_accurate index stage later)

/-- The actual canonical B-word value approximates the original B-period program at every sufficient later model stage.
-/
theorem b_accurate (request : SurfaceRequest prepared
  domains differential target minimumStage)
    (index : Fin genus) (stage : Nat) (later : request.family.requested.stage ≤ stage) :
    Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue request.value
      (prepared.bWord index) -
      ((prepared.periodData.bProgram differential index).integral.model stage).integralSample) < target := by
  have chartLater : (request.charts.get index).b.index ≤ request.family.numericalIndex :=
    (Nat.Order.le_max_right _ _).trans ((request.charts.get_le_maximum (fun _ row => row.minimum) index).trans
      (request.chartIndex_eq ▸ request.chartIndex_le))
  have chart := (request.charts.get index).b.accurate chartLater request.triangles
  rw [AssignedSegments.cornerRoutes_values,
    Prepared.cornerAssigned_indexed prepared] at chart
  change Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue request.value
    (prepared.bWord index) - _) < request.pieceTarget at chart
  rw [← (request.family.requested.rows.get index).b.value_eq] at chart
  exact SurfaceRequest.pay request.pieceTarget_eq
    chart (request.family.requested.b_accurate index stage later)

/-- The actual closed-word reading approaches its retained canonical period combination with both original residuals.

The supplied coefficient caches belong to the same integral cut coordinates.
Every A and B sample uses the original prepared period family and one common
later stage. The physical remainder and face correction remain the literal
values of the same retained surface bank; neither is assumed to vanish.
-/
theorem word_accurate (request : SurfaceRequest prepared domains differential target minimumStage)
    {cut : PeriodCoordinates.CutBank prepared}
    {word : List (Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count)}
    {row : PeriodCoordinates.ClosedCoordinates word cut.integral}
    (coordinates : SpanningRows.BasisCoordinates cut row)
    (aCoefficients : Periods.WeightedPeriods.Coefficients coordinates.a)
    (bCoefficients : Periods.WeightedPeriods.Coefficients coordinates.b)
    (stage : Nat) (later : request.family.requested.stage ≤ stage) :
    Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue request.value word -
      (aCoefficients.combine (fun index =>
          ((prepared.periodData.aProgram differential index).integral.model stage).integralSample) +
        bCoefficients.combine (fun index =>
          ((prepared.periodData.bProgram differential index).integral.model stage).integralSample) +
        coordinates.physicalValue request.value + coordinates.faceResidual request.value)) ≤
      2 * (aCoefficients.charge (fun _ => target) + bCoefficients.charge (fun _ => target)) := by
  let aWords := fun index => SewingRetraction.wordValue request.value (prepared.aWord index)
  let bWords := fun index => SewingRetraction.wordValue request.value (prepared.bWord index)
  let aSamples := fun index =>
    ((prepared.periodData.aProgram differential index).integral.model stage).integralSample
  let bSamples := fun index =>
    ((prepared.periodData.bProgram differential index).integral.model stage).integralSample
  have aBound := aCoefficients.normSq_difference_le aWords aSamples (fun _ => target)
    (fun index => (Gaussian.Norm.Basic.normSq_eq_canonical _).symm.trans_le
      (request.a_accurate index stage later).le)
  have bBound := bCoefficients.normSq_difference_le bWords bSamples (fun _ => target)
    (fun index => (Gaussian.Norm.Basic.normSq_eq_canonical _).symm.trans_le
      (request.b_accurate index stage later).le)
  have aNorm := (Gaussian.Norm.Basic.normSq_eq_canonical _).trans_le aBound
  have bNorm := (Gaussian.Norm.Basic.normSq_eq_canonical _).trans_le bBound
  have periodEq : coordinates.periodValue request.value =
      aCoefficients.combine aWords + bCoefficients.combine bWords := by
    change Algebra.FiniteSum.Fin.sumFin (fun index : Fin genus =>
        (coordinates.a index : Gaussian.Basic.Canonical) * aWords index +
          (coordinates.b index : Gaussian.Basic.Canonical) * bWords index) = _
    rewrite [aCoefficients.combine_eq, bCoefficients.combine_eq,
      ← Algebra.FiniteSum.Fin.sumFin_add]
    rfl
  have wordEq := coordinates.word_value_eq request.value request.value_reverse
  have difference : SewingRetraction.wordValue request.value word -
      (aCoefficients.combine aSamples + bCoefficients.combine bSamples +
        coordinates.physicalValue request.value + coordinates.faceResidual request.value) =
      (aCoefficients.combine aWords - aCoefficients.combine aSamples) +
        (bCoefficients.combine bWords - bCoefficients.combine bSamples) := by
    rewrite [wordEq, periodEq]
    ring1
  rewrite [difference]
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct aNorm bNorm) (by decide +kernel))

/-- The valuation approximating the actual programs is consumed directly by
the ordered identity. Physical boundaries and regular-face areas remain. -/
theorem area_formula (request : SurfaceRequest
  prepared domains differential target minimumStage) :
    lifted.edges.chainArea lifted.vertices request.value base.bank.exterior sheet + prepared.pairing request.value =
      paired.rows.internalArea request.value + paired.ending.internalArea request.value +
        Path.BoundaryRibbon.area (SewingRetraction.wordValue request.value paired.rows.word)
          (-SewingRetraction.wordValue request.value (paired.reference.hole.liftedBoundary
            lifted.vertices lifted.edges)) +
        paired.ending.exteriorArea request.value (SewingRetraction.wordValue request.value
          paired.rows.word) +
        Topology.Mesh.RetracingWords.AreaTerm.total request.value ordered.prepared.compiled.areaTerms :=
  prepared.area_formula request.value request.value_reverse

end SurfaceRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SurfacePeriods.Prepared
