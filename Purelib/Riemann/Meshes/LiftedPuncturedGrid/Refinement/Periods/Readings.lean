module

public import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Periods
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodCanonical
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodRoutes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Tactic.Ring
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Topology.Surface.Sewing.SewingRetraction

/-! # Original period programmes and the same retained refined cochain

The original covered request, its sheet-aware fragments, one shared bank,
one routed-reading cache and one mesh-reading cache supply four independent
error terms. The actual frame-prefix selector determines the lifted word.
No root owner is identified by its coordinate, sheet label or numerical sum.
-/

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement.PeriodFaces

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellBank (ClearancePreparation)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
  (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces
  (MeshWordReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings.ClearGrid
open RegularPrimitiveSplits.SheetEntries (LiftedSources)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
  (RouteRequest RouteRequests canonicalRoute)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries
  (SharedSum)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments (IncludedFragments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests (RouteChartRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (PathFaces)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Topology.Surface.Sewing
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm perTerm_positive)

/-- Four independently retained squared-norm errors compose with the exact factor four. -/
private theorem four_errors (cochain mesh original fragments sample : Gaussian)
    (chart route source period : Rational)
    (chartBound : normSq (cochain - mesh) < chart)
    (routeBound : normSq (mesh - original) < route)
    (sourceBound : normSq (original - fragments) ≤ source)
    (periodBound : normSq (fragments - sample) < period) :
    normSq (cochain - sample) < 4 * (chart + route + source + period) := by
  have first : normSq (cochain - original) < 2 * (chart + route) := by
    rewrite [show cochain - original = (cochain - mesh) + (mesh - original) by ring1]
    exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
      (Arithmetic.mul_lt_mul_of_pos_left_direct (by decide +kernel : (0 : Rational) < 2)
        ((Arithmetic.add_lt_add_right_direct chartBound _).trans
          (Arithmetic.add_lt_add_left_direct routeBound _)))
  have last : normSq (original - sample) < 2 * (source + period) := by
    rewrite [show original - sample = (original - fragments) + (fragments - sample) by ring1]
    exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
      (Arithmetic.mul_lt_mul_of_pos_left_direct (by decide +kernel : (0 : Rational) < 2)
        ((Arithmetic.add_lt_add_left_direct periodBound _).trans_le
          (Arithmetic.add_le_add_direct sourceBound (Basic.le_refl _))))
  rewrite [show cochain - sample = (cochain - original) + (original - sample) by ring1]
  have total := (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Arithmetic.mul_lt_mul_of_pos_left_direct (by decide +kernel : (0 : Rational) < 2)
      ((Arithmetic.add_lt_add_right_direct first _).trans
        (Arithmetic.add_lt_add_left_direct last _)))
  exact total.trans_eq (by ring1)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {original : LiftedPuncturedGrid base}
variable {patches : List (ContinuedNeighborhood curve.polynomial count)}
variable {clearance : ClearancePreparation base.bank.toBranchCellBank patches}
variable {retained : ClearanceRefinement original clearance} {vertex : Fin original.vertices.count}
variable {source : Differential genus}
variable {period : PeriodWalk base.bank.grid (original.vertices.coordinate vertex)
  (original.vertices.owner original.frames vertex) source}
variable (kept : PeriodFaces retained vertex period)
variable {differential : Fin genus} {minimum : Nat} {periodTarget : Rational}
variable {split : IncludedFragments (base := retained.fineBase) period differential minimum periodTarget}
variable {domains : FaceDomainBank retained.fine.frames retained.fineBase.faces.regulars}
variable {entries : Fragment.SplitSheets domains split.cells split.comparison.request.requests}
variable (sources : LiftedSources retained.fine.mesh entries)
variable {points : List Gaussian} {tolerance : Rational} {index : Nat}
variable {budgets : FaceMeshBudgets (standardDifferential differential) points tolerance domains}
variable {numerics : FacePrimitiveBank (standardDifferential differential) index domains}
variable {shared : FaceSharedMeshes budgets numerics}
variable {routeTarget : Rational} (routePositive : 0 < routeTarget)
variable (routing : RouteRequest (LiftedSources.pieces sources) routeTarget)
variable (routingFactory : routing = RouteRequest.build (LiftedSources.pieces sources)
  canonicalRoute routeTarget routePositive)

public section

include routePositive routingFactory in
/-- The cached canonical-route total is the SAME actual refined mesh total.

Only scalar readback laws are used. The given routing cache, original
fragment occurrences and mesh readings are retained; no route request,
root/query, primitive or numerical reading is executed to prove equality.
-/
theorem routed_sum (routed : RouteRequest.Readings routing shared)
    (meshReadings : MeshWordReadings shared kept.view.geometry) : routed.sum = meshReadings.value := by
  have selected := RouteRequests.build_values
    (perTerm routeTarget (LiftedSources.pieces sources).length)
    (perTerm_positive routePositive _) canonicalRoute (LiftedSources.pieces sources) shared
  have requested : routing.requests.values shared =
      (LiftedSources.pieces sources).map (fun piece => RouteContacts.routeValue piece (canonicalRoute piece) shared) :=
    (congrArg (fun request : RouteRequest (LiftedSources.pieces sources) routeTarget =>
      request.requests.values shared) routingFactory).trans selected
  have geometric : SkeletonFaceAssignments.walkFaces retained.fine.mesh
      (retained.included.resplit period.closed.walk (original.vertices.coordinate_onGrid vertex)) kept.view.sheet =
      kept.view.geometry :=
    (congrArg (SkeletonFaceAssignments.walkFaces retained.fine.mesh
      (retained.included.resplit period.closed.walk (original.vertices.coordinate_onGrid vertex)))
      kept.view_sheet).trans kept.view_geometry.symm
  have meshSum := congrArg (fun assigned : PathFaces retained.fine.mesh
      (retained.included.resplit period.closed.walk (original.vertices.coordinate_onGrid vertex)).path =>
      gaussianSum (assigned.values (fun _ route =>
        Face.MeshWords.FaceSharedMeshes.edgeIncrement shared route))) geometric
  exact (routed.sum_eq.trans (congrArg gaussianSum (routed.values_eq.trans requested))).trans
    ((PeriodRoutes.routed_sum sources (original.vertices.coordinate_onGrid vertex)
      retained.included kept.view shared).trans
        (meshSum.trans ((congrArg gaussianSum meshReadings.values_eq).symm.trans meshReadings.value_eq.symm)))

include routePositive routingFactory in
/-- The actual old programme sample and original resplit cochain have their full four-error finite bound.

The original covered-period request pays the programme comparison, the
original SharedSum pays every retained fragment, the given route readings
pay routing, and the same primitive bank pays chart/corner comparison.
Stages and all old charges remain independent explicit inputs.
-/
theorem programme_bound (summary : SharedSum shared entries)
    (routed : RouteRequest.Readings routing shared)
    (meshReadings : MeshWordReadings shared kept.view.geometry)
    {chartTarget : Rational}
    (charts : RouteChartRequest kept.view.geometry.routeSpine (standardDifferential differential)
      domains chartTarget)
    (chartLater : charts.index ≤ index) (triangles : TriangleReadings numerics retained.fine.mesh)
    (periodStage : Nat) (periodLater : split.comparison.stage ≤ periodStage) :
    normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation retained.fine.mesh
      triangles.values) kept.view.geometry.indexed -
        ((period.program differential).integral.model periodStage).integralSample) <
      4 * (2 * (chartTarget + meshReadings.bound) + routeTarget + summary.bound + periodTarget) := by
  have routedComparison := routed.accurate
  rewrite [PeriodWords.source_sum sources summary,
    kept.routed_sum sources routePositive routing routingFactory routed meshReadings] at routedComparison
  have reversed : normSq (meshReadings.value - summary.value) < routeTarget := by
    rewrite [show meshReadings.value - summary.value = -(summary.value - meshReadings.value) by ring1,
      Data.Gaussian.Norm.Basic.normSq_neg]
    exact routedComparison
  have originalIncrement : gaussianSum split.comparison.request.requests.increments = split.fragments.sum :=
    (congrArg gaussianSum split.comparison.request.increments_eq.symm).trans
      (split.comparison.request.primitiveSum_eq.symm.trans split.fragments.original_sum.symm)
  have sourceComparison := summary.accurate
  rewrite [originalIncrement] at sourceComparison
  exact four_errors _ _ _ _ _ _ _ _ _
    (PeriodCanonical.canonical_bound meshReadings charts chartLater triangles)
    reversed sourceComparison (split.accurate periodStage periodLater)

/-- The complete original period, fragment, shared-bank and request inputs of one comparison.

Both differential indices, the numerical and programme stages, the original
programme floor and targets remain data with their whole owners. This
product retains the supplied caches themselves; no field copies or
reconstructed preparation stand in for either side of the comparison.
-/
@[expose] def ComparisonInputs (summary : SharedSum shared entries)
    {chartTarget : Rational}
    (charts : RouteChartRequest kept.view.geometry.routeSpine (standardDifferential differential)
      domains chartTarget)
    (triangles : TriangleReadings numerics retained.fine.mesh) (periodStage : Nat) : Type _ :=
  {value : PeriodFaces retained vertex period ×
      IncludedFragments (base := retained.fineBase) period differential minimum periodTarget ×
      LiftedSources retained.fine.mesh entries × FaceSharedMeshes budgets numerics × SharedSum shared entries ×
      RouteRequest (LiftedSources.pieces sources) routeTarget ×
      RouteChartRequest kept.view.geometry.routeSpine (standardDifferential differential) domains chartTarget ×
      TriangleReadings numerics retained.fine.mesh ×
      (Differential genus × Fin genus × Nat × Nat × Nat) × (Rational × Rational × Rational × Rational) //
    value = (kept, split, sources, shared, summary, routing, charts, triangles,
      (source, differential, minimum, index, periodStage), (periodTarget, routeTarget, chartTarget, tolerance))}

/-- The whole supplied inputs, two exact reading caches, canonical reading and derived four-error bound.

The original programme remains the target owner at its retained model stage.
Its model is not executed to produce another observation; the certificate
relates that same programme to the one cached canonical cochain reading.
-/
abbrev Comparison (summary : SharedSum shared entries)
    {chartTarget : Rational}
    (charts : RouteChartRequest kept.view.geometry.routeSpine (standardDifferential differential)
      domains chartTarget)
    (triangles : TriangleReadings numerics retained.fine.mesh)
    (periodStage : Nat)
    (routeLater : routing.index ≤ index)
    (endpoints : ∀ piece ∈ LiftedSources.pieces sources, piece.first ∈ points ∧ piece.last ∈ points)
    (vertices : ∀ vertex, retained.fine.vertices.coordinate vertex ∈ points) :=
  ComparisonInputs (kept := kept) (sources := sources) (routing := routing) summary charts triangles periodStage ×
  (Σ _routed : {value : RouteRequest.Readings routing shared //
      value = routing.readings shared routeLater endpoints},
  Σ meshReadings : {value : MeshWordReadings shared kept.view.geometry //
      value = MeshWordReadings.build shared vertices kept.view.geometry},
  Σ value : {value : Gaussian // value = SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation retained.fine.mesh triangles.values) kept.view.geometry.indexed},
  {bound : Rational //
    bound = 4 * (2 * (chartTarget + meshReadings.val.bound) + routeTarget + summary.bound + periodTarget) ∧
    normSq (value.val - ((period.program differential).integral.model periodStage).integralSample) < bound})

/-- Read the supplied numerical bank once per actual route and mesh cache, retaining both complete factories.

All geometry, old request polynomials, root/query owners, primitives,
shared values and triangle readings are given. Endpoint membership and
actual stage floors are genuine preparation evidence. They are not
postulated numerical agreement or an arbitrary-payment conclusion.
-/
def compare (summary : SharedSum shared entries)
    {chartTarget : Rational}
    (charts : RouteChartRequest kept.view.geometry.routeSpine (standardDifferential differential)
      domains chartTarget)
    (chartLater : charts.index ≤ index) (triangles : TriangleReadings numerics retained.fine.mesh)
    (periodStage : Nat) (periodLater : split.comparison.stage ≤ periodStage)
    (routeLater : routing.index ≤ index)
    (endpoints : ∀ piece ∈ LiftedSources.pieces sources, piece.first ∈ points ∧ piece.last ∈ points)
    (vertices : ∀ vertex, retained.fine.vertices.coordinate vertex ∈ points) :
    Comparison (kept := kept) (sources := sources) (routing := routing)
      (chartTarget := chartTarget) summary charts triangles periodStage routeLater endpoints vertices :=
  let inputs : ComparisonInputs (kept := kept) (sources := sources) (routing := routing)
      summary charts triangles periodStage :=
    ⟨(kept, split, sources, shared, summary, routing, charts, triangles,
      (source, differential, minimum, index, periodStage), (periodTarget, routeTarget, chartTarget, tolerance)), rfl⟩
  let routed : {value : RouteRequest.Readings routing shared //
      value = routing.readings shared routeLater endpoints} :=
    ⟨routing.readings shared routeLater endpoints, rfl⟩
  let meshReadings : {value : MeshWordReadings shared kept.view.geometry //
      value = MeshWordReadings.build shared vertices kept.view.geometry} :=
    ⟨MeshWordReadings.build shared vertices kept.view.geometry, rfl⟩
  let value : {value : Gaussian // value = SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation retained.fine.mesh triangles.values) kept.view.geometry.indexed} :=
    ⟨SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation retained.fine.mesh triangles.values)
      kept.view.geometry.indexed, rfl⟩
  ⟨inputs, routed, meshReadings, value,
    4 * (2 * (chartTarget + meshReadings.val.bound) + routeTarget + summary.bound + periodTarget), rfl,
    Eq.mpr (congrArg (fun actual : Gaussian =>
      normSq (actual - ((period.program differential).integral.model periodStage).integralSample) <
        4 * (2 * (chartTarget + meshReadings.val.bound) + routeTarget + summary.bound + periodTarget)) value.property)
      (kept.programme_bound sources routePositive routing routingFactory summary routed.val meshReadings.val
        charts chartLater triangles periodStage periodLater)⟩

namespace Comparison

variable {kept sources routing} {summary : SharedSum shared entries} {chartTarget : Rational}
variable {charts : RouteChartRequest kept.view.geometry.routeSpine (standardDifferential differential)
  domains chartTarget}
variable {triangles : TriangleReadings numerics retained.fine.mesh} {periodStage : Nat}
variable {routeLater : routing.index ≤ index}
variable {endpoints : ∀ piece ∈ LiftedSources.pieces sources, piece.first ∈ points ∧ piece.last ∈ points}
variable {vertices : ∀ vertex, retained.fine.vertices.coordinate vertex ∈ points}
variable (compared : Comparison (kept := kept) (sources := sources) (routing := routing)
  summary charts triangles periodStage routeLater endpoints vertices)

/-- Read the same complete period, source, numerical and request inputs retained as actual data. -/
@[expose] def inputs : ComparisonInputs (kept := kept) (sources := sources) (routing := routing)
    summary charts triangles periodStage := compared.1

/-- Read the one retained canonical-route reading cache without repeating its observation. -/
@[expose] def routed : RouteRequest.Readings routing shared := compared.2.1.val

/-- Read the one retained mesh-word reading cache on the same actual period face geometry. -/
@[expose] def meshReadings : MeshWordReadings shared kept.view.geometry := compared.2.2.1.val

/-- Read the actual once computed canonical cochain value on the given triangle bank. -/
@[expose] def value : Gaussian := compared.2.2.2.1.val

/-- Read the computed bound on those same four retained error contributions. -/
@[expose] def bound : Rational := compared.2.2.2.2.val

/-- Every complete input, differential, stage and target retains its original given value. -/
theorem inputs_eq : compared.inputs.val = (kept, split, sources, shared, summary, routing, charts, triangles,
    (source, differential, minimum, index, periodStage), (periodTarget, routeTarget, chartTarget, tolerance)) :=
  compared.1.property

/-- The route cache retains its one actual original reading factory and preparation evidence. -/
theorem routed_eq : compared.routed = routing.readings shared routeLater endpoints := compared.2.1.property

/-- The mesh cache retains its one original whole reading factory on the same supplied bank. -/
theorem meshReadings_eq : compared.meshReadings = MeshWordReadings.build shared vertices kept.view.geometry :=
  compared.2.2.1.property

/-- The stored cochain scalar reads the actual original resplit period word on the supplied numerical bank. -/
theorem value_eq : compared.value = SewingRetraction.wordValue
    (CanonicalEdgeValues.edgeValuation retained.fine.mesh triangles.values) kept.view.geometry.indexed :=
  compared.2.2.2.1.property

/-- The retained bound is exactly the same four-error allocation from the original caches and targets. -/
theorem bound_eq : compared.bound =
    4 * (2 * (chartTarget + compared.meshReadings.bound) + routeTarget + summary.bound + periodTarget) :=
  compared.2.2.2.2.property.1

/-- The cached canonical reading and the same original programme sample obey the derived finite bound. -/
theorem accurate : normSq (compared.value -
    ((period.program differential).integral.model periodStage).integralSample) < compared.bound :=
  compared.2.2.2.2.property.2

end Comparison

end

end Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement.PeriodFaces
