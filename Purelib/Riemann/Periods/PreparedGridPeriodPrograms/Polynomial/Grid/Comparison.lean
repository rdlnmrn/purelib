module

public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Grid.Readings
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Grid.Routes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents.Polynomial.Accuracy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.Polynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodCanonical.Polynomial
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents.Polynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Grid
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Primitive.Comparison
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Readings.UniformPreparedRequests.Covered
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.SewingRetraction

/-! # Fresh canonical ordinary-numerator models on the same retained P bank

Given the actual target-specific fragment geometry, reference word,
route/chart requests and supplied P bank, construct all physical/numerical
comparisons once. Whole model transports preserve the original Work and
Models. The signed bound includes the actual model charge, routing error,
fixed-grid mesh charge and actual chart comparison; individual primitive
jumps and offsets remain unchanged.
-/

public section

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine.GridFragments

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces (MeshWordReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords (RouteRequest)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Cast.Order
open Purelib.Data.Rat.Fraction.Order
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)

variable {parameter : Canonical} {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {framed : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
    {lifted : LiftedPuncturedGrid framed} {vertex : Fin lifted.vertices.count} {source : Differential 1}
    {walk : PeriodWalk framed.bank.grid (lifted.vertices.coordinate vertex)
      (lifted.vertices.owner lifted.frames vertex) source}
    {spine : PolynomialSpine (parameter := parameter) (frame := frame) walk}
    {sourceStart periodStart : Nat} {tolerance : Rational} {positive : 0 < tolerance}
    {selection : PrimitiveSelection walk sourceStart periodStart tolerance positive}
    {domains : FaceDomainBank lifted.frames framed.faces.regulars}
    {fragments : GridFragments lifted vertex walk spine selection domains}
    {points : List Canonical} {oldTolerance : Rational} {oldStage : Nat} {oldNumerator : CoefficientPolynomial}
    {oldBudgets : FaceMeshBudgets (standardDifferential (0 : Fin 1)) points oldTolerance
      (numerator := oldNumerator) domains}
    {oldPrimitives : FacePrimitiveBank (standardDifferential (0 : Fin 1)) oldStage
      (numerator := oldNumerator) domains}
    {oldLater : oldBudgets.index ≤ oldStage}
    {acquired : FaceSharedMeshes.Acquisition oldBudgets oldPrimitives oldLater}
    {pointPrefix before after : List Canonical}
    (reference : Reference fragments acquired pointPrefix before after)
    {ordinary : Ordinary (Fibre.frameCurve frame).polynomial} {target : Rational} {targetPositive : 0 < target}
    (contacts : Contacts fragments ordinary target targetPositive)
    {numericTolerance : Rational} {stage floor modelStage : Nat}
    {budgets : FaceMeshBudgets (standardDifferential (0 : Fin 1)) points numericTolerance
      (numerator := ordinary.numerator) domains}
    {primitives : FacePrimitiveBank (standardDifferential (0 : Fin 1)) stage
      (numerator := ordinary.numerator) domains}
    (shared : FaceSharedMeshes budgets primitives)
    (triangles : {value : TriangleReadings primitives lifted.mesh //
      value = TriangleReadings.build primitives lifted.mesh})
    (work : PolynomialWork selection.1.val.requests.covered floor ordinary.val) (models : work.Models modelStage)
    (routeLater : contacts.route.index ≤ stage) (chartLater : contacts.charts.index ≤ stage)

/-- Exact retained physical/reference/contact/numerical/model inputs and their independent actual stages. -/
@[expose] def Comparison.Inputs : Type _ :=
  {inputs : Reference fragments acquired pointPrefix before after × Contacts fragments ordinary target targetPositive ×
      FaceMeshBudgets (standardDifferential (0 : Fin 1)) points numericTolerance
        (numerator := ordinary.numerator) domains ×
      FacePrimitiveBank (standardDifferential (0 : Fin 1)) stage (numerator := ordinary.numerator) domains ×
      FaceSharedMeshes budgets primitives ×
      {value : TriangleReadings primitives lifted.mesh // value = TriangleReadings.build primitives lifted.mesh} ×
      PolynomialWork selection.1.val.requests.covered floor ordinary.val × work.Models modelStage ×
      (Nat × Nat × Nat) //
    inputs = (reference, contacts, budgets, primitives, shared, triangles, work, models, (stage, floor, modelStage)) ∧
      contacts.route.index ≤ stage ∧ contacts.charts.index ≤ stage}

/-- The same whole model/physical caches and one set of actual post-bank comparisons with their derived finite bound. -/
@[expose] def Comparison : Type _ :=
  (inputs : Comparison.Inputs reference contacts shared triangles work models) ×
  (Σ viewedWork : {value : PolynomialWork fragments.request.requests.covered floor ordinary.val // HEq value work},
  Σ viewedModels : {value : viewedWork.val.Models modelStage // HEq value models ∧
    (PathModel.mk (PolynomialWork.Models.cells fragments.request.requests.covered
      viewedWork.val value)).integralSample =
      (PathModel.mk (PolynomialWork.Models.cells selection.1.val.requests.covered work models)).integralSample},
  Σ changed : {value : SplitSheets.Closed.NumeratorWord shared reference.word //
    value = SplitSheets.Closed.withNumerics reference.word shared},
  Σ compared : {value : SplitSheets.PolynomialComparison.Cache shared fragments.request.requests
      fragments.entries fragments.geometry fragments.roots changed.val.val.2 viewedWork.val viewedModels.val
      ordinary.property //
    value = SplitSheets.PolynomialComparison.build shared fragments.request.requests fragments.entries
      fragments.geometry fragments.roots changed.val.val.2 viewedWork.val viewedModels.val ordinary.property},
  Σ _routed : {value : RouteRequest.PolynomialReadings shared changed.val.val.2 fragments.rooted contacts.rawRoute
      ⟨contacts.route, contacts.route_eq⟩ inputs.property.2.1 //
    value = RouteRequest.compareClosed shared changed.val.val.2 fragments.rooted contacts.rawRoute
      ⟨contacts.route, contacts.route_eq⟩ inputs.property.2.1},
  Σ mesh : {value : MeshWordReadings shared contacts.faces.geometry //
    value = MeshWordReadings.build shared reference.vertices_mem contacts.faces.geometry},
  Σ _charts : {value : contacts.charts.Comparisons primitives triangles.val //
    value = contacts.charts.compare primitives triangles.val},
  Σ value : {value : Canonical // value = wordValue
      (CanonicalEdgeValues.edgeValuation lifted.mesh triangles.val.values) contacts.faces.geometry.indexed ∧
    value = wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh triangles.val.values)
      (lifted.edges.indexedEdges lifted.vertices walk.closed.walk (lifted.vertices.sheet vertex))},
  {bound : Rational // bound = 2 * (compared.val.bound + 2 * (target + 2 * (target + mesh.val.bound))) ∧
    normSq ((PathModel.mk (PolynomialWork.Models.cells selection.1.val.requests.covered work models)).integralSample -
      value.val) < bound})

/-- The scalar two-triangle estimate keeps all independent model, routing, chart and mesh charges. -/
private theorem compose_bound (model gap routed cochain : Canonical)
    (modelBound routeBound chartBound meshBound : Rational)
    (modelPaid : normSq (gap - model) ≤ modelBound) (routePaid : normSq (gap - routed) < routeBound)
    (chartPaid : normSq (cochain - routed) < 2 * (chartBound + meshBound)) :
    normSq (model - cochain) < 2 * (modelBound + 2 * (routeBound + 2 * (chartBound + meshBound))) := by
  have twoPositive := natCast_pos_direct (n := 2) (Nat.zero_lt_succ 1)
  have reverseChart : normSq (routed - cochain) < 2 * (chartBound + meshBound) := by
    rewrite [show routed - cochain = -(cochain - routed) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
    exact chartPaid
  have gapPaid : normSq (gap - cochain) < 2 * (routeBound + 2 * (chartBound + meshBound)) := by
    rewrite [show gap - cochain = (gap - routed) + (routed - cochain) by ring1]
    exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
      (Arithmetic.mul_lt_mul_of_pos_left_direct twoPositive (Arithmetic.add_lt_add_direct routePaid reverseChart))
  have reverseModel : normSq (model - gap) ≤ modelBound := by
    rewrite [show model - gap = -(gap - model) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
    exact modelPaid
  rewrite [show model - cochain = (model - gap) + (gap - cochain) by ring1]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Arithmetic.mul_lt_mul_of_pos_left_direct twoPositive
      ((Arithmetic.add_le_add_direct reverseModel (Basic.le_refl _)).trans_lt
        (Arithmetic.add_lt_add_left_direct gapPaid modelBound)))

/-- Construct the actual fresh ordinary model-to-cycle comparison on the supplied SAME P bank.

The old reference word supplies every physical Finish and join. Its one
numerical revaluation, full-model comparison, route comparison, mesh
reading and chart comparison are retained with whole factories. The only
model operation is the original joint cover transport; no model, source,
root, reference or P-bank producer is executed to recover data.
-/
def compareNumerics : Comparison reference contacts shared triangles work models :=
  fragments.withModels work models
    (fun viewedWork workHEq viewedModels modelsHEq integralEq =>
      let inputs : Comparison.Inputs reference contacts shared triangles work models :=
        ⟨(reference, contacts, budgets, primitives, shared, triangles, work, models, (stage, floor, modelStage)),
          rfl, routeLater, chartLater⟩
      let actualWork : {value : PolynomialWork fragments.request.requests.covered floor ordinary.val //
          HEq value work} :=
        ⟨viewedWork, workHEq⟩
      let actualModels : {value : actualWork.val.Models modelStage // HEq value models ∧
          (PathModel.mk (PolynomialWork.Models.cells fragments.request.requests.covered
            actualWork.val value)).integralSample =
            (PathModel.mk (PolynomialWork.Models.cells selection.1.val.requests.covered work models)).integralSample} :=
        ⟨viewedModels, modelsHEq, integralEq⟩
      let changed : {value : SplitSheets.Closed.NumeratorWord shared reference.word //
          value = SplitSheets.Closed.withNumerics reference.word shared} :=
        ⟨SplitSheets.Closed.withNumerics reference.word shared, rfl⟩
      let compared : {value : SplitSheets.PolynomialComparison.Cache shared fragments.request.requests
          fragments.entries fragments.geometry fragments.roots changed.val.val.2 actualWork.val actualModels.val
          ordinary.property //
          value = SplitSheets.PolynomialComparison.build shared fragments.request.requests fragments.entries
            fragments.geometry fragments.roots changed.val.val.2 actualWork.val actualModels.val ordinary.property} :=
        ⟨SplitSheets.PolynomialComparison.build shared fragments.request.requests fragments.entries
          fragments.geometry fragments.roots changed.val.val.2 actualWork.val actualModels.val ordinary.property, rfl⟩
      let routed : {value : RouteRequest.PolynomialReadings shared changed.val.val.2 fragments.rooted contacts.rawRoute
          ⟨contacts.route, contacts.route_eq⟩ routeLater //
          value = RouteRequest.compareClosed shared changed.val.val.2 fragments.rooted contacts.rawRoute
            ⟨contacts.route, contacts.route_eq⟩ routeLater} :=
        ⟨RouteRequest.compareClosed shared changed.val.val.2 fragments.rooted contacts.rawRoute
          ⟨contacts.route, contacts.route_eq⟩ routeLater, rfl⟩
      let mesh : {value : MeshWordReadings shared contacts.faces.geometry //
          value = MeshWordReadings.build shared reference.vertices_mem contacts.faces.geometry} :=
        ⟨MeshWordReadings.build shared reference.vertices_mem contacts.faces.geometry, rfl⟩
      let charts : {value : contacts.charts.Comparisons primitives triangles.val //
          value = contacts.charts.compare primitives triangles.val} :=
        ⟨contacts.charts.compare primitives triangles.val, rfl⟩
      let value : {value : Canonical // value = wordValue
          (CanonicalEdgeValues.edgeValuation lifted.mesh triangles.val.values) contacts.faces.geometry.indexed ∧
          value = wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh triangles.val.values)
            (lifted.edges.indexedEdges lifted.vertices walk.closed.walk (lifted.vertices.sheet vertex))} :=
        ⟨wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh triangles.val.values) contacts.faces.geometry.indexed,
          rfl, contacts.original_value _ (CanonicalEdgeValues.edgeValuation_reverse lifted.mesh triangles.val.values)⟩
      have routingValue : routed.val.value = mesh.val.value :=
        routed.val.value_eq.trans ((congrArg gaussianSum routed.val.routed_values_eq).trans
          ((contacts.routed_sum shared).trans
            (mesh.val.value_eq.trans (congrArg gaussianSum mesh.val.values_eq)).symm))
      have routedPaid : normSq (compared.val.value - mesh.val.value) < target :=
        Eq.mp (congrArg₂ (fun first last : Canonical => normSq (first - last) < target)
          compared.val.value_eq.symm routingValue) routed.val.accurate
      have canonicalPaid : normSq
          (wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh triangles.val.values)
            contacts.faces.geometry.indexed - mesh.val.value) < 2 * (target + mesh.val.bound) :=
        Inclusion.PeriodCanonical.comparison_bound (genus := 1) (curve := Fibre.frameCurve frame)
          (branches := branches) (higher := higher) (base := framed) (frames := lifted.frames)
          (vertices := lifted.vertices) (edges := lifted.edges) (mesh := lifted.mesh)
          (source := standardDifferential (0 : Fin 1)) (domains := domains) (polynomial := some ordinary)
          (points := points) (tolerance := numericTolerance) (stage := stage) (budgets := budgets)
          (numerics := primitives) (shared := shared) (assigned := contacts.faces.geometry)
          mesh.val contacts.charts chartLater triangles.val charts.val
      have valuePaid : normSq (value.val - mesh.val.value) < 2 * (target + mesh.val.bound) :=
        Eq.mpr (congrArg (fun amount : Canonical => normSq (amount - mesh.val.value) <
          2 * (target + mesh.val.bound)) value.property.1) canonicalPaid
      have actualBound := compose_bound
        (PathModel.mk (PolynomialWork.Models.cells fragments.request.requests.covered actualWork.val
          actualModels.val)).integralSample compared.val.value mesh.val.value value.val
        compared.val.bound target target mesh.val.bound compared.val.accurate routedPaid valuePaid
      let bound := 2 * (compared.val.bound + 2 * (target + 2 * (target + mesh.val.bound)))
      have originalBound : normSq
          ((PathModel.mk (PolynomialWork.Models.cells selection.1.val.requests.covered work models)).integralSample -
            value.val) < bound :=
        Eq.mp (congrArg (fun amount : Canonical => normSq (amount - value.val) < bound) integralEq) actualBound
      ⟨inputs, actualWork, actualModels, changed, compared, routed, mesh, charts, value,
        bound, rfl, originalBound⟩)

namespace Comparison

variable {reference contacts shared triangles work models}
    (kept : Comparison reference contacts shared triangles work models)

/-- Read the complete original owners, numerical caches and all independent stages without their producers. -/
@[expose] def inputs := kept.1.val

/-- The complete stored owners and stages remain the original supplied inputs. -/
theorem inputs_eq : kept.inputs =
    (reference, contacts, budgets, primitives, shared, triangles, work, models, (stage, floor, modelStage)) :=
  kept.1.property.1

/-- Read the SAME high-floor Work after its whole physical-cover transport. -/
@[expose] def sourceWork := kept.2.1.val

/-- The complete high-floor Work is the SAME actual original work cache heterogeneously. -/
theorem sourceWork_heq : HEq kept.sourceWork work := kept.2.1.property

/-- Read the SAME independent-stage Models after the joint physical-cover transport. -/
@[expose] def sourceModels : kept.sourceWork.Models modelStage := kept.2.2.1.val

/-- The complete Models cache remains the same given object heterogeneously. -/
theorem sourceModels_heq : HEq kept.sourceModels models := kept.2.2.1.property.1

/-- Whole model transport preserves the actual original comparison integral sample. -/
theorem model_integral :
    (PathModel.mk (PolynomialWork.Models.cells fragments.request.requests.covered kept.sourceWork
      kept.sourceModels)).integralSample =
    (PathModel.mk (PolynomialWork.Models.cells selection.1.val.requests.covered work models)).integralSample :=
  kept.2.2.1.property.2

/-- Read the actual old/new physical word pair, retaining every original Finish and closing join. -/
@[expose] def changed := kept.2.2.2.1.val

/-- The complete new numerical realization is the original given-physical-cache operation. -/
theorem changed_eq : kept.changed = SplitSheets.Closed.withNumerics reference.word shared :=
  kept.2.2.2.1.property

/-- Read the actual once-materialized full-model fragment comparison. -/
@[expose] def compared := kept.2.2.2.2.1.val

/-- The entire model comparison consumes the SAME retained high-floor work, models and physical word. -/
theorem compared_eq : kept.compared = SplitSheets.PolynomialComparison.build shared
    fragments.request.requests fragments.entries fragments.geometry fragments.roots kept.changed.val.2
    kept.sourceWork kept.sourceModels ordinary.property := kept.2.2.2.2.1.property

/-- Read the actual route comparison and all of its retained partial-endpoint views. -/
@[expose] def routed := kept.2.2.2.2.2.1.val

/-- Read the actual selected period mesh-word cache, including its global count-squared allowance. -/
@[expose] def mesh := kept.2.2.2.2.2.2.1.val

/-- Read the SAME ordered Some chart/contact comparison cache on the supplied P primitive bank. -/
@[expose] def charts := kept.2.2.2.2.2.2.2.1.val

/-- Read the once-cached actual current-grid canonical cochain scalar. -/
@[expose] def value : Canonical := kept.2.2.2.2.2.2.2.2.1.val

/-- The scalar reads the actual selected face word on the SAME triangle bank. -/
theorem value_eq : kept.value = wordValue
    (CanonicalEdgeValues.edgeValuation lifted.mesh triangles.val.values) contacts.faces.geometry.indexed :=
  kept.2.2.2.2.2.2.2.2.1.property.1

/-- The same scalar reads the original fresh period's actual signed cycle, by genuine self-resplit comparison. -/
theorem original_value : kept.value = wordValue
    (CanonicalEdgeValues.edgeValuation lifted.mesh triangles.val.values)
    (lifted.edges.indexedEdges lifted.vertices walk.closed.walk (lifted.vertices.sheet vertex)) :=
  kept.2.2.2.2.2.2.2.2.1.property.2

/-- Read the computed finite error with its actual model, route, chart and mesh charges. -/
@[expose] def bound : Rational := kept.2.2.2.2.2.2.2.2.2.val

/-- The finite error retains the real independent cached analytic and fixed-word mesh contributions. -/
theorem bound_eq : kept.bound = 2 * (kept.compared.bound + 2 * (target + 2 * (target + kept.mesh.bound))) :=
  kept.2.2.2.2.2.2.2.2.2.property.1

/-- The actual original high-floor model and original fresh cycle cochain satisfy the derived finite bound. -/
theorem accurate : normSq
    ((PathModel.mk (PolynomialWork.Models.cells selection.1.val.requests.covered work models)).integralSample -
      kept.value) < kept.bound := kept.2.2.2.2.2.2.2.2.2.property.2

/-- The original per-leaf allocation pays the SAME retained model-gap cache at its genuine two floors. -/
theorem model_bound_lt {requested : Rational} (requestedPositive : 0 < requested)
    (allocated : SplitSheets.PolynomialComparison.Requests budgets fragments.entries
      (Approximation.Rational.Budget.Aggregate.perTerm requested
        (Fragment.SplitSheets.fragmentCount fragments.entries)))
    (sourcePaid : SplitSheets.PolynomialComparison.sourceFloor budgets fragments.entries allocated ≤ floor)
    (facePaid : SplitSheets.PolynomialComparison.faceFloor budgets fragments.entries allocated ≤ stage) :
    kept.compared.bound < requested :=
  SplitSheets.PolynomialComparison.Cache.bound_lt budgets shared fragments.request.requests
    fragments.entries fragments.geometry fragments.roots kept.changed.val.2 kept.sourceWork kept.sourceModels
    kept.compared requestedPositive allocated sourcePaid facePaid

/-- The actual selected period mesh charge keeps its original fixed global word count and numerical tolerance. -/
theorem mesh_bound_eq : kept.mesh.bound =
    Approximation.Rational.Budget.Aggregate.countCoordinate contacts.faces.geometry.indexed.length *
      (Approximation.Rational.Budget.Aggregate.countCoordinate contacts.faces.geometry.indexed.length *
        (16 * numericTolerance)) :=
  kept.mesh.bound_eq.trans (congrArg (fun count =>
    Approximation.Rational.Budget.Aggregate.countCoordinate count *
      (Approximation.Rational.Budget.Aggregate.countCoordinate count * (16 * numericTolerance))) kept.mesh.count_eq)

end Comparison

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine.GridFragments

end
