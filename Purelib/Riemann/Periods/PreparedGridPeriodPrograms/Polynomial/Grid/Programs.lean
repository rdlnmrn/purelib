module

public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Grid.Comparison
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Holomorphic
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial.Primitives
import Purelib.Curves.Legendre.Periods.Jets.Specification
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Grid
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Grid.Readings
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Grid.Routes
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Models
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Primitive.Comparison
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Readings.UniformPreparedRequests.Covered
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices

/-! # Original fresh programmes and the SAME actual P-bank cochain

The old polynomial programme and original holomorphic programme retain
their actual old model/request floors. Their supplied cached comparison
is composed with the fresh current-grid comparison on the same high-floor
Work and Models. No P bank, geometry, query or numerical comparison is
prepared by these readbacks, and no name is created from a finite scalar.
-/

public section

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine

open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell (PreparedParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Cast.Order
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)

/-- Two actual comparison caches compose their independent squared-norm charges through the SAME model sample. -/
private theorem through_model (program model cochain : Canonical) (first second : Rational)
    (firstPaid : normSq (program - model) ≤ first) (secondPaid : normSq (model - cochain) < second) :
    normSq (program - cochain) < 2 * (first + second) := by
  rewrite [show program - cochain = (program - model) + (model - cochain) by ring1]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Arithmetic.mul_lt_mul_of_pos_left_direct (natCast_pos_direct (n := 2) (Nat.zero_lt_succ 1))
      ((Arithmetic.add_le_add_direct firstPaid (Basic.le_refl _)).trans_lt
        (Arithmetic.add_lt_add_left_direct secondPaid first)))

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
    (reference : GridFragments.Reference fragments acquired pointPrefix before after)
    {target : Rational} {targetPositive : 0 < target} {numericTolerance : Rational}
    {stage newFloor newStage sourceFloor sourceStage : Nat}
    (chain : {actual : CenteredPathChain
        (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
        (start := walk.initial.state.start) (finish := walk.initial.state.start) //
      actual = spine.chain.castParents spine.parents_eq})
    (targets : {actual : CellEndpoints.Targets chain.val.path sourceStage //
      actual = CellEndpoints.Targets.build chain.val.path sourceStage})

section Polynomial

variable {coordinate : Fin 2} {oldFloor oldModelStage : Nat}
    (value : PolynomialValue walk spine oldFloor coordinate)
    (oldModels : {actual : value.1.Models oldModelStage // actual = value.1.models oldModelStage})

variable (work : {actual : PolynomialWork selection.1.val.requests.covered newFloor (⟨Specification.valueSpecification
  parameter coordinate,
      Specification.valueSpecification_denominatorPairs parameter coordinate⟩ :
      Ordinary (Fibre.frameCurve frame).polynomial).val //
      actual = PolynomialWork.build selection.1.val.requests.covered newFloor (⟨Specification.valueSpecification
        parameter coordinate,
      Specification.valueSpecification_denominatorPairs parameter coordinate⟩ :
      Ordinary (Fibre.frameCurve frame).polynomial).val})
    (models : {actual : work.val.Models newStage // actual = work.val.models newStage})
    (prepared : {actual : PreparedParents (parameter := parameter) (frame := frame)
        selection.1.val.requests.covered sourceFloor targets.val //
      actual = Jets.Source.Cell.prepareCovered (parameter := parameter) (frame := frame)
        selection.1.val.requests.covered sourceFloor targets.val})
    (modelComparison : ModelComparison spine value oldModels selection chain targets work models prepared)
    (contacts : GridFragments.Contacts fragments (⟨Specification.valueSpecification parameter coordinate,
      Specification.valueSpecification_denominatorPairs parameter coordinate⟩ :
      Ordinary (Fibre.frameCurve frame).polynomial) target targetPositive)
    {budgets : FaceMeshBudgets (standardDifferential (0 : Fin 1)) points numericTolerance
      (numerator := Ordinary.numerator (⟨Specification.valueSpecification parameter coordinate,
      Specification.valueSpecification_denominatorPairs parameter coordinate⟩ :
      Ordinary (Fibre.frameCurve frame).polynomial)) domains}
    {primitives : FacePrimitiveBank (standardDifferential (0 : Fin 1)) stage
      (numerator := Ordinary.numerator (⟨Specification.valueSpecification parameter coordinate,
      Specification.valueSpecification_denominatorPairs parameter coordinate⟩ :
      Ordinary (Fibre.frameCurve frame).polynomial)) domains}
    {shared : FaceSharedMeshes budgets primitives}
    {triangles : {value : TriangleReadings primitives lifted.mesh //
      value = TriangleReadings.build primitives lifted.mesh}}
    (compared : GridFragments.Comparison reference contacts shared triangles work.val models.val)

/-- The complete given high-floor work/model factory identifies its literal original integral sample. -/
theorem ModelComparison.model_integral :
    (PathModel.mk (PolynomialWork.Models.cells selection.1.val.requests.covered
      modelComparison.comparisonWork modelComparison.comparisonModels)).integralSample =
    (PathModel.mk (PolynomialWork.Models.cells selection.1.val.requests.covered work.val models.val)).integralSample :=
  PolynomialWork.Models.integral_congr modelComparison.comparisonWork_eq
    modelComparison.comparisonModels models.val modelComparison.comparisonModels_heq

/-- The actual old polynomial programme model and the SAME fresh cycle cochain satisfy the two computed cache charges.

This includes the genuine numerator x without a differential-index
reinterpretation. Both stages, original value owner, common high-floor
Work/Models and actual physical closing caches remain unchanged.
-/
theorem ModelComparison.cochain_bound : normSq
    ((value.2.val.integral.model oldModelStage).integralSample - compared.value) <
      2 * (modelComparison.bound + compared.bound) := by
  have modelPaid := Eq.mp (congrArg (fun sample : Canonical => normSq
    ((value.2.val.integral.model oldModelStage).integralSample - sample) ≤ modelComparison.bound)
    (ModelComparison.model_integral (modelComparison := modelComparison)))
      modelComparison.accurate
  exact through_model _ _ _ _ _ modelPaid compared.accurate

end Polynomial

section Holomorphic

variable (workZero : PolynomialWork selection.1.val.requests.covered newFloor (⟨Specification.valueSpecification
  parameter 0,
      Specification.valueSpecification_denominatorPairs parameter 0⟩ :
      Ordinary (Fibre.frameCurve frame).polynomial).val)
    (modelsZero : workZero.Models newStage)
    (preparedZero : PreparedParents (parameter := parameter) (frame := frame)
      selection.1.val.requests.covered sourceFloor targets.val)
    {periodStage : Nat}
    (holomorphic : HolomorphicComparison (periodStage := periodStage) walk selection chain.val targets workZero
      modelsZero preparedZero)
    (contactsZero : GridFragments.Contacts fragments (⟨Specification.valueSpecification parameter 0,
      Specification.valueSpecification_denominatorPairs parameter 0⟩ :
      Ordinary (Fibre.frameCurve frame).polynomial) target targetPositive)
    {budgetsZero : FaceMeshBudgets (standardDifferential (0 : Fin 1)) points numericTolerance
      (numerator := Ordinary.numerator (⟨Specification.valueSpecification parameter 0,
      Specification.valueSpecification_denominatorPairs parameter 0⟩ :
      Ordinary (Fibre.frameCurve frame).polynomial)) domains}
    {primitivesZero : FacePrimitiveBank (standardDifferential (0 : Fin 1)) stage
      (numerator := Ordinary.numerator (⟨Specification.valueSpecification parameter 0,
      Specification.valueSpecification_denominatorPairs parameter 0⟩ :
      Ordinary (Fibre.frameCurve frame).polynomial)) domains}
    {sharedZero : FaceSharedMeshes budgetsZero primitivesZero}
    {trianglesZero : {value : TriangleReadings primitivesZero lifted.mesh //
      value = TriangleReadings.build primitivesZero lifted.mesh}}
    (comparedZero : GridFragments.Comparison reference contactsZero sharedZero trianglesZero workZero modelsZero)

/-- The genuine original dx/y programme and SAME fresh-cycle P=1 cochain retain both actual comparison charges.

The original PeriodWalk programme is the left owner. The only source
observation is the one forwarded to its fixed-preparation comparison;
no polynomial programme is substituted for that owner or named from a
single scalar reading.
-/
theorem HolomorphicComparison.cochain_bound : normSq
    (((walk.program 0).integral.model periodStage).integralSample - comparedZero.value) <
      2 * (holomorphic.bound + comparedZero.bound) :=
  through_model _ _ _ _ _ holomorphic.accurate.le comparedZero.accurate

end Holomorphic

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine

end
