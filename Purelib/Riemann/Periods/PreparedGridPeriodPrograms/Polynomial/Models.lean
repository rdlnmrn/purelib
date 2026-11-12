module

public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Primitive.Comparison
public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial.Primitives
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Polynomial
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Entries
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.Readings.UniformPreparedRequests.Covered
import Purelib.Tactic.Ring
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Specification
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Primitive
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # Independently floored comparison models of an actual polynomial period

The actual initial spine and primitive request give the complete cover
identity. Given work/model caches are transported jointly and compared
through one retained source preparation. A real pre-observation selection
pays their independent stages; no old construction floor is relabelled and
no numerical P bank or model producer executes in the cache constructor.
-/

public section

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine

open Purelib
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_antitone quarterRadius_eq_mul_pow)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell (PreparedParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Rat.Fraction.Cast.Order
open Purelib.Geometry.Rational (Box)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass movementMass_nonnegative)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {base : Canonical}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval base)} {source : Differential 1}
    {walk : PeriodWalk grid base owner source}
    (spine : PolynomialSpine walk) {coordinate : Fin 2} {oldFloor oldStage : Nat}
    (value : PolynomialValue walk spine oldFloor coordinate)
    (oldModels : {models : value.1.Models oldStage // models = value.1.models oldStage})
    {sourceStart periodStart : Nat} {tolerance : Rational} {positive : 0 < tolerance}
    (request : PrimitiveSelection walk sourceStart periodStart tolerance positive)
    (chain : {actual : CenteredPathChain
        (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
        (start := walk.initial.state.start) (finish := walk.initial.state.start) //
      actual = spine.chain.castParents spine.parents_eq})
    {newFloor newStage sourceFloor sourceStage : Nat}
    (targets : {actual : CellEndpoints.Targets chain.val.path sourceStage //
      actual = CellEndpoints.Targets.build chain.val.path sourceStage})
    (work : {actual : PolynomialWork request.1.val.requests.covered newFloor
        (Jets.Specification.valueSpecification parameter coordinate) //
      actual = PolynomialWork.build request.1.val.requests.covered newFloor
        (Jets.Specification.valueSpecification parameter coordinate)})
    (models : {actual : work.val.Models newStage // actual = work.val.models newStage})
    (prepared : {actual : PreparedParents (parameter := parameter) (frame := frame)
        request.1.val.requests.covered sourceFloor targets.val //
      actual = Jets.Source.Cell.prepareCovered (parameter := parameter) (frame := frame)
        request.1.val.requests.covered sourceFloor targets.val})

/-- The actual cached initial spine and retained primitive-request factory give one whole target cover. -/
theorem requested_cover : spine.covered.castParents spine.parents_eq = request.1.val.requests.covered :=
  ((CoveredParents.castParents_eq_mp spine.covered spine.parents_eq).trans spine.covered_factory).trans
    (walk.primitiveRequest_covered (parameter := parameter) (frame := frame)
      (Field.div_pos_direct positive (natCast_pos_direct (n := 64) (Nat.zero_lt_succ 63))) request.1.val
        request.1.property).symm

namespace ModelComparison

/-- The exact original owners, certified input caches and independent source/model stages of one comparison. -/
@[expose] def Inputs : Type _ :=
  PeriodWalk grid base owner source × PolynomialSpine walk ×
      PolynomialValue walk spine oldFloor coordinate ×
      {models : value.1.Models oldStage // models = value.1.models oldStage} ×
      PrimitiveSelection walk sourceStart periodStart tolerance positive ×
      {actual : CenteredPathChain
        (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
        (start := walk.initial.state.start) (finish := walk.initial.state.start) //
        actual = spine.chain.castParents spine.parents_eq} ×
      {actual : CellEndpoints.Targets chain.val.path sourceStage //
        actual = CellEndpoints.Targets.build chain.val.path sourceStage} ×
      {actual : PolynomialWork request.1.val.requests.covered newFloor
        (Jets.Specification.valueSpecification parameter coordinate) //
        actual = PolynomialWork.build request.1.val.requests.covered newFloor
          (Jets.Specification.valueSpecification parameter coordinate)} ×
      {actual : work.val.Models newStage // actual = work.val.models newStage} ×
      {actual : PreparedParents (parameter := parameter) (frame := frame)
        request.1.val.requests.covered sourceFloor targets.val //
        actual = Jets.Source.Cell.prepareCovered (parameter := parameter) (frame := frame)
          request.1.val.requests.covered sourceFloor targets.val} ×
      (Fin 2 × Nat × Nat × Nat × Nat × Nat × Nat)

end ModelComparison

/-- The complete original programme, supplied observations and whole transported polynomial caches with derived error.

Both original work floors and both literal model stages remain independent.
The retained request and target factories certify the actual source cover
and source precision. The comparison's mathematical bound is derived from
both original source-model laws; it is not a proposed scalar agreement.
-/
abbrev ModelComparison :=
  {inputs : ModelComparison.Inputs (oldFloor := oldFloor) (oldStage := oldStage)
      (newFloor := newFloor) (newStage := newStage) (sourceFloor := sourceFloor) (sourceStage := sourceStage)
      spine value request chain targets work //
    inputs = (walk, spine, value, oldModels, request, chain, targets, work, models, prepared,
      (coordinate, oldFloor, oldStage, newFloor, newStage, sourceFloor, sourceStage))} ×
  (Σ newWork : {actual : PolynomialWork request.1.val.requests.covered newFloor
      (Jets.Specification.valueSpecification parameter coordinate) // actual = work.val ∧
      actual = PolynomialWork.build request.1.val.requests.covered newFloor
        (Jets.Specification.valueSpecification parameter coordinate)},
  Σ newModels : {actual : newWork.val.Models newStage //
    HEq actual models.val ∧ actual = newWork.val.models newStage},
  Σ viewedCover : {actual : CoveredParents 1
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))) //
    actual = spine.covered.castParents spine.parents_eq ∧ HEq actual spine.covered ∧
      actual = request.1.val.requests.covered},
  Σ parentWork : {actual : PolynomialWork viewedCover.val oldFloor
      (Jets.Specification.valueSpecification parameter coordinate) // HEq actual value.1},
  Σ _parentModels : {actual : parentWork.val.Models oldStage // HEq actual oldModels.val},
  Σ sharedWork : {actual : PolynomialWork request.1.val.requests.covered oldFloor
      (Jets.Specification.valueSpecification parameter coordinate) // HEq actual value.1},
  Σ _sharedModels : {actual : sharedWork.val.Models oldStage // HEq actual oldModels.val},
  {bound : Rational // bound =
      32 * (quarterRadius 1 oldStage + quarterRadius 1 newStage + 2 * targets.val.localBound) *
        movementMass spine.parents ∧
    normSq ((value.2.val.integral.model oldStage).integralSample -
      (PathModel.mk (PolynomialWork.Models.cells
        request.1.val.requests.covered newWork.val newModels.val)).integralSample) ≤ bound})

/-- Consume the GIVEN old programme models and new work/models/source observation without running their factories.

Original withParents and withCovered operations move the complete old
caches jointly. Exact initial-spine and primitive-request factories derive
the cover identity. Both model errors use the same actual source observation;
no primitive constant, query, geometry, period or numerical bank is replaced.
-/
def compareModels : ModelComparison spine value oldModels request chain targets work models prepared :=
  let newWork : {actual : PolynomialWork request.1.val.requests.covered newFloor
      (Jets.Specification.valueSpecification parameter coordinate) // actual = work.val ∧
      actual = PolynomialWork.build request.1.val.requests.covered newFloor
        (Jets.Specification.valueSpecification parameter coordinate)} :=
    ⟨work.val, rfl, work.property⟩
  let newModels : {actual : newWork.val.Models newStage //
      HEq actual models.val ∧ actual = newWork.val.models newStage} :=
    ⟨models.val, HEq.rfl, models.property⟩
  PolynomialWork.Models.withParents spine.parents_eq spine.covered value.1 oldModels.val
    (fun viewedCover coverEq coverHEq parentWork workHEq parentModels modelsHEq parentIntegral =>
      let actualCover : {actual : CoveredParents 1
          (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))) //
          actual = spine.covered.castParents spine.parents_eq ∧ HEq actual spine.covered ∧
            actual = request.1.val.requests.covered} :=
        ⟨viewedCover, coverEq, coverHEq, coverEq.trans (requested_cover spine request)⟩
      PolynomialWork.Models.withCovered actualCover.property.2.2 parentWork parentModels
        (fun sharedWork sharedWorkHEq sharedModels sharedModelsHEq sharedIntegral =>
          let oldWorkView : {actual : PolynomialWork actualCover.val oldFloor
              (Jets.Specification.valueSpecification parameter coordinate) // HEq actual value.1} :=
            ⟨parentWork, workHEq⟩
          let oldModelsView : {actual : oldWorkView.val.Models oldStage // HEq actual oldModels.val} :=
            ⟨parentModels, modelsHEq⟩
          let sharedWorkView : {actual : PolynomialWork request.1.val.requests.covered oldFloor
              (Jets.Specification.valueSpecification parameter coordinate) // HEq actual value.1} :=
            ⟨sharedWork, sharedWorkHEq.trans workHEq⟩
          let sharedModelsView : {actual : sharedWorkView.val.Models oldStage // HEq actual oldModels.val} :=
            ⟨sharedModels, sharedModelsHEq.trans modelsHEq⟩
          have actualModel := (walk.polynomialValue_model value oldStage).trans
            (congrArg PathModel.mk (PolynomialWork.model_cells value.1 value.1.models oldStage))
          have cachedModel := congrArg (fun actual : value.1.Models oldStage =>
            (PathModel.mk (PolynomialWork.Models.cells spine.covered value.1 actual)).integralSample)
            oldModels.property
          have sampleEq := sharedIntegral.trans (parentIntegral.trans
            (cachedModel.trans (congrArg PathModel.integralSample actualModel).symm))
          have bounded := PreparedParents.polynomial_models_difference_le request.1.val.requests.covered coordinate
            sharedWorkView.val sharedModelsView.val newWork.val newModels.val prepared.val chain.val
          let bound := 32 * (quarterRadius 1 oldStage + quarterRadius 1 newStage + 2 * targets.val.localBound) *
            movementMass spine.parents
          have sameMass := congrArg movementMass spine.parents_eq
          have cachedBound := bounded.trans_eq (congrArg (fun mass : Rational =>
            32 * (quarterRadius 1 oldStage + quarterRadius 1 newStage + 2 * targets.val.localBound) * mass)
              sameMass.symm)
          let inputs : {inputs :
              ModelComparison.Inputs (oldFloor := oldFloor) (oldStage := oldStage)
                (newFloor := newFloor) (newStage := newStage) (sourceFloor := sourceFloor) (sourceStage := sourceStage)
                spine value request chain targets work //
              inputs = (walk, spine, value, oldModels, request, chain, targets, work, models, prepared,
                (coordinate, oldFloor, oldStage, newFloor, newStage, sourceFloor, sourceStage))} :=
            ⟨(walk, spine, value, oldModels, request, chain, targets, work, models, prepared,
              (coordinate, oldFloor, oldStage, newFloor, newStage, sourceFloor, sourceStage)), rfl⟩
          ⟨inputs, newWork, newModels, actualCover, oldWorkView, oldModelsView,
            sharedWorkView, sharedModelsView, bound, rfl,
            Eq.mp (congrArg (fun actual : Canonical => normSq (actual -
              (PathModel.mk (PolynomialWork.Models.cells
                request.1.val.requests.covered newWork.val newModels.val)).integralSample)
                ≤ bound) sampleEq) cachedBound⟩))

/-- Select actual independent old/new/source model stages before their observations.

The source target carries its own selected stage. The exact coefficient
128 pays q_old, q_new and twice that source allowance on the retained
parent count/movement data. Zero movement is supported without division.
-/
def modelSelection (oldStart newStart observedStart : Nat) (requested : Rational) (positiveRequest : 0 < requested) :
    {selected : Search.Selection (128 * movementMass spine.parents)
      (max oldStart (max newStart observedStart)) requested //
      selected = Search.Selection.build (128 * movementMass spine.parents)
        (Arithmetic.mul_nonneg_direct (show (0 : Rational) ≤ (128 : Rational) from by
          change (0 : Rational) ≤ ((128 : Nat) : Rational)
          rewrite [Data.Rat.Fraction.Cast.natCast_eq_fromInt 128]
          decide +kernel)
          (movementMass_nonnegative spine.parents))
        (max oldStart (max newStart observedStart)) requested positiveRequest} :=
  ⟨Search.Selection.build (128 * movementMass spine.parents)
    (Arithmetic.mul_nonneg_direct (show (0 : Rational) ≤ (128 : Rational) from by
          change (0 : Rational) ≤ ((128 : Nat) : Rational)
          rewrite [Data.Rat.Fraction.Cast.natCast_eq_fromInt 128]
          decide +kernel) (movementMass_nonnegative
      spine.parents))
    (max oldStart (max newStart observedStart)) requested positiveRequest, rfl⟩

namespace ModelComparison

variable {spine value oldModels request chain targets work models prepared}
variable (compared : ModelComparison spine value oldModels request chain targets work models prepared)

/-- Read the same complete original period, old and new caches and independent floor/stage allocation. -/
@[expose] def inputs : Inputs (oldFloor := oldFloor) (oldStage := oldStage)
    (newFloor := newFloor) (newStage := newStage) (sourceFloor := sourceFloor) (sourceStage := sourceStage)
    spine value request chain targets work := compared.1.val

/-- Every original nominal input and whole factory is retained as its exact given certified value. -/
theorem inputs_eq : compared.inputs = (walk, spine, value, oldModels, request, chain, targets, work, models, prepared,
    (coordinate, oldFloor, oldStage, newFloor, newStage, sourceFloor, sourceStage)) := compared.1.property

/-- Read the unchanged given old programme under the original retained initial-spine index. -/
@[expose] def oldValue : PolynomialValue walk spine oldFloor coordinate := compared.inputs.2.2.1

/-- Read the actual given new work cache without its producer. -/
@[expose] def newWork : PolynomialWork request.1.val.requests.covered newFloor
    (Jets.Specification.valueSpecification parameter coordinate) := compared.inputs.2.2.2.2.2.2.2.1.val

/-- Read the one supplied source observation shared by the old/new comparisons. -/
@[expose] def sourceObservation : PreparedParents (parameter := parameter) (frame := frame)
    request.1.val.requests.covered sourceFloor targets.val := compared.inputs.2.2.2.2.2.2.2.2.2.1.val

/-- Read the actual high-floor work before its dependent model cache, without recovering it from a type. -/
@[expose] def comparisonWork : PolynomialWork request.1.val.requests.covered newFloor
    (Jets.Specification.valueSpecification parameter coordinate) := compared.2.1.val

/-- Read the SAME dependent high-floor model cache on that actual retained work. -/
@[expose] def comparisonModels : compared.comparisonWork.Models newStage := compared.2.2.1.val

/-- The whole retained high-floor work remains the supplied actual input cache. -/
theorem comparisonWork_eq : compared.comparisonWork = work.val := compared.2.1.property.1

/-- The high-floor work retains its actual source-covered construction factory as a proof only. -/
theorem comparisonWork_factory : compared.comparisonWork =
    PolynomialWork.build request.1.val.requests.covered newFloor
      (Jets.Specification.valueSpecification parameter coordinate) := compared.2.1.property.2

/-- The dependent model data remain the literal supplied input heterogeneously. -/
theorem comparisonModels_heq : HEq compared.comparisonModels models.val := compared.2.2.1.property.1

/-- The model cache retains its original whole stage factory on the SAME high-floor work. -/
theorem comparisonModels_factory : compared.comparisonModels = compared.comparisonWork.models newStage :=
  compared.2.2.1.property.2

/-- Read the genuine whole-cover/model view, including both independent primitive constant banks. -/
@[expose] def sharedOldWork : PolynomialWork request.1.val.requests.covered oldFloor
    (Jets.Specification.valueSpecification parameter coordinate) := compared.2.2.2.2.2.2.1.val

/-- The complete old work is retained heterogeneously after both exact nominal transports. -/
theorem sharedOldWork_heq : HEq compared.sharedOldWork value.1 := compared.2.2.2.2.2.2.1.property

/-- Read the exact source/model-stage charge without evaluating any cache again. -/
@[expose] def bound : Rational := compared.2.2.2.2.2.2.2.2.val

/-- The charge keeps q_old, q_new and twice the actual source target at their independent stages. -/
theorem bound_eq : compared.bound =
    32 * (quarterRadius 1 oldStage + quarterRadius 1 newStage + 2 * targets.val.localBound) *
      movementMass spine.parents := compared.2.2.2.2.2.2.2.2.property.1

/-- The actual original programme model and GIVEN new model integral meet the internally derived comparison bound. -/
theorem accurate : normSq ((value.2.val.integral.model oldStage).integralSample -
    (PathModel.mk (PolynomialWork.Models.cells request.1.val.requests.covered
      compared.comparisonWork compared.comparisonModels)).integralSample) ≤
    compared.bound := compared.2.2.2.2.2.2.2.2.property.2

/-- Scalar multiplication reads the original quarter-radius at the same unchanged model stage. -/
private theorem scale_quarter (scale : Rational) (stage : Nat) :
    scale * quarterRadius 1 stage = quarterRadius scale stage := by
  rewrite [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
  ring1

/-- The actual fixed source target and both independent model stages pay the retained exact charge.

All three lower bounds refer to the SAME original pre-observation search.
The source record's actual localBound is paid from its own stage, not an
assumed small target or a replacement request. The two construction floors
and every original source/model observation remain unchanged.
-/
theorem bound_lt {oldStart newStart observedStart : Nat} {requested : Rational}
    (selected : Search.Selection (128 * movementMass spine.parents)
      (max oldStart (max newStart observedStart)) requested)
    (oldAfter : selected.stage ≤ oldStage) (newAfter : selected.stage ≤ newStage)
    (sourceAfter : selected.stage ≤ sourceStage) : compared.bound < requested := by
  let mass := movementMass spine.parents
  have massNonnegative : 0 ≤ mass := movementMass_nonnegative spine.parents
  have modelScaleNonnegative : 0 ≤ 32 * mass :=
    Arithmetic.mul_nonneg_direct (natCast_le_direct (m := 0) (n := 32) (Nat.zero_le 32)) massNonnegative
  have sourceScaleNonnegative : 0 ≤ 64 * mass :=
    Arithmetic.mul_nonneg_direct (natCast_le_direct (m := 0) (n := 64) (Nat.zero_le 64)) massNonnegative
  have oldPaid : 32 * mass * quarterRadius 1 oldStage ≤ quarterRadius (32 * mass) selected.stage :=
    (scale_quarter (32 * mass) oldStage).trans_le (quarterRadius_antitone modelScaleNonnegative oldAfter)
  have newPaid : 32 * mass * quarterRadius 1 newStage ≤ quarterRadius (32 * mass) selected.stage :=
    (scale_quarter (32 * mass) newStage).trans_le (quarterRadius_antitone modelScaleNonnegative newAfter)
  have sourcePaid : 64 * mass * targets.val.localBound ≤ quarterRadius (64 * mass) selected.stage :=
    (targets.val.mul_localBound_le_quarterRadius (64 * mass) sourceScaleNonnegative).trans
      (quarterRadius_antitone sourceScaleNonnegative sourceAfter)
  have allPaid := Arithmetic.add_le_add_direct (Arithmetic.add_le_add_direct oldPaid newPaid) sourcePaid
  have boundFormula : compared.bound = 32 * mass * quarterRadius 1 oldStage +
      32 * mass * quarterRadius 1 newStage + 64 * mass * targets.val.localBound := by
    rewrite [compared.bound_eq]
    dsimp only [mass]
    ring1
  have scaleSum : quarterRadius (32 * mass) selected.stage + quarterRadius (32 * mass) selected.stage +
      quarterRadius (64 * mass) selected.stage = quarterRadius (128 * mass) selected.stage := by
    simp only [quarterRadius_eq_mul_pow]
    ring1
  exact (boundFormula.trans_le (allPaid.trans_eq scaleSum)).trans_lt
    (selected.later_accurate (Nat.le_refl selected.stage))

/-- The actual old programme sample and supplied high-floor model obey the original selected positive request. -/
theorem paid {oldStart newStart observedStart : Nat} {requested : Rational}
    (selected : Search.Selection (128 * movementMass spine.parents)
      (max oldStart (max newStart observedStart)) requested)
    (oldAfter : selected.stage ≤ oldStage) (newAfter : selected.stage ≤ newStage)
    (sourceAfter : selected.stage ≤ sourceStage) :
    normSq ((value.2.val.integral.model oldStage).integralSample -
      (PathModel.mk (PolynomialWork.Models.cells request.1.val.requests.covered
      compared.comparisonWork compared.comparisonModels)).integralSample) <
      requested := compared.accurate.trans_lt (compared.bound_lt selected oldAfter newAfter sourceAfter)

end ModelComparison

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine
