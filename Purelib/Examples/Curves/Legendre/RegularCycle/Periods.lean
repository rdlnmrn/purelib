module

public import Purelib.Examples.Curves.Legendre.RegularCycle.Programs
public import Purelib.Examples.Curves.Legendre.RegularCycle.Stages
public import Purelib.Examples.Curves.Legendre.Frame
public import Purelib.Curves.Legendre.Periods.Jets.Source.Observations
public import Purelib.Curves.Legendre.Periods.Jets.Source.Attachment
public import Purelib.Curves.Legendre.Periods.Jets.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Certified periods on the original regular four-sided cycle

All six uniform requests precede the common original source model. One
bundled side query shares the actual continued point, divided coefficient
caches and root reading. Each original per-channel certificate answers its
individual query independently. The numerical programs and source attachment consume the
same retained four-side cell models on either selected sheet.
-/

public section

namespace Purelib.Examples.Curves.Legendre.RegularCycle

open Purelib
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)
open Purelib.Curves.Legendre.Periods.Jets.Source
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Riemann.Normalization.ContinuedInverseRoot
open ContinuedNeighborhood (UniformBounds)
open Purelib.Approximation.Rational

attribute [local irreducible] patch lowerLeft lowerRight upperRight upperLeft

variable {sheet : Fin 2} {cache : Cache (patch sheet)} {sourceFloor floor : Nat}
    {target allowance : Rational} {request : Request cache sourceFloor target}
    {bounds : UniformBounds (patch sheet)}

namespace Cells

/-- The exact six-query projection needed to certify one retained spatial coefficient. -/
@[expose] def ObservationProjection (request : Request cache sourceFloor target) (allowance : Rational)
    (requests : IntegrandRequests bounds floor (allowance / 4))
    (differential : OddPowerDifferential (Paths.polynomial (2 : Canonical))) (source : Coefficients)
    (projection : Projection request allowance source) :=
  {start finish : LiftedPoint 2} → (liftedCell : LiftedCell start finish) →
    (models : SideModels request start.coordinate finish.coordinate allowance) → (input : Rational) →
    CellModels.Observations Frame.frame liftedCell models requests input →
    Jets.UniformObservation (Fibre.frameCurve Frame.frame) differential liftedCell (projection models).model input

/-- Certify the four literal retained cells using their original six-channel query cache.

The uniform floors are paid by the already selected common model. Each
actual side keeps its original lifted edge and endpoint membership. Its
per-channel callback answers independently; a retained bundled observation
is the interface for consuming six same-query results together.
-/
def certify (cells : Cells request allowance) (requests : IntegrandRequests bounds floor (allowance / 4))
    {differential : OddPowerDifferential (Paths.polynomial (2 : Canonical))} {source : Coefficients}
    (projection : Projection request allowance source)
    (observation : ObservationProjection request allowance requests differential source projection)
    (positive : 0 < allowance) (stage : requests.stage ≤ request.selection.stage) :
    Jets.UniformPathCertificates (Fibre.frameCurve Frame.frame) differential
      (cells.path projection).cells (loop sheet).path := by
  let valid {start finish : LiftedPoint 2} (liftedCell : LiftedCell start finish)
      (models : SideModels request start.coordinate finish.coordinate allowance)
      (startInside : (patch sheet).box.Contains start.coordinate)
      (finishInside : (patch sheet).box.Contains finish.coordinate) :
      Jets.ValidCellCertificate (Fibre.frameCurve Frame.frame) differential liftedCell
        (projection models).model :=
    .uniform ⟨fun input lower upper => observation liftedCell models input
      (models.observations Frame.frame liftedCell requests input lower upper positive startInside finishInside stage)⟩
  exact .cons (projection cells.lower).start_eq (projection cells.lower).finish_eq
    (valid (lowerSide sheet) cells.lower (lowerLeft_inside sheet) (lowerRight_inside sheet))
    (.cons (projection cells.right).start_eq (projection cells.right).finish_eq
      (valid (rightSide sheet) cells.right (lowerRight_inside sheet) (upperRight_inside sheet))
      (.cons (projection cells.upper).start_eq (projection cells.upper).finish_eq
        (valid (upperSide sheet) cells.upper (upperRight_inside sheet) (upperLeft_inside sheet))
        (.cons (projection cells.left).start_eq (projection cells.left).finish_eq
          (valid (leftSide sheet) cells.left (upperLeft_inside sheet) (lowerLeft_inside sheet)) (.nil _))))

end Cells

/-- The six original uniform request caches retained at each geometric local allowance. -/
@[expose] def UniformRequests (bounds : UniformBounds (patch sheet)) (floors : Nat → Nat) :=
  (index : Nat) → IntegrandRequests bounds (floors index) (Geometric.Basic.quarterRadius 1 index / 4)

namespace Programs

variable {floors : Nat → Nat} {targets : Nat → Rational} {sources : Sources cache floors targets}
    {uniformFloors : Nat → Nat} {bounds : UniformBounds (patch sheet)}

/-- Certify the original retained value program at either displayed basis coordinate. -/
def certifiedValue (programs : Programs sources) (requests : UniformRequests bounds uniformFloors)
    (paid : ∀ index, (requests index).stage ≤ (sources index).selection.stage) (coordinate : Fin 2) :
    CertifiedPeriodProgram (Fibre.frameCurve Frame.frame) (Specification.valueSpecification 2 coordinate)
      (cycle sheet) where
  integral := programs.value coordinate
  certificates := by
    intro index
    by_cases zero : coordinate = 0
    · rewrite [value, if_pos zero, programs.valueZero_eq, program_model, zero]
      exact (programs.cells index).certify (requests index) (fun {_ _} models => models.valueZero)
        (fun {_ _} _ _ _ retained => retained.valueZero)
        (Geometric.Basic.quarterRadius_pos (by decide) index) (paid index)
    · rewrite [value, if_neg zero, programs.valueOne_eq, program_model]
      have sameSpecification : Specification.valueSpecification 2 coordinate =
          Specification.valueSpecification 2 1 := by
        unfold Specification.valueSpecification Specification.valueNumerator
        rewrite [if_neg zero, if_neg (by decide : (1 : Fin 2) ≠ 0)]
        rfl
      rewrite [sameSpecification]
      exact (programs.cells index).certify (requests index) (fun {_ _} models => models.valueOne)
        (fun {_ _} _ _ _ retained => retained.valueOne)
        (Geometric.Basic.quarterRadius_pos (by decide) index) (paid index)

/-- The value certification retains the same original numerical refinement program. -/
theorem certifiedValue_integral (programs : Programs sources) (requests : UniformRequests bounds uniformFloors)
    (paid : ∀ index, (requests index).stage ≤ (sources index).selection.stage) (coordinate : Fin 2) :
    (programs.certifiedValue requests paid coordinate).integral = programs.value coordinate := by
  unfold certifiedValue
  rfl

/-- Certify the original retained first program at either displayed basis coordinate. -/
def certifiedFirst (programs : Programs sources) (requests : UniformRequests bounds uniformFloors)
    (paid : ∀ index, (requests index).stage ≤ (sources index).selection.stage) (coordinate : Fin 2) :
    CertifiedPeriodProgram (Fibre.frameCurve Frame.frame) (Specification.firstDerivativeSpecification 2 coordinate)
      (cycle sheet) where
  integral := programs.first coordinate
  certificates := by
    intro index
    by_cases zero : coordinate = 0
    · rewrite [first, if_pos zero, programs.firstZero_eq, program_model, zero]
      exact (programs.cells index).certify (requests index) (fun {_ _} models => models.firstZero)
        (fun {_ _} _ _ _ retained => retained.firstZero)
        (Geometric.Basic.quarterRadius_pos (by decide) index) (paid index)
    · rewrite [first, if_neg zero, programs.firstOne_eq, program_model]
      have sameSpecification : Specification.firstDerivativeSpecification 2 coordinate =
          Specification.firstDerivativeSpecification 2 1 := by
        unfold Specification.firstDerivativeSpecification Specification.firstDerivativeNumerator
        rewrite [if_neg zero, if_neg (by decide : (1 : Fin 2) ≠ 0)]
        rfl
      rewrite [sameSpecification]
      exact (programs.cells index).certify (requests index) (fun {_ _} models => models.firstOne)
        (fun {_ _} _ _ _ retained => retained.firstOne)
        (Geometric.Basic.quarterRadius_pos (by decide) index) (paid index)

/-- The first certification retains the same original numerical refinement program. -/
theorem certifiedFirst_integral (programs : Programs sources) (requests : UniformRequests bounds uniformFloors)
    (paid : ∀ index, (requests index).stage ≤ (sources index).selection.stage) (coordinate : Fin 2) :
    (programs.certifiedFirst requests paid coordinate).integral = programs.first coordinate := by
  unfold certifiedFirst
  rfl

/-- Certify the original retained second program at either displayed basis coordinate. -/
def certifiedSecond (programs : Programs sources) (requests : UniformRequests bounds uniformFloors)
    (paid : ∀ index, (requests index).stage ≤ (sources index).selection.stage) (coordinate : Fin 2) :
    CertifiedPeriodProgram (Fibre.frameCurve Frame.frame) (Specification.secondDerivativeSpecification 2 coordinate)
      (cycle sheet) where
  integral := programs.second coordinate
  certificates := by
    intro index
    by_cases zero : coordinate = 0
    · rewrite [second, if_pos zero, programs.secondZero_eq, program_model, zero]
      exact (programs.cells index).certify (requests index) (fun {_ _} models => models.secondZero)
        (fun {_ _} _ _ _ retained => retained.secondZero)
        (Geometric.Basic.quarterRadius_pos (by decide) index) (paid index)
    · rewrite [second, if_neg zero, programs.secondOne_eq, program_model]
      have sameSpecification : Specification.secondDerivativeSpecification 2 coordinate =
          Specification.secondDerivativeSpecification 2 1 := by
        unfold Specification.secondDerivativeSpecification Specification.secondDerivativeNumerator
        rewrite [if_neg zero, if_neg (by decide : (1 : Fin 2) ≠ 0)]
        rfl
      rewrite [sameSpecification]
      exact (programs.cells index).certify (requests index) (fun {_ _} models => models.secondOne)
        (fun {_ _} _ _ _ retained => retained.secondOne)
        (Geometric.Basic.quarterRadius_pos (by decide) index) (paid index)

/-- The second certification retains the same original numerical refinement program. -/
theorem certifiedSecond_integral (programs : Programs sources) (requests : UniformRequests bounds uniformFloors)
    (paid : ∀ index, (requests index).stage ≤ (sources index).selection.stage) (coordinate : Fin 2) :
    (programs.certifiedSecond requests paid coordinate).integral = programs.second coordinate := by
  unfold certifiedSecond
  rfl

/-- Attach the literal shared side models to all six original certified numerical programs. -/
def attachment (programs : Programs sources) (requests : UniformRequests bounds uniformFloors)
    (paid : ∀ index, (requests index).stage ≤ (sources index).selection.stage)
    (stages : ∀ index, Stage 2 (loop sheet) index)
    (sources_eq : ∀ index, (stages index).sources = (programs.cells index).sourcePath) :
    Attachment Frame.frame (cycle sheet) (programs.certifiedValue requests paid)
      (programs.certifiedFirst requests paid) (programs.certifiedSecond requests paid) where
  stages := stages
  valueZero_eq := by
    intro index
    rewrite [sources_eq index]
    rewrite [certifiedValue_integral, value, if_pos rfl,
      programs.valueZero_eq, program_model]
    rfl
  valueOne_eq := by
    intro index
    rewrite [sources_eq index]
    rewrite [certifiedValue_integral, value, if_neg (by decide : (1 : Fin 2) ≠ 0),
      programs.valueOne_eq, program_model]
    rfl
  firstZero_eq := by
    intro index
    rewrite [sources_eq index]
    rewrite [certifiedFirst_integral, first, if_pos rfl,
      programs.firstZero_eq, program_model]
    rfl
  firstOne_eq := by
    intro index
    rewrite [sources_eq index]
    rewrite [certifiedFirst_integral, first, if_neg (by decide : (1 : Fin 2) ≠ 0),
      programs.firstOne_eq, program_model]
    rfl
  secondZero_eq := by
    intro index
    rewrite [sources_eq index]
    rewrite [certifiedSecond_integral, second, if_pos rfl,
      programs.secondZero_eq, program_model]
    rfl
  secondOne_eq := by
    intro index
    rewrite [sources_eq index]
    rewrite [certifiedSecond_integral, second, if_neg (by decide : (1 : Fin 2) ≠ 0),
      programs.secondOne_eq, program_model]
    rfl

end Programs

set_option genInjectivity false in
/-- A source-selected six-channel schedule on the original nonempty regular cycle.

Each stage retains the six uniform requests before selecting the common
Newton model. The original source cache, patch-wide scalar bounds, all
four side models and six numerical programs remain explicit owners.
-/
structure Schedule (sheet : Fin 2) where
  /-- The original continued chart's cached derivative and relation budgets. -/
  cache : Cache (patch sheet)
  /-- Patch-wide odd-power bounds consuming this same original clearance cache. -/
  bounds : UniformBounds (patch sheet)
  /-- The retained displacement-cost sum computed once from the original four sides. -/
  cost : Rational
  /-- The same retained cost is the original geometric procedure. -/
  cost_eq : cost = geometricCost sheet
  /-- The actual original corner points and their static primitive caches. -/
  vertices : Vertices sheet
  /-- The retained corner caches are the actual original point constructor. -/
  vertices_eq : vertices = Vertices.build sheet
  /-- The count-paid endpoint plans retained before any original model is selected. -/
  plans : ∀ index, EndpointPlans (Vertices.build sheet) index
  /-- The six uniform model-depth requests at each actual local allowance. -/
  requests : UniformRequests bounds id
  /-- The common original sources selected after all six integrand and eight endpoint floors. -/
  sources : Sources cache (fun index => max (requests index).stage (plans index).stage)
    (fun index => (plans index).targets.sourceTarget cost)
  /-- Each original source retains the exact earlier model-depth requests and computed target. -/
  sources_eq : ∀ index, sources index = (requests index).modelRequest cache (plans index).stage
    ((plans index).targets.sourceTarget cost)
    ((plans index).targets.sourceTarget_positive cost (cost_eq.symm ▸ geometricCost_nonnegative sheet))
  /-- All six numerical programs consume the same actual retained four-side stage caches. -/
  programs : Programs sources
  /-- The four original vertex-bank entries and actual finite lookups at each stage. -/
  banks : ∀ index, Vertices.Bank (Vertices.build sheet) (plans index).targets.endpoint
  /-- The retained source cells and admissions derived from those exact endpoint caches. -/
  sides : ∀ index, Stages.Sides (plans index) (banks index) (programs.cells index)

constructive_injectivity Schedule

namespace Schedule

/-- Prepare all original endpoint and integrand requests, then retain one common source and four admitted sides.

The original corner factors and inverse multipliers are computed once.
Each stage's source target comes from its actual path count and retained
displacement cost. Its four endpoint attachments serve both incident sides.
-/
def build (sheet : Fin 2) : Schedule sheet := by
  let cache := Cache.ofPatch (patch sheet)
  let bounds := UniformBounds.ofClearance (patch sheet) cache.clearance cache.clearance_eq
  let cost := geometricCost sheet
  let vertices := Vertices.build sheet
  let plans : ∀ index, EndpointPlans (Vertices.build sheet) index :=
    fun index => EndpointPlans.build vertices index
  let requests : UniformRequests bounds id := fun index => IntegrandRequests.build bounds index
    (Geometric.Basic.quarterRadius 1 index / 4)
    (Order.Field.div_pos_direct (Geometric.Basic.quarterRadius_pos (by decide) index) (by decide))
  let sources : Sources cache (fun index => max (requests index).stage (plans index).stage)
      (fun index => (plans index).targets.sourceTarget cost) :=
    fun index => (requests index).modelRequest cache (plans index).stage
      ((plans index).targets.sourceTarget cost)
      ((plans index).targets.sourceTarget_positive cost (geometricCost_nonnegative sheet))
  let programs := Programs.build (stageCells sources)
  let banks : ∀ index, Vertices.Bank (Vertices.build sheet) (plans index).targets.endpoint :=
    fun index => Vertices.Bank.build vertices (plans index).targets.endpoint (plans index).targets.endpoint_positive
  let sides : ∀ index, Stages.Sides (plans index) (banks index) (programs.cells index) :=
    fun index => Stages.Sides.build (plans index) (banks index) (programs.cells index) cost rfl rfl
      ((requests index).endpointFloor_le_modelRequest cache (plans index).stage
        ((plans index).targets.sourceTarget cost)
        ((plans index).targets.sourceTarget_positive cost (geometricCost_nonnegative sheet)))
  exact ⟨cache, bounds, cost, rfl, vertices, rfl, plans, requests, sources, fun _ => rfl,
    programs, banks, sides⟩

/-- Read the original admitted stage from its retained four side admissions without another root request. -/
@[expose] def stages (schedule : Schedule sheet) (index : Nat) : Stage 2 (loop sheet) index :=
  (schedule.sides index).stage

/-- The admitted stage consumes the literal same four cached numerical program cells. -/
theorem stages_eq (schedule : Schedule sheet) (index : Nat) :
    (schedule.stages index).sources = (schedule.programs.cells index).sourcePath :=
  (schedule.sides index).stage_sources_eq

/-- The actual common source stage pays all six retained uniform request floors. -/
theorem stage_paid (schedule : Schedule sheet) (index : Nat) :
    (schedule.requests index).stage ≤ (schedule.sources index).selection.stage := by
  rewrite [schedule.sources_eq index]
  exact (schedule.requests index).stage_le_modelRequest schedule.cache (schedule.plans index).stage
    ((schedule.plans index).targets.sourceTarget schedule.cost)
    ((schedule.plans index).targets.sourceTarget_positive schedule.cost
      (schedule.cost_eq.symm ▸ geometricCost_nonnegative sheet))

/-- The same original common source stage also pays all prepared endpoint model floors. -/
theorem endpoint_stage_paid (schedule : Schedule sheet) (index : Nat) :
    (schedule.plans index).stage ≤ (schedule.sources index).selection.stage := by
  rewrite [schedule.sources_eq index]
  exact (schedule.requests index).endpointFloor_le_modelRequest schedule.cache (schedule.plans index).stage
    ((schedule.plans index).targets.sourceTarget schedule.cost)
    ((schedule.plans index).targets.sourceTarget_positive schedule.cost
      (schedule.cost_eq.symm ▸ geometricCost_nonnegative sheet))

/-- Retain a six-channel query at the actual admitted lower-side source without rebuilding its model. -/
def lowerQuery (schedule : Schedule sheet) (index : Nat) : Cell.Query (schedule.sides index).lower :=
  let query := Cell.Query.ofModels (lifted := lowerSide sheet) (schedule.sources index)
    (schedule.programs.cells index).lower (lowerLeft_inside sheet) (lowerRight_inside sheet)
    (schedule.requests index) (Geometric.Basic.quarterRadius_pos (by decide) index) (schedule.stage_paid index)
    (schedule.sides index).lower (schedule.sides index).lower_eq
  query

/-- Retain the paid request cache at the distinct actual admitted right-side source. -/
def rightQuery (schedule : Schedule sheet) (index : Nat) : Cell.Query (schedule.sides index).right :=
  let query := Cell.Query.ofModels (lifted := rightSide sheet) (schedule.sources index)
    (schedule.programs.cells index).right (lowerRight_inside sheet) (upperRight_inside sheet)
    (schedule.requests index) (Geometric.Basic.quarterRadius_pos (by decide) index) (schedule.stage_paid index)
    (schedule.sides index).right (schedule.sides index).right_eq
  query

/-- Execute one lower-side bundle and read all six same-query integrand samples. -/
def lowerSamples (schedule : Schedule sheet) (index : Nat) (input : Rational)
    (lower : 0 ≤ input) (upper : input ≤ 1) : List Canonical :=
  (schedule.lowerQuery index).samples Frame.frame input lower upper

/-- Execute the distinct right-side query once before consuming its six integrand projections. -/
def rightSamples (schedule : Schedule sheet) (index : Nat) (input : Rational)
    (lower : 0 ≤ input) (upper : input ≤ 1) : List Canonical :=
  (schedule.rightQuery index).samples Frame.frame input lower upper

/-- Retain the original six certified programs and their literal common source attachment as one original period jet. -/
@[expose] def jet (schedule : Schedule sheet) : Basic.SynchronizedPeriodJet Frame.frame :=
  let value := schedule.programs.certifiedValue schedule.requests schedule.stage_paid
  let first := schedule.programs.certifiedFirst schedule.requests schedule.stage_paid
  let second := schedule.programs.certifiedSecond schedule.requests schedule.stage_paid
  let source := schedule.programs.attachment schedule.requests schedule.stage_paid schedule.stages schedule.stages_eq
  Basic.SynchronizedPeriodJet.ofSource (cycle sheet) value first second source

/-- The completed original jet retains the same nonempty lifted cycle and selected sheet. -/
theorem jet_cycle (schedule : Schedule sheet) : schedule.jet.cycle = cycle sheet := by
  unfold jet Basic.SynchronizedPeriodJet.ofSource
  rfl

/-- Every original source residual remains nonzero as a polynomial at coordinate zero.

The cubic vanishes at zero, so the retained Newton residual equation reads
one there, independently of the selected actual approximation depth.
-/
theorem residual_at_zero (schedule : Schedule sheet) (index : Nat) :
    (schedule.sources index).model.residual.eval (0 : Canonical) = 1 := by
  rewrite [(schedule.sources index).model.residual_eq (0 : Canonical)]
  have zero : (Paths.polynomial (2 : Canonical)).eval (0 : Canonical) = 0 := by decide +kernel
  rewrite [zero, Data.Gaussian.Basic.zero_mul, Data.Gaussian.Basic.sub_zero]
  rfl

/-- The literal same four-side cache is retained by the completed original jet's source attachment. -/
theorem jet_stage (schedule : Schedule sheet) (index : Nat) :
    (schedule.jet.source.stages index).sources = (schedule.programs.cells index).sourcePath := by
  unfold jet Basic.SynchronizedPeriodJet.ofSource Programs.attachment
  exact schedule.stages_eq index

/-- The completed value channel keeps its exact original retained numerical program. -/
theorem jet_value_integral (schedule : Schedule sheet) (coordinate : Fin 2) :
    (schedule.jet.value coordinate).integral = schedule.programs.value coordinate := by
  unfold jet Basic.SynchronizedPeriodJet.ofSource
  exact Programs.certifiedValue_integral schedule.programs schedule.requests schedule.stage_paid coordinate

/-- The completed first channel keeps its exact original retained numerical program. -/
theorem jet_first_integral (schedule : Schedule sheet) (coordinate : Fin 2) :
    (schedule.jet.first coordinate).integral = schedule.programs.first coordinate := by
  unfold jet Basic.SynchronizedPeriodJet.ofSource
  exact Programs.certifiedFirst_integral schedule.programs schedule.requests schedule.stage_paid coordinate

/-- The completed second channel keeps its exact original retained numerical program. -/
theorem jet_second_integral (schedule : Schedule sheet) (coordinate : Fin 2) :
    (schedule.jet.second coordinate).integral = schedule.programs.second coordinate := by
  unfold jet Basic.SynchronizedPeriodJet.ofSource
  exact Programs.certifiedSecond_integral schedule.programs schedule.requests schedule.stage_paid coordinate

end Schedule

end Purelib.Examples.Curves.Legendre.RegularCycle

end
