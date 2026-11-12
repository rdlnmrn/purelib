module

public import Purelib.Examples.Curves.Legendre.RegularCycle.Periods
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Curves.Legendre.Periods.Jets.Source.Stage

/-!
# Closed regular representatives with different starting vertices

The initial representative starts at the lower-left continued corner. Every
later representative traverses the same four original sides starting at the
lower-right corner. The selected sheet and each original cell are retained;
the two actual lifted basepoints are distinct.
-/

public section

namespace Purelib.Examples.Curves.Legendre.RegularCycle.Rotated

open Purelib.Geometry.Path.Gaussian.Lifted.Closed (ClosedLiftedPath)
open Purelib.Geometry.Path.Gaussian.Lifted.Refinement (LiftedCycleRefinement)
open Purelib.Curves.Legendre.Periods.Jets.Source
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Legendre

variable {sheet : Fin 2} {cache : Cache (patch sheet)} {floor index : Nat} {target allowance : Rational}
    {request : Request cache floor target} {plans : Stages.Plans sheet index} {bank : Stages.Bank plans}

attribute [local irreducible] patch lowerLeft lowerRight upperRight upperLeft
  Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

/-- The same four original continued sides, starting at the actual lower-right lifted corner. -/
@[expose] def loop (sheet : Fin 2) : ClosedLiftedPath 2 :=
  { basepoint := lowerRight sheet
    path := .cons (rightSide sheet)
      (.cons (upperSide sheet)
        (.cons (leftSide sheet)
          (.cons (lowerSide sheet) (.nil _)))) }

/-- Retain the original representative initially and the rotated closed representative at every later stage. -/
@[expose] def cycle (sheet : Fin 2) : LiftedCycleRefinement 2 :=
  ⟨fun index => match index with
    | 0 => RegularCycle.loop sheet
    | _ + 1 => loop sheet⟩

/-- The initial representative retains the original lower-left basepoint and cell order. -/
theorem cycle_initial (sheet : Fin 2) : (cycle sheet).liftedPath 0 = RegularCycle.loop sheet := rfl

/-- Every later representative retains the actual lower-right basepoint and rotated original cell order. -/
theorem cycle_later (sheet : Fin 2) (index : Nat) :
    (cycle sheet).liftedPath (index + 1) = loop sheet := rfl

/-- Both actual representatives remain nonempty paths with four original cells. -/
theorem cycle_cellCount (sheet : Fin 2) (index : Nat) :
    ((cycle sheet).liftedPath index).cellCount = 4 := by
  cases index with
  | zero => rfl
  | succ index => rfl

/-- The initial and every later lifted representative have genuinely different basepoints. -/
theorem basepoints_ne (sheet : Fin 2) (index : Nat) :
    ((cycle sheet).liftedPath 0).basepoint ≠ ((cycle sheet).liftedPath (index + 1)).basepoint := by
  intro equal
  exact first_side_nontrivial sheet (congrArg (fun point => point.coordinate) equal)

/-- Read the same four actual source cells in the rotated closed path's original order. -/
@[expose] def sources {cells : Cells (sheet := sheet) request allowance} (sides : Stages.Sides plans bank cells) :
    Path 2 (loop sheet).path :=
  sides.admitted.sources.rotateHead

/-- The actual rotated source spine contains the same four retained cells in cyclic order. -/
theorem sources_eq {cells : Cells (sheet := sheet) request allowance} (sides : Stages.Sides plans bank cells) :
    sources sides = .cons sides.right (.cons sides.upper (.cons sides.left (.cons sides.lower (.nil _)))) := by
  unfold sources
  rewrite [sides.admitted_sources_eq]
  rfl

/-- The exact rotated admission type indexed by the actually retained source stage's target and bank caches. -/
@[expose] def AdmittedCells {cells : Cells (sheet := sheet) request allowance}
    (sides : Stages.Sides plans bank cells) (actual : Stage 2 (RegularCycle.loop sheet) index) :=
  Admissions (actual.targets.onPath (loop sheet).path rfl) actual.bank (sources sides)

/-- Reindex the same already-computed original admissions by the actual retained target and bank caches. -/
def retainedAdmissions {cells : Cells (sheet := sheet) request allowance} (sides : Stages.Sides plans bank cells) :
    AdmittedCells sides sides.admitted :=
  (sides.retainedAdmissions.rotateHead sides.admitted.sources).onPath (loop sheet).path rfl

/-- Retain a rotated source chain and actual lower-right bank lookup under a cached original stage's count budget. -/
@[expose] def ofRetained (actual : Stage 2 (RegularCycle.loop sheet) index) (retained : Path 2 (loop sheet).path)
    (paid : Admissions (actual.targets.onPath (loop sheet).path rfl) actual.bank retained)
    (base : Vertex.Bank.Found actual.bank (lowerRight sheet)) : Stage 2 (loop sheet) index :=
  (Stage.ofAdmissions (actual.targets.onPath (loop sheet).path rfl)
    (actual.targets.onPath_computed (loop sheet).path rfl actual.targets_eq) actual.bank base retained paid).lower
      index actual.index_le_precision

/-- Construct the rotated closed stage from the actual retained cells, bank lookup and paid original admissions.

The basepoint is the original lower-right bank owner. The initial stage's
primitive value is not compared with this value; the new stage telescopes
on its own actual closed lift and retains its own endpoint readings.
-/
@[expose] def stage {cells : Cells (sheet := sheet) request allowance} (sides : Stages.Sides plans bank cells) :
    Stage 2 (loop sheet) index :=
  ofRetained sides.admitted (sources sides) (retainedAdmissions sides) sides.admitted_lowerRight

/-- The rotated stage retains the same actual first source cell as the original right side. -/
theorem stage_first_source {cells : Cells (sheet := sheet) request allowance} (sides : Stages.Sides plans bank cells) :
    (stage sides).sources =
      .cons sides.right (.cons sides.upper (.cons sides.left (.cons sides.lower (.nil _)))) := sources_eq sides

/-- The rotated stage's actual primitive basepoint owner is the retained original lower-right bank entry. -/
theorem stage_base_original {cells : Cells (sheet := sheet) request allowance}
    (sides : Stages.Sides plans bank cells) : (stage sides).base.original = bank.lowerRight.original :=
  sides.admitted_lowerRight_original

/-- Retain the initial admitted representative and then rotate each later stage's own actual source and vertex caches.

Each representative uses the bank and endpoint attachments paid for its
actual index. No primitive-channel comparison between representatives is
required to derive their individual closed telescopes.
-/
@[expose] def representatives (schedule : Schedule sheet) (index : Nat) :
    Stage 2 ((cycle sheet).liftedPath index) index :=
  match index with
  | 0 => schedule.stages 0
  | later + 1 => stage (schedule.sides (later + 1))

/-- The initial admitted representative retains the original stage's lower-left bank basepoint. -/
theorem representatives_initial (schedule : Schedule sheet) :
    representatives schedule 0 = schedule.stages 0 := rfl

/-- The initial representative retains its own cached lower-left primitive channel owner. -/
theorem representatives_initial_base (schedule : Schedule sheet) :
    (representatives schedule 0).base.original = (schedule.banks 0).lowerLeft.original :=
  (schedule.sides 0).admitted_lowerLeft_original

/-- Every later admitted representative uses the actual rotated sources and lower-right lookup of its own stage. -/
theorem representatives_later (schedule : Schedule sheet) (index : Nat) :
    representatives schedule (index + 1) = stage (schedule.sides (index + 1)) := rfl

/-- The later representative retains its own stage's actual lower-right primitive channel owner. -/
theorem representatives_later_base (schedule : Schedule sheet) (index : Nat) :
    (representatives schedule (index + 1)).base.original = (schedule.banks (index + 1)).lowerRight.original :=
  stage_base_original (schedule.sides (index + 1))

/-- The actual selected bank entries at the initial and later representatives have distinct lifted points. -/
theorem retained_basepoints_ne (schedule : Schedule sheet) (index : Nat) :
    (representatives schedule 0).base.entry.point ≠ (representatives schedule (index + 1)).base.entry.point := by
  intro equal
  exact basepoints_ne sheet index
    ((representatives schedule 0).base.point_eq.symm.trans
      (equal.trans (representatives schedule (index + 1)).base.point_eq))

/-- Retain the initial numerical model and cyclically rotate each later model's original cell list. -/
@[expose] def models (program : RefinementProgram) (index : Nat) : PathModel :=
  match index with
  | 0 => program.model 0
  | later + 1 => (program.model (later + 1)).rotateHead

/-- The rotated numerical models have exactly the original finite samples at every index. -/
theorem models_sample (program : RefinementProgram) (index : Nat) :
    (models program index).integralSample = (program.model index).integralSample := by
  cases index with
  | zero => rfl
  | succ later => exact (program.model (later + 1)).integralSample_rotateHead

/-- The rotated models retain the original numerical program's count-weighted local allowances. -/
theorem models_allowance (program : RefinementProgram) (index : Nat) :
    (models program index).aggregateAllowance ≤
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius program.errorScale index := by
  cases index with
  | zero => exact program.modelAllowance_le 0
  | succ later =>
    exact (program.model (later + 1)).aggregateAllowance_rotateHead.le.trans (program.modelAllowance_le (later + 1))

/-- Reuse an original numerical program with its same samples, scales and bounds on the rotated retained cell lists. -/
def integral (program : RefinementProgram) : RefinementProgram :=
  program.withModels (models program) (models_sample program) (models_allowance program)

/-- The reused numerical program's model is the actual retained original cyclic cell permutation. -/
theorem integral_model (program : RefinementProgram) (index : Nat) :
    (integral program).model index = models program index :=
  program.withModels_model (models program) (models_sample program) (models_allowance program) index

/-- The reused numerical program retains exactly the original finite samples. -/
theorem integral_sample (program : RefinementProgram) (index : Nat) :
    ((integral program).model index).integralSample = (program.model index).integralSample :=
  (congrArg (fun model => model.integralSample) (integral_model program index)).trans (models_sample program index)

/-- The reused numerical program retains the original geometric error scale. -/
theorem integral_errorScale (program : RefinementProgram) : (integral program).errorScale = program.errorScale := by
  unfold integral
  rfl

/-- The reused numerical program retains the original common sample bound. -/
theorem integral_centerBound (program : RefinementProgram) : (integral program).centerBound = program.centerBound := by
  unfold integral
  rfl

/-- Reuse the original period program and its actual uniform certificates on the rotated lifted representatives.

The numerical models change only by cyclic cell permutation. Every
original certified cell and its observation callback remains retained;
this constructor executes no new integrand or root observation.
-/
def certified {differential : OddPowerDifferential (Paths.polynomial 2)}
    (original : CertifiedPeriodProgram (Fibre.frameCurve Frame.frame) differential (RegularCycle.cycle sheet)) :
    CertifiedPeriodProgram (Fibre.frameCurve Frame.frame) differential (cycle sheet) where
  integral := integral original.integral
  certificates := by
    intro index
    rewrite [integral_model]
    cases index with
    | zero => exact original.certificates 0
    | succ later => exact (original.certificates (later + 1)).rotateHead

/-- The reused certified period keeps the original numerical program's actual cyclically retained models. -/
theorem certified_integral {differential : OddPowerDifferential (Paths.polynomial 2)}
    (original : CertifiedPeriodProgram (Fibre.frameCurve Frame.frame) differential (RegularCycle.cycle sheet)) :
    (certified original).integral = integral original.integral := by
  unfold certified
  rfl

/-- The original completed jet's source chain is the same actually cached admitted stage of its schedule. -/
theorem original_sources (schedule : Schedule sheet) (index : Nat) :
    (schedule.jet.source.stages index).sources = (schedule.stages index).sources :=
  (schedule.jet_stage index).trans (schedule.stages_eq index).symm

/-- Reuse all six original certified programs on the actual rotating closed representatives.

The original programs retain their scales, allowances, samples and uniform
certificates. Their actual cell permutations are tied to the same retained
source cells and each stage's own cached bank and branch admissions.
-/
@[expose] def jet (schedule : Schedule sheet) : Basic.SynchronizedPeriodJet Frame.frame :=
  let original := schedule.jet
  let value := fun coordinate => certified (original.value coordinate)
  let first := fun coordinate => certified (original.first coordinate)
  let second := fun coordinate => certified (original.second coordinate)
  let attached : Attachment Frame.frame (cycle sheet) value first second :=
    { stages := representatives schedule
      valueZero_eq := by
        intro index
        change ((integral (original.value 0).integral).model index).cells = _
        rewrite [integral_model]
        cases index with
        | zero =>
          exact (original.source.valueZero_eq 0).trans
            (congrArg (fun source => source.valueZero) (original_sources schedule 0))
        | succ later =>
          have scalar := (original.source.valueZero_eq (later + 1)).trans
            (congrArg (fun source => source.valueZero)
              ((original_sources schedule (later + 1)).trans (schedule.sides (later + 1)).admitted_sources_eq))
          change ((original.value 0).integral.model (later + 1)).rotateHead.cells = _
          have permuted := congrArg (fun cells => (PathModel.mk cells).rotateHead.cells) scalar
          exact permuted.trans
            (congrArg (fun source => source.valueZero) (stage_first_source (schedule.sides (later + 1)))).symm
      valueOne_eq := by
        intro index
        change ((integral (original.value 1).integral).model index).cells = _
        rewrite [integral_model]
        cases index with
        | zero =>
          exact (original.source.valueOne_eq 0).trans
            (congrArg (fun source => source.valueOne) (original_sources schedule 0))
        | succ later =>
          have scalar := (original.source.valueOne_eq (later + 1)).trans
            (congrArg (fun source => source.valueOne)
              ((original_sources schedule (later + 1)).trans (schedule.sides (later + 1)).admitted_sources_eq))
          change ((original.value 1).integral.model (later + 1)).rotateHead.cells = _
          have permuted := congrArg (fun cells => (PathModel.mk cells).rotateHead.cells) scalar
          exact permuted.trans
            (congrArg (fun source => source.valueOne) (stage_first_source (schedule.sides (later + 1)))).symm
      firstZero_eq := by
        intro index
        change ((integral (original.first 0).integral).model index).cells = _
        rewrite [integral_model]
        cases index with
        | zero =>
          exact (original.source.firstZero_eq 0).trans
            (congrArg (fun source => source.firstZero) (original_sources schedule 0))
        | succ later =>
          have scalar := (original.source.firstZero_eq (later + 1)).trans
            (congrArg (fun source => source.firstZero)
              ((original_sources schedule (later + 1)).trans (schedule.sides (later + 1)).admitted_sources_eq))
          change ((original.first 0).integral.model (later + 1)).rotateHead.cells = _
          have permuted := congrArg (fun cells => (PathModel.mk cells).rotateHead.cells) scalar
          exact permuted.trans
            (congrArg (fun source => source.firstZero) (stage_first_source (schedule.sides (later + 1)))).symm
      firstOne_eq := by
        intro index
        change ((integral (original.first 1).integral).model index).cells = _
        rewrite [integral_model]
        cases index with
        | zero =>
          exact (original.source.firstOne_eq 0).trans
            (congrArg (fun source => source.firstOne) (original_sources schedule 0))
        | succ later =>
          have scalar := (original.source.firstOne_eq (later + 1)).trans
            (congrArg (fun source => source.firstOne)
              ((original_sources schedule (later + 1)).trans (schedule.sides (later + 1)).admitted_sources_eq))
          change ((original.first 1).integral.model (later + 1)).rotateHead.cells = _
          have permuted := congrArg (fun cells => (PathModel.mk cells).rotateHead.cells) scalar
          exact permuted.trans
            (congrArg (fun source => source.firstOne) (stage_first_source (schedule.sides (later + 1)))).symm
      secondZero_eq := by
        intro index
        change ((integral (original.second 0).integral).model index).cells = _
        rewrite [integral_model]
        cases index with
        | zero =>
          exact (original.source.secondZero_eq 0).trans
            (congrArg (fun source => source.secondZero) (original_sources schedule 0))
        | succ later =>
          have scalar := (original.source.secondZero_eq (later + 1)).trans
            (congrArg (fun source => source.secondZero)
              ((original_sources schedule (later + 1)).trans (schedule.sides (later + 1)).admitted_sources_eq))
          change ((original.second 0).integral.model (later + 1)).rotateHead.cells = _
          have permuted := congrArg (fun cells => (PathModel.mk cells).rotateHead.cells) scalar
          exact permuted.trans
            (congrArg (fun source => source.secondZero) (stage_first_source (schedule.sides (later + 1)))).symm
      secondOne_eq := by
        intro index
        change ((integral (original.second 1).integral).model index).cells = _
        rewrite [integral_model]
        cases index with
        | zero =>
          exact (original.source.secondOne_eq 0).trans
            (congrArg (fun source => source.secondOne) (original_sources schedule 0))
        | succ later =>
          have scalar := (original.source.secondOne_eq (later + 1)).trans
            (congrArg (fun source => source.secondOne)
              ((original_sources schedule (later + 1)).trans (schedule.sides (later + 1)).admitted_sources_eq))
          change ((original.second 1).integral.model (later + 1)).rotateHead.cells = _
          have permuted := congrArg (fun cells => (PathModel.mk cells).rotateHead.cells) scalar
          exact permuted.trans
            (congrArg (fun source => source.secondOne) (stage_first_source (schedule.sides (later + 1)))).symm }
  Basic.SynchronizedPeriodJet.ofSource (cycle sheet) value first second attached

/-- The rotating value channels reuse the original numerical programs' cyclic models and exact samples. -/
theorem jet_value_integral (schedule : Schedule sheet) (coordinate : Fin 2) :
    ((jet schedule).value coordinate).integral = integral ((schedule.jet.value coordinate).integral) := by
  unfold jet Basic.SynchronizedPeriodJet.ofSource
  exact certified_integral (schedule.jet.value coordinate)

/-- The rotating first channels reuse the original numerical programs' cyclic models and exact samples. -/
theorem jet_first_integral (schedule : Schedule sheet) (coordinate : Fin 2) :
    ((jet schedule).first coordinate).integral = integral ((schedule.jet.first coordinate).integral) := by
  unfold jet Basic.SynchronizedPeriodJet.ofSource
  exact certified_integral (schedule.jet.first coordinate)

/-- The rotating second channels reuse the original numerical programs' cyclic models and exact samples. -/
theorem jet_second_integral (schedule : Schedule sheet) (coordinate : Fin 2) :
    ((jet schedule).second coordinate).integral = integral ((schedule.jet.second coordinate).integral) := by
  unfold jet Basic.SynchronizedPeriodJet.ofSource
  exact certified_integral (schedule.jet.second coordinate)

/-- Every value-channel sample vanishes on these original contractible regular representatives. -/
theorem jet_value_sample_zero (schedule : Schedule sheet) (coordinate : Fin 2) (index : Nat) :
    (((jet schedule).value coordinate).integral.model index).integralSample = 0 := by
  rewrite [jet_value_integral, integral_sample, schedule.jet_value_integral]
  exact schedule.programs.value_integralSample_zero coordinate index

/-- Every first-channel sample vanishes on these original contractible regular representatives. -/
theorem jet_first_sample_zero (schedule : Schedule sheet) (coordinate : Fin 2) (index : Nat) :
    (((jet schedule).first coordinate).integral.model index).integralSample = 0 := by
  rewrite [jet_first_integral, integral_sample, schedule.jet_first_integral]
  exact schedule.programs.first_integralSample_zero coordinate index

/-- Every second-channel sample vanishes on these original contractible regular representatives. -/
theorem jet_second_sample_zero (schedule : Schedule sheet) (coordinate : Fin 2) (index : Nat) :
    (((jet schedule).second coordinate).integral.model index).integralSample = 0 := by
  rewrite [jet_second_integral, integral_sample, schedule.jet_second_integral]
  exact schedule.programs.second_integralSample_zero coordinate index

/-- The completed original six-channel jet retains the actual varying lifted representatives. -/
theorem jet_cycle (schedule : Schedule sheet) : (jet schedule).cycle = cycle sheet := rfl

/-- The completed source attachment retains the same actual stage banks and endpoint admissions. -/
theorem jet_stage (schedule : Schedule sheet) (index : Nat) : (jet schedule).source.stages index =
    representatives schedule index := rfl

end Purelib.Examples.Curves.Legendre.RegularCycle.Rotated

end
