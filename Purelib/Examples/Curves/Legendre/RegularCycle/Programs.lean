module

public import Purelib.Examples.Curves.Legendre.RegularCycle
public import Purelib.Curves.Legendre.Periods.Jets.Source.Cells
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path
public import Purelib.Integration.Program.Gaussian.Basic
public import Purelib.Integration.Path.Lifted.Model
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Polynomial.Dense.Gaussian.Antiderivative
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Actual polynomial programs on the regular four-sided cycle

One retained source request at each stage supplies all six spatial
coefficients. The four original cell caches consume these same tables.
Their global polynomial primitives telescope on the actual closed lifted
cycle, giving internal coherence and sample bounds for all six programs.
-/

public section

namespace Purelib.Examples.Curves.Legendre.RegularCycle

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Legendre.Periods.Jets.Source
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic
open Purelib.Approximation.Rational

variable {sheet : Fin 2} {cache : Cache (patch sheet)} {floor : Nat} {target allowance : Rational}

attribute [local irreducible] patch lowerLeft lowerRight upperRight upperLeft

/-- The exact original source cell type with the fixture's retained patch and parameter indices fixed. -/
@[expose] def SideModels (request : Request cache floor target) (start finish : Canonical) (allowance : Rational) :=
  CellModels (parameter := 2) (count := 2) (patch := patch sheet) request start finish allowance

set_option genInjectivity false in
/-- The four actual side caches consuming one original source request and local allowance.

All six coefficients on every side use that same retained model. The
displayed original endpoints and sheet-labelled cycle remain indexed. -/
structure Cells (request : Request cache floor target) (allowance : Rational) where
  /-- The original lower-side six-channel cell cache. -/
  lower : SideModels request (lowerLeft sheet).coordinate (lowerRight sheet).coordinate allowance
  /-- The original right-side six-channel cell cache. -/
  right : SideModels request (lowerRight sheet).coordinate (upperRight sheet).coordinate allowance
  /-- The original upper-side six-channel cell cache. -/
  upper : SideModels request (upperRight sheet).coordinate (upperLeft sheet).coordinate allowance
  /-- The original left-side six-channel cell cache. -/
  left : SideModels request (upperLeft sheet).coordinate (lowerLeft sheet).coordinate allowance

constructive_injectivity Cells

namespace Cells

/-- Cache the four actual side models once, preserving all six shared source coefficients. -/
@[expose] def build (request : Request cache floor target) (allowance : Rational) (nonnegative : 0 ≤ allowance) :
    Cells request allowance :=
  let lower : SideModels request _ _ allowance :=
    CellModels.build request (lowerLeft sheet).coordinate (lowerRight sheet).coordinate allowance nonnegative
  let right : SideModels request _ _ allowance :=
    CellModels.build request (lowerRight sheet).coordinate (upperRight sheet).coordinate allowance nonnegative
  let upper : SideModels request _ _ allowance :=
    CellModels.build request (upperRight sheet).coordinate (upperLeft sheet).coordinate allowance nonnegative
  let left : SideModels request _ _ allowance :=
    CellModels.build request (upperLeft sheet).coordinate (lowerLeft sheet).coordinate allowance nonnegative
  ⟨lower, right, upper, left⟩

/-- A projection of one original spatial coefficient from a retained six-channel cell cache. -/
@[expose] def Projection (request : Request cache floor target) (allowance : Rational)
    (source : Coefficients) :=
  {start finish : Canonical} → (models : SideModels request start finish allowance) →
    Spatial.Pullback models.coordinate source allowance

/-- Read one coefficient's four original cached cells in the retained lifted-cycle order. -/
@[expose] def path {request : Request cache floor target} (cells : Cells request allowance)
    {source : Coefficients} (projection : Projection request allowance source) :
    Path.Basic.PathModel :=
  ⟨[(projection cells.lower).model, (projection cells.right).model,
    (projection cells.upper).model, (projection cells.left).model]⟩

/-- The four retained coefficient cells follow the same original nonempty lifted loop. -/
theorem follows {request : Request cache floor target} (cells : Cells request allowance)
    {source : Coefficients} (projection : Projection request allowance source) :
    LiftedPath.FollowedBy (cells.path projection).cells (loop sheet).path :=
  .cons (projection cells.lower).start_eq (projection cells.lower).finish_eq
    (.cons (projection cells.right).start_eq (projection cells.right).finish_eq
      (.cons (projection cells.upper).start_eq (projection cells.upper).finish_eq
        (.cons (projection cells.left).start_eq (projection cells.left).finish_eq (.nil _))))

/-- The actual four cell integrals of a single retained spatial polynomial telescope to zero. -/
theorem integralSample_zero {request : Request cache floor target} (cells : Cells request allowance)
    {source : Coefficients} (projection : Projection request allowance source) :
    (cells.path projection).integralSample = 0 := by
  let primitive := Antiderivative.denseAntiderivative source
  have derivative := Antiderivative.denseAntiderivative_derivative source
  change (projection cells.lower).model.integralSample + ((projection cells.right).model.integralSample +
    ((projection cells.upper).model.integralSample + ((projection cells.left).model.integralSample + 0))) = 0
  rewrite [(projection cells.lower).integralSample_primitive primitive derivative,
    (projection cells.right).integralSample_primitive primitive derivative,
    (projection cells.upper).integralSample_primitive primitive derivative,
    (projection cells.left).integralSample_primitive primitive derivative]
  ring1

/-- Attach the same four original side caches to their actual lifted source chain. -/
@[expose] def sourcePath {request : Request cache floor target}
    (cells : Cells (sheet := sheet) request allowance) : Source.Path 2 (loop sheet).path :=
  let lower := Source.Cell.ofModels request (lowerSide sheet) cells.lower
    (lowerLeft_inside sheet) (lowerRight_inside sheet)
  let right := Source.Cell.ofModels request (rightSide sheet) cells.right
    (lowerRight_inside sheet) (upperRight_inside sheet)
  let upper := Source.Cell.ofModels request (upperSide sheet) cells.upper
    (upperRight_inside sheet) (upperLeft_inside sheet)
  let left := Source.Cell.ofModels request (leftSide sheet) cells.left
    (upperLeft_inside sheet) (lowerLeft_inside sheet)
  .cons lower (.cons right (.cons upper (.cons left (.nil _))))


end Cells

/-- The original count-weighted sum of the four retained geometric squared displacements. -/
@[expose] def errorScale (sheet : Fin 2) : Rational :=
  4 * (Canonical.normSq ((lowerRight sheet).coordinate - (lowerLeft sheet).coordinate) +
    Canonical.normSq ((upperRight sheet).coordinate - (lowerRight sheet).coordinate) +
    Canonical.normSq ((upperLeft sheet).coordinate - (upperRight sheet).coordinate) +
    Canonical.normSq ((lowerLeft sheet).coordinate - (upperLeft sheet).coordinate))

/-- The actual four-sided displacement scale is nonnegative. -/
theorem errorScale_nonnegative (sheet : Fin 2) : 0 ≤ errorScale sheet := by
  unfold errorScale
  exact Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (add_nonneg (add_nonneg (Canonical.normSq_nonneg _) (Canonical.normSq_nonneg _))
      (Canonical.normSq_nonneg _)) (Canonical.normSq_nonneg _))

/-- The original count-weighted allowance equals the computed cycle scale times the retained local allowance. -/
theorem Cells.aggregateAllowance_eq {request : Request cache floor target} (cells : Cells request allowance)
    {source : Coefficients} (projection : Projection request allowance source) :
    (cells.path projection).aggregateAllowance = errorScale sheet * allowance := by
  change (4 : Rational) * ((projection cells.lower).model.weightedAllowance +
    ((projection cells.right).model.weightedAllowance + ((projection cells.upper).model.weightedAllowance +
      ((projection cells.left).model.weightedAllowance + 0)))) = _
  rewrite [(projection cells.lower).weightedAllowance_eq, (projection cells.right).weightedAllowance_eq,
    (projection cells.upper).weightedAllowance_eq, (projection cells.left).weightedAllowance_eq, errorScale]
  ring1

/-- The indexed original source requests consumed by a retained stage family. -/
@[expose] def Sources (cache : Cache (patch sheet)) (floors : Nat → Nat) (targets : Nat → Rational) :=
  (index : Nat) → Request cache (floors index) (targets index)

/-- The exact four-side cell caches sharing each source request's six tables and positive geometric allowance. -/
@[expose] def StageCells {floors : Nat → Nat} {targets : Nat → Rational}
    (sources : Sources cache floors targets) :=
  (index : Nat) → Cells (sources index) (Geometric.Basic.quarterRadius 1 index)

/-- Build all four side caches from each retained original source request once. -/
@[expose] def stageCells {floors : Nat → Nat} {targets : Nat → Rational}
    (sources : Sources cache floors targets) : StageCells sources :=
  fun index => Cells.build (sources index) (Geometric.Basic.quarterRadius 1 index)
    (Geometric.Basic.quarterRadius_nonneg (by decide) index)

/-- Derive a refinement program from the same actual side caches and a retained coefficient projection.

The finite antiderivative telescope proves all sample comparisons and the
zero center bound internally. The positive shrinking local allowance uses
the actual geometric scale; the original Newton source is unchanged. -/
def program {floors : Nat → Nat} {targets : Nat → Rational} {sources : Sources cache floors targets}
    (cells : StageCells sources) (source : Nat → Coefficients)
    (projection : (index : Nat) → Cells.Projection (sources index) (Geometric.Basic.quarterRadius 1 index)
      (source index)) :
    RefinementProgram where
  model := fun index => (cells index).path (projection index)
  errorScale := errorScale sheet
  errorScale_nonneg := errorScale_nonnegative sheet
  modelAllowance_le := by
    intro index
    rewrite [(cells index).aggregateAllowance_eq (projection index), Geometric.Basic.quarterRadius_eq_mul_pow,
      Geometric.Basic.quarterRadius_eq_mul_pow]
    exact (show errorScale sheet * (1 * (4 : Rational)⁻¹ ^ index) =
      errorScale sheet * (4 : Rational)⁻¹ ^ index by ring1).le
  later_close := by
    intro earlier later _
    rewrite [(cells later).integralSample_zero (projection later),
      (cells earlier).integralSample_zero (projection earlier), Data.Gaussian.Basic.sub_self, Canonical.normSq_zero]
    exact Geometric.Basic.quarterRadius_nonneg (errorScale_nonnegative sheet) earlier
  centerBound := 0
  centerBound_nonneg := Order.Basic.le_refl _
  sample_bounded := by
    intro index
    rewrite [(cells index).integralSample_zero (projection index), Canonical.normSq_zero]
    exact Order.Basic.le_refl _

/-- The derived refinement program consumes precisely the retained four-side stage cache. -/
theorem program_model {floors : Nat → Nat} {targets : Nat → Rational} {sources : Sources cache floors targets}
    (cells : StageCells sources) (source : Nat → Coefficients)
    (projection : (index : Nat) → Cells.Projection (sources index) (Geometric.Basic.quarterRadius 1 index)
      (source index)) (index : Nat) :
    (program cells source projection).model index = (cells index).path (projection index) := by
  unfold program
  rfl

set_option genInjectivity false in
/-- Six retained refinement programs consuming the same original four-side caches at every source stage.

The actual common source requests remain indexed. Each program's defining
equation retains its original coefficient projection and the one shared
stage cache; both labelled sheets use their original lifted cycle. -/
structure Programs {floors : Nat → Nat} {targets : Nat → Rational} (sources : Sources cache floors targets) where
  /-- The actual shared side caches of every retained original source request. -/
  cells : StageCells sources
  /-- The original first value-channel program. -/
  valueZero : RefinementProgram
  /-- The program consumes the actual original first value coefficients. -/
  valueZero_eq : valueZero = program cells (fun index => (sources index).models.valueZero)
    (fun _ {_ _} models => models.valueZero)
  /-- The original second value-channel program. -/
  valueOne : RefinementProgram
  /-- This program consumes the same original side caches and second value coefficients. -/
  valueOne_eq : valueOne = program cells (fun index => (sources index).models.valueOne)
    (fun _ {_ _} models => models.valueOne)
  /-- The original first first-derivative-channel program. -/
  firstZero : RefinementProgram
  /-- The program consumes the actual original first derivative coefficients. -/
  firstZero_eq : firstZero = program cells (fun index => (sources index).models.firstZero)
    (fun _ {_ _} models => models.firstZero)
  /-- The original second first-derivative-channel program. -/
  firstOne : RefinementProgram
  /-- The program consumes the retained weighted first derivative coefficients. -/
  firstOne_eq : firstOne = program cells (fun index => (sources index).models.firstOne)
    (fun _ {_ _} models => models.firstOne)
  /-- The original first second-derivative-channel program. -/
  secondZero : RefinementProgram
  /-- The program consumes the actual original first second derivative coefficients. -/
  secondZero_eq : secondZero = program cells (fun index => (sources index).models.secondZero)
    (fun _ {_ _} models => models.secondZero)
  /-- The original second second-derivative-channel program. -/
  secondOne : RefinementProgram
  /-- The program consumes the retained weighted second derivative coefficients. -/
  secondOne_eq : secondOne = program cells (fun index => (sources index).models.secondOne)
    (fun _ {_ _} models => models.secondOne)

constructive_injectivity Programs

namespace Programs

variable {floors : Nat → Nat} {targets : Nat → Rational} {sources : Sources cache floors targets}

/-- Construct all six actual programs from the same retained original side caches. -/
def build (cells : StageCells sources) : Programs sources :=
  let valueZero := program cells (fun index => (sources index).models.valueZero)
    (fun _ {_ _} models => models.valueZero)
  let valueOne := program cells (fun index => (sources index).models.valueOne)
    (fun _ {_ _} models => models.valueOne)
  let firstZero := program cells (fun index => (sources index).models.firstZero)
    (fun _ {_ _} models => models.firstZero)
  let firstOne := program cells (fun index => (sources index).models.firstOne)
    (fun _ {_ _} models => models.firstOne)
  let secondZero := program cells (fun index => (sources index).models.secondZero)
    (fun _ {_ _} models => models.secondZero)
  let secondOne := program cells (fun index => (sources index).models.secondOne)
    (fun _ {_ _} models => models.secondOne)
  ⟨cells, valueZero, rfl, valueOne, rfl, firstZero, rfl, firstOne, rfl, secondZero, rfl, secondOne, rfl⟩

/-- The constructor retains the exact supplied original stage caches. -/
theorem build_cells (cells : StageCells sources) : (build cells).cells = cells := by
  unfold build
  rfl

/-- Select an original retained value-channel program at the displayed basis coordinate. -/
@[expose] def value (programs : Programs sources) (coordinate : Fin 2) : RefinementProgram :=
  if coordinate = 0 then programs.valueZero else programs.valueOne

/-- Select an original retained first-derivative-channel program at that basis coordinate. -/
@[expose] def first (programs : Programs sources) (coordinate : Fin 2) : RefinementProgram :=
  if coordinate = 0 then programs.firstZero else programs.firstOne

/-- Select an original retained second-derivative-channel program at that basis coordinate. -/
@[expose] def second (programs : Programs sources) (coordinate : Fin 2) : RefinementProgram :=
  if coordinate = 0 then programs.secondZero else programs.secondOne

/-- Every retained original value-channel model follows the actual four-edge lifted cycle. -/
theorem value_follows (programs : Programs sources) (coordinate : Fin 2) (index : Nat) :
    LiftedPath.FollowedBy ((programs.value coordinate).model index).cells (loop sheet).path := by
  by_cases zero : coordinate = 0
  · rewrite [value, if_pos zero, programs.valueZero_eq, program_model]
    exact (programs.cells index).follows (fun {_ _} models => models.valueZero)
  · rewrite [value, if_neg zero, programs.valueOne_eq, program_model]
    exact (programs.cells index).follows (fun {_ _} models => models.valueOne)

/-- Every retained first-derivative model follows that same original nonempty lifted cycle. -/
theorem first_follows (programs : Programs sources) (coordinate : Fin 2) (index : Nat) :
    LiftedPath.FollowedBy ((programs.first coordinate).model index).cells (loop sheet).path := by
  by_cases zero : coordinate = 0
  · rewrite [first, if_pos zero, programs.firstZero_eq, program_model]
    exact (programs.cells index).follows (fun {_ _} models => models.firstZero)
  · rewrite [first, if_neg zero, programs.firstOne_eq, program_model]
    exact (programs.cells index).follows (fun {_ _} models => models.firstOne)

/-- Every retained second-derivative model follows the same original nonempty lifted cycle. -/
theorem second_follows (programs : Programs sources) (coordinate : Fin 2) (index : Nat) :
    LiftedPath.FollowedBy ((programs.second coordinate).model index).cells (loop sheet).path := by
  by_cases zero : coordinate = 0
  · rewrite [second, if_pos zero, programs.secondZero_eq, program_model]
    exact (programs.cells index).follows (fun {_ _} models => models.secondZero)
  · rewrite [second, if_neg zero, programs.secondOne_eq, program_model]
    exact (programs.cells index).follows (fun {_ _} models => models.secondOne)

/-- Every original value-channel sample is zero by the source polynomial antiderivative telescope. -/
theorem value_integralSample_zero (programs : Programs sources) (coordinate : Fin 2) (index : Nat) :
    ((programs.value coordinate).model index).integralSample = 0 := by
  by_cases zero : coordinate = 0
  · rewrite [value, if_pos zero, programs.valueZero_eq, program_model]
    exact (programs.cells index).integralSample_zero (fun {_ _} models => models.valueZero)
  · rewrite [value, if_neg zero, programs.valueOne_eq, program_model]
    exact (programs.cells index).integralSample_zero (fun {_ _} models => models.valueOne)

/-- Every original first-derivative sample is zero by the same source-owned telescope. -/
theorem first_integralSample_zero (programs : Programs sources) (coordinate : Fin 2) (index : Nat) :
    ((programs.first coordinate).model index).integralSample = 0 := by
  by_cases zero : coordinate = 0
  · rewrite [first, if_pos zero, programs.firstZero_eq, program_model]
    exact (programs.cells index).integralSample_zero (fun {_ _} models => models.firstZero)
  · rewrite [first, if_neg zero, programs.firstOne_eq, program_model]
    exact (programs.cells index).integralSample_zero (fun {_ _} models => models.firstOne)

/-- Every original second-derivative sample is zero by the original finite antiderivative telescope. -/
theorem second_integralSample_zero (programs : Programs sources) (coordinate : Fin 2) (index : Nat) :
    ((programs.second coordinate).model index).integralSample = 0 := by
  by_cases zero : coordinate = 0
  · rewrite [second, if_pos zero, programs.secondZero_eq, program_model]
    exact (programs.cells index).integralSample_zero (fun {_ _} models => models.secondZero)
  · rewrite [second, if_neg zero, programs.secondOne_eq, program_model]
    exact (programs.cells index).integralSample_zero (fun {_ _} models => models.secondOne)

end Programs

end Purelib.Examples.Curves.Legendre.RegularCycle

end
