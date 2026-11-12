module
public import Purelib.Integration.Cell.Source.Continuous
public import Purelib.Approximation.Rational.Exceptional.Modulus
public import Purelib.Integration.Partition.Exceptional
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.List.Map
import Purelib.Data.List.Rat.Linear
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite exceptional-source integration

A finite point list and a global rational magnitude bound determine a mesh
budget alongside the regular variation modulus. Cells touching an exception
use the global range; the other cells use their cached source readings and
the original regular variation law.
-/

public section

namespace Purelib.Integration.SourceFrontier.Exceptional

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Integration.Partition
open Purelib.Data.List.Rat.Linear

set_option genInjectivity false in
/-- A positive request with its computed regular and exceptional mesh budgets.

The original source modulus remains the indexed owner. The finite exception
count, magnitude-dependent scale, local variation and actual uniform
partition retain the exact computations used by the constructor. -/
structure Preparation {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Exceptional.Modulus source) where
  /-- The original positive rational accuracy request. -/ request : AccuracyRequest
  /-- The regular-piece local variation budget. -/ variation : Fraction.Rational
  /-- The regular variation is one quarter of the original request. -/ variation_eq :
    variation = request.tolerance / 4
  /-- The rational readback of the original finite exception count. -/ count : Fraction.Rational
  /-- The count is the actual length of the retained exception list. -/ count_eq : count = modulus.points.length
  /-- The positive magnitude-and-count scale. -/ scale : Fraction.Rational
  /-- The scale is computed from the original magnitude and retained count. -/ scale_eq :
    scale = (modulus.magnitude + 1) * (count + 1)
  /-- The allocated exceptional-neighborhood mesh limit. -/ exceptionRadius : Fraction.Rational
  /-- The limit uses the retained quarter budget and scale. -/ exceptionRadius_eq :
    exceptionRadius = variation / (4 * scale)
  /-- The chosen mesh is the minimum of the regular and exceptional limits. -/ mesh : Fraction.Rational
  /-- The mesh retains both original computed limits. -/ mesh_eq :
    mesh = min (modulus.radius variation) exceptionRadius
  /-- The actual normalized uniform partition selected for the mesh. -/ partition : Unit.Normalized
  /-- The retained partition is the original computed grid for that mesh. -/ partition_eq :
    partition = Uniform.Grid.forWidth mesh

constructive_injectivity Preparation

namespace Preparation

/-- Compute the finite exception budget, regular mesh and actual normalized partition. -/
@[expose] def prepare {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Exceptional.Modulus source) (request : AccuracyRequest) : Preparation modulus :=
  let variation := request.tolerance / 4
  let count : Fraction.Rational := modulus.points.length
  let scale := (modulus.magnitude + 1) * (count + 1)
  let exceptionRadius := variation / (4 * scale)
  let mesh := min (modulus.radius variation) exceptionRadius
  let partition := Uniform.Grid.forWidth mesh
  { request := request
    variation := variation
    variation_eq := rfl
    count := count
    count_eq := rfl
    scale := scale
    scale_eq := rfl
    exceptionRadius := exceptionRadius
    exceptionRadius_eq := rfl
    mesh := mesh
    mesh_eq := rfl
    partition := partition
    partition_eq := rfl }

/-- The retained regular variation budget is positive. -/
theorem variationPositive {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Exceptional.Modulus source} (prepared : Preparation modulus) : 0 < prepared.variation := by
  rw [prepared.variation_eq]
  exact Bounds.Quarter.quarter_pos prepared.request.positive

/-- The retained finite exception count is nonnegative. -/
theorem countNonnegative {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Exceptional.Modulus source} (prepared : Preparation modulus) : 0 ≤ prepared.count := by
  rw [prepared.count_eq]
  exact Fraction.Cast.Order.natCast_le_direct (Nat.zero_le modulus.points.length)

/-- Adding one to a nonnegative rational yields a positive rational. -/
private theorem add_one_positive {value : Fraction.Rational} (nonnegative : 0 ≤ value) : 0 < value + 1 := by
  have shifted := Arithmetic.add_le_add_right_direct nonnegative 1
  rw [Fraction.Field.zero_add] at shifted
  exact (by decide : (0 : Fraction.Rational) < 1).trans_le shifted

/-- The retained magnitude-and-count scale is strictly positive, including zero and empty cases. -/
theorem scalePositive {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Exceptional.Modulus source} (prepared : Preparation modulus) : 0 < prepared.scale := by
  rw [prepared.scale_eq]
  exact Arithmetic.mul_pos_direct (add_one_positive modulus.magnitude_nonnegative)
    (add_one_positive prepared.countNonnegative)

/-- The exceptional mesh limit is strictly positive. -/
theorem exceptionRadiusPositive {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Exceptional.Modulus source} (prepared : Preparation modulus) :
    0 < prepared.exceptionRadius := by
  rw [prepared.exceptionRadius_eq]
  exact Fraction.Order.Field.div_pos_direct prepared.variationPositive
    (Arithmetic.mul_pos_direct (by decide) prepared.scalePositive)

/-- The minimum of the computed regular and exceptional radii is strictly positive. -/
theorem meshPositive {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Exceptional.Modulus source} (prepared : Preparation modulus) : 0 < prepared.mesh := by
  rw [prepared.mesh_eq]
  exact Fraction.Order.Basic.lt_min (modulus.radius_pos prepared.variation prepared.variationPositive)
    prepared.exceptionRadiusPositive

/-- Every actual retained grid cell is strictly shorter than the computed mesh. -/
theorem intervalSmall {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Exceptional.Modulus source} (prepared : Preparation modulus)
    (interval : Partition.Interval) (member : interval ∈ prepared.partition.intervals) :
    interval.signedLength < prepared.mesh := by
  have intervals := congrArg Unit.Normalized.intervals prepared.partition_eq
  have actual : interval ∈ (Uniform.Grid.forWidth prepared.mesh).intervals := intervals ▸ member
  exact Uniform.Grid.forWidth_interval_lt prepared.meshPositive interval actual

/-- The computed mesh is at most the retained regular-variation radius. -/
theorem mesh_le_regular {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Exceptional.Modulus source} (prepared : Preparation modulus) :
    prepared.mesh ≤ modulus.radius prepared.variation := by
  rw [prepared.mesh_eq]
  exact Fraction.Order.Basic.min_le_left _ _

/-- The computed mesh is at most the retained exceptional-neighborhood radius. -/
theorem mesh_le_exception {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Exceptional.Modulus source} (prepared : Preparation modulus) :
    prepared.mesh ≤ prepared.exceptionRadius := by
  rw [prepared.mesh_eq]
  exact Fraction.Order.Basic.min_le_right _ _

/-- The computed mesh is no larger than the retained local variation budget.

The positive scale contains one more than both the nonnegative magnitude and
the finite point count. Its exceptional denominator is therefore at least one. -/
theorem mesh_le_variation {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Exceptional.Modulus source} (prepared : Preparation modulus) :
    prepared.mesh ≤ prepared.variation := by
  have magnitudeBound : 1 ≤ modulus.magnitude + 1 := by
    have shifted := Arithmetic.add_le_add_right_direct modulus.magnitude_nonnegative 1
    rw [Fraction.Field.zero_add] at shifted
    exact shifted
  have countBound : 1 ≤ prepared.count + 1 := by
    have shifted := Arithmetic.add_le_add_right_direct prepared.countNonnegative 1
    rw [Fraction.Field.zero_add] at shifted
    exact shifted
  have scaleBound : 1 ≤ prepared.scale := by
    rw [prepared.scale_eq]
    have product := Arithmetic.mul_le_mul_direct magnitudeBound countBound
      (by decide : (0 : Fraction.Rational) ≤ 1) (add_one_positive modulus.magnitude_nonnegative).le
    rw [Fraction.Field.one_mul] at product
    exact product
  have denominatorBound : 1 ≤ (4 : Fraction.Rational) * prepared.scale := by
    have product := Arithmetic.mul_le_mul_direct
      (by decide : (1 : Fraction.Rational) ≤ 4) scaleBound
      (by decide : (0 : Fraction.Rational) ≤ 1) (by decide : (0 : Fraction.Rational) ≤ 4)
    rw [Fraction.Field.one_mul] at product
    exact product
  have bounded := Fraction.Order.Field.divide_le_self prepared.variationPositive.le denominatorBound
  rw [← prepared.exceptionRadius_eq] at bounded
  exact prepared.mesh_le_exception.trans bounded

/-- The actual marked-cell contribution is paid by the retained exceptional budget.

The complete finite union is bounded by its original point count and mesh.
The positive scale dominates both magnitude and count, including zero values. -/
theorem markedBudget {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Exceptional.Modulus source} (prepared : Preparation modulus) :
    (modulus.magnitude + modulus.magnitude) * prepared.partition.markedLength modulus.points ≤ prepared.variation := by
  have marked := prepared.partition.markedLength_le modulus.points prepared.mesh prepared.meshPositive
    prepared.intervalSmall
  rw [← prepared.count_eq] at marked
  have magnitudeLe : modulus.magnitude ≤ modulus.magnitude + 1 := by
    have shifted := Arithmetic.add_le_add_right_direct (by decide : (0 : Fraction.Rational) ≤ 1)
      modulus.magnitude
    calc
      modulus.magnitude = 0 + modulus.magnitude := by ring1
      _ ≤ 1 + modulus.magnitude := shifted
      _ = modulus.magnitude + 1 := by ring1
  have countLe : prepared.count ≤ prepared.count + 1 := by
    have shifted := Arithmetic.add_le_add_right_direct (by decide : (0 : Fraction.Rational) ≤ 1)
      prepared.count
    calc
      prepared.count = 0 + prepared.count := by ring1
      _ ≤ 1 + prepared.count := shifted
      _ = prepared.count + 1 := by ring1
  have productLe : modulus.magnitude * prepared.count ≤ prepared.scale := by
    rw [prepared.scale_eq]
    exact Arithmetic.mul_le_mul_direct magnitudeLe countLe prepared.countNonnegative
      (add_one_positive modulus.magnitude_nonnegative).le
  have magnitudeTwiceNonnegative : 0 ≤ modulus.magnitude + modulus.magnitude := by
    have sum := Arithmetic.add_le_add_direct modulus.magnitude_nonnegative modulus.magnitude_nonnegative
    change (0 : Fraction.Rational) ≤ modulus.magnitude + modulus.magnitude at sum
    exact sum
  have fourMeshNonnegative : 0 ≤ (4 : Fraction.Rational) * prepared.mesh :=
    Arithmetic.mul_nonneg_direct (by decide) prepared.meshPositive.le
  have scaledMarked := Arithmetic.mul_le_mul_of_nonneg_left_direct marked magnitudeTwiceNonnegative
  have scaledProduct := Arithmetic.mul_le_mul_of_nonneg_right_direct productLe fourMeshNonnegative
  have meshLimit : prepared.mesh ≤ prepared.variation / (4 * prepared.scale) := by
    have bound := prepared.mesh_le_exception
    rw [prepared.exceptionRadius_eq] at bound
    exact bound
  have denominatorPositive := Arithmetic.mul_pos_direct
    (by decide : (0 : Fraction.Rational) < 4) prepared.scalePositive
  have paid := (Fraction.Order.Field.le_div_iff_pos denominatorPositive).mp meshLimit
  calc
    _ ≤ (modulus.magnitude + modulus.magnitude) * (prepared.count * (prepared.mesh + prepared.mesh)) := scaledMarked
    _ = (modulus.magnitude * prepared.count) * (4 * prepared.mesh) := by ring1
    _ ≤ prepared.scale * (4 * prepared.mesh) := scaledProduct
    _ = prepared.mesh * (4 * prepared.scale) := by ring1
    _ ≤ prepared.variation := paid

end Preparation

/-- Derive a value range from the retained tag and its actual exceptional classification. -/
@[expose] def readingRange {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Exceptional.Modulus source) (variation : Fraction.Rational) (nonnegative : 0 ≤ variation)
    (tag : SourcePoint source) : Purelib.Data.Rat.Interval :=
  if tag.interval.marked modulus.points then
    ⟨-modulus.magnitude, modulus.magnitude,
      Arithmetic.neg_le_self_of_nonnegative modulus.magnitude_nonnegative⟩
  else Continuous.readingRange variation nonnegative tag

/-- The reading-derived range has the actual regular or exceptional width. -/
theorem readingRange_width {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Exceptional.Modulus source) (variation : Fraction.Rational) (nonnegative : 0 ≤ variation)
    (tag : SourcePoint source) :
    (readingRange modulus variation nonnegative tag).width =
      if tag.interval.marked modulus.points then modulus.magnitude + modulus.magnitude else variation + variation := by
  unfold readingRange
  split
  · change modulus.magnitude - -modulus.magnitude = modulus.magnitude + modulus.magnitude
    ring1
  · exact Continuous.readingRange_width variation nonnegative tag

namespace Preparation

/-- The actual marked or regular range encloses every rational source reading in its retained cell. -/
theorem rangeValid {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Exceptional.Modulus source} (prepared : Preparation modulus)
    (interval : Partition.Interval) (member : interval ∈ prepared.partition.intervals)
    (point : Fraction.Rational) (lower : interval.start ≤ point) (upper : point ≤ interval.finish) :
    (readingRange modulus prepared.variation prepared.variationPositive.le
      (SourcePoint.atStart source interval (prepared.partition.valid interval member))).Contains (source point) := by
  have valid := prepared.partition.valid interval member
  have pointLower := valid.1.trans lower
  have pointUpper := upper.trans valid.2.2
  cases marked : interval.marked modulus.points with
  | true =>
      change (if interval.marked modulus.points then
        (⟨-modulus.magnitude, modulus.magnitude,
          Arithmetic.neg_le_self_of_nonnegative modulus.magnitude_nonnegative⟩ :
          Purelib.Data.Rat.Interval)
        else Continuous.readingRange prepared.variation prepared.variationPositive.le
          (SourcePoint.atStart source interval (prepared.partition.valid interval member))).Contains (source point)
      rw [marked]
      exact modulus.bounded point pointLower pointUpper
  | false =>
      have noExceptions : ∀ exceptional ∈ modulus.points,
          ¬ (interval.start ≤ exceptional ∧ exceptional ≤ point) := by
        intro exceptional present inside
        have hit := (interval.marked_iff modulus.points).mpr ⟨exceptional, present, inside.1, inside.2.trans upper⟩
        rw [marked] at hit
        cases hit
      have difference : point - interval.start ≤ interval.signedLength :=
        Arithmetic.sub_le_sub_direct upper le_rfl
      have small : point - interval.start < modulus.radius prepared.variation :=
        difference.trans_lt ((prepared.intervalSmall interval member).trans_le prepared.mesh_le_regular)
      have bounded := modulus.variation prepared.variation prepared.variationPositive interval.start point
        valid.1 lower pointUpper noExceptions small
      change (if interval.marked modulus.points then
        (⟨-modulus.magnitude, modulus.magnitude,
          Arithmetic.neg_le_self_of_nonnegative modulus.magnitude_nonnegative⟩ :
          Purelib.Data.Rat.Interval)
        else Continuous.readingRange prepared.variation prepared.variationPositive.le
          (SourcePoint.atStart source interval (prepared.partition.valid interval member))).Contains (source point)
      rw [marked]
      exact bounded

/-- Read the retained grid starts and construct their marked or regular source ranges. -/
@[expose] def frontier {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Exceptional.Modulus source} (prepared : Preparation modulus) : SourceFrontier source :=
  SourceFrontier.ofRanges source prepared.partition
    (readingRange modulus prepared.variation prepared.variationPositive.le) prepared.rangeValid

/-- Build this exceptional preparation using matching retained exact source readings. -/
@[expose] def frontierCached {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Exceptional.Modulus source} (prepared : Preparation modulus)
    (cached : List (SourcePoint source)) : SourceFrontier source :=
  SourceFrontier.ofRangesCached source cached prepared.partition
    (readingRange modulus prepared.variation prepared.variationPositive.le) prepared.rangeValid

/-- Reusing exact readings preserves the original exceptional frontier. -/
theorem frontierCached_eq {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Exceptional.Modulus source} (prepared : Preparation modulus)
    (cached : List (SourcePoint source)) : prepared.frontierCached cached = prepared.frontier :=
  SourceFrontier.ofRangesCached_eq source cached prepared.partition
    (readingRange modulus prepared.variation prepared.variationPositive.le) prepared.rangeValid

/-- The finite cell-weight sum agrees with its original integration-weight recursion. -/
private theorem weight_sum {α : Type} : ∀ cells : List (IntegrationCell α),
    integrationWeight cells = (cells.map (fun cell => cell.weight)).sum
  | [] => rfl
  | cell :: remaining => by
      change cell.weight + integrationWeight remaining = cell.weight + (remaining.map (fun other => other.weight)).sum
      rw [weight_sum remaining]

/-- Marked source-cell weights read back to the original partition's marked length. -/
private theorem marked_weight_eq {source : Fraction.Rational → Fraction.Rational}
    (frontier : SourceFrontier source) (points : List Fraction.Rational) :
    (frontier.cells.map (fun cell => if cell.item.interval.marked points then cell.weight else 0)).sum =
      frontier.partition.markedLength points := by
  have weights : ∀ cell ∈ frontier.cells,
      (if cell.item.interval.marked points then cell.weight else 0) =
        if cell.item.interval.marked points then cell.item.interval.signedLength else 0 := by
    intro cell member
    rw [frontier.weight_eq cell member]
  calc
    _ = (frontier.cells.map (fun cell =>
        if cell.item.interval.marked points then cell.item.interval.signedLength else 0)).sum :=
      sum_congr _ _ frontier.cells weights
    _ = ((frontier.cells.map (fun cell => cell.item.interval)).map
        (fun interval => if interval.marked points then interval.signedLength else 0)).sum := by
      rw [Purelib.Data.List.Map.map_map]
      rfl
    _ = frontier.partition.markedLength points := by rw [frontier.domains_eq]; rfl

/-- The actual source-cell oscillations are bounded by regular and marked-cell contributions. -/
theorem oscillation_le {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Exceptional.Modulus source} (prepared : Preparation modulus) :
    integralOscillation prepared.frontier.cells ≤
      integrationWeight prepared.frontier.cells * (prepared.variation + prepared.variation) +
        (modulus.magnitude + modulus.magnitude) * prepared.partition.markedLength modulus.points := by
  let regular := prepared.variation + prepared.variation
  let exceptional := modulus.magnitude + modulus.magnitude
  let markedWeight := fun cell : IntegrationCell (SourcePoint source) =>
    if cell.item.interval.marked modulus.points then cell.weight else 0
  let extra := fun cell : IntegrationCell (SourcePoint source) =>
    if cell.item.interval.marked modulus.points then exceptional else 0
  have regularNonnegative : 0 ≤ regular := by
    have sum := Arithmetic.add_le_add_direct prepared.variationPositive.le prepared.variationPositive.le
    change (0 : Fraction.Rational) ≤ regular at sum
    exact sum
  have cellBound : ∀ cell ∈ prepared.frontier.cells, cell.oscillation ≤ regular + extra cell := by
    intro cell member
    have width := SourceFrontier.ofRanges_oscillation source prepared.partition
      (readingRange modulus prepared.variation prepared.variationPositive.le) prepared.rangeValid cell member
    rw [readingRange_width] at width
    cases marked : cell.item.interval.marked modulus.points with
    | false =>
        rw [marked] at width
        dsimp only [extra]
        rw [marked]
        change cell.oscillation ≤ regular + 0
        rw [width]
        have identity : regular + 0 = regular := by ring1
        rewrite [identity]
        exact Fraction.Order.Basic.le_refl _
    | true =>
        rw [marked] at width
        dsimp only [extra]
        rw [marked]
        change cell.oscillation ≤ regular + exceptional
        have shifted := Arithmetic.add_le_add_right_direct regularNonnegative exceptional
        rw [Fraction.Field.zero_add] at shifted
        rw [width]
        exact shifted
  have weighted := sum_le (fun cell => cell.weight * cell.oscillation)
    (fun cell => cell.weight * (regular + extra cell)) prepared.frontier.cells (fun cell member =>
      Arithmetic.mul_le_mul_of_nonneg_left_direct (cellBound cell member) cell.weight_nonnegative)
  have distributive : ∀ cell ∈ prepared.frontier.cells,
      cell.weight * (regular + extra cell) = cell.weight * regular + markedWeight cell * exceptional := by
    intro cell _
    dsimp only [extra, markedWeight]
    cases cell.item.interval.marked modulus.points with
    | false =>
        change cell.weight * (regular + 0) = cell.weight * regular + 0 * exceptional
        ring1
    | true =>
        change cell.weight * (regular + exceptional) = cell.weight * regular + cell.weight * exceptional
        ring1
  have distribute := sum_congr (fun cell => cell.weight * (regular + extra cell))
    (fun cell => cell.weight * regular + markedWeight cell * exceptional) prepared.frontier.cells distributive
  have split := sum_add (fun cell => cell.weight * regular) (fun cell => markedWeight cell * exceptional)
    prepared.frontier.cells
  have first := sum_mul_right (fun cell => cell.weight) regular prepared.frontier.cells
  have second := sum_mul_right markedWeight exceptional prepared.frontier.cells
  rw [distribute, split, first, second, ← weight_sum, marked_weight_eq] at weighted
  rw [integralOscillation_eq_sum]
  calc
    _ ≤ integrationWeight prepared.frontier.cells * regular +
        prepared.partition.markedLength modulus.points * exceptional := weighted
    _ = integrationWeight prepared.frontier.cells * regular +
        exceptional * prepared.partition.markedLength modulus.points := by ring1

/-- The computed marked and regular source ranges meet the original positive width request. -/
theorem frontier_width_lt {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Exceptional.Modulus source} (prepared : Preparation modulus) :
    (integralBound prepared.frontier.cells).width < prepared.request.tolerance := by
  have weighted := prepared.oscillation_le
  rw [prepared.frontier.totalWeight, Fraction.Field.one_mul] at weighted
  have paid := Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl (prepared.variation + prepared.variation)) prepared.markedBudget
  have bound := Fraction.Order.Basic.le_trans _ _ _ weighted paid
  rw [prepared.variation_eq, Bounds.Quarter.two_quarters] at bound
  rw [integralBound_width]
  exact bound.trans_lt (Bounds.Quarter.half_add_quarter_lt prepared.request.positive)

end Preparation

set_option genInjectivity false in
/-- A completed finite exceptional-source request with its actual source frontier and paid width.

The original exception list, global magnitude, regular modulus, mesh and
partition remain in the indexed preparation and its cached frontier. -/
structure Result {source : Fraction.Rational → Fraction.Rational} (modulus : Rational.Exceptional.Modulus source) where
  /-- The original request and computed regular and exceptional budgets. -/ preparation : Preparation modulus
  /-- The actual cached source-linked frontier. -/ frontier : SourceFrontier source
  /-- The frontier is the exact output of the retained preparation. -/ frontier_eq : frontier = preparation.frontier
  /-- The retained source frontier meets the original positive request. -/ accurate :
    (integralBound frontier.cells).width < preparation.request.tolerance

constructive_injectivity Result

namespace Result

/-- Select the midpoint of the original exceptional-source integral enclosure. -/
@[expose] def answer {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Exceptional.Modulus source} (result : Result modulus) : Fraction.Rational :=
  (integralBound result.frontier.cells).midpoint

/-- The selected answer belongs to the original source-linked integral enclosure. -/
theorem answer_contains {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Exceptional.Modulus source} (result : Result modulus) :
    (integralBound result.frontier.cells).Contains result.answer :=
  (integralBound result.frontier.cells).midpoint_contains

/-- Every admitted rational differs from the selected answer by at most half the actual enclosure width. -/
theorem answer_error {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Exceptional.Modulus source} (result : Result modulus) (value : Fraction.Rational)
    (inside : (integralBound result.frontier.cells).Contains value) :
    Fraction.abs (value - result.answer) ≤ (integralBound result.frontier.cells).width * (1 / 2) :=
  Purelib.Data.Rat.Interval.abs_sub_midpoint_le inside

end Result

/-- Compute a complete finite exceptional-source frontier for one positive integration request. -/
@[expose] def build {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Exceptional.Modulus source) (request : AccuracyRequest) : Result modulus :=
  let preparation := Preparation.prepare modulus request
  let frontier := preparation.frontier
  { preparation := preparation
    frontier := frontier
    frontier_eq := rfl
    accurate := preparation.frontier_width_lt }

/-- Compute the original exceptional result using matching previously retained source readings. -/
@[expose] def buildCached {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Exceptional.Modulus source) (cached : List (SourcePoint source))
    (request : AccuracyRequest) : Result modulus := by
  let preparation := Preparation.prepare modulus request
  let frontier := preparation.frontierCached cached
  have same : frontier = preparation.frontier := preparation.frontierCached_eq cached
  exact
    { preparation := preparation
      frontier := frontier
      frontier_eq := same
      accurate := same.symm ▸ preparation.frontier_width_lt }

/-- Cache-selected construction preserves the complete original exceptional result. -/
theorem buildCached_eq {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Exceptional.Modulus source) (cached : List (SourcePoint source))
    (request : AccuracyRequest) : buildCached modulus cached request = build modulus request := by
  unfold buildCached build
  simp only [-eq_self, -iff_self, Preparation.frontierCached_eq]
  rfl

end Purelib.Integration.SourceFrontier.Exceptional

end
