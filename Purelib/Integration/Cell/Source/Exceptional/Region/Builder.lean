module
public import Purelib.Approximation.Rational.Exceptional.Region
public import Purelib.Integration.Cell.Source.Continuous
public import Purelib.Integration.Cell.Source.Producer
import Purelib.Data.List.Rat.Linear
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Partition.Uniform.Grid
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Integrating outside effectively small rational regions

An accuracy request selects the actual finite exceptional regions, a regular
variation radius and a normalized rational grid. Marked cells use the global
range; other cells use the original rational tag and local variation law.
-/

public section

namespace Purelib.Integration.SourceFrontier.Exceptional.Region.Builder

open Purelib.Approximation
open Purelib.Approximation.Rational.Exceptional.Region (Modulus)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.List.Rat.Linear
open Purelib.Integration.Partition

set_option genInjectivity false in
/-- A request with its computed region budget, original regions and actual grid.

The original source modulus remains the owner. Every cached region, count,
scale and mesh is linked to the exact request and the same prior computations. -/
structure Preparation {source : Fraction.Rational → Fraction.Rational}
    (modulus : Modulus source) where
  /-- The original positive accuracy request. -/ request : AccuracyRequest
  /-- The positive regular variation budget. -/ variation : Fraction.Rational
  /-- The variation is one eighth of the request. -/ variation_eq : variation = request.tolerance / 8
  /-- The requested total length of the original exceptional regions. -/ regionBudget : Fraction.Rational
  /-- The region budget is scaled by the original magnitude. -/ regionBudget_eq :
    regionBudget = variation / (4 * (modulus.magnitude + 1))
  /-- The actual finite regions selected by the original source modulus. -/ regions : List Partition.Interval
  /-- The regions are exactly those selected by the retained region budget. -/ regions_eq :
    regions = modulus.regions regionBudget
  /-- The rational reading of the actual finite region count. -/ count : Fraction.Rational
  /-- The count retains every region occurrence. -/ count_eq : count = regions.length
  /-- The positive magnitude-and-count scale. -/ scale : Fraction.Rational
  /-- The scale retains the original magnitude and count. -/ scale_eq :
    scale = (modulus.magnitude + 1) * (count + 1)
  /-- The exceptional mesh limit computed from that scale. -/ regionMesh : Fraction.Rational
  /-- The mesh limit is the variation divided by four times the scale. -/ regionMesh_eq :
    regionMesh = variation / (4 * scale)
  /-- The selected mesh is the minimum of the regular and exceptional limits. -/ mesh : Fraction.Rational
  /-- The mesh preserves both original computed radii. -/ mesh_eq :
    mesh = min (modulus.radius regionBudget variation) regionMesh
  /-- The actual normalized rational grid selected by the mesh. -/ partition : Unit.Normalized
  /-- The partition is exactly the original grid for the retained mesh. -/ partition_eq :
    partition = Uniform.Grid.forWidth mesh

constructive_injectivity Preparation

namespace Preparation

/-- Compute the original finite regions and normalized grid from one positive request. -/
@[expose] def prepare {source : Fraction.Rational → Fraction.Rational}
    (modulus : Modulus source) (request : AccuracyRequest) : Preparation modulus :=
  let variation := request.tolerance / 8
  let regionBudget := variation / (4 * (modulus.magnitude + 1))
  let regions := modulus.regions regionBudget
  let count : Fraction.Rational := regions.length
  let scale := (modulus.magnitude + 1) * (count + 1)
  let regionMesh := variation / (4 * scale)
  let mesh := min (modulus.radius regionBudget variation) regionMesh
  let partition := Uniform.Grid.forWidth mesh
  { request := request
    variation := variation
    variation_eq := rfl
    regionBudget := regionBudget
    regionBudget_eq := rfl
    regions := regions
    regions_eq := rfl
    count := count
    count_eq := rfl
    scale := scale
    scale_eq := rfl
    regionMesh := regionMesh
    regionMesh_eq := rfl
    mesh := mesh
    mesh_eq := rfl
    partition := partition
    partition_eq := rfl }

/-- The retained variation budget is positive. -/
theorem variationPositive {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus) :
    0 < prepared.variation := by
  rw [prepared.variation_eq]
  exact Fraction.Order.Field.div_pos_direct prepared.request.positive (by decide)

/-- Adding one to a nonnegative rational yields a positive rational. -/
private theorem add_one_positive {value : Fraction.Rational} (nonnegative : 0 ≤ value) : 0 < value + 1 := by
  have shifted := Arithmetic.add_le_add_right_direct nonnegative 1
  rw [Fraction.Field.zero_add] at shifted
  exact (by decide : (0 : Fraction.Rational) < 1).trans_le shifted

/-- The finite region-count reading is nonnegative. -/
theorem countNonnegative {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus) :
    0 ≤ prepared.count := by
  rw [prepared.count_eq]
  exact Fraction.Cast.Order.natCast_le_direct (Nat.zero_le prepared.regions.length)

/-- The retained magnitude-and-count scale is positive even for zero magnitude or no regions. -/
theorem scalePositive {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus) : 0 < prepared.scale := by
  rw [prepared.scale_eq]
  exact Arithmetic.mul_pos_direct (add_one_positive modulus.magnitude_nonnegative)
    (add_one_positive prepared.countNonnegative)

/-- The computed total region-length budget is positive. -/
theorem regionBudgetPositive {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus) :
    0 < prepared.regionBudget := by
  rw [prepared.regionBudget_eq]
  exact Fraction.Order.Field.div_pos_direct prepared.variationPositive
    (Arithmetic.mul_pos_direct (by decide) (add_one_positive modulus.magnitude_nonnegative))

/-- The computed exceptional mesh limit is positive. -/
theorem regionMeshPositive {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus) :
    0 < prepared.regionMesh := by
  rw [prepared.regionMesh_eq]
  exact Fraction.Order.Field.div_pos_direct prepared.variationPositive
    (Arithmetic.mul_pos_direct (by decide) prepared.scalePositive)

/-- The retained minimum mesh is positive. -/
theorem meshPositive {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus) : 0 < prepared.mesh := by
  rw [prepared.mesh_eq]
  exact Fraction.Order.Basic.lt_min
    (modulus.radius_pos prepared.regionBudget prepared.regionBudgetPositive
      prepared.variation prepared.variationPositive)
    prepared.regionMeshPositive

/-- Each original grid cell is strictly shorter than the retained mesh. -/
theorem intervalSmall {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus)
    (interval : Partition.Interval) (member : interval ∈ prepared.partition.intervals) :
    interval.signedLength < prepared.mesh := by
  have intervals := congrArg Unit.Normalized.intervals prepared.partition_eq
  have actual : interval ∈ (Uniform.Grid.forWidth prepared.mesh).intervals := intervals ▸ member
  exact Uniform.Grid.forWidth_interval_lt prepared.meshPositive interval actual

/-- The mesh does not exceed the original local variation radius. -/
theorem mesh_le_regular {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus) :
    prepared.mesh ≤ modulus.radius prepared.regionBudget prepared.variation := by
  rw [prepared.mesh_eq]
  exact Fraction.Order.Basic.min_le_left _ _

/-- The mesh does not exceed the computed exceptional-cell radius. -/
theorem mesh_le_region {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus) :
    prepared.mesh ≤ prepared.regionMesh := by
  rw [prepared.mesh_eq]
  exact Fraction.Order.Basic.min_le_right _ _

/-- Every original retained region is ordered and lies in the unit interval. -/
theorem regionBounds {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus)
    (region : Partition.Interval) (member : region ∈ prepared.regions) :
    0 ≤ region.start ∧ region.start ≤ region.finish ∧ region.finish ≤ 1 := by
  rw [prepared.regions_eq] at member
  exact modulus.region_bounds prepared.regionBudget prepared.regionBudgetPositive region member

/-- The selected original region lengths meet the computed length budget. -/
theorem regionLengths_le {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus) :
    (prepared.regions.map Partition.Interval.signedLength).sum ≤ prepared.regionBudget := by
  rw [prepared.regions_eq]
  exact modulus.regions_length_le prepared.regionBudget prepared.regionBudgetPositive

/-- The selected regions and their mesh expansions consume at most twice the retained variation.

The original region-length budget and the finite region count are paid
separately. The actual marked-cell union charges overlaps only once. -/
theorem markedBudget {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus) :
    (modulus.magnitude + modulus.magnitude) * prepared.partition.regionsLength prepared.regions ≤
      prepared.variation + prepared.variation := by
  have marked := prepared.partition.regionsLength_le_total prepared.regions prepared.mesh prepared.regionBounds
    prepared.meshPositive prepared.intervalSmall
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
    have bound := prepared.mesh_le_region
    rw [prepared.regionMesh_eq] at bound
    exact bound
  have denominatorPositive := Arithmetic.mul_pos_direct
    (by decide : (0 : Fraction.Rational) < 4) prepared.scalePositive
  have meshPaid := (Fraction.Order.Field.le_div_iff_pos denominatorPositive).mp meshLimit
  have meshCharge : (modulus.magnitude + modulus.magnitude) *
      (prepared.count * (prepared.mesh + prepared.mesh)) ≤ prepared.variation := by
    calc
      _ = (modulus.magnitude * prepared.count) * (4 * prepared.mesh) := by ring1
      _ ≤ prepared.scale * (4 * prepared.mesh) := scaledProduct
      _ = prepared.mesh * (4 * prepared.scale) := by ring1
      _ ≤ prepared.variation := meshPaid
  have doubleLe : modulus.magnitude + modulus.magnitude ≤ 4 * (modulus.magnitude + 1) := by
    have doubled := Arithmetic.add_le_add_direct magnitudeLe magnitudeLe
    have larger := Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide : (2 : Fraction.Rational) ≤ 4) (add_one_positive modulus.magnitude_nonnegative).le
    have identity : (modulus.magnitude + 1) + (modulus.magnitude + 1) =
        2 * (modulus.magnitude + 1) := by ring1
    rw [identity] at doubled
    exact doubled.trans larger
  have lengthScaled := Arithmetic.mul_le_mul_of_nonneg_left_direct prepared.regionLengths_le
    magnitudeTwiceNonnegative
  have denominatorLe := Arithmetic.mul_le_mul_of_nonneg_right_direct doubleLe
    prepared.regionBudgetPositive.le
  have regionDenominatorPositive := Arithmetic.mul_pos_direct
    (by decide : (0 : Fraction.Rational) < 4) (add_one_positive modulus.magnitude_nonnegative)
  have regionLimit : prepared.regionBudget ≤ prepared.variation / (4 * (modulus.magnitude + 1)) := by
    rewrite [prepared.regionBudget_eq]
    exact Fraction.Order.Basic.le_refl _
  have regionPaid := (Fraction.Order.Field.le_div_iff_pos regionDenominatorPositive).mp regionLimit
  have regionCharge : (modulus.magnitude + modulus.magnitude) *
      (prepared.regions.map Partition.Interval.signedLength).sum ≤ prepared.variation := by
    calc
      _ ≤ (modulus.magnitude + modulus.magnitude) * prepared.regionBudget := lengthScaled
      _ ≤ (4 * (modulus.magnitude + 1)) * prepared.regionBudget := denominatorLe
      _ = prepared.regionBudget * (4 * (modulus.magnitude + 1)) := by ring1
      _ ≤ prepared.variation := regionPaid
  calc
    _ ≤ (modulus.magnitude + modulus.magnitude) *
        ((prepared.regions.map Partition.Interval.signedLength).sum +
          prepared.count * (prepared.mesh + prepared.mesh)) := scaledMarked
    _ = (modulus.magnitude + modulus.magnitude) *
        (prepared.regions.map Partition.Interval.signedLength).sum +
          (modulus.magnitude + modulus.magnitude) * (prepared.count * (prepared.mesh + prepared.mesh)) := by ring1
    _ ≤ prepared.variation + prepared.variation := Arithmetic.add_le_add_direct regionCharge meshCharge

end Preparation

/-- The original tag determines either the global exceptional range or the regular variation range. -/
@[expose] def readingRange {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus)
    (tag : SourcePoint source) : Purelib.Data.Rat.Interval :=
  if tag.interval.regionMarked prepared.regions then
    ⟨-modulus.magnitude, modulus.magnitude,
      Arithmetic.neg_le_self_of_nonnegative modulus.magnitude_nonnegative⟩
  else Continuous.readingRange prepared.variation prepared.variationPositive.le tag

/-- The selected range has the exact global or regular width for its original cell. -/
theorem readingRange_width {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus)
    (tag : SourcePoint source) :
    (readingRange prepared tag).width =
      if tag.interval.regionMarked prepared.regions then modulus.magnitude + modulus.magnitude
      else prepared.variation + prepared.variation := by
  unfold readingRange
  split
  · change modulus.magnitude - -modulus.magnitude = modulus.magnitude + modulus.magnitude
    ring1
  · exact Continuous.readingRange_width prepared.variation prepared.variationPositive.le tag

namespace Preparation

/-- The selected range encloses every rational source reading in its original grid cell. -/
theorem rangeValid {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus)
    (interval : Partition.Interval) (member : interval ∈ prepared.partition.intervals)
    (point : Fraction.Rational) (lower : interval.start ≤ point) (upper : point ≤ interval.finish) :
    (readingRange prepared (SourcePoint.atStart source interval (prepared.partition.valid interval member))).Contains
      (source point) := by
  have valid := prepared.partition.valid interval member
  have pointLower := valid.1.trans lower
  have pointUpper := upper.trans valid.2.2
  cases marked : interval.regionMarked prepared.regions with
  | true =>
      change (if interval.regionMarked prepared.regions then
        (⟨-modulus.magnitude, modulus.magnitude,
          Arithmetic.neg_le_self_of_nonnegative modulus.magnitude_nonnegative⟩ :
          Purelib.Data.Rat.Interval)
        else Continuous.readingRange prepared.variation prepared.variationPositive.le
          (SourcePoint.atStart source interval (prepared.partition.valid interval member))).Contains (source point)
      rw [marked]
      exact modulus.bounded point pointLower pointUpper
  | false =>
      have noRegions : ∀ region ∈ modulus.regions prepared.regionBudget,
          ¬ (interval.start ≤ region.finish ∧ region.start ≤ point) := by
        intro region present inside
        have retained : region ∈ prepared.regions := prepared.regions_eq.symm ▸ present
        have hit := (interval.regionMarked_iff prepared.regions).mpr
          ⟨region, retained, inside.1, inside.2.trans upper⟩
        rw [marked] at hit
        cases hit
      have difference : point - interval.start ≤ interval.signedLength :=
        Arithmetic.sub_le_sub_direct upper le_rfl
      have small : point - interval.start < modulus.radius prepared.regionBudget prepared.variation :=
        difference.trans_lt ((prepared.intervalSmall interval member).trans_le prepared.mesh_le_regular)
      have bounded := modulus.variation prepared.regionBudget prepared.regionBudgetPositive
        prepared.variation prepared.variationPositive interval.start point valid.1 lower pointUpper noRegions small
      change (if interval.regionMarked prepared.regions then
        (⟨-modulus.magnitude, modulus.magnitude,
          Arithmetic.neg_le_self_of_nonnegative modulus.magnitude_nonnegative⟩ :
          Purelib.Data.Rat.Interval)
        else Continuous.readingRange prepared.variation prepared.variationPositive.le
          (SourcePoint.atStart source interval (prepared.partition.valid interval member))).Contains (source point)
      rw [marked]
      exact bounded

/-- Read each original grid start once and retain the selected source-linked range. -/
@[expose] def frontier {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus) : SourceFrontier source :=
  SourceFrontier.ofRanges source prepared.partition (readingRange prepared) prepared.rangeValid

/-- Build this region preparation using matching retained exact source readings. -/
@[expose] def frontierCached {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus)
    (cached : List (SourcePoint source)) : SourceFrontier source :=
  SourceFrontier.ofRangesCached source cached prepared.partition (readingRange prepared) prepared.rangeValid

/-- Reusing exact readings preserves the original region frontier. -/
theorem frontierCached_eq {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus)
    (cached : List (SourcePoint source)) : prepared.frontierCached cached = prepared.frontier :=
  SourceFrontier.ofRangesCached_eq source cached prepared.partition (readingRange prepared) prepared.rangeValid

/-- The finite cell-weight sum agrees with its original integration-weight recursion. -/
private theorem weight_sum {α : Type} : ∀ cells : List (IntegrationCell α),
    integrationWeight cells = (cells.map (fun cell => cell.weight)).sum
  | [] => rfl
  | cell :: remaining => by
      change cell.weight + integrationWeight remaining = cell.weight + (remaining.map (fun other => other.weight)).sum
      rw [weight_sum remaining]

/-- The marked cell weights read back to the actual union length of the retained partition. -/
private theorem marked_weight_eq {source : Fraction.Rational → Fraction.Rational}
    (frontier : SourceFrontier source) (regions : List Partition.Interval) :
    (frontier.cells.map (fun cell => if cell.item.interval.regionMarked regions then cell.weight else 0)).sum =
      frontier.partition.regionsLength regions := by
  have weights : ∀ cell ∈ frontier.cells,
      (if cell.item.interval.regionMarked regions then cell.weight else 0) =
        if cell.item.interval.regionMarked regions then cell.item.interval.signedLength else 0 := by
    intro cell member
    rw [frontier.weight_eq cell member]
  calc
    _ = (frontier.cells.map (fun cell =>
        if cell.item.interval.regionMarked regions then cell.item.interval.signedLength else 0)).sum :=
      sum_congr _ _ frontier.cells weights
    _ = ((frontier.cells.map (fun cell => cell.item.interval)).map
        (fun interval => if interval.regionMarked regions then interval.signedLength else 0)).sum := by
      rw [Purelib.Data.List.Map.map_map]
      rfl
    _ = frontier.partition.regionsLength regions := by rw [frontier.domains_eq]; rfl

/-- The actual weighted oscillation is bounded by regular variation and marked-cell contributions. -/
theorem oscillation_le {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus) :
    integralOscillation prepared.frontier.cells ≤
      integrationWeight prepared.frontier.cells * (prepared.variation + prepared.variation) +
        (modulus.magnitude + modulus.magnitude) * prepared.partition.regionsLength prepared.regions := by
  let regular := prepared.variation + prepared.variation
  let exceptional := modulus.magnitude + modulus.magnitude
  let markedWeight := fun cell : IntegrationCell (SourcePoint source) =>
    if cell.item.interval.regionMarked prepared.regions then cell.weight else 0
  let extra := fun cell : IntegrationCell (SourcePoint source) =>
    if cell.item.interval.regionMarked prepared.regions then exceptional else 0
  have regularNonnegative : 0 ≤ regular := by
    have sum := Arithmetic.add_le_add_direct prepared.variationPositive.le prepared.variationPositive.le
    change (0 : Fraction.Rational) ≤ regular at sum
    exact sum
  have cellBound : ∀ cell ∈ prepared.frontier.cells, cell.oscillation ≤ regular + extra cell := by
    intro cell member
    have width := SourceFrontier.ofRanges_oscillation source prepared.partition
      (readingRange prepared) prepared.rangeValid cell member
    rw [readingRange_width] at width
    cases marked : cell.item.interval.regionMarked prepared.regions with
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
    cases cell.item.interval.regionMarked prepared.regions with
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
        prepared.partition.regionsLength prepared.regions * exceptional := weighted
    _ = integrationWeight prepared.frontier.cells * regular +
        exceptional * prepared.partition.regionsLength prepared.regions := by ring1

/-- The computed region and regular budgets meet the original positive enclosure-width request. -/
theorem frontier_width_lt {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus) :
    (integralBound prepared.frontier.cells).width < prepared.request.tolerance := by
  have weighted := prepared.oscillation_le
  rw [prepared.frontier.totalWeight, Fraction.Field.one_mul] at weighted
  have paid := Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl (prepared.variation + prepared.variation)) prepared.markedBudget
  have bound := weighted.trans paid
  have budgetEq : (prepared.variation + prepared.variation) + (prepared.variation + prepared.variation) =
      prepared.request.tolerance / 2 := by
    rw [prepared.variation_eq]
    apply Fraction.Field.mul_right_cancel_of_ne (c := (2 : Fraction.Rational)) (by decide)
    calc
      _ = (prepared.request.tolerance / 8) * 8 := by ring1
      _ = prepared.request.tolerance := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
      _ = (prepared.request.tolerance / 2) * 2 :=
        (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)).symm
  rw [budgetEq] at bound
  rw [integralBound_width]
  exact bound.trans_lt (Fraction.Order.Field.half_lt_self prepared.request.positive)

end Preparation

set_option genInjectivity false in
/-- A completed request retaining its selected regions, actual source frontier and paid width. -/
structure Result {source : Fraction.Rational → Fraction.Rational}
    (modulus : Modulus source) where
  /-- The original request and its computed finite regions and mesh. -/ preparation : Preparation modulus
  /-- The actual cached source-linked frontier. -/ frontier : SourceFrontier source
  /-- The frontier is exactly the one constructed from the retained preparation. -/ frontier_eq :
    frontier = preparation.frontier
  /-- The actual integral enclosure meets the original request. -/ accurate :
    (integralBound frontier.cells).width < preparation.request.tolerance

constructive_injectivity Result

/-- Compute the complete finite region-source frontier for one positive integration request. -/
@[expose] def build {source : Fraction.Rational → Fraction.Rational}
    (modulus : Modulus source) (request : AccuracyRequest) : Result modulus :=
  let preparation := Preparation.prepare modulus request
  { preparation := preparation
    frontier := preparation.frontier
    frontier_eq := rfl
    accurate := preparation.frontier_width_lt }

/-- Compute the original region result using matching previously retained source readings. -/
@[expose] def buildCached {source : Fraction.Rational → Fraction.Rational}
    (modulus : Modulus source) (cached : List (SourcePoint source))
    (request : AccuracyRequest) : Result modulus := by
  let preparation := Preparation.prepare modulus request
  let frontier := preparation.frontierCached cached
  have same : frontier = preparation.frontier := preparation.frontierCached_eq cached
  exact
    { preparation := preparation
      frontier := frontier
      frontier_eq := same
      accurate := same.symm ▸ preparation.frontier_width_lt }

/-- Cache-selected construction preserves the complete original region result. -/
theorem buildCached_eq {source : Fraction.Rational → Fraction.Rational}
    (modulus : Modulus source) (cached : List (SourcePoint source))
    (request : AccuracyRequest) : buildCached modulus cached request = build modulus request := by
  unfold buildCached build
  simp only [-eq_self, -iff_self, Preparation.frontierCached_eq]
  rfl

/-- Use the original effective-region construction as a persistent source-frontier producer. -/
@[expose] def producer {source : Fraction.Rational → Fraction.Rational}
    (modulus : Modulus source) : SourceFrontier.Producer source where
  Output := Result modulus
  request := build modulus
  requestCached := buildCached modulus
  requestCached_eq := buildCached_eq modulus
  frontier := Result.frontier
  accurate := fun request => (build modulus request).accurate

end Purelib.Integration.SourceFrontier.Exceptional.Region.Builder

end
