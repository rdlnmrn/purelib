module

public import Purelib.Approximation.Rational.Pi.Source
import Purelib.Integration.Partition.Uniform.Grid
import Purelib.Data.List.Range.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

/-!
# Endpoint enclosures for the circle source

The original uniform request with `extra` interior cuts supplies `extra + 1`
intervals. Each cell retains its original interval, its left endpoint tag and
the exact length; its range uses both endpoint source readings.
-/

namespace Purelib.Approximation.Rational.Pi.Endpoint

open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Integration
open Purelib.Integration.Partition

/-- The exact endpoint range associated with an original source observation.

The minimum and maximum make the construction meaningful for any observation;
on a unit partition the decreasing circle source puts the finish reading first. -/
@[expose] public def range (tag : SourcePoint Source.value) : Purelib.Data.Rat.Interval :=
  ⟨min (Source.value tag.interval.finish) tag.reading,
    max (Source.value tag.interval.finish) tag.reading,
    (Basic.min_le_right _ _).trans (Basic.le_max_right _ _)⟩

/-- The endpoint range encloses the circle source throughout each original unit cell. -/
public theorem range_valid (partition : Unit.Normalized) (interval : Partition.Interval)
    (member : interval ∈ partition.intervals) (point : Fraction.Rational)
    (lower : interval.start ≤ point) (upper : point ≤ interval.finish) :
    (range (SourcePoint.atStart Source.value interval (partition.valid interval member))).Contains
      (Source.value point) := by
  have valid := partition.valid interval member
  constructor
  · exact (Basic.min_le_left _ _).trans (Source.value_antitone (valid.1.trans lower) upper)
  · exact (Source.value_antitone valid.1 lower).trans (Basic.le_max_right _ _)

/-- The original normalized partition for a positive number `extra + 1` of uniform cells. -/
@[expose] public def partition (extra : Nat) : Unit.Normalized :=
  Unit.Normalized.ofRequest (Purelib.CCL.Progressive.IntegrationPrograms.uniformCuts extra)

/-- The source-linked endpoint frontier on the original uniform partition.

The builder reads the left endpoint once for each retained cell and certifies
its entire range, keeping the ordered cells, exact weights and partition cache. -/
@[expose] public def frontier (extra : Nat) : SourceFrontier Source.value :=
  SourceFrontier.ofRanges Source.value (partition extra) range (range_valid (partition extra))

/-- The endpoint frontier retains the actual normalized uniform partition. -/
public theorem frontier_partition (extra : Nat) : (frontier extra).partition = partition extra := rfl

/-- Each retained cell has the reciprocal of the original positive cell count as weight. -/
public theorem frontier_weight (extra : Nat) (cell : IntegrationCell (SourcePoint Source.value))
    (member : cell ∈ (frontier extra).cells) :
    cell.weight = 1 / ((extra + 1 : Nat) : Fraction.Rational) := by
  rw [(frontier extra).weight_eq cell member]
  apply Uniform.Grid.uniform_interval_length extra
  have domains := (frontier extra).domains_eq
  change cell.item.interval ∈ (frontier extra).partition.intervals
  rw [← domains]
  exact Purelib.Data.List.Map.mem_map.mpr ⟨cell, member, rfl⟩

/-- Each original cell retains its left tag and both exact endpoint readings.

The lower endpoint is the source value at the cell finish, and the upper
endpoint is the source value at the start. -/
public theorem frontier_endpoints (extra : Nat) (cell : IntegrationCell (SourcePoint Source.value))
    (member : cell ∈ (frontier extra).cells) :
    cell.item.point = cell.item.interval.start ∧
      cell.lower = Source.value cell.item.interval.finish ∧
      cell.upper = Source.value cell.item.interval.start := by
  change cell ∈ (partition extra).intervals.attach.map
    (SourceFrontier.rangeCell Source.value (partition extra) range) at member
  obtain ⟨entry, _, equal⟩ := Purelib.Data.List.Map.mem_map.mp member
  cases equal
  have valid := (partition extra).valid entry.val entry.property
  have ordered := Source.value_antitone valid.1 valid.2.1.le
  change _ ∧ min (Source.value entry.val.finish) (Source.value entry.val.start) = _ ∧
    max (Source.value entry.val.finish) (Source.value entry.val.start) = _
  exact ⟨rfl, Basic.min_eq_left ordered, Basic.max_eq_right ordered⟩

/-- The consecutive grid chain retains the ascending indices of its intervals. -/
private theorem grid_intervals (denominator : Nat) : ∀ start count,
    Partition.Interval.intervalsBetween (Uniform.Grid.point denominator start)
      (Uniform.Grid.point denominator (start + count + 1)) (Uniform.Grid.nodes denominator start count) =
      (List.range (count + 1)).map (fun index =>
        (⟨Uniform.Grid.point denominator (start + index),
          Uniform.Grid.point denominator (start + index + 1)⟩ : Partition.Interval))
  | start, 0 => by
      rfl
  | start, count + 1 => by
      rw [Purelib.Data.List.Range.Basic.range_succ_eq_map, List.map_cons, Purelib.Data.List.Map.map_map]
      change _ :: Partition.Interval.intervalsBetween (Uniform.Grid.point denominator (start + 1))
        (Uniform.Grid.point denominator (start + (count + 1) + 1))
        (Uniform.Grid.nodes denominator (start + 1) count) = _ :: _
      apply congrArg (List.cons _)
      rw [show start + (count + 1) + 1 = (start + 1) + count + 1 from by omega0,
        grid_intervals denominator (start + 1) count]
      apply Purelib.Data.List.Map.map_congr_left
      intro index _
      change (⟨Uniform.Grid.point denominator (start + 1 + index),
        Uniform.Grid.point denominator (start + 1 + index + 1)⟩ : Partition.Interval) =
        ⟨Uniform.Grid.point denominator (start + (index + 1)),
          Uniform.Grid.point denominator (start + (index + 1) + 1)⟩
      rw [show start + 1 + index = start + (index + 1) from by omega0]

/-- The actual ordered cell domains are the original consecutive indexed grid intervals. -/
public theorem frontier_domains (extra : Nat) :
    (frontier extra).cells.map (fun cell => cell.item.interval) =
      (List.range (extra + 1)).map (fun index =>
        (⟨Uniform.Grid.point (extra + 1) index, Uniform.Grid.point (extra + 1) (index + 1)⟩ :
          Partition.Interval)) := by
  rw [(frontier extra).domains_eq, frontier_partition]
  change (Unit.Normalized.ofRequest (Purelib.CCL.Progressive.IntegrationPrograms.uniformCuts extra)).intervals = _
  rw [Uniform.Grid.uniform_intervals, grid_intervals]
  apply Purelib.Data.List.Map.map_congr_left
  intro index _
  rw [Nat.zero_add]

/-- The finite lower and upper sums retain each original cell occurrence and endpoint reading. -/
private theorem integral_readbacks (weight : Fraction.Rational) :
    ∀ cells : List (IntegrationCell (SourcePoint Source.value)),
      (∀ cell ∈ cells, cell.weight = weight) →
      (∀ cell ∈ cells, cell.lower = Source.value cell.item.interval.finish ∧
        cell.upper = Source.value cell.item.interval.start) →
      lowerIntegral cells = (cells.map (fun cell => weight * Source.value cell.item.interval.finish)).sum ∧
      upperIntegral cells = (cells.map (fun cell => weight * Source.value cell.item.interval.start)).sum
  | [], _, _ => ⟨rfl, rfl⟩
  | cell :: tail, weights, endpoints => by
      have remaining := integral_readbacks weight tail
        (fun other member => weights other (List.mem_cons_of_mem _ member))
        (fun other member => endpoints other (List.mem_cons_of_mem _ member))
      have headWeight := weights cell List.mem_cons_self
      have headEndpoints := endpoints cell List.mem_cons_self
      constructor
      · change cell.weight * cell.lower + lowerIntegral tail =
          weight * Source.value cell.item.interval.finish +
            (tail.map (fun other => weight * Source.value other.item.interval.finish)).sum
        rw [headWeight, headEndpoints.1, remaining.1]
      · change cell.weight * cell.upper + upperIntegral tail =
          weight * Source.value cell.item.interval.start +
            (tail.map (fun other => weight * Source.value other.item.interval.start)).sum
        rw [headWeight, headEndpoints.2, remaining.2]

/-- The lower integral is the ordered sum of the original right endpoint readings. -/
public theorem lowerIntegral_eq (extra : Nat) :
    lowerIntegral (frontier extra).cells =
      ((List.range (extra + 1)).map (fun index =>
        (1 / ((extra + 1 : Nat) : Fraction.Rational)) *
          Source.value (Uniform.Grid.point (extra + 1) (index + 1)))).sum := by
  let weight : Fraction.Rational := 1 / ((extra + 1 : Nat) : Fraction.Rational)
  have readback := integral_readbacks weight (frontier extra).cells
    (fun cell member => frontier_weight extra cell member)
    (fun cell member => ⟨(frontier_endpoints extra cell member).2.1,
      (frontier_endpoints extra cell member).2.2⟩)
  rw [readback.1]
  change ((frontier extra).cells.map (fun cell => weight * Source.value cell.item.interval.finish)).sum = _
  calc
    _ = (((frontier extra).cells.map (fun cell => cell.item.interval)).map
      (fun interval => weight * Source.value interval.finish)).sum :=
        congrArg (fun values : List Fraction.Rational => values.sum)
          (Purelib.Data.List.Map.map_map (fun interval : Partition.Interval => weight * Source.value interval.finish)
            (fun cell : IntegrationCell (SourcePoint Source.value) => cell.item.interval) _).symm
    _ = _ := by rw [frontier_domains, Purelib.Data.List.Map.map_map]; rfl

/-- The upper integral is the ordered sum of the original left endpoint readings. -/
public theorem upperIntegral_eq (extra : Nat) :
    upperIntegral (frontier extra).cells =
      ((List.range (extra + 1)).map (fun index =>
        (1 / ((extra + 1 : Nat) : Fraction.Rational)) *
          Source.value (Uniform.Grid.point (extra + 1) index))).sum := by
  let weight : Fraction.Rational := 1 / ((extra + 1 : Nat) : Fraction.Rational)
  have readback := integral_readbacks weight (frontier extra).cells
    (fun cell member => frontier_weight extra cell member)
    (fun cell member => ⟨(frontier_endpoints extra cell member).2.1,
      (frontier_endpoints extra cell member).2.2⟩)
  rw [readback.2]
  change ((frontier extra).cells.map (fun cell => weight * Source.value cell.item.interval.start)).sum = _
  calc
    _ = (((frontier extra).cells.map (fun cell => cell.item.interval)).map
      (fun interval => weight * Source.value interval.start)).sum :=
        congrArg (fun values : List Fraction.Rational => values.sum)
          (Purelib.Data.List.Map.map_map (fun interval : Partition.Interval => weight * Source.value interval.start)
            (fun cell : IntegrationCell (SourcePoint Source.value) => cell.item.interval) _).symm
    _ = _ := by rw [frontier_domains, Purelib.Data.List.Map.map_map]; rfl

/-- The retained weighted oscillations are the negated transformed endpoint lengths. -/
private theorem oscillation_readback (weight : Fraction.Rational) :
    ∀ cells : List (IntegrationCell (SourcePoint Source.value)),
      (∀ cell ∈ cells, cell.weight = weight) →
      (∀ cell ∈ cells, cell.lower = Source.value cell.item.interval.finish ∧
        cell.upper = Source.value cell.item.interval.start) →
      integralOscillation cells = -weight * Partition.Interval.lengthSum
        (cells.map (fun cell => ⟨Source.value cell.item.interval.start, Source.value cell.item.interval.finish⟩))
  | [], _, _ => by
      change (0 : Fraction.Rational) = -weight * 0
      ring1
  | cell :: tail, weights, endpoints => by
      have remaining := oscillation_readback weight tail
        (fun other member => weights other (List.mem_cons_of_mem _ member))
        (fun other member => endpoints other (List.mem_cons_of_mem _ member))
      have headWeight := weights cell List.mem_cons_self
      have headEndpoints := endpoints cell List.mem_cons_self
      change cell.weight * (cell.upper - cell.lower) + integralOscillation tail =
        -weight * ((Source.value cell.item.interval.finish - Source.value cell.item.interval.start) +
          Partition.Interval.lengthSum (tail.map (fun item =>
            ⟨Source.value item.item.interval.start, Source.value item.item.interval.finish⟩)))
      rw [headWeight, headEndpoints.1, headEndpoints.2, remaining]
      ring1

/-- The exact uniform endpoint frontier has width `2 / (extra + 1)`.

The actual ordered cells project to the original interval chain. Mapping its
endpoints through the circle source telescopes the same weighted oscillations. -/
public theorem frontier_width (extra : Nat) :
    (integralBound (frontier extra).cells).width = 2 / ((extra + 1 : Nat) : Fraction.Rational) := by
  let cells := (frontier extra).cells
  have telescope := (frontier extra).partition.chain.lengthSum_mapEndpoints Source.value
  rw [← (frontier extra).domains_eq, Purelib.Data.List.Map.map_map] at telescope
  have readback := oscillation_readback (1 / ((extra + 1 : Nat) : Fraction.Rational)) cells
    (fun cell member => frontier_weight extra cell member)
    (fun cell member => ⟨(frontier_endpoints extra cell member).2.1,
      (frontier_endpoints extra cell member).2.2⟩)
  change Partition.Interval.lengthSum (cells.map (fun cell =>
    ⟨Source.value cell.item.interval.start, Source.value cell.item.interval.finish⟩)) =
      Source.value 1 - Source.value 0 at telescope
  rw [integralBound_width, readback, telescope]
  have atZero : Source.value 0 = 4 := by decide
  have atOne : Source.value 1 = 2 := by decide
  rw [atZero, atOne]
  rw [Fraction.Field.div_eq_mul_inv_direct 1 _, Fraction.Field.div_eq_mul_inv_direct 2 _]
  ring1

end Purelib.Approximation.Rational.Pi.Endpoint
