module
public import Purelib.Integration.Cell.Source
public import Purelib.Integration.Partition.Uniform.Grid
public import Purelib.Approximation.Rational.Uniform.Modulus
public import Purelib.Approximation.AccuracyRequest
public import Purelib.Data.Rat.Interval.Bisection
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Effective integration from a rational uniform modulus

A positive request pays for an explicit variation and an actual uniform
partition. Each cell's source range is built from its cached left-endpoint
reading and the supplied source variation law.
-/

public section

namespace Purelib.Integration.SourceFrontier.Continuous

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- Enclose values within a nonnegative variation of the retained exact source reading. -/
@[expose] def readingRange {source : Fraction.Rational → Fraction.Rational}
    (variation : Fraction.Rational) (nonnegative : 0 ≤ variation) (tag : SourcePoint source) :
    Purelib.Data.Rat.Interval where
  lower := tag.reading - variation
  upper := tag.reading + variation
  valid := by
    have signed := Fraction.Order.Arithmetic.neg_le_self_of_nonnegative nonnegative
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct signed tag.reading
    calc
      tag.reading - variation = -variation + tag.reading := by ring1
      _ ≤ variation + tag.reading := shifted
      _ = tag.reading + variation := by ring1

/-- The reading-derived range has exactly twice the supplied variation as its width. -/
theorem readingRange_width {source : Fraction.Rational → Fraction.Rational}
    (variation : Fraction.Rational) (nonnegative : 0 ≤ variation) (tag : SourcePoint source) :
    (readingRange variation nonnegative tag).width = variation + variation := by
  change (tag.reading + variation) - (tag.reading - variation) = variation + variation
  ring1

set_option genInjectivity false in
/-- A positive integration request with its computed variation, mesh and original normalized partition.

The source and its original modulus remain the indexed owners. The requested
tolerance, computed quarter budget, modulus response and actual partition are
retained together with their exact defining equations. -/
structure Preparation {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) where
  /-- The original positive rational width request. -/ request : AccuracyRequest
  /-- The retained local variation budget. -/ variation : Fraction.Rational
  /-- The local variation is one quarter of the original request. -/ variation_eq :
    variation = request.tolerance / 4
  /-- The original modulus's computed distance for the retained variation. -/ mesh : Fraction.Rational
  /-- The mesh is the actual response of the same original modulus. -/ mesh_eq : mesh = modulus.radius variation
  /-- The original normalized uniform partition selected from that distance. -/ partition : Unit.Normalized
  /-- The partition is the exact computed uniform partition for the retained mesh. -/ partition_eq :
    partition = Uniform.Grid.forWidth mesh

constructive_injectivity Preparation

namespace Preparation

/-- Compute a finite mesh and normalized partition from the original request and modulus. -/
@[expose] def prepare {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (request : AccuracyRequest) : Preparation modulus :=
  let variation := request.tolerance / 4
  let mesh := modulus.radius variation
  let partition := Uniform.Grid.forWidth mesh
  { request := request
    variation := variation
    variation_eq := rfl
    mesh := mesh
    mesh_eq := rfl
    partition := partition
    partition_eq := rfl }

/-- The retained quarter-variation budget is strictly positive. -/
theorem variationPositive {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) : 0 < prepared.variation := by
  rw [prepared.variation_eq]
  exact Bounds.Quarter.quarter_pos prepared.request.positive

/-- The retained mesh is the original modulus response to a positive variation request. -/
theorem meshPositive {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) : 0 < prepared.mesh := by
  rw [prepared.mesh_eq]
  exact modulus.radius_pos prepared.variation prepared.variationPositive

/-- Every actual retained partition interval has length below the computed modulus distance. -/
theorem intervalSmall {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus)
    (interval : Partition.Interval) (member : interval ∈ prepared.partition.intervals) :
    interval.signedLength < prepared.mesh := by
  have intervals := congrArg Unit.Normalized.intervals prepared.partition_eq
  have actual : interval ∈ (Uniform.Grid.forWidth prepared.mesh).intervals := intervals ▸ member
  exact Uniform.Grid.forWidth_interval_lt prepared.meshPositive interval actual

/-- The range from an original left-endpoint reading encloses the source throughout that retained cell. -/
theorem rangeValid {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus)
    (interval : Partition.Interval) (member : interval ∈ prepared.partition.intervals)
    (point : Fraction.Rational) (lower : interval.start ≤ point) (upper : point ≤ interval.finish) :
    (readingRange prepared.variation prepared.variationPositive.le
      (SourcePoint.atStart source interval (prepared.partition.valid interval member))).Contains (source point) := by
  have valid := prepared.partition.valid interval member
  have difference : point - interval.start ≤ interval.signedLength :=
    Fraction.Order.Arithmetic.sub_le_sub_direct upper le_rfl
  have small : point - interval.start < modulus.radius prepared.variation := by
    have mesh := prepared.intervalSmall interval member
    rw [prepared.mesh_eq] at mesh
    exact difference.trans_lt mesh
  have bounded := modulus.variation prepared.variation prepared.variationPositive interval.start point valid.1 lower
    (upper.trans valid.2.2) small
  change source interval.start - prepared.variation ≤ source point ∧
    source point ≤ source interval.start + prepared.variation
  exact bounded

/-- Read each actual partition start once and construct its source-linked rational range. -/
@[expose] def frontier {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) : SourceFrontier source :=
  SourceFrontier.ofRanges source prepared.partition
    (readingRange prepared.variation prepared.variationPositive.le) prepared.rangeValid

/-- Build this preparation's frontier using matching retained source readings. -/
@[expose] def frontierCached {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus)
    (cached : List (SourcePoint source)) : SourceFrontier source :=
  SourceFrontier.ofRangesCached source cached prepared.partition
    (readingRange prepared.variation prepared.variationPositive.le) prepared.rangeValid

/-- Reusing exact readings preserves the original prepared frontier. -/
theorem frontierCached_eq {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus)
    (cached : List (SourcePoint source)) : prepared.frontierCached cached = prepared.frontier :=
  SourceFrontier.ofRangesCached_eq source cached prepared.partition
    (readingRange prepared.variation prepared.variationPositive.le) prepared.rangeValid

/-- The computed source frontier's integral enclosure is strictly narrower than the original request. -/
theorem frontier_width_lt {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) :
    (integralBound prepared.frontier.cells).width < prepared.request.tolerance := by
  have nonnegative : 0 ≤ prepared.variation + prepared.variation := by
    have sum := Fraction.Order.Arithmetic.add_le_add_direct prepared.variationPositive.le prepared.variationPositive.le
    change (0 : Fraction.Rational) ≤ prepared.variation + prepared.variation at sum
    exact sum
  have bounded : ∀ cell ∈ prepared.frontier.cells, cell.oscillation ≤ prepared.variation + prepared.variation := by
    intro cell member
    have width := SourceFrontier.ofRanges_oscillation source prepared.partition
      (readingRange prepared.variation prepared.variationPositive.le) prepared.rangeValid cell member
    rewrite [width, readingRange_width]
    exact Fraction.Order.Basic.le_refl _
  have budget : integrationWeight prepared.frontier.cells * (prepared.variation + prepared.variation) <
      prepared.request.tolerance := by
    rw [prepared.frontier.totalWeight, Fraction.Field.one_mul, prepared.variation_eq, Bounds.Quarter.two_quarters]
    exact Fraction.Order.Field.half_lt_self prepared.request.positive
  exact integralBound_width_lt_of_uniform nonnegative bounded budget

end Preparation

set_option genInjectivity false in
/-- A completed finite request retaining its preparation, actual source frontier and paid width.

The cached frontier is exactly the one built from the retained preparation,
and its original integral enclosure meets the retained positive request. -/
structure Result {source : Fraction.Rational → Fraction.Rational} (modulus : Rational.Uniform.Modulus source) where
  /-- The original request and its computed mesh and partition. -/ preparation : Preparation modulus
  /-- The actual cached source-linked frontier. -/ frontier : SourceFrontier source
  /-- The frontier is the exact output of the retained preparation. -/ frontier_eq : frontier = preparation.frontier
  /-- The original request pays for the retained frontier's weighted oscillation. -/ accurate :
    (integralBound frontier.cells).width < preparation.request.tolerance

constructive_injectivity Result

namespace Result

/-- Continuous results with the same preparation and source frontier are equal. -/
theorem ext {source : Fraction.Rational → Fraction.Rational} {modulus : Rational.Uniform.Modulus source}
    (left right : Result modulus) (preparation_eq : left.preparation = right.preparation)
    (frontier_eq : left.frontier = right.frontier) : left = right := by
  cases left with
  | mk leftPreparation leftFrontier leftEqual leftAccurate =>
    cases right with
    | mk rightPreparation rightFrontier rightEqual rightAccurate =>
      cases preparation_eq
      cases frontier_eq
      rfl

/-- Select the midpoint of the original retained frontier's integral enclosure. -/
@[expose] def answer {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (result : Result modulus) : Fraction.Rational :=
  (integralBound result.frontier.cells).midpoint

/-- The computed answer lies in the original frontier's integral enclosure. -/
theorem answer_contains {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (result : Result modulus) :
    (integralBound result.frontier.cells).Contains result.answer :=
  (integralBound result.frontier.cells).midpoint_contains

/-- Every rational admitted by the original enclosure differs from its answer by at most half the width. -/
theorem answer_error {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (result : Result modulus) (value : Fraction.Rational)
    (inside : (integralBound result.frontier.cells).Contains value) :
    Fraction.abs (value - result.answer) ≤ (integralBound result.frontier.cells).width * (1 / 2) :=
  Interval.abs_sub_midpoint_le inside

end Result

/-- Compute the complete finite source frontier for one positive integration request. -/
@[expose] def build {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (request : AccuracyRequest) : Result modulus :=
  let preparation := Preparation.prepare modulus request
  let frontier := preparation.frontier
  { preparation := preparation
    frontier := frontier
    frontier_eq := rfl
    accurate := preparation.frontier_width_lt }

/-- Compute the original continuous result using matching previously retained source readings. -/
@[expose] def buildCached {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (cached : List (SourcePoint source))
    (request : AccuracyRequest) : Result modulus := by
  let preparation := Preparation.prepare modulus request
  let frontier := preparation.frontierCached cached
  have same : frontier = preparation.frontier := preparation.frontierCached_eq cached
  exact
    { preparation := preparation
      frontier := frontier
      frontier_eq := same
      accurate := same.symm ▸ preparation.frontier_width_lt }

/-- Cache-selected construction preserves the complete original continuous result. -/
theorem buildCached_eq {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (cached : List (SourcePoint source))
    (request : AccuracyRequest) : buildCached modulus cached request = build modulus request := by
  unfold buildCached build
  simp only [-eq_self, -iff_self, Preparation.frontierCached_eq]
  rfl

end Purelib.Integration.SourceFrontier.Continuous

end
