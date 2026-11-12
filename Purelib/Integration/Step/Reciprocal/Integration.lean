module
public import Purelib.Integration.Step.Reciprocal.Truncated
public import Purelib.Integration.Cell.Source.Initial
public import Purelib.Integration.Cell.Source.Exceptional
public import Purelib.Integration.Cell.Source.Producer
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Interval.Bisection
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite rational integration of the reciprocal step

Every positive request selects a finite reciprocal tail, constructs an
exceptional frontier for the truncated rule and restores the original rule
on the tail with the exact range `[0,1]`. All cells, tags, cached readings
and the original truncated result remain retained.
-/

public section

namespace Purelib.Integration.Step.Reciprocal

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Integration

/-- Reserve one quarter of the original positive integration request. -/
@[expose] def quarterRequest (request : AccuracyRequest) : AccuracyRequest :=
  ⟨request.tolerance / 4, Bounds.Quarter.quarter_pos request.positive⟩

/-- The exact range of every original reciprocal-step reading. -/
@[expose] def unitRange : Purelib.Data.Rat.Interval := ⟨0, 1, by decide⟩

/-- The original reciprocal step lies in its retained unit range at every rational point. -/
theorem unitRange_contains (point : Fraction.Rational) : unitRange.Contains (value point) :=
  value_range point

/-- Construct the finite exceptional-source model selected by the original request. -/
@[expose] def auxiliaryModulus (request : AccuracyRequest) :
    Rational.Exceptional.Modulus (truncated (tailCount request.tolerance)) :=
  truncatedModulus (tailCount request.tolerance) (tailCount_ge_two request.tolerance)

/-- Compute the actual truncated-source result using the retained quarter request. -/
@[expose] def auxiliaryResult (request : AccuracyRequest) :
    SourceFrontier.Exceptional.Result (auxiliaryModulus request) :=
  SourceFrontier.Exceptional.build (auxiliaryModulus request) (quarterRequest request)

/-- Above the selected tail, the original and truncated source readings are identical. -/
theorem agreement (request : AccuracyRequest) (point : Fraction.Rational)
    (above : 1 / (tailCount request.tolerance : Fraction.Rational) < point) :
    value point = truncated (tailCount request.tolerance) point :=
  (truncated_eq_of_above _ point above).symm

/-- Transfer saved readings using one retained truncated-source tail.

The supplied endpoint is the reciprocal of the selected count and is shared
by every entry. Only points above it are transferred. -/
@[expose] def auxiliaryCachedReadingsAt (count : Nat) (endpoint : Fraction.Rational)
    (endpointEq : endpoint = 1 / (count : Fraction.Rational)) :
    List (SourcePoint value) → List (SourcePoint (truncated count))
  | [] => []
  | retained :: remaining =>
      if above : endpoint < retained.point then
        have aboveCount : 1 / (count : Fraction.Rational) < retained.point := by
          rw [← endpointEq]
          exact above
        { interval := retained.interval
          point := retained.point
          start_le := retained.start_le
          point_le_finish := retained.point_le_finish
          reading := retained.reading
          reading_eq := retained.reading_eq.trans (truncated_eq_of_above count retained.point aboveCount).symm } ::
            auxiliaryCachedReadingsAt count endpoint endpointEq remaining
      else
        auxiliaryCachedReadingsAt count endpoint endpointEq remaining

/-- Transfer saved original readings to the request's truncated source where their values agree.

Only points strictly above the selected tail are transferred. Each resulting
point retains its original interval, rational tag and cached reading. -/
@[expose] def auxiliaryCachedReadings (request : AccuracyRequest) (cached : List (SourcePoint value)) :
    List (SourcePoint (truncated (tailCount request.tolerance))) :=
  let count := tailCount request.tolerance
  let endpoint := 1 / (count : Fraction.Rational)
  auxiliaryCachedReadingsAt count endpoint rfl cached

/-- Restore the original step source on the actual truncated frontier's initial tail. -/
@[expose] def frontier (request : AccuracyRequest) : SourceFrontier value :=
  SourceFrontier.Initial.replace (auxiliaryResult request).frontier
    (1 / (tailCount request.tolerance : Fraction.Rational)) unitRange (agreement request)
    (fun point _ _ => unitRange_contains point)

/-- The restored original-source frontier meets the original positive width request.

The tail costs less than half the request. The actual truncated enclosure
costs less than one quarter, and its retained mesh is at most another
quarter; the original marked-cell accounting includes the closed tail end. -/
theorem frontier_width_lt (request : AccuracyRequest) :
    (integralBound (frontier request).cells).width < request.tolerance := by
  let result := auxiliaryResult request
  let tail : Fraction.Rational := 1 / (tailCount request.tolerance : Fraction.Rational)
  let mesh := result.preparation.mesh
  let oldWidth := (integralBound result.frontier.cells).width
  have requestEq : result.preparation.request = quarterRequest request := rfl
  have partitionEq : result.frontier.partition = result.preparation.partition := by
    rw [result.frontier_eq]
    rfl
  have tailPositive : 0 < tail := Fraction.Order.Field.div_pos_direct (by decide)
    (Fraction.Cast.Order.natCast_pos_direct
      (Nat.lt_of_lt_of_le (by decide : 0 < 2) (tailCount_ge_two request.tolerance)))
  have tailSmall : tail < request.tolerance / 2 := tail_width_lt request.tolerance request.positive
  have oldSmall : oldWidth < request.tolerance / 4 := by
    have accurate := result.accurate
    rw [requestEq] at accurate
    exact accurate
  have meshSmall : mesh ≤ request.tolerance / 4 := by
    have variationBound : result.preparation.variation ≤ request.tolerance / 4 := by
      rw [result.preparation.variation_eq, requestEq]
      change (request.tolerance / 4) / 4 ≤ request.tolerance / 4
      exact Fraction.Order.Field.divide_le_self (Bounds.Quarter.quarter_pos request.positive).le (by decide)
    exact result.preparation.mesh_le_variation.trans variationBound
  have small : ∀ interval ∈ result.frontier.partition.intervals, interval.signedLength < mesh := by
    intro interval member
    rw [partitionEq] at member
    exact result.preparation.intervalSmall interval member
  have marked := result.frontier.partition.initialLength_le tail mesh tailPositive.le
    result.preparation.meshPositive small
  have transferred := SourceFrontier.Initial.replace_oscillation_le result.frontier tail unitRange
    (agreement request) (fun point _ _ => unitRange_contains point)
  rw [← integralBound_width, ← integralBound_width] at transferred
  have rangeWidth : unitRange.width = 1 := by decide
  rw [rangeWidth, Fraction.Field.mul_one_direct] at transferred
  have replacedBound : (integralBound (frontier request).cells).width ≤ oldWidth + (tail + mesh) := by
    have enlarged := Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl oldWidth) marked
    exact transferred.trans enlarged
  have oldAndMesh : oldWidth + mesh < request.tolerance / 4 + request.tolerance / 4 := by
    have first := Fraction.Order.Arithmetic.add_lt_add_right_direct oldSmall mesh
    have second := Fraction.Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Basic.le_refl (request.tolerance / 4)) meshSmall
    exact first.trans_le second
  have paid := Fraction.Order.Arithmetic.add_lt_add_direct tailSmall oldAndMesh
  have leftIdentity : tail + (oldWidth + mesh) = oldWidth + (tail + mesh) := by ring1
  have rightIdentity : request.tolerance / 2 + (request.tolerance / 4 + request.tolerance / 4) =
      request.tolerance := by
    rw [Bounds.Quarter.two_quarters]
    have identity : request.tolerance / 2 + request.tolerance / 2 = (request.tolerance / 2) * 2 := by ring1
    rw [identity, Bounds.Quarter.half_mul_two]
  rw [leftIdentity, rightIdentity] at paid
  exact replacedBound.trans_lt paid

set_option genInjectivity false in
/-- A reciprocal-step request with its actual truncated construction and restored source frontier.

The original positive request selects the exact finite cutoff and auxiliary
request. The cached frontier is the actual source replacement over that
retained result, and its enclosure meets the original request. -/
structure Result where
  /-- The original positive integration request. -/ request : AccuracyRequest
  /-- The original finite exceptional construction for the selected truncation. -/
  auxiliary : SourceFrontier.Exceptional.Result (auxiliaryModulus request)
  /-- The auxiliary is the exact output selected by the retained request. -/ auxiliary_eq :
    auxiliary = auxiliaryResult request
  /-- The restored frontier of the original reciprocal step. -/ frontier : SourceFrontier value
  /-- The frontier uses the original auxiliary result and its actual partition. -/ frontier_eq :
    frontier = SourceFrontier.Initial.replace auxiliary.frontier
      (1 / (tailCount request.tolerance : Fraction.Rational)) unitRange (agreement request)
      (fun point _ _ => unitRange_contains point)
  /-- The retained original-source enclosure meets the original request. -/ accurate :
    (integralBound frontier.cells).width < request.tolerance

constructive_injectivity Result

namespace Result

/-- Select the midpoint of the retained original-source integral enclosure. -/
@[expose] def answer (result : Result) : Fraction.Rational :=
  (integralBound result.frontier.cells).midpoint

/-- The selected answer lies inside the original-source integral enclosure. -/
theorem answer_contains (result : Result) : (integralBound result.frontier.cells).Contains result.answer :=
  (integralBound result.frontier.cells).midpoint_contains

/-- Any admitted enclosure reading differs from the answer by at most half the retained width. -/
theorem answer_error (result : Result) (reading : Fraction.Rational)
    (inside : (integralBound result.frontier.cells).Contains reading) :
    Fraction.abs (reading - result.answer) ≤ (integralBound result.frontier.cells).width * (1 / 2) :=
  Interval.abs_sub_midpoint_le inside

/-- Independently constructed reciprocal-step answers agree within their two requests.

The actual source-linked frontiers supply a common refinement and matching
rational readings, even when their selected tails and partitions differ. -/
theorem answer_difference_lt (left right : Result) :
    Fraction.abs (left.answer - right.answer) < left.request.tolerance + right.request.tolerance := by
  let common := SourceFrontier.commonReadings left.frontier right.frontier
  have comparison := common.answers_difference_le_of_same left.answer right.answer left.answer_contains
    right.answer_contains (fun _ _ _ => rfl)
  have paid := Fraction.Order.Arithmetic.add_lt_add_direct left.accurate right.accurate
  exact comparison.trans_lt paid

end Result

/-- Compute a complete finite reciprocal-step integration result for one positive request. -/
@[expose] def build (request : AccuracyRequest) : Result :=
  let auxiliary := auxiliaryResult request
  let retained := SourceFrontier.Initial.replace auxiliary.frontier
    (1 / (tailCount request.tolerance : Fraction.Rational)) unitRange (agreement request)
    (fun point _ _ => unitRange_contains point)
  { request := request
    auxiliary := auxiliary
    auxiliary_eq := rfl
    frontier := retained
    frontier_eq := rfl
    accurate := frontier_width_lt request }

/-- Compute the original reciprocal-step result while reusing compatible saved source readings. -/
@[expose] def buildCached (cached : List (SourcePoint value)) (request : AccuracyRequest) : Result := by
  let count := tailCount request.tolerance
  let endpoint := 1 / (count : Fraction.Rational)
  let modulus := truncatedModulus count (tailCount_ge_two request.tolerance)
  let readings := auxiliaryCachedReadingsAt count endpoint rfl cached
  let auxiliary := SourceFrontier.Exceptional.buildCached modulus readings (quarterRequest request)
  let bounded : ∀ point, 0 ≤ point → point ≤ 1 → unitRange.Contains (value point) :=
    fun point _ _ => unitRange_contains point
  let retained := SourceFrontier.Initial.replaceCached cached auxiliary.frontier endpoint unitRange
    (agreement request) bounded
  have auxiliary_eq : auxiliary = auxiliaryResult request :=
    SourceFrontier.Exceptional.buildCached_eq (auxiliaryModulus request)
      (auxiliaryCachedReadings request cached) (quarterRequest request)
  have retained_eq : retained = SourceFrontier.Initial.replace auxiliary.frontier endpoint unitRange
      (agreement request) bounded :=
    SourceFrontier.Initial.replaceCached_eq cached auxiliary.frontier endpoint unitRange (agreement request) bounded
  have accurate : (integralBound retained.cells).width < request.tolerance := by
    rw [retained_eq, auxiliary_eq]
    exact frontier_width_lt request
  exact
    { request := request
      auxiliary := auxiliary
      auxiliary_eq := auxiliary_eq
      frontier := retained
      frontier_eq := retained_eq
      accurate := accurate }

/-- Compatible cache selection preserves the complete original reciprocal-step result. -/
theorem buildCached_eq (cached : List (SourcePoint value)) (request : AccuracyRequest) :
    buildCached cached request = build request := by
  unfold buildCached build
  simp only [SourceFrontier.Exceptional.buildCached_eq, SourceFrontier.Initial.replaceCached_eq]
  rfl

/-- Use the actual finite reciprocal-step construction for persistent integration requests. -/
@[expose] def producer : SourceFrontier.Producer value where
  Output := Result
  request := build
  requestCached := buildCached
  requestCached_eq := buildCached_eq
  frontier := Result.frontier
  accurate := fun request => (build request).accurate

end Purelib.Integration.Step.Reciprocal

end
