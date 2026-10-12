module

import Purelib.Data.List.Filter
import Purelib.Data.List.Map
import Purelib.Data.List.Membership

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Bisection
import Purelib.Polynomial.Clearance.Pair.Cover.Basic
import Purelib.Polynomial.Clearance.Pair.Cover.Leaf
import Purelib.Polynomial.Clearance.Pair.Cover.Prepare
public import Purelib.Polynomial.Clearance.Pair.Cover.Retained
import Purelib.Polynomial.Dense.Rational.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Polynomial.Clearance.Pair.Cover.Leaf (Source)
open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

/-!
# Certified accounts of inconclusive finite clearance attempts

The report records the actual retained leaves and exactly those whose computed
floor is nonpositive.  The retained run equation links their depth to the
finite budget.  It certifies failure of this attempt to establish separation,
not a zero of the polynomial or failure of every possible method.
-/

namespace Purelib.Polynomial

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Geometry.Rational

namespace Geometry.PolynomialClearanceCover

set_option genInjectivity false in
/-- An original retained clearance leaf paired with its interval and actual refinement depth.

The retained source index links each cached leaf to the same original coordinate tables. Its displayed interval and
depth describe that actual leaf in the refinement tree. -/
public structure Snapshot {realPolynomial imagPolynomial : CoordinatePolynomial} (source
  : Source realPolynomial imagPolynomial) where
  /-- The original parameter interval of this retained leaf. -/ parameters : Data.Rat.Interval.Bounds
  /-- The leaf's recorded depth in the finite refinement tree. -/ depth : Nat
  /-- The actual cached leaf indexed by the original source and retained interval. -/ data :
    Clearance.Pair.Cover.Leaf source parameters

constructive_injectivity Snapshot

end Geometry.PolynomialClearanceCover

namespace Clearance.Pair.Cover

-- The existing public tree API retains Cover.Basic.Cover in its nominal name.

variable {realPolynomial imagPolynomial : CoordinatePolynomial} {source :
  Source realPolynomial imagPolynomial}

/-- The exact retained leaf data, in left-to-right order, with their depth.
No coefficient evaluation, root preparation or refinement is repeated.

A leaf contributes its cached data, indexed interval and current depth once. A split concatenates left then right
snapshots with the same successor depth. -/
@[expose] public def snapshots : {parameters :
  Data.Rat.Interval.Bounds} → {normFloor coordinateFloor : Fraction.Rational} →
    Cover source parameters normFloor coordinateFloor → Nat → List
      (_root_.Purelib.Polynomial.Geometry.PolynomialClearanceCover.Snapshot source)
  | parameters, _, _, .leaf data, depth => [⟨parameters, depth, data⟩]
  | _, _, _, .split _ left right, depth => left.snapshots (depth + 1) ++ right.snapshots (depth + 1)

/-- Reading the intervals of retained leaf snapshots gives exactly the original ordered cover regions.

The interval projection consumes the same ordered snapshot tree. Structural induction preserves each leaf and
concatenates both child readbacks. -/
public theorem snapshots_regions {parameters :
  Data.Rat.Interval.Bounds} {normFloor coordinateFloor : Fraction.Rational}
    (cover : Cover source parameters normFloor coordinateFloor) (depth : Nat) :
    (cover.snapshots depth).map (·.parameters) = cover.regions := by
  induction cover generalizing depth with
  | leaf data => rfl
  | split baseline left right leftEqual rightEqual =>
      change (left.snapshots (depth + 1) ++ right.snapshots (depth + 1)).map _ = left.regions ++ right.regions
      rw [Data.List.Map.map_append, leftEqual, rightEqual]

/-- A nonpositive aggregate cover floor has a retained leaf with nonpositive floor.

A nonpositive split floor bounds the smaller child floor by zero. The retained rational comparison selects a child with
an explicit failed snapshot witness. -/
public theorem exists_failed {parameters :
  Data.Rat.Interval.Bounds} {normFloor coordinateFloor : Fraction.Rational}
    (cover : Cover source parameters normFloor coordinateFloor) (depth : Nat) (nonpositive :
      normFloor ≤ 0) :
    ∃ snapshot, snapshot ∈ cover.snapshots depth ∧ snapshot.data.normFloor ≤ 0 := by
  induction cover generalizing depth with
  | leaf data => exact ⟨⟨_, depth, data⟩, List.mem_cons_self, nonpositive⟩
  | @split parameters baseline leftNorm leftCoordinate rightNorm rightCoordinate left right leftFailed rightFailed =>
      have minimum : min leftNorm rightNorm ≤ 0 := (Fraction.Order.Basic.le_max_right _ _).trans nonpositive
      by_cases ordered : leftNorm ≤ rightNorm
      · change (if leftNorm ≤ rightNorm then leftNorm else rightNorm) ≤ 0 at minimum
        rw [if_pos ordered] at minimum
        obtain ⟨snapshot, member, failed⟩ := leftFailed (depth + 1) minimum
        exact ⟨snapshot, Data.List.Membership.mem_append.mpr (Or.inl member), failed⟩
      · change (if leftNorm ≤ rightNorm then leftNorm else rightNorm) ≤ 0 at minimum
        rw [if_neg ordered] at minimum
        obtain ⟨snapshot, member, failed⟩ := rightFailed (depth + 1) minimum
        exact ⟨snapshot, Data.List.Membership.mem_append.mpr (Or.inr member), failed⟩

end Clearance.Pair.Cover

namespace Geometry.PolynomialClearanceCover

/-- Every nonpositive leaf retained by bounded refinement lies at the initial depth plus the full attempted budget.

A positive leaf cannot satisfy the supplied failed-floor certificate. Every remaining successor-depth branch consumes
one budget unit and adds one to the actual retained depth. -/
public theorem refine_failed_depth {realPolynomial imagPolynomial :
  CoordinatePolynomial}
    {source : Source realPolynomial imagPolynomial} {parameters :
      Data.Rat.Interval.Bounds}
    (leaf : Clearance.Pair.Cover.Leaf source parameters) (budget depth : Nat) (snapshot : Snapshot source)
    (member : snapshot ∈ (Clearance.Pair.Cover.Prepare.refine leaf budget).cover.snapshots depth)
    (failed : snapshot.data.normFloor ≤ 0) : snapshot.depth = depth + budget := by
  induction budget generalizing parameters depth leaf with
  | zero =>
      have equal : snapshot = ⟨parameters, depth, leaf⟩ := Data.List.Membership.mem_singleton.mp member
      cases equal
      rfl
  | succ budget inductionHypothesis =>
      dsimp only [Clearance.Pair.Cover.Prepare.refine] at member
      by_cases positive : 0 < leaf.normFloor
      · rw [if_pos positive] at member
        have equal : snapshot = ⟨parameters, depth, leaf⟩ := Data.List.Membership.mem_singleton.mp member
        cases equal
        exact (not_lt_of_ge failed positive).elim
      · rw [if_neg positive] at member
        rcases Data.List.Membership.mem_append.mp member with leftMember | rightMember
        · have equal := inductionHypothesis (Clearance.Pair.Cover.Leaf.prepare source
            (Data.Rat.Interval.Bisection.leftHalf parameters)) (depth + 1) leftMember
          omega
        · have equal := inductionHypothesis (Clearance.Pair.Cover.Leaf.prepare source
            (Data.Rat.Interval.Bisection.rightHalf parameters)) (depth + 1) rightMember
          omega

end Geometry.PolynomialClearanceCover

namespace Geometry.PolynomialClearanceCover

set_option genInjectivity false in
/-- A stopped finite run, with an exact cached failure list.  Every reported
leaf is certified nonpositive, and every such leaf from the run is listed.

The record retains the actual finite attempt, its complete snapshot list and exactly the nonpositive-floor filter. Exact
equalities link both cached lists to that same run. -/
public structure Inconclusive (realPolynomial imagPolynomial : CoordinatePolynomial)
  (parameters : Data.Rat.Interval.Bounds) where
  /-- The original retained bounded clearance attempt. -/ attempted : Clearance.Pair.Cover.Retained
    realPolynomial imagPolynomial parameters
  /-- The attempt's computed aggregate norm floor is nonpositive. -/ nonpositive : attempted.result.normFloor ≤ 0
  /-- The cached complete leaf snapshot list of the attempted run. -/ leaves : List (Snapshot attempted.source)
  /-- The cached list is exactly the run's retained cover snapshots from depth zero. -/ leaves_eq : leaves =
    attempted.result.cover.snapshots 0
  /-- The cached list of precisely those retained leaves whose norm floor is nonpositive. -/ unresolved : List (Snapshot
    attempted.source)
  /-- The unresolved list is exactly the rational nonpositivity filter of the retained leaf list. -/ unresolved_eq :
    unresolved = leaves.filter (fun snapshot => decide (snapshot.data.normFloor ≤ 0))

constructive_injectivity Inconclusive

end Geometry.PolynomialClearanceCover

namespace Geometry.PolynomialClearanceCover.Inconclusive

variable {realPolynomial imagPolynomial : CoordinatePolynomial} {parameters :
  Data.Rat.Interval.Bounds}

/-- Package a nonpositive retained attempt with its exact leaf and unresolved-leaf lists, reusing the original cover.

The retained tree is read once into snapshots. Filtering those same snapshots records every failed leaf while preserving
source indices and occurrence order. -/
@[expose] public def ofAttempt (attempted : Clearance.Pair.Cover.Retained realPolynomial imagPolynomial
  parameters)
    (nonpositive : attempted.result.normFloor ≤ 0) : Inconclusive realPolynomial imagPolynomial parameters :=
  let leaves := attempted.result.cover.snapshots 0
  { attempted, nonpositive, leaves, leaves_eq := rfl
    unresolved := leaves.filter (fun snapshot => decide (snapshot.data.normFloor ≤ 0))
    unresolved_eq := rfl }

/-- A snapshot is reported unresolved exactly when it is a retained leaf with nonpositive norm floor.

The retained list equality identifies the actual nonpositivity filter. Structural filter membership supplies both the
original snapshot occurrence and its exact failed-floor certificate. -/
public theorem unresolved_iff (report : Inconclusive realPolynomial imagPolynomial parameters)
    (snapshot : Snapshot report.attempted.source) :
    snapshot ∈ report.unresolved ↔ snapshot ∈ report.leaves ∧ snapshot.data.normFloor ≤ 0 := by
  rw [report.unresolved_eq]
  constructor
  · intro member
    have retained := (Data.List.Filter.mem_filter.mp member)
    exact ⟨retained.1, of_decide_eq_true retained.2⟩
  · intro member
    exact Data.List.Filter.mem_filter.mpr ⟨member.1, decide_eq_true member.2⟩

/-- Every unresolved reported leaf reached the original attempt's full refinement depth budget.

An unresolved member is a retained failed leaf of the exact attempted tree. The refinement depth certificate identifies
its displayed depth with the attempted budget. -/
public theorem failed_at_budget (report : Inconclusive realPolynomial imagPolynomial parameters)
    (snapshot : Snapshot report.attempted.source) (member : snapshot ∈ report.unresolved) :
    snapshot.depth = report.attempted.budget := by
  obtain ⟨retained, failed⟩ := (report.unresolved_iff snapshot).mp member
  rw [report.leaves_eq, report.attempted.result_eq] at retained
  simpa only [Nat.zero_add] using
    refine_failed_depth report.attempted.initial report.attempted.budget 0 snapshot retained failed

/-- An unresolved leaf's floor is nonpositive and remains a valid quadrance lower bound throughout its original
interval.

The filter supplies the nonpositive-floor certificate. The same cached leaf still bounds quadrance throughout its
retained interval. -/
public theorem failed_bound_sound (report : Inconclusive realPolynomial imagPolynomial parameters)
    (snapshot : Snapshot report.attempted.source) (member : snapshot ∈ report.unresolved)
    {parameter : Fraction.Rational} (inside : snapshot.parameters.Contains parameter) :
    snapshot.data.normFloor ≤ 0 ∧
      snapshot.data.normFloor ≤ realPolynomial.eval parameter ^ 2 + imagPolynomial.eval parameter ^ 2 :=
  ⟨((report.unresolved_iff snapshot).mp member).2, snapshot.data.normFloor_le inside⟩

/-- A certified inconclusive attempt retains at least one unresolved leaf.

The nonpositive aggregate floor supplies an explicit failed snapshot. Exact filter membership places that same witness
in the cached unresolved list. -/
public theorem unresolved_nonempty (report : Inconclusive realPolynomial imagPolynomial parameters) :
    report.unresolved ≠ [] := by
  intro empty
  obtain ⟨snapshot, retained, failed⟩ := report.attempted.result.cover.exists_failed 0 report.nonpositive
  have member : snapshot ∈ report.leaves := by
    rw [report.leaves_eq]
    exact retained
  have reported := (report.unresolved_iff snapshot).mpr ⟨member, failed⟩
  rw [empty] at reported
  exact List.not_mem_nil reported

end Geometry.PolynomialClearanceCover.Inconclusive

end Purelib.Polynomial
