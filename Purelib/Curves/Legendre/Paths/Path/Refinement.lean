module

public import Purelib.Curves.Legendre.Paths.Path
public import Purelib.Curves.Legendre.Paths.AxisSegment.Window
public import Purelib.Curves.Legendre.Paths.SafePath
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.ConvexCombination
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

/-!
# Ordered physical refinement of original Legendre axis geometry

Each actual retained path segment traverses an affine restriction of the same
original axis. Consecutive cut parameters are ordered and shared, including
constant owner-comparison pieces. The final empty tail retains the actual
original endpoint parameter rather than introducing a replacement path.
-/

public section

namespace Purelib.Curves.Legendre.Paths.Path

open Purelib.Data.Rat
open Fraction.Order

/-- A point occurs on an actual retained unit segment or the final actual endpoint frame of the original path.

Nonempty membership retains the exact unit parameter and head geometry,
or membership of the original tail. Empty membership uses the original
frame parameter rather than a replacement point or path.
-/
def Visits : {source target : Gaussian} → {left : Frame source} → {right : Frame target} →
    Path left right → Gaussian → Prop
  | source, _, _, _, .nil _, point => point = source
  | _, _, _, _, .cons head tail, point =>
      (∃ parameter : Coordinate, 0 ≤ parameter ∧ parameter ≤ 1 ∧ head.geometry.pointAt parameter = point) ∨
        Visits tail point

namespace Visits

/-- The original empty path visits the actual parameter of its same retained frame. -/
theorem nil {source : Gaussian} (frame : Frame source) {point : Gaussian} (same : point = source) :
    (Path.nil frame).Visits point := same

/-- Read the actual original point equality from membership in an empty prepared path. -/
theorem nil_data {source : Gaussian} {frame : Frame source} {point : Gaussian}
    (visited : (Path.nil frame).Visits point) : point = source := visited

/-- Retain the actual original head and its exact unit parameter as a path-point membership witness. -/
theorem cons_head {source middle target : Gaussian} {left : Frame source} {center : Frame middle} {right : Frame target}
    (head : Segment left center) {tail : Path center right} {point : Gaussian} (parameter : Coordinate)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) (hits : head.geometry.pointAt parameter = point) :
    (Path.cons head tail).Visits point := Or.inl ⟨parameter, inside.1, inside.2, hits⟩

/-- Retain original-tail point membership when prepending the actual original head segment. -/
theorem cons_tail {source middle target : Gaussian} {left : Frame source} {center : Frame middle} {right : Frame target}
    (head : Segment left center) {tail : Path center right} {point : Gaussian} (visited : tail.Visits point) :
    (Path.cons head tail).Visits point := Or.inr visited

/-- Read the actual original head parameter or the retained tail membership from a nonempty prepared path. -/
theorem cons_data {source middle target : Gaussian} {left : Frame source} {center : Frame middle} {right : Frame target}
    {head : Segment left center} {tail : Path center right} {point : Gaussian}
    (visited : (Path.cons head tail).Visits point) :
    (∃ parameter : Coordinate, 0 ≤ parameter ∧ parameter ≤ 1 ∧ head.geometry.pointAt parameter = point) ∨
      tail.Visits point := visited

/-- An original prepared path visits its actual source parameter, including when it has no segments. -/
theorem source {source target : Gaussian} {left : Frame source} {right : Frame target} (path : Path left right) :
    path.Visits source := by
  cases path with
  | nil => exact Visits.nil _ rfl
  | cons head tail => exact cons_head head 0 ⟨by decide, by decide⟩ head.geometry.pointAt_zero

/-- Points of the original left path remain points of its concatenation with the retained right path. -/
theorem append_left {source middle target : Gaussian} {left : Frame source} {center : Frame middle}
    {right : Frame target} {initial : Path left center} (remaining : Path center right) {point : Gaussian}
    (visited : initial.Visits point) : (initial.append remaining).Visits point := by
  induction initial with
  | nil frame =>
      have same := nil_data visited
      rewrite [same]
      exact Visits.source remaining
  | cons head tail inductionHypothesis =>
      rcases cons_data visited with onHead | onTail
      · rcases onHead with ⟨parameter, lower, upper, hits⟩
        exact cons_head head parameter ⟨lower, upper⟩ hits
      · exact cons_tail head (inductionHypothesis remaining onTail)

/-- Points of the original right path remain points of its concatenation after the retained left path. -/
theorem append_right {source middle target : Gaussian} {left : Frame source} {center : Frame middle}
    {right : Frame target} (initial : Path left center) {remaining : Path center right} {point : Gaussian}
    (visited : remaining.Visits point) : (initial.append remaining).Visits point := by
  induction initial with
  | nil frame => exact visited
  | cons head tail inductionHypothesis => exact cons_tail head (inductionHypothesis visited)

/-- Reversal retains every actual unit-segment or final-frame point of the same original path.

An original head witness uses its reflected unit parameter on that same
reversed head. Tail witnesses remain on the actual reversed tail before
the reversed head is appended, including constant and endpoint pieces.
-/
theorem reverse {source target : Gaussian} {left : Frame source} {right : Frame target}
    {path : Path left right} {point : Gaussian} (visited : path.Visits point) : path.reverse.Visits point := by
  induction path with
  | nil frame => exact nil frame (nil_data visited)
  | cons head tail inductionHypothesis =>
      rcases cons_data visited with onHead | onTail
      · rcases onHead with ⟨parameter, lower, upper, hits⟩
        have reflectedLower : (0 : Coordinate) ≤ 1 - parameter :=
          (Arithmetic.sub_le_sub_left_direct upper 1).trans_eq' (by ring1)
        have reflectedUpper : 1 - parameter ≤ (1 : Coordinate) :=
          (Arithmetic.sub_le_sub_left_direct lower 1).trans_eq (by ring1)
        have originalPoint : head.reverse.geometry.pointAt (1 - parameter) = point := by
          rewrite [Segment.reverse_geometry, AxisSegment.pointAt_reverse]
          have reflection : 1 - (1 - parameter) = parameter := by ring1
          rewrite [reflection]
          exact hits
        exact append_right tail.reverse (cons_head head.reverse (1 - parameter)
          ⟨reflectedLower, reflectedUpper⟩ originalPoint)
      · exact append_left (Path.cons head.reverse (Path.nil _)) (inductionHypothesis onTail)

end Visits

/-- The actual original path traverses one original axis interval through ordered affine restrictions.

Each retained head has an explicit next cut between the current and final
cuts, and every head parameter evaluates the same original affine point.
The tail starts at that exact next cut. The empty tail identifies the final
cut and its actual retained frame parameter; zero-length comparisons remain
part of the original path.
-/
def RefinesAxis {originalStart originalFinish : Gaussian} (axis : AxisSegment originalStart originalFinish) :
    {source target : Gaussian} → {left : Frame source} → {right : Frame target} →
      Path left right → Coordinate → Coordinate → Prop
  | source, _, _, _, .nil _, lower, upper => lower = upper ∧ axis.pointAt lower = source
  | _, _, _, _, .cons head tail, lower, upper =>
      ∃ middle : Coordinate, lower ≤ middle ∧ middle ≤ upper ∧
        (∀ parameter : Coordinate, head.geometry.pointAt parameter =
          axis.pointAt (lower + parameter * (middle - lower))) ∧ RefinesAxis axis tail middle upper

namespace RefinesAxis

variable {originalStart originalFinish : Gaussian} (axis : AxisSegment originalStart originalFinish)

/-- Certify the original empty path at an explicitly retained original axis parameter. -/
theorem nil {source : Gaussian} (frame : Frame source) (parameter : Coordinate)
    (same : axis.pointAt parameter = source) : (Path.nil frame).RefinesAxis axis parameter parameter := ⟨rfl, same⟩

/-- Read the actual final cut and original frame parameter from an empty refinement. -/
theorem nil_data {source : Gaussian} {frame : Frame source} {lower upper : Coordinate}
    (refinement : (Path.nil frame).RefinesAxis axis lower upper) :
    lower = upper ∧ axis.pointAt lower = source := refinement

/-- Prepend one actual affine segment to a retained ordered refinement at its same next cut. -/
theorem cons {source middle target : Gaussian} {left : Frame source} {center : Frame middle} {right : Frame target}
    (head : Segment left center) {tail : Path center right} {lower next upper : Coordinate}
    (first : lower ≤ next) (last : next ≤ upper)
    (geometry : ∀ parameter : Coordinate, head.geometry.pointAt parameter =
      axis.pointAt (lower + parameter * (next - lower)))
    (remaining : tail.RefinesAxis axis next upper) : (Path.cons head tail).RefinesAxis axis lower upper :=
  ⟨next, first, last, geometry, remaining⟩

/-- Read the original next cut, ordered bounds, all-parameter geometry and retained tail from a nonempty refinement. -/
theorem cons_data {source middle target : Gaussian} {left : Frame source} {center : Frame middle} {right : Frame target}
    {head : Segment left center} {tail : Path center right} {lower upper : Coordinate}
    (refinement : (Path.cons head tail).RefinesAxis axis lower upper) :
    ∃ next : Coordinate, lower ≤ next ∧ next ≤ upper ∧
      (∀ parameter : Coordinate, head.geometry.pointAt parameter =
        axis.pointAt (lower + parameter * (next - lower))) ∧ tail.RefinesAxis axis next upper := refinement

/-- Every retained original axis refinement has its source cut weakly before its final cut. -/
theorem lower_le_upper {source target : Gaussian} {left : Frame source} {right : Frame target}
    {path : Path left right} {lower upper : Coordinate} (refinement : path.RefinesAxis axis lower upper) :
    lower ≤ upper := by
  cases path with
  | nil frame =>
      have same := (nil_data axis refinement).1
      rewrite [same]
      exact Basic.le_refl _
  | cons head tail =>
      rcases cons_data axis refinement with ⟨next, first, last, _, _⟩
      exact Basic.le_trans _ _ _ first last

/-- Both actual path endpoint indices are the original axis readings at the same retained outer cuts. -/
theorem endpoints {source target : Gaussian} {left : Frame source} {right : Frame target}
    {path : Path left right} {lower upper : Coordinate} (refinement : path.RefinesAxis axis lower upper) :
    axis.pointAt lower = source ∧ axis.pointAt upper = target := by
  induction path generalizing lower with
  | nil frame =>
      have original := nil_data axis refinement
      exact ⟨original.2, (congrArg axis.pointAt original.1).symm.trans original.2⟩
  | cons head tail inductionHypothesis =>
      rcases cons_data axis refinement with ⟨next, _, _, geometry, remaining⟩
      have initial := geometry 0
      rewrite [head.geometry.pointAt_zero] at initial
      have scalar : lower + (0 : Coordinate) * (next - lower) = lower := by ring1
      rewrite [scalar] at initial
      exact ⟨initial.symm, (inductionHypothesis remaining).2⟩

/-- Every original interval point is visited by an actual unit segment or final frame of its refinement.

The original next cut selects the current head or retained tail by exact
comparison. Head membership computes an explicit affine unit parameter
from the same original interval and transports its exact interpolation
identity through the retained head geometry, including constant cuts.
-/
theorem visits {source target : Gaussian} {left : Frame source} {right : Frame target}
    {path : Path left right} {lower upper : Coordinate} (refinement : path.RefinesAxis axis lower upper)
    (parameter : Coordinate) (inside : lower ≤ parameter ∧ parameter ≤ upper) :
    path.Visits (axis.pointAt parameter) := by
  induction path generalizing lower with
  | nil frame =>
      have original := nil_data axis refinement
      have same := Basic.le_antisymm _ _ (inside.2.trans_eq original.1.symm) inside.1
      exact Visits.nil frame ((congrArg axis.pointAt same).trans original.2)
  | cons head tail inductionHypothesis =>
      rcases cons_data axis refinement with ⟨next, _, _, geometry, remaining⟩
      rcases le_total parameter next with before | after
      · have contained := And.intro ((Basic.min_le_left lower next).trans inside.1)
          (before.trans (Basic.le_max_right lower next))
        let unit := Interval.ConvexCombination.segmentParameter lower next parameter
        have bounds := Interval.ConvexCombination.segmentParameter_bounds lower next parameter contained
        have reading := Interval.ConvexCombination.segmentParameter_interpolates lower next parameter contained
        exact Visits.cons_head head unit bounds ((geometry unit).trans (congrArg axis.pointAt reading))
      · exact Visits.cons_tail head (inductionHypothesis remaining ⟨after, inside.2⟩)

/-- Exact frame-parameter transport preserves the same original axis refinement and all retained path segments. -/
theorem castParameters {source target start finish : Gaussian} {left : Frame source} {right : Frame target}
    {path : Path left right} {lower upper : Coordinate} (refinement : path.RefinesAxis axis lower upper)
    (first : source = start) (last : target = finish) :
    (path.castParameters first last).RefinesAxis axis lower upper := by
  subst start
  subst finish
  exact refinement

/-- Exact outer-cut equalities preserve the same original path and its retained refinement. -/
theorem castCuts {source target : Gaussian} {left : Frame source} {right : Frame target}
    {path : Path left right} {lower upper first last : Coordinate} (refinement : path.RefinesAxis axis lower upper)
    (sourceCut : lower = first) (targetCut : upper = last) : path.RefinesAxis axis first last := by
  subst first
  subst last
  exact refinement

/-- A single actual segment traversing the original affine interval gives a complete original axis refinement. -/
theorem single {source target : Gaussian} {left : Frame source} {right : Frame target} {lower upper : Coordinate}
    (head : Segment left right) (ordered : lower ≤ upper)
    (geometry : ∀ parameter : Coordinate, head.geometry.pointAt parameter =
      axis.pointAt (lower + parameter * (upper - lower))) :
    (Path.cons head (Path.nil right)).RefinesAxis axis lower upper := by
  have final := geometry 1
  rewrite [head.geometry.pointAt_one] at final
  have scalar : lower + (1 : Coordinate) * (upper - lower) = upper := by ring1
  rewrite [scalar] at final
  exact cons axis head ordered (Basic.le_refl _) geometry (nil axis right upper final.symm)

/-- Append two actual ordered refinements at their same retained intermediate cut and original frame.

The original path append retains every head. Each left cut stays below the
same right final cut, and the shared intermediate parameter joins the actual
tail to the original right refinement without reconstructing either path.
-/
theorem append {source middle target : Gaussian} {left : Frame source} {center : Frame middle} {right : Frame target}
    {initial : Path left center} {remaining : Path center right} {lower next upper : Coordinate}
    (first : initial.RefinesAxis axis lower next) (last : remaining.RefinesAxis axis next upper) :
    (initial.append remaining).RefinesAxis axis lower upper := by
  induction initial generalizing lower with
  | nil frame =>
      have same := (nil_data axis first).1
      rewrite [same]
      exact last
  | cons head tail inductionHypothesis =>
      rcases cons_data axis first with ⟨cut, before, after, geometry, tailRefinement⟩
      exact cons axis head before (Basic.le_trans _ _ _ after (lower_le_upper axis last)) geometry
        (inductionHypothesis tailRefinement last)

/-- Lift a retained refinement of an original forward restriction to the same original parent axis.

The affine cut map sends each original local cut to the corresponding
parent cut and preserves its order. Every retained head point is transported
through the original restriction equation; the actual path is unchanged.
-/
theorem restrict {source target : Gaussian} {left : Frame source} {right : Frame target}
    {path : Path left right} {first last lower upper : Coordinate} (ordered : first ≤ last)
    (refinement : path.RefinesAxis (axis.restrict first last) lower upper) :
    path.RefinesAxis axis (first + lower * (last - first)) (first + upper * (last - first)) := by
  have nonnegative := Arithmetic.sub_nonneg_direct ordered
  induction path generalizing lower with
  | nil frame =>
      have original := nil_data (axis.restrict first last) refinement
      have same := original.1
      subst lower
      exact nil axis frame _ ((axis.restrict_pointAt first last upper).symm.trans original.2)
  | cons head tail inductionHypothesis =>
      rcases cons_data (axis.restrict first last) refinement with ⟨next, before, after, geometry, remaining⟩
      have firstBound := Arithmetic.add_le_add_direct (Basic.le_refl first)
        (Arithmetic.mul_le_mul_of_nonneg_right_direct before nonnegative)
      have lastBound := Arithmetic.add_le_add_direct (Basic.le_refl first)
        (Arithmetic.mul_le_mul_of_nonneg_right_direct after nonnegative)
      apply cons axis head firstBound lastBound
      · intro parameter
        calc
          head.geometry.pointAt parameter =
              (axis.restrict first last).pointAt (lower + parameter * (next - lower)) := geometry parameter
          _ = axis.pointAt (first + (lower + parameter * (next - lower)) * (last - first)) :=
            axis.restrict_pointAt first last _
          _ = axis.pointAt ((first + lower * (last - first)) +
              parameter * ((first + next * (last - first)) - (first + lower * (last - first)))) :=
            congrArg axis.pointAt (by ring1)
      · exact inductionHypothesis remaining

/-- A complete local-unit refinement traverses the exact original parent interval of its forward restriction. -/
theorem restrict_unit {source target : Gaussian} {left : Frame source} {right : Frame target}
    {path : Path left right} {first last : Coordinate} (ordered : first ≤ last)
    (refinement : path.RefinesAxis (axis.restrict first last) 0 1) : path.RefinesAxis axis first last :=
  (restrict axis ordered refinement).castCuts axis (by ring1) (by ring1)

/-- Reversing an actual refinement traverses the reversed original axis with its reflected cuts.

Every retained head is reversed in place and appended after the reversed
tail. The cut map sends the original interval to its oppositely traversed
interval on the original reversed axis, preserving all affine point readings
and the actual source and target frames.
-/
theorem reverse {source target : Gaussian} {left : Frame source} {right : Frame target}
    {path : Path left right} {lower upper : Coordinate} (refinement : path.RefinesAxis axis lower upper) :
    path.reverse.RefinesAxis axis.reverse (1 - upper) (1 - lower) := by
  induction path generalizing lower with
  | nil frame =>
      have original := nil_data axis refinement
      have cuts := original.1
      subst upper
      apply nil axis.reverse frame (1 - lower)
      calc
        axis.reverse.pointAt (1 - lower) = axis.pointAt (1 - (1 - lower)) := axis.pointAt_reverse _
        _ = axis.pointAt lower := congrArg axis.pointAt (by ring1)
        _ = _ := original.2
  | cons head tail inductionHypothesis =>
      rcases cons_data axis refinement with ⟨next, before, _, geometry, remaining⟩
      have reversedTail := inductionHypothesis remaining
      have reversedHead : (Path.cons head.reverse (Path.nil _)).RefinesAxis axis.reverse
          (1 - next) (1 - lower) := by
        apply single axis.reverse head.reverse (Arithmetic.sub_le_sub_left_direct before 1)
        intro parameter
        rewrite [Segment.reverse_geometry, AxisSegment.pointAt_reverse, geometry (1 - parameter),
          AxisSegment.pointAt_reverse]
        exact congrArg axis.pointAt (by ring1)
      exact reversedTail.append axis.reverse reversedHead

/-- Reversing a complete original-axis refinement retains the whole reversed original unit interval. -/
theorem reverse_unit {source target : Gaussian} {left : Frame source} {right : Frame target}
    {path : Path left right} (refinement : path.RefinesAxis axis 0 1) :
    path.reverse.RefinesAxis axis.reverse 0 1 :=
  (reverse axis refinement).castCuts axis.reverse (by ring1) (by ring1)

end RefinesAxis

/-- The original joined-segment fold refines its same parent axis through the actual ordered piece and join cuts.

Each supplied segment and comparison has an all-parameter readback to its
original affine interval. Ordered piece and join bounds keep every next cut
before the same actual final cut. Structural recursion consumes the original
frame and segment families without reconstructing their data.
-/
theorem ofJoinedSegments_refinesAxis {originalStart originalFinish : Gaussian}
    (axis : AxisSegment originalStart originalFinish) :
    (size : Nat) → (lower upper : Fin (size + 1) → Coordinate) →
    (left : (index : Fin (size + 1)) → Frame (axis.pointAt (lower index))) →
    (right : (index : Fin (size + 1)) → Frame (axis.pointAt (upper index))) →
    (pieces : (index : Fin (size + 1)) → Segment (left index) (right index)) →
    (joins : (index : Fin size) → Segment (right index.castSucc) (left index.succ)) →
    (∀ index : Fin (size + 1), lower index ≤ upper index) →
    (∀ index : Fin (size + 1), upper index ≤ upper ⟨size, Nat.lt_succ_self size⟩) →
    (∀ index : Fin size, upper index.castSucc ≤ lower index.succ) →
    (∀ index : Fin (size + 1), ∀ parameter : Coordinate, (pieces index).geometry.pointAt parameter =
      axis.pointAt (lower index + parameter * (upper index - lower index))) →
    (∀ index : Fin size, ∀ parameter : Coordinate, (joins index).geometry.pointAt parameter =
      axis.pointAt (upper index.castSucc + parameter * (lower index.succ - upper index.castSucc))) →
    (ofJoinedSegments size (fun index => axis.pointAt (lower index)) (fun index => axis.pointAt (upper index))
      left right pieces joins).RefinesAxis axis (lower 0) (upper ⟨size, Nat.lt_succ_self size⟩)
  | 0, _, _, _, _, pieces, _, ordered, _, _, geometry, _ =>
      RefinesAxis.single axis (pieces 0) (ordered 0) (geometry 0)
  | size + 1, lower, upper, left, right, pieces, joins, ordered, bounded, joinOrdered, geometry, joinGeometry => by
      apply RefinesAxis.cons axis (pieces 0) (ordered 0) (bounded 0) (geometry 0)
      apply RefinesAxis.cons axis (joins 0) (joinOrdered 0)
        (Basic.le_trans _ _ _ (ordered (0 : Fin (size + 1)).succ) (bounded (0 : Fin (size + 1)).succ))
        (joinGeometry 0)
      exact ofJoinedSegments_refinesAxis axis size (fun index => lower index.succ) (fun index => upper index.succ)
        (fun index => left index.succ) (fun index => right index.succ)
        (fun index => pieces index.succ) (fun index => joins index.succ)
        (fun index => ordered index.succ) (fun index => bounded index.succ)
        (fun index => joinOrdered index.succ) (fun index => geometry index.succ)
        (fun index => joinGeometry index.succ)

/-- The actual prepared path retains one ordered axis refinement for each original safe-path head in traversal order.

Every original head splits the same prepared path at an actual frame of its
original target fibre. The retained prefix refines that complete original
axis, while the remainder refines the same original safe tail. Empty input
has no prepared segments. No braid equality replaces the physical relation.
-/
def RefinesSafePath : {start finish : Gaussian} → SafePath start finish →
    {left : Frame start} → {right : Frame finish} → Path left right → Prop
  | _, _, .nil _, _, _, prepared => prepared.stepCount = 0
  | _, _, .cons (middle := middle) segment _ tail, left, right, prepared =>
      ∃ center : Frame middle, ∃ initial : Path left center, ∃ remaining : Path center right,
        prepared = initial.append remaining ∧ initial.RefinesAxis segment 0 1 ∧ RefinesSafePath tail remaining

namespace RefinesSafePath

/-- The original empty prepared path refines the same original empty geometric path. -/
theorem nil {start : Gaussian} (frame : Frame start) : (Path.nil frame).RefinesSafePath (SafePath.nil start) := by
  change (Path.nil frame).stepCount = 0
  rfl

/-- An empty original safe-path refinement contains no actual prepared segments. -/
theorem nil_data {start : Gaussian} {left right : Frame start} {prepared : Path left right}
    (refinement : prepared.RefinesSafePath (SafePath.nil start)) : prepared.stepCount = 0 := refinement

/-- Retain an actual complete original-head refinement followed by the refinement of its same original safe tail. -/
theorem cons {start middle finish : Gaussian} (segment : AxisSegment start middle) (safe : AxisSegment.Safe segment)
    {tail : SafePath middle finish} {left : Frame start} {center : Frame middle} {right : Frame finish}
    {initial : Path left center} {remaining : Path center right}
    (first : initial.RefinesAxis segment 0 1) (last : remaining.RefinesSafePath tail) :
    (initial.append remaining).RefinesSafePath (SafePath.cons segment safe tail) :=
  ⟨center, initial, remaining, rfl, first, last⟩

/-- Read the same actual prepared split, its original complete head refinement and the retained safe-tail refinement. -/
theorem cons_data {start middle finish : Gaussian} {segment : AxisSegment start middle}
    {safe : AxisSegment.Safe segment} {tail : SafePath middle finish} {left : Frame start} {right : Frame finish}
    {prepared : Path left right} (refinement : prepared.RefinesSafePath (SafePath.cons segment safe tail)) :
    ∃ center : Frame middle, ∃ initial : Path left center, ∃ remaining : Path center right,
      prepared = initial.append remaining ∧ initial.RefinesAxis segment 0 1 ∧ remaining.RefinesSafePath tail :=
  refinement

/-- Concatenating actual prepared refinements retains the concatenation of their same original geometric paths.

The retained head split is preserved while its actual remaining refinement
is concatenated with the original right preparation. Empty original input
has no prepared segments, so the same original right path is returned.
-/
theorem append {start middle finish : Gaussian} {firstOriginal : SafePath start middle}
    {lastOriginal : SafePath middle finish} {left : Frame start} {center : Frame middle} {right : Frame finish}
    {initial : Path left center} {remaining : Path center right}
    (first : initial.RefinesSafePath firstOriginal) (last : remaining.RefinesSafePath lastOriginal) :
    (initial.append remaining).RefinesSafePath (firstOriginal.append lastOriginal) := by
  induction firstOriginal with
  | nil point =>
      have count := nil_data first
      cases initial with
      | nil => exact last
      | cons head tail => exact False.elim (Nat.noConfusion count)
  | cons segment safe tail inductionHypothesis =>
      rcases cons_data first with ⟨middleFrame, initialPart, remainingPart, readback, headRefinement, tailRefinement⟩
      rewrite [readback, Path.append_assoc]
      exact cons segment safe headRefinement (inductionHypothesis tailRefinement last)

/-- Reversal preserves physical refinement of the same original finite safe path.

Each original retained head split is reversed with its original endpoint
frames and appended after the reversed tail. The proof retains the complete
original reversed geometry and safety data, including stationary comparison
segments, rather than using a braid-word identity as a physical certificate.
-/
theorem reverse {start finish : Gaussian} {original : SafePath start finish}
    {left : Frame start} {right : Frame finish} {prepared : Path left right}
    (refinement : prepared.RefinesSafePath original) : prepared.reverse.RefinesSafePath original.reverse := by
  induction original with
  | nil point =>
      have count := nil_data refinement
      cases prepared with
      | nil => exact nil _
      | cons head tail => exact False.elim (Nat.noConfusion count)
  | cons segment safe tail inductionHypothesis =>
      rcases cons_data refinement with ⟨center, initial, remaining, readback, first, last⟩
      rewrite [readback, Path.reverse_append]
      have reversedHead : initial.reverse.RefinesSafePath
          (SafePath.cons segment.reverse safe.reverse (SafePath.nil _)) := by
        have retained := cons segment.reverse safe.reverse (first.reverse_unit segment) (nil _)
        rewrite [Path.append_nil] at retained
        exact retained
      exact (inductionHypothesis last).append reversedHead

/-- Every point of the same original finite safe path occurs on the actual retained prepared path.

The original head parameter selects its point in the retained axis
refinement. Original-tail membership is transported through the actual
remaining refinement and the same path append; an empty original path
visits its own original fibre parameter.
-/
theorem visits {start finish : Gaussian} {original : SafePath start finish} {left : Frame start} {right : Frame finish}
    {prepared : Path left right} (refinement : prepared.RefinesSafePath original) {point : Gaussian}
    (visited : original.Visits point) : prepared.Visits point := by
  induction original with
  | nil parameter =>
      have same := SafePath.Visits.nil_data visited
      rewrite [same]
      exact Visits.source prepared
  | cons segment safe tail inductionHypothesis =>
      rcases cons_data refinement with ⟨center, initial, remaining, readback, first, last⟩
      rewrite [readback]
      rcases SafePath.Visits.cons_data visited with onHead | onTail
      · rcases onHead with ⟨parameter, lower, upper, hits⟩
        have originalPoint := first.visits segment parameter ⟨lower, upper⟩
        rewrite [hits] at originalPoint
        exact Visits.append_left remaining originalPoint
      · exact Visits.append_right initial (inductionHypothesis last onTail)

end RefinesSafePath

end Purelib.Curves.Legendre.Paths.Path
