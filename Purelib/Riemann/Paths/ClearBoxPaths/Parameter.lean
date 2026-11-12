module

public import Purelib.Riemann.Paths.ClearBoxPaths
public import Purelib.Geometry.Rational.Affine.Segment
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Data.Rat.Interval.ConvexCombination
import Purelib.Geometry.Rational.Affine.Segment.Convex
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-! # The actual unit-parameter points of a retained short clear Route

The original path's zero, one or two ordered edge occurrences determine its
unit parameter. A two-edge route assigns its first and second half intervals
to those exact retained edges. Convex interpolation from the endpoint chord
to that literal route stays in the original cleared box and fixes endpoints.
-/

public section

namespace Purelib.Riemann.Paths.ClearBoxPaths.Route

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Rational
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)

variable {polynomial : ClearPath.GaussianPolynomial} {box : Box}

/-- Read one original path with its retained at-most-two-edge certificate. -/
private def pointOn : {start finish : Canonical} → (path : ClearPath polynomial box start finish) →
    path.segmentCount ≤ 2 → Fraction.Rational → Canonical
  | _, _, .nil point, _ => fun _ => point
  | _, _, .cons head tail, short =>
      match tail with
      | .nil _ => fun time => head.pointAt time
      | .cons second remaining =>
          match remaining with
          | .nil _ => fun time =>
              if time ≤ (1 / 2 : Fraction.Rational) then head.pointAt (2 * time)
              else second.pointAt (2 * time - 1)
          | .cons _ rest => False.elim (by
              change Nat.succ (Nat.succ (Nat.succ rest.segmentCount)) ≤ 2 at short
              omega0)

/-- Read the SAME retained Route at a rational unit parameter without reconstructing any edge.

An empty route is constant. A one-edge route uses the original edge's whole
unit interval. Two original edges occupy respectively the first and second
half, retaining their order and orientation and their common original corner.
-/
def pointAt {start finish : Canonical} (route : Route polynomial box start finish)
    (time : Fraction.Rational) : Canonical := pointOn route.path route.short time

/-- An actual empty Route reads its original point at every parameter. -/
theorem pointAt_nil {point : Canonical} (route : Route polynomial box point point)
    (path_eq : route.path = .nil point) (time : Fraction.Rational) : route.pointAt time = point := by
  cases route with
  | mk path within short =>
      cases path_eq
      unfold pointAt pointOn
      rfl

/-- A one-edge Route reads the SAME actual retained edge at its unchanged unit parameter. -/
theorem pointAt_single {start finish : Canonical} (route : Route polynomial box start finish)
    (edge : ClearSegment polynomial box start finish) (path_eq : route.path = .cons edge (.nil finish))
    (time : Fraction.Rational) : route.pointAt time = edge.pointAt time := by
  cases route with
  | mk path within short =>
      cases path_eq
      unfold pointAt pointOn
      rfl

/-- The first half of a two-edge Route reads its SAME original first edge with the positive doubled parameter. -/
theorem pointAt_first {start middle finish : Canonical} (route : Route polynomial box start finish)
    (first : ClearSegment polynomial box start middle) (second : ClearSegment polynomial box middle finish)
    (path_eq : route.path = .cons first (.cons second (.nil finish)))
    {time : Fraction.Rational} (before : time ≤ 1 / 2) : route.pointAt time = first.pointAt (2 * time) := by
  cases route with
  | mk path within short =>
      cases path_eq
      unfold pointAt pointOn
      change (if time ≤ (1 / 2 : Fraction.Rational) then first.pointAt (2 * time)
        else second.pointAt (2 * time - 1)) = _
      rewrite [if_pos before]
      rfl

/-- The second half of a two-edge Route reads its SAME original second edge with the positive doubled parameter. -/
theorem pointAt_second {start middle finish : Canonical} (route : Route polynomial box start finish)
    (first : ClearSegment polynomial box start middle) (second : ClearSegment polynomial box middle finish)
    (path_eq : route.path = .cons first (.cons second (.nil finish)))
    {time : Fraction.Rational} (after : ¬time ≤ 1 / 2) : route.pointAt time = second.pointAt (2 * time - 1) := by
  cases route with
  | mk path within short =>
      cases path_eq
      unfold pointAt pointOn
      change (if time ≤ (1 / 2 : Fraction.Rational) then first.pointAt (2 * time)
        else second.pointAt (2 * time - 1)) = _
      rewrite [if_neg after]
      rfl

/-- The SAME two retained edges meet at their exact original corner at the shared half parameter. -/
theorem pointAt_half {start middle finish : Canonical} (route : Route polynomial box start finish)
    (first : ClearSegment polynomial box start middle) (second : ClearSegment polynomial box middle finish)
    (path_eq : route.path = .cons first (.cons second (.nil finish))) :
    route.pointAt (1 / 2) = middle := by
  rewrite [route.pointAt_first first second path_eq (Fraction.Order.Basic.le_refl _),
    show (2 * (1 / 2) : Fraction.Rational) = 1 from of_decide_eq_true rfl]
  exact first.pointAt_one

/-- Unit times on the first half give unit times on the original first edge. -/
theorem first_time_inside {time : Fraction.Rational} (inside : 0 ≤ time ∧ time ≤ 1)
    (before : time ≤ 1 / 2) : 0 ≤ 2 * time ∧ 2 * time ≤ 1 := by
  constructor
  · exact Arithmetic.mul_nonneg_direct (of_decide_eq_true rfl) inside.1
  · have bound := Arithmetic.mul_le_mul_of_nonneg_left_direct before
      (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 2)
    exact bound.trans_eq (of_decide_eq_true rfl)

/-- Unit times on the second half give unit times on the original second edge. -/
theorem second_time_inside {time : Fraction.Rational} (inside : 0 ≤ time ∧ time ≤ 1)
    (after : ¬time ≤ 1 / 2) : 0 ≤ 2 * time - 1 ∧ 2 * time - 1 ≤ 1 := by
  have lower := (Arithmetic.lt_of_not_ge_direct after).le
  have doubled := Arithmetic.mul_le_mul_of_nonneg_left_direct lower
    (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 2)
  have upper := Arithmetic.mul_le_mul_of_nonneg_left_direct inside.2
    (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 2)
  constructor
  · apply Arithmetic.sub_nonneg_direct
    exact (of_decide_eq_true rfl : (2 * (1 / 2) : Fraction.Rational) = 1) ▸ doubled
  · have translated := Arithmetic.sub_le_sub_direct upper (Fraction.Order.Basic.le_refl 1)
    exact translated.trans_eq (of_decide_eq_true rfl)

/-- The original Route parameter begins at its SAME source coordinate. -/
theorem pointAt_zero {start finish : Canonical} (route : Route polynomial box start finish) :
    route.pointAt 0 = start := by
  cases route with
  | mk path within short =>
      cases path with
      | nil point => unfold pointAt pointOn; rfl
      | cons head tail =>
          cases tail with
          | nil finish => unfold pointAt pointOn; exact head.pointAt_zero
          | cons second remaining =>
              cases remaining with
              | nil finish =>
                  unfold pointAt pointOn
                  change (if (0 : Fraction.Rational) ≤ 1 / 2 then head.pointAt (2 * 0)
                    else second.pointAt (2 * 0 - 1)) = _
                  rewrite [if_pos (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 1 / 2),
                    show (2 * 0 : Fraction.Rational) = 0 by ring1]
                  exact head.pointAt_zero
              | cons third rest =>
                  change Nat.succ (Nat.succ (Nat.succ rest.segmentCount)) ≤ 2 at short
                  omega0

/-- The original Route parameter finishes at its SAME target coordinate. -/
theorem pointAt_one {start finish : Canonical} (route : Route polynomial box start finish) :
    route.pointAt 1 = finish := by
  cases route with
  | mk path within short =>
      cases path with
      | nil point => unfold pointAt pointOn; rfl
      | cons head tail =>
          cases tail with
          | nil finish => unfold pointAt pointOn; exact head.pointAt_one
          | cons second remaining =>
              cases remaining with
              | nil finish =>
                  unfold pointAt pointOn
                  change (if (1 : Fraction.Rational) ≤ 1 / 2 then head.pointAt (2 * 1)
                    else second.pointAt (2 * 1 - 1)) = _
                  rewrite [if_neg (of_decide_eq_true rfl : ¬(1 : Fraction.Rational) ≤ 1 / 2),
                    show (2 * 1 - 1 : Fraction.Rational) = 1 by ring1]
                  exact second.pointAt_one
              | cons third rest =>
                  change Nat.succ (Nat.succ (Nat.succ rest.segmentCount)) ≤ 2 at short
                  omega0

/-- Every original in-box Route parameter remains in the SAME box, including a stationary empty Route. -/
theorem pointAt_contains {start finish : Canonical} (route : Route polynomial box start finish)
    (sourceInside : box.Contains start) {time : Fraction.Rational} (inside : 0 ≤ time ∧ time ≤ 1) :
    box.Contains (route.pointAt time) := by
  cases route with
  | mk path within short =>
      cases path with
      | nil point => unfold pointAt pointOn; exact sourceInside
      | cons head tail =>
          cases tail with
          | nil finish => unfold pointAt pointOn; exact head.pointAt_contains within.head time inside
          | cons second remaining =>
              cases remaining with
              | nil finish =>
                  unfold pointAt pointOn
                  change box.Contains (if time ≤ (1 / 2 : Fraction.Rational) then head.pointAt (2 * time)
                    else second.pointAt (2 * time - 1))
                  by_cases before : time ≤ 1 / 2
                  · rewrite [if_pos before]
                    exact head.pointAt_contains within.head _ (first_time_inside inside before)
                  · rewrite [if_neg before]
                    exact second.pointAt_contains within.tail.head _ (second_time_inside inside before)
              | cons third rest =>
                  change Nat.succ (Nat.succ (Nat.succ rest.segmentCount)) ≤ 2 at short
                  omega0

/-- The original Route's endpoint chord uses its unchanged source and target with their positive unit parameter. -/
@[expose] def chord {start finish : Canonical} (_route : Route polynomial box start finish)
    (time : Fraction.Rational) : Canonical := Affine.line start (finish - start) time

/-- The displayed chord-to-Route deformation uses the SAME actual ordered edge parameterization. -/
@[expose] def deformation {start finish : Canonical} (route : Route polynomial box start finish)
    (time blend : Fraction.Rational) : Canonical :=
  Affine.line (route.chord time) (route.pointAt time - route.chord time) blend

/-- Zero blend gives the actual original endpoint chord rather than a stored axis route edge. -/
theorem deformation_chord {start finish : Canonical} (route : Route polynomial box start finish)
    (time : Fraction.Rational) : route.deformation time 0 = route.chord time := Affine.line_zero _ _

/-- Unit blend gives the literal actual Route point with its original ordered edge occurrence. -/
theorem deformation_route {start finish : Canonical} (route : Route polynomial box start finish)
    (time : Fraction.Rational) : route.deformation time 1 = route.pointAt time := Affine.line_one _ _

/-- The chord-to-Route deformation fixes the SAME source at every blend. -/
theorem deformation_zero {start finish : Canonical} (route : Route polynomial box start finish)
    (blend : Fraction.Rational) : route.deformation 0 blend = start := by
  unfold deformation chord
  rewrite [Affine.line_zero, route.pointAt_zero]
  exact Affine.Segment.line_self _ _

/-- The chord-to-Route deformation fixes the SAME target at every blend. -/
theorem deformation_one {start finish : Canonical} (route : Route polynomial box start finish)
    (blend : Fraction.Rational) : route.deformation 1 blend = finish := by
  unfold deformation chord
  rewrite [Affine.line_one, route.pointAt_one]
  exact Affine.Segment.line_self _ _

/-- The entire literal chord-to-Route deformation remains in the SAME retained clear box. -/
theorem deformation_contains {start finish : Canonical} (route : Route polynomial box start finish)
    (sourceInside : box.Contains start) (targetInside : box.Contains finish)
    {time blend : Fraction.Rational} (timeInside : 0 ≤ time ∧ time ≤ 1) (blendInside : 0 ≤ blend ∧ blend ≤ 1) :
    box.Contains (route.deformation time blend) :=
  Box.contains_line (Box.contains_line sourceInside targetInside timeInside)
    (route.pointAt_contains sourceInside timeInside) blendInside

/-- Original full-box clearance pays every point of the actual chord-to-Route deformation. -/
theorem deformation_lower {start finish : Canonical} (route : Route polynomial box start finish)
    (clearance : Polynomial.Clearance.Box.Region.RegionClearance polynomial box)
    (sourceInside : box.Contains start) (targetInside : box.Contains finish)
    {time blend : Fraction.Rational} (timeInside : 0 ≤ time ∧ time ≤ 1) (blendInside : 0 ≤ blend ∧ blend ≤ 1) :
    clearance.bound ≤ Norm.Basic.normSq (polynomial.eval (route.deformation time blend)) :=
  clearance.lower _ (route.deformation_contains sourceInside targetInside timeInside blendInside)

/-- An empty original Route gives a constant chord-to-Route deformation without introducing an edge. -/
theorem deformation_nil {point : Canonical} (route : Route polynomial box point point)
    (path_eq : route.path = .nil point) (time blend : Fraction.Rational) :
    route.deformation time blend = point := by
  unfold deformation chord
  rewrite [Affine.Segment.line_self, route.pointAt_nil path_eq time]
  exact Affine.Segment.line_self _ _

/-- The SAME retained region-clearance certificate proves nonvanishing throughout the actual chord-to-Route fan. -/
theorem deformation_nonroot {start finish : Canonical} (route : Route polynomial box start finish)
    (clearance : Polynomial.Clearance.Box.Region.RegionClearance polynomial box)
    (sourceInside : box.Contains start) (targetInside : box.Contains finish)
    {time blend : Fraction.Rational} (timeInside : 0 ≤ time ∧ time ≤ 1) (blendInside : 0 ≤ blend ∧ blend ≤ 1) :
    polynomial.eval (route.deformation time blend) ≠ 0 :=
  clearance.eval_ne_zero (route.deformation_contains sourceInside targetInside timeInside blendInside)

/-- A local original edge uses the retained chord interval and its SAME oriented edge parameter. -/
@[expose] def edgeDeformation {start finish edgeStart edgeFinish : Canonical}
    (route : Route polynomial box start finish) (edge : ClearSegment polynomial box edgeStart edgeFinish)
    (left right time blend : Fraction.Rational) : Canonical :=
  let chord := route.chord (left + time * (right - left))
  Affine.line chord (edge.pointAt time - chord) blend

/-- Zero blend of a local actual edge reads its exact original chord interval. -/
theorem edgeDeformation_chord {start finish edgeStart edgeFinish : Canonical}
    (route : Route polynomial box start finish) (edge : ClearSegment polynomial box edgeStart edgeFinish)
    (left right time : Fraction.Rational) :
    route.edgeDeformation edge left right time 0 = route.chord (left + time * (right - left)) :=
  Affine.line_zero _ _

/-- Unit blend of a local actual edge reads the SAME original physical edge at its unchanged unit parameter. -/
theorem edgeDeformation_edge {start finish edgeStart edgeFinish : Canonical}
    (route : Route polynomial box start finish) (edge : ClearSegment polynomial box edgeStart edgeFinish)
    (left right time : Fraction.Rational) :
    route.edgeDeformation edge left right time 1 = edge.pointAt time := Affine.line_one _ _

/-- The local ruled edge begins at the actual chord/edge pair with their original left indices. -/
theorem edgeDeformation_zero {start finish edgeStart edgeFinish : Canonical}
    (route : Route polynomial box start finish) (edge : ClearSegment polynomial box edgeStart edgeFinish)
    (left right blend : Fraction.Rational) :
    route.edgeDeformation edge left right 0 blend =
      Affine.line (route.chord left) (edgeStart - route.chord left) blend := by
  unfold edgeDeformation
  rewrite [show left + 0 * (right - left) = left by ring1, edge.pointAt_zero]
  rfl

/-- The local ruled edge finishes at the actual chord/edge pair with their original right indices. -/
theorem edgeDeformation_one {start finish edgeStart edgeFinish : Canonical}
    (route : Route polynomial box start finish) (edge : ClearSegment polynomial box edgeStart edgeFinish)
    (left right blend : Fraction.Rational) :
    route.edgeDeformation edge left right 1 blend =
      Affine.line (route.chord right) (edgeFinish - route.chord right) blend := by
  unfold edgeDeformation
  rewrite [show left + 1 * (right - left) = right by ring1, edge.pointAt_one]
  rfl

/-- Every local ruled edge lies in the SAME box when its actual edge and retained chord times lie there. -/
theorem edgeDeformation_contains {start finish edgeStart edgeFinish : Canonical}
    (route : Route polynomial box start finish) (edge : ClearSegment polynomial box edgeStart edgeFinish)
    (within : edge.WithinAmbient) (sourceInside : box.Contains start) (targetInside : box.Contains finish)
    {left right time blend : Fraction.Rational}
    (leftInside : 0 ≤ left ∧ left ≤ 1) (rightInside : 0 ≤ right ∧ right ≤ 1)
    (timeInside : 0 ≤ time ∧ time ≤ 1) (blendInside : 0 ≤ blend ∧ blend ≤ 1) :
    box.Contains (route.edgeDeformation edge left right time blend) :=
  Box.contains_line (Box.contains_line sourceInside targetInside
    (Box.coordinate_between leftInside rightInside timeInside))
    (edge.pointAt_contains within time timeInside) blendInside

/-- The exact squared-distance scale of an actual affine ruled edge retains its chord and edge increments separately. -/
@[expose] def edgeScale {start finish edgeStart edgeFinish : Canonical}
    (_route : Route polynomial box start finish) (_edge : ClearSegment polynomial box edgeStart edgeFinish)
    (left right blend : Fraction.Rational) : Fraction.Rational :=
  (1 - blend) * (Norm.Basic.normSq (finish - start) * (right - left) ^ 2) +
    blend * Norm.Basic.normSq (edgeFinish - edgeStart)

/-- The actual ruled-edge squared-distance scale is nonnegative at every retained unit blend. -/
theorem edgeScale_nonnegative {start finish edgeStart edgeFinish : Canonical}
    (route : Route polynomial box start finish) (edge : ClearSegment polynomial box edgeStart edgeFinish)
    (left right : Fraction.Rational) {blend : Fraction.Rational} (inside : 0 ≤ blend ∧ blend ≤ 1) :
    0 ≤ route.edgeScale edge left right blend :=
by
  have firstPaid := Arithmetic.mul_nonneg_direct
    (Arithmetic.sub_nonneg_direct inside.2)
    (Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg (finish - start))
      (Arithmetic.sq_nonneg_direct (right - left)))
  have secondPaid := Arithmetic.mul_nonneg_direct inside.1
    (Norm.Basic.normSq_nonneg (edgeFinish - edgeStart))
  have total := Arithmetic.add_le_add_direct firstPaid secondPaid
  exact (show (0 : Fraction.Rational) = 0 + 0 by ring1).trans_le total

/-- The actual local chord-to-edge deformation has an internally derived horizontal squared-distance bound. -/
theorem edgeDeformation_distance {start finish edgeStart edgeFinish : Canonical}
    (route : Route polynomial box start finish) (edge : ClearSegment polynomial box edgeStart edgeFinish)
    (left right : Fraction.Rational) {blend : Fraction.Rational} (inside : 0 ≤ blend ∧ blend ≤ 1)
    (first last : Fraction.Rational) :
    Norm.Basic.normSq (route.edgeDeformation edge left right first blend -
      route.edgeDeformation edge left right last blend) ≤
        route.edgeScale edge left right blend * (last - first) ^ 2 := by
  have convex := Affine.Segment.normSq_line_difference_le
    (route.chord (left + first * (right - left))) (edge.pointAt first)
    (route.chord (left + last * (right - left))) (edge.pointAt last) inside
  have chordDistance :
      Norm.Basic.normSq (route.chord (left + first * (right - left)) -
        route.chord (left + last * (right - left))) =
      (Norm.Basic.normSq (finish - start) * (right - left) ^ 2) * (last - first) ^ 2 := by
    unfold chord
    rewrite [Affine.normSq_line_sub]
    ring1
  rewrite [chordDistance, edge.normSq_pointAt_sub_pointAt] at convex
  exact convex.trans_eq (by unfold edgeScale; ring1)

/-- The single retained edge's local fan is literally the SAME chord-to-Route deformation. -/
theorem deformation_single {start finish : Canonical} (route : Route polynomial box start finish)
    (edge : ClearSegment polynomial box start finish) (path_eq : route.path = .cons edge (.nil finish))
    (time blend : Fraction.Rational) :
    route.edgeDeformation edge 0 1 time blend = route.deformation time blend := by
  unfold edgeDeformation deformation
  rewrite [show (0 + time * (1 - 0) : Fraction.Rational) = time by ring1,
    route.pointAt_single edge path_eq]
  rfl

/-- The two actual local fans have the SAME full physical point at their retained common corner for every blend. -/
theorem edgeDeformation_join {start finish edgeStart middle edgeFinish : Canonical}
    (route : Route polynomial box start finish)
    (first : ClearSegment polynomial box edgeStart middle) (second : ClearSegment polynomial box middle edgeFinish)
    (blend : Fraction.Rational) :
    route.edgeDeformation first 0 (1 / 2) 1 blend = route.edgeDeformation second (1 / 2) 1 0 blend := by
  rewrite [route.edgeDeformation_one, route.edgeDeformation_zero]
  rfl

/-- The first local fan is the literal first-half restriction of the SAME retained two-edge Route deformation. -/
theorem deformation_first {start middle finish : Canonical} (route : Route polynomial box start finish)
    (first : ClearSegment polynomial box start middle) (second : ClearSegment polynomial box middle finish)
    (path_eq : route.path = .cons first (.cons second (.nil finish)))
    {time : Fraction.Rational} (inside : 0 ≤ time ∧ time ≤ 1) (blend : Fraction.Rational) :
    route.edgeDeformation first 0 (1 / 2) time blend =
      route.deformation (0 + time * (1 / 2 - 0)) blend := by
  have before : 0 + time * (1 / 2 - 0) ≤ (1 / 2 : Fraction.Rational) := by
    have bound := Arithmetic.mul_le_mul_of_nonneg_left_direct inside.2
      (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 1 / 2)
    exact (show (0 + time * (1 / 2 - 0) : Fraction.Rational) = (1 / 2) * time by ring1).trans_le
      (bound.trans_eq (by ring1))
  have twice : (2 * (1 / 2) : Fraction.Rational) = 1 := of_decide_eq_true rfl
  have parameter : (2 * (0 + time * (1 / 2 - 0)) : Fraction.Rational) = time := by
    calc
      _ = (2 * (1 / 2)) * time := by ring1
      _ = time := by rewrite [twice]; exact Fraction.Field.one_mul _
  unfold edgeDeformation deformation
  rewrite [route.pointAt_first first second path_eq before, parameter]
  rfl

/-- The second local fan is the literal second-half restriction, including the SAME original corner at time zero. -/
theorem deformation_second {start middle finish : Canonical} (route : Route polynomial box start finish)
    (first : ClearSegment polynomial box start middle) (second : ClearSegment polynomial box middle finish)
    (path_eq : route.path = .cons first (.cons second (.nil finish)))
    {time : Fraction.Rational} (inside : 0 ≤ time ∧ time ≤ 1) (blend : Fraction.Rational) :
    route.edgeDeformation second (1 / 2) 1 time blend =
      route.deformation (1 / 2 + time * (1 - 1 / 2)) blend := by
  have point : route.pointAt (1 / 2 + time * (1 - 1 / 2)) = second.pointAt time := by
    by_cases stationary : time = 0
    · rewrite [stationary, show (1 / 2 + 0 * (1 - 1 / 2) : Fraction.Rational) = 1 / 2 by ring1,
        route.pointAt_half first second path_eq, second.pointAt_zero]
      rfl
    · have strict : (0 : Fraction.Rational) < time :=
        ⟨inside.1, fun reverse => stationary (Fraction.Order.Basic.le_antisymm _ _ reverse inside.1)⟩
      have shifted := Arithmetic.add_lt_add_left_direct
        (Arithmetic.mul_pos_direct
          (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1 / 2) strict) (1 / 2)
      rewrite [show (1 / 2 + 0 : Fraction.Rational) = 1 / 2 by ring1] at shifted
      have normalized : (1 / 2 + time * (1 - 1 / 2) : Fraction.Rational) = 1 / 2 + (1 / 2) * time := by
        rewrite [show (1 - 1 / 2 : Fraction.Rational) = 1 / 2 from of_decide_eq_true rfl]
        ring1
      have after : ¬(1 / 2 + time * (1 - 1 / 2) : Fraction.Rational) ≤ 1 / 2 := by
        rewrite [normalized]
        intro bound
        exact shifted.2 bound
      have twice : (2 * (1 / 2) : Fraction.Rational) = 1 := of_decide_eq_true rfl
      have parameter : (2 * (1 / 2 + time * (1 - 1 / 2)) - 1 : Fraction.Rational) = time := by
        rewrite [show (1 - 1 / 2 : Fraction.Rational) = 1 / 2 from of_decide_eq_true rfl]
        calc
          _ = (2 * (1 / 2) - 1) + (2 * (1 / 2)) * time := by ring1
          _ = time := by rewrite [twice]; ring1
      exact (route.pointAt_second first second path_eq after).trans (congrArg second.pointAt parameter)
  unfold edgeDeformation deformation
  rewrite [point]
  rfl

/-- The original x-first connector remains on the source horizontal or target vertical line at every parameter.

This reads the literal zero, one or two stored edge occurrences of build.
It needs no unit-interval restriction; each original affine leg retains its
fixed coordinate even outside that interval.
-/
theorem build_pointAt_axes (clearance : Polynomial.Clearance.Box.Region.RegionClearance polynomial box)
    (start finish : Canonical) (first : box.Contains start) (last : box.Contains finish)
    (time : Fraction.Rational) :
    ((build clearance start finish first last).pointAt time).im = start.im ∨
      ((build clearance start finish first last).pointAt time).re = finish.re := by
  unfold build
  split
  next same =>
    cases same
    exact Or.inl rfl
  next different =>
    dsimp only
    split
    next sameHeight =>
      apply Or.inl
      change start.im + time * (finish.im - start.im) = start.im
      rewrite [sameHeight]
      ring1
    next differentHeight =>
      split
      next sameWidth =>
        apply Or.inr
        change start.re + time * (finish.re - start.re) = finish.re
        rewrite [sameWidth]
        ring1
      next differentWidth =>
        by_cases before : time ≤ 1 / 2
        · apply Or.inl
          dsimp only [pointAt, pointOn]
          rewrite [if_pos before]
          change start.im + (2 * time) * (start.im - start.im) = start.im
          ring1
        · apply Or.inr
          dsimp only [pointAt, pointOn]
          rewrite [if_neg before]
          change finish.re + (2 * time - 1) * (finish.re - finish.re) = finish.re
          ring1

/-- Equal endpoint heights make every original connector point retain that height, including the nil case. -/
theorem build_pointAt_horizontal (clearance : Polynomial.Clearance.Box.Region.RegionClearance polynomial box)
    (start finish : Canonical) (first : box.Contains start) (last : box.Contains finish)
    (sameHeight : start.im = finish.im) (time : Fraction.Rational) :
    ((build clearance start finish first last).pointAt time).im = start.im := by
  unfold build
  split
  next same =>
    cases same
    rfl
  next different =>
    dsimp only
    rewrite [dif_pos sameHeight]
    change start.im + time * (finish.im - start.im) = start.im
    rewrite [sameHeight]
    ring1

/-- Equal endpoint widths make every original connector point retain that width, including the nil case. -/
theorem build_pointAt_vertical (clearance : Polynomial.Clearance.Box.Region.RegionClearance polynomial box)
    (start finish : Canonical) (first : box.Contains start) (last : box.Contains finish)
    (sameWidth : start.re = finish.re) (time : Fraction.Rational) :
    ((build clearance start finish first last).pointAt time).re = start.re := by
  unfold build
  split
  next same =>
    cases same
    rfl
  next different =>
    dsimp only
    split
    next sameHeight =>
      change start.re + time * (finish.re - start.re) = start.re
      rewrite [sameWidth]
      ring1
    next differentHeight =>
      change start.re + time * (finish.re - start.re) = start.re
      rewrite [sameWidth]
      ring1

end Purelib.Riemann.Paths.ClearBoxPaths.Route
