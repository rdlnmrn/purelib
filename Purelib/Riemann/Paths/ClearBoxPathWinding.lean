module
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Polynomial.Clearance.Box.Region

public import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.PreparedPathClosure
import Purelib.Polynomial.Geometry.RegionWinding
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Path independence inside a cleared rectangle

The two-axis route defines an integer winding potential. Every contained
axis segment has the corresponding potential difference, so arbitrary finite
clear paths telescope. Their original ambient boxes may differ: containment
is checked in the common cleared face, not inferred from the path's ambient.
-/

namespace Purelib.Riemann.Paths.ClearBoxPathWinding.ClearBoxPaths

open Purelib.Data.Int

open Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides (horizontalEdge verticalEdge)

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {box :
  Purelib.Geometry.Rational.Box}

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- The original horizontal-then-vertical doubled winding from the box's lower-left anchor to the point. -/
@[expose] def windingPotential (polynomial : Geometry.ClearPath.GaussianPolynomial) (box : Box) (point :
  Basic.Canonical) : Int :=
  (Path.Box.Sides.horizontalEdge polynomial box.yLower box.xLower point.re).doubledWinding +
    (Path.Box.Sides.verticalEdge polynomial point.re box.yLower point.im).doubledWinding

section
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
/-- Consecutive original horizontal doubled windings add to their combined interval winding. -/
private theorem horizontal_add (polynomial : Geometry.ClearPath.GaussianPolynomial) (y a b c : Fraction.Rational) :
    (Path.Box.Sides.horizontalEdge polynomial y a b).doubledWinding + (Path.Box.Sides.horizontalEdge polynomial y b
      c).doubledWinding =
      (Path.Box.Sides.horizontalEdge polynomial y a c).doubledWinding :=
        (Dense.Rational.CauchyIndex.Basic.cauchyIndex2_add _ _ _ _ _).symm

/-- Consecutive original vertical doubled windings add to their combined interval winding. -/
private theorem vertical_add (polynomial : Geometry.ClearPath.GaussianPolynomial) (x a b c : Fraction.Rational) :
    (Path.Box.Sides.verticalEdge polynomial x a b).doubledWinding + (Path.Box.Sides.verticalEdge polynomial x b
      c).doubledWinding =
      (Path.Box.Sides.verticalEdge polynomial x a c).doubledWinding :=
        (Dense.Rational.CauchyIndex.Basic.cauchyIndex2_add _ _ _ _ _).symm

/-- Reversing the original horizontal interval negates its doubled winding. -/
private theorem horizontal_reverse (polynomial : Geometry.ClearPath.GaussianPolynomial) (y a b : Fraction.Rational) :
    (Path.Box.Sides.horizontalEdge polynomial y b a).doubledWinding = -(Path.Box.Sides.horizontalEdge polynomial y a
      b).doubledWinding :=
  Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse _ _ _ _

/-- Reversing the original vertical interval negates its doubled winding. -/
private theorem vertical_reverse (polynomial : Geometry.ClearPath.GaussianPolynomial) (x a b : Fraction.Rational) :
    (Path.Box.Sides.verticalEdge polynomial x b a).doubledWinding = -(Path.Box.Sides.verticalEdge polynomial x a
      b).doubledWinding :=
  Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse _ _ _ _

/-- The original zero-length horizontal interval has zero doubled winding.

The coincident endpoints give the same retained Cauchy-index reading.
Their displayed difference vanishes by integer additive cancellation. -/
private theorem horizontal_self (polynomial : Geometry.ClearPath.GaussianPolynomial) (y a : Fraction.Rational) :
    (Path.Box.Sides.horizontalEdge polynomial y a a).doubledWinding = 0 := Arithmetic.sub_eq_zero_of_eq rfl

/-- The original zero-length vertical interval has zero doubled winding.

The coincident endpoints give the same retained Cauchy-index reading.
Their displayed difference vanishes by integer additive cancellation. -/
private theorem vertical_self (polynomial : Geometry.ClearPath.GaussianPolynomial) (x a : Fraction.Rational) :
    (Path.Box.Sides.verticalEdge polynomial x a a).doubledWinding = 0 := Arithmetic.sub_eq_zero_of_eq rfl

end

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Clearance.Box in
open Purelib.Polynomial.Dense.Gaussian in
/-- A possibly degenerate subrectangle of the cleared original box has zero signed boundary winding.

The original polynomial has positive degree, and the retained endpoint bounds place the entire rectangle within the same
clearance box. -/
private theorem rectangle_zero (clearance : Region.RegionClearance polynomial box)
    (degreePositive : 0 < polynomial.natDegree) {a b y : Fraction.Rational}
    (first : box.xLower ≤ a) (ordered : a ≤ b) (last : b ≤ box.xUpper)
    (height : box.yLower ≤ y) (top : y ≤ box.yUpper) :
    (Path.Box.Sides.horizontalEdge polynomial box.yLower a b).doubledWinding +
      (Path.Box.Sides.verticalEdge polynomial b box.yLower y).doubledWinding -
      (Path.Box.Sides.horizontalEdge polynomial y a b).doubledWinding -
      (Path.Box.Sides.verticalEdge polynomial a box.yLower y).doubledWinding = 0 := by
  by_cases width : a < b
  · by_cases strictHeight : box.yLower < y
    · let inner : Box := ⟨a, b, box.yLower, y, width.le, strictHeight.le⟩
      have refines : inner.Refines box := ⟨first, last, le_rfl, top⟩
      have zero := (clearance.restrict refines).winding_zero degreePositive ⟨width, strictHeight⟩
      rw [Winding.Box.Basic.quadrupledBoxWinding_eq] at zero
      change (Path.Box.Sides.horizontalEdge polynomial box.yLower a b).doubledWinding +
        (Path.Box.Sides.verticalEdge polynomial b box.yLower y).doubledWinding +
        (Path.Box.Sides.horizontalEdge polynomial y b a).doubledWinding +
        (Path.Box.Sides.verticalEdge polynomial a y box.yLower).doubledWinding = 0 at zero
      rw [horizontal_reverse polynomial y a b, vertical_reverse polynomial a box.yLower y] at zero
      omega
    · have equal : y = box.yLower :=
        le_antisymm (Fraction.Order.Arithmetic.le_of_not_gt_direct strictHeight) height
      subst y
      rw [vertical_self, vertical_self]
      omega
  · have equal : b = a := le_antisymm (Fraction.Order.Arithmetic.le_of_not_gt_direct width) ordered
    subst b
    rw [horizontal_self, horizontal_self]
    omega

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial.Clearance.Box in
open Purelib.Polynomial.Dense.Gaussian in
/-- A contained horizontal segment's original doubled winding is the difference of its endpoint potentials. -/
theorem horizontal_winding (clearance : Region.RegionClearance polynomial box)
    (degreePositive : 0 < polynomial.natDegree) {a b y : Fraction.Rational}
    (first : box.Contains (Components.Basic.point a y)) (last : box.Contains (Components.Basic.point b y)) :
    (Path.Box.Sides.horizontalEdge polynomial y a b).doubledWinding =
      windingPotential polynomial box (Components.Basic.point b y) - windingPotential polynomial box
        (Components.Basic.point a y) := by
  have add := horizontal_add polynomial box.yLower box.xLower a b
  change _ = ((Path.Box.Sides.horizontalEdge polynomial box.yLower box.xLower b).doubledWinding +
    (Path.Box.Sides.verticalEdge polynomial b box.yLower y).doubledWinding) -
    ((Path.Box.Sides.horizontalEdge polynomial box.yLower box.xLower a).doubledWinding +
      (Path.Box.Sides.verticalEdge polynomial a box.yLower y).doubledWinding)
  rcases le_total a b with ordered | ordered
  · have zero := rectangle_zero clearance degreePositive (a := a) (b := b) (y := y)
      first.1 ordered last.2.1 first.2.2.1 first.2.2.2
    omega
  · have zero := rectangle_zero clearance degreePositive (a := b) (b := a) (y := y)
      last.1 ordered first.2.1 first.2.2.1 first.2.2.2
    rw [horizontal_reverse polynomial box.yLower a b, horizontal_reverse polynomial y a b] at zero
    omega

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- A vertical segment's original doubled winding is the difference of its endpoint potentials. -/
theorem vertical_winding (polynomial : Geometry.ClearPath.GaussianPolynomial) (box : Box) (x a b :
  Fraction.Rational) :
    (Path.Box.Sides.verticalEdge polynomial x a b).doubledWinding =
      windingPotential polynomial box (Components.Basic.point x b) - windingPotential polynomial box
        (Components.Basic.point x a) := by
  have add := vertical_add polynomial x box.yLower a b
  unfold windingPotential
  change _ = ((Path.Box.Sides.horizontalEdge polynomial box.yLower box.xLower x).doubledWinding +
    (Path.Box.Sides.verticalEdge polynomial x box.yLower b).doubledWinding) -
    ((Path.Box.Sides.horizontalEdge polynomial box.yLower box.xLower x).doubledWinding +
      (Path.Box.Sides.verticalEdge polynomial x box.yLower a).doubledWinding)
  omega

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Clearance.Box in
open Purelib.Riemann.Paths in
/-- An original cleared coordinate segment in the cleared box has winding equal to its endpoint potential difference. -/
theorem segment_winding (clearance : Region.RegionClearance polynomial box)
    (degreePositive : 0 < polynomial.natDegree) {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (first : box.Contains start) (last :
      box.Contains finish) :
    PreparedPathWinding.ClearSegment.rawWinding segment = windingPotential polynomial box finish - windingPotential
      polynomial box start := by
  rw [PreparedPathWinding.ClearSegment.rawWinding_eq_coordinateWinding segment]
  cases segment with
  | horizontal => exact horizontal_winding clearance degreePositive first last
  | vertical => exact vertical_winding polynomial box _ _ _

end Purelib.Riemann.Paths.ClearBoxPathWinding.ClearBoxPaths

namespace Purelib

open Purelib.Data.Int

open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Paths.ClearBoxPathWinding.ClearBoxPaths (windingPotential)

variable {polynomial : GaussianPolynomial} {ambient box :
  Box}

namespace Polynomial.Geometry.ClearPath

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- Every retained vertex of the original cleared path belongs to the given box. -/
@[expose] def InBox (box : Box) : {start finish :
  Basic.Canonical} → ClearPath polynomial ambient start finish → Prop
  | _, _, .nil point => box.Contains point
  | start, _, .cons _ tail => box.Contains start ∧ InBox box tail

end Polynomial.Geometry.ClearPath

open _root_.Purelib.Polynomial.Geometry.ClearPath (InBox)

namespace Polynomial.Geometry.ClearPath.InBox

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- An original path retained inside a box starts inside that same box. -/
theorem start {start finish : Basic.Canonical} {path :
  ClearPath polynomial ambient start finish}
    (inside : InBox box path) : box.Contains start := by
  cases path with
  | nil => exact inside
  | cons => exact inside.1

end Polynomial.Geometry.ClearPath.InBox

namespace Polynomial.Geometry.ClearPath.InBox

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- Transport original path-vertex containment along the retained box refinement. -/
theorem mono {larger : Box} (refines :
  box.Refines larger) :
    ∀ {start finish : Basic.Canonical} {path : ClearPath polynomial ambient start finish},
      InBox box path → InBox larger path
  | _, _, .nil _, inside => refines.contains inside
  | _, _, .cons _ _, inside => ⟨refines.contains inside.1, mono
    refines inside.2⟩

end Polynomial.Geometry.ClearPath.InBox

namespace Polynomial.Geometry.ClearPath.InBox

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- An original ambient-contained path with a contained start has every retained vertex inside its ambient box. -/
theorem ofWithin : ∀ {start finish : Basic.Canonical} (path
  : ClearPath polynomial ambient start finish),
    path.WithinAmbient → ambient.Contains start → InBox ambient path
  | _, _, .nil _, _, inside => inside
  | _, _, .cons head tail, within, inside => by
      have last := head.pointAt_contains within.head 1 (by decide)
      rw [Geometry.ClearPath.ClearSegment.pointAt_one] at last
      exact ⟨inside, ofWithin tail within.tail last⟩

end Polynomial.Geometry.ClearPath.InBox

namespace Riemann.Paths.ClearBoxPathWinding.ClearPath

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Clearance.Box in
open Purelib.Riemann.Paths in
/-- The original path winding inside a cleared box telescopes to its endpoint potential difference.

The positive-degree polynomial retains the same box clearance, and every original path vertex satisfies that box's
containment condition. -/
theorem rawWinding_eq_potential (clearance : Region.RegionClearance polynomial box)
    (degreePositive : 0 < polynomial.natDegree) :
    ∀ {start finish : Basic.Canonical} (path : Polynomial.Geometry.ClearPath polynomial ambient start finish),
      Polynomial.Geometry.ClearPath.InBox box path →
      PreparedPathWinding.ClearPath.rawWinding path = ClearBoxPaths.windingPotential polynomial box finish -
        ClearBoxPaths.windingPotential polynomial box start
  | _, _, .nil _, _ => by
      rw [Int.sub_eq_add_neg, Arithmetic.add_comm, Arithmetic.neg_add_cancel]
      rfl
  | _, _, .cons head tail, inside => by
      change PreparedPathWinding.ClearSegment.rawWinding head + PreparedPathWinding.ClearPath.rawWinding tail = _
      rw [ClearBoxPaths.segment_winding clearance degreePositive head inside.1 inside.2.start,
        rawWinding_eq_potential clearance degreePositive tail inside.2]
      omega

end Riemann.Paths.ClearBoxPathWinding.ClearPath

namespace Riemann.Paths.ClearBoxPathWinding.ClearPath

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Clearance.Box in
open Purelib.Riemann.Paths in
/-- Original paths with the same endpoints inside one cleared box have equal raw winding. -/
theorem rawWinding_eq_of_inBox (clearance : Region.RegionClearance polynomial box)
    (degreePositive : 0 < polynomial.natDegree) {otherAmbient : Box} {start finish : Basic.Canonical}
    (first : Polynomial.Geometry.ClearPath polynomial ambient start finish) (second : Polynomial.Geometry.ClearPath
      polynomial otherAmbient start finish)
    (firstInside : Polynomial.Geometry.ClearPath.InBox box first) (secondInside : Polynomial.Geometry.ClearPath.InBox
      box
      second) : PreparedPathWinding.ClearPath.rawWinding first = PreparedPathWinding.ClearPath.rawWinding second := by
  rw [rawWinding_eq_potential clearance degreePositive first firstInside,
    rawWinding_eq_potential clearance degreePositive second secondInside]

end Riemann.Paths.ClearBoxPathWinding.ClearPath

namespace Riemann.Paths.ClearBoxPathWinding.ClearPath

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Clearance.Box in
open Purelib.Riemann.Paths in
/-- An original closed path inside the cleared box has zero raw winding.

The path retains its original polynomial and a containment certificate in
the cleared box. Its endpoint potential readings coincide, so their integer
difference vanishes. -/
theorem rawWinding_zero_of_inBox (clearance : Region.RegionClearance polynomial box)
    (degreePositive : 0 < polynomial.natDegree) {base : Basic.Canonical}
    (path : Polynomial.Geometry.ClearPath polynomial ambient base base) (inside : Polynomial.Geometry.ClearPath.InBox
      box
      path) : PreparedPathWinding.ClearPath.rawWinding path = 0 := by
  rw [rawWinding_eq_potential clearance degreePositive path inside, Int.sub_eq_add_neg,
    Arithmetic.add_comm, Arithmetic.neg_add_cancel]

end Riemann.Paths.ClearBoxPathWinding.ClearPath

end Purelib

namespace Purelib.Riemann.Paths.ClearBoxPathWinding.Route

open Purelib.Riemann.Paths.ClearBoxPaths (Route)

open Purelib.Riemann.Paths.ClearBoxPathWinding.ClearBoxPaths (windingPotential)

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Clearance.Box in
open Purelib.Riemann.Paths in
/-- The original box route's raw winding equals the potential difference of its retained endpoints. -/
theorem winding {polynomial : Geometry.ClearPath.GaussianPolynomial} {box : Box} {start finish :
  Basic.Canonical}
    (clearance : Region.RegionClearance polynomial box) (degreePositive : 0 < polynomial.natDegree)
    (route : Route polynomial box start finish) (first : box.Contains start) :
    PreparedPathWinding.ClearPath.rawWinding route.path = windingPotential polynomial box finish - windingPotential
      polynomial box start :=
  ClearBoxPathWinding.ClearPath.rawWinding_eq_potential clearance degreePositive route.path
    (Polynomial.Geometry.ClearPath.InBox.ofWithin route.path route.within first)

end Purelib.Riemann.Paths.ClearBoxPathWinding.Route
