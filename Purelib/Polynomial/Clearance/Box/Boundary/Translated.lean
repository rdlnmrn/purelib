module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Square.Centered
public import Purelib.Geometry.Rational.Box.Outside
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
public import Purelib.Polynomial.Dense.Gaussian.Roots.Linear.Evaluation
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order
open Purelib.Polynomial.Dense.Gaussian.Linear
open Purelib.Data.Gaussian.Basic

/-!
# Translated-coordinate boundary clearance

The displayed centred and separated boxes retain quantitative norm-square
clearance for the original translated-coordinate and linear-factor programs.
-/

namespace Purelib.Polynomial.Clearance.Box.Boundary.Translated

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial

/-- The translated coordinate has clearance equal to radius squared on its positive centered square.

The supplied positive radius defines the same centred square and
the exact cached bound is its square. On each retained boundary side,
one translated coordinate has that square and the other adds nonnegatively. -/
@[expose] public def translatedCoordinate_boundaryClearance
    (c : Canonical) {r : Fraction.Rational} (positive : 0 < r) :
    Basic.BoundaryClearance
      (Translated.translatedCoordinate c) (Box.Square.Centered.Affine.centeredSquare c r
        positive.le) where
  bound := r ^ 2
  positive := Arithmetic.pow_pos_direct positive 2
  lower := by
    intro z boundary
    rw [Translated.translatedCoordinate_eval]
    rw [Canonical.normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
    simp only [← pow_two]
    rcases boundary.2 with left | right | bottom | top
    · change z.re = c.re - r at left
      rw [left]
      have first : (c.re - r - c.re) ^ 2 = r ^ 2 := by ring1
      rw [first]
      exact le_add_of_nonneg_right
        (Arithmetic.sq_nonneg_direct _)
    · change z.re = c.re + r at right
      rw [right]
      have first : (c.re + r - c.re) ^ 2 = r ^ 2 := by ring1
      rw [first]
      exact le_add_of_nonneg_right
        (Arithmetic.sq_nonneg_direct _)
    · change z.im = c.im - r at bottom
      rw [bottom]
      have second : (c.im - r - c.im) ^ 2 = r ^ 2 := by ring1
      rw [second]
      exact le_add_of_nonneg_left
        (Arithmetic.sq_nonneg_direct _)
    · change z.im = c.im + r at top
      rw [top]
      have second : (c.im + r - c.im) ^ 2 = r ^ 2 := by ring1
      rw [second]
      exact le_add_of_nonneg_left
        (Arithmetic.sq_nonneg_direct _)

/-- Quantitative clearance of `Z-c` on any rational rectangle whose strict
interior contains `c`.

Four strict coordinate separations from the box sides make the same
squared gaps positive. Their original nested minimum is retained as
the certificate bound and controls every original boundary side. -/
@[expose] public def Affine.translatedCoordinate_boundaryClearanceBox
    (c : Canonical) {box : Box}
    (left : box.xLower < c.re) (right : c.re < box.xUpper)
    (below : box.yLower < c.im) (above : c.im < box.yUpper) :
    Basic.BoundaryClearance
      (Translated.translatedCoordinate c) box where
  bound := min ((c.re - box.xLower) ^ 2)
    (min ((box.xUpper - c.re) ^ 2)
      (min ((c.im - box.yLower) ^ 2) ((box.yUpper - c.im) ^ 2)))
  positive := Basic.lt_min
    (Arithmetic.pow_pos_direct
      (Arithmetic.sub_pos_direct left) 2)
    (Basic.lt_min
      (Arithmetic.pow_pos_direct
        (Arithmetic.sub_pos_direct right) 2)
      (Basic.lt_min
        (Arithmetic.pow_pos_direct
          (Arithmetic.sub_pos_direct below) 2)
        (Arithmetic.pow_pos_direct
          (Arithmetic.sub_pos_direct above) 2)))
  lower := by
    intro z boundary
    rw [Translated.translatedCoordinate_eval]
    rw [Canonical.normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
    simp only [← pow_two]
    rcases boundary.2 with onLeft | onRight | onBottom | onTop
    · have selected : min ((c.re - box.xLower) ^ 2)
          (min ((box.xUpper - c.re) ^ 2)
            (min ((c.im - box.yLower) ^ 2)
              ((box.yUpper - c.im) ^ 2))) ≤
          (c.re - box.xLower) ^ 2 := Basic.min_le_left _ _
      calc
        _ ≤ (c.re - box.xLower) ^ 2 := selected
        _ = (z.re - c.re) ^ 2 := by rw [onLeft]; ring1
        _ ≤ (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 :=
          le_add_of_nonneg_right
            (Arithmetic.sq_nonneg_direct _)
    · have selected : min ((c.re - box.xLower) ^ 2)
          (min ((box.xUpper - c.re) ^ 2)
            (min ((c.im - box.yLower) ^ 2)
              ((box.yUpper - c.im) ^ 2))) ≤
          (box.xUpper - c.re) ^ 2 :=
        (Basic.min_le_right _ _).trans (Basic.min_le_left _ _)
      calc
        _ ≤ (box.xUpper - c.re) ^ 2 := selected
        _ = (z.re - c.re) ^ 2 := by rw [onRight]
        _ ≤ (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 :=
          le_add_of_nonneg_right
            (Arithmetic.sq_nonneg_direct _)
    · have selected : min ((c.re - box.xLower) ^ 2)
          (min ((box.xUpper - c.re) ^ 2)
            (min ((c.im - box.yLower) ^ 2)
              ((box.yUpper - c.im) ^ 2))) ≤
          (c.im - box.yLower) ^ 2 :=
        (Basic.min_le_right _ _).trans
          ((Basic.min_le_right _ _).trans (Basic.min_le_left _ _))
      calc
        _ ≤ (c.im - box.yLower) ^ 2 := selected
        _ = (z.im - c.im) ^ 2 := by rw [onBottom]; ring1
        _ ≤ (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 :=
          le_add_of_nonneg_left
            (Arithmetic.sq_nonneg_direct _)
    · have selected : min ((c.re - box.xLower) ^ 2)
          (min ((box.xUpper - c.re) ^ 2)
            (min ((c.im - box.yLower) ^ 2)
              ((box.yUpper - c.im) ^ 2))) ≤
          (box.yUpper - c.im) ^ 2 :=
        (Basic.min_le_right _ _).trans
          ((Basic.min_le_right _ _).trans (Basic.min_le_right _ _))
      calc
        _ ≤ (box.yUpper - c.im) ^ 2 := selected
        _ = (z.im - c.im) ^ 2 := by rw [onTop]
        _ ≤ (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 :=
          le_add_of_nonneg_left
            (Arithmetic.sq_nonneg_direct _)

/-- Quantitative clearance of `Z-c` on a box lying strictly to the right of
`c`.  Real-coordinate separation alone supplies the positive lower bound.

The box left endpoint lies strictly to the right of the supplied
centre. The retained squared real-coordinate gap is positive and
bounds the same translated norm square at every box-boundary point. -/
@[expose] public def Affine.translatedCoordinate_boundaryClearance_of_left
    (c : Canonical) {box : Box} (left : c.re < box.xLower) :
    Basic.BoundaryClearance
      (Translated.translatedCoordinate c) box where
  bound := (box.xLower - c.re) ^ 2
  positive := Arithmetic.pow_pos_direct
    (Arithmetic.sub_pos_direct left) 2
  lower := by
    intro z boundary
    rw [Translated.translatedCoordinate_eval]
    rw [Canonical.normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
    simp only [← pow_two]
    have shifted : box.xLower - c.re ≤ z.re - c.re :=
      Arithmetic.sub_le_sub_right_direct boundary.1.1 c.re
    have square : (box.xLower - c.re) ^ 2 ≤ (z.re - c.re) ^ 2 :=
      Arithmetic.pow_le_pow_direct
        (Arithmetic.sub_nonneg_direct left.le) shifted 2
    exact square.trans (le_add_of_nonneg_right
      (Arithmetic.sq_nonneg_direct _))

/-- A box strictly left of the centre has quantitative translated-coordinate clearance.

The box right endpoint lies strictly to the left of the supplied
centre. The retained reflected squared real-coordinate gap is
positive and bounds the same translated boundary norm square. -/
@[expose] public def Affine.translatedCoordinate_boundaryClearance_of_right
    (c : Canonical) {box : Box} (right : box.xUpper < c.re) :
    Basic.BoundaryClearance
      (Translated.translatedCoordinate c) box where
  bound := (c.re - box.xUpper) ^ 2
  positive := Arithmetic.pow_pos_direct
    (Arithmetic.sub_pos_direct right) 2
  lower := by
    intro z boundary
    rw [Translated.translatedCoordinate_eval]
    rw [Canonical.normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
    simp only [← pow_two]
    have shifted : c.re - box.xUpper ≤ c.re - z.re :=
      Arithmetic.sub_le_sub_left_direct boundary.1.2.1 c.re
    have square : (c.re - box.xUpper) ^ 2 ≤ (c.re - z.re) ^ 2 :=
      Arithmetic.pow_le_pow_direct
        (Arithmetic.sub_nonneg_direct right.le) shifted 2
    have reflected : (c.re - z.re) ^ 2 = (z.re - c.re) ^ 2 := by ring1
    rw [reflected] at square
    exact square.trans (le_add_of_nonneg_right
      (Arithmetic.sq_nonneg_direct _))

/-- Quantitative clearance of `Z-c` on a box lying strictly above `c`.

The box bottom endpoint lies strictly above the supplied centre.
The retained squared imaginary-coordinate gap is positive and
bounds the same translated norm square on the original boundary. -/
@[expose] public def Affine.translatedCoordinate_boundaryClearance_of_below
    (c : Canonical) {box : Box} (below : c.im < box.yLower) :
    Basic.BoundaryClearance
      (Translated.translatedCoordinate c) box where
  bound := (box.yLower - c.im) ^ 2
  positive := Arithmetic.pow_pos_direct
    (Arithmetic.sub_pos_direct below) 2
  lower := by
    intro z boundary
    rw [Translated.translatedCoordinate_eval]
    rw [Canonical.normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
    simp only [← pow_two]
    have shifted : box.yLower - c.im ≤ z.im - c.im :=
      Arithmetic.sub_le_sub_right_direct boundary.1.2.2.1 c.im
    have square : (box.yLower - c.im) ^ 2 ≤ (z.im - c.im) ^ 2 :=
      Arithmetic.pow_le_pow_direct
        (Arithmetic.sub_nonneg_direct below.le) shifted 2
    exact square.trans (le_add_of_nonneg_left
      (Arithmetic.sq_nonneg_direct _))

/-- Quantitative clearance of `Z-c` on a box lying strictly below `c`.

The box top endpoint lies strictly below the supplied centre.
The retained reflected squared imaginary-coordinate gap is
positive and bounds the same translated boundary norm square. -/
@[expose] public def Affine.translatedCoordinate_boundaryClearance_of_above
    (c : Canonical) {box : Box} (above : box.yUpper < c.im) :
    Basic.BoundaryClearance
      (Translated.translatedCoordinate c) box where
  bound := (c.im - box.yUpper) ^ 2
  positive := Arithmetic.pow_pos_direct
    (Arithmetic.sub_pos_direct above) 2
  lower := by
    intro z boundary
    rw [Translated.translatedCoordinate_eval]
    rw [Canonical.normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
    simp only [← pow_two]
    have shifted : c.im - box.yUpper ≤ c.im - z.im :=
      Arithmetic.sub_le_sub_left_direct boundary.1.2.2.2 c.im
    have square : (c.im - box.yUpper) ^ 2 ≤ (c.im - z.im) ^ 2 :=
      Arithmetic.pow_le_pow_direct
        (Arithmetic.sub_nonneg_direct above.le) shifted 2
    have reflected : (c.im - z.im) ^ 2 = (z.im - c.im) ^ 2 := by ring1
    rw [reflected] at square
    exact square.trans (le_add_of_nonneg_left
      (Arithmetic.sq_nonneg_direct _))

/-- Construct boundary clearance for the retained linear factor when its root lies strictly inside the box.

The original retained linear factor has its root strictly between
both pairs of box endpoints. Its defining equation preserves the
same translated-coordinate clearance and exact cached minimum. -/
@[expose] public def ExplicitLegendreSegment.centeredClearance (root : Canonical) {box :
  Box}
    (left : box.xLower < root.re) (right : root.re < box.xUpper)
    (below : box.yLower < root.im) (above : root.im < box.yUpper) :
    Basic.BoundaryClearance
      (Translated.translatedCoordinate root) box :=
  Affine.translatedCoordinate_boundaryClearanceBox root
    left right below above

/-- Construct boundary clearance for a linear factor whose root lies strictly below the box.

The original factor root is strictly below the retained box. Its
defining equation preserves the translated-coordinate certificate
and the same squared vertical separation as cached clearance. -/
@[expose] public def ExplicitLegendreSegment.belowClearance (root : Canonical) {box :
  Box}
    (below : root.im < box.yLower) :
    Basic.BoundaryClearance
      (Translated.translatedCoordinate root) box :=
  Affine.translatedCoordinate_boundaryClearance_of_below
    root below

/-- Construct boundary clearance for a linear factor whose root lies strictly above the box.

The original factor root is strictly above the retained box. Its
defining equation preserves the translated-coordinate certificate
and the same reflected squared vertical separation. -/
@[expose] public def ExplicitLegendreSegment.aboveClearance (root : Canonical) {box :
  Box}
    (above : box.yUpper < root.im) :
    Basic.BoundaryClearance
      (Translated.translatedCoordinate root) box :=
  Affine.translatedCoordinate_boundaryClearance_of_above
    root above

/-- Construct boundary clearance for a linear factor whose root lies strictly left of the box.

The original factor root is strictly left of the retained box.
Its defining equation preserves the translated-coordinate certificate
and the same squared real-coordinate separation. -/
@[expose] public def ExplicitLegendreSegment.leftClearance (root : Canonical) {box : Box}
    (left : root.re < box.xLower) :
    Basic.BoundaryClearance
      (Translated.translatedCoordinate root) box :=
  Affine.translatedCoordinate_boundaryClearance_of_left root left

/-- Construct boundary clearance for a linear factor whose root lies strictly right of the box.

The original factor root is strictly right of the retained box.
Its defining equation preserves the translated-coordinate certificate
and the same reflected squared real-coordinate separation. -/
@[expose] public def ExplicitLegendreSegment.rightClearance (root : Canonical) {box :
  Box}
    (right : box.xUpper < root.re) :
    Basic.BoundaryClearance
      (Translated.translatedCoordinate root) box :=
  Affine.translatedCoordinate_boundaryClearance_of_right root right

/-- Construct boundary clearance for the retained linear factor on its fixed sixteenth-radius centered square.

The original linear factor and fixed centred box retain their root
parameter. The four displayed strict side inequalities supply the
same quantitative clearance certificate for that realization. -/
@[expose] public def centeredSquareSixteenthClearance (root : Canonical) :
    Basic.BoundaryClearance
      (Translated.translatedCoordinate root)
      (Box.Square.Centered.connectorFixedBox root) :=
  ExplicitLegendreSegment.centeredClearance root (Box.Square.Centered.connectorFixedBox_left root)
    (Box.Square.Centered.connectorFixedBox_right root) (Box.Square.Centered.connectorFixedBox_below root)
    (Box.Square.Centered.connectorFixedBox_above root)

/-- Construct translated-coordinate boundary clearance from the original certified outside side.

The retained side selects one of the four existing coordinate-gap
certificates. Its bound is the same squared side margin, and applies on the
original box without replacing its center or endpoints. -/
@[expose] public def Affine.translatedCoordinate_boundaryClearance_of_outside
    (root : Gaussian.Basic.Canonical) {box : Box} (side : Box.OutsideSide box root) :
    Boundary.Basic.BoundaryClearance
      (Dense.Gaussian.Linear.Translated.translatedCoordinate root) box :=
  match side with
  | .left less => Affine.translatedCoordinate_boundaryClearance_of_left root less
  | .right less => Affine.translatedCoordinate_boundaryClearance_of_right root less
  | .bottom less => Affine.translatedCoordinate_boundaryClearance_of_below root less
  | .top less => Affine.translatedCoordinate_boundaryClearance_of_above root less

/-- The outside-side clearance retains exactly that original side's squared margin. -/
public theorem Affine.translatedCoordinate_boundaryClearance_of_outside_bound
    (root : Gaussian.Basic.Canonical) {box : Box} (side : Box.OutsideSide box root) :
    (Affine.translatedCoordinate_boundaryClearance_of_outside root side).bound = side.margin := by
  cases side <;> rfl

/-- Retain quantitative clearance for an original affine polynomial whose cached root is outside the box.

The original leading coefficient and exact root determine the same ordered
constant/displacement product. Its bound is their retained quadrance product.
-/
@[expose] public def Affine.linear_boundaryClearance_of_outside
    {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (data : Dense.Gaussian.Roots.Linear.RootData polynomial) {box outer : Box}
    (side : Box.OutsideSide outer data.point) (refines : box.Refines outer) :
    Basic.BoundaryClearance polynomial box where
  bound := Gaussian.Basic.Canonical.normSq data.leading * side.margin
  positive := Fraction.Order.Arithmetic.mul_pos_direct
    (by
      rewrite [← Gaussian.Norm.Basic.normSq_eq_canonical]
      exact Gaussian.Norm.Basic.normSq_pos data.leadingNonzero)
    side.margin_pos
  lower := by
    intro point boundary
    rewrite [data.eval_eq point, Gaussian.Basic.Canonical.normSq_mul]
    have lower := side.margin_le_normSq_sub (refines.contains boundary.1)
    rewrite [Gaussian.Norm.Basic.normSq_eq_canonical] at lower
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lower
      (Gaussian.Basic.Canonical.normSq_nonneg data.leading)

/-- The affine clearance retains the original leading quadrance and original outside-side squared margin. -/
public theorem Affine.linear_boundaryClearance_of_outside_bound
    {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (data : Dense.Gaussian.Roots.Linear.RootData polynomial) {box outer : Box}
    (side : Box.OutsideSide outer data.point) (refines : box.Refines outer) :
    (Affine.linear_boundaryClearance_of_outside data side refines).bound =
      Gaussian.Basic.Canonical.normSq data.leading * side.margin := rfl

end Purelib.Polynomial.Clearance.Box.Boundary.Translated
