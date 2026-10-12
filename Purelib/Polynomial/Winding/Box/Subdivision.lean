module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
public import Purelib.Polynomial.Winding.Box.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Even
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Rational.Pair.Path.Basic (PolynomialEdge)

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

namespace Purelib.RootIsolation.Winding

end Purelib.RootIsolation.Winding

section
namespace Purelib.Polynomial.Winding.Box.Subdivision

open _root_.Purelib.RootIsolation.Winding
/-- Adjacent horizontal edge restrictions have additive doubled winding. -/
private theorem horizontal_add (p :
  CoefficientPolynomial)
    (y a b c : Fraction.Rational) :
    (Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides.horizontalEdge p y a b).doubledWinding +
        (Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides.horizontalEdge p y b c).doubledWinding =
      (Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides.horizontalEdge p y a c).doubledWinding :=
  PolynomialEdge.doubledWinding_restrict_add
    (Dense.Gaussian.Path.Box.Sides.horizontalEdge p y a c) a b c
/-- Adjacent vertical edge restrictions have additive doubled winding. -/
private theorem vertical_add (p :
  CoefficientPolynomial)
    (x a b c : Fraction.Rational) :
    (Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides.verticalEdge p x a b).doubledWinding +
        (Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides.verticalEdge p x b c).doubledWinding =
      (Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides.verticalEdge p x a c).doubledWinding :=
  PolynomialEdge.doubledWinding_restrict_add
    (Dense.Gaussian.Path.Box.Sides.verticalEdge p x a c) a b c
/-- Reversing a horizontal edge negates its doubled winding. -/
private theorem horizontal_reverse (p :
  CoefficientPolynomial)
    (y a b : Fraction.Rational) :
    (Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides.horizontalEdge p y b a).doubledWinding =
      -(Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides.horizontalEdge p y a b).doubledWinding :=
  PolynomialEdge.doubledWinding_reverse (Dense.Gaussian.Path.Box.Sides.horizontalEdge p y
    a b)
/-- Reversing a vertical edge negates its doubled winding. -/
private theorem vertical_reverse (p :
  CoefficientPolynomial)
    (x a b : Fraction.Rational) :
    (Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides.verticalEdge p x b a).doubledWinding =
      -(Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides.verticalEdge p x a b).doubledWinding :=
  PolynomialEdge.doubledWinding_reverse (Dense.Gaussian.Path.Box.Sides.verticalEdge p x a
    b)
end Purelib.Polynomial.Winding.Box.Subdivision
end

namespace Purelib.Polynomial.Winding.Box.Subdivision

/-- Exact cancellation of the internal edge in a vertical subdivision. -/
theorem quadrupledBoxWinding_vertical_split (p :
  CoefficientPolynomial) (box : Box)
    (cut : Fraction.Rational)
    (inside : box.xLower ≤ cut ∧ cut ≤ box.xUpper) :
    Winding.Box.Basic.quadrupledBoxWinding p box =
      Winding.Box.Basic.quadrupledBoxWinding p (box.verticalLeft cut inside) +
        Winding.Box.Basic.quadrupledBoxWinding p (box.verticalRight cut inside) := by
  rw [Winding.Box.Basic.quadrupledBoxWinding_eq, Winding.Box.Basic.quadrupledBoxWinding_eq,
    Winding.Box.Basic.quadrupledBoxWinding_eq]
  dsimp only [Box.verticalLeft,
    Box.verticalRight]
  have bottom := horizontal_add p box.yLower box.xLower cut box.xUpper
  have top := horizontal_add p box.yUpper box.xUpper cut box.xLower
  have internal := vertical_reverse p cut box.yLower box.yUpper
  rw [← bottom, ← top, internal]
  ring1

/-- Exact cancellation of the internal edge in a horizontal subdivision. -/
theorem quadrupledBoxWinding_horizontal_split (p :
  CoefficientPolynomial)
    (box : Box) (cut : Fraction.Rational)
    (inside : box.yLower ≤ cut ∧ cut ≤ box.yUpper) :
    Winding.Box.Basic.quadrupledBoxWinding p box =
      Winding.Box.Basic.quadrupledBoxWinding p (box.horizontalLower cut inside) +
        Winding.Box.Basic.quadrupledBoxWinding p (box.horizontalUpper cut inside) := by
  rw [Winding.Box.Basic.quadrupledBoxWinding_eq, Winding.Box.Basic.quadrupledBoxWinding_eq,
    Winding.Box.Basic.quadrupledBoxWinding_eq]
  dsimp only [Box.horizontalLower,
    Box.horizontalUpper]
  have right := vertical_add p box.xUpper box.yLower cut box.yUpper
  have left := vertical_add p box.xLower box.yUpper cut box.yLower
  have internal := horizontal_reverse p cut box.xLower box.xUpper
  rw [← right, ← left, internal]
  ring1

/-- One vertical and one horizontal cut give exact four-child additivity. -/
theorem quadrupledBoxWinding_four_split (p :
  CoefficientPolynomial) (box : Box)
    (xCut yCut : Fraction.Rational)
    (xInside : box.xLower ≤ xCut ∧ xCut ≤ box.xUpper)
    (yInside : box.yLower ≤ yCut ∧ yCut ≤ box.yUpper) :
    let left := box.verticalLeft xCut xInside
    let right := box.verticalRight xCut xInside
    let yInsideLeft : left.yLower ≤ yCut ∧ yCut ≤ left.yUpper := yInside
    let yInsideRight : right.yLower ≤ yCut ∧ yCut ≤ right.yUpper := yInside
    Winding.Box.Basic.quadrupledBoxWinding p box =
      Winding.Box.Basic.quadrupledBoxWinding p (left.horizontalLower yCut yInsideLeft) +
      Winding.Box.Basic.quadrupledBoxWinding p (left.horizontalUpper yCut yInsideLeft) +
      Winding.Box.Basic.quadrupledBoxWinding p (right.horizontalLower yCut yInsideRight) +
      Winding.Box.Basic.quadrupledBoxWinding p (right.horizontalUpper yCut yInsideRight) := by
  dsimp only
  rw [quadrupledBoxWinding_vertical_split p box xCut xInside,
    quadrupledBoxWinding_horizontal_split p
      (box.verticalLeft xCut xInside) yCut yInside,
    quadrupledBoxWinding_horizontal_split p
      (box.verticalRight xCut xInside) yCut yInside]
  ring1

/-! ## Normalized subdivision -/

/-- Doubled box winding is additive across a vertical cut when both child raw windings are even. -/
theorem doubledBoxWinding_vertical_split (p :
  CoefficientPolynomial) (box : Box)
    (cut : Fraction.Rational)
    (inside : box.xLower ≤ cut ∧ cut ≤ box.xUpper)
    (leftEven : Even (Winding.Box.Basic.quadrupledBoxWinding p (box.verticalLeft cut inside)))
    (rightEven : Even (Winding.Box.Basic.quadrupledBoxWinding p (box.verticalRight cut inside))) :
    Winding.Box.Basic.doubledBoxWinding p box =
      Winding.Box.Basic.doubledBoxWinding p (box.verticalLeft cut inside) +
        Winding.Box.Basic.doubledBoxWinding p (box.verticalRight cut inside) := by
  rcases leftEven with ⟨left, leftEven⟩
  rcases rightEven with ⟨right, rightEven⟩
  rw [Winding.Box.Basic.doubledBoxWinding, Winding.Box.Basic.doubledBoxWinding, Winding.Box.Basic.doubledBoxWinding,
    quadrupledBoxWinding_vertical_split p box cut inside,
    leftEven, rightEven]
  omega

/-- Doubled box winding is additive across a horizontal cut when both child raw windings are even. -/
theorem doubledBoxWinding_horizontal_split (p :
  CoefficientPolynomial)
    (box : Box) (cut : Fraction.Rational)
    (inside : box.yLower ≤ cut ∧ cut ≤ box.yUpper)
    (lowerEven : Even
      (Winding.Box.Basic.quadrupledBoxWinding p (box.horizontalLower cut inside)))
    (upperEven : Even
      (Winding.Box.Basic.quadrupledBoxWinding p (box.horizontalUpper cut inside))) :
    Winding.Box.Basic.doubledBoxWinding p box =
      Winding.Box.Basic.doubledBoxWinding p (box.horizontalLower cut inside) +
        Winding.Box.Basic.doubledBoxWinding p (box.horizontalUpper cut inside) := by
  rcases lowerEven with ⟨lower, lowerEven⟩
  rcases upperEven with ⟨upper, upperEven⟩
  rw [Winding.Box.Basic.doubledBoxWinding, Winding.Box.Basic.doubledBoxWinding, Winding.Box.Basic.doubledBoxWinding,
    quadrupledBoxWinding_horizontal_split p box cut inside,
    lowerEven, upperEven]
  omega

/-- Box winding is additive across a vertical cut when both child raw windings are divisible by four. -/
theorem boxWinding_vertical_split (p :
  CoefficientPolynomial) (box : Box)
    (cut : Fraction.Rational)
    (inside : box.xLower ≤ cut ∧ cut ≤ box.xUpper)
    (leftDivisible : (4 : Int) ∣
      Winding.Box.Basic.quadrupledBoxWinding p (box.verticalLeft cut inside))
    (rightDivisible : (4 : Int) ∣
      Winding.Box.Basic.quadrupledBoxWinding p (box.verticalRight cut inside)) :
    Winding.Box.Basic.boxWinding p box =
      Winding.Box.Basic.boxWinding p (box.verticalLeft cut inside) +
        Winding.Box.Basic.boxWinding p (box.verticalRight cut inside) := by
  rcases leftDivisible with ⟨left, leftDivisible⟩
  rcases rightDivisible with ⟨right, rightDivisible⟩
  rw [Winding.Box.Basic.boxWinding, Winding.Box.Basic.boxWinding, Winding.Box.Basic.boxWinding,
    quadrupledBoxWinding_vertical_split p box cut inside,
    leftDivisible, rightDivisible]
  omega

/-- Box winding is additive across a horizontal cut when both child raw windings are divisible by four. -/
theorem boxWinding_horizontal_split (p :
  CoefficientPolynomial) (box : Box)
    (cut : Fraction.Rational)
    (inside : box.yLower ≤ cut ∧ cut ≤ box.yUpper)
    (lowerDivisible : (4 : Int) ∣
      Winding.Box.Basic.quadrupledBoxWinding p (box.horizontalLower cut inside))
    (upperDivisible : (4 : Int) ∣
      Winding.Box.Basic.quadrupledBoxWinding p (box.horizontalUpper cut inside)) :
    Winding.Box.Basic.boxWinding p box =
      Winding.Box.Basic.boxWinding p (box.horizontalLower cut inside) +
        Winding.Box.Basic.boxWinding p (box.horizontalUpper cut inside) := by
  rcases lowerDivisible with ⟨lower, lowerDivisible⟩
  rcases upperDivisible with ⟨upper, upperDivisible⟩
  rw [Winding.Box.Basic.boxWinding, Winding.Box.Basic.boxWinding, Winding.Box.Basic.boxWinding,
    quadrupledBoxWinding_horizontal_split p box cut inside,
    lowerDivisible, upperDivisible]
  omega

end Purelib.Polynomial.Winding.Box.Subdivision

end
