module

public import Purelib.Curves.Legendre.Polynomial
public import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
public import Purelib.Data.Fin
public import Purelib.Polynomial.Quadratic.Split
public import Purelib.Polynomial.Dense.Derivative
public import Purelib.Geometry.Rational.Box.Outside
public import Purelib.Geometry.Rational.Box.Square.Centered
public import Purelib.Polynomial.Winding.Box.Power
public import Purelib.Polynomial.Dense.Gaussian.Constants
import Purelib.Polynomial.Clearance.Box.Boundary.Constant
import Purelib.Polynomial.Clearance.Box.Boundary.Power
import Purelib.Polynomial.Clearance.Box.Boundary.Translated
import Purelib.Polynomial.Winding.Box.Affine
import Purelib.Polynomial.Winding.Box.Constant
import Purelib.Polynomial.Winding.Box.Product
import Purelib.Polynomial.Dense.Gaussian.Power
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Data.Fin.Two
import Purelib.Curves.Legendre.Paths.Frame
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# The two labelled Legendre nodal collisions

The original fixed and moving branch labels determine the centered quadratic
factor of the original cubic. Its smoothing parameter is the squared signed
half-gap. A computed spatial box excludes the remaining branch throughout,
and the original finite winding algorithms certify the quadratic base change.
These algebraic local data do not yet construct a lifted geometric twist.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration

open Purelib.Polynomial.Dense.Gaussian
open Purelib.Geometry.Rational.Box

open Purelib
open Purelib.Data
open Purelib.Algebra.Field
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Quadratic
open Purelib.Curves.Legendre
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian

/-- The original fixed branch label involved in the selected zero or one collision. -/
@[expose] def fixedLabel (site : Fin 2) : Fin 3 := Data.Fin.cases 0 (fun _ => 2) site

/-- The original fixed branch label remaining outside the selected collision. -/
@[expose] def remainingLabel (site : Fin 2) : Fin 3 := Data.Fin.cases 2 (fun _ => 0) site

/-- The singular parameter and curve coordinate of the selected zero or one collision. -/
@[expose] def criticalValue (site : Fin 2) : Canonical := Data.Fin.cases 0 (fun _ => 1) site

/-- The remaining fixed root of the same original cubic. -/
@[expose] def remainingValue (site : Fin 2) : Canonical := Data.Fin.cases 1 (fun _ => 0) site

/-- The selected critical value is the reading of its original fixed branch label on every fibre. -/
theorem criticalValue_eq_branchPoint (site : Fin 2) (parameter : Canonical) :
    criticalValue site = Paths.branchPoint parameter (fixedLabel site) := by
  rcases Fin.Two.finTwo_cases site with zero | one
  · subst site
    rfl
  · subst site
    rfl

/-- The excluded root is the reading of its original remaining branch label on every fibre. -/
theorem remainingValue_eq_branchPoint (site : Fin 2) (parameter : Canonical) :
    remainingValue site = Paths.branchPoint parameter (remainingLabel site) := by
  rcases Fin.Two.finTwo_cases site with zero | one
  · subst site
    rfl
  · subst site
    rfl

/-- The midpoint of the original fixed root and the same original moving parameter root. -/
@[expose] def center (site : Fin 2) (parameter : Canonical) : Canonical :=
  Split.center (criticalValue site) parameter

/-- The signed half-gap from the original fixed root to the same original moving root. -/
@[expose] def halfGap (site : Fin 2) (parameter : Canonical) : Canonical :=
  Split.halfGap (criticalValue site) parameter

/-- The local smoothing parameter computed from the original labelled branch displacement. -/
@[expose] def smoothing (site : Fin 2) (parameter : Canonical) : Canonical := halfGap site parameter ^ 2

/-- The original curve coordinate translated by the computed collision midpoint. -/
@[expose] def coordinate (site : Fin 2) (parameter point : Canonical) : Canonical :=
  point - center site parameter

/-- The remaining affine factor of the same original cubic on the collision patch. -/
@[expose] def unitPolynomial (site : Fin 2) : Paths.GaussianPolynomial :=
  Linear.Translated.translatedCoordinate (remainingValue site)

/-- The original cubic is the product of its original collision pair and the remaining affine factor. -/
theorem polynomial_eq_pair (site : Fin 2) (parameter point : Canonical) :
    (Paths.polynomial parameter).eval point =
      ((point - criticalValue site) * (point - parameter)) * (unitPolynomial site).eval point := by
  rewrite [Paths.polynomial_eval, unitPolynomial, Linear.Translated.translatedCoordinate_eval]
  rcases Fin.Two.finTwo_cases site with zero | one
  · subst site
    change point * (point - 1) * (point - parameter) = ((point - 0) * (point - parameter)) * (point - 1)
    ring1
  · subst site
    change point * (point - 1) * (point - parameter) = ((point - 1) * (point - parameter)) * (point - 0)
    ring1

/-- Centering the original cubic leaves its retained affine unit times the standard quadratic nodal core.

The same original root labels determine the midpoint and signed half-gap.
The equality keeps the remaining factor; removing it requires its actual
nonvanishing and a separately constructed compatible unit-root reading.
-/
theorem polynomial_centered (site : Fin 2) (parameter point : Canonical) :
    (Paths.polynomial parameter).eval point =
      (coordinate site parameter point ^ 2 - smoothing site parameter) * (unitPolynomial site).eval point := by
  rewrite [polynomial_eq_pair, Split.product_eq (criticalValue site) parameter point (by decide +kernel)]
  rfl

/-- The negative half-gap recovers the original fixed root in the centered coordinate. -/
theorem center_sub_halfGap (site : Fin 2) (parameter : Canonical) :
    center site parameter - halfGap site parameter = Paths.branchPoint parameter (fixedLabel site) :=
  (Split.center_sub_halfGap _ _ (by decide +kernel)).trans (criticalValue_eq_branchPoint site parameter)

/-- The positive half-gap recovers the same original moving root. -/
theorem center_add_halfGap (site : Fin 2) (parameter : Canonical) :
    center site parameter + halfGap site parameter = Paths.branchPoint parameter 1 :=
  (Split.center_add_halfGap _ _ (by decide +kernel)).trans (Paths.branchPoint_one parameter).symm

/-- A parameter different from the selected critical value has a nonzero computed smoothing parameter. -/
theorem smoothing_ne_zero (site : Fin 2) {parameter : Canonical} (regular : parameter ≠ criticalValue site) :
    smoothing site parameter ≠ 0 := by
  have gap : halfGap site parameter ≠ 0 := Split.halfGap_ne_zero (by decide +kernel) regular.symm
  unfold smoothing
  rewrite [pow_two]
  exact Field.mul_ne_zero_direct gap gap

/-- The computed half-width-one-half spatial square around the original collision coordinate. -/
@[expose] def spatialBox (site : Fin 2) : Box :=
  Square.Centered.Affine.centeredSquare (criticalValue site) (1 / 2) (by decide +kernel)

/-- The computed half-width-one-quarter parameter square about the same original critical value. -/
@[expose] def parameterBox (site : Fin 2) : Box :=
  Square.Centered.Affine.centeredSquare (criticalValue site) (1 / 4) (by decide +kernel)

/-- The original remaining root has a computed strict outside side on the same retained collision square. -/
def remainingSide : (site : Fin 2) → (spatialBox site).OutsideSide (remainingValue site) :=
  Data.Fin.casesDependent (.right (by decide +kernel))
    (Data.Fin.casesDependent (.left (by decide +kernel)) (fun index => Fin.elim0 index))

/-- The same selected outside side retains its exact squared separation one quarter. -/
theorem remainingSide_margin (site : Fin 2) : (remainingSide site).margin = 1 / 4 := by
  rcases Fin.Two.finTwo_cases site with zero | one
  · subst site
    rfl
  · subst site
    rfl

/-- The remaining unit factor is uniformly separated from zero throughout the full original collision square. -/
theorem unit_lower (site : Fin 2) {point : Canonical} (inside : (spatialBox site).Contains point) :
    (1 / 4 : Rat.Fraction.Rational) ≤ Norm.Basic.normSq ((unitPolynomial site).eval point) := by
  have lower := (remainingSide site).margin_le_normSq_sub inside
  rewrite [remainingSide_margin] at lower
  rewrite [unitPolynomial, Linear.Translated.translatedCoordinate_eval]
  exact lower

/-- Every original collision-square reading has a nonzero remaining affine factor. -/
theorem unit_ne_zero (site : Fin 2) {point : Canonical} (inside : (spatialBox site).Contains point) :
    (unitPolynomial site).eval point ≠ 0 := by
  intro zero
  have lower := unit_lower site inside
  rewrite [zero, Norm.Basic.normSq_zero] at lower
  exact (by decide +kernel : ¬ (1 / 4 : Rat.Fraction.Rational) ≤ 0) lower

/-- The original moving root lies strictly inside the collision square on the computed parameter square. -/
theorem moving_strictContains (site : Fin 2) {parameter : Canonical}
    (inside : (parameterBox site).Contains parameter) : (spatialBox site).StrictContains parameter := by
  change (criticalValue site).re - 1 / 4 ≤ parameter.re ∧
    parameter.re ≤ (criticalValue site).re + 1 / 4 ∧
    (criticalValue site).im - 1 / 4 ≤ parameter.im ∧ parameter.im ≤ (criticalValue site).im + 1 / 4 at inside
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Rat.Fraction.Order.Arithmetic.sub_lt_sub_left_direct
      (by decide +kernel : (1 / 4 : Rat.Fraction.Rational) < 1 / 2) (criticalValue site).re).trans_le inside.1
  · exact inside.2.1.trans_lt (Rat.Fraction.Order.Arithmetic.add_lt_add_left_direct
      (by decide +kernel : (1 / 4 : Rat.Fraction.Rational) < 1 / 2) (criticalValue site).re)
  · exact (Rat.Fraction.Order.Arithmetic.sub_lt_sub_left_direct
      (by decide +kernel : (1 / 4 : Rat.Fraction.Rational) < 1 / 2) (criticalValue site).im).trans_le inside.2.2.1
  · exact inside.2.2.2.trans_lt (Rat.Fraction.Order.Arithmetic.add_lt_add_left_direct
      (by decide +kernel : (1 / 4 : Rat.Fraction.Rational) < 1 / 2) (criticalValue site).im)

/-- Patch admission separates the original moving root from the same retained remaining branch. -/
theorem parameter_ne_remaining (site : Fin 2) {parameter : Canonical}
    (inside : (parameterBox site).Contains parameter) : parameter ≠ remainingValue site := by
  have spatial := moving_strictContains site inside
  have nonzero := unit_ne_zero site ⟨spatial.1.le, spatial.2.1.le, spatial.2.2.1.le, spatial.2.2.2.le⟩
  intro equal
  apply nonzero
  rewrite [unitPolynomial, Linear.Translated.translatedCoordinate_eval, equal]
  ring1

/-- Construct the original regular Legendre frame on the computed collision-parameter patch.

Intrinsic exclusion of the selected critical value and patch admission
derive both original zero/one exclusions. The existing original frame
constructor computes all three owners and their chart internally.
-/
def frameOnPatch (site : Fin 2) (parameter : Canonical)
    (regular : parameter ≠ criticalValue site) (inside : (parameterBox site).Contains parameter) :
    Paths.Frame parameter := by
  have other := parameter_ne_remaining site inside
  by_cases zero : site = 0
  · subst site
    exact Paths.Frame.ofParameter parameter regular other
  · have one := (Fin.Two.finTwo_cases site).resolve_left zero
    subst site
    exact Paths.Frame.ofParameter parameter other regular

/-- The original smoothing parameter is represented by a quarter-scaled square of the same translated parameter. -/
@[expose] def smoothingPolynomial (site : Fin 2) : Paths.GaussianPolynomial :=
  Dense.Gaussian.Constants.gaussianConstant (1 / 4) *
    Dense.Gaussian.Power.polynomialPower
      (Linear.Translated.translatedCoordinate (criticalValue site)) 2

/-- The finite smoothing polynomial reads the squared half-gap of the same original labelled roots. -/
theorem smoothingPolynomial_eval (site : Fin 2) (parameter : Canonical) :
    (smoothingPolynomial site).eval parameter = smoothing site parameter := by
  rewrite [smoothingPolynomial, Dense.Basic.DensePolynomial.eval_mul,
    Dense.Gaussian.Constants.gaussianConstant_eval, Dense.Gaussian.Power.eval_polynomialPower,
    Linear.Translated.translatedCoordinate_eval]
  unfold smoothing halfGap Split.halfGap
  rewrite [ExplicitField.div_eq_mul_inv]
  have inverseSquare : ((2 : Canonical)⁻¹) ^ 2 = (1 : Canonical) / 4 := by decide +kernel
  calc
    (1 / 4 : Canonical) * (parameter - criticalValue site) ^ 2 =
        (parameter - criticalValue site) ^ 2 * ((2 : Canonical)⁻¹) ^ 2 := by
      rewrite [inverseSquare]
      ring1
    _ = ((parameter - criticalValue site) * (2 : Canonical)⁻¹) ^ 2 := by ring1

/-- Compute the original smoothing polynomial's boundary clearance on a positive critical-value square.

The same translated coordinate supplies its retained centered-square
clearance. The existing finite power and constant-product constructors
build the quadratic base-change certificate without a supplied winding law.
-/
def smoothingClearance (site : Fin 2) {radius : Rat.Fraction.Rational} (positive : 0 < radius) :
    Clearance.Box.Boundary.Basic.BoundaryClearance (smoothingPolynomial site)
      (Square.Centered.Affine.centeredSquare (criticalValue site) radius positive.le) :=
  let coordinateClearance := Clearance.Box.Boundary.Translated.translatedCoordinate_boundaryClearance
    (criticalValue site) positive
  let constantClearance := Clearance.Box.Boundary.Constant.gaussianConstant_boundaryClearance
    (by decide +kernel : (1 / 4 : Canonical) ≠ 0)
    (Square.Centered.Affine.centeredSquare (criticalValue site) radius positive.le)
  constantClearance.mul (Clearance.Box.Boundary.Power.polynomialPower_boundaryClearance coordinateClearance 2)

/-- The original smoothing map has quadrupled winding eight on every positive critical-value square.

The retained translated parameter has winding one. Finite squaring doubles
its winding, and the nonzero quarter coefficient contributes zero. These
computed family data explain the labelled quadratic base change; the lifted
geometric twist comparison remains a separate construction.
-/
theorem smoothing_quadrupledWinding (site : Fin 2) {radius : Rat.Fraction.Rational} (positive : 0 < radius) :
    Winding.Box.Basic.quadrupledBoxWinding (smoothingPolynomial site)
      (Square.Centered.Affine.centeredSquare (criticalValue site) radius positive.le) = 8 := by
  let box := Square.Centered.Affine.centeredSquare (criticalValue site) radius positive.le
  let coordinatePolynomial := Linear.Translated.translatedCoordinate (criticalValue site)
  let coordinateClearance := Clearance.Box.Boundary.Translated.translatedCoordinate_boundaryClearance
    (criticalValue site) positive
  let constantClearance := Clearance.Box.Boundary.Constant.gaussianConstant_boundaryClearance
    (by decide +kernel : (1 / 4 : Canonical) ≠ 0) box
  have proper := Box.Square.Centered.centeredSquare_proper (criticalValue site) positive
  have powerWinding := Winding.Box.Power.quadrupledBoxWinding_polynomialPower proper coordinateClearance 2
  have coordinateWinding := Winding.Box.Affine.quadrupledBoxWinding_translatedCoordinate_centeredSquare
    (criticalValue site) positive
  have productWinding := Winding.Box.Product.quadrupledBoxWinding_mul_of_boundaryClearances
    (Dense.Gaussian.Constants.gaussianConstant (1 / 4))
    (Dense.Gaussian.Power.polynomialPower coordinatePolynomial 2) box proper constantClearance
    (Clearance.Box.Boundary.Power.polynomialPower_boundaryClearance coordinateClearance 2)
  change Winding.Box.Basic.quadrupledBoxWinding
    (Dense.Gaussian.Constants.gaussianConstant (1 / 4) *
      Dense.Gaussian.Power.polynomialPower coordinatePolynomial 2) box = 8
  rewrite [productWinding, Winding.Box.Constant.quadrupledBoxWinding_gaussianConstant
    (by decide +kernel : (1 / 4 : Canonical) ≠ 0) box, powerWinding, coordinateWinding]
  decide +kernel

/-- The same original finite boundary algorithm computes smoothing winding two after its retained normalization. -/
theorem smoothing_winding (site : Fin 2) {radius : Rat.Fraction.Rational} (positive : 0 < radius) :
    Winding.Box.Basic.boxWinding (smoothingPolynomial site)
      (Square.Centered.Affine.centeredSquare (criticalValue site) radius positive.le) = 2 := by
  unfold Winding.Box.Basic.boxWinding
  rewrite [smoothing_quadrupledWinding site positive]
  decide +kernel

/-- The original selected critical fibre has a double root with nonzero second spatial derivative.

The two checks evaluate the original finite dense derivative algorithm on
the original cubic. They do not replace a labelled base change by a transverse
one-parameter nodal smoothing.
-/
theorem critical_fibre_node (site : Fin 2) :
    (Paths.polynomial (criticalValue site)).eval (criticalValue site) = 0 ∧
      (Dense.Derivative.derivative (Paths.polynomial (criticalValue site))).eval (criticalValue site) = 0 ∧
      (Dense.Derivative.derivative (Dense.Derivative.derivative
        (Paths.polynomial (criticalValue site)))).eval (criticalValue site) ≠ 0 := by
  rcases Fin.Two.finTwo_cases site with zero | one
  · subst site
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
  · subst site
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The same original remaining branch is a simple root on the selected critical fibre. -/
theorem remaining_fibre_simple (site : Fin 2) :
    (Paths.polynomial (criticalValue site)).eval (remainingValue site) = 0 ∧
      (Dense.Derivative.derivative (Paths.polynomial (criticalValue site))).eval (remainingValue site) ≠ 0 := by
  rcases Fin.Two.finTwo_cases site with zero | one
  · subst site
    exact ⟨by decide +kernel, by decide +kernel⟩
  · subst site
    exact ⟨by decide +kernel, by decide +kernel⟩

/-- Parameter variation leaves the original fixed node coordinate a root.

Every finite increment keeps the exact same reading at the original node
coordinate. Thus the labelled parameter is not a transverse smoothing there.
-/
theorem parameter_variation_at_node (site : Fin 2) (increment : Canonical) :
    (Paths.polynomial (criticalValue site + increment)).eval (criticalValue site) =
      (Paths.polynomial (criticalValue site)).eval (criticalValue site) := by
  rcases Fin.Two.finTwo_cases site with zero | one
  · subst site
    exact (Paths.polynomial_zero _).trans (Paths.polynomial_zero _).symm
  · subst site
    exact (Paths.polynomial_one _).trans (Paths.polynomial_one _).symm

open Purelib.Polynomial.Dense.Gaussian.Bounds

/-- Either original nodal square has endpoint enclosure radius at most three halves.

The bound is computed from the same two critical values and the original
half-width one half; it does not depend on a branch frame or root owner.
-/
theorem spatialBox_enclosingRadius_le (site : Fin 2) :
    (spatialBox site).enclosingRadius ≤ (3 / 2 : Rat.Fraction.Rational) := by
  rcases Fin.Two.finTwo_cases site with zero | one
  · subst site
    change max 0 (max (max (-((0 : Rat.Fraction.Rational) - 1 / 2)) (0 + 1 / 2))
      (max (-(0 - 1 / 2)) (0 + 1 / 2))) ≤ 3 / 2
    decide
  · subst site
    change max 0 (max (max (-((1 : Rat.Fraction.Rational) - 1 / 2)) (1 + 1 / 2))
      (max (-((0 : Rat.Fraction.Rational) - 1 / 2)) (0 + 1 / 2))) ≤ 3 / 2
    decide

/-- Both original nodal spatial squares lie in the same coefficient-computed Legendre ambient square.

The actual collision square has half-width one half. Its finite endpoint
enclosure is at most three halves, whereas the original polynomial radius
is at least four for every parameter. The original frame is unchanged. -/
theorem spatialBox_refines_largeSquare (site : Fin 2) (parameter : Canonical) :
    (spatialBox site).Refines (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)) := by
  have enclosed := spatialBox_enclosingRadius_le site
  exact (spatialBox site).refines_symmetric_of_enclosingRadius_le
    (RootRadius.denseLargeSquareRadius_pos (Paths.polynomial parameter)).le
    (enclosed.trans ((by decide : (3 / 2 : Rat.Fraction.Rational) ≤ 4).trans
      (Curves.Legendre.Polynomial.four_le_largeSquareRadius parameter)))

end Purelib.Curves.Legendre.Degeneration
