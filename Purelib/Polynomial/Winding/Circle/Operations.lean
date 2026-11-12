module

public import Purelib.Polynomial.Winding.Circle.Product
public import Purelib.Polynomial.Winding.Circle.LinearFactor
public import Purelib.Polynomial.Dense.Gaussian.Power
public import Purelib.Polynomial.Dense.Gaussian.Split
import Purelib.Polynomial.Winding.Circle.Comparison
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Power
import Purelib.Algebra.NatCast
import Purelib.Tactic.Ring

/-!
# Finite algebra of independent circle winding

Constant scaling, original finite natural powers and original ordered split
products all use the same chart-event winding. The scalar identities follow
from actual dense evaluation and the checked product formula.
-/

namespace Purelib.Polynomial.Clearance.Circle

open Purelib.Data
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Dense.Basic (DensePolynomial)
open Dense.Gaussian
open Gaussian.Basic (Canonical)

/-- A nonzero scalar multiplies the original circle margin by its exact quadrance. -/
@[expose] public def Certificate.scale {polynomial : CoefficientPolynomial}
    (clearance : Certificate polynomial) (scalar : Canonical) (nonzero : scalar ≠ 0) :
    Certificate (DensePolynomial.scale scalar polynomial) :=
  ((Certificate.constant scalar nonzero).product clearance).transport
    (fun point _ => by rw [DensePolynomial.eval_scale, DensePolynomial.eval_mul, DensePolynomial.eval_constant])

/-- A finite coordinate shift preserves the original whole-circle quadrance margin.

The same original polynomial is multiplied by a unit-quadrance monomial.
The original positive payment is retained unchanged at every rational unit point.
-/
@[expose] public def Certificate.shift {polynomial : CoefficientPolynomial}
    (clearance : Certificate polynomial) (exponent : Nat) : Certificate (DensePolynomial.shift exponent polynomial) :=
  { bound := clearance.bound
    positive := clearance.positive
    lower := by
      intro point unit
      rewrite [DensePolynomial.eval_shift, Gaussian.Norm.Basic.normSq_mul,
        Gaussian.Power.normSq_pow, Gaussian.Norm.Basic.normSq_eq_canonical point, unit, one_pow,
        Rat.Fraction.Field.mul_one_direct]
      exact clearance.lower point unit }

/-- Natural powers retain the product of the original factor margins. -/
@[expose] public def Certificate.power {polynomial : CoefficientPolynomial} (clearance : Certificate polynomial) :
    (exponent : Nat) → Certificate (Power.polynomialPower polynomial exponent)
  | 0 => Certificate.constant 1 (by decide)
  | exponent + 1 => clearance.product (clearance.power exponent)

/-- The original ordered split product inherits the supplied margins of its same displayed linear factors. -/
@[expose] public def Certificate.splitProduct : (roots : List Canonical) →
    (∀ point, point ∈ roots → Certificate (LinearFactor.linearFactor point)) →
    Certificate (Split.splitPolynomial roots)
  | [], _ => Certificate.constant 1 (by decide)
  | head :: remaining, margins =>
      (margins head (List.Mem.head _)).product
        (Certificate.splitProduct remaining (fun point member => margins point (List.Mem.tail _ member)))

end Purelib.Polynomial.Clearance.Circle

namespace Purelib.Polynomial.Winding.Circle

open Purelib.Data
open Purelib.Algebra
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Dense.Basic (DensePolynomial)
open Dense.Gaussian
open Gaussian.Basic (Canonical)
open Purelib.Polynomial.Clearance.Circle (Certificate)

/-- Nonzero constant scaling preserves the actual independent circle raw winding. -/
public theorem raw_scale {polynomial : CoefficientPolynomial} (clearance : Certificate polynomial)
    (scalar : Canonical) (nonzero : scalar ≠ 0) (paths : Boundary.Substitutions polynomial)
    (scaledPaths : Boundary.Substitutions (DensePolynomial.scale scalar polynomial)) :
    raw scaledPaths = raw paths := by
  let constantPaths := Boundary.Substitutions.prepare (DensePolynomial.constant scalar)
  let productPaths := Boundary.Substitutions.prepare (DensePolynomial.constant scalar * polynomial)
  have same := Comparison.raw_eq_of_eval_eq ((Certificate.constant scalar nonzero).product clearance)
    productPaths scaledPaths (fun point _ => by
      rw [DensePolynomial.eval_scale, DensePolynomial.eval_mul, DensePolynomial.eval_constant])
  calc
    raw scaledPaths = raw productPaths := same
    _ = raw constantPaths + raw paths := raw_mul (Certificate.constant scalar nonzero) clearance
      constantPaths paths productPaths
    _ = raw paths := by rw [raw_constant]; ring1

/-- The original finite natural polynomial power multiplies independent raw winding by its exponent. -/
public theorem raw_power {polynomial : CoefficientPolynomial} (clearance : Certificate polynomial)
    (paths : Boundary.Substitutions polynomial) : (exponent : Nat) →
    (powerPaths : Boundary.Substitutions (Power.polynomialPower polynomial exponent)) →
    raw powerPaths = (exponent : Int) * raw paths
  | 0, powerPaths => by
      change raw powerPaths = (0 : Int) * raw paths
      exact (raw_constant 1 powerPaths).trans (by ring1)
  | exponent + 1, powerPaths => by
      let tailPaths := Boundary.Substitutions.prepare (Power.polynomialPower polynomial exponent)
      have product := raw_mul clearance (clearance.power exponent) paths tailPaths powerPaths
      rw [raw_power clearance paths exponent tailPaths] at product
      rewrite [NatCast.add]
      change raw powerPaths = ((exponent : Int) + 1) * raw paths
      exact product.trans (by ring1)

/-- An actual finite coordinate shift adds its exponent to the independent circle winding.

Both substitution owners remain supplied actual inputs. The proof uses the
same original coordinate-power and product phase identities, without any root
inventory or fixed-degree hypothesis.
-/
public theorem raw_shift {polynomial : CoefficientPolynomial} (clearance : Certificate polynomial)
    (paths : Boundary.Substitutions polynomial) (exponent : Nat)
    (shiftedPaths : Boundary.Substitutions (DensePolynomial.shift exponent polynomial)) :
    raw shiftedPaths = raw paths + 4 * (exponent : Int) := by
  let coordinatePaths := Boundary.Substitutions.prepare (LinearFactor.linearFactor 0)
  let power := Power.polynomialPower (LinearFactor.linearFactor 0) exponent
  let powerPaths := Boundary.Substitutions.prepare power
  let productPaths := Boundary.Substitutions.prepare (power * polynomial)
  have agreement := Comparison.raw_eq_of_eval_eq ((Certificate.coordinatePower exponent).product clearance)
    productPaths shiftedPaths (fun point _ => by
      rewrite [DensePolynomial.eval_shift, DensePolynomial.eval_mul,
        Power.eval_polynomialPower, LinearFactor.linearFactor_eval, Gaussian.Basic.sub_zero]
      exact Gaussian.Basic.mul_comm _ _)
  have coordinate := raw_power (Certificate.linearInside 0 (by decide)) coordinatePaths exponent powerPaths
  rewrite [raw_coordinate] at coordinate
  have product := raw_mul (Certificate.coordinatePower exponent) clearance powerPaths paths productPaths
  calc
    raw shiftedPaths = raw productPaths := agreement
    _ = (exponent : Int) * 4 + raw paths := by rewrite [product, coordinate]; rfl
    _ = _ := by ring1

/-- The original ordered split product sums the independently proved linear-factor readings.

Each input root occurrence remains in the original list. The supplied natural
weight is only a theorem target: the executable winding remains the original
chart-event reading, and every linear-factor equality is required separately.
-/
public theorem raw_splitProduct (weight : Canonical → Nat) : (roots : List Canonical) →
    (margins : ∀ point, point ∈ roots → Certificate (LinearFactor.linearFactor point)) →
    (∀ point, point ∈ roots → (paths : Boundary.Substitutions (LinearFactor.linearFactor point)) →
      raw paths = 4 * (weight point : Int)) →
    (paths : Boundary.Substitutions (Split.splitPolynomial roots)) →
    raw paths = 4 * ((roots.foldr (fun point total => weight point + total) 0 : Nat) : Int)
  | [], _, _, paths => by
      change raw paths = 0
      exact raw_constant 1 paths
  | head :: remaining, margins, readings, paths => by
      let headPaths := Boundary.Substitutions.prepare (LinearFactor.linearFactor head)
      let tailPaths := Boundary.Substitutions.prepare (Split.splitPolynomial remaining)
      let tailMargins := fun point member => margins point (List.Mem.tail head member)
      have product := raw_mul (margins head (List.Mem.head _))
        (Certificate.splitProduct remaining tailMargins) headPaths tailPaths paths
      have tail := raw_splitProduct weight remaining tailMargins
        (fun point member => readings point (List.Mem.tail head member)) tailPaths
      rw [readings head (List.Mem.head _) headPaths, tail] at product
      change raw paths = 4 * ((weight head + remaining.foldr (fun point total => weight point + total) 0 : Nat) : Int)
      rewrite [NatCast.add]
      exact product.trans (by ring1)

end Purelib.Polynomial.Winding.Circle
