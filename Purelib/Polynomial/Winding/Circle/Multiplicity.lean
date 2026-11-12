module

public import Purelib.Polynomial.Winding.Circle.Operations
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Product
import Purelib.Data.List.OfFn.Basic
import Purelib.Algebra.NatCast
import Purelib.Tactic.Ring

/-!
# Independent winding of the original weighted polynomial product

The original positive multiplicity list retains every squarefree factor and
its natural exponent. Its same dense polynomial product sums the independent
factor windings with those exact weights and original occurrence order.
-/

namespace Purelib.Polynomial.Clearance.Circle

open Purelib.Data
open Dense.Gaussian.Multiplicity.Basis
open Positive (PositiveEntry)

/-- The original weighted positive product inherits its same bounded factor-occurrence margins. -/
@[expose] public def Certificate.positiveProduct : (entries : List PositiveEntry) →
    (∀ index : Fin entries.length, Certificate (entries.get index).part.polynomial) →
    Certificate (Product.positivePolynomial entries)
  | [], _ => Certificate.constant 1 (by decide)
  | head :: remaining, margins =>
      ((margins 0).power head.multiplicity).product
        (Certificate.positiveProduct remaining (fun index => margins index.succ))

end Purelib.Polynomial.Clearance.Circle

namespace Purelib.Polynomial.Winding.Circle

open Purelib.Data
open Purelib.Algebra
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Dense.Gaussian
open Multiplicity.Basis
open Positive (PositiveEntry)
open Purelib.Polynomial.Clearance.Circle (Certificate)

/-- The independent reading of the original weighted product is the same ordered weighted sum of factor readings.

Every bounded input occurrence supplies its own original margin and independent
factor equality. The natural counts are theorem targets and never define the
executable chart-event winding of the retained product.
-/
public theorem raw_positiveProduct : (entries : List PositiveEntry) →
    (margins : ∀ index : Fin entries.length, Certificate (entries.get index).part.polynomial) →
    (counts : Fin entries.length → Nat) →
    (∀ index : Fin entries.length, (paths : Boundary.Substitutions (entries.get index).part.polynomial) →
      raw paths = 4 * (counts index : Int)) →
    (paths : Boundary.Substitutions (Product.positivePolynomial entries)) →
    raw paths = 4 * (((List.ofFn (fun index : Fin entries.length =>
      (entries.get index).multiplicity * counts index)).foldr Nat.add 0 : Nat) : Int)
  | [], _, _, _, paths => by
      change raw paths = 0
      exact raw_constant 1 paths
  | head :: remaining, margins, counts, readings, paths => by
      let headPaths := Boundary.Substitutions.prepare head.part.polynomial
      let powerPaths := Boundary.Substitutions.prepare (Power.polynomialPower head.part.polynomial head.multiplicity)
      let tailPaths := Boundary.Substitutions.prepare (Product.positivePolynomial remaining)
      let tailMargins := fun index : Fin remaining.length => margins index.succ
      have product := raw_mul ((margins 0).power head.multiplicity)
        (Certificate.positiveProduct remaining tailMargins) powerPaths tailPaths paths
      have headReading := raw_power (margins 0) headPaths head.multiplicity powerPaths
      have tailReading := raw_positiveProduct remaining tailMargins (fun index => counts index.succ)
        (fun index => readings index.succ) tailPaths
      rw [readings 0 headPaths] at headReading
      rw [headReading, tailReading] at product
      rw [List.OfFn.Basic.ofFn_succ]
      change raw paths = 4 * ((head.multiplicity * counts 0 +
        (List.ofFn (fun index : Fin remaining.length =>
          (remaining.get index).multiplicity * counts index.succ)).foldr Nat.add 0 : Nat) : Int)
      rewrite [NatCast.add, NatCast.mul]
      exact product.trans (by ring1)

end Purelib.Polynomial.Winding.Circle
