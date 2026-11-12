module

import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bounds.Family
import Purelib.Polynomial.Winding.Circle.Operations

/-!
# Bound families from actual mixed multiplicity preprocessing

The original source has one zero and a double exterior linear root.
Automatic original preprocessing, observations, locations and arguments
supply both family entries, whose cached radii and endpoints are checked
in the unchanged original context order.
-/

namespace TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bounds.Family

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Purelib.RootIsolation.Multiplicity.Circle
open Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading (Bounds)

/-- The normalized original source is the actual product `z(z-2)^2`. -/
private def source : CoefficientPolynomial := ⟨[1, -4, 4, 0]⟩

/-- The same original exterior linear margin and unit monomial give a whole-circle source certificate. -/
private def clearance : Certificate source :=
  have same : DensePolynomial.shift 1 (Power.polynomialPower (LinearFactor.linearFactor 2) 2) = source :=
    by decide +kernel
  same ▸ ((Certificate.linearOutside 2 (by decide +kernel)).power 2).shift 1

/-- The original automatic inventory retains its actual mixed multiplicity preprocessing and physical locations. -/
private def inventory := Inventory.prepare clearance (by decide +kernel)

/-- Read the cached family at the same original positive contexts after their actual arguments are prepared.

Rows retain the original focused multiplicity and all three stored scalar
bounds. The positive branch prepares its actual argument payload once and
uses the original context order for the cached-bound readout.
-/
private def rows : List (Nat × Rational × Rational × Rational) :=
  match inventory.side, inventory.locations with
  | .constant _ _ _, _ => []
  | .positive input _, locations =>
      let argument := PositiveArgument.prepare locations
      let retained := Bounds.Family.prepare argument
      List.ofFn (fun index : Fin input.contexts.length =>
        ((input.contexts.get index).focus.multiplicity, retained.radii index,
          (retained.boundsAt index).ceiling, (retained.boundsAt index).floor))

/-- The actual original exterior and zero contexts have the independently calculated cached physical bounds. -/
private theorem original_rows : rows = [(2, 5, 4, 4), (1, 1, 0, 0)] := by decide +kernel

end TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bounds.Family
