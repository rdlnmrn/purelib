module

public import Purelib.RootIsolation.Multiplicity.Circle.Comparison
public import Purelib.Polynomial.Winding.Circle.Operations
import Purelib.Tactic.QuotientFreeOmega

/-!
# Actual radial inventory compensation under a coordinate shift

Both complete inventories are those retained by the original automatic circle
comparisons. Their independent phase readings prove that a coordinate shift
adds precisely its exponent to the actual inside multiplicity.
-/

namespace Purelib.RootIsolation.Multiplicity.Circle.Comparison

open Purelib.Polynomial
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Dense.Basic (DensePolynomial)

/-- Independently constructed original inventories acquire exactly the shifted zero multiplicity inside the circle. -/
public theorem shift_insideCount {polynomial : CoefficientPolynomial}
    {paths : Boundary.Substitutions polynomial} {clearance : Boundary.Clearance paths}
    (comparison : Comparison paths clearance) (exponent : Nat)
    {shiftedPaths : Boundary.Substitutions (DensePolynomial.shift exponent polynomial)}
    {shiftedClearance : Boundary.Clearance shiftedPaths}
    (shifted : Comparison shiftedPaths shiftedClearance) :
    shifted.inventory.insideCount = comparison.inventory.insideCount + exponent := by
  have shiftedRaw := Winding.Circle.raw_shift comparison.margin.toCertificate paths exponent shiftedPaths
  rewrite [shifted.raw_eq, comparison.raw_eq] at shiftedRaw
  omega0

/-- Adding the same shift to the pole count and the actual inside inventory leaves their signed difference unchanged. -/
public theorem shift_balance {polynomial : CoefficientPolynomial}
    {paths : Boundary.Substitutions polynomial} {clearance : Boundary.Clearance paths}
    (comparison : Comparison paths clearance) (pole exponent : Nat)
    {shiftedPaths : Boundary.Substitutions (DensePolynomial.shift exponent polynomial)}
    {shiftedClearance : Boundary.Clearance shiftedPaths}
    (shifted : Comparison shiftedPaths shiftedClearance) :
    ((pole + exponent : Nat) : Int) - (shifted.inventory.insideCount : Int) =
      (pole : Int) - (comparison.inventory.insideCount : Int) := by
  rewrite [comparison.shift_insideCount exponent shifted]
  omega0

end Purelib.RootIsolation.Multiplicity.Circle.Comparison
