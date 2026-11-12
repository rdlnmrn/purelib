module

public import Purelib.Polynomial.Laurent.Toeplitz
public import Purelib.RootIsolation.Multiplicity.Circle.Comparison.Shift

/-!
# Nonminimal polynomializing shifts of the same Laurent index

The additional polynomial has its own original automatic root inventory.
Its added zero roots compensate the larger polynomializing shift. The
recurrence ledger remains the one at the original minimal Laurent pole order.
-/

namespace Purelib.Polynomial.Laurent.Toeplitz.Comparison

open Basic (LaurentPolynomial)
open Normalization (Normalized)
open Dense.Basic (DensePolynomial)
open Purelib.RationalFunctions.Curve.Canonical.Circle

/-- The actual shifted polynomial inventory gives the same original recurrence index after pole compensation. -/
public theorem nonminimal_index {source : LaurentPolynomial} {normalized : Normalized source}
    {paths : Boundary.Substitutions normalized.polynomial} {clearance : Boundary.Clearance paths}
    (comparison : Comparison normalized paths clearance) (extra : Nat)
    {shiftedPaths : Boundary.Substitutions (DensePolynomial.shift extra normalized.polynomial)}
    {shiftedClearance : Boundary.Clearance shiftedPaths}
    (shifted : RootIsolation.Multiplicity.Circle.Comparison shiftedPaths shiftedClearance) :
    ((normalized.poleOrder + extra : Nat) : Int) - (shifted.inventory.insideCount : Int) =
      comparison.index :=
  (comparison.circle.polynomial.shift_balance normalized.poleOrder extra shifted).trans comparison.index_eq.symm

end Purelib.Polynomial.Laurent.Toeplitz.Comparison
