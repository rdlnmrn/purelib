module

public import Purelib.Polynomial.Laurent.Circle.Transport
import Purelib.Tactic.QuotientFreeOmega

/-!
# Actual inside and outside counts under Laurent transports

The original source and actual transformed comparison each retain their own
complete root inventory. Reversal and adjoint exchange the nonzero radial
classes; the actual target zero roots remain inside, and the original zero
roots have no outside counterpart.
-/

namespace Purelib.Polynomial.Laurent.Circle.Transport.Comparison

open Basic (LaurentPolynomial)
open Normalization (Normalized)
open Dense.Basic (DensePolynomial)
open Dense.Gaussian
open Purelib.RationalFunctions.Curve.Canonical.Circle

variable {source : LaurentPolynomial} {normalized : Normalized source}
variable {sourcePaths : Boundary.Substitutions normalized.polynomial}
variable {sourceClearance : Boundary.Clearance sourcePaths}
variable {original : Circle.Comparison normalized sourcePaths sourceClearance}

/-- Coefficient conjugation preserves both actual radial inventory counts, including the retained zero roots. -/
public theorem conjugate_locations (comparison : Comparison original source.conjugate .preserving) :
    comparison.result.polynomial.inventory.insideCount = original.polynomial.inventory.insideCount ∧
      comparison.result.polynomial.inventory.outsideCount = original.polynomial.inventory.outsideCount := by
  cases comparison with
  | mk symbol symbolEq target targetEq paths pathsEq margin bound clearance clearanceEq result resultEq windingEq =>
      cases symbolEq
      change result.polynomial.inventory.insideCount = original.polynomial.inventory.insideCount ∧
        result.polynomial.inventory.outsideCount = original.polynomial.inventory.outsideCount
      have raw := conjugate_raw normalized original.polynomial.margin.toCertificate target sourcePaths paths
      rewrite [result.polynomial.raw_eq, original.polynomial.raw_eq] at raw
      have firstTotal := original.polynomial.total
      have secondTotal := result.polynomial.total
      have degrees := congrArg DensePolynomial.natDegree (normalized.conjugate_polynomial target)
      rewrite [Conjugate.natDegree] at degrees
      constructor
      · omega0
      · omega0

/-- Exponent reversal exchanges the actual nonzero radial classes, retaining both zero-root compensations. -/
public theorem reverse_locations (comparison : Comparison original source.reverse .reversing) :
    comparison.result.polynomial.inventory.insideCount =
        original.polynomial.inventory.outsideCount + comparison.normalized.zeroMultiplicity ∧
      comparison.result.polynomial.inventory.outsideCount + normalized.zeroMultiplicity =
        original.polynomial.inventory.insideCount := by
  cases comparison with
  | mk symbol symbolEq target targetEq paths pathsEq margin bound clearance clearanceEq result resultEq windingEq =>
      cases symbolEq
      change result.polynomial.inventory.insideCount =
          original.polynomial.inventory.outsideCount + target.zeroMultiplicity ∧
        result.polynomial.inventory.outsideCount + normalized.zeroMultiplicity =
          original.polynomial.inventory.insideCount
      have raw := reverse_raw normalized original.polynomial.margin.toCertificate target sourcePaths paths
      rewrite [result.polynomial.raw_eq, original.polynomial.raw_eq] at raw
      have firstTotal := original.polynomial.total
      have secondTotal := result.polynomial.total
      have firstDegree := normalized.polynomial_degree
      have secondDegree := target.polynomial_degree
      have firstZero := normalized.zeroMultiplicity_eq
      have secondZero := target.zeroMultiplicity_eq
      have lower := normalized.reverse_lower target
      have upper := normalized.reverse_upper target
      constructor
      · omega0
      · omega0

/-- Adjoint has the same actual zero-corrected radial exchange as exponent reversal. -/
public theorem adjoint_locations (comparison : Comparison original source.adjoint .reversing) :
    comparison.result.polynomial.inventory.insideCount =
        original.polynomial.inventory.outsideCount + comparison.normalized.zeroMultiplicity ∧
      comparison.result.polynomial.inventory.outsideCount + normalized.zeroMultiplicity =
        original.polynomial.inventory.insideCount := by
  cases comparison with
  | mk symbol symbolEq target targetEq paths pathsEq margin bound clearance clearanceEq result resultEq windingEq =>
      cases symbolEq
      change result.polynomial.inventory.insideCount =
          original.polynomial.inventory.outsideCount + target.zeroMultiplicity ∧
        result.polynomial.inventory.outsideCount + normalized.zeroMultiplicity =
          original.polynomial.inventory.insideCount
      have raw := adjoint_raw normalized original.polynomial.margin.toCertificate target sourcePaths paths
      rewrite [result.polynomial.raw_eq, original.polynomial.raw_eq] at raw
      have firstTotal := original.polynomial.total
      have secondTotal := result.polynomial.total
      have firstDegree := normalized.polynomial_degree
      have secondDegree := target.polynomial_degree
      have firstZero := normalized.zeroMultiplicity_eq
      have secondZero := target.zeroMultiplicity_eq
      have lower := normalized.adjoint_lower target
      have upper := normalized.adjoint_upper target
      constructor
      · omega0
      · omega0

end Purelib.Polynomial.Laurent.Circle.Transport.Comparison
