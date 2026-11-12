module

public import Purelib.Polynomial.Dense.Map.Basic
public import Purelib.Algebra.Ring.GaussianReading
import Purelib.Data.List.Map

/-!
# Exact coefficient readback of original Gaussian scalar images

A Gaussian reading recovers every displayed original scalar coefficient
exactly. The same structural polynomial map therefore recovers the whole
original table, including nonmonic coefficients and zero slots, without
requiring multiplicativity on the surrounding coefficient algebra.
-/

public section

namespace Purelib.Polynomial.Dense.Map

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Algebra.Ring (Weight GaussianReading)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data

variable {K : Type*} [CommRing K] {weight : Weight K} {scalar : Canonical → K}

/-- Reading the same original scalar-mapped polynomial recovers all original Gaussian coefficients. -/
theorem read_scalar (reading : GaussianReading weight scalar) (polynomial : DensePolynomial Canonical) :
    map reading.read (map scalar polynomial) = polynomial := by
  rewrite [map_map]
  have pointwise : polynomial.coeffs.map (reading.read ∘ scalar) = polynomial.coeffs.map id :=
    List.Map.map_congr_left (fun coefficient _ => reading.read_scalar coefficient)
  exact (DensePolynomial.ext pointwise).trans (map_id polynomial)

/-- The same original Gaussian polynomial is a valid observed cache for any retained mapped table. -/
theorem source_eq_read (reading : GaussianReading weight scalar)
    (polynomial : DensePolynomial Canonical) (mapped : DensePolynomial K)
    (mappedEq : mapped = map scalar polynomial) : polynomial = map reading.read mapped :=
  ((congrArg (map reading.read) mappedEq).trans (read_scalar reading polynomial)).symm

end Purelib.Polynomial.Dense.Map

end
