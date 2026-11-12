module

public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages
public import Purelib.Polynomial.Dense.Map.Reading

/-!
# Original factor caches for retained stage readings

The mapped factor of an original context retains its original coefficient
map. A Gaussian reading of that same algebra reads its scalar images
exactly, so the original Gaussian factor itself supplies the observed cache.
No formal coefficient table needs to be remapped at runtime.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Algebra.Ring (Weight GaussianReading)
open Purelib.Data.Gaussian.Basic (Canonical)

variable {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}
variable {K : Type*} [CommRing K] {function : Canonical → K} {parent : Weight K}

/-- The same original context factor is the exact observed cache of its retained mapped polynomial.

The equality is oriented for constructors consuming an existing observed
polynomial. Only exact scalar readback is used; the parent reading may have
a nonzero multiplication error on other elements of the original algebra.
-/
theorem factor_eq_map (reading : GaussianReading parent function) {index : Fin contexts.length}
    {mapped : DensePolynomial K} (mappedEq : mapped = Dense.Map.map function (factor contexts index)) :
    factor contexts index = Dense.Map.map reading.read mapped :=
  Dense.Map.source_eq_read reading (factor contexts index) mapped mappedEq

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading

end
