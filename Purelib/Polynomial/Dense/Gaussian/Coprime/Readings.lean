module

public import Purelib.Polynomial.Dense.Gaussian.Coprime.Identity
public import Purelib.Data.Vector.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cached interpreted original Bezout cofactor readings

One original Gaussian coprimality certificate supplies the same mapped
right cofactor at each original bounded point occurrence. The cofactor is
mapped once and its readings are materialized once in the original vector.
Each reading inverts the other input value at a root of the first input.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Coprime

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Coprime.Basic (CoprimeCertificate)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic

variable {K : Type*} [CommRing K] [DecidableEq K] {A : Type*}
variable {first second : DensePolynomial Canonical}

set_option genInjectivity false in
/-- The same original certificate's mapped cofactor and actual inverse readings at retained point occurrences.

The original item list and bounded projection retain every point's original
owner and index. The right polynomial and reading vector are actual caches;
the unit equation concerns the same interpreted second input at that point.
-/
structure Readings (certificate : CoprimeCertificate first second) (function : Canonical → K)
    (items : List A) (point : Fin items.length → K) where
  /-- The same retained original certificate supplying the mapped cofactor. -/
  original : CoprimeCertificate first second
  /-- The retained original data is exactly the supplied certificate. -/
  original_eq : original = certificate
  /-- The original right Bezout cofactor mapped once through the same coefficient function. -/
  right : DensePolynomial K
  /-- The retained cofactor maps exactly the original certificate's right polynomial. -/
  right_eq : right = Dense.Map.map function certificate.right
  /-- The actual original vector of once-evaluated cofactor readings. -/
  inverses : Vec K items.length
  /-- Every retained vector entry reads the same mapped cofactor at its original bounded point. -/
  inverses_eq : ∀ index, inverses index = right.eval (point index)
  /-- Each same retained reading is an explicit inverse of the original second input value. -/
  unit : ∀ index, (Dense.Map.map function second).eval (point index) * inverses index = 1

constructive_injectivity Readings

namespace Readings

/-- Map the original right cofactor once and evaluate it once per original point occurrence.

Original first-input vanishing is a proof prerequisite. The resulting
explicit second-value units follow from the same retained original Bezout
identity over an arbitrary commutative target ring, including zero divisors.
-/
@[expose] def prepare (certificate : CoprimeCertificate first second)
    (function : Canonical → K) (mapZero : function 0 = 0) (injective : Function.Injective function)
    (mapOne : function 1 = 1)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapMul : ∀ left right, function (left * right) = function left * function right)
    (items : List A) (point : Fin items.length → K)
    (vanishes : ∀ index, (Dense.Map.map function first).eval (point index) = 0) :
    Readings certificate function items point :=
  let right := Dense.Map.map function certificate.right
  let inverses := vectorOfFn fun index => right.eval (point index)
  { original := certificate
    original_eq := rfl
    right := right
    right_eq := rfl
    inverses := inverses
    inverses_eq := fun index => vectorOfFn_apply _ index
    unit := by
      intro index
      rewrite [vectorOfFn_apply]
      exact certificate.right_unit function mapZero injective mapOne mapAdd mapMul (point index) (vanishes index) }

end Readings

end Purelib.Polynomial.Dense.Gaussian.Coprime

end
