module

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Basic
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-! ### The certified finite chamber loop -/

set_option genInjectivity false in
/-- A displayed rational parameter together with its exact unit-norm certificate. -/
structure UnitVertex where
  /-- The retained Gaussian rational point. -/ value : Data.Gaussian.Basic.Canonical
  /-- The retained point has quadrance one. -/ unit : Data.Gaussian.Norm.Basic.normSq value = 1

constructive_injectivity UnitVertex

end Purelib.Geometry.Gaussian.UnitCircle.Basic

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Basic.UnitVertex
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian
section

/-- Unit-circle vertices are equal when their retained Gaussian points are equal. -/
theorem eq_of_value_eq {left right :
  UnitVertex}
    (same : left.value = right.value) : left = right := by
  cases left with
  | mk leftValue leftUnit =>
      cases right with
      | mk rightValue rightUnit =>
          dsimp only at same
          subst rightValue
          rfl

end
end Purelib.Geometry.Gaussian.UnitCircle.Basic.UnitVertex

end
