module

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
meta import Purelib.Elab.Deriving.Repr

open Purelib

open Purelib.Data.Rat

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

namespace Purelib.Geometry.Gaussian.UnitCircle.Quarter
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- Four successive rotations of the primary rational quarter chart. -/
inductive UnitCircuitQuarter
  /-- The first quarter of the unit-circle circuit. -/ | first
  /-- The second quarter of the unit-circle circuit. -/ | second
  /-- The third quarter of the unit-circle circuit. -/ | third
  /-- The fourth quarter of the unit-circle circuit. -/ | fourth
deriving DecidableEq
derive_exposed_repr UnitCircuitQuarter
end Purelib.Geometry.Gaussian.UnitCircle.Quarter

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

namespace Purelib.Geometry.Gaussian.UnitCircle.Quarter
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The quarter-turn multiplier `1`, `i`, `-1`, or `-i` for the selected circuit quarter. -/
def unitCircuitMultiplier :
  UnitCircuitQuarter → Data.Gaussian.Basic.Canonical
  | .first => ⟨1, 0⟩
  | .second => ⟨0, 1⟩
  | .third => ⟨-1, 0⟩
  | .fourth => ⟨0, -1⟩
end Purelib.Geometry.Gaussian.UnitCircle.Quarter

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

namespace Purelib.Geometry.Gaussian.UnitCircle.Quarter
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- Every circuit-quarter multiplier has quadrance one. -/
theorem unitCircuitMultiplier_unit (quarter :
  UnitCircuitQuarter) :
    Data.Gaussian.Norm.Basic.normSq (unitCircuitMultiplier quarter) = 1 :=
      by
  cases quarter <;> decide
end Purelib.Geometry.Gaussian.UnitCircle.Quarter

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

namespace Purelib.Geometry.Gaussian.UnitCircle.Quarter
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The quadrance-two Gaussian multiplier aligning the selected circuit quarter.

Multiplying it by the quarter-turn multiplier always gives `1 - i`. -/
def unitCircuitRotation :
  UnitCircuitQuarter → Data.Gaussian.Basic.Canonical
  | .first => ⟨1, -1⟩
  | .second => ⟨-1, -1⟩
  | .third => ⟨-1, 1⟩
  | .fourth => ⟨1, 1⟩
end Purelib.Geometry.Gaussian.UnitCircle.Quarter

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

namespace Purelib.Geometry.Gaussian.UnitCircle.Quarter
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The aligning multiplier times the circuit-quarter multiplier is `1 - i`. -/
theorem unitCircuitRotation_mul_multiplier
    (quarter : UnitCircuitQuarter) :
    unitCircuitRotation quarter *
      unitCircuitMultiplier quarter =
      ⟨1, -1⟩ := by
  cases quarter <;> decide
end Purelib.Geometry.Gaussian.UnitCircle.Quarter

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

namespace Purelib.Geometry.Gaussian.UnitCircle.Quarter
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- Every circuit alignment multiplier has quadrance two. -/
theorem unitCircuitRotation_normSq (quarter :
  UnitCircuitQuarter) :
    Data.Gaussian.Norm.Basic.normSq (unitCircuitRotation quarter) = 2 :=
      by
  cases quarter <;> decide
end Purelib.Geometry.Gaussian.UnitCircle.Quarter

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

namespace Purelib.Geometry.Gaussian.UnitCircle.Quarter
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- Every circuit alignment multiplier is nonzero. -/
theorem unitCircuitRotation_ne_zero (quarter :
  UnitCircuitQuarter) :
    unitCircuitRotation quarter ≠ 0 := by
  intro zero
  have normZero := congrArg Data.Gaussian.Norm.Basic.normSq zero
  rw [unitCircuitRotation_normSq, Data.Gaussian.Norm.Basic.normSq_zero] at normZero
  exact (by decide : (2 : Fraction.Rational) ≠ 0) normZero
end Purelib.Geometry.Gaussian.UnitCircle.Quarter

end
