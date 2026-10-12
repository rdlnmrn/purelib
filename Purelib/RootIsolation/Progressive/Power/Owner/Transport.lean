module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Power.Gaussian
public import Purelib.Polynomial.Power.Gaussian.Perturbation
import Purelib.Polynomial.Winding.Box.Rouche.Connection
public import Purelib.RootIsolation.Owner.Bridge.Rouche
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.Owner.Bridge.Basic

open Purelib.RootIsolation.Owner.Local.Basic (LocalOwner)

open Purelib.Data

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

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

namespace Purelib.RootIsolation.Progressive.Power.Owner.Transport

open Purelib.Data.Gaussian

/-- A constant parameter displacement smaller than one owner's displayed
boundary clearance supplies the complete finite Rouché comparison. -/
def ownerMoveRouche
    {source target : Gaussian.Basic.Canonical} (degree : Data.Nat.Positive.RootDegree)
    (owner : LocalOwner
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree))
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) < owner.clearance.bound) :
    Winding.Box.Rouche.Connection.OrientedRouche
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree) (Purelib.Polynomial.Power.Gaussian.rootPolynomial
        target
        degree) owner.box where
  perturbation := Power.Gaussian.Perturbation.parameterPerturbation source target
  target_eq_add := Power.Gaussian.Perturbation.polynomial_target_eq_add_perturbation source target degree
  dominance :=
    { margin := owner.clearance.bound - Data.Gaussian.Norm.Basic.normSq (source - target)
      positive := Purelib.Data.Rat.Fraction.Order.Arithmetic.sub_pos_direct small
      lower := by
        intro point boundary
        rw [Power.Gaussian.Perturbation.parameterPerturbation_eval]
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
          (Purelib.Data.Rat.Fraction.Order.Arithmetic.sub_le_sub_right_direct
            (owner.clearance.lower point boundary) (Data.Gaussian.Norm.Basic.normSq (source - target))) }
end Purelib.RootIsolation.Progressive.Power.Owner.Transport

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

namespace Purelib.RootIsolation.Progressive.Power.Owner.Transport

open Purelib.Data.Gaussian

/-- The old rational owner box, read at the new parameter after the
constant-coefficient Rouché move. -/
def transportedOwner
    {source target : Gaussian.Basic.Canonical} (degree : Data.Nat.Positive.RootDegree)
    (owner : LocalOwner
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree))
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) < owner.clearance.bound) :
    LocalOwner
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree) :=
  (Owner.Bridge.Basic.OwnerBridge.ofForward owner
    (ownerMoveRouche degree owner small)).rightOwner
end Purelib.RootIsolation.Progressive.Power.Owner.Transport

end
