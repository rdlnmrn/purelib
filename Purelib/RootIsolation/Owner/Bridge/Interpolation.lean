module

public import Purelib.RootIsolation.Owner.Bridge.Rouche
public import Purelib.RootIsolation.Owner.Bridge.Transport
public import Purelib.Polynomial.Winding.Box.Rouche.Connection.Interpolation
import Purelib.RootIsolation.Owner.Local.Transport
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Owner.Local.Basic (LocalOwner)
open Purelib.Polynomial.Winding.Box.Rouche.Connection (OrientedRouche RoucheConnection)
open Purelib.Geometry.Rational (Box)
open Purelib.RootIsolation.Owner

public section

namespace Purelib.RootIsolation.Owner.Bridge.Basic.OwnerBridge

/-- Reindexing both bridge endpoints preserves its complete original interpolation polynomial. -/
theorem cast_polynomialAt {left left' right right' : CoefficientPolynomial}
    (leftSame : left = left') (rightSame : right = right')
    (bridge : OwnerBridge left right) (time : Rational) :
    (bridge.cast leftSame rightSame).connection.polynomialAt time =
      bridge.connection.polynomialAt time := by
  cases leftSame
  cases rightSame
  rfl

/-- Construct the actual original-box owner bridge to one rational coefficient reading.

The zero endpoint retains the original base owner. The unit endpoint reuses
the original oriented certificate. Interior parameters scale that same
perturbation and retain its positive boundary-dominance margin.
-/
@[expose] def ofInterpolation {base target : CoefficientPolynomial}
    (owner : LocalOwner base) (certificate : OrientedRouche base target owner.box)
    (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) :
    OwnerBridge base (certificate.polynomialAt time) :=
  if zero : time = 0 then
    (reflexive owner).cast rfl (by rw [zero, certificate.at_zero])
  else if one : time = 1 then
    (ofForward owner certificate).cast rfl (by rw [one, certificate.at_one])
  else
    (ofForward owner (certificate.scaled time inside)).cast rfl
      (by rw [OrientedRouche.polynomialAt, if_neg zero, if_neg one])

/-- Every constructed interpolation bridge retains the exact original owner box. -/
theorem ofInterpolation_box {base target : CoefficientPolynomial}
    (owner : LocalOwner base) (certificate : OrientedRouche base target owner.box)
    (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) :
    (ofInterpolation owner certificate time inside).box = owner.box := by
  unfold ofInterpolation
  split
  · exact cast_box _ _ _
  · split <;> exact cast_box _ _ _

/-- Every constructed interpolation bridge retains its complete original base-side owner. -/
theorem ofInterpolation_leftOwner {base target : CoefficientPolynomial}
    (owner : LocalOwner base) (certificate : OrientedRouche base target owner.box)
    (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) :
    (ofInterpolation owner certificate time inside).leftOwner = owner := by
  unfold ofInterpolation
  split
  · rw [cast_leftOwner]
    rfl
  · split <;> rw [cast_leftOwner] <;> rfl

/-- Read the winding-one owner of each interior coefficient polynomial on the exact original bridge box.

Both endpoint branches retain the bridge's complete original endpoint owner,
including its actual clearance and winding witnesses. Interior readings use
the original dominant endpoint chosen by the retained Rouché orientation.
No squarefreeness or identification between distinct root ambients is inferred.
-/
@[expose] def ownerAt {left right : CoefficientPolynomial} (bridge : OwnerBridge left right)
    (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) : LocalOwner (bridge.connection.polynomialAt time) :=
  if zero : time = 0 then
    Local.Transport.castOwner (by rw [zero, bridge.connection.at_zero]) bridge.leftOwner
  else if one : time = 1 then
    Local.Transport.castOwner (by rw [one, bridge.connection.at_one]) bridge.rightOwner
  else
    match bridge.connection with
    | .equal _ => bridge.leftOwner
    | .forward certificate => (ofInterpolation bridge.leftOwner certificate time inside).rightOwner
    | .backward certificate =>
        (ofInterpolation bridge.rightOwner certificate (1 - time)
          (RoucheConnection.complement_inside time inside)).rightOwner

/-- The zero-parameter owner is the complete original left owner after its endpoint index readback. -/
theorem ownerAt_zero {left right : CoefficientPolynomial} (bridge : OwnerBridge left right)
    (inside : (0 : Rational) ≤ 0 ∧ (0 : Rational) ≤ 1) :
    Local.Transport.castOwner bridge.connection.at_zero (bridge.ownerAt 0 inside) = bridge.leftOwner := by
  rw [ownerAt, dif_pos rfl]
  exact Local.Transport.castOwner_inverse bridge.connection.at_zero.symm bridge.leftOwner

/-- The unit-parameter owner is the complete original right owner after its endpoint index readback. -/
theorem ownerAt_one {left right : CoefficientPolynomial} (bridge : OwnerBridge left right)
    (inside : (0 : Rational) ≤ 1 ∧ (1 : Rational) ≤ 1) :
    Local.Transport.castOwner bridge.connection.at_one (bridge.ownerAt 1 inside) = bridge.rightOwner := by
  rw [ownerAt, dif_neg (by decide), dif_pos rfl]
  exact Local.Transport.castOwner_inverse bridge.connection.at_one.symm bridge.rightOwner

/-- Every rational-parameter owner retains the exact original bridge box. -/
theorem ownerAt_box {left right : CoefficientPolynomial} (bridge : OwnerBridge left right)
    (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) :
    (bridge.ownerAt time inside).box = bridge.box := by
  unfold ownerAt
  split
  · exact Local.Transport.castOwner_box _ _
  · split
    · exact Local.Transport.castOwner_box _ _
    · cases bridge.connection with
      | equal same => rfl
      | forward certificate => exact ofInterpolation_box bridge.leftOwner certificate time inside
      | backward certificate =>
          exact (ofInterpolation_box bridge.rightOwner certificate (1 - time)
            (RoucheConnection.complement_inside time inside))

end Purelib.RootIsolation.Owner.Bridge.Basic.OwnerBridge

end
