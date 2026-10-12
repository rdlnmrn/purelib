module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Finite literal checks for certified prepared centres

A rounded literal need not be a witness of a root or coefficient process.
Instead, retain an actual certified centre state and check its squared
distance from the literal.  The checked distance is cached with its exact
specification.  Failure rejects this shortcut only; callers may retain an
existing total comparison construction as their fallback.
-/

namespace Purelib.Riemann.Integration.PreparedLiteralCenters

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Riemann.Integration.PreparedConstantModels

section
open Purelib.Data
/-- Rational squared distances and error allowances. -/
abbrev Coordinate := Rat.Fraction.Rational
/-- Gaussian rational literal and center values. -/
abbrev Gaussian := Gaussian.Basic.Canonical

end

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Curves in
set_option genInjectivity false in
/-- A prepared center with a cached bound on its distance from a literal.

The retained center belongs to the supplied prepared edge; the literal itself need not be a witness of its coefficient
process. -/
structure Certificate {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus} (prepared : PreparedEdge curve differential)
    (literal : Gaussian) (allowance : Coordinate) where
  /-- The retained certified center of the prepared edge. -/ center : PreparedEdge.CenterState prepared
  /-- The cached squared distance between the literal and the center. -/ distanceSq : Coordinate
  /-- The cache equals the exact squared Gaussian distance. -/ distanceSq_eq : distanceSq = normSq (literal -
    center.value)
  /-- The cached distance fits the supplied allowance. -/ within : distanceSq ≤ allowance

constructive_injectivity Certificate

open Purelib.Curves in
/-- Recover the literal-to-center distance bound from its certificate. -/
theorem Certificate.error_le {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus} {prepared : PreparedEdge curve differential}
    {literal : Gaussian} {allowance : Coordinate}
    (certificate : Certificate prepared literal allowance) :
    normSq (literal - certificate.center.value) ≤ allowance := by
  rw [← certificate.distanceSq_eq]
  exact certificate.within

section
open Purelib.Curves
/-- Check and cache a literal's squared distance from a certified center.

Return the retained certificate exactly when the distance fits the allowance; an unsuccessful check returns none. -/
def check {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus} {prepared : PreparedEdge curve differential}
    (center : PreparedEdge.CenterState prepared) (literal : Gaussian)
    (allowance : Coordinate) : Option (Certificate prepared literal allowance) :=
  let distanceSq := normSq (literal - center.value)
  if within : distanceSq ≤ allowance then
    some ⟨center, distanceSq, rfl, within⟩
  else none

/-- The literal check returns none when the allowance is strictly below the actual distance. -/
theorem check_rejects {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus} {prepared : PreparedEdge curve differential}
    (center : PreparedEdge.CenterState prepared) (literal : Gaussian)
    (allowance : Coordinate) (tooLarge : allowance < normSq (literal - center.value)) :
    check center literal allowance = none := by
  unfold check
  rw [dif_neg (not_le_of_gt tooLarge)]

/-- Check a literal against the canonical center of the prepared edge. -/
def canonical? {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus} (prepared : PreparedEdge curve differential)
    (literal : Gaussian) (allowance : Coordinate) :
    Option (Certificate prepared literal allowance) :=
  check (PreparedEdge.CenterState.canonical prepared) literal allowance

end

open Purelib.Curves in
open Purelib.Data in
/-- Certify a literal by comparing it and the prepared center through a common value.

Two squared errors bounded by the same error give a literal-to-center allowance of four times that error; only the
certified center and actual distance are retained. -/
def ofTwoErrors {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus} {prepared : PreparedEdge curve differential}
    (center : PreparedEdge.CenterState prepared) (literal bridge : Gaussian)
    (error : Coordinate) (bridgeError : normSq (bridge - literal) ≤ error)
    (close : normSq (bridge - center.value) < error) :
    Certificate prepared literal (4 * error) where
  center := center
  distanceSq := normSq (literal - center.value)
  distanceSq_eq := rfl
  within := by
    have reverse : literal - bridge = -(bridge - literal) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.neg_re, Gaussian.Basic.neg_im] <;> ring1
    have literalError : normSq (literal - bridge) ≤ error := by
      rw [reverse, Gaussian.Basic.Canonical.normSq_neg]
      exact bridgeError
    have identity : literal - center.value =
        (literal - bridge) + (bridge - center.value) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;> ring1
    rw [identity]
    have triangle := Gaussian.Norm.Bounds.normSq_add_le_two (literal - bridge) (bridge - center.value)
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at triangle
    exact triangle.trans
      ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add literalError close.le) (by decide)).trans_eq (by ring1))

end Purelib.Riemann.Integration.PreparedLiteralCenters
