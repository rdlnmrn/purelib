module

import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.Inverse
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Geometry.Rotations.Reflection
import Purelib.LinearAlgebra.Coordinates3.Antisymmetric
import Purelib.Geometry.Rotations.Cayley.Cap
import Purelib.Geometry.Rotations.Basic
import Purelib.Algebra.Field.Squares
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Squares.Witness
public import Purelib.Geometry.Rotations.Axis.Parameters
public import Purelib.Geometry.Quadratic.Space3.NullVectors
import Purelib.Geometry.Rotations.Axis.Recovery
public import Purelib.Geometry.Rotations.Orientation.Handedness
import Purelib.Geometry.Rotations.Spread
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Tactic.Ring

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Algebra.Field

open Purelib.Algebra.Field.Squares

open Purelib.Geometry

open Purelib.Geometry.Quadratic.Space3

open Purelib.Geometry.Rotations

open Purelib.Geometry.Rotations.Axis

open Purelib.Geometry.Rotations.Cayley

open Purelib.Geometry.Rotations.Orientation

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3

section
public section

/-!
# Rational rotations, Theorem 65 and Examples 66--67

The square condition for a prescribed axis and half spread is carried by an
explicit nonzero root.  From that root we compute the two opposite anchor
vectors and hence the two inverse rotations.  No square-root operation or
choice principle enters the construction.
-/

namespace Purelib.Geometry.Rotations.Axis.Prescribed

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The finite square test occurring in Theorem 65. -/
@[expose] def prescribedAxisSquareValue (axis : Coordinates3.Vector K)
  (spread : K) : K :=
  axis.quadrance * spread * (1 - spread)

set_option genInjectivity false in
/-- A rotation with prescribed non-half-turn axis line and half spread. The nonzero scalar explicitly records equality
of projective axis lines. -/
structure PrescribedAxisRotation (axis : Coordinates3.Vector K)
  (spread : K) where
  /-- The retained rotation with the prescribed axis and half spread. -/ rotation : Rotations.Basic.Rotation K
  /-- The retained rotation has half spread different from one. -/ notHalfTurn : Spread.halfSpread rotation ≠ 1
  /-- The retained rotation has exactly the requested half spread. -/ halfSpread_eq : Spread.halfSpread rotation =
    spread
  /-- The retained scalar relating the recovered anchor to the requested axis. -/ anchorScale : K
  /-- The retained projective axis scale is nonzero. -/ anchorScaleNonzero : anchorScale ≠ 0
  /-- The recovered anchor is exactly the requested axis multiplied by the retained scale. -/ anchor_eq :
    Recovery.rotationAnchorVector rotation notHalfTurn =
    Coordinates3.Vector.scale anchorScale axis

constructive_injectivity PrescribedAxisRotation

/-- Necessity in Theorem 65: a displayed rotation with the requested axis and nonzero, non-unit half spread supplies a
nonzero square root. -/
@[expose] def PrescribedAxisRotation.squareCertificate
    {axis : Coordinates3.Vector K} {spread : K}
    (candidate : PrescribedAxisRotation axis spread)
    (axisNonNull : axis.quadrance ≠ 0)
    (spreadNotOne : spread ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Witness.NonzeroSquare (Purelib.Geometry.Rotations.Axis.Prescribed.prescribedAxisSquareValue axis spread) where
  root := candidate.anchorScale * axis.quadrance * (1 - spread)
  rootNonzero := by
    exact Algebra.Field.ExplicitField.mul_ne_zero
      (Algebra.Field.ExplicitField.mul_ne_zero candidate.anchorScaleNonzero axisNonNull)
      (Purelib.Algebra.Field.ExplicitField.one_sub_ne_zero_of_ne_one spreadNotOne)
  square := by
    have complementNonzero := Purelib.Algebra.Field.ExplicitField.one_sub_ne_zero_of_ne_one spreadNotOne
    have complementCancel := Algebra.Field.ExplicitField.mul_inv_cancel
      (1 - spread) complementNonzero
    have anchorQuadrance := Recovery.quadrance_rotationAnchorVector
      candidate.rotation candidate.notHalfTurn twoNonzero
    rw [candidate.halfSpread_eq, candidate.anchor_eq,
      Coordinates3.Vector.quadrance_scale] at anchorQuadrance
    unfold Purelib.Geometry.Rotations.Axis.Prescribed.prescribedAxisSquareValue
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv] at anchorQuadrance
    calc
      (candidate.anchorScale * axis.quadrance * (1 - spread)) ^ 2 =
          (candidate.anchorScale ^ 2 * axis.quadrance) *
            (axis.quadrance * (1 - spread) ^ 2) := by ring1
      _ = (spread * (1 - spread)⁻¹) *
            (axis.quadrance * (1 - spread) ^ 2) := by
              rw [anchorQuadrance]
      _ = axis.quadrance * spread * (1 - spread) := by
        calc
          spread * (1 - spread)⁻¹ *
                (axis.quadrance * (1 - spread) ^ 2) =
              axis.quadrance * spread * (1 - spread) *
                ((1 - spread) * (1 - spread)⁻¹) := by ring1
          _ = axis.quadrance * spread * (1 - spread) := by
            rw [complementCancel, mul_one]

/-- The anchor scalar computed from a supplied root of the Theorem 65 condition. -/
@[expose] def prescribedAnchorScale (axis : Coordinates3.Vector K)
  (spread : K)
    (certificate : Witness.NonzeroSquare (Geometry.Rotations.Axis.Prescribed.prescribedAxisSquareValue axis spread)) : K
      :=
  certificate.root / (axis.quadrance * (1 - spread))

/-- The root-derived anchor scale is nonzero for a non-null axis and a half spread different from one. -/
theorem prescribedAnchorScale_nonzero (axis : Coordinates3.Vector K)
  (spread : K)
    (certificate : Witness.NonzeroSquare (Geometry.Rotations.Axis.Prescribed.prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1) :
    Prescribed.prescribedAnchorScale axis spread certificate ≠ 0 := by
  unfold Prescribed.prescribedAnchorScale
  exact Algebra.Field.ExplicitField.div_ne_zero certificate.rootNonzero
    (Algebra.Field.ExplicitField.mul_ne_zero axisNonNull
      (Purelib.Algebra.Field.ExplicitField.one_sub_ne_zero_of_ne_one spreadNotOne))

/-- The computed scalar has exactly the anchor quadrance required by the half-spread equation. -/
theorem prescribedAnchorScale_quadrance (axis : Coordinates3.Vector K)
  (spread : K)
    (certificate : Witness.NonzeroSquare (Geometry.Rotations.Axis.Prescribed.prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1) :
    Prescribed.prescribedAnchorScale axis spread certificate ^ 2 * axis.quadrance =
      spread / (1 - spread) := by
  let complement := 1 - spread
  let denominator := axis.quadrance * complement
  have complementNonzero : complement ≠ 0 :=
    Purelib.Algebra.Field.ExplicitField.one_sub_ne_zero_of_ne_one spreadNotOne
  have denominatorNonzero : denominator ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero axisNonNull complementNonzero
  have denominatorCancel := Algebra.Field.ExplicitField.mul_inv_cancel denominator
    denominatorNonzero
  apply Purelib.Algebra.Field.Inverse.eq_div_of_mul_eq complementNonzero
  unfold Prescribed.prescribedAnchorScale
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  change (certificate.root * denominator⁻¹) ^ 2 * axis.quadrance *
      complement = spread
  calc
    (certificate.root * denominator⁻¹) ^ 2 * axis.quadrance *
          complement =
        certificate.root ^ 2 * denominator⁻¹ *
          (denominator * denominator⁻¹) := by
            unfold denominator
            ring1
    _ = certificate.root ^ 2 * denominator⁻¹ := by
      rw [denominatorCancel, mul_one]
    _ = (axis.quadrance * spread * complement) * denominator⁻¹ := by
      rw [certificate.square]
      rfl
    _ = spread * (denominator * denominator⁻¹) := by
      unfold denominator
      ring1
    _ = spread := by rw [denominatorCancel, mul_one]

/-- The constructed anchor denominator times the complementary half spread is one. -/
private theorem prescribedAnchor_capDenominator_mul
    (axis : Coordinates3.Vector K) (spread : K)
    (certificate : Witness.NonzeroSquare (Geometry.Rotations.Axis.Prescribed.prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1) :
    Cap.capDenominator
        (Coordinates3.Vector.scale (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate)
          axis) *
      (1 - spread) = 1 := by
  have quadranceFormula := prescribedAnchorScale_quadrance axis spread
    certificate axisNonNull spreadNotOne
  have complementNonzero := Purelib.Algebra.Field.ExplicitField.one_sub_ne_zero_of_ne_one spreadNotOne
  have complementCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    (1 - spread) complementNonzero
  unfold Cap.capDenominator
  rw [Coordinates3.Vector.quadrance_scale, quadranceFormula]
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    (1 + spread * (1 - spread)⁻¹) * (1 - spread) =
        (1 - spread) + spread *
          ((1 - spread)⁻¹ * (1 - spread)) := by ring1
    _ = (1 - spread) + spread := by
      rw [show (1 - spread)⁻¹ * (1 - spread) = 1 by
        calc
          (1 - spread)⁻¹ * (1 - spread) =
              (1 - spread) * (1 - spread)⁻¹ := by ring1
          _ = 1 := complementCancel,
        mul_one]
    _ = 1 := by ring1

/-- The root-derived prescribed anchor has nonzero cap denominator. -/
theorem prescribedAnchor_capDefined (axis : Coordinates3.Vector K)
  (spread : K)
    (certificate : Witness.NonzeroSquare (Geometry.Rotations.Axis.Prescribed.prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1) :
    Cap.capDenominator
      (Coordinates3.Vector.scale (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate)
        axis) ≠ 0 := by
  intro denominatorZero
  have product := prescribedAnchor_capDenominator_mul axis spread
    certificate
    axisNonNull spreadNotOne
  rw [denominatorZero, zero_mul] at product
  exact (Purelib.Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_nonzero axisNonNull) product.symm

/-- The cap built from the supplied square certificate has the requested half spread. -/
theorem halfSpread_prescribedAnchor (axis : Coordinates3.Vector K)
  (spread : K)
    (certificate : Witness.NonzeroSquare (Geometry.Rotations.Axis.Prescribed.prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Spread.halfSpread
        (Cap.capRotation
          (Coordinates3.Vector.scale (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate)
            axis)
          (prescribedAnchor_capDefined axis spread certificate axisNonNull
            spreadNotOne)) = spread := by
  let anchorVector :=
    Coordinates3.Vector.scale (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate) axis
  let defined := prescribedAnchor_capDefined axis spread certificate
    axisNonNull spreadNotOne
  let negativeDefined := prescribedAnchor_capDefined axis spread
    certificate.neg axisNonNull spreadNotOne
  have denominatorProduct := prescribedAnchor_capDenominator_mul axis
    spread
    certificate axisNonNull spreadNotOne
  have denominatorInverse := Purelib.Algebra.Field.Inverse.inverse_eq_of_mul_eq_one defined
    denominatorProduct
  have quadranceFormula := prescribedAnchorScale_quadrance axis spread
    certificate axisNonNull spreadNotOne
  have complementNonzero := Purelib.Algebra.Field.ExplicitField.one_sub_ne_zero_of_ne_one spreadNotOne
  have complementCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    (1 - spread) complementNonzero
  rw [Spread.halfSpread_cap anchorVector defined twoNonzero]
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  rw [denominatorInverse]
  unfold anchorVector
  rw [Coordinates3.Vector.quadrance_scale, quadranceFormula]
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    spread * (1 - spread)⁻¹ * (1 - spread) =
        spread * ((1 - spread) * (1 - spread)⁻¹) := by ring1
    _ = spread := by rw [complementCancel, mul_one]

/-- Sufficiency in Theorem 65 as an executable construction. -/
@[expose] def prescribedAxisRotationOfSquare (axis :
  Coordinates3.Vector K) (spread : K)
    (certificate : Witness.NonzeroSquare (Geometry.Rotations.Axis.Prescribed.prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) : PrescribedAxisRotation axis spread where
  rotation := Cap.capRotation
    (Coordinates3.Vector.scale (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate) axis)
    (prescribedAnchor_capDefined axis spread certificate axisNonNull
      spreadNotOne)
  notHalfTurn := Spread.halfSpread_cap_ne_one _ _ twoNonzero
  halfSpread_eq := halfSpread_prescribedAnchor axis spread certificate
    axisNonNull spreadNotOne twoNonzero
  anchorScale := Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate
  anchorScaleNonzero := prescribedAnchorScale_nonzero axis spread certificate
    axisNonNull spreadNotOne
  anchor_eq := by
    unfold Purelib.Geometry.Rotations.Axis.Recovery.rotationAnchorVector
    rw [Recovery.rotationAnchor_cap _ _ twoNonzero]
    exact Antisymmetric.anchorVector_anchor _

/-- Theorem 65's existence equivalence, with every square witness retained as finite data. -/
theorem prescribedAxisRotation_exists_iff
    (axis : Coordinates3.Vector K) (spread : K)
    (axisNonNull : axis.quadrance ≠ 0) (_spreadNonzero : spread ≠ 0)
    (spreadNotOne : spread ≠ 1) (twoNonzero : (2 : K) ≠ 0) :
    Nonempty (PrescribedAxisRotation axis spread) ↔
      Nonempty (Witness.NonzeroSquare (Geometry.Rotations.Axis.Prescribed.prescribedAxisSquareValue axis spread)) := by
  constructor
  · rintro ⟨candidate⟩
    exact ⟨candidate.squareCertificate axisNonNull spreadNotOne twoNonzero⟩
  · rintro ⟨certificate⟩
    exact ⟨Geometry.Rotations.Axis.Prescribed.prescribedAxisRotationOfSquare axis spread certificate axisNonNull
      spreadNotOne twoNonzero⟩

/-- Multiplication by four does not change the existence condition, because four is the displayed square of two. This is
Theorem 65's equivalent spread formulation. -/
theorem prescribedAxis_square_iff_spreadSquare
    (axis : Coordinates3.Vector K) (spread : K) (twoNonzero : (2 : K) ≠ 0) :
    Nonempty (Witness.NonzeroSquare (Prescribed.prescribedAxisSquareValue axis spread)) ↔
      Nonempty
        (Witness.NonzeroSquare
          (axis.quadrance * (4 * spread * (1 - spread)))) := by
  constructor
  · rintro ⟨certificate⟩
    refine ⟨{
      root := 2 * certificate.root
      rootNonzero := Algebra.Field.ExplicitField.mul_ne_zero twoNonzero
        certificate.rootNonzero
      square := ?_ }⟩
    unfold Prescribed.prescribedAxisSquareValue at certificate
    calc
      (2 * certificate.root) ^ 2 = 4 * certificate.root ^ 2 := by ring1
      _ = 4 * (axis.quadrance * spread * (1 - spread)) := by
        rw [certificate.square]
      _ = axis.quadrance * (4 * spread * (1 - spread)) := by ring1
  · rintro ⟨certificate⟩
    have twoCancel := Algebra.Field.ExplicitField.mul_inv_cancel (2 : K) twoNonzero
    refine ⟨{
      root := certificate.root / 2
      rootNonzero := Algebra.Field.ExplicitField.div_ne_zero certificate.rootNonzero
        twoNonzero
      square := ?_ }⟩
    unfold Prescribed.prescribedAxisSquareValue
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      (certificate.root * (2 : K)⁻¹) ^ 2 =
          certificate.root ^ 2 * (2 : K)⁻¹ ^ 2 := by ring1
      _ = (axis.quadrance * (4 * spread * (1 - spread))) *
          (2 : K)⁻¹ ^ 2 := by rw [certificate.square]
      _ = axis.quadrance * spread * (1 - spread) *
          (2 * (2 : K)⁻¹) ^ 2 := by ring1
      _ = axis.quadrance * spread * (1 - spread) := by
        rw [twoCancel]
        ring1

/-- Negating the square witness negates the computed anchor scale. -/
theorem prescribedAnchorScale_neg (axis : Coordinates3.Vector K)
  (spread : K)
    (certificate : Witness.NonzeroSquare (Geometry.Rotations.Axis.Prescribed.prescribedAxisSquareValue axis spread)) :
    Prescribed.prescribedAnchorScale axis spread certificate.neg =
      -Prescribed.prescribedAnchorScale axis spread certificate := by
  unfold Prescribed.prescribedAnchorScale Witness.NonzeroSquare.neg
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  ring1

/-- Negating the square witness negates the computed anchor vector. -/
theorem prescribedAnchorVector_neg (axis : Coordinates3.Vector K)
  (spread : K)
    (certificate : Witness.NonzeroSquare (Geometry.Rotations.Axis.Prescribed.prescribedAxisSquareValue axis spread)) :
    Coordinates3.Vector.scale (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate.neg)
      axis =
      Coordinates3.Vector.neg
        (Coordinates3.Vector.scale (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate)
          axis) := by
  rw [prescribedAnchorScale_neg]
  ext <;> unfold Coordinates3.Vector.scale Coordinates3.Vector.neg <;> ring1

/-- The two rotations computed from the two square roots are inverse in both orders. -/
theorem prescribedAxisRotation_pair_inverse
    (axis : Coordinates3.Vector K) (spread : K)
    (certificate : Witness.NonzeroSquare (Geometry.Rotations.Axis.Prescribed.prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.mul
        (Geometry.Rotations.Axis.Prescribed.prescribedAxisRotationOfSquare axis spread certificate axisNonNull
          spreadNotOne twoNonzero).rotation.matrix
        (Geometry.Rotations.Axis.Prescribed.prescribedAxisRotationOfSquare axis spread certificate.neg axisNonNull
          spreadNotOne twoNonzero).rotation.matrix = Matrix3.identity ∧
      Matrix3.mul
        (Geometry.Rotations.Axis.Prescribed.prescribedAxisRotationOfSquare axis spread certificate.neg axisNonNull
          spreadNotOne twoNonzero).rotation.matrix
        (Geometry.Rotations.Axis.Prescribed.prescribedAxisRotationOfSquare axis spread certificate axisNonNull
          spreadNotOne twoNonzero).rotation.matrix = Matrix3.identity := by
  let anchorVector :=
    Coordinates3.Vector.scale (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate) axis
  let defined := prescribedAnchor_capDefined axis spread certificate
    axisNonNull spreadNotOne
  let negativeDefined := prescribedAnchor_capDefined axis spread
    certificate.neg axisNonNull spreadNotOne
  have oppositeAnchor := prescribedAnchorVector_neg axis spread certificate
  have negativeCap :
      Cap.cap
          (Coordinates3.Vector.scale
            (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate.neg) axis)
          negativeDefined =
        Cap.cap (Coordinates3.Vector.neg anchorVector) (Cap.cap_neg_defined anchorVector defined) :=
    Geometry.Rotations.Cayley.Cap.cap_congr_vector oppositeAnchor negativeDefined
      (Cap.cap_neg_defined anchorVector defined)
  constructor
  · change Matrix3.mul (Cap.cap anchorVector defined)
        (Cap.cap
          (Coordinates3.Vector.scale
            (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate.neg) axis)
          negativeDefined) =
        Matrix3.identity
    rw [negativeCap]
    exact Cap.cap_mul_cap_neg anchorVector defined
  · change Matrix3.mul
        (Cap.cap
          (Coordinates3.Vector.scale
            (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate.neg) axis)
          negativeDefined)
        (Cap.cap anchorVector defined) = Matrix3.identity
    rw [negativeCap]
    exact Cap.cap_neg_mul_cap anchorVector defined

/-- The root-derived anchor on a non-null axis is nonzero. -/
private theorem prescribedAnchorVector_ne_zero
    (axis : Coordinates3.Vector K) (spread : K)
    (certificate : Witness.NonzeroSquare (Geometry.Rotations.Axis.Prescribed.prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1) :
    Coordinates3.Vector.scale (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate) axis ≠
      Coordinates3.Vector.zero := by
  intro vectorZero
  have scaledNonNull := Coordinates3.Vector.quadrance_scale_ne_zero
    (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate) axis
    (prescribedAnchorScale_nonzero axis spread certificate axisNonNull
      spreadNotOne) axisNonNull
  apply scaledNonNull
  rw [vectorZero, Coordinates3.Vector.quadrance_zero]

/-- The two displayed rotations are distinct. -/
theorem prescribedAxisRotation_pair_distinct
    (axis : Coordinates3.Vector K) (spread : K)
    (certificate : Witness.NonzeroSquare (Geometry.Rotations.Axis.Prescribed.prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    (Geometry.Rotations.Axis.Prescribed.prescribedAxisRotationOfSquare axis spread certificate axisNonNull
      spreadNotOne twoNonzero).rotation.matrix ≠
      (Geometry.Rotations.Axis.Prescribed.prescribedAxisRotationOfSquare axis spread certificate.neg axisNonNull
        spreadNotOne twoNonzero).rotation.matrix := by
  let anchorVector :=
    Coordinates3.Vector.scale (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate) axis
  let defined := prescribedAnchor_capDefined axis spread certificate
    axisNonNull spreadNotOne
  let negativeDefined := prescribedAnchor_capDefined axis spread
    certificate.neg axisNonNull spreadNotOne
  have distinct := Handedness.cap_ne_cap_neg_of_ne_zero anchorVector defined
    (prescribedAnchorVector_ne_zero axis spread certificate
      axisNonNull
      spreadNotOne) twoNonzero
  have negativeCap :
      Cap.cap
          (Coordinates3.Vector.scale
            (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate.neg) axis)
          negativeDefined =
        Cap.cap (Coordinates3.Vector.neg anchorVector) (Cap.cap_neg_defined anchorVector defined) :=
    Geometry.Rotations.Cayley.Cap.cap_congr_vector
      (prescribedAnchorVector_neg axis spread certificate) negativeDefined
      (Cap.cap_neg_defined anchorVector defined)
  change Cap.cap anchorVector defined ≠
    Cap.cap
      (Coordinates3.Vector.scale (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate.neg)
        axis)
      negativeDefined
  intro equal
  exact distinct (equal.trans negativeCap)

/-- Opposite roots give opposite handedness determinants, measured with the same first anchor vector and perpendicular
transversal. -/
theorem prescribedAxisRotation_pair_oppositeHandedness
    (axis : Coordinates3.Vector K) (spread : K)
    (certificate : Witness.NonzeroSquare (Geometry.Rotations.Axis.Prescribed.prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) (transversal : Coordinates3.Vector K)
    (perpendicular : transversal.Perpendicular
      (Coordinates3.Vector.scale (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate)
        axis)) :
    Handedness.handednessDet
        (Coordinates3.Vector.scale (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate)
          axis)
        transversal
        (Geometry.Rotations.Axis.Prescribed.prescribedAxisRotationOfSquare axis spread certificate.neg axisNonNull
          spreadNotOne twoNonzero).rotation.matrix =
      -Handedness.handednessDet
        (Coordinates3.Vector.scale (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate)
          axis)
        transversal
        (Geometry.Rotations.Axis.Prescribed.prescribedAxisRotationOfSquare axis spread certificate axisNonNull
          spreadNotOne twoNonzero).rotation.matrix := by
  let anchorVector :=
    Coordinates3.Vector.scale (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate) axis
  let defined := prescribedAnchor_capDefined axis spread certificate
    axisNonNull spreadNotOne
  let negativeDefined := prescribedAnchor_capDefined axis spread
    certificate.neg axisNonNull spreadNotOne
  have negativeCap :
      Cap.cap
          (Coordinates3.Vector.scale
            (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate.neg) axis)
          negativeDefined =
        Cap.cap (Coordinates3.Vector.neg anchorVector) (Cap.cap_neg_defined anchorVector defined) :=
    Geometry.Rotations.Cayley.Cap.cap_congr_vector
      (prescribedAnchorVector_neg axis spread certificate) negativeDefined
      (Cap.cap_neg_defined anchorVector defined)
  change Handedness.handednessDet anchorVector transversal
      (Cap.cap
        (Coordinates3.Vector.scale (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread
          certificate.neg) axis)
        negativeDefined) =
      -Handedness.handednessDet anchorVector transversal (Cap.cap anchorVector defined)
  rw [negativeCap,
    Handedness.handednessDet_cap_neg_sameAxis anchorVector defined transversal
      perpendicular,
    Handedness.handednessDet_cap anchorVector defined transversal perpendicular]

/-- The “exactly two” part of Theorem 65: every displayed rotation with the requested axis line and half spread is one
of the two computed matrices. -/
theorem PrescribedAxisRotation.matrix_eq_pair [DecidableEq K]
    {axis : Coordinates3.Vector K} {spread : K}
    (candidate : PrescribedAxisRotation axis spread)
    (certificate : Witness.NonzeroSquare (Geometry.Rotations.Axis.Prescribed.prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    candidate.rotation.matrix =
        (Geometry.Rotations.Axis.Prescribed.prescribedAxisRotationOfSquare axis spread certificate axisNonNull
          spreadNotOne twoNonzero).rotation.matrix ∨
      candidate.rotation.matrix =
        (Geometry.Rotations.Axis.Prescribed.prescribedAxisRotationOfSquare axis spread certificate.neg axisNonNull
          spreadNotOne twoNonzero).rotation.matrix := by
  have candidateQuadrance := Recovery.quadrance_rotationAnchorVector candidate.rotation
    candidate.notHalfTurn twoNonzero
  rw [candidate.halfSpread_eq, candidate.anchor_eq,
    Coordinates3.Vector.quadrance_scale] at candidateQuadrance
  have canonicalQuadrance := prescribedAnchorScale_quadrance axis spread
    certificate axisNonNull spreadNotOne
  have scaleSquares : candidate.anchorScale ^ 2 =
      Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate ^ 2 :=
    Purelib.Algebra.Field.ExplicitField.eq_of_mul_eq_mul_right axisNonNull (by
      rw [candidateQuadrance, canonicalQuadrance])
  let recovered := Recovery.rotationAnchorVector candidate.rotation candidate.notHalfTurn
  let recoveredDefined := Recovery.rotationAnchorVector_capDefined candidate.rotation
    candidate.notHalfTurn twoNonzero
  let candidateDefined :
      Cap.capDenominator (Coordinates3.Vector.scale candidate.anchorScale axis) ≠ 0 := by
    rw [← candidate.anchor_eq]
    exact recoveredDefined
  let positiveDefined := prescribedAnchor_capDefined axis spread certificate
    axisNonNull spreadNotOne
  let negativeDefined := prescribedAnchor_capDefined axis spread certificate.neg
    axisNonNull spreadNotOne
  have recoveredCap : Cap.cap recovered recoveredDefined =
      Cap.cap (Coordinates3.Vector.scale candidate.anchorScale axis) candidateDefined :=
    Geometry.Rotations.Cayley.Cap.cap_congr_vector candidate.anchor_eq recoveredDefined
      candidateDefined
  rcases Squares.eq_or_eq_neg_of_square_eq scaleSquares with scaleEqual | scaleEqual
  · left
    have scaledEqual : Coordinates3.Vector.scale candidate.anchorScale axis =
        Coordinates3.Vector.scale (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate)
          axis :=
      congrArg (fun scalar => Coordinates3.Vector.scale scalar axis) scaleEqual
    calc
      candidate.rotation.matrix =
          Cap.cap recovered recoveredDefined :=
        (Recovery.cap_rotationAnchor candidate.rotation candidate.notHalfTurn
          twoNonzero).symm
      _ = Cap.cap (Coordinates3.Vector.scale candidate.anchorScale axis) candidateDefined :=
        recoveredCap
      _ = Cap.cap
          (Coordinates3.Vector.scale
            (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate) axis)
          positiveDefined :=
        Geometry.Rotations.Cayley.Cap.cap_congr_vector scaledEqual candidateDefined
          positiveDefined
      _ = (Geometry.Rotations.Axis.Prescribed.prescribedAxisRotationOfSquare axis spread certificate axisNonNull
          spreadNotOne twoNonzero).rotation.matrix := rfl
  · right
    have scaledEqual : Coordinates3.Vector.scale candidate.anchorScale axis =
        Coordinates3.Vector.scale (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate.neg)
          axis := by
      apply congrArg (fun scalar => Coordinates3.Vector.scale scalar axis)
      calc
        candidate.anchorScale =
            -Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate := scaleEqual
        _ = Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate.neg :=
          (prescribedAnchorScale_neg axis spread certificate).symm
    calc
      candidate.rotation.matrix =
          Cap.cap recovered recoveredDefined :=
        (Recovery.cap_rotationAnchor candidate.rotation candidate.notHalfTurn
          twoNonzero).symm
      _ = Cap.cap (Coordinates3.Vector.scale candidate.anchorScale axis) candidateDefined :=
        recoveredCap
      _ = Cap.cap
          (Coordinates3.Vector.scale
            (Geometry.Rotations.Axis.Prescribed.prescribedAnchorScale axis spread certificate.neg) axis)
          negativeDefined :=
        Geometry.Rotations.Cayley.Cap.cap_congr_vector scaledEqual candidateDefined
          negativeDefined
      _ = (Geometry.Rotations.Axis.Prescribed.prescribedAxisRotationOfSquare axis spread certificate.neg
          axisNonNull spreadNotOne twoNonzero).rotation.matrix := rfl

/-- The endpoint `p=1`: the canonical half turn about the supplied non-null axis has half spread one. -/
theorem prescribedAxis_halfTurn_halfSpread (axis : Coordinates3.Vector
  K)
    (axisNonNull : axis.quadrance ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    Spread.halfSpread (Reflection.halfTurnRotation axis axisNonNull) = 1 :=
  Spread.halfSpread_halfTurn axis axisNonNull twoNonzero

/-- The endpoint `p=1` is unique on the projective axis line: replacing the axis by any nonzero scalar multiple gives
the same half-turn matrix. -/
theorem prescribedAxis_halfTurn_unique (axis : Coordinates3.Vector K)
    (axisNonNull : axis.quadrance ≠ 0) (scalar : K)
    (scalarNonzero : scalar ≠ 0) :
    (Reflection.halfTurnRotation (Coordinates3.Vector.scale scalar axis)
      (Coordinates3.Vector.quadrance_scale_ne_zero scalar axis scalarNonzero axisNonNull)).matrix =
      (Reflection.halfTurnRotation axis axisNonNull).matrix :=
  Reflection.halfTurn_scale scalar axis scalarNonzero axisNonNull

/-- The endpoint `p=0`: in a field whose only null vector is zero, a half-spread-zero rotation is the identity matrix.
-/
theorem rotation_eq_identity_of_halfSpread_zero
    (separation : NullVectors.SumSquaresSeparate K) (rotation : Rotations.Basic.Rotation K)
    (spreadZero : Spread.halfSpread rotation = 0) (twoNonzero : (2 : K) ≠ 0) :
    rotation.matrix = Matrix3.identity := by
  have oneNonzero : (1 : K) ≠ 0 := Purelib.Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_nonzero twoNonzero
  have notHalfTurn : Spread.halfSpread rotation ≠ 1 := by
    intro spreadOne
    apply oneNonzero
    calc
      (1 : K) = Spread.halfSpread rotation := spreadOne.symm
      _ = 0 := spreadZero
  let recovered := Recovery.rotationAnchorVector rotation notHalfTurn
  let recoveredDefined := Recovery.rotationAnchorVector_capDefined rotation notHalfTurn
    twoNonzero
  have recoveredNull : recovered.IsNull := by
    have quadranceFormula := Recovery.quadrance_rotationAnchorVector rotation
      notHalfTurn twoNonzero
    rw [spreadZero] at quadranceFormula
    simp only [SubNegMonoid.sub_eq_add_neg, SubNegZeroMonoid.neg_zero, AddZeroClass.add_zero,
      Algebra.Field.ExplicitField.zero_div] at quadranceFormula
    exact quadranceFormula
  have recoveredZero := NullVectors.only_zero_null_vector separation recovered recoveredNull
  let zeroDefined : Cap.capDenominator (Coordinates3.Vector.zero : Coordinates3.Vector K) ≠ 0 := by
    unfold Cap.capDenominator
    rw [Coordinates3.Vector.quadrance_zero, add_zero]
    exact oneNonzero
  calc
    rotation.matrix = Cap.cap recovered recoveredDefined :=
      (Recovery.cap_rotationAnchor rotation notHalfTurn twoNonzero).symm
    _ = Cap.cap Coordinates3.Vector.zero zeroDefined :=
      Geometry.Rotations.Cayley.Cap.cap_congr_vector recoveredZero recoveredDefined zeroDefined
    _ = Matrix3.identity := by
      ext <;> unfold Cap.cap Matrix3.add Matrix3.scale Matrix3.identity
        Matrix3.mul Antisymmetric.anchor Coordinates3.Vector.zero <;> ring1

end Purelib.Geometry.Rotations.Axis.Prescribed

namespace Purelib.Geometry.Rotations.Axis.Prescribed

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K]

/-- The original Euclidean anchor scale is the shared scalar parameter computed from the same root and quadrance. -/
theorem prescribedAnchorScale_eq_parameters (axis : Vector3 K) (spread : K)
    (certificate : Witness.NonzeroSquare (prescribedAxisSquareValue axis spread)) :
    prescribedAnchorScale axis spread certificate = Parameters.anchorScale axis.quadrance spread certificate := rfl

/-- A retained prescribed-axis rotation fixes exactly the scalar multiples of its original axis.

The nonzero anchor scale transports the cap's complete fixed line to the requested non-null axis. -/
theorem PrescribedAxisRotation.fixed_iff_scale {axis : Vector3 K} {spread : K}
    (candidate : PrescribedAxisRotation axis spread) (axisNonNull : axis.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (vector : Vector3 K) :
    Matrix3.rowMul vector candidate.rotation.matrix = vector ↔
      ∃ factor : K, vector = Vector3.scale factor axis := by
  let recovered := Recovery.rotationAnchorVector candidate.rotation candidate.notHalfTurn
  let defined := Recovery.rotationAnchorVector_capDefined candidate.rotation candidate.notHalfTurn twoNonzero
  have recoveredEqual : recovered = Vector3.scale candidate.anchorScale axis := candidate.anchor_eq
  have recoveredNonNull : recovered.quadrance ≠ 0 := by
    rw [recoveredEqual]
    exact Vector3.quadrance_scale_ne_zero candidate.anchorScale axis candidate.anchorScaleNonzero axisNonNull
  have capEqual : Cap.cap recovered defined = candidate.rotation.matrix :=
    Recovery.cap_rotationAnchor candidate.rotation candidate.notHalfTurn twoNonzero
  constructor
  · intro fixed
    have projected := (Cap.rowMul_cap_eq_self_iff_projection recovered vector defined
      recoveredNonNull twoNonzero).mp (capEqual.symm ▸ fixed)
    refine ⟨(vector.dot recovered / recovered.quadrance) * candidate.anchorScale, ?_⟩
    calc
      vector = Vector3.scale (vector.dot recovered / recovered.quadrance) recovered := projected
      _ = Vector3.scale ((vector.dot recovered / recovered.quadrance) * candidate.anchorScale) axis := by
        rw [recoveredEqual, Vector3.scale_scale]
  · rintro ⟨factor, equal⟩
    have anchorFixed := Recovery.rowMul_rotationAnchorVector candidate.rotation candidate.notHalfTurn twoNonzero
    rw [candidate.anchor_eq] at anchorFixed
    have cancel : candidate.anchorScale⁻¹ * candidate.anchorScale = 1 := by
      rw [mul_comm]
      exact ExplicitField.mul_inv_cancel candidate.anchorScale candidate.anchorScaleNonzero
    have axisFixed : Matrix3.rowMul axis candidate.rotation.matrix = axis := by
      calc
        Matrix3.rowMul axis candidate.rotation.matrix = Vector3.scale candidate.anchorScale⁻¹
            (Matrix3.rowMul (Vector3.scale candidate.anchorScale axis) candidate.rotation.matrix) := by
          rw [← Matrix3.rowMul_vector_scale, Vector3.scale_scale, cancel, Vector3.one_scale]
        _ = Vector3.scale candidate.anchorScale⁻¹ (Vector3.scale candidate.anchorScale axis) :=
          congrArg (Vector3.scale candidate.anchorScale⁻¹) anchorFixed
        _ = axis := by rw [Vector3.scale_scale, cancel, Vector3.one_scale]
    calc
      Matrix3.rowMul vector candidate.rotation.matrix =
          Matrix3.rowMul (Vector3.scale factor axis) candidate.rotation.matrix :=
        congrArg (fun value => Matrix3.rowMul value candidate.rotation.matrix) equal
      _ = Vector3.scale factor axis := by rw [Matrix3.rowMul_vector_scale, axisFixed]
      _ = vector := equal.symm

/-- Prescribing the complete fixed line and a non-endpoint half spread is equivalent to the nonzero-square condition.

The geometric condition refers to the original rotation matrix. Its recovered anchor supplies the same retained axis
scale used by the executable square-witness construction. -/
theorem prescribedAxis_fixedLine_exists_iff (axis : Vector3 K) (spread : K)
    (axisNonNull : axis.quadrance ≠ 0) (spreadNonzero : spread ≠ 0)
    (spreadNotOne : spread ≠ 1) (twoNonzero : (2 : K) ≠ 0) :
    (∃ rotation : Rotations.Basic.Rotation K, Spread.halfSpread rotation = spread ∧
      ∀ vector : Vector3 K, Matrix3.rowMul vector rotation.matrix = vector ↔
        ∃ factor : K, vector = Vector3.scale factor axis) ↔
      Nonempty (Witness.NonzeroSquare (prescribedAxisSquareValue axis spread)) := by
  constructor
  · rintro ⟨rotation, amount, fixedLine⟩
    have notHalfTurn : Spread.halfSpread rotation ≠ 1 := by
      intro equal
      exact spreadNotOne (amount.symm.trans equal)
    let recovered := Recovery.rotationAnchorVector rotation notHalfTurn
    have recoveredFixed : Matrix3.rowMul recovered rotation.matrix = recovered :=
      Recovery.rowMul_rotationAnchorVector rotation notHalfTurn twoNonzero
    obtain ⟨factor, recoveredEqual⟩ := (fixedLine recovered).mp recoveredFixed
    have recoveredNonNull : recovered.quadrance ≠ 0 := by
      rw [Recovery.quadrance_rotationAnchorVector rotation notHalfTurn twoNonzero, amount]
      exact ExplicitField.div_ne_zero spreadNonzero (ExplicitField.one_sub_ne_zero_of_ne_one spreadNotOne)
    have factorNonzero : factor ≠ 0 := by
      intro zero
      rw [recoveredEqual, zero, Vector3.zero_scale, Vector3.quadrance_zero] at recoveredNonNull
      exact recoveredNonNull rfl
    let candidate : PrescribedAxisRotation axis spread :=
      ⟨rotation, notHalfTurn, amount, factor, factorNonzero, recoveredEqual⟩
    exact ⟨candidate.squareCertificate axisNonNull spreadNotOne twoNonzero⟩
  · rintro ⟨certificate⟩
    let candidate := prescribedAxisRotationOfSquare axis spread certificate axisNonNull spreadNotOne twoNonzero
    exact ⟨candidate.rotation, candidate.halfSpread_eq,
      candidate.fixed_iff_scale axisNonNull twoNonzero⟩

end Purelib.Geometry.Rotations.Axis.Prescribed

end

end
