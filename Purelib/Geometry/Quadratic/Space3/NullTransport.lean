module

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Rotations.Reflection
import Purelib.LinearAlgebra.Coordinates3.Vector
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Tactic.Ring
public import Purelib.LinearAlgebra.Coordinates3.Antisymmetric
public import Purelib.Algebra.Field.Squares
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry.Rotations

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3

section
@[expose] public section

/-!
# Constructive conjugacy classification of finite-field parabolics

Problem 69 asks for the parabolic classes over the null directions.  The
counting layer gives unique null-direction and scalar coordinates.  This
module proves the stronger conjugacy-orbit interpretation: over every
displayed odd finite field, all nonidentity parabolic rotations form one
conjugacy class.  The conjugator is built from finitely selected reflections;
no quotient, basis extension, or choice principle is used.
-/

namespace Purelib.Geometry.Quadratic.Space3.NullTransport

variable {K : Type*} [ExplicitField K]

set_option genInjectivity false in
/-- Executable scale data for two vectors on the same displayed line. -/
structure NullLineScale (source target : Coordinates3.Vector K)
  where
  /-- The retained scalar expressing the target on the source line. -/ factor : K
  /-- The target equals the retained scalar multiple of the source. -/ target_eq : target = Coordinates3.Vector.scale
    factor source

constructive_injectivity NullLineScale

/-- Two null vectors perpendicular to one another lie on the same displayed null line. The scalar is computed from the
first nonzero coordinate of the source, and the remaining two coordinates are discharged by the binary rigidity lemma
above. -/
def nullLineScaleOfPerpendicular [DecidableEq K]
    (source target : Coordinates3.Vector K)
    (sourceNull : source.quadrance = 0)
    (sourceNonzero : source ≠ Coordinates3.Vector.zero)
    (targetNull : target.quadrance = 0)
    (perpendicular : Coordinates3.Vector.dot source target = 0) :
    NullLineScale source target := by
  by_cases sourceTNonzero : source.t ≠ 0
  · let factor := source.t⁻¹ * target.t
    have sourceTCancel :=
      ExplicitField.mul_inv_cancel source.t sourceTNonzero
    have targetT : target.t = factor * source.t := by
      calc
        target.t = 1 * target.t := by ring1
        _ = (source.t * source.t⁻¹) * target.t := by rw [sourceTCancel]
        _ = factor * source.t := by unfold factor; ring1
    let differenceR := target.r - factor * source.r
    let differenceS := target.s - factor * source.s
    have tailNonNull : source.r ^ 2 + source.s ^ 2 ≠ 0 := by
      intro tailZero
      have sourceTSquareZero : source.t ^ 2 = 0 := by
        calc
          source.t ^ 2 = source.quadrance -
              (source.r ^ 2 + source.s ^ 2) := by
            unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot
            ring1
          _ = 0 := by rw [sourceNull, tailZero]; ring1
      have sourceTSquareNonzero : source.t ^ 2 ≠ 0 := by
        simpa only [pow_two] using
          ExplicitField.mul_ne_zero sourceTNonzero sourceTNonzero
      exact sourceTSquareNonzero sourceTSquareZero
    have tailPerpendicular :
        source.r * differenceR + source.s * differenceS = 0 := by
      calc
        source.r * differenceR + source.s * differenceS =
            (source.t * target.t + source.r * target.r +
              source.s * target.s) -
              factor * (source.t * source.t + source.r * source.r +
                source.s * source.s) -
              source.t * (target.t - factor * source.t) := by
          unfold differenceR differenceS
          ring1
        _ = 0 := by
          change source.t * target.t + source.r * target.r +
            source.s * target.s = 0 at perpendicular
          change source.t * source.t + source.r * source.r +
            source.s * source.s = 0 at sourceNull
          rw [perpendicular, sourceNull, targetT]
          ring1
    have tailNull : differenceR ^ 2 + differenceS ^ 2 = 0 := by
      calc
        differenceR ^ 2 + differenceS ^ 2 =
            (target.t - factor * source.t) ^ 2 +
              differenceR ^ 2 + differenceS ^ 2 := by
          rw [targetT]
          ring1
        _ = (target.t * target.t + target.r * target.r +
              target.s * target.s) -
              2 * factor * (source.t * target.t + source.r * target.r +
                source.s * target.s) +
                factor ^ 2 * (source.t * source.t +
                  source.r * source.r + source.s * source.s) := by
          unfold differenceR differenceS
          ring1
        _ = 0 := by
          change target.t * target.t + target.r * target.r +
            target.s * target.s = 0 at targetNull
          change source.t * target.t + source.r * target.r +
            source.s * target.s = 0 at perpendicular
          change source.t * source.t + source.r * source.r +
            source.s * source.s = 0 at sourceNull
          rw [targetNull, perpendicular, sourceNull]
          ring1
    have tailZero := Purelib.Algebra.Field.Squares.pair_eq_zero_of_null_of_perpendicular
      source.r source.s differenceR differenceS tailNonNull
      tailPerpendicular tailNull
    refine ⟨factor, ?_⟩
    apply Coordinates3.Vector.ext
    · exact targetT
    · change target.r = factor * source.r
      have := tailZero.1
      unfold differenceR at this
      calc
        target.r = (target.r - factor * source.r) +
            factor * source.r := by ring1
        _ = factor * source.r := by rw [this]; ring1
    · change target.s = factor * source.s
      have := tailZero.2
      unfold differenceS at this
      calc
        target.s = (target.s - factor * source.s) +
            factor * source.s := by ring1
        _ = factor * source.s := by rw [this]; ring1

  · have sourceTZero : source.t = 0 := by
      cases (inferInstance : DecidableEq K) source.t 0 with
      | isTrue equal => exact equal
      | isFalse different => exact False.elim (sourceTNonzero different)
    have sourceRNonzero : source.r ≠ 0 := by
      intro sourceRZero
      have sourceSSquareZero : source.s ^ 2 = 0 := by
        calc
          source.s ^ 2 = source.quadrance := by
            unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot
            rw [sourceTZero, sourceRZero]
            ring1
          _ = 0 := sourceNull
      have sourceSZero :=
        Purelib.Algebra.Field.Squares.eq_zero_of_square_eq_zero (value := _) sourceSSquareZero
      apply sourceNonzero
      apply Coordinates3.Vector.ext
      · exact sourceTZero
      · exact sourceRZero
      · exact sourceSZero
    let factor := source.r⁻¹ * target.r
    have sourceRCancel :=
      ExplicitField.mul_inv_cancel source.r sourceRNonzero
    have targetR : target.r = factor * source.r := by
      calc
        target.r = 1 * target.r := by ring1
        _ = (source.r * source.r⁻¹) * target.r := by rw [sourceRCancel]
        _ = factor * source.r := by unfold factor; ring1
    let differenceT := target.t - factor * source.t
    let differenceS := target.s - factor * source.s
    have outsideNonNull : source.t ^ 2 + source.s ^ 2 ≠ 0 := by
      intro outsideZero
      have sourceRSquareZero : source.r ^ 2 = 0 := by
        calc
          source.r ^ 2 = source.quadrance -
              (source.t ^ 2 + source.s ^ 2) := by
            unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot
            ring1
          _ = 0 := by rw [sourceNull, outsideZero]; ring1
      have sourceRSquareNonzero : source.r ^ 2 ≠ 0 := by
        simpa only [pow_two] using
          ExplicitField.mul_ne_zero sourceRNonzero sourceRNonzero
      exact sourceRSquareNonzero sourceRSquareZero
    have outsidePerpendicular :
        source.t * differenceT + source.s * differenceS = 0 := by
      calc
        source.t * differenceT + source.s * differenceS =
            (source.t * target.t + source.r * target.r +
              source.s * target.s) -
              factor * (source.t * source.t + source.r * source.r +
                source.s * source.s) -
              source.r * (target.r - factor * source.r) := by
          unfold differenceT differenceS
          ring1
        _ = 0 := by
          change source.t * target.t + source.r * target.r +
            source.s * target.s = 0 at perpendicular
          change source.t * source.t + source.r * source.r +
            source.s * source.s = 0 at sourceNull
          rw [perpendicular, sourceNull, targetR]
          ring1
    have outsideNull : differenceT ^ 2 + differenceS ^ 2 = 0 := by
      calc
        differenceT ^ 2 + differenceS ^ 2 =
            differenceT ^ 2 +
              (target.r - factor * source.r) ^ 2 +
                differenceS ^ 2 := by
          rw [targetR]
          ring1
        _ = (target.t * target.t + target.r * target.r +
              target.s * target.s) -
              2 * factor * (source.t * target.t + source.r * target.r +
                source.s * target.s) +
                factor ^ 2 * (source.t * source.t +
                  source.r * source.r + source.s * source.s) := by
          unfold differenceT differenceS
          ring1
        _ = 0 := by
          change target.t * target.t + target.r * target.r +
            target.s * target.s = 0 at targetNull
          change source.t * target.t + source.r * target.r +
            source.s * target.s = 0 at perpendicular
          change source.t * source.t + source.r * source.r +
            source.s * source.s = 0 at sourceNull
          rw [targetNull, perpendicular, sourceNull]
          ring1
    have outsideZero := Purelib.Algebra.Field.Squares.pair_eq_zero_of_null_of_perpendicular
      source.t source.s differenceT differenceS outsideNonNull
      outsidePerpendicular outsideNull
    refine ⟨factor, ?_⟩
    apply Coordinates3.Vector.ext
    · change target.t = factor * source.t
      have := outsideZero.1
      unfold differenceT at this
      calc
        target.t = (target.t - factor * source.t) +
            factor * source.t := by ring1
        _ = factor * source.t := by rw [this]; ring1
    · exact targetR
    · change target.s = factor * source.s
      have := outsideZero.2
      unfold differenceS at this
      calc
        target.s = (target.s - factor * source.s) +
            factor * source.s := by ring1
        _ = factor * source.s := by rw [this]; ring1

/-- Propositional form of the executable null-line scale classification. -/
theorem null_eq_scale_of_perpendicular [DecidableEq K]
    (source target : Coordinates3.Vector K)
    (sourceNull : source.quadrance = 0)
    (sourceNonzero : source ≠ Coordinates3.Vector.zero)
    (targetNull : target.quadrance = 0)
    (perpendicular : Coordinates3.Vector.dot source target = 0) :
    ∃ factor : K, target = Coordinates3.Vector.scale factor source := by
  let scaling := nullLineScaleOfPerpendicular source target sourceNull
    sourceNonzero targetNull perpendicular
  exact ⟨scaling.factor, scaling.target_eq⟩

set_option genInjectivity false in
/-- A cached null partner with nonzero pairing. Two explicit sign changes cover every nonzero null vector in
characteristic different from two. -/
structure NullPartner (source : Coordinates3.Vector K) where
  /-- The cached null partner vector. -/ value : Coordinates3.Vector K
  /-- The partner has zero quadrance. -/ valueNull : value.quadrance = 0
  /-- The source and partner have nonzero dot product. -/ pairingNonzero : Coordinates3.Vector.dot source value ≠ 0

constructive_injectivity NullPartner

/-- Construct a null partner by changing the sign of `s` when it is nonzero, and otherwise changing the sign of `r`. -/
def nullPartner [DecidableEq K]
    (source : Coordinates3.Vector K) (sourceNull : source.quadrance = 0)
    (sourceNonzero : source ≠ Coordinates3.Vector.zero) (twoNonzero : (2 : K) ≠ 0) :
    NullPartner source := by
  by_cases sourceSNonzero : source.s ≠ 0
  · let partner : Coordinates3.Vector K := ⟨source.t, source.r, -source.s⟩
    have sourceEquation : source.t * source.t + source.r * source.r +
        source.s * source.s = 0 := by
      simpa only [Coordinates3.Vector.quadrance, Coordinates3.Vector.dot]
        using sourceNull
    refine
      { value := partner
        valueNull := ?_
        pairingNonzero := ?_ }
    · change source.t * source.t + source.r * source.r +
        (-source.s) * (-source.s) = 0
      calc
        source.t * source.t + source.r * source.r +
            (-source.s) * (-source.s) =
          source.t * source.t + source.r * source.r +
            source.s * source.s := by ring1
        _ = 0 := sourceEquation
    · have sourceSSquareNonzero : source.s ^ 2 ≠ 0 := by
        simpa only [pow_two] using
          ExplicitField.mul_ne_zero sourceSNonzero sourceSNonzero
      have twiceSquareNonzero : (2 : K) * source.s ^ 2 ≠ 0 :=
        ExplicitField.mul_ne_zero twoNonzero sourceSSquareNonzero
      intro pairingZero
      apply twiceSquareNonzero
      calc
        2 * source.s ^ 2 = -Coordinates3.Vector.dot source partner := by
          calc
            2 * source.s ^ 2 =
                -(source.t * source.t + source.r * source.r -
                    source.s * source.s) := by
              calc
                2 * source.s ^ 2 = 2 * source.s ^ 2 -
                    (source.t * source.t + source.r * source.r +
                      source.s * source.s) := by
                  rw [sourceEquation]
                  ring1
                _ = -(source.t * source.t + source.r * source.r -
                    source.s * source.s) := by ring1
            _ = -Coordinates3.Vector.dot source partner := by
              unfold partner Coordinates3.Vector.dot
              ring1
        _ = 0 := by rw [pairingZero]; ring1
  · have sourceSZero : source.s = 0 := by
      cases (inferInstance : DecidableEq K) source.s 0 with
      | isTrue equal => exact equal
      | isFalse different => exact False.elim (sourceSNonzero different)
    have sourceTNonzero : source.t ≠ 0 := by
      intro sourceTZero
      have sourceRSquareZero : source.r ^ 2 = 0 := by
        calc
          source.r ^ 2 = source.quadrance := by
            unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot
            rw [sourceTZero, sourceSZero]
            ring1
          _ = 0 := sourceNull
      have sourceRZero :=
        Purelib.Algebra.Field.Squares.eq_zero_of_square_eq_zero (value := _) sourceRSquareZero
      apply sourceNonzero
      apply Coordinates3.Vector.ext
      · exact sourceTZero
      · exact sourceRZero
      · exact sourceSZero
    let partner : Coordinates3.Vector K := ⟨source.t, -source.r, 0⟩
    have sourceEquation : source.t * source.t + source.r * source.r = 0 := by
      change source.t * source.t + source.r * source.r +
        source.s * source.s = 0 at sourceNull
      rw [sourceSZero] at sourceNull
      simpa only [zero_mul, add_zero] using sourceNull
    refine
      { value := partner
        valueNull := ?_
        pairingNonzero := ?_ }
    · change source.t * source.t + (-source.r) * (-source.r) + 0 * 0 = 0
      calc
        source.t * source.t + (-source.r) * (-source.r) + 0 * 0 =
            source.t * source.t + source.r * source.r := by ring1
        _ = 0 := sourceEquation
    · have sourceTSquareNonzero : source.t ^ 2 ≠ 0 := by
        simpa only [pow_two] using
          ExplicitField.mul_ne_zero sourceTNonzero sourceTNonzero
      have twiceSquareNonzero : (2 : K) * source.t ^ 2 ≠ 0 :=
        ExplicitField.mul_ne_zero twoNonzero sourceTSquareNonzero
      intro pairingZero
      apply twiceSquareNonzero
      calc
        2 * source.t ^ 2 = Coordinates3.Vector.dot source partner := by
          calc
            2 * source.t ^ 2 =
                source.t * source.t - source.r * source.r := by
              calc
                2 * source.t ^ 2 = 2 * source.t ^ 2 -
                    (source.t * source.t + source.r * source.r) := by
                  rw [sourceEquation]
                  ring1
                _ = source.t * source.t - source.r * source.r := by
                  ring1
            _ = Coordinates3.Vector.dot source partner := by
              unfold partner Coordinates3.Vector.dot
              rw [sourceSZero]
              ring1
        _ = 0 := pairingZero

/-- Quadrance of a displayed vector difference. -/
theorem quadrance_sub_expansion (left right : Coordinates3.Vector
  K) :
    (Coordinates3.Vector.sub left right).quadrance =
      left.quadrance - 2 * Coordinates3.Vector.dot left right + right.quadrance := by
  simp only [Coordinates3.Vector.quadrance]
  unfold Coordinates3.Vector.dot Coordinates3.Vector.sub
  ring1

/-- Reflection in the non-null difference of two equal-quadrance vectors maps the first vector to the second. -/
theorem rowMul_reflection_difference
    (first second : Coordinates3.Vector K)
    (equalQuadrance : first.quadrance = second.quadrance)
    (differenceNonNull :
      (Coordinates3.Vector.sub first second).quadrance ≠ 0) :
    Matrix3.rowMul first
        (Reflection.reflection (Coordinates3.Vector.sub first second) differenceNonNull) = second := by
  have twicePairing :
      2 * Coordinates3.Vector.dot first (Coordinates3.Vector.sub first second) =
        (Coordinates3.Vector.sub first second).quadrance := by
    calc
      2 * Coordinates3.Vector.dot first (Coordinates3.Vector.sub first second) =
          2 * (first.quadrance - Coordinates3.Vector.dot first second) := by
        simp only [Coordinates3.Vector.quadrance]
        unfold Coordinates3.Vector.dot Coordinates3.Vector.sub
        ring1
      _ = first.quadrance - 2 * Coordinates3.Vector.dot first second +
          second.quadrance := by
        rw [← equalQuadrance]
        ring1
      _ = (Coordinates3.Vector.sub first second).quadrance :=
        (quadrance_sub_expansion first second).symm
  have cancel := ExplicitField.mul_inv_cancel
    (Coordinates3.Vector.sub first second).quadrance differenceNonNull
  have coefficient :
      2 * Coordinates3.Vector.dot first (Coordinates3.Vector.sub first second) /
          (Coordinates3.Vector.sub first second).quadrance = 1 := by
    simp only [ExplicitField.div_eq_mul_inv]
    rw [twicePairing, cancel]
  rw [Reflection.rowMul_reflection, coefficient]
  ext <;> unfold Coordinates3.Vector.sub Coordinates3.Vector.scale <;> ring1

end Purelib.Geometry.Quadratic.Space3.NullTransport

end
