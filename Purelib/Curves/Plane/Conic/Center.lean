module

import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.Inverse
import Purelib.Geometry.Plane.Line.Affine
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Proportion.Three.Basic
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Curves.Plane.Conic.QuadraticPart
public import Purelib.Curves.Plane.Conic.Scale
public import Purelib.Geometry.Plane.HalfTurn.Basic
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.ExistsUnique
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Plane

open Purelib.Curves.Plane.Conic

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

section
@[expose] public section

/-!
# Divine Proportions, §15.1: conics and their centers

A conic is kept as its six displayed coefficients.  Its quadratic part is
required to be nonzero, exactly as in the source.  Center calculations use only
the two finite linear equations obtained by expanding rotation invariance.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The source's symmetry condition under rotation in a proposed center. -/
def RotationInvariant (conic : Conic K) (center :
  Plane.Point K) : Prop :=
  ∀ point : Plane.Point K,
    conic.evaluate (HalfTurn.Basic.rotateInPoint center point) = conic.evaluate point

/-- The two linear equations obtained from the center symmetry condition. -/
def IsCenter (conic : Conic K) (center :
  Plane.Point K) : Prop :=
  2 * conic.d * center.x + conic.e * center.y + conic.a = 0 ∧
    conic.e * center.x + 2 * conic.f * center.y + conic.b = 0

/-- A conic is centered when an explicit center exists. -/
def IsCentered (conic : Conic K) : Prop :=
  ∃ center : Plane.Point K, conic.IsCenter center

/-- A central conic has the displayed origin as a center. -/
def IsCentral (conic : Conic K) : Prop :=
  conic.IsCenter ⟨0, 0⟩

/-- The explicit center printed in the nonsingular case of Theorem 99. -/
def centerPoint (conic : Conic K) : Plane.Point K
  :=
  ⟨(2 * conic.a * conic.f - conic.b * conic.e) /
      conic.centerDiscriminant,
    (2 * conic.b * conic.d - conic.a * conic.e) /
      conic.centerDiscriminant⟩

/-- The compatibility proportion `e : 2f : b = 2d : e : a`. -/
def CenterRowsEquivalent (conic : Conic K) : Prop :=
  Conic.OrderedTriplesEquivalent conic.e (2 * conic.f) conic.b
    (2 * conic.d) conic.e conic.a

/-- The finite meaning of “more than one center”. -/
def HasMultipleCenters (conic : Conic K) : Prop :=
  ∃ first second : Plane.Point K,
    first ≠ second ∧ conic.IsCenter first ∧ conic.IsCenter second

/-- The source definition by rotation invariance is equivalent to the two linear center equations. The reverse
implication needs only two test points. -/
theorem isCenter_iff_rotationInvariant (conic : Conic K)
  (center : Plane.Point K)
    (twoNonzero : (2 : K) ≠ 0) :
    conic.IsCenter center ↔ conic.RotationInvariant center := by
  constructor
  · rintro ⟨firstEquation, secondEquation⟩ point
    unfold Conic.evaluate HalfTurn.Basic.rotateInPoint
    calc
      conic.d * (2 * center.x - point.x) ^ 2 +
          conic.e * (2 * center.x - point.x) *
            (2 * center.y - point.y) +
          conic.f * (2 * center.y - point.y) ^ 2 +
          conic.a * (2 * center.x - point.x) +
          conic.b * (2 * center.y - point.y) + conic.c =
        conic.d * point.x ^ 2 + conic.e * point.x * point.y +
          conic.f * point.y ^ 2 + conic.a * point.x +
          conic.b * point.y + conic.c -
          2 * ((point.x - center.x) *
              (2 * conic.d * center.x + conic.e * center.y + conic.a) +
            (point.y - center.y) *
              (conic.e * center.x + 2 * conic.f * center.y + conic.b)) := by
            ring1
      _ = conic.d * point.x ^ 2 + conic.e * point.x * point.y +
          conic.f * point.y ^ 2 + conic.a * point.x +
          conic.b * point.y + conic.c := by
        rw [firstEquation, secondEquation]
        ring1
  · intro invariant
    have xInvariant := invariant ⟨center.x + 1, center.y⟩
    have yInvariant := invariant ⟨center.x, center.y + 1⟩
    unfold Conic.evaluate HalfTurn.Basic.rotateInPoint at xInvariant yInvariant
    have firstProductZero :
        (-2 : K) *
          (2 * conic.d * center.x + conic.e * center.y + conic.a) = 0 := by
      calc
        (-2 : K) *
            (2 * conic.d * center.x + conic.e * center.y + conic.a) =
          (conic.d * (2 * center.x - (center.x + 1)) ^ 2 +
              conic.e * (2 * center.x - (center.x + 1)) *
                (2 * center.y - center.y) +
              conic.f * (2 * center.y - center.y) ^ 2 +
              conic.a * (2 * center.x - (center.x + 1)) +
              conic.b * (2 * center.y - center.y) + conic.c) -
            (conic.d * (center.x + 1) ^ 2 +
              conic.e * (center.x + 1) * center.y +
              conic.f * center.y ^ 2 + conic.a * (center.x + 1) +
              conic.b * center.y + conic.c) := by ring1
        _ = 0 := by rw [xInvariant]; ring1
    have secondProductZero :
        (-2 : K) *
          (conic.e * center.x + 2 * conic.f * center.y + conic.b) = 0 := by
      calc
        (-2 : K) *
            (conic.e * center.x + 2 * conic.f * center.y + conic.b) =
          (conic.d * (2 * center.x - center.x) ^ 2 +
              conic.e * (2 * center.x - center.x) *
                (2 * center.y - (center.y + 1)) +
              conic.f * (2 * center.y - (center.y + 1)) ^ 2 +
              conic.a * (2 * center.x - center.x) +
              conic.b * (2 * center.y - (center.y + 1)) + conic.c) -
            (conic.d * center.x ^ 2 +
              conic.e * center.x * (center.y + 1) +
              conic.f * (center.y + 1) ^ 2 + conic.a * center.x +
              conic.b * (center.y + 1) + conic.c) := by ring1
        _ = 0 := by rw [yInvariant]; ring1
    exact
      ⟨Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left
        (Purelib.Algebra.Field.Characteristic.Nonzero.negative_two_nonzero twoNonzero)
          firstProductZero,
        Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left
          (Purelib.Algebra.Field.Characteristic.Nonzero.negative_two_nonzero twoNonzero)
          secondProductZero⟩

/-- The printed center formula satisfies both center equations whenever the displayed determinant is nonzero. -/
theorem centerPoint_isCenter (conic : Conic K)
    (discriminantNonzero : conic.centerDiscriminant ≠ 0) :
    conic.IsCenter conic.centerPoint := by
  have discriminantCancel :
      conic.centerDiscriminant * conic.centerDiscriminant⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel _ discriminantNonzero
  constructor
  · unfold Conic.centerPoint
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      2 * conic.d *
            ((2 * conic.a * conic.f - conic.b * conic.e) *
              conic.centerDiscriminant⁻¹) +
          conic.e *
            ((2 * conic.b * conic.d - conic.a * conic.e) *
              conic.centerDiscriminant⁻¹) + conic.a =
        2 * conic.d *
            ((2 * conic.a * conic.f - conic.b * conic.e) *
              conic.centerDiscriminant⁻¹) +
          conic.e *
            ((2 * conic.b * conic.d - conic.a * conic.e) *
              conic.centerDiscriminant⁻¹) +
          conic.a *
            (conic.centerDiscriminant * conic.centerDiscriminant⁻¹) := by
              rw [discriminantCancel]
              ring1
      _ =
        (2 * conic.d * (2 * conic.a * conic.f - conic.b * conic.e) +
            conic.e * (2 * conic.b * conic.d - conic.a * conic.e) +
            conic.a * conic.centerDiscriminant) *
          conic.centerDiscriminant⁻¹ := by ring1
      _ = 0 := by unfold Conic.centerDiscriminant; ring1
  · unfold Conic.centerPoint
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      conic.e *
            ((2 * conic.a * conic.f - conic.b * conic.e) *
              conic.centerDiscriminant⁻¹) +
          2 * conic.f *
            ((2 * conic.b * conic.d - conic.a * conic.e) *
              conic.centerDiscriminant⁻¹) + conic.b =
        conic.e *
            ((2 * conic.a * conic.f - conic.b * conic.e) *
              conic.centerDiscriminant⁻¹) +
          2 * conic.f *
            ((2 * conic.b * conic.d - conic.a * conic.e) *
              conic.centerDiscriminant⁻¹) +
          conic.b *
            (conic.centerDiscriminant * conic.centerDiscriminant⁻¹) := by
              rw [discriminantCancel]
              ring1
      _ =
        (conic.e * (2 * conic.a * conic.f - conic.b * conic.e) +
            2 * conic.f * (2 * conic.b * conic.d - conic.a * conic.e) +
            conic.b * conic.centerDiscriminant) *
          conic.centerDiscriminant⁻¹ := by ring1
      _ = 0 := by unfold Conic.centerDiscriminant; ring1

/-- Every center equals the printed formula in the nonsingular case. -/
theorem center_eq_centerPoint (conic : Conic K) (center :
  Plane.Point K)
    (discriminantNonzero : conic.centerDiscriminant ≠ 0)
    (isCenter : conic.IsCenter center) :
    center = conic.centerPoint := by
  rcases isCenter with ⟨firstEquation, secondEquation⟩
  have xCleared :
      conic.centerDiscriminant * center.x =
        2 * conic.a * conic.f - conic.b * conic.e := by
    calc
      conic.centerDiscriminant * center.x =
        2 * conic.a * conic.f - conic.b * conic.e +
          conic.e *
            (conic.e * center.x + 2 * conic.f * center.y + conic.b) -
          2 * conic.f *
            (2 * conic.d * center.x + conic.e * center.y + conic.a) := by
              unfold Conic.centerDiscriminant
              ring1
      _ = 2 * conic.a * conic.f - conic.b * conic.e := by
        rw [firstEquation, secondEquation]
        ring1
  have yCleared :
      conic.centerDiscriminant * center.y =
        2 * conic.b * conic.d - conic.a * conic.e := by
    calc
      conic.centerDiscriminant * center.y =
        2 * conic.b * conic.d - conic.a * conic.e +
          conic.e *
            (2 * conic.d * center.x + conic.e * center.y + conic.a) -
          2 * conic.d *
            (conic.e * center.x + 2 * conic.f * center.y + conic.b) := by
              unfold Conic.centerDiscriminant
              ring1
      _ = 2 * conic.b * conic.d - conic.a * conic.e := by
        rw [firstEquation, secondEquation]
        ring1
  apply Plane.Point.ext
  · exact (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] {denominator value numerator : K}
    (denominatorNonzero : denominator ≠ 0) (cleared : denominator * value = numerator) =>
    (Purelib.Algebra.Field.Inverse.eq_div_of_mul_eq (K := K) (left := value) (right := numerator) (denominator :=
    denominator) denominatorNonzero ((mul_comm value denominator).trans cleared) : value = numerator / denominator))
      discriminantNonzero xCleared
  · exact (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] {denominator value numerator : K}
    (denominatorNonzero : denominator ≠ 0) (cleared : denominator * value = numerator) =>
    (Purelib.Algebra.Field.Inverse.eq_div_of_mul_eq (K := K) (left := value) (right := numerator) (denominator :=
    denominator) denominatorNonzero ((mul_comm value denominator).trans cleared) : value = numerator / denominator))
      discriminantNonzero yCleared

/-- The nonsingular case of Theorem 99, with its explicit unique witness. -/
theorem unique_center_of_discriminant_ne_zero (conic : Conic
  K)
    (discriminantNonzero : conic.centerDiscriminant ≠ 0) :
    ∃! center : Plane.Point K, conic.IsCenter center := by
  refine ⟨conic.centerPoint, centerPoint_isCenter conic discriminantNonzero,
    ?_⟩
  intro center isCenter
  exact center_eq_centerPoint conic center discriminantNonzero isCenter

/-- A nonzero horizontal displacement changes the original point. -/
private theorem shiftedPoint_ne_of_x (point : Plane.Point K)
  {shiftX shiftY : K}
    (shiftNonzero : shiftX ≠ 0) :
    (⟨point.x + shiftX, point.y + shiftY⟩ : Plane.Point K) ≠ point := by
  intro equalPoints
  have equalX := congrArg Plane.Point.x equalPoints
  change point.x + shiftX = point.x at equalX
  apply shiftNonzero
  calc
    shiftX = (point.x + shiftX) - point.x := by ring1
    _ = point.x - point.x := by rw [equalX]
    _ = 0 := by ring1

/-- A nonzero vertical displacement changes the original point. -/
private theorem shiftedPoint_ne_of_y (point : Plane.Point K)
  {shiftX shiftY : K}
    (shiftNonzero : shiftY ≠ 0) :
    (⟨point.x + shiftX, point.y + shiftY⟩ : Plane.Point K) ≠ point := by
  intro equalPoints
  have equalY := congrArg Plane.Point.y equalPoints
  change point.y + shiftY = point.y at equalY
  apply shiftNonzero
  calc
    shiftY = (point.y + shiftY) - point.y := by ring1
    _ = point.y - point.y := by rw [equalY]
    _ = 0 := by ring1

/-- A singular center always has a second, explicitly displaced center. -/
theorem secondCenter_of_discriminant_zero [DecidableEq K]
    (conic : Conic K) (twoNonzero : (2 : K) ≠ 0)
    (discriminantZero : conic.centerDiscriminant = 0)
    (center : Plane.Point K) (isCenter : conic.IsCenter center) :
    ∃ other : Plane.Point K, other ≠ center ∧ conic.IsCenter other := by
  rcases isCenter with ⟨firstEquation, secondEquation⟩
  by_cases dZero : conic.d = 0
  · have eSquareZero : conic.e * conic.e = 0 := by
      calc
        conic.e * conic.e = conic.centerDiscriminant := by
          unfold Conic.centerDiscriminant
          rw [dZero]
          ring1
        _ = 0 := discriminantZero
    have eZero : conic.e = 0 := by
      by_cases eZero : conic.e = 0
      · exact eZero
      · exact False.elim
          ((Algebra.Field.ExplicitField.mul_ne_zero eZero eZero) eSquareZero)
    have fNonzero : conic.f ≠ 0 := by
      rcases conic.quadratic_nonzero with dNonzero | eNonzero | fNonzero
      · exact False.elim (dNonzero dZero)
      · exact False.elim (eNonzero eZero)
      · exact fNonzero
    have twoFNonzero : 2 * conic.f ≠ 0 :=
      Algebra.Field.ExplicitField.mul_ne_zero twoNonzero fNonzero
    let other : Plane.Point K :=
      ⟨center.x + 2 * conic.f, center.y - conic.e⟩
    refine ⟨other, ?_, ?_⟩
    · dsimp only [other]
      simpa only [sub_eq_add_neg] using
        shiftedPoint_ne_of_x center (shiftY := -conic.e) twoFNonzero
    · constructor
      · dsimp only [other]
        calc
          2 * conic.d * (center.x + 2 * conic.f) +
              conic.e * (center.y - conic.e) + conic.a =
            (2 * conic.d * center.x + conic.e * center.y + conic.a) -
              conic.centerDiscriminant := by
                unfold Conic.centerDiscriminant
                ring1
          _ = 0 := by rw [firstEquation, discriminantZero]; ring1
      · dsimp only [other]
        calc
          conic.e * (center.x + 2 * conic.f) +
              2 * conic.f * (center.y - conic.e) + conic.b =
            conic.e * center.x + 2 * conic.f * center.y + conic.b := by
              ring1
          _ = 0 := secondEquation
  · have twoDNonzero : 2 * conic.d ≠ 0 :=
      Algebra.Field.ExplicitField.mul_ne_zero twoNonzero dZero
    have negativeTwoDNonzero : -(2 * conic.d) ≠ 0 := by
      intro negativeZero
      apply twoDNonzero
      calc
        2 * conic.d = -(-(2 * conic.d)) := by ring1
        _ = -0 := by rw [negativeZero]
        _ = 0 := neg_zero
    let other : Plane.Point K :=
      ⟨center.x + conic.e, center.y - 2 * conic.d⟩
    refine ⟨other, ?_, ?_⟩
    · dsimp only [other]
      simpa only [sub_eq_add_neg] using
        shiftedPoint_ne_of_y center (shiftX := conic.e)
          negativeTwoDNonzero
    · constructor
      · dsimp only [other]
        calc
          2 * conic.d * (center.x + conic.e) +
              conic.e * (center.y - 2 * conic.d) + conic.a =
            2 * conic.d * center.x + conic.e * center.y + conic.a := by
              ring1
          _ = 0 := firstEquation
      · dsimp only [other]
        calc
          conic.e * (center.x + conic.e) +
              2 * conic.f * (center.y - 2 * conic.d) + conic.b =
            (conic.e * center.x + 2 * conic.f * center.y + conic.b) +
              conic.centerDiscriminant := by
                unfold Conic.centerDiscriminant
                ring1
          _ = 0 := by rw [secondEquation, discriminantZero]; ring1

/-- A center of a singular conic forces the printed row proportion. -/
theorem centerRowsEquivalent_of_discriminant_zero_and_center
    (conic : Conic K)
    (discriminantZero : conic.centerDiscriminant = 0)
    (center : Plane.Point K) (isCenter : conic.IsCenter center) :
    conic.CenterRowsEquivalent := by
  rcases isCenter with ⟨firstEquation, secondEquation⟩
  unfold Conic.CenterRowsEquivalent Conic.OrderedTriplesEquivalent
  constructor
  · calc
      conic.e * conic.e = conic.e ^ 2 := by ring1
      _ = 4 * conic.d * conic.f := by
        calc
          conic.e ^ 2 =
              conic.centerDiscriminant + 4 * conic.d * conic.f := by
                unfold Conic.centerDiscriminant
                ring1
          _ = 4 * conic.d * conic.f := by rw [discriminantZero]; ring1
      _ = (2 * conic.d) * (2 * conic.f) := by ring1
  · constructor
    · calc
        conic.e * conic.a =
            (2 * conic.d) * conic.b +
              conic.e *
                (2 * conic.d * center.x + conic.e * center.y + conic.a) -
              2 * conic.d *
                (conic.e * center.x + 2 * conic.f * center.y + conic.b) -
              conic.centerDiscriminant * center.y := by
                unfold Conic.centerDiscriminant
                ring1
        _ = (2 * conic.d) * conic.b := by
          rw [firstEquation, secondEquation, discriminantZero]
          ring1
    · calc
        (2 * conic.f) * conic.a =
            conic.e * conic.b +
              2 * conic.f *
                (2 * conic.d * center.x + conic.e * center.y + conic.a) -
              conic.e *
                (conic.e * center.x + 2 * conic.f * center.y + conic.b) +
              conic.centerDiscriminant * center.x := by
                unfold Conic.centerDiscriminant
                ring1
        _ = conic.e * conic.b := by
          rw [firstEquation, secondEquation, discriminantZero]
          ring1

/-- The compatible singular equations have a concrete solution. -/
theorem center_exists_of_discriminant_zero_and_rowsEquivalent
    [DecidableEq K] (conic : Conic K) (twoNonzero : (2 : K) ≠ 0)
    (discriminantZero : conic.centerDiscriminant = 0)
    (rowsEquivalent : conic.CenterRowsEquivalent) :
    ∃ center : Plane.Point K, conic.IsCenter center := by
  unfold Conic.CenterRowsEquivalent Conic.OrderedTriplesEquivalent at rowsEquivalent
  rcases rowsEquivalent with ⟨_, secondProportion, thirdProportion⟩
  by_cases dZero : conic.d = 0
  · have eSquareZero : conic.e * conic.e = 0 := by
      calc
        conic.e * conic.e = conic.centerDiscriminant := by
          unfold Conic.centerDiscriminant
          rw [dZero]
          ring1
        _ = 0 := discriminantZero
    have eZero : conic.e = 0 := by
      by_cases eZero : conic.e = 0
      · exact eZero
      · exact False.elim
          ((Algebra.Field.ExplicitField.mul_ne_zero eZero eZero) eSquareZero)
    have fNonzero : conic.f ≠ 0 := by
      rcases conic.quadratic_nonzero with dNonzero | eNonzero | fNonzero
      · exact False.elim (dNonzero dZero)
      · exact False.elim (eNonzero eZero)
      · exact fNonzero
    have twoFNonzero : 2 * conic.f ≠ 0 :=
      Algebra.Field.ExplicitField.mul_ne_zero twoNonzero fNonzero
    have aZero : conic.a = 0 := by
      apply Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left twoFNonzero
      calc
        (2 * conic.f) * conic.a = conic.e * conic.b := thirdProportion
        _ = 0 := by rw [eZero]; ring1
    let center : Plane.Point K := ⟨0, -conic.b / (2 * conic.f)⟩
    refine ⟨center, ?_⟩
    constructor
    · dsimp only [center]
      rw [dZero, eZero, aZero]
      ring1
    · dsimp only [center]
      calc
        conic.e * 0 + 2 * conic.f * (-conic.b / (2 * conic.f)) +
            conic.b =
          (-conic.b / (2 * conic.f)) * (2 * conic.f) + conic.b := by
            ring1
        _ = -conic.b + conic.b := by
          rw [Algebra.Field.ExplicitField.div_mul_cancel (-conic.b) twoFNonzero]
        _ = 0 := by ring1
  · have twoDNonzero : 2 * conic.d ≠ 0 :=
      Algebra.Field.ExplicitField.mul_ne_zero twoNonzero dZero
    let center : Plane.Point K := ⟨-conic.a / (2 * conic.d), 0⟩
    refine ⟨center, ?_⟩
    constructor
    · dsimp only [center]
      calc
        2 * conic.d * (-conic.a / (2 * conic.d)) +
            conic.e * 0 + conic.a =
          (-conic.a / (2 * conic.d)) * (2 * conic.d) + conic.a := by
            ring1
        _ = -conic.a + conic.a := by
          rw [Algebra.Field.ExplicitField.div_mul_cancel (-conic.a) twoDNonzero]
        _ = 0 := by ring1
    · dsimp only [center]
      apply Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left twoDNonzero
      calc
        (2 * conic.d) *
            (conic.e * (-conic.a / (2 * conic.d)) +
              2 * conic.f * 0 + conic.b) =
          conic.e *
              ((-conic.a / (2 * conic.d)) * (2 * conic.d)) +
            (2 * conic.d) * conic.b := by ring1
        _ = conic.e * (-conic.a) + (2 * conic.d) * conic.b := by
          rw [Algebra.Field.ExplicitField.div_mul_cancel (-conic.a) twoDNonzero]
        _ = 0 := by rw [← secondProportion]; ring1

/-- The compatible singular case of Theorem 99 has at least two centers. -/
theorem multipleCenters_of_discriminant_zero_and_rowsEquivalent
    [DecidableEq K] (conic : Conic K) (twoNonzero : (2 : K) ≠ 0)
    (discriminantZero : conic.centerDiscriminant = 0)
    (rowsEquivalent : conic.CenterRowsEquivalent) :
    conic.HasMultipleCenters := by
  rcases center_exists_of_discriminant_zero_and_rowsEquivalent conic
      twoNonzero discriminantZero rowsEquivalent with ⟨first, firstCenter⟩
  rcases secondCenter_of_discriminant_zero conic twoNonzero
      discriminantZero first firstCenter with ⟨second, different, secondCenter⟩
  exact ⟨second, first, different, secondCenter, firstCenter⟩

/-- The incompatible singular case of Theorem 99 has no center. -/
theorem noCenter_of_discriminant_zero_and_rowsNotEquivalent
    (conic : Conic K) (discriminantZero : conic.centerDiscriminant = 0)
    (rowsNotEquivalent : ¬ conic.CenterRowsEquivalent) :
    ¬ ∃ center : Plane.Point K, conic.IsCenter center := by
  rintro ⟨center, isCenter⟩
  exact rowsNotEquivalent
    (centerRowsEquivalent_of_discriminant_zero_and_center conic
      discriminantZero center isCenter)

/-- Theorem 99 (Conic center), including the unique, multiple, and empty solution cases and the exact displayed formula.
-/
theorem conic_center [DecidableEq K] (conic : Conic K)
    (twoNonzero : (2 : K) ≠ 0) :
    ((∃! center : Plane.Point K, conic.IsCenter center) ↔
        conic.centerDiscriminant ≠ 0) ∧
      (conic.centerDiscriminant ≠ 0 →
        conic.IsCenter conic.centerPoint ∧
          ∀ center : Plane.Point K, conic.IsCenter center →
            center = conic.centerPoint) ∧
      (conic.centerDiscriminant = 0 →
        (conic.HasMultipleCenters ↔ conic.CenterRowsEquivalent)) ∧
      (conic.centerDiscriminant = 0 →
        ((¬ ∃ center : Plane.Point K, conic.IsCenter center) ↔
          ¬ conic.CenterRowsEquivalent)) := by
  constructor
  · constructor
    · rintro ⟨center, isCenter, unique⟩ discriminantZero
      rcases secondCenter_of_discriminant_zero conic twoNonzero
          discriminantZero center isCenter with ⟨other, different, otherCenter⟩
      exact different (unique other otherCenter)
    · exact unique_center_of_discriminant_ne_zero conic
  · constructor
    · intro discriminantNonzero
      exact
        ⟨centerPoint_isCenter conic discriminantNonzero,
          fun center isCenter =>
            center_eq_centerPoint conic center discriminantNonzero isCenter⟩
    · constructor
      · intro discriminantZero
        constructor
        · rintro ⟨first, _, _, firstCenter, _⟩
          exact centerRowsEquivalent_of_discriminant_zero_and_center conic
            discriminantZero first firstCenter
        · exact multipleCenters_of_discriminant_zero_and_rowsEquivalent conic
            twoNonzero discriminantZero
      · intro discriminantZero
        constructor
        · intro noCenter rowsEquivalent
          exact noCenter
            (center_exists_of_discriminant_zero_and_rowsEquivalent conic
              twoNonzero discriminantZero rowsEquivalent)
        · exact noCenter_of_discriminant_zero_and_rowsNotEquivalent conic
            discriminantZero

/-- Centers are closed under every displayed affine combination. -/
theorem isCenter_affineCombination (conic : Conic K)
    (first second : Plane.Point K) (firstCenter : conic.IsCenter first)
    (secondCenter : conic.IsCenter second)
    (leftWeight rightWeight : K) (weights : leftWeight + rightWeight = 1) :
    conic.IsCenter
      (Purelib.Geometry.Plane.Point.Affine.affineCombination leftWeight first rightWeight second) := by
  rcases firstCenter with ⟨firstEquation₁, firstEquation₂⟩
  rcases secondCenter with ⟨secondEquation₁, secondEquation₂⟩
  constructor
  · unfold Affine.affineCombination
    calc
      2 * conic.d *
            (leftWeight * first.x + rightWeight * second.x) +
          conic.e * (leftWeight * first.y + rightWeight * second.y) +
          conic.a =
        leftWeight *
            (2 * conic.d * first.x + conic.e * first.y + conic.a) +
          rightWeight *
            (2 * conic.d * second.x + conic.e * second.y + conic.a) +
          (1 - (leftWeight + rightWeight)) * conic.a := by ring1
      _ = 0 := by
        rw [firstEquation₁, secondEquation₁, weights]
        ring1
  · unfold Affine.affineCombination
    calc
      conic.e * (leftWeight * first.x + rightWeight * second.x) +
          2 * conic.f *
            (leftWeight * first.y + rightWeight * second.y) + conic.b =
        leftWeight *
            (conic.e * first.x + 2 * conic.f * first.y + conic.b) +
          rightWeight *
            (conic.e * second.x + 2 * conic.f * second.y + conic.b) +
          (1 - (leftWeight + rightWeight)) * conic.b := by ring1
      _ = 0 := by
        rw [firstEquation₂, secondEquation₂, weights]
        ring1

/-- Exercise 15.2: every point on the line through two distinct centers is a center. The witness is the finite affine
decomposition from Theorem 9. -/
theorem exercise_15_2 [DecidableEq K] (conic : Conic K)
    (first second point : Plane.Point K) (distinct : first ≠ second)
    (firstCenter : conic.IsCenter first) (secondCenter : conic.IsCenter second)
    (onLine : (Incidence.lineThrough first second distinct).Contains point) :
    conic.IsCenter point := by
  rcases (Affine.affineCombination_iff_on_line first second point distinct).1 onLine with
    ⟨leftWeight, rightWeight, weights, combination⟩
  rw [← combination]
  exact isCenter_affineCombination conic first second firstCenter secondCenter
    leftWeight rightWeight weights

end Purelib.Curves.Plane.Conic

end

section
@[expose] public section

/-!
# Divine Proportions, §15.4 and Exercise 19.3: quadrolas

A quadrola is given by one finite Archimedes polynomial in the two focal
quadrances and its associated quadrance.  The apparent quartic terms cancel
to an explicit conic.  Its gradient tangent satisfies the equal-spread
reflection property by a denominator-cleared polynomial identity.
-/

namespace Purelib.Curves.Plane.Conic.Scale.CoefficientScale

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Scaling every conic coefficient multiplies its center discriminant by the square of the scale. -/
theorem discriminant
    {source target : Conic K} {scale : K}
    (scaled : Scale.CoefficientScale source target scale) :
    source.centerDiscriminant = scale ^ 2 * target.centerDiscriminant := by
  unfold Conic.centerDiscriminant
  rw [scaled.d, scaled.e, scaled.f]
  ring1

/-- A center of the target conic remains a center after the retained coefficient scaling. -/
theorem isCenter
    {source target : Conic K} {scale : K}
    (scaled : Scale.CoefficientScale source target scale) (center : Plane.Point K)
    (targetCenter : target.IsCenter center) :
    source.IsCenter center := by
  rcases targetCenter with ⟨firstEquation, secondEquation⟩
  constructor
  · rw [scaled.d, scaled.e, scaled.a]
    calc
      2 * (scale * target.d) * center.x +
          scale * target.e * center.y + scale * target.a =
        scale * (2 * target.d * center.x + target.e * center.y +
          target.a) := by ring1
      _ = 0 := by rw [firstEquation]; ring1
  · rw [scaled.e, scaled.f, scaled.b]
    calc
      scale * target.e * center.x +
          2 * (scale * target.f) * center.y + scale * target.b =
        scale * (target.e * center.x + 2 * target.f * center.y +
          target.b) := by ring1
      _ = 0 := by rw [secondEquation]; ring1

end Purelib.Curves.Plane.Conic.Scale.CoefficientScale

end
