module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Geometry.Quadratic.Ternary.RationalMinkowski
import Purelib.Data.Rat.Fraction.Basic
public import Purelib.Geometry.Rotations.Ternary.Split.Parabolic
import Purelib.Geometry.Quadratic.Ternary.SplitNullConic
public import Purelib.Geometry.Rotations.Ternary.Split.Theory
import Purelib.Algebra.Clifford.Ternary.Basic
import Purelib.Algebra.Quadratic.Ternary.Basic
import Purelib.Algebra.Quadratic.Ternary.Minkowski
import Purelib.Geometry.Rotations.Orientation.Handedness
import Purelib.Geometry.Rotations.Ternary.Basic
import Purelib.Geometry.Rotations.Ternary.Clifford

import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
public import Purelib.Geometry.Rotations.Ternary.Cayley
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Quadratic.Ternary.Isometry
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Ring.Nat

open Purelib

open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm

open Purelib.Algebra.Quadratic

open Purelib.Algebra.Quadratic.Ternary.Basic

open Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Data.Rat

open Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Geometry.Quadratic.Ternary.RationalMinkowski

open Purelib.Geometry.Quadratic.Ternary.SplitNullConic

open Purelib.Geometry.Rotations.Orientation

open Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm

open Purelib.Geometry.Rotations.Ternary.Cayley

open Purelib.Geometry.Rotations.Ternary.Cayley.TernaryForm

open Purelib.Geometry.Rotations.Ternary.Split.Parabolic

open Purelib.Geometry.Rotations.Ternary.Split.Theory

open Purelib.LinearAlgebra

@[expose] public section

/-!
# Completed finite theory for general ternary rotations

This module packages the separate constructive components of Problem 71 into
one public result.  The general package includes the quotient-free projective
Clifford correspondence, the cached axis/chart/spread interface for every
rotation, and the affine Cayley product.  The rational Minkowski package adds
the explicit two-by-two matrix algebra, complete null-conic parametrization,
parabolic families, and the evaluated zero-handedness example.
-/

namespace Purelib.Geometry.Rotations.Ternary.Theory

open Purelib.LinearAlgebra.Coordinates3

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section TernaryForm

set_option genInjectivity false in
/-- The finite-coordinate rotation theory of one displayed nondegenerate ternary form.

The original form and nonzero-two certificate index the retained projective correspondence, per-rotation axis/spread
witnesses and the two affine-cap laws. -/
structure TernaryForm.GeneralRotationTheory (form : Ternary.Basic.TernaryForm K)
    (twoNonzero : (2 : K) ≠ 0) where
  /-- The retained projective Clifford correspondence for the original ternary form. -/ projective :
    TernaryForm.ProjectiveCliffordCorrespondence form twoNonzero
  /-- Construct the cached axis, chart, and geometric spread witness for each rotation of the original form. -/
    axisSpread : (rotation : form.SpecialOrthogonal) →
    TernaryForm.RotationAxisSpreadWitness form rotation
  /-- Equal defined caps have equal displayed anchor vectors. -/ capInjective : ∀ left right : Coordinates3.Vector K,
    (leftDefined : (TernaryForm.cayleyDenominator form) left ≠ 0) →
    (rightDefined : (TernaryForm.cayleyDenominator form) right ≠ 0) →
    (TernaryForm.capRotation form) left leftDefined =
      (TernaryForm.capRotation form) right rightDefined → left = right
  /-- Multiplication of defined caps agrees with the defined determinant-corrected anchor product. -/ capProduct : ∀
    left right : Coordinates3.Vector K,
    (leftDefined : (TernaryForm.cayleyDenominator form) left ≠ 0) →
    (rightDefined : (TernaryForm.cayleyDenominator form) right ≠ 0) →
    (productDefined : (TernaryForm.anchorProductDenominator form) left right ≠ 0) →
    SpecialOrthogonal.mul
        ((TernaryForm.capRotation form) left leftDefined)
        ((TernaryForm.capRotation form) right rightDefined) =
      (TernaryForm.capRotation form) ((TernaryForm.anchorProduct form) left right productDefined)
        ((TernaryForm.cayleyDenominator_anchorProduct_ne_zero form) left right
          leftDefined rightDefined productDefined)

constructive_injectivity TernaryForm.GeneralRotationTheory

/-- Assemble the projective, affine-chart, and geometric-spread layers for an arbitrary displayed ternary form. -/
def TernaryForm.generalRotationTheory [DecidableEq K]
    (form : Ternary.Basic.TernaryForm K) (twoNonzero : (2 : K) ≠ 0) :
    Geometry.Rotations.Ternary.Theory.TernaryForm.GeneralRotationTheory form twoNonzero where
  projective := form.projectiveCliffordCorrespondence twoNonzero
  axisSpread := fun rotation =>
    (TernaryForm.rotationAxisSpreadWitness form) rotation twoNonzero
  capInjective := fun left right leftDefined rightDefined equal =>
    (TernaryForm.capRotation_injective form) left right leftDefined rightDefined
      twoNonzero equal
  capProduct := fun left right leftDefined rightDefined productDefined =>
    (TernaryForm.capRotation_mul form) left right leftDefined rightDefined productDefined

end TernaryForm

section MinkowskiClifford

set_option genInjectivity false in
/-- A retained parabolic normal form for one nonidentity half-spread-zero split-form rotation.

The original Clifford preimage, scalar-normalized null axis, conic parameters and nonzero family parameter are cached
together. Their equations identify the supplied rotation and certify its fixed axis, characteristic polynomial and zero
handedness. -/
structure MinkowskiClifford.ParabolicClassification [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (rotation : (TernaryForm.minkowski oneNonzero).SpecialOrthogonal) where
  /-- The cached non-null Clifford preimage of the original rotation. -/ representative :
    (TernaryForm.minkowski oneNonzero).NonNullEvenClifford
  /-- The cached Clifford preimage acts as the original rotation. -/ represents : (NonNullEvenClifford.actionRotation
    representative) = rotation
  /-- The retained Clifford representative has nonzero scalar coordinate. -/ representativeScalarNonzero :
    representative.toEvenClifford.scalar ≠ 0
  /-- The cached scalar-normalized axis vector. -/ axis : Coordinates3.Vector K
  /-- The retained axis is exactly the representative vector scaled by the inverse scalar coordinate. -/ axis_eq : axis
    = Coordinates3.Vector.scale representative.toEvenClifford.scalar⁻¹
    representative.toEvenClifford.vector
  /-- The normalized retained axis is Minkowski null. -/ axisNull : (TernaryForm.minkowski oneNonzero).IsNull axis
  /-- The normalized retained axis is a nonzero vector. -/ axisNonzero : axis ≠ Coordinates3.Vector.zero
  /-- The retained complete null-conic parameter witness of the normalized axis. -/ coordinates :
    MinkowskiClifford.NullParameterWitness axis
  /-- The retained scalar parameter of the null-axis parabolic family. -/ parameter : K
  /-- The retained parabolic parameter is nonzero. -/ parameterNonzero : parameter ≠ 0
  /-- The original rotation is exactly the family member at the retained conic coordinates and parameter. -/ rotation_eq
    :
    rotation = MinkowskiClifford.parabolicRotationAt oneNonzero
      (MinkowskiClifford.nullParameter coordinates.first coordinates.second)
      (MinkowskiClifford.nullParameter_isNull oneNonzero coordinates.first coordinates.second)
      parameter
  /-- The original rotation fixes the null vector given by the retained conic coordinates. -/ fixedAxis :
    (Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act rotation.toIsometry) (MinkowskiClifford.nullParameter
        coordinates.first coordinates.second) =
      MinkowskiClifford.nullParameter coordinates.first coordinates.second
  /-- The original rotation has characteristic polynomial `(X - 1)³`. -/ characteristicUnipotent : ∀ X : K,
    Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3
  /-- Every transversal perpendicular to the retained conic axis has zero handedness under the original rotation. -/
    handednessZero : ∀ transversal : Coordinates3.Vector K,
    (TernaryForm.minkowski oneNonzero).Perpendicular transversal
      (MinkowskiClifford.nullParameter coordinates.first coordinates.second) →
    Handedness.handednessDet (MinkowskiClifford.nullParameter coordinates.first coordinates.second)
      transversal rotation.matrix = 0

constructive_injectivity MinkowskiClifford.ParabolicClassification

/-- For a displayed special-orthogonal matrix, the usual unipotent characteristic polynomial forces trace half spread
zero. Evaluations at `1` and `-1` recover the trace without polynomial extensionality or an infinite-root argument. -/
theorem MinkowskiClifford.rotationHalfSpread_eq_zero_of_characteristicUnipotent
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (rotation : (TernaryForm.minkowski oneNonzero).SpecialOrthogonal)
    (characteristic : ∀ X : K,
      Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3) :
    (TernaryForm.rotationHalfSpread (TernaryForm.minkowski oneNonzero)) rotation = 0 := by
  have atOne := characteristic 1
  rw [Matrix3.characteristicValue_expansion,
    rotation.determinantOne] at atOne
  have principalEqTrace :
      Matrix3.principalTrace rotation.matrix =
        Matrix3.trace rotation.matrix := by
    calc
      Matrix3.principalTrace rotation.matrix =
          (1 ^ 3 - Matrix3.trace rotation.matrix * 1 ^ 2 +
              Matrix3.principalTrace rotation.matrix * 1 - 1) +
            Matrix3.trace rotation.matrix := by ring1
      _ = (1 - 1) ^ 3 + Matrix3.trace rotation.matrix := by
        rw [atOne]
      _ = Matrix3.trace rotation.matrix := by ring1
  have atNegativeOne := characteristic (-1)
  rw [Matrix3.characteristicValue_expansion,
    rotation.determinantOne] at atNegativeOne
  have tracePlusPrincipal :
      Matrix3.trace rotation.matrix +
          Matrix3.principalTrace rotation.matrix = 6 := by
    calc
      Matrix3.trace rotation.matrix +
          Matrix3.principalTrace rotation.matrix =
        -((-1) ^ 3 - Matrix3.trace rotation.matrix * (-1) ^ 2 +
            Matrix3.principalTrace rotation.matrix * (-1) - 1) - 2 := by
          ring1
      _ = -((-1 - 1) ^ 3) - 2 := by rw [atNegativeOne]
      _ = 6 := by ring1
  have twiceTrace : 2 * Matrix3.trace rotation.matrix = 6 := by
    calc
      2 * Matrix3.trace rotation.matrix =
          Matrix3.trace rotation.matrix +
            Matrix3.principalTrace rotation.matrix := by
        rw [principalEqTrace]
        ring1
      _ = 6 := tracePlusPrincipal
  have traceDifferenceZero : Matrix3.trace rotation.matrix - 3 = 0 := by
    apply (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] {factor value : K} (factorNonzero : factor ≠ 0)
      (productZero : factor * value = 0) => (Purelib.Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left (R := K)
      (factor := factor) (value := value) factorNonzero productZero : value = 0))
      twoNonzero
    calc
      2 * (Matrix3.trace rotation.matrix - 3) =
          2 * Matrix3.trace rotation.matrix - 6 := by ring1
      _ = 0 := by rw [twiceTrace]; ring1
  have traceEqThree : Matrix3.trace rotation.matrix = 3 := by
    calc
      Matrix3.trace rotation.matrix =
          (Matrix3.trace rotation.matrix - 3) + 3 := by ring1
      _ = 0 + 3 := by rw [traceDifferenceZero]
      _ = 3 := by ring1
  unfold TernaryForm.rotationHalfSpread
  rw [traceEqThree]
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  ring1

/-- Every nonidentity half-spread-zero rotation of the displayed Minkowski form is constructively classified by a
nonzero rational-conic parameter pair and a nonzero scalar in its null-axis parabolic family. -/
def MinkowskiClifford.parabolicClassification [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (rotation : (TernaryForm.minkowski oneNonzero).SpecialOrthogonal)
    (spreadZero :
      (TernaryForm.rotationHalfSpread (TernaryForm.minkowski oneNonzero)) rotation = 0)
    (nonidentity : rotation.matrix ≠ Matrix3.identity) :
    Geometry.Rotations.Ternary.Theory.MinkowskiClifford.ParabolicClassification oneNonzero twoNonzero rotation := by
  let form := TernaryForm.minkowski oneNonzero
  let correspondence := form.projectiveCliffordCorrespondence twoNonzero
  let representative := correspondence.preimage rotation
  have represents : (NonNullEvenClifford.actionRotation representative) = rotation :=
    correspondence.action_preimage rotation
  have halfSpreadFormula :=
    (NonNullEvenClifford.rotationHalfSpread_actionRotation representative) twoNonzero
  rw [represents, spreadZero] at halfSpreadFormula
  have productZero :
      form.determinant *
          form.quadrance representative.toEvenClifford.vector *
          (Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford.norm representative.toEvenClifford)⁻¹ = 0 :=
            by
    simpa only [Algebra.Field.ExplicitField.div_eq_mul_inv] using
      halfSpreadFormula.symm
  have determinantQuadranceZero :
      form.determinant *
          form.quadrance representative.toEvenClifford.vector = 0 := by
    apply (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] {factor value : K} (factorNonzero : factor ≠ 0)
      (productZero : factor * value = 0) => (Purelib.Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left (R := K)
      (factor := factor) (value := value) factorNonzero productZero : value = 0))
      (Algebra.Field.ExplicitField.inv_ne_zero representative.normNonzero)
    calc
      (Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford.norm representative.toEvenClifford)⁻¹ *
          (form.determinant *
            form.quadrance representative.toEvenClifford.vector) =
        form.determinant *
          form.quadrance representative.toEvenClifford.vector *
          (Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford.norm representative.toEvenClifford)⁻¹ := by
            ring1
      _ = 0 := productZero
  have vectorNull :
      form.IsNull representative.toEvenClifford.vector := by
    exact (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] {factor value : K} (factorNonzero : factor ≠ 0)
      (productZero : factor * value = 0) => (Purelib.Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left (R := K)
      (factor := factor) (value := value) factorNonzero productZero : value = 0))
      form.determinantNonzero determinantQuadranceZero
  have scalarNonzero : representative.toEvenClifford.scalar ≠ 0 := by
    intro scalarZero
    apply representative.normNonzero
    unfold Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.EvenClifford.norm
    rw [scalarZero, vectorNull]
    ring1
  have vectorNonzero :
      representative.toEvenClifford.vector ≠ Coordinates3.Vector.zero := by
    intro vectorZero
    have equivalentIdentity :=
      (NonNullEvenClifford.equivalent_identity_iff_vector_eq_zero
        representative).2 vectorZero
    have representativeIdentity :=
      (NonNullEvenClifford.actionRotation_eq_identity_iff_equivalent_identity
          representative twoNonzero).2 equivalentIdentity
    apply nonidentity
    have rotationIdentity :
        rotation = SpecialOrthogonal.identity form := by
      calc
        rotation = (NonNullEvenClifford.actionRotation representative) := represents.symm
        _ = SpecialOrthogonal.identity form :=
          representativeIdentity
    exact congrArg
      (fun value : form.SpecialOrthogonal => value.matrix) rotationIdentity
  let axis := Coordinates3.Vector.scale representative.toEvenClifford.scalar⁻¹
    representative.toEvenClifford.vector
  have axisNull : form.IsNull axis :=
    form.isNull_scale representative.toEvenClifford.scalar⁻¹
      representative.toEvenClifford.vector vectorNull
  have inverseScalarNonzero :
      representative.toEvenClifford.scalar⁻¹ ≠ 0 :=
    Algebra.Field.ExplicitField.inv_ne_zero scalarNonzero
  have axisNonzero : axis ≠ Coordinates3.Vector.zero := by
    intro axisZero
    apply vectorNonzero
    apply Coordinates3.Vector.ext
    · apply (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] {factor value : K} (factorNonzero : factor ≠ 0)
      (productZero : factor * value = 0) => (Purelib.Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left (R := K)
      (factor := factor) (value := value) factorNonzero productZero : value = 0))
        inverseScalarNonzero
      exact congrArg Coordinates3.Vector.t axisZero
    · apply (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] {factor value : K} (factorNonzero : factor ≠ 0)
      (productZero : factor * value = 0) => (Purelib.Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left (R := K)
      (factor := factor) (value := value) factorNonzero productZero : value = 0))
        inverseScalarNonzero
      exact congrArg Coordinates3.Vector.r axisZero
    · apply (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] {factor value : K} (factorNonzero : factor ≠ 0)
      (productZero : factor * value = 0) => (Purelib.Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left (R := K)
      (factor := factor) (value := value) factorNonzero productZero : value = 0))
        inverseScalarNonzero
      exact congrArg Coordinates3.Vector.s axisZero
  let coordinates := MinkowskiClifford.nullParameterWitness oneNonzero twoNonzero
    axis axisNull axisNonzero
  let parameter := coordinates.factor⁻¹
  have parameterNonzero : parameter ≠ 0 :=
    Algebra.Field.ExplicitField.inv_ne_zero coordinates.factorNonzero
  let parameterAxis := MinkowskiClifford.nullParameter coordinates.first coordinates.second
  let parameterAxisNull :=
    MinkowskiClifford.nullParameter_isNull oneNonzero coordinates.first coordinates.second
  let parabolic := MinkowskiClifford.parabolicAt oneNonzero parameterAxis parameterAxisNull
    parameter
  have factorCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    coordinates.factor coordinates.factorNonzero
  have inverseFactorCancel : coordinates.factor⁻¹ * coordinates.factor = 1 := by
    calc
      coordinates.factor⁻¹ * coordinates.factor =
          coordinates.factor * coordinates.factor⁻¹ := by ring1
      _ = 1 := factorCancel
  have equivalent : (NonNullEvenClifford.Equivalent representative) parabolic := by
    refine ⟨representative.toEvenClifford.scalar⁻¹,
      inverseScalarNonzero, ?_⟩
    apply EvenClifford.ext
    · change 1 = representative.toEvenClifford.scalar⁻¹ *
        representative.toEvenClifford.scalar
      calc
        (1 : K) = representative.toEvenClifford.scalar *
            representative.toEvenClifford.scalar⁻¹ :=
          (Algebra.Field.ExplicitField.mul_inv_cancel
            representative.toEvenClifford.scalar scalarNonzero).symm
        _ = representative.toEvenClifford.scalar⁻¹ *
            representative.toEvenClifford.scalar := by ring1
    · change Coordinates3.Vector.scale parameter parameterAxis =
        Coordinates3.Vector.scale representative.toEvenClifford.scalar⁻¹
          representative.toEvenClifford.vector
      unfold parameterAxis
      rw [coordinates.parameter_spec]
      unfold parameter axis
      rw [Coordinates3.Vector.scale_scale, inverseFactorCancel, Coordinates3.Vector.one_scale]
  have rotationEq :
      rotation = MinkowskiClifford.parabolicRotationAt oneNonzero parameterAxis
        parameterAxisNull parameter := by
    calc
      rotation = (NonNullEvenClifford.actionRotation representative) := represents.symm
      _ = (NonNullEvenClifford.actionRotation parabolic) :=
        NonNullEvenClifford.actionRotation_respects_equivalent
          equivalent
      _ = MinkowskiClifford.parabolicRotationAt oneNonzero parameterAxis
          parameterAxisNull parameter := rfl
  refine
    { representative := representative
      represents := represents
      representativeScalarNonzero := scalarNonzero
      axis := axis
      axis_eq := rfl
      axisNull := axisNull
      axisNonzero := axisNonzero
      coordinates := coordinates
      parameter := parameter
      parameterNonzero := parameterNonzero
      rotation_eq := rotationEq
      fixedAxis := ?_
      characteristicUnipotent := ?_
      handednessZero := ?_ }
  · rw [rotationEq]
    exact MinkowskiClifford.parabolicRotationAt_fixedAxis oneNonzero parameterAxis
      parameterAxisNull parameter
  · intro X
    rw [rotationEq]
    exact MinkowskiClifford.parabolicRotationAt_characteristic oneNonzero parameterAxis
      parameterAxisNull parameter X
  · intro transversal perpendicular
    rw [rotationEq]
    exact MinkowskiClifford.parabolicRotationAt_handedness_zero oneNonzero parameterAxis
      transversal parameterAxisNull perpendicular parameter

/-- Characteristic-polynomial form of the complete classifier. This is the direct converse to
`parabolicRotationAt_characteristic`: every nonidentity rotation with characteristic polynomial `(X-1)^3` is one of the
displayed null-conic parabolic normal forms. -/
def MinkowskiClifford.parabolicClassificationOfCharacteristic [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (rotation : (TernaryForm.minkowski oneNonzero).SpecialOrthogonal)
    (characteristic : ∀ X : K,
      Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3)
    (nonidentity : rotation.matrix ≠ Matrix3.identity) :
    Geometry.Rotations.Ternary.Theory.MinkowskiClifford.ParabolicClassification oneNonzero twoNonzero rotation :=
  Geometry.Rotations.Ternary.Theory.MinkowskiClifford.parabolicClassification oneNonzero twoNonzero rotation
    (Geometry.Rotations.Ternary.Theory.MinkowskiClifford.rotationHalfSpread_eq_zero_of_characteristicUnipotent
      oneNonzero
      twoNonzero rotation characteristic)
    nonidentity

end MinkowskiClifford

section RationalMinkowski

/-- Exact rational specialization of the complete parabolic normal-form classifier. -/
def RationalMinkowski.classifyParabolic
    (rotation : (TernaryForm.SpecialOrthogonal
      Quadratic.Ternary.RationalMinkowski.form))
    (spreadZero : (TernaryForm.rotationHalfSpread Quadratic.Ternary.RationalMinkowski.form) rotation = 0)
    (nonidentity : rotation.matrix ≠ Matrix3.identity) :
    Geometry.Rotations.Ternary.Theory.MinkowskiClifford.ParabolicClassification
        Quadratic.Ternary.RationalMinkowski.oneNonzero
      Quadratic.Ternary.RationalMinkowski.twoNonzero rotation :=
  Geometry.Rotations.Ternary.Theory.MinkowskiClifford.parabolicClassification
      Quadratic.Ternary.RationalMinkowski.oneNonzero
    Quadratic.Ternary.RationalMinkowski.twoNonzero rotation
    spreadZero nonidentity

/-- Rational classifier from the paper's characteristic-polynomial description of a parabolic rotation. -/
def RationalMinkowski.classifyParabolicOfCharacteristic
    (rotation : (TernaryForm.SpecialOrthogonal
      Quadratic.Ternary.RationalMinkowski.form))
    (characteristic : ∀ X : Fraction.Basic.Rational,
      Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3)
    (nonidentity : rotation.matrix ≠ Matrix3.identity) :
    Geometry.Rotations.Ternary.Theory.MinkowskiClifford.ParabolicClassification
        Quadratic.Ternary.RationalMinkowski.oneNonzero
      Quadratic.Ternary.RationalMinkowski.twoNonzero rotation :=
  Geometry.Rotations.Ternary.Theory.MinkowskiClifford.parabolicClassificationOfCharacteristic
    Quadratic.Ternary.RationalMinkowski.oneNonzero
    Quadratic.Ternary.RationalMinkowski.twoNonzero rotation characteristic nonidentity

/-- The rational null axis remains in the affine Cayley chart even though the Minkowski determinant changes the
denominator from `1 + Q` to `1 - Q`. -/
theorem RationalMinkowski.parabolicAxis_cayleyDenominator :
    (TernaryForm.cayleyDenominator Quadratic.Ternary.RationalMinkowski.form) RationalMinkowski.parabolicAxis = 1 := by
  unfold TernaryForm.cayleyDenominator
  have nullQuadrance : (TernaryForm.quadrance
    Quadratic.Ternary.RationalMinkowski.form) RationalMinkowski.parabolicAxis = 0 :=
    RationalMinkowski.parabolicAxis_null
  rw [nullQuadrance]
  ring1

/-- The displayed rational parabolic axis has nonzero form-relative cap denominator. -/
theorem RationalMinkowski.parabolicCapDefined
    : (TernaryForm.cayleyDenominator Quadratic.Ternary.RationalMinkowski.form) RationalMinkowski.parabolicAxis ≠ 0
  := by
  rw [Geometry.Rotations.Ternary.Theory.RationalMinkowski.parabolicAxis_cayleyDenominator]
  exact Quadratic.Ternary.RationalMinkowski.oneNonzero

/-- The previously evaluated rational unipotent is exactly the new form-relative Cayley cap of its null anchor. -/
theorem RationalMinkowski.parabolic_capRotation :
    (TernaryForm.capRotation Quadratic.Ternary.RationalMinkowski.form) RationalMinkowski.parabolicAxis
      Geometry.Rotations.Ternary.Theory.RationalMinkowski.parabolicCapDefined =
      (NonNullEvenClifford.actionRotation RationalMinkowski.parabolicValue) := by
  apply SpecialOrthogonal.eq_of_matrix_eq
  rfl

/-- The displayed rational null-axis cap has half spread zero. -/
theorem RationalMinkowski.parabolic_cap_halfSpread :
    (TernaryForm.rotationHalfSpread Quadratic.Ternary.RationalMinkowski.form)
      ((TernaryForm.capRotation Quadratic.Ternary.RationalMinkowski.form) RationalMinkowski.parabolicAxis
        Geometry.Rotations.Ternary.Theory.RationalMinkowski.parabolicCapDefined) = 0 := by
  rw [(TernaryForm.rotationHalfSpread_cap Quadratic.Ternary.RationalMinkowski.form) RationalMinkowski.parabolicAxis
    Geometry.Rotations.Ternary.Theory.RationalMinkowski.parabolicCapDefined
    Quadratic.Ternary.RationalMinkowski.twoNonzero]
  have nullQuadrance : (TernaryForm.quadrance
    Quadratic.Ternary.RationalMinkowski.form) RationalMinkowski.parabolicAxis = 0 :=
    RationalMinkowski.parabolicAxis_null
  rw [nullQuadrance]
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  ring1

/-- A concrete rational anchor on the Minkowski unit quadric. Its affine cap is excluded because the
discriminant-corrected denominator is `1 - Q`. -/
def RationalMinkowski.excludedCapAnchor : Coordinates3.Vector Fraction.Basic.Rational := ⟨1, 0, 0⟩

/-- The displayed Minkowski unit-axis anchor has zero cap denominator. -/
theorem RationalMinkowski.excludedCapAnchor_cayleyDenominator_zero :
    (TernaryForm.cayleyDenominator Quadratic.Ternary.RationalMinkowski.form)
      Geometry.Rotations.Ternary.Theory.RationalMinkowski.excludedCapAnchor = 0 := by
  unfold TernaryForm.cayleyDenominator Quadratic.Ternary.RationalMinkowski.form
  rw [TernaryForm.minkowski_determinant,
    TernaryForm.quadrance_minkowski]
  unfold Geometry.Rotations.Ternary.Theory.RationalMinkowski.excludedCapAnchor
  ring1

set_option genInjectivity false in
/-- The rational split-form rotation theory with an evaluated parabolic and exact classifiers.

The original rational form indexes the general and split packages. The retained parabolic certificate and both
classifier functions refer to the same displayed rotations and their original characteristic or half-spread evidence. -/
structure RationalMinkowski.CompleteTheory where
  /-- The complete finite-coordinate rotation theory for the retained ternary form. -/ general :
    Geometry.Rotations.Ternary.Theory.TernaryForm.GeneralRotationTheory Quadratic.Ternary.RationalMinkowski.form
    Quadratic.Ternary.RationalMinkowski.twoNonzero
  /-- The retained split Clifford algebra, null-conic, and parabolic-family package. -/ split :
    MinkowskiClifford.SplitTheory Quadratic.Ternary.RationalMinkowski.oneNonzero
        Quadratic.Ternary.RationalMinkowski.twoNonzero
  /-- The exact certificate for the displayed rational Minkowski parabolic. -/ evaluatedParabolic :
    RationalMinkowski.ParabolicCertificate (NonNullEvenClifford.actionRotation RationalMinkowski.parabolicValue)
  /-- Classify each nonidentity rational Minkowski rotation of half spread zero by retained null-conic parabolic data.
  -/ classifyParabolic : ∀ rotation : (TernaryForm.SpecialOrthogonal
    Quadratic.Ternary.RationalMinkowski.form),
    (TernaryForm.rotationHalfSpread Quadratic.Ternary.RationalMinkowski.form) rotation = 0 →
    rotation.matrix ≠ Matrix3.identity →
      Geometry.Rotations.Ternary.Theory.MinkowskiClifford.ParabolicClassification
          Quadratic.Ternary.RationalMinkowski.oneNonzero
        Quadratic.Ternary.RationalMinkowski.twoNonzero rotation
  /-- Classify each nonidentity rational Minkowski rotation with characteristic polynomial `(X - 1)³` by retained
    parabolic data. -/ classifyParabolicCharacteristic : ∀ rotation : (TernaryForm.SpecialOrthogonal
      Quadratic.Ternary.RationalMinkowski.form),
    (∀ X : Fraction.Basic.Rational,
      Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3) →
    rotation.matrix ≠ Matrix3.identity →
      Geometry.Rotations.Ternary.Theory.MinkowskiClifford.ParabolicClassification
          Quadratic.Ternary.RationalMinkowski.oneNonzero
        Quadratic.Ternary.RationalMinkowski.twoNonzero rotation

constructive_injectivity RationalMinkowski.CompleteTheory

/-- Assemble every completed finite clause of the Minkowski specialization. -/
def RationalMinkowski.completeTheory : RationalMinkowski.CompleteTheory where
  general := Geometry.Rotations.Ternary.Theory.TernaryForm.generalRotationTheory
      Quadratic.Ternary.RationalMinkowski.form
    Quadratic.Ternary.RationalMinkowski.twoNonzero
  split := MinkowskiClifford.splitTheory Quadratic.Ternary.RationalMinkowski.oneNonzero
      Quadratic.Ternary.RationalMinkowski.twoNonzero
  evaluatedParabolic := RationalMinkowski.parabolicCertificate
  classifyParabolic := fun rotation spreadZero nonidentity =>
    Geometry.Rotations.Ternary.Theory.RationalMinkowski.classifyParabolic rotation spreadZero nonidentity
  classifyParabolicCharacteristic := fun rotation characteristic nonidentity =>
    Geometry.Rotations.Ternary.Theory.RationalMinkowski.classifyParabolicOfCharacteristic rotation characteristic
      nonidentity

end RationalMinkowski

set_option genInjectivity false in
/-- A general ternary rotation theory paired with its fully evaluated rational split-form model.

The supplied form and nonzero-two certificate index the general package; the rational model retains its own original
form, evaluated parabolic and complete normal-form classifiers. -/
structure ProblemSeventyOneSolution (form : Ternary.Basic.TernaryForm K)
    (twoNonzero : (2 : K) ≠ 0) where
  /-- The complete finite-coordinate rotation theory for the retained ternary form. -/ general :
    Geometry.Rotations.Ternary.Theory.TernaryForm.GeneralRotationTheory form twoNonzero
  /-- The complete rational Minkowski specialization with its evaluated parabolic and classifiers. -/ rationalMinkowski
    : Geometry.Rotations.Ternary.Theory.RationalMinkowski.CompleteTheory

constructive_injectivity ProblemSeventyOneSolution

/-- Construct the complete Problem 71 package without diagonalization, quotients, or proposition-derived choices. -/
def problemSeventyOneSolution [DecidableEq K]
    (form : Ternary.Basic.TernaryForm K) (twoNonzero : (2 : K) ≠ 0) :
    Geometry.Rotations.Ternary.Theory.ProblemSeventyOneSolution form twoNonzero where
  general := Geometry.Rotations.Ternary.Theory.TernaryForm.generalRotationTheory form twoNonzero
  rationalMinkowski := Geometry.Rotations.Ternary.Theory.RationalMinkowski.completeTheory

end Purelib.Geometry.Rotations.Ternary.Theory
