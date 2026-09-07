import FTA.CCLCompleteOwnerCompatibility

/-!
# Strict sector-interior tangent cones

The ordinary sector owner list records only weakly owned faces.  At an exact
algebraic boundary, however, one of the strict strip faces of an axis sector
can also vanish.  Such a face must be entered rather than treated as an
already-strict prior.  This module records every oriented face of the strict
interior of a deterministic sector row.  It is the phase-local geometry
needed by the history-free boundary controller.
-/

namespace FTA
namespace CCLSectorInteriorCone

open CCL CCL.GaussianRat
open FTA.CCLGeometry
open FTA.CCLCompleteOwnerCompatibility
open FTA.CCLMultiOwnerGrid
open FTA.CCLOwnerDirection
open FTA.CCLParserGeometry
open FTA.CCLSectorTangent

abbrev QI := CCL.GaussianRat

/-- A real-coordinate boundary oriented toward either increasing or
decreasing real coordinate. -/
def orientedRealForm (increasing : Bool) (matrix : Mat2 QI)
    (threshold : ℚ) : HermitianForm :=
  if increasing then realComparisonForm matrix threshold
  else (realComparisonForm matrix threshold).neg

/-- An imaginary-coordinate boundary oriented toward either increasing or
decreasing imaginary coordinate. -/
def orientedImagForm (increasing : Bool) (matrix : Mat2 QI)
    (threshold : ℚ) : HermitianForm :=
  if increasing then imagComparisonForm matrix threshold
  else (imagComparisonForm matrix threshold).neg

@[simp] theorem orientedRealForm_true (matrix : Mat2 QI) (threshold : ℚ) :
    orientedRealForm true matrix threshold =
      realComparisonForm matrix threshold := rfl

@[simp] theorem orientedRealForm_false (matrix : Mat2 QI) (threshold : ℚ) :
    orientedRealForm false matrix threshold =
      (realComparisonForm matrix threshold).neg := rfl

@[simp] theorem orientedImagForm_true (matrix : Mat2 QI) (threshold : ℚ) :
    orientedImagForm true matrix threshold =
      imagComparisonForm matrix threshold := rfl

@[simp] theorem orientedImagForm_false (matrix : Mat2 QI) (threshold : ℚ) :
    orientedImagForm false matrix threshold =
      (imagComparisonForm matrix threshold).neg := rfl

/-- Every face of the strict interior of a deterministic sector row,
oriented so that the interior is its positive side.  Axis rows have two
strict strip walls in addition to their weak outward wall. -/
def sectorInteriorForms : Sector → Mat2 QI → List HermitianForm
  | .east, matrix =>
      [orientedRealForm true matrix (1 / 2),
        orientedImagForm true matrix (-1 / 2),
        orientedImagForm false matrix (1 / 2)]
  | .northEast, matrix =>
      [orientedRealForm true matrix (1 / 2),
        orientedImagForm true matrix (1 / 2)]
  | .north, matrix =>
      [orientedImagForm true matrix (1 / 2),
        orientedRealForm true matrix (-1 / 2),
        orientedRealForm false matrix (1 / 2)]
  | .northWest, matrix =>
      [orientedRealForm false matrix (-1 / 2),
        orientedImagForm true matrix (1 / 2)]
  | .west, matrix =>
      [orientedRealForm false matrix (-1 / 2),
        orientedImagForm true matrix (-1 / 2),
        orientedImagForm false matrix (1 / 2)]
  | .southWest, matrix =>
      [orientedRealForm false matrix (-1 / 2),
        orientedImagForm false matrix (-1 / 2)]
  | .south, matrix =>
      [orientedImagForm false matrix (-1 / 2),
        orientedRealForm true matrix (-1 / 2),
        orientedRealForm false matrix (1 / 2)]
  | .southEast, matrix =>
      [orientedRealForm true matrix (1 / 2),
        orientedImagForm false matrix (-1 / 2)]

/-- Making every oriented interior face positive realizes the corresponding
sector formula, including all of its strict strip inequalities. -/
theorem sectorFormula_holds_of_interiorForms_pos
    (sector : Sector) (matrix : Mat2 QI) (point : QI)
    (positive : ∀ form ∈ sectorInteriorForms sector matrix,
      0 < form.eval point) :
    (sectorFormula sector matrix).Holds point := by
  cases sector with
  | east =>
      have real := positive (orientedRealForm true matrix (1 / 2)) (by
        simp [sectorInteriorForms])
      have imagLower := positive (orientedImagForm true matrix (-1 / 2)) (by
        simp [sectorInteriorForms])
      have imagUpper := positive (orientedImagForm false matrix (1 / 2)) (by
        simp [sectorInteriorForms])
      simp only [orientedImagForm_false, HermitianForm.eval_neg] at imagUpper
      simpa [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        orientedRealForm, orientedImagForm] using
          And.intro real.le (And.intro imagLower (neg_pos.mp imagUpper))
  | northEast =>
      have real := positive (orientedRealForm true matrix (1 / 2)) (by
        simp [sectorInteriorForms])
      have imag := positive (orientedImagForm true matrix (1 / 2)) (by
        simp [sectorInteriorForms])
      simpa [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        orientedRealForm, orientedImagForm] using And.intro real.le imag.le
  | north =>
      have realLower := positive (orientedRealForm true matrix (-1 / 2)) (by
        simp [sectorInteriorForms])
      have realUpper := positive (orientedRealForm false matrix (1 / 2)) (by
        simp [sectorInteriorForms])
      have imag := positive (orientedImagForm true matrix (1 / 2)) (by
        simp [sectorInteriorForms])
      simp only [orientedRealForm_false, HermitianForm.eval_neg] at realUpper
      simpa [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        orientedRealForm, orientedImagForm] using
          And.intro realLower (And.intro (neg_pos.mp realUpper) imag.le)
  | northWest =>
      have real := positive (orientedRealForm false matrix (-1 / 2)) (by
        simp [sectorInteriorForms])
      have imag := positive (orientedImagForm true matrix (1 / 2)) (by
        simp [sectorInteriorForms])
      simp only [orientedRealForm_false, HermitianForm.eval_neg] at real
      simpa [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        orientedRealForm, orientedImagForm] using
          And.intro (neg_pos.mp real).le imag.le
  | west =>
      have real := positive (orientedRealForm false matrix (-1 / 2)) (by
        simp [sectorInteriorForms])
      have imagLower := positive (orientedImagForm true matrix (-1 / 2)) (by
        simp [sectorInteriorForms])
      have imagUpper := positive (orientedImagForm false matrix (1 / 2)) (by
        simp [sectorInteriorForms])
      simp only [orientedRealForm_false, HermitianForm.eval_neg] at real
      simp only [orientedImagForm_false, HermitianForm.eval_neg] at imagUpper
      simpa [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        orientedRealForm, orientedImagForm] using
          And.intro (neg_pos.mp real).le
            (And.intro imagLower (neg_pos.mp imagUpper))
  | southWest =>
      have real := positive (orientedRealForm false matrix (-1 / 2)) (by
        simp [sectorInteriorForms])
      have imag := positive (orientedImagForm false matrix (-1 / 2)) (by
        simp [sectorInteriorForms])
      simp only [orientedRealForm_false, HermitianForm.eval_neg] at real
      simp only [orientedImagForm_false, HermitianForm.eval_neg] at imag
      simpa [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        orientedRealForm, orientedImagForm] using
          And.intro (neg_pos.mp real).le (neg_pos.mp imag).le
  | south =>
      have realLower := positive (orientedRealForm true matrix (-1 / 2)) (by
        simp [sectorInteriorForms])
      have realUpper := positive (orientedRealForm false matrix (1 / 2)) (by
        simp [sectorInteriorForms])
      have imag := positive (orientedImagForm false matrix (-1 / 2)) (by
        simp [sectorInteriorForms])
      simp only [orientedRealForm_false, HermitianForm.eval_neg] at realUpper
      simp only [orientedImagForm_false, HermitianForm.eval_neg] at imag
      simpa [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        orientedRealForm, orientedImagForm] using
          And.intro realLower
            (And.intro (neg_pos.mp realUpper) (neg_pos.mp imag).le)
  | southEast =>
      have real := positive (orientedRealForm true matrix (1 / 2)) (by
        simp [sectorInteriorForms])
      have imag := positive (orientedImagForm false matrix (-1 / 2)) (by
        simp [sectorInteriorForms])
      simp only [orientedImagForm_false, HermitianForm.eval_neg] at imag
      simpa [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        orientedRealForm, orientedImagForm] using
          And.intro real.le (neg_pos.mp imag).le

/-- Interior faces which are exact equalities at the displayed rational
anchor and therefore need a tangent entry step. -/
def activeSectorInteriorForms (sector : Sector) (matrix : Mat2 QI)
    (point : QI) : List HermitianForm :=
  (sectorInteriorForms sector matrix).filter fun form =>
    decide (form.eval point = 0)

theorem orientedRealForm_gradient_norm
    (increasing : Bool) (matrix : Mat2 QI) (threshold : ℚ) (point : QI)
    (boundary : (orientedRealForm increasing matrix threshold).eval point = 0) :
    normSq (gradientVector (orientedRealForm increasing matrix threshold)
      point) = normSq (determinant matrix) := by
  cases increasing with
  | false =>
      exact gradientVector_normSq_neg_realComparison matrix threshold point
        boundary
  | true =>
      exact gradientVector_normSq_realComparison matrix threshold point
        boundary

theorem orientedImagForm_gradient_norm
    (increasing : Bool) (matrix : Mat2 QI) (threshold : ℚ) (point : QI)
    (boundary : (orientedImagForm increasing matrix threshold).eval point = 0) :
    normSq (gradientVector (orientedImagForm increasing matrix threshold)
      point) = normSq (determinant matrix) := by
  cases increasing with
  | false =>
      exact gradientVector_normSq_neg_imagComparison matrix threshold point
        boundary
  | true =>
      exact gradientVector_normSq_imagComparison matrix threshold point
        boundary

theorem orientedRealForm_gradient_pos
    (increasing : Bool) (matrix : Mat2 QI) (threshold : ℚ) (point : QI)
    (determinantNonzero : determinant matrix ≠ 0)
    (boundary : (orientedRealForm increasing matrix threshold).eval point = 0) :
    0 < normSq (gradientVector
      (orientedRealForm increasing matrix threshold) point) := by
  rw [orientedRealForm_gradient_norm increasing matrix threshold point boundary]
  exact normSq_pos determinantNonzero

theorem orientedImagForm_gradient_pos
    (increasing : Bool) (matrix : Mat2 QI) (threshold : ℚ) (point : QI)
    (determinantNonzero : determinant matrix ≠ 0)
    (boundary : (orientedImagForm increasing matrix threshold).eval point = 0) :
    0 < normSq (gradientVector
      (orientedImagForm increasing matrix threshold) point) := by
  rw [orientedImagForm_gradient_norm increasing matrix threshold point boundary]
  exact normSq_pos determinantNonzero

theorem orientedReal_orientedImag_gradient_orthogonal
    (realIncreasing imagIncreasing : Bool) (matrix : Mat2 QI)
    (realThreshold imagThreshold : ℚ) (point : QI)
    (realBoundary :
      (orientedRealForm realIncreasing matrix realThreshold).eval point = 0)
    (imagBoundary :
      (orientedImagForm imagIncreasing matrix imagThreshold).eval point = 0) :
    gradientDot (orientedRealForm realIncreasing matrix realThreshold)
      (orientedImagForm imagIncreasing matrix imagThreshold) point = 0 := by
  have realBase :
      (realComparisonForm matrix realThreshold).eval point = 0 := by
    cases realIncreasing <;>
      simpa [orientedRealForm, HermitianForm.eval_neg] using realBoundary
  have imagBase :
      (imagComparisonForm matrix imagThreshold).eval point = 0 := by
    cases imagIncreasing <;>
      simpa [orientedImagForm, HermitianForm.eval_neg] using imagBoundary
  have orthogonal := real_imag_gradient_orthogonal matrix realThreshold
    imagThreshold point realBase imagBase
  cases realIncreasing <;> cases imagIncreasing <;>
    simp [orientedRealForm, orientedImagForm, gradientDot] <;>
    nlinarith [orthogonal]

theorem orientedImag_orientedReal_gradient_orthogonal
    (imagIncreasing realIncreasing : Bool) (matrix : Mat2 QI)
    (imagThreshold realThreshold : ℚ) (point : QI)
    (imagBoundary :
      (orientedImagForm imagIncreasing matrix imagThreshold).eval point = 0)
    (realBoundary :
      (orientedRealForm realIncreasing matrix realThreshold).eval point = 0) :
    gradientDot (orientedImagForm imagIncreasing matrix imagThreshold)
      (orientedRealForm realIncreasing matrix realThreshold) point = 0 := by
  rw [gradientDot_comm]
  exact orientedReal_orientedImag_gradient_orthogonal realIncreasing
    imagIncreasing matrix realThreshold imagThreshold point realBoundary
      imagBoundary

/-- A real and an imaginary wall through the same invertible homography have
the strict invariant angle gap used by the finite compass search.  Orienting
either wall reverses its gradient but does not change this gap. -/
theorem orientedReal_orientedImag_angleGap_pos
    (realIncreasing imagIncreasing : Bool) (matrix : Mat2 QI)
    (realThreshold imagThreshold : ℚ)
    (determinantNonzero : determinant matrix ≠ 0) :
    0 < boundaryDiscriminant
          (orientedRealForm realIncreasing matrix realThreshold) *
        boundaryDiscriminant
          (orientedImagForm imagIncreasing matrix imagThreshold) -
      2 * gradientPairingConstant
          (orientedRealForm realIncreasing matrix realThreshold)
          (orientedImagForm imagIncreasing matrix imagThreshold) ^ 2 := by
  have determinantPositive : 0 < normSq (determinant matrix) :=
    normSq_pos determinantNonzero
  cases realIncreasing <;> cases imagIncreasing <;>
    simp only [orientedRealForm, orientedImagForm, Bool.false_eq_true,
      if_false, if_true, boundaryDiscriminant_neg,
      gradientPairingConstant_neg_left, gradientPairingConstant_neg_right,
      boundaryDiscriminant_realComparisonForm,
      boundaryDiscriminant_imagComparisonForm,
      gradientPairingConstant_real_imag, neg_zero, neg_mul_neg] <;>
    norm_num <;>
    nlinarith [sq_pos_of_pos determinantPositive]

/-- Symmetric orientation of `orientedReal_orientedImag_angleGap_pos`. -/
theorem orientedImag_orientedReal_angleGap_pos
    (imagIncreasing realIncreasing : Bool) (matrix : Mat2 QI)
    (imagThreshold realThreshold : ℚ)
    (determinantNonzero : determinant matrix ≠ 0) :
    0 < boundaryDiscriminant
          (orientedImagForm imagIncreasing matrix imagThreshold) *
        boundaryDiscriminant
          (orientedRealForm realIncreasing matrix realThreshold) -
      2 * gradientPairingConstant
          (orientedImagForm imagIncreasing matrix imagThreshold)
          (orientedRealForm realIncreasing matrix realThreshold) ^ 2 := by
  have forward := orientedReal_orientedImag_angleGap_pos realIncreasing
    imagIncreasing matrix realThreshold imagThreshold determinantNonzero
  have pairingSymmetric :
      gradientPairingConstant
          (orientedImagForm imagIncreasing matrix imagThreshold)
          (orientedRealForm realIncreasing matrix realThreshold) =
        gradientPairingConstant
          (orientedRealForm realIncreasing matrix realThreshold)
          (orientedImagForm imagIncreasing matrix imagThreshold) := by
    simp only [gradientPairingConstant]
    ring
  rw [pairingSymmetric]
  nlinarith

theorem orientedRealForms_not_both_zero
    (leftIncreasing rightIncreasing : Bool) (matrix : Mat2 QI)
    (leftThreshold rightThreshold : ℚ) (point : QI)
    (denominator : matrix.c * point + matrix.d ≠ 0)
    (thresholdsDistinct : leftThreshold ≠ rightThreshold) :
    ¬((orientedRealForm leftIncreasing matrix leftThreshold).eval point = 0 ∧
      (orientedRealForm rightIncreasing matrix rightThreshold).eval point = 0) := by
  rintro ⟨leftZero, rightZero⟩
  have leftBase : (realComparisonForm matrix leftThreshold).eval point = 0 := by
    cases leftIncreasing <;>
      simpa [orientedRealForm, HermitianForm.eval_neg] using leftZero
  have rightBase :
      (realComparisonForm matrix rightThreshold).eval point = 0 := by
    cases rightIncreasing <;>
      simpa [orientedRealForm, HermitianForm.eval_neg] using rightZero
  have leftCoordinate :=
    (real_homographic_eq_iff matrix point leftThreshold denominator).2 leftBase
  have rightCoordinate :=
    (real_homographic_eq_iff matrix point rightThreshold denominator).2 rightBase
  apply thresholdsDistinct
  exact leftCoordinate.symm.trans rightCoordinate

theorem orientedImagForms_not_both_zero
    (lowerIncreasing upperIncreasing : Bool) (matrix : Mat2 QI)
    (lowerThreshold upperThreshold : ℚ) (point : QI)
    (denominator : matrix.c * point + matrix.d ≠ 0)
    (thresholdsDistinct : lowerThreshold ≠ upperThreshold) :
    ¬((orientedImagForm lowerIncreasing matrix lowerThreshold).eval point = 0 ∧
      (orientedImagForm upperIncreasing matrix upperThreshold).eval point = 0) := by
  rintro ⟨lowerZero, upperZero⟩
  have lowerBase :
      (imagComparisonForm matrix lowerThreshold).eval point = 0 := by
    cases lowerIncreasing <;>
      simpa [orientedImagForm, HermitianForm.eval_neg] using lowerZero
  have upperBase :
      (imagComparisonForm matrix upperThreshold).eval point = 0 := by
    cases upperIncreasing <;>
      simpa [orientedImagForm, HermitianForm.eval_neg] using upperZero
  have lowerCoordinate :=
    (imag_homographic_eq_iff matrix point lowerThreshold denominator).2 lowerBase
  have upperCoordinate :=
    (imag_homographic_eq_iff matrix point upperThreshold denominator).2 upperBase
  apply thresholdsDistinct
  exact lowerCoordinate.symm.trans upperCoordinate

private theorem tangentDirectionCertificate?_isSome_activeTriple
    (first second third : HermitianForm) (point : QI)
    (firstSecond : (tangentDirectionCertificate?
      ([first, second].filter fun form => decide (form.eval point = 0))
        point).isSome)
    (firstThird : (tangentDirectionCertificate?
      ([first, third].filter fun form => decide (form.eval point = 0))
        point).isSome)
    (secondThirdNotBoth : ¬(second.eval point = 0 ∧ third.eval point = 0)) :
    (tangentDirectionCertificate?
      ([first, second, third].filter fun form =>
        decide (form.eval point = 0)) point).isSome := by
  by_cases secondZero : second.eval point = 0
  · have thirdNonzero : third.eval point ≠ 0 := by
      intro thirdZero
      exact secondThirdNotBoth ⟨secondZero, thirdZero⟩
    apply tangentDirectionCertificate?_isSome_of_subset _ firstSecond
    intro form member
    rcases List.mem_filter.mp member with ⟨source, zero⟩
    apply List.mem_filter.mpr
    refine ⟨?_, zero⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at source ⊢
    rcases source with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (thirdNonzero (of_decide_eq_true zero)).elim
  · apply tangentDirectionCertificate?_isSome_of_subset _ firstThird
    intro form member
    rcases List.mem_filter.mp member with ⟨source, zero⟩
    apply List.mem_filter.mpr
    refine ⟨?_, zero⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at source ⊢
    rcases source with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact (secondZero (of_decide_eq_true zero)).elim
    · exact Or.inr rfl

private theorem orientedRealImagPair_search
    (realIncreasing imagIncreasing : Bool) (matrix : Mat2 QI)
    (realThreshold imagThreshold : ℚ) (point : QI)
    (determinantNonzero : determinant matrix ≠ 0) :
    (tangentDirectionCertificate?
      ([orientedRealForm realIncreasing matrix realThreshold,
        orientedImagForm imagIncreasing matrix imagThreshold].filter
          fun form => decide (form.eval point = 0)) point).isSome := by
  apply tangentDirectionCertificate?_isSome_activePair
  · exact orientedRealForm_gradient_pos realIncreasing matrix realThreshold
      point determinantNonzero
  · exact orientedImagForm_gradient_pos imagIncreasing matrix imagThreshold
      point determinantNonzero
  · intro realBoundary imagBoundary
    rw [orientedRealForm_gradient_norm realIncreasing matrix realThreshold
        point realBoundary,
      orientedImagForm_gradient_norm imagIncreasing matrix imagThreshold
        point imagBoundary]
  · exact orientedReal_orientedImag_gradient_orthogonal realIncreasing
      imagIncreasing matrix realThreshold imagThreshold point

private theorem orientedImagRealPair_search
    (imagIncreasing realIncreasing : Bool) (matrix : Mat2 QI)
    (imagThreshold realThreshold : ℚ) (point : QI)
    (determinantNonzero : determinant matrix ≠ 0) :
    (tangentDirectionCertificate?
      ([orientedImagForm imagIncreasing matrix imagThreshold,
        orientedRealForm realIncreasing matrix realThreshold].filter
          fun form => decide (form.eval point = 0)) point).isSome := by
  apply tangentDirectionCertificate?_isSome_activePair
  · exact orientedImagForm_gradient_pos imagIncreasing matrix imagThreshold
      point determinantNonzero
  · exact orientedRealForm_gradient_pos realIncreasing matrix realThreshold
      point determinantNonzero
  · intro imagBoundary realBoundary
    rw [orientedImagForm_gradient_norm imagIncreasing matrix imagThreshold
        point imagBoundary,
      orientedRealForm_gradient_norm realIncreasing matrix realThreshold
        point realBoundary]
  · exact orientedImag_orientedReal_gradient_orthogonal imagIncreasing
      realIncreasing matrix imagThreshold realThreshold point

/-- The finite eight-direction table succeeds for every exact active subset
of the strict sector-interior faces.  The affine-denominator premise excludes
the projective pole, at which two distinct parallel strip walls would both
clear to zero. -/
theorem tangentDirectionCertificate?_isSome_activeSectorInteriorForms
    (sector : Sector) (matrix : Mat2 QI) (point : QI)
    (determinantNonzero : determinant matrix ≠ 0)
    (denominator : matrix.c * point + matrix.d ≠ 0) :
    (tangentDirectionCertificate?
      (activeSectorInteriorForms sector matrix point) point).isSome := by
  cases sector with
  | east =>
      apply tangentDirectionCertificate?_isSome_activeTriple
        (orientedRealForm true matrix (1 / 2))
        (orientedImagForm true matrix (-1 / 2))
        (orientedImagForm false matrix (1 / 2)) point
      · exact orientedRealImagPair_search true true matrix (1 / 2) (-1 / 2)
          point determinantNonzero
      · exact orientedRealImagPair_search true false matrix (1 / 2) (1 / 2)
          point determinantNonzero
      · exact orientedImagForms_not_both_zero true false matrix (-1 / 2)
          (1 / 2) point denominator (by norm_num)
  | northEast =>
      exact orientedRealImagPair_search true true matrix (1 / 2) (1 / 2)
        point determinantNonzero
  | north =>
      apply tangentDirectionCertificate?_isSome_activeTriple
        (orientedImagForm true matrix (1 / 2))
        (orientedRealForm true matrix (-1 / 2))
        (orientedRealForm false matrix (1 / 2)) point
      · exact orientedImagRealPair_search true true matrix (1 / 2) (-1 / 2)
          point determinantNonzero
      · exact orientedImagRealPair_search true false matrix (1 / 2) (1 / 2)
          point determinantNonzero
      · exact orientedRealForms_not_both_zero true false matrix (-1 / 2)
          (1 / 2) point denominator (by norm_num)
  | northWest =>
      exact orientedRealImagPair_search false true matrix (-1 / 2) (1 / 2)
        point determinantNonzero
  | west =>
      apply tangentDirectionCertificate?_isSome_activeTriple
        (orientedRealForm false matrix (-1 / 2))
        (orientedImagForm true matrix (-1 / 2))
        (orientedImagForm false matrix (1 / 2)) point
      · exact orientedRealImagPair_search false true matrix (-1 / 2) (-1 / 2)
          point determinantNonzero
      · exact orientedRealImagPair_search false false matrix (-1 / 2) (1 / 2)
          point determinantNonzero
      · exact orientedImagForms_not_both_zero true false matrix (-1 / 2)
          (1 / 2) point denominator (by norm_num)
  | southWest =>
      exact orientedRealImagPair_search false false matrix (-1 / 2) (-1 / 2)
        point determinantNonzero
  | south =>
      apply tangentDirectionCertificate?_isSome_activeTriple
        (orientedImagForm false matrix (-1 / 2))
        (orientedRealForm true matrix (-1 / 2))
        (orientedRealForm false matrix (1 / 2)) point
      · exact orientedImagRealPair_search false true matrix (-1 / 2) (-1 / 2)
          point determinantNonzero
      · exact orientedImagRealPair_search false false matrix (-1 / 2) (1 / 2)
          point determinantNonzero
      · exact orientedRealForms_not_both_zero true false matrix (-1 / 2)
          (1 / 2) point denominator (by norm_num)
  | southEast =>
      exact orientedRealImagPair_search true false matrix (1 / 2) (-1 / 2)
        point determinantNonzero

/-- Executable bounded direction entering every exact sector-interior face. -/
def sectorInteriorTangentDirection
    (sector : Sector) (matrix : Mat2 QI) (point : QI)
    (determinantNonzero : determinant matrix ≠ 0)
    (denominator : matrix.c * point + matrix.d ≠ 0) :
    TangentDirection (activeSectorInteriorForms sector matrix point) point :=
  (tangentDirectionCertificate?
    (activeSectorInteriorForms sector matrix point) point).get
      (tangentDirectionCertificate?_isSome_activeSectorInteriorForms sector
        matrix point determinantNonzero denominator)

/-! ## Strict radial interiors -/

/-- Both oriented faces of the normalized annulus.  Unlike
`radialOwnerForm`, this list also includes a strict annulus wall which may
vanish at an exact algebraic intersection. -/
def radialInteriorForms
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI) :
    List HermitianForm :=
  match kind with
  | .initialHigh =>
      [normComparisonForm matrix ((2 : ℚ) ^ exponent),
        (normComparisonForm matrix ((2 : ℚ) ^ (exponent + 1))).neg]
  | .initialLow =>
      [normComparisonForm matrix (1 / (2 : ℚ) ^ exponent),
        (normComparisonForm matrix (2 / (2 : ℚ) ^ exponent)).neg]
  | .loop =>
      [normComparisonForm matrix ((2 : ℚ) ^ exponent),
        (normComparisonForm matrix ((2 : ℚ) ^ (exponent + 1))).neg]

/-- Strict positivity of both annulus-interior forms realizes the parser's
radial bracket, including the asymmetric loop equality convention. -/
theorem radialFormula_holds_of_interiorForms_pos
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI)
    (point : QI)
    (positive : ∀ form ∈ radialInteriorForms kind exponent matrix,
      0 < form.eval point) :
    (radialFormula kind exponent matrix).Holds point := by
  cases kind with
  | initialHigh =>
      have lower := positive
        (normComparisonForm matrix ((2 : ℚ) ^ exponent)) (by
          simp [radialInteriorForms])
      have upper := positive
        (normComparisonForm matrix ((2 : ℚ) ^ (exponent + 1))).neg (by
          simp [radialInteriorForms])
      simp only [HermitianForm.eval_neg] at upper
      simpa [radialFormula, Formula.Holds, Atom.Holds, SignTest.Holds] using
        And.intro lower.le (neg_pos.mp upper)
  | initialLow =>
      have lower := positive
        (normComparisonForm matrix (1 / (2 : ℚ) ^ exponent)) (by
          simp [radialInteriorForms])
      have upper := positive
        (normComparisonForm matrix (2 / (2 : ℚ) ^ exponent)).neg (by
          simp [radialInteriorForms])
      simp only [HermitianForm.eval_neg] at upper
      simpa [radialFormula, Formula.Holds, Atom.Holds, SignTest.Holds] using
        And.intro lower.le (neg_pos.mp upper)
  | loop =>
      have lower := positive
        (normComparisonForm matrix ((2 : ℚ) ^ exponent)) (by
          simp [radialInteriorForms])
      have upper := positive
        (normComparisonForm matrix ((2 : ℚ) ^ (exponent + 1))).neg (by
          simp [radialInteriorForms])
      simp only [HermitianForm.eval_neg] at upper
      simpa [radialFormula, Formula.Holds, Atom.Holds, SignTest.Holds] using
        And.intro lower (neg_pos.mp upper).le

def activeRadialInteriorForms
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI)
    (point : QI) : List HermitianForm :=
  (radialInteriorForms kind exponent matrix).filter fun form =>
    decide (form.eval point = 0)

/-- A radial boundary oriented toward either its norm-increasing or its
norm-decreasing side. -/
def orientedNormForm (increasing : Bool) (matrix : Mat2 QI)
    (radiusSq : ℚ) : HermitianForm :=
  if increasing then normComparisonForm matrix radiusSq
  else (normComparisonForm matrix radiusSq).neg

@[simp] theorem orientedNormForm_true (matrix : Mat2 QI) (radiusSq : ℚ) :
    orientedNormForm true matrix radiusSq =
      normComparisonForm matrix radiusSq := rfl

@[simp] theorem orientedNormForm_false (matrix : Mat2 QI) (radiusSq : ℚ) :
    orientedNormForm false matrix radiusSq =
      (normComparisonForm matrix radiusSq).neg := rfl

/-- The invariant radial/real-coordinate angle gap in parser-normalized
coordinates.  Orientations can change the pairing sign but not its square. -/
theorem orientedNorm_orientedReal_angleGap
    (radialIncreasing realIncreasing : Bool)
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI)
    (radiusSq threshold : ℚ) :
    boundaryDiscriminant (orientedNormForm radialIncreasing matrix radiusSq) *
          boundaryDiscriminant
            (orientedRealForm realIncreasing
              (normalizedMatrix kind exponent matrix) threshold) -
        2 * gradientPairingConstant
            (orientedNormForm radialIncreasing matrix radiusSq)
            (orientedRealForm realIncreasing
              (normalizedMatrix kind exponent matrix) threshold) ^ 2 =
      4 * radiusSq * normSq (determinant matrix) *
          normSq (determinant (normalizedMatrix kind exponent matrix)) -
        8 * threshold ^ 2 * normSq (determinant matrix) ^ 2 := by
  cases radialIncreasing <;> cases realIncreasing <;>
    simp only [orientedNormForm, orientedRealForm, Bool.false_eq_true,
      if_false, if_true, boundaryDiscriminant_neg,
      gradientPairingConstant_neg_left, gradientPairingConstant_neg_right,
      boundaryDiscriminant_normComparisonForm,
      boundaryDiscriminant_realComparisonForm,
      gradientPairingConstant_norm_normalizedReal] <;>
    ring

/-- Imaginary-coordinate counterpart of
`orientedNorm_orientedReal_angleGap`. -/
theorem orientedNorm_orientedImag_angleGap
    (radialIncreasing imagIncreasing : Bool)
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI)
    (radiusSq threshold : ℚ) :
    boundaryDiscriminant (orientedNormForm radialIncreasing matrix radiusSq) *
          boundaryDiscriminant
            (orientedImagForm imagIncreasing
              (normalizedMatrix kind exponent matrix) threshold) -
        2 * gradientPairingConstant
            (orientedNormForm radialIncreasing matrix radiusSq)
            (orientedImagForm imagIncreasing
              (normalizedMatrix kind exponent matrix) threshold) ^ 2 =
      4 * radiusSq * normSq (determinant matrix) *
          normSq (determinant (normalizedMatrix kind exponent matrix)) -
        8 * threshold ^ 2 * normSq (determinant matrix) ^ 2 := by
  cases radialIncreasing <;> cases imagIncreasing <;>
    simp only [orientedNormForm, orientedImagForm, Bool.false_eq_true,
      if_false, if_true, boundaryDiscriminant_neg,
      gradientPairingConstant_neg_left, gradientPairingConstant_neg_right,
      boundaryDiscriminant_normComparisonForm,
      boundaryDiscriminant_imagComparisonForm,
      gradientPairingConstant_norm_normalizedImag] <;>
    ring

/-- Every annulus-interior face has a strict compass angle gap from every
normalized real-coordinate wall at threshold magnitude one half. -/
theorem radialInterior_orientedReal_angleGap_pos
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI)
    (determinantNonzero : determinant matrix ≠ 0)
    {radialForm : HermitianForm}
    (radialMember : radialForm ∈ radialInteriorForms kind exponent matrix)
    (realIncreasing : Bool) (threshold : ℚ)
    (thresholdSq : threshold ^ 2 = (1 / 2 : ℚ) ^ 2) :
    0 < boundaryDiscriminant radialForm *
          boundaryDiscriminant
            (orientedRealForm realIncreasing
              (normalizedMatrix kind exponent matrix) threshold) -
        2 * gradientPairingConstant radialForm
            (orientedRealForm realIncreasing
              (normalizedMatrix kind exponent matrix) threshold) ^ 2 := by
  have determinantPositive : 0 < normSq (determinant matrix) :=
    normSq_pos determinantNonzero
  cases kind with
  | initialHigh =>
      simp only [radialInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at radialMember
      rcases radialMember with rfl | rfl
      · rw [← orientedNormForm_true matrix ((2 : ℚ) ^ exponent)]
        rw [orientedNorm_orientedReal_angleGap,
          normSq_determinant_normalizedMatrix, thresholdSq]
        have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
        field_simp
        nlinarith [sq_pos_of_pos determinantPositive]

      · rw [← orientedNormForm_false matrix ((2 : ℚ) ^ (exponent + 1))]
        rw [orientedNorm_orientedReal_angleGap,
          normSq_determinant_normalizedMatrix, thresholdSq]
        have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
        rw [pow_succ]
        field_simp
        nlinarith [sq_pos_of_pos determinantPositive]
  | initialLow =>
      simp only [radialInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at radialMember
      rcases radialMember with rfl | rfl
      · rw [← orientedNormForm_true matrix (1 / (2 : ℚ) ^ exponent)]
        rw [orientedNorm_orientedReal_angleGap,
          normSq_determinant_normalizedMatrix, thresholdSq]
        have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
        field_simp
        nlinarith [sq_pos_of_pos determinantPositive]
      · rw [← orientedNormForm_false matrix (2 / (2 : ℚ) ^ exponent)]
        rw [orientedNorm_orientedReal_angleGap,
          normSq_determinant_normalizedMatrix, thresholdSq]
        have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
        field_simp
        nlinarith [sq_pos_of_pos determinantPositive]
  | loop =>
      simp only [radialInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at radialMember
      rcases radialMember with rfl | rfl
      · rw [← orientedNormForm_true matrix ((2 : ℚ) ^ exponent)]
        rw [orientedNorm_orientedReal_angleGap,
          normSq_determinant_normalizedMatrix, thresholdSq]
        have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
        field_simp
        nlinarith [sq_pos_of_pos determinantPositive]
      · rw [← orientedNormForm_false matrix ((2 : ℚ) ^ (exponent + 1))]
        rw [orientedNorm_orientedReal_angleGap,
          normSq_determinant_normalizedMatrix, thresholdSq]
        have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
        rw [pow_succ]
        field_simp
        nlinarith [sq_pos_of_pos determinantPositive]

/-- Imaginary-coordinate version of
`radialInterior_orientedReal_angleGap_pos`. -/
theorem radialInterior_orientedImag_angleGap_pos
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI)
    (determinantNonzero : determinant matrix ≠ 0)
    {radialForm : HermitianForm}
    (radialMember : radialForm ∈ radialInteriorForms kind exponent matrix)
    (imagIncreasing : Bool) (threshold : ℚ)
    (thresholdSq : threshold ^ 2 = (1 / 2 : ℚ) ^ 2) :
    0 < boundaryDiscriminant radialForm *
          boundaryDiscriminant
            (orientedImagForm imagIncreasing
              (normalizedMatrix kind exponent matrix) threshold) -
        2 * gradientPairingConstant radialForm
            (orientedImagForm imagIncreasing
              (normalizedMatrix kind exponent matrix) threshold) ^ 2 := by
  have realGap := radialInterior_orientedReal_angleGap_pos kind exponent
    matrix determinantNonzero radialMember imagIncreasing threshold thresholdSq
  cases kind with
  | initialHigh =>
      simp only [radialInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at radialMember
      rcases radialMember with rfl | rfl
      · rw [← orientedNormForm_true matrix ((2 : ℚ) ^ exponent)]
        rw [orientedNorm_orientedImag_angleGap]
        rw [← orientedNormForm_true matrix ((2 : ℚ) ^ exponent)] at realGap
        rw [orientedNorm_orientedReal_angleGap] at realGap
        exact realGap
      · rw [← orientedNormForm_false matrix ((2 : ℚ) ^ (exponent + 1))]
        rw [orientedNorm_orientedImag_angleGap]
        rw [← orientedNormForm_false matrix ((2 : ℚ) ^ (exponent + 1))] at realGap
        rw [orientedNorm_orientedReal_angleGap] at realGap
        exact realGap
  | initialLow =>
      simp only [radialInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at radialMember
      rcases radialMember with rfl | rfl
      · rw [← orientedNormForm_true matrix (1 / (2 : ℚ) ^ exponent)]
        rw [orientedNorm_orientedImag_angleGap]
        rw [← orientedNormForm_true matrix (1 / (2 : ℚ) ^ exponent)] at realGap
        rw [orientedNorm_orientedReal_angleGap] at realGap
        exact realGap
      · rw [← orientedNormForm_false matrix (2 / (2 : ℚ) ^ exponent)]
        rw [orientedNorm_orientedImag_angleGap]
        rw [← orientedNormForm_false matrix (2 / (2 : ℚ) ^ exponent)] at realGap
        rw [orientedNorm_orientedReal_angleGap] at realGap
        exact realGap
  | loop =>
      simp only [radialInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at radialMember
      rcases radialMember with rfl | rfl
      · rw [← orientedNormForm_true matrix ((2 : ℚ) ^ exponent)]
        rw [orientedNorm_orientedImag_angleGap]
        rw [← orientedNormForm_true matrix ((2 : ℚ) ^ exponent)] at realGap
        rw [orientedNorm_orientedReal_angleGap] at realGap
        exact realGap
      · rw [← orientedNormForm_false matrix ((2 : ℚ) ^ (exponent + 1))]
        rw [orientedNorm_orientedImag_angleGap]
        rw [← orientedNormForm_false matrix ((2 : ℚ) ^ (exponent + 1))] at realGap
        rw [orientedNorm_orientedReal_angleGap] at realGap
        exact realGap

/-- Any annulus-interior face and any strict sector-interior face have the
uniform rational angle gap required by the eight-direction compass table. -/
theorem radialInterior_sectorInterior_angleGap_pos
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (determinantNonzero : determinant matrix ≠ 0)
    {radialForm sectorForm : HermitianForm}
    (radialMember : radialForm ∈ radialInteriorForms kind exponent matrix)
    (sectorMember : sectorForm ∈ sectorInteriorForms sector
      (normalizedMatrix kind exponent matrix)) :
    0 < boundaryDiscriminant radialForm * boundaryDiscriminant sectorForm -
      2 * gradientPairingConstant radialForm sectorForm ^ 2 := by
  cases sector with
  | east =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at sectorMember
      rcases sectorMember with rfl | rfl | rfl
      · exact radialInterior_orientedReal_angleGap_pos kind exponent matrix
          determinantNonzero radialMember true (1 / 2) (by norm_num)
      · exact radialInterior_orientedImag_angleGap_pos kind exponent matrix
          determinantNonzero radialMember true (-1 / 2) (by norm_num)
      · exact radialInterior_orientedImag_angleGap_pos kind exponent matrix
          determinantNonzero radialMember false (1 / 2) (by norm_num)
  | northEast =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at sectorMember
      rcases sectorMember with rfl | rfl
      · exact radialInterior_orientedReal_angleGap_pos kind exponent matrix
          determinantNonzero radialMember true (1 / 2) (by norm_num)
      · exact radialInterior_orientedImag_angleGap_pos kind exponent matrix
          determinantNonzero radialMember true (1 / 2) (by norm_num)
  | north =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at sectorMember
      rcases sectorMember with rfl | rfl | rfl
      · exact radialInterior_orientedImag_angleGap_pos kind exponent matrix
          determinantNonzero radialMember true (1 / 2) (by norm_num)
      · exact radialInterior_orientedReal_angleGap_pos kind exponent matrix
          determinantNonzero radialMember true (-1 / 2) (by norm_num)
      · exact radialInterior_orientedReal_angleGap_pos kind exponent matrix
          determinantNonzero radialMember false (1 / 2) (by norm_num)
  | northWest =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at sectorMember
      rcases sectorMember with rfl | rfl
      · exact radialInterior_orientedReal_angleGap_pos kind exponent matrix
          determinantNonzero radialMember false (-1 / 2) (by norm_num)
      · exact radialInterior_orientedImag_angleGap_pos kind exponent matrix
          determinantNonzero radialMember true (1 / 2) (by norm_num)
  | west =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at sectorMember
      rcases sectorMember with rfl | rfl | rfl
      · exact radialInterior_orientedReal_angleGap_pos kind exponent matrix
          determinantNonzero radialMember false (-1 / 2) (by norm_num)
      · exact radialInterior_orientedImag_angleGap_pos kind exponent matrix
          determinantNonzero radialMember true (-1 / 2) (by norm_num)
      · exact radialInterior_orientedImag_angleGap_pos kind exponent matrix
          determinantNonzero radialMember false (1 / 2) (by norm_num)
  | southWest =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at sectorMember
      rcases sectorMember with rfl | rfl
      · exact radialInterior_orientedReal_angleGap_pos kind exponent matrix
          determinantNonzero radialMember false (-1 / 2) (by norm_num)
      · exact radialInterior_orientedImag_angleGap_pos kind exponent matrix
          determinantNonzero radialMember false (-1 / 2) (by norm_num)
  | south =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at sectorMember
      rcases sectorMember with rfl | rfl | rfl
      · exact radialInterior_orientedImag_angleGap_pos kind exponent matrix
          determinantNonzero radialMember false (-1 / 2) (by norm_num)
      · exact radialInterior_orientedReal_angleGap_pos kind exponent matrix
          determinantNonzero radialMember true (-1 / 2) (by norm_num)
      · exact radialInterior_orientedReal_angleGap_pos kind exponent matrix
          determinantNonzero radialMember false (1 / 2) (by norm_num)
  | southEast =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at sectorMember
      rcases sectorMember with rfl | rfl
      · exact radialInterior_orientedReal_angleGap_pos kind exponent matrix
          determinantNonzero radialMember true (1 / 2) (by norm_num)
      · exact radialInterior_orientedImag_angleGap_pos kind exponent matrix
          determinantNonzero radialMember false (-1 / 2) (by norm_num)

/-- A normalized sector corner has squared norm one half, whereas either
annulus-interior wall has normalized squared radius one or two. -/
theorem radialInterior_realImag_not_all_zero
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI)
    (point : QI) (denominator : matrix.c * point + matrix.d ≠ 0)
    {radialForm : HermitianForm}
    (radialMember : radialForm ∈ radialInteriorForms kind exponent matrix)
    (realIncreasing imagIncreasing : Bool)
    (realThreshold imagThreshold : ℚ)
    (cornerNorm :
      realThreshold ^ 2 + imagThreshold ^ 2 =
        (1 / 2 : ℚ) ^ 2 + (1 / 2 : ℚ) ^ 2)
    (radialZero : radialForm.eval point = 0)
    (realZero : (orientedRealForm realIncreasing
      (normalizedMatrix kind exponent matrix) realThreshold).eval point = 0)
    (imagZero : (orientedImagForm imagIncreasing
      (normalizedMatrix kind exponent matrix) imagThreshold).eval point = 0) :
    False := by
  let normalized := normalizedMatrix kind exponent matrix
  have normalizedDenominator :
      normalized.c * point + normalized.d ≠ 0 := by
    have lowerRow := normalizedMatrix_lowerRow kind exponent matrix
    simpa only [normalized, lowerRow.1, lowerRow.2] using denominator
  have realBase :
      (realComparisonForm normalized realThreshold).eval point = 0 := by
    cases realIncreasing <;>
      simpa [normalized, orientedRealForm, HermitianForm.eval_neg] using realZero
  have imagBase :
      (imagComparisonForm normalized imagThreshold).eval point = 0 := by
    cases imagIncreasing <;>
      simpa [normalized, orientedImagForm, HermitianForm.eval_neg] using imagZero
  have realCoordinate :=
    (real_homographic_eq_iff normalized point realThreshold
      normalizedDenominator).2 realBase
  have imagCoordinate :=
    (imag_homographic_eq_iff normalized point imagThreshold
      normalizedDenominator).2 imagBase
  have normalizedNorm :
      normSq (CCL.RatBox.homographic normalized point) =
        (1 / 2 : ℚ) ^ 2 + (1 / 2 : ℚ) ^ 2 := by
    simp only [normSq, realCoordinate, imagCoordinate]
    exact cornerNorm
  rw [show normalized = normalizedMatrix kind exponent matrix from rfl,
    homographic_normalizedMatrix] at normalizedNorm
  cases kind with
  | initialHigh =>
      simp only [radialInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at radialMember
      rcases radialMember with rfl | rfl
      · have originalNorm := (norm_homographic_eq_iff matrix point
          ((2 : ℚ) ^ exponent) denominator).2 radialZero
        rw [RawParser.normalizedValue, normSq_mul,
          normSq_inv _ (RawParser.natPow_gamma_ne exponent),
          normSq_natPow, normSq_gamma, originalNorm] at normalizedNorm
        have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
        field_simp at normalizedNorm
        nlinarith
      · have baseZero :
            (normComparisonForm matrix
              ((2 : ℚ) ^ (exponent + 1))).eval point = 0 := by
          simpa only [HermitianForm.eval_neg, neg_eq_zero] using radialZero
        have originalNorm := (norm_homographic_eq_iff matrix point
          ((2 : ℚ) ^ (exponent + 1)) denominator).2 baseZero
        rw [RawParser.normalizedValue, normSq_mul,
          normSq_inv _ (RawParser.natPow_gamma_ne exponent),
          normSq_natPow, normSq_gamma, originalNorm, pow_succ] at normalizedNorm
        have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
        field_simp at normalizedNorm
        nlinarith
  | initialLow =>
      simp only [radialInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at radialMember
      rcases radialMember with rfl | rfl
      · have originalNorm := (norm_homographic_eq_iff matrix point
          (1 / (2 : ℚ) ^ exponent) denominator).2 radialZero
        rw [RawParser.normalizedValue, normSq_mul, normSq_natPow,
          normSq_gamma, originalNorm] at normalizedNorm
        have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
        field_simp at normalizedNorm
        nlinarith
      · have baseZero :
            (normComparisonForm matrix
              (2 / (2 : ℚ) ^ exponent)).eval point = 0 := by
          simpa only [HermitianForm.eval_neg, neg_eq_zero] using radialZero
        have originalNorm := (norm_homographic_eq_iff matrix point
          (2 / (2 : ℚ) ^ exponent) denominator).2 baseZero
        rw [RawParser.normalizedValue, normSq_mul, normSq_natPow,
          normSq_gamma, originalNorm] at normalizedNorm
        have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
        field_simp at normalizedNorm
        nlinarith
  | loop =>
      simp only [radialInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at radialMember
      rcases radialMember with rfl | rfl
      · have originalNorm := (norm_homographic_eq_iff matrix point
          ((2 : ℚ) ^ exponent) denominator).2 radialZero
        rw [RawParser.normalizedValue, normSq_mul,
          normSq_inv _ (RawParser.natPow_gamma_ne exponent),
          normSq_natPow, normSq_gamma, originalNorm] at normalizedNorm
        have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
        field_simp at normalizedNorm
        nlinarith
      · have baseZero :
            (normComparisonForm matrix
              ((2 : ℚ) ^ (exponent + 1))).eval point = 0 := by
          simpa only [HermitianForm.eval_neg, neg_eq_zero] using radialZero
        have originalNorm := (norm_homographic_eq_iff matrix point
          ((2 : ℚ) ^ (exponent + 1)) denominator).2 baseZero
        rw [RawParser.normalizedValue, normSq_mul,
          normSq_inv _ (RawParser.natPow_gamma_ne exponent),
          normSq_natPow, normSq_gamma, originalNorm, pow_succ] at normalizedNorm
        have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
        field_simp at normalizedNorm
        nlinarith

private theorem activePair_length_le_one
    (first second : HermitianForm) (point : QI)
    (notBoth : ¬(first.eval point = 0 ∧ second.eval point = 0)) :
    ([first, second].filter fun form =>
      decide (form.eval point = 0)).length ≤ 1 := by
  by_cases firstZero : first.eval point = 0 <;>
    by_cases secondZero : second.eval point = 0
  · exact (notBoth ⟨firstZero, secondZero⟩).elim
  · simp [firstZero, secondZero]
  · simp [firstZero, secondZero]
  · simp [firstZero, secondZero]

private theorem activeTriple_length_le_one
    (first second third : HermitianForm) (point : QI)
    (firstSecond : ¬(first.eval point = 0 ∧ second.eval point = 0))
    (firstThird : ¬(first.eval point = 0 ∧ third.eval point = 0))
    (secondThird : ¬(second.eval point = 0 ∧ third.eval point = 0)) :
    ([first, second, third].filter fun form =>
      decide (form.eval point = 0)).length ≤ 1 := by
  by_cases firstZero : first.eval point = 0 <;>
    by_cases secondZero : second.eval point = 0 <;>
      by_cases thirdZero : third.eval point = 0
  · exact (firstSecond ⟨firstZero, secondZero⟩).elim
  · exact (firstSecond ⟨firstZero, secondZero⟩).elim
  · exact (firstThird ⟨firstZero, thirdZero⟩).elim
  · simp [firstZero, secondZero, thirdZero]
  · exact (secondThird ⟨secondZero, thirdZero⟩).elim
  · simp [firstZero, secondZero, thirdZero]
  · simp [firstZero, secondZero, thirdZero]
  · simp [firstZero, secondZero, thirdZero]

/-- Once an annulus wall is active, no two strict sector walls can also be
active: parallel strip walls are disjoint, while perpendicular pairs form a
corner of normalized squared radius one half. -/
theorem activeSectorInteriorForms_length_le_one_of_radial_zero
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (point : QI)
    (denominator : matrix.c * point + matrix.d ≠ 0)
    {radialForm : HermitianForm}
    (radialMember : radialForm ∈ radialInteriorForms kind exponent matrix)
    (radialZero : radialForm.eval point = 0) :
    (activeSectorInteriorForms sector
      (normalizedMatrix kind exponent matrix) point).length ≤ 1 := by
  let normalized := normalizedMatrix kind exponent matrix
  have normalizedDenominator :
      normalized.c * point + normalized.d ≠ 0 := by
    have lowerRow := normalizedMatrix_lowerRow kind exponent matrix
    simpa only [normalized, lowerRow.1, lowerRow.2] using denominator
  cases sector with
  | east =>
      apply activeTriple_length_le_one
      · rintro ⟨realZero, imagZero⟩
        exact radialInterior_realImag_not_all_zero kind exponent matrix point
          denominator radialMember true true (1 / 2) (-1 / 2) (by norm_num)
            radialZero realZero imagZero
      · rintro ⟨realZero, imagZero⟩
        exact radialInterior_realImag_not_all_zero kind exponent matrix point
          denominator radialMember true false (1 / 2) (1 / 2) (by norm_num)
            radialZero realZero imagZero
      · exact orientedImagForms_not_both_zero true false normalized (-1 / 2)
          (1 / 2) point normalizedDenominator (by norm_num)
  | northEast =>
      apply activePair_length_le_one
      rintro ⟨realZero, imagZero⟩
      exact radialInterior_realImag_not_all_zero kind exponent matrix point
        denominator radialMember true true (1 / 2) (1 / 2) (by norm_num)
          radialZero realZero imagZero
  | north =>
      apply activeTriple_length_le_one
      · rintro ⟨imagZero, realZero⟩
        exact radialInterior_realImag_not_all_zero kind exponent matrix point
          denominator radialMember true true (-1 / 2) (1 / 2) (by norm_num)
            radialZero realZero imagZero
      · rintro ⟨imagZero, realZero⟩
        exact radialInterior_realImag_not_all_zero kind exponent matrix point
          denominator radialMember false true (1 / 2) (1 / 2) (by norm_num)
            radialZero realZero imagZero
      · exact orientedRealForms_not_both_zero true false normalized (-1 / 2)
          (1 / 2) point normalizedDenominator (by norm_num)
  | northWest =>
      apply activePair_length_le_one
      rintro ⟨realZero, imagZero⟩
      exact radialInterior_realImag_not_all_zero kind exponent matrix point
        denominator radialMember false true (-1 / 2) (1 / 2) (by norm_num)
          radialZero realZero imagZero
  | west =>
      apply activeTriple_length_le_one
      · rintro ⟨realZero, imagZero⟩
        exact radialInterior_realImag_not_all_zero kind exponent matrix point
          denominator radialMember false true (-1 / 2) (-1 / 2) (by norm_num)
            radialZero realZero imagZero
      · rintro ⟨realZero, imagZero⟩
        exact radialInterior_realImag_not_all_zero kind exponent matrix point
          denominator radialMember false false (-1 / 2) (1 / 2) (by norm_num)
            radialZero realZero imagZero
      · exact orientedImagForms_not_both_zero true false normalized (-1 / 2)
          (1 / 2) point normalizedDenominator (by norm_num)
  | southWest =>
      apply activePair_length_le_one
      rintro ⟨realZero, imagZero⟩
      exact radialInterior_realImag_not_all_zero kind exponent matrix point
        denominator radialMember false false (-1 / 2) (-1 / 2) (by norm_num)
          radialZero realZero imagZero
  | south =>
      apply activeTriple_length_le_one
      · rintro ⟨imagZero, realZero⟩
        exact radialInterior_realImag_not_all_zero kind exponent matrix point
          denominator radialMember true false (-1 / 2) (-1 / 2) (by norm_num)
            radialZero realZero imagZero
      · rintro ⟨imagZero, realZero⟩
        exact radialInterior_realImag_not_all_zero kind exponent matrix point
          denominator radialMember false false (1 / 2) (-1 / 2) (by norm_num)
            radialZero realZero imagZero
      · exact orientedRealForms_not_both_zero true false normalized (-1 / 2)
          (1 / 2) point normalizedDenominator (by norm_num)
  | southEast =>
      apply activePair_length_le_one
      rintro ⟨realZero, imagZero⟩
      exact radialInterior_realImag_not_all_zero kind exponent matrix point
        denominator radialMember true false (1 / 2) (-1 / 2) (by norm_num)
          radialZero realZero imagZero

private theorem negNormComparison_gradient_nonzero
    (matrix : Mat2 QI) (radiusSq : ℚ) (point : QI)
    (determinantNonzero : determinant matrix ≠ 0)
    (radiusPositive : 0 < radiusSq)
    (boundary : (normComparisonForm matrix radiusSq).neg.eval point = 0) :
    gradientX (normComparisonForm matrix radiusSq).neg point ≠ 0 ∨
      gradientY (normComparisonForm matrix radiusSq).neg point ≠ 0 := by
  have baseBoundary :
      (normComparisonForm matrix radiusSq).eval point = 0 := by
    simpa only [HermitianForm.eval_neg, neg_eq_zero] using boundary
  rcases normComparison_gradient_nonzero matrix radiusSq point
      determinantNonzero radiusPositive baseBoundary with xNonzero | yNonzero
  · exact Or.inl (by simpa using neg_ne_zero.mpr xNonzero)
  · exact Or.inr (by simpa using neg_ne_zero.mpr yNonzero)

private theorem normSq_pos_of_coordinates (value : QI)
    (nonzero : value.re ≠ 0 ∨ value.im ≠ 0) : 0 < normSq value := by
  rcases nonzero with realNonzero | imagNonzero
  · simp only [normSq]
    nlinarith [sq_pos_of_ne_zero realNonzero]
  · simp only [normSq]
    nlinarith [sq_pos_of_ne_zero imagNonzero]

theorem orientedNormForm_boundaryDiscriminant_neg
    (increasing : Bool) (matrix : Mat2 QI) (radiusSq : ℚ)
    (determinantNonzero : determinant matrix ≠ 0)
    (radiusPositive : 0 < radiusSq) :
    boundaryDiscriminant
      (orientedNormForm increasing matrix radiusSq) < 0 := by
  have determinantPositive := normSq_pos determinantNonzero
  cases increasing <;>
    simp only [orientedNormForm, Bool.false_eq_true, if_false, if_true,
      boundaryDiscriminant_neg, boundaryDiscriminant_normComparisonForm] <;>
    nlinarith

theorem orientedRealForm_boundaryDiscriminant_neg
    (increasing : Bool) (matrix : Mat2 QI) (threshold : ℚ)
    (determinantNonzero : determinant matrix ≠ 0) :
    boundaryDiscriminant
      (orientedRealForm increasing matrix threshold) < 0 := by
  have determinantPositive := normSq_pos determinantNonzero
  cases increasing <;>
    simp only [orientedRealForm, Bool.false_eq_true, if_false, if_true,
      boundaryDiscriminant_neg, boundaryDiscriminant_realComparisonForm] <;>
    linarith

theorem orientedImagForm_boundaryDiscriminant_neg
    (increasing : Bool) (matrix : Mat2 QI) (threshold : ℚ)
    (determinantNonzero : determinant matrix ≠ 0) :
    boundaryDiscriminant
      (orientedImagForm increasing matrix threshold) < 0 := by
  have determinantPositive := normSq_pos determinantNonzero
  cases increasing <;>
    simp only [orientedImagForm, Bool.false_eq_true, if_false, if_true,
      boundaryDiscriminant_neg, boundaryDiscriminant_imagComparisonForm] <;>
    linarith

theorem radialInteriorForm_boundaryDiscriminant_neg
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI)
    (determinantNonzero : determinant matrix ≠ 0)
    {form : HermitianForm}
    (member : form ∈ radialInteriorForms kind exponent matrix) :
    boundaryDiscriminant form < 0 := by
  cases kind with
  | initialHigh =>
      simp only [radialInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact orientedNormForm_boundaryDiscriminant_neg true matrix
          ((2 : ℚ) ^ exponent) determinantNonzero (by positivity)
      · exact orientedNormForm_boundaryDiscriminant_neg false matrix
          ((2 : ℚ) ^ (exponent + 1)) determinantNonzero (by positivity)
  | initialLow =>
      simp only [radialInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact orientedNormForm_boundaryDiscriminant_neg true matrix
          (1 / (2 : ℚ) ^ exponent) determinantNonzero (by positivity)
      · exact orientedNormForm_boundaryDiscriminant_neg false matrix
          (2 / (2 : ℚ) ^ exponent) determinantNonzero (by positivity)
  | loop =>
      simp only [radialInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact orientedNormForm_boundaryDiscriminant_neg true matrix
          ((2 : ℚ) ^ exponent) determinantNonzero (by positivity)
      · exact orientedNormForm_boundaryDiscriminant_neg false matrix
          ((2 : ℚ) ^ (exponent + 1)) determinantNonzero (by positivity)

theorem sectorInteriorForm_boundaryDiscriminant_neg
    (sector : Sector) (matrix : Mat2 QI)
    (determinantNonzero : determinant matrix ≠ 0)
    {form : HermitianForm} (member : form ∈ sectorInteriorForms sector matrix) :
    boundaryDiscriminant form < 0 := by
  have equality : boundaryDiscriminant form =
      -normSq (determinant matrix) := by
    cases sector <;>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
    all_goals rcases member with rfl | rfl | rfl
    all_goals
      simp [orientedRealForm, orientedImagForm, boundaryDiscriminant_neg,
        boundaryDiscriminant_realComparisonForm,
        boundaryDiscriminant_imagComparisonForm]
  rw [equality]
  exact neg_lt_zero.mpr (normSq_pos determinantNonzero)

theorem orientedNormForm_gradient_pos
    (increasing : Bool) (matrix : Mat2 QI) (radiusSq : ℚ) (point : QI)
    (determinantNonzero : determinant matrix ≠ 0)
    (radiusPositive : 0 < radiusSq)
    (boundary : (orientedNormForm increasing matrix radiusSq).eval point = 0) :
    0 < normSq (gradientVector
      (orientedNormForm increasing matrix radiusSq) point) := by
  apply normSq_pos_of_coordinates
    (gradientVector (orientedNormForm increasing matrix radiusSq) point)
  cases increasing with
  | false =>
      simpa only [orientedNormForm_false, gradientVector] using
        negNormComparison_gradient_nonzero matrix radiusSq point
          determinantNonzero radiusPositive boundary
  | true =>
      simpa only [orientedNormForm_true, gradientVector] using
        normComparison_gradient_nonzero matrix radiusSq point
          determinantNonzero radiusPositive boundary

/-- Every strict annulus-interior face has a nonzero gradient on its zero
set. -/
theorem radialInteriorForm_gradient_pos
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI)
    (point : QI) (determinantNonzero : determinant matrix ≠ 0)
    {form : HermitianForm}
    (member : form ∈ radialInteriorForms kind exponent matrix)
    (boundary : form.eval point = 0) :
    0 < normSq (gradientVector form point) := by
  cases kind with
  | initialHigh =>
      simp only [radialInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact orientedNormForm_gradient_pos true matrix ((2 : ℚ) ^ exponent)
          point determinantNonzero (by positivity) boundary
      · exact orientedNormForm_gradient_pos false matrix
          ((2 : ℚ) ^ (exponent + 1)) point determinantNonzero
            (by positivity) boundary
  | initialLow =>
      simp only [radialInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact orientedNormForm_gradient_pos true matrix
          (1 / (2 : ℚ) ^ exponent) point determinantNonzero
            (by positivity) boundary
      · exact orientedNormForm_gradient_pos false matrix
          (2 / (2 : ℚ) ^ exponent) point determinantNonzero
            (by positivity) boundary
  | loop =>
      simp only [radialInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact orientedNormForm_gradient_pos true matrix ((2 : ℚ) ^ exponent)
          point determinantNonzero (by positivity) boundary
      · exact orientedNormForm_gradient_pos false matrix
          ((2 : ℚ) ^ (exponent + 1)) point determinantNonzero
            (by positivity) boundary

/-- Every strict sector-interior face has a nonzero gradient on its zero
set. -/
theorem sectorInteriorForm_gradient_pos
    (sector : Sector) (matrix : Mat2 QI) (point : QI)
    (determinantNonzero : determinant matrix ≠ 0)
    {form : HermitianForm} (member : form ∈ sectorInteriorForms sector matrix)
    (boundary : form.eval point = 0) :
    0 < normSq (gradientVector form point) := by
  cases sector with
  | east =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl | rfl
      · exact orientedRealForm_gradient_pos true matrix (1 / 2) point
          determinantNonzero boundary
      · exact orientedImagForm_gradient_pos true matrix (-1 / 2) point
          determinantNonzero boundary
      · exact orientedImagForm_gradient_pos false matrix (1 / 2) point
          determinantNonzero boundary
  | northEast =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact orientedRealForm_gradient_pos true matrix (1 / 2) point
          determinantNonzero boundary
      · exact orientedImagForm_gradient_pos true matrix (1 / 2) point
          determinantNonzero boundary
  | north =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl | rfl
      · exact orientedImagForm_gradient_pos true matrix (1 / 2) point
          determinantNonzero boundary
      · exact orientedRealForm_gradient_pos true matrix (-1 / 2) point
          determinantNonzero boundary
      · exact orientedRealForm_gradient_pos false matrix (1 / 2) point
          determinantNonzero boundary
  | northWest =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact orientedRealForm_gradient_pos false matrix (-1 / 2) point
          determinantNonzero boundary
      · exact orientedImagForm_gradient_pos true matrix (1 / 2) point
          determinantNonzero boundary
  | west =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl | rfl
      · exact orientedRealForm_gradient_pos false matrix (-1 / 2) point
          determinantNonzero boundary
      · exact orientedImagForm_gradient_pos true matrix (-1 / 2) point
          determinantNonzero boundary
      · exact orientedImagForm_gradient_pos false matrix (1 / 2) point
          determinantNonzero boundary
  | southWest =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact orientedRealForm_gradient_pos false matrix (-1 / 2) point
          determinantNonzero boundary
      · exact orientedImagForm_gradient_pos false matrix (-1 / 2) point
          determinantNonzero boundary
  | south =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl | rfl
      · exact orientedImagForm_gradient_pos false matrix (-1 / 2) point
          determinantNonzero boundary
      · exact orientedRealForm_gradient_pos true matrix (-1 / 2) point
          determinantNonzero boundary
      · exact orientedRealForm_gradient_pos false matrix (1 / 2) point
          determinantNonzero boundary
  | southEast =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact orientedRealForm_gradient_pos true matrix (1 / 2) point
          determinantNonzero boundary
      · exact orientedImagForm_gradient_pos false matrix (-1 / 2) point
          determinantNonzero boundary

private theorem normComparisonForms_not_both_zero
    (matrix : Mat2 QI) (lowerRadius upperRadius : ℚ) (point : QI)
    (denominator : matrix.c * point + matrix.d ≠ 0)
    (radiiDistinct : lowerRadius ≠ upperRadius) :
    ¬((normComparisonForm matrix lowerRadius).eval point = 0 ∧
      (normComparisonForm matrix upperRadius).neg.eval point = 0) := by
  rintro ⟨lowerZero, upperNegZero⟩
  have upperZero :
      (normComparisonForm matrix upperRadius).eval point = 0 := by
    simpa only [HermitianForm.eval_neg, neg_eq_zero] using upperNegZero
  have lowerNorm :=
    (norm_homographic_eq_iff matrix point lowerRadius denominator).2 lowerZero
  have upperNorm :=
    (norm_homographic_eq_iff matrix point upperRadius denominator).2 upperZero
  apply radiiDistinct
  exact lowerNorm.symm.trans upperNorm

/-- A positive angle gap between the two actual gradients at a rational
point closes the executable two-face compass search.  Unlike the invariant
boundary specialization below, this statement deliberately requires no
exact-zero hypothesis and is therefore the form used by rational
approximations to algebraic intersections. -/
theorem tangentDirectionCertificate?_isSome_pair_of_gradientGap
    (left right : HermitianForm) (point : QI)
    (gradientGap :
      0 < normSq (gradientVector left point) *
            normSq (gradientVector right point) -
          2 * ((gradientVector left point).re *
                (gradientVector right point).re +
              (gradientVector left point).im *
                (gradientVector right point).im) ^ 2) :
    (tangentDirectionCertificate? [left, right] point).isSome := by
  rcases exists_coordinateDirection_slopes_of_angleGap_pos
      (gradientVector left point) (gradientVector right point) gradientGap with
    ⟨direction, member, leftPositive, rightPositive⟩
  apply tangentDirectionCertificate?_isSome_of_mem member
  intro form formMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at formMember
  rcases formMember with rfl | rfl
  · simpa [directionalSlope, gradientVector] using leftPositive
  · simpa [directionalSlope, gradientVector] using rightPositive

def gradientGapResidualCoefficient
    (left right : HermitianForm) : ℚ :=
  let leftDelta := 4 * |left.radial|
  let rightDelta := 4 * |right.radial|
  let pairingDelta := 2 * (|right.radial| + |left.radial|)
  1 +
    |boundaryDiscriminant left| * rightDelta +
    |boundaryDiscriminant right| * leftDelta +
    leftDelta * rightDelta +
    4 * |gradientPairingConstant left right| * pairingDelta +
    2 * pairingDelta ^ 2

theorem gradientGapResidualCoefficient_pos
    (left right : HermitianForm) :
    0 < gradientGapResidualCoefficient left right := by
  unfold gradientGapResidualCoefficient
  positivity

def gradientNormResidualCoefficient (form : HermitianForm) : ℚ :=
  1 + 4 * |form.radial|

theorem gradientNormResidualCoefficient_pos (form : HermitianForm) :
    0 < gradientNormResidualCoefficient form := by
  unfold gradientNormResidualCoefficient
  positivity

/-- A nondegenerate boundary gradient stays nonzero at a nearby rational
point once the form residual is smaller than an explicit rational fraction
of its negative discriminant. -/
theorem gradientNorm_pos_of_small_residual
    (form : HermitianForm) (point : QI) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon)
    (residual : |form.eval point| < epsilon)
    (small : gradientNormResidualCoefficient form * epsilon <
      -boundaryDiscriminant form) :
    0 < normSq (gradientVector form point) := by
  have productBound :
      |4 * form.radial * form.eval point| ≤
        4 * |form.radial| * epsilon := by
    rw [abs_mul, abs_mul]
    norm_num
    exact mul_le_mul_of_nonneg_left (le_of_lt residual) (by positivity)
  have coefficientBound :
      4 * |form.radial| * epsilon <
        gradientNormResidualCoefficient form * epsilon := by
    unfold gradientNormResidualCoefficient
    nlinarith [epsilonPositive]
  have absoluteBound := productBound.trans_lt coefficientBound
  have productLower := (abs_lt.mp absoluteBound).1
  have identity := gradient_discriminant_identity form point
  change 0 < gradientX form point ^ 2 + gradientY form point ^ 2
  nlinarith

/-- Quantitative version of gradient nondegeneracy: half of the invariant
boundary norm remains after a residual perturbation smaller than the other
half. -/
theorem neg_boundaryDiscriminant_div_two_lt_gradientNorm
    (form : HermitianForm) (point : QI) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon)
    (residual : |form.eval point| < epsilon)
    (small : gradientNormResidualCoefficient form * epsilon <
      -boundaryDiscriminant form / 2) :
    -boundaryDiscriminant form / 2 <
      normSq (gradientVector form point) := by
  have productBound :
      |4 * form.radial * form.eval point| ≤
        4 * |form.radial| * epsilon := by
    rw [abs_mul, abs_mul]
    norm_num
    exact mul_le_mul_of_nonneg_left (le_of_lt residual) (by positivity)
  have coefficientBound :
      4 * |form.radial| * epsilon <
        gradientNormResidualCoefficient form * epsilon := by
    unfold gradientNormResidualCoefficient
    nlinarith [epsilonPositive]
  have absoluteBound := productBound.trans_lt coefficientBound
  have productLower := (abs_lt.mp absoluteBound).1
  have identity := gradient_discriminant_identity form point
  change -boundaryDiscriminant form / 2 <
    gradientX form point ^ 2 + gradientY form point ^ 2
  nlinarith

theorem gradientGap_lower_of_residual
    (left right : HermitianForm) (point : QI) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) (epsilonLeOne : epsilon ≤ 1)
    (leftResidual : |left.eval point| < epsilon)
    (rightResidual : |right.eval point| < epsilon) :
    boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2 -
          gradientGapResidualCoefficient left right * epsilon ≤
      normSq (gradientVector left point) *
          normSq (gradientVector right point) -
        2 * ((gradientVector left point).re *
              (gradientVector right point).re +
            (gradientVector left point).im *
              (gradientVector right point).im) ^ 2 := by
  let leftDiscriminant := boundaryDiscriminant left
  let rightDiscriminant := boundaryDiscriminant right
  let pairing := gradientPairingConstant left right
  let leftDelta := 4 * left.radial * left.eval point
  let rightDelta := 4 * right.radial * right.eval point
  let pairingDelta :=
    2 * right.radial * left.eval point +
      2 * left.radial * right.eval point
  let leftCoefficient := 4 * |left.radial|
  let rightCoefficient := 4 * |right.radial|
  let pairingCoefficient := 2 * (|right.radial| + |left.radial|)
  let coefficient := gradientGapResidualCoefficient left right
  have epsilonNonnegative : 0 ≤ epsilon := epsilonPositive.le
  have leftCoefficientNonnegative : 0 ≤ leftCoefficient := by
    dsimp only [leftCoefficient]
    positivity
  have rightCoefficientNonnegative : 0 ≤ rightCoefficient := by
    dsimp only [rightCoefficient]
    positivity
  have pairingCoefficientNonnegative : 0 ≤ pairingCoefficient := by
    dsimp only [pairingCoefficient]
    positivity
  have leftDeltaBound : |leftDelta| ≤ leftCoefficient * epsilon := by
    dsimp only [leftDelta, leftCoefficient]
    rw [abs_mul, abs_mul]
    norm_num
    exact mul_le_mul_of_nonneg_left (le_of_lt leftResidual)
      (mul_nonneg (by norm_num) (abs_nonneg left.radial))
  have rightDeltaBound : |rightDelta| ≤ rightCoefficient * epsilon := by
    dsimp only [rightDelta, rightCoefficient]
    rw [abs_mul, abs_mul]
    norm_num
    exact mul_le_mul_of_nonneg_left (le_of_lt rightResidual)
      (mul_nonneg (by norm_num) (abs_nonneg right.radial))
  have pairingDeltaBound :
      |pairingDelta| ≤ pairingCoefficient * epsilon := by
    dsimp only [pairingDelta, pairingCoefficient]
    calc
      |2 * right.radial * left.eval point +
          2 * left.radial * right.eval point| ≤
          |2 * right.radial * left.eval point| +
            |2 * left.radial * right.eval point| := abs_add_le _ _
      _ = 2 * |right.radial| * |left.eval point| +
          2 * |left.radial| * |right.eval point| := by
            simp only [abs_mul]
            norm_num
      _ ≤ 2 * |right.radial| * epsilon +
          2 * |left.radial| * epsilon := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left (le_of_lt leftResidual)
                (mul_nonneg (by norm_num) (abs_nonneg right.radial)))
              (mul_le_mul_of_nonneg_left (le_of_lt rightResidual)
                (mul_nonneg (by norm_num) (abs_nonneg left.radial)))
      _ = 2 * (|right.radial| + |left.radial|) * epsilon := by ring
  have epsilonSquareLe : epsilon * epsilon ≤ epsilon := by
    nlinarith
  have leftRightBound :
      |leftDelta * rightDelta| ≤
        leftCoefficient * rightCoefficient * epsilon := by
    rw [abs_mul]
    calc
      |leftDelta| * |rightDelta| ≤
          (leftCoefficient * epsilon) *
            (rightCoefficient * epsilon) := by
        exact mul_le_mul leftDeltaBound rightDeltaBound
          (abs_nonneg rightDelta)
          (mul_nonneg leftCoefficientNonnegative epsilonNonnegative)
      _ = leftCoefficient * rightCoefficient *
          (epsilon * epsilon) := by ring
      _ ≤ leftCoefficient * rightCoefficient * epsilon := by
        exact mul_le_mul_of_nonneg_left epsilonSquareLe
          (mul_nonneg leftCoefficientNonnegative rightCoefficientNonnegative)
  have pairingSquareBound :
      |2 * pairingDelta ^ 2| ≤
        2 * pairingCoefficient ^ 2 * epsilon := by
    have upperNonnegative :
        0 ≤ pairingCoefficient * epsilon :=
      mul_nonneg pairingCoefficientNonnegative epsilonNonnegative
    have squareBound :
        |pairingDelta| ^ 2 ≤
          (pairingCoefficient * epsilon) ^ 2 := by
      simpa only [pow_two] using
        (mul_self_le_mul_self (abs_nonneg pairingDelta) pairingDeltaBound)
    calc
      |2 * pairingDelta ^ 2| = 2 * |pairingDelta| ^ 2 := by
        rw [abs_mul, abs_pow]
        norm_num
      _ ≤
          2 * (pairingCoefficient * epsilon) ^ 2 := by
        exact mul_le_mul_of_nonneg_left squareBound (by norm_num)
      _ = 2 * pairingCoefficient ^ 2 * (epsilon * epsilon) := by ring
      _ ≤ 2 * pairingCoefficient ^ 2 * epsilon := by
        exact mul_le_mul_of_nonneg_left epsilonSquareLe (by positivity)
  let perturbation :=
    (-leftDiscriminant) * rightDelta +
      (-rightDiscriminant) * leftDelta +
      leftDelta * rightDelta - 4 * pairing * pairingDelta -
      2 * pairingDelta ^ 2
  have firstBound :
      |(-leftDiscriminant) * rightDelta| ≤
        |leftDiscriminant| * rightCoefficient * epsilon := by
    rw [abs_mul, abs_neg]
    exact (mul_le_mul_of_nonneg_left rightDeltaBound
      (abs_nonneg leftDiscriminant)).trans_eq (by ring)
  have secondBound :
      |(-rightDiscriminant) * leftDelta| ≤
        |rightDiscriminant| * leftCoefficient * epsilon := by
    rw [abs_mul, abs_neg]
    exact (mul_le_mul_of_nonneg_left leftDeltaBound
      (abs_nonneg rightDiscriminant)).trans_eq (by ring)
  have fourthBound :
      |4 * pairing * pairingDelta| ≤
        4 * |pairing| * pairingCoefficient * epsilon := by
    rw [abs_mul, abs_mul]
    norm_num
    exact (mul_le_mul_of_nonneg_left pairingDeltaBound
      (mul_nonneg (by norm_num) (abs_nonneg pairing))).trans_eq (by ring)
  have perturbationBound : |perturbation| ≤ coefficient * epsilon := by
    calc
      |perturbation| ≤
          |(-leftDiscriminant) * rightDelta| +
            |(-rightDiscriminant) * leftDelta| +
            |leftDelta * rightDelta| +
            |4 * pairing * pairingDelta| +
            |2 * pairingDelta ^ 2| := by
              dsimp only [perturbation]
              calc
                |_ + _ + _ - _ - _| =
                    |(((-leftDiscriminant) * rightDelta +
                        (-rightDiscriminant) * leftDelta) +
                      leftDelta * rightDelta) +
                      (-(4 * pairing * pairingDelta)) +
                      (-(2 * pairingDelta ^ 2))| := by
                        congr 1
                        ring_nf
                _ ≤ |(((-leftDiscriminant) * rightDelta +
                        (-rightDiscriminant) * leftDelta) +
                      leftDelta * rightDelta) +
                      (-(4 * pairing * pairingDelta))| +
                      |-(2 * pairingDelta ^ 2)| := abs_add_le _ _
                _ ≤ (|((-leftDiscriminant) * rightDelta +
                        (-rightDiscriminant) * leftDelta) +
                      leftDelta * rightDelta| +
                      |-(4 * pairing * pairingDelta)|) +
                      |-(2 * pairingDelta ^ 2)| := by
                        gcongr
                        exact abs_add_le _ _
                _ ≤ ((|(-leftDiscriminant) * rightDelta +
                        (-rightDiscriminant) * leftDelta| +
                      |leftDelta * rightDelta|) +
                      |-(4 * pairing * pairingDelta)|) +
                      |-(2 * pairingDelta ^ 2)| := by
                        gcongr
                        exact abs_add_le _ _
                _ ≤ (((|(-leftDiscriminant) * rightDelta| +
                        |(-rightDiscriminant) * leftDelta|) +
                      |leftDelta * rightDelta|) +
                      |-(4 * pairing * pairingDelta)|) +
                      |-(2 * pairingDelta ^ 2)| := by
                        gcongr
                        exact abs_add_le _ _
                _ = |(-leftDiscriminant) * rightDelta| +
                    |(-rightDiscriminant) * leftDelta| +
                    |leftDelta * rightDelta| +
                    |4 * pairing * pairingDelta| +
                    |2 * pairingDelta ^ 2| := by
                      rw [abs_neg, abs_neg]
      _ ≤ (|leftDiscriminant| * rightCoefficient +
            |rightDiscriminant| * leftCoefficient +
            leftCoefficient * rightCoefficient +
            4 * |pairing| * pairingCoefficient +
            2 * pairingCoefficient ^ 2) * epsilon := by
          calc
            _ ≤ |leftDiscriminant| * rightCoefficient * epsilon +
                |rightDiscriminant| * leftCoefficient * epsilon +
                leftCoefficient * rightCoefficient * epsilon +
                4 * |pairing| * pairingCoefficient * epsilon +
                2 * pairingCoefficient ^ 2 * epsilon := by
                  gcongr
            _ = _ := by ring
      _ ≤ coefficient * epsilon := by
        dsimp only [coefficient, gradientGapResidualCoefficient,
          leftCoefficient, rightCoefficient, pairingCoefficient,
          leftDiscriminant, rightDiscriminant, pairing]
        nlinarith
  have leftNormIdentity :
      normSq (gradientVector left point) =
        -leftDiscriminant + leftDelta := by
    have identity := gradient_discriminant_identity left point
    dsimp only [leftDiscriminant, leftDelta]
    change 4 * left.radial * left.eval point =
      normSq (gradientVector left point) + boundaryDiscriminant left at identity
    linarith
  have rightNormIdentity :
      normSq (gradientVector right point) =
        -rightDiscriminant + rightDelta := by
    have identity := gradient_discriminant_identity right point
    dsimp only [rightDiscriminant, rightDelta]
    change 4 * right.radial * right.eval point =
      normSq (gradientVector right point) + boundaryDiscriminant right at identity
    linarith
  have pairingIdentity :
      (gradientVector left point).re * (gradientVector right point).re +
          (gradientVector left point).im * (gradientVector right point).im =
        pairing + pairingDelta := by
    have identity := gradient_pairing_identity left right point
    dsimp only [pairing, pairingDelta]
    change gradientX left point * gradientX right point +
      gradientY left point * gradientY right point = _
    linarith
  have expansion :
      normSq (gradientVector left point) *
            normSq (gradientVector right point) -
          2 * ((gradientVector left point).re *
                (gradientVector right point).re +
              (gradientVector left point).im *
                (gradientVector right point).im) ^ 2 =
        (leftDiscriminant * rightDiscriminant - 2 * pairing ^ 2) +
          perturbation := by
    rw [leftNormIdentity, rightNormIdentity, pairingIdentity]
    dsimp only [perturbation]
    ring
  have perturbationLower : -coefficient * epsilon ≤ perturbation := by
    have lower := neg_abs_le perturbation
    linarith
  rw [expansion]
  dsimp only [coefficient, leftDiscriminant, rightDiscriminant, pairing]
    at perturbationLower
  linarith

theorem gradientGap_pos_of_small_residual
    (left right : HermitianForm) (point : QI) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) (epsilonLeOne : epsilon ≤ 1)
    (leftResidual : |left.eval point| < epsilon)
    (rightResidual : |right.eval point| < epsilon)
    (small :
      gradientGapResidualCoefficient left right * epsilon <
        boundaryDiscriminant left * boundaryDiscriminant right -
          2 * gradientPairingConstant left right ^ 2) :
    0 < normSq (gradientVector left point) *
          normSq (gradientVector right point) -
        2 * ((gradientVector left point).re *
              (gradientVector right point).re +
            (gradientVector left point).im *
              (gradientVector right point).im) ^ 2 := by
  have lower := gradientGap_lower_of_residual left right point epsilon
    epsilonPositive epsilonLeOne leftResidual rightResidual
  linarith

/-- Half of the invariant two-face angle gap survives when twice the
explicit perturbation bound remains below the invariant gap. -/
theorem angleGap_div_two_lt_gradientGap
    (left right : HermitianForm) (point : QI) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) (epsilonLeOne : epsilon ≤ 1)
    (leftResidual : |left.eval point| < epsilon)
    (rightResidual : |right.eval point| < epsilon)
    (small : 2 * gradientGapResidualCoefficient left right * epsilon <
      boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2) :
    (boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2) / 2 <
      normSq (gradientVector left point) *
          normSq (gradientVector right point) -
        2 * ((gradientVector left point).re *
              (gradientVector right point).re +
            (gradientVector left point).im *
              (gradientVector right point).im) ^ 2 := by
  have lower := gradientGap_lower_of_residual left right point epsilon
    epsilonPositive epsilonLeOne leftResidual rightResidual
  nlinarith

/-- A list of at most two residual-controlled faces has a successful
executable compass direction when its singleton discriminant or pair angle
gap dominates the displayed residual. -/
theorem tangentDirectionCertificate?_isSome_of_length_le_two_residual
    (forms : List HermitianForm) (point : QI) (epsilon : ℚ)
    (length : forms.length ≤ 2)
    (epsilonPositive : 0 < epsilon) (epsilonLeOne : epsilon ≤ 1)
    (residual : ∀ form ∈ forms, |form.eval point| < epsilon)
    (singletonSmall : ∀ form, forms = [form] →
      gradientNormResidualCoefficient form * epsilon <
        -boundaryDiscriminant form)
    (pairSmall : ∀ left right, forms = [left, right] →
      gradientGapResidualCoefficient left right * epsilon <
        boundaryDiscriminant left * boundaryDiscriminant right -
          2 * gradientPairingConstant left right ^ 2) :
    (tangentDirectionCertificate? forms point).isSome := by
  cases forms with
  | nil =>
      exact tangentDirectionCertificate?_isSome_empty point
  | cons first tail =>
      cases tail with
      | nil =>
          have gradientPositive := gradientNorm_pos_of_small_residual first
            point epsilon epsilonPositive (residual first (by simp))
              (singletonSmall first rfl)
          exact tangentDirectionCertificate?_isSome_singleton first point
            (coordinates_nonzero_of_normSq_pos _ gradientPositive)
      | cons second rest =>
          have restNil : rest = [] := by
            cases rest with
            | nil => rfl
            | cons third further => simp at length
          subst rest
          have gradientGap := gradientGap_pos_of_small_residual first second
            point epsilon epsilonPositive epsilonLeOne
              (residual first (by simp)) (residual second (by simp))
              (pairSmall first second rfl)
          exact tangentDirectionCertificate?_isSome_pair_of_gradientGap first
            second point gradientGap

/-- Static residual threshold for a list known to contain at most two active
faces.  The fallback branch is irrelevant under that length proof but keeps
the definition total and executable. -/
def tangentResidualBudget : List HermitianForm → ℚ
  | [] => 1
  | [form] =>
      min 1 ((-boundaryDiscriminant form) /
        (2 * gradientNormResidualCoefficient form))
  | [left, right] =>
      min 1 ((boundaryDiscriminant left * boundaryDiscriminant right -
          2 * gradientPairingConstant left right ^ 2) /
        (2 * gradientGapResidualCoefficient left right))
  | _ :: _ :: _ :: _ => 1

theorem tangentResidualBudget_le_one (forms : List HermitianForm) :
    tangentResidualBudget forms ≤ 1 := by
  cases forms with
  | nil => simp [tangentResidualBudget]
  | cons first tail =>
      cases tail with
      | nil => exact min_le_left _ _
      | cons second rest =>
          cases rest with
          | nil => exact min_le_left _ _
          | cons third further => simp [tangentResidualBudget]

theorem tangentResidualBudget_pos_of_length_le_two
    (forms : List HermitianForm) (length : forms.length ≤ 2)
    (discriminantNegative : ∀ form ∈ forms,
      boundaryDiscriminant form < 0)
    (pairGap : ∀ left right, forms = [left, right] →
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2) :
    0 < tangentResidualBudget forms := by
  cases forms with
  | nil => norm_num [tangentResidualBudget]
  | cons first tail =>
      cases tail with
      | nil =>
          apply lt_min zero_lt_one
          exact div_pos (neg_pos.mpr (discriminantNegative first (by simp)))
            (mul_pos (by norm_num)
              (gradientNormResidualCoefficient_pos first))
      | cons second rest =>
          have restNil : rest = [] := by
            cases rest with
            | nil => rfl
            | cons third further => simp at length
          subst rest
          apply lt_min zero_lt_one
          exact div_pos (pairGap first second rfl)
            (mul_pos (by norm_num)
              (gradientGapResidualCoefficient_pos first second))

theorem tangentDirectionCertificate?_isSome_of_residual_lt_budget
    (forms : List HermitianForm) (point : QI) (epsilon : ℚ)
    (length : forms.length ≤ 2)
    (epsilonPositive : 0 < epsilon)
    (epsilonSmall : epsilon < tangentResidualBudget forms)
    (residual : ∀ form ∈ forms, |form.eval point| < epsilon)
    (discriminantNegative : ∀ form ∈ forms,
      boundaryDiscriminant form < 0)
    (pairGap : ∀ left right, forms = [left, right] →
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2) :
    (tangentDirectionCertificate? forms point).isSome := by
  apply tangentDirectionCertificate?_isSome_of_length_le_two_residual forms
    point epsilon length epsilonPositive
    (epsilonSmall.trans_le (tangentResidualBudget_le_one forms)).le residual
  · intro form singleton
    have negative := discriminantNegative form (by rw [singleton]; simp)
    have coefficientPositive := gradientNormResidualCoefficient_pos form
    have epsilonBudget : epsilon < tangentResidualBudget [form] := by
      simpa only [singleton] using epsilonSmall
    have scaled := mul_lt_mul_of_pos_left epsilonBudget coefficientPositive
    apply scaled.trans
    unfold tangentResidualBudget
    have budgetLe := min_le_right (1 : ℚ)
      ((-boundaryDiscriminant form) /
        (2 * gradientNormResidualCoefficient form))
    calc
      gradientNormResidualCoefficient form *
          tangentResidualBudget [form] ≤
        gradientNormResidualCoefficient form *
          ((-boundaryDiscriminant form) /
            (2 * gradientNormResidualCoefficient form)) :=
        mul_le_mul_of_nonneg_left budgetLe coefficientPositive.le
      _ = (-boundaryDiscriminant form) / 2 := by field_simp
      _ < -boundaryDiscriminant form := by linarith
  · intro left right pair
    have gapPositive := pairGap left right pair
    have coefficientPositive := gradientGapResidualCoefficient_pos left right
    have epsilonBudget : epsilon < tangentResidualBudget [left, right] := by
      simpa only [pair] using epsilonSmall
    have scaled := mul_lt_mul_of_pos_left epsilonBudget coefficientPositive
    apply scaled.trans
    unfold tangentResidualBudget
    let gap := boundaryDiscriminant left * boundaryDiscriminant right -
      2 * gradientPairingConstant left right ^ 2
    have budgetLe := min_le_right (1 : ℚ)
      (gap / (2 * gradientGapResidualCoefficient left right))
    calc
      gradientGapResidualCoefficient left right *
          tangentResidualBudget [left, right] ≤
        gradientGapResidualCoefficient left right *
          (gap / (2 * gradientGapResidualCoefficient left right)) :=
        mul_le_mul_of_nonneg_left budgetLe coefficientPositive.le
      _ = gap / 2 := by field_simp
      _ < gap := by dsimp only [gap]; linarith


/-- A positive invariant angle gap closes the executable two-face search at
an exact common boundary point. -/
private theorem tangentDirectionCertificate?_isSome_pair_of_angleGap
    (left right : HermitianForm) (point : QI)
    (leftBoundary : left.eval point = 0)
    (rightBoundary : right.eval point = 0)
    (angleGap :
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2) :
    (tangentDirectionCertificate? [left, right] point).isSome := by
  have leftIdentity := gradient_discriminant_identity left point
  have rightIdentity := gradient_discriminant_identity right point
  have pairingIdentity := gradient_pairing_identity left right point
  rw [leftBoundary] at leftIdentity
  rw [rightBoundary] at rightIdentity
  rw [leftBoundary, rightBoundary] at pairingIdentity
  norm_num at pairingIdentity
  have leftNorm :
      normSq (gradientVector left point) = -boundaryDiscriminant left := by
    change gradientX left point ^ 2 + gradientY left point ^ 2 = _
    linarith
  have rightNorm :
      normSq (gradientVector right point) = -boundaryDiscriminant right := by
    change gradientX right point ^ 2 + gradientY right point ^ 2 = _
    linarith
  have pairing :
      (gradientVector left point).re * (gradientVector right point).re +
          (gradientVector left point).im * (gradientVector right point).im =
        gradientPairingConstant left right := by
    simpa only [gradientVector, zero_mul, add_zero] using pairingIdentity
  have vectorGap :
      0 < normSq (gradientVector left point) *
            normSq (gradientVector right point) -
          2 * ((gradientVector left point).re *
                (gradientVector right point).re +
              (gradientVector left point).im *
                (gradientVector right point).im) ^ 2 := by
    rw [leftNorm, rightNorm, pairing]
    simpa only [neg_mul_neg] using angleGap
  exact tangentDirectionCertificate?_isSome_pair_of_gradientGap left right
    point vectorGap

/-- Optional-active version of the invariant angle-gap search. -/
private theorem tangentDirectionCertificate?_isSome_activePair_of_angleGap
    (left right : HermitianForm) (point : QI)
    (leftPositive : left.eval point = 0 →
      0 < normSq (gradientVector left point))
    (rightPositive : right.eval point = 0 →
      0 < normSq (gradientVector right point))
    (angleGap :
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2) :
    (tangentDirectionCertificate?
      ([left, right].filter fun form => decide (form.eval point = 0))
        point).isSome := by
  by_cases leftBoundary : left.eval point = 0
  · by_cases rightBoundary : right.eval point = 0
    · have filtered :
          [left, right].filter (fun form => decide (form.eval point = 0)) =
            [left, right] := by
        simp [leftBoundary, rightBoundary]
      rw [filtered]
      exact tangentDirectionCertificate?_isSome_pair_of_angleGap left right
        point leftBoundary rightBoundary angleGap
    · have filtered :
          [left, right].filter (fun form => decide (form.eval point = 0)) =
            [left] := by
        simp [leftBoundary, rightBoundary]
      rw [filtered]
      exact tangentDirectionCertificate?_isSome_singleton left point
        (coordinates_nonzero_of_normSq_pos _ (leftPositive leftBoundary))
  · by_cases rightBoundary : right.eval point = 0
    · have filtered :
          [left, right].filter (fun form => decide (form.eval point = 0)) =
            [right] := by
        simp [leftBoundary, rightBoundary]
      rw [filtered]
      exact tangentDirectionCertificate?_isSome_singleton right point
        (coordinates_nonzero_of_normSq_pos _ (rightPositive rightBoundary))
    · have filtered :
          [left, right].filter (fun form => decide (form.eval point = 0)) =
            [] := by
        simp [leftBoundary, rightBoundary]
      rw [filtered]
      exact tangentDirectionCertificate?_isSome_empty point

private theorem tangentDirectionCertificate?_isSome_activeExclusivePair
    (left right : HermitianForm) (point : QI)
    (leftSearch : (tangentDirectionCertificate?
      ([left].filter fun form => decide (form.eval point = 0)) point).isSome)
    (rightSearch : (tangentDirectionCertificate?
      ([right].filter fun form => decide (form.eval point = 0)) point).isSome)
    (notBoth : ¬(left.eval point = 0 ∧ right.eval point = 0)) :
    (tangentDirectionCertificate?
      ([left, right].filter fun form => decide (form.eval point = 0))
        point).isSome := by
  by_cases leftZero : left.eval point = 0
  · have rightNonzero : right.eval point ≠ 0 := by
      intro rightZero
      exact notBoth ⟨leftZero, rightZero⟩
    apply tangentDirectionCertificate?_isSome_of_subset _ leftSearch
    intro form member
    rcases List.mem_filter.mp member with ⟨source, zero⟩
    apply List.mem_filter.mpr
    refine ⟨?_, zero⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at source ⊢
    rcases source with rfl | rfl
    · rfl
    · exact (rightNonzero (of_decide_eq_true zero)).elim
  · apply tangentDirectionCertificate?_isSome_of_subset _ rightSearch
    intro form member
    rcases List.mem_filter.mp member with ⟨source, zero⟩
    apply List.mem_filter.mpr
    refine ⟨?_, zero⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at source ⊢
    rcases source with rfl | rfl
    · exact (leftZero (of_decide_eq_true zero)).elim
    · rfl

/-- At an affine point, at most one annulus wall is active, and its
nondegenerate circle gradient makes the finite compass search total. -/
theorem tangentDirectionCertificate?_isSome_activeRadialInteriorForms
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI)
    (point : QI) (determinantNonzero : determinant matrix ≠ 0)
    (denominator : matrix.c * point + matrix.d ≠ 0) :
    (tangentDirectionCertificate?
      (activeRadialInteriorForms kind exponent matrix point) point).isSome := by
  cases kind with
  | initialHigh =>
      let lower := normComparisonForm matrix ((2 : ℚ) ^ exponent)
      let upper :=
        (normComparisonForm matrix ((2 : ℚ) ^ (exponent + 1))).neg
      have notBoth : ¬(lower.eval point = 0 ∧ upper.eval point = 0) := by
        apply normComparisonForms_not_both_zero matrix
          ((2 : ℚ) ^ exponent) ((2 : ℚ) ^ (exponent + 1)) point denominator
        have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
        rw [pow_succ]
        nlinarith
      apply tangentDirectionCertificate?_isSome_activeExclusivePair lower
        upper point
      · apply tangentDirectionCertificate?_isSome_activeSingleton
        intro lowerZero
        apply normSq_pos_of_coordinates (gradientVector lower point)
        simpa only [gradientVector] using
          normComparison_gradient_nonzero matrix ((2 : ℚ) ^ exponent)
            point determinantNonzero (by positivity) lowerZero
      · apply tangentDirectionCertificate?_isSome_activeSingleton
        intro upperZero
        apply normSq_pos_of_coordinates (gradientVector upper point)
        simpa only [gradientVector] using
          negNormComparison_gradient_nonzero matrix
            ((2 : ℚ) ^ (exponent + 1)) point determinantNonzero
              (by positivity) upperZero
      · exact notBoth
  | initialLow =>
      let lower := normComparisonForm matrix (1 / (2 : ℚ) ^ exponent)
      let upper :=
        (normComparisonForm matrix (2 / (2 : ℚ) ^ exponent)).neg
      have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
      have notBoth : ¬(lower.eval point = 0 ∧ upper.eval point = 0) := by
        apply normComparisonForms_not_both_zero matrix
          (1 / (2 : ℚ) ^ exponent) (2 / (2 : ℚ) ^ exponent) point
            denominator
        apply ne_of_lt
        exact div_lt_div_of_pos_right (by norm_num) powerPositive
      apply tangentDirectionCertificate?_isSome_activeExclusivePair lower
        upper point
      · apply tangentDirectionCertificate?_isSome_activeSingleton
        intro lowerZero
        apply normSq_pos_of_coordinates (gradientVector lower point)
        simpa only [gradientVector] using
          normComparison_gradient_nonzero matrix
            (1 / (2 : ℚ) ^ exponent) point determinantNonzero
              (div_pos zero_lt_one powerPositive) lowerZero
      · apply tangentDirectionCertificate?_isSome_activeSingleton
        intro upperZero
        apply normSq_pos_of_coordinates (gradientVector upper point)
        simpa only [gradientVector] using
          negNormComparison_gradient_nonzero matrix
            (2 / (2 : ℚ) ^ exponent) point determinantNonzero
              (div_pos (by norm_num) powerPositive) upperZero
      · exact notBoth
  | loop =>
      let lower := normComparisonForm matrix ((2 : ℚ) ^ exponent)
      let upper :=
        (normComparisonForm matrix ((2 : ℚ) ^ (exponent + 1))).neg
      have notBoth : ¬(lower.eval point = 0 ∧ upper.eval point = 0) := by
        apply normComparisonForms_not_both_zero matrix
          ((2 : ℚ) ^ exponent) ((2 : ℚ) ^ (exponent + 1)) point denominator
        have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
        rw [pow_succ]
        nlinarith
      apply tangentDirectionCertificate?_isSome_activeExclusivePair lower
        upper point
      · apply tangentDirectionCertificate?_isSome_activeSingleton
        intro lowerZero
        apply normSq_pos_of_coordinates (gradientVector lower point)
        simpa only [gradientVector] using
          normComparison_gradient_nonzero matrix ((2 : ℚ) ^ exponent)
            point determinantNonzero (by positivity) lowerZero
      · apply tangentDirectionCertificate?_isSome_activeSingleton
        intro upperZero
        apply normSq_pos_of_coordinates (gradientVector upper point)
        simpa only [gradientVector] using
          negNormComparison_gradient_nonzero matrix
            ((2 : ℚ) ^ (exponent + 1)) point determinantNonzero
              (by positivity) upperZero
      · exact notBoth

/-- Joining two active lists preserves finite-search totality when the left
list has at most one active face and, whenever it has one, so does the right
list. -/
private theorem tangentDirectionCertificate?_isSome_activeAppend
    (leftForms rightForms : List HermitianForm) (point : QI)
    (leftSearch : (tangentDirectionCertificate?
      (leftForms.filter fun form => decide (form.eval point = 0))
        point).isSome)
    (rightSearch : (tangentDirectionCertificate?
      (rightForms.filter fun form => decide (form.eval point = 0))
        point).isSome)
    (leftLength :
      (leftForms.filter fun form => decide (form.eval point = 0)).length ≤ 1)
    (rightLength : ∀ left ∈ leftForms, left.eval point = 0 →
      (rightForms.filter fun form => decide (form.eval point = 0)).length ≤ 1)
    (pairSearch : ∀ left ∈ leftForms, ∀ right ∈ rightForms,
      (tangentDirectionCertificate?
        ([left, right].filter fun form => decide (form.eval point = 0))
          point).isSome) :
    (tangentDirectionCertificate?
      ((leftForms ++ rightForms).filter fun form =>
        decide (form.eval point = 0)) point).isSome := by
  generalize leftActiveEq :
      leftForms.filter (fun form => decide (form.eval point = 0)) = leftActive
  cases leftActive with
  | nil =>
      rw [List.filter_append, leftActiveEq]
      exact rightSearch
  | cons left tail =>
      have tailNil : tail = [] := by
        have bound := leftLength
        rw [leftActiveEq] at bound
        cases tail with
        | nil => rfl
        | cons next rest => simp at bound
      subst tail
      have leftFiltered : left ∈ leftForms.filter fun form =>
          decide (form.eval point = 0) := by
        rw [leftActiveEq]
        simp
      rcases List.mem_filter.mp leftFiltered with ⟨leftMember, leftDecision⟩
      have leftZero : left.eval point = 0 := of_decide_eq_true leftDecision
      have rightBound := rightLength left leftMember leftZero
      generalize rightActiveEq :
          rightForms.filter (fun form => decide (form.eval point = 0)) =
            rightActive
      cases rightActive with
      | nil =>
          rw [leftActiveEq] at leftSearch
          rw [List.filter_append, leftActiveEq, rightActiveEq]
          exact leftSearch
      | cons right tail =>
          have tailNil : tail = [] := by
            rw [rightActiveEq] at rightBound
            cases tail with
            | nil => rfl
            | cons next rest => simp at rightBound
          subst tail
          have rightFiltered : right ∈ rightForms.filter fun form =>
              decide (form.eval point = 0) := by
            rw [rightActiveEq]
            simp
          rcases List.mem_filter.mp rightFiltered with
            ⟨rightMember, rightDecision⟩
          have rightZero : right.eval point = 0 :=
            of_decide_eq_true rightDecision
          have pair := pairSearch left leftMember right rightMember
          have pairFilter :
              [left, right].filter
                  (fun form => decide (form.eval point = 0)) =
                [left, right] := by
            simp [leftZero, rightZero]
          rw [pairFilter] at pair
          rw [List.filter_append, leftActiveEq, rightActiveEq]
          exact pair

theorem activeRadialInteriorForms_length_le_one
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI)
    (point : QI) (denominator : matrix.c * point + matrix.d ≠ 0) :
    (activeRadialInteriorForms kind exponent matrix point).length ≤ 1 := by
  cases kind with
  | initialHigh =>
      apply activePair_length_le_one
      apply normComparisonForms_not_both_zero matrix ((2 : ℚ) ^ exponent)
        ((2 : ℚ) ^ (exponent + 1)) point denominator
      have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
      rw [pow_succ]
      nlinarith
  | initialLow =>
      apply activePair_length_le_one
      apply normComparisonForms_not_both_zero matrix
        (1 / (2 : ℚ) ^ exponent) (2 / (2 : ℚ) ^ exponent) point denominator
      have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
      exact ne_of_lt (div_lt_div_of_pos_right (by norm_num) powerPositive)
  | loop =>
      apply activePair_length_le_one
      apply normComparisonForms_not_both_zero matrix ((2 : ℚ) ^ exponent)
        ((2 : ℚ) ^ (exponent + 1)) point denominator
      have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
      rw [pow_succ]
      nlinarith

/-- Every radial and strict sector face relevant to one completed parser
block, before filtering to the exact active subset. -/
def blockSectorInteriorForms
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) : List HermitianForm :=
  radialInteriorForms kind exponent matrix ++
    sectorInteriorForms sector (normalizedMatrix kind exponent matrix)

def activeBlockSectorInteriorForms
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (point : QI) : List HermitianForm :=
  (blockSectorInteriorForms kind exponent sector matrix).filter fun form =>
    decide (form.eval point = 0)

/-- The actual finite eight-direction table succeeds simultaneously on all
active annulus and strict sector-interior faces of a completed block. -/
theorem tangentDirectionCertificate?_isSome_activeBlockSectorInteriorForms
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (point : QI)
    (determinantNonzero : determinant matrix ≠ 0)
    (denominator : matrix.c * point + matrix.d ≠ 0) :
    (tangentDirectionCertificate?
      (activeBlockSectorInteriorForms kind exponent sector matrix point)
        point).isSome := by
  have normalizedDeterminantNonzero :
      determinant (normalizedMatrix kind exponent matrix) ≠ 0 :=
    FTA.CCLCompleteOwnerShapes.normalizedMatrix_determinant_ne_of kind exponent
      matrix determinantNonzero
  apply tangentDirectionCertificate?_isSome_activeAppend
  · exact tangentDirectionCertificate?_isSome_activeRadialInteriorForms kind
      exponent matrix point determinantNonzero denominator
  · exact tangentDirectionCertificate?_isSome_activeSectorInteriorForms sector
      (normalizedMatrix kind exponent matrix) point
        normalizedDeterminantNonzero (by
          have lowerRow := normalizedMatrix_lowerRow kind exponent matrix
          simpa only [lowerRow.1, lowerRow.2] using denominator)
  · exact activeRadialInteriorForms_length_le_one kind exponent matrix point
      denominator
  · intro radial radialMember radialZero
    exact activeSectorInteriorForms_length_le_one_of_radial_zero kind exponent
      sector matrix point denominator radialMember radialZero
  · intro radial radialMember sectorForm sectorMember
    apply tangentDirectionCertificate?_isSome_activePair_of_angleGap
    · exact radialInteriorForm_gradient_pos kind exponent matrix point
        determinantNonzero radialMember
    · exact sectorInteriorForm_gradient_pos sector
        (normalizedMatrix kind exponent matrix) point
          normalizedDeterminantNonzero sectorMember
    · exact radialInterior_sectorInterior_angleGap_pos kind exponent sector
        matrix determinantNonzero radialMember sectorMember

/-- Executable proof-bearing direction entering every exact active annulus
and strict sector face. -/
def blockSectorInteriorTangentDirection
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (point : QI)
    (determinantNonzero : determinant matrix ≠ 0)
    (denominator : matrix.c * point + matrix.d ≠ 0) :
    TangentDirection
      (activeBlockSectorInteriorForms kind exponent sector matrix point)
        point :=
  (tangentDirectionCertificate?
    (activeBlockSectorInteriorForms kind exponent sector matrix point)
      point).get
        (tangentDirectionCertificate?_isSome_activeBlockSectorInteriorForms
          kind exponent sector matrix point determinantNonzero denominator)

end CCLSectorInteriorCone
end FTA
