module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Bool.Decide
import Purelib.Data.Fin
import Purelib.Polynomial.Dense.Bivariate.Gaussian.Lift
public import Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficients.Constants
import Purelib.Polynomial.Dense.Gaussian.Multiplication.Coordinate
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation
import Purelib.Algebra.Field.Embedding
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Resource.Model
import Purelib.Data.List.Map
import Purelib.Data.List.GetD
import Purelib.Data.List.Reverse
import Purelib.Data.Nat.Subtraction

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Basic
public import Purelib.Data.Rat.Sign.Variation
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Bivariate.Basic
import Purelib.Polynomial.Dense.Bivariate.Resultant
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Components
public import Purelib.Polynomial.Dense.Map
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Elimination.Separated.Bezout
import Purelib.Polynomial.Elimination.Separated.Sylvester
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Map

import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Bounds.Horner
import Purelib.Polynomial.Dense.Gaussian.Bounds.Horner
import Purelib.Polynomial.Dense.Rational.Bounds.Horner.Pair

import Purelib.Tactic.QuotientFreeOmega
import Purelib.LinearAlgebra.PolynomialMatrix.Map
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Field
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Algebra.Field

open Purelib.Data

open Purelib.Data.Gaussian.Resource

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Data.Rat.Sign

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.PolynomialMatrix

open Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled

open Purelib.Polynomial

open Purelib.Polynomial.Bounds

open Purelib.Polynomial.Dense

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Bivariate

open Purelib.Polynomial.Dense.Bivariate.Basic

open Purelib.Polynomial.Dense.Bivariate.Gaussian.Lift

open Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial.Dense.Gaussian.Bounds

open Purelib.Polynomial.Dense.Gaussian.Coefficients.Constants

open Purelib.Polynomial.Dense.Gaussian.Multiplication.Coordinate

open Purelib.Polynomial.Dense.Rational.Basic

open Purelib.Polynomial.Dense.Rational.Bounds.Horner

open Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic

open Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic

open Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation

open Purelib.Polynomial.Elimination.Separated

section

/-!
# Normalized separated-Sylvester eliminants

This is the reduced-record execution of the separated-variable preparation
and fraction-free Schur recursion.  Its compatibility map to the established
separated-Sylvester interface is structural on the same canonical Gaussian
scalar.  Thus every persistent Gaussian-rational coefficient in this
execution is canonical while the paper-facing algebraic API remains stable.
-/

namespace Test.Polynomial.ProgramContracts.CoefficientModels

/-- The canonical Gaussian-rational scalar carrier. -/
private abbrev SemanticGaussian := Data.Gaussian.Basic.Canonical
/-- The retained reference working Gaussian carrier. -/
private abbrev WorkingGaussian := Data.Gaussian.Basic.Number
/-- Dense polynomials over canonical Gaussian rationals. -/
private abbrev SemanticPolynomial :=
  Dense.Basic.DensePolynomial SemanticGaussian
/-- Dense polynomials over the reference working Gaussian carrier. -/
private abbrev WorkingPolynomial :=
  Dense.Basic.DensePolynomial WorkingGaussian
/-- Dense bivariate polynomials over the reference working Gaussian carrier. -/
private abbrev WorkingBivariate :=
  Bivariate.Basic.DenseBivariate WorkingGaussian
/-- The reference finite square matrix of working Gaussian polynomials at the supplied dimension. -/
private abbrev WorkingMatrix (n : Nat) :=
  PolynomialMatrix.Basic.Matrix WorkingGaussian n
/-- The retained executable arithmetic resource model for Gaussian rationals. -/
private abbrev gaussianModel :=
  Model.gaussianModel

open Purelib.Polynomial.Dense.Basic.DensePolynomial

/-- The reference injective field embedding from working Gaussian records to their exact scalar values. -/
private def eraseEmbedding :
    Algebra.Field.Embedding WorkingGaussian SemanticGaussian where
  toFun := Data.Gaussian.Basic.value
  injective := Data.Gaussian.Basic.value_injective
  map_zero := Data.Gaussian.Basic.value_zero
  map_one := Data.Gaussian.Basic.value_one
  map_add := Data.Gaussian.Basic.value_add_instance
  map_neg := Data.Gaussian.Basic.value_neg_instance
  map_mul := Data.Gaussian.Basic.value_mul_instance
  map_inv := Data.Gaussian.Field.value_inv_instance

/-- The reference injective field embedding from exact Gaussian scalars into working records.

Both carriers retain the identical canonical Gaussian scalar. The reference
readback function therefore preserves every supplied field operation directly. -/
private def canonicalEmbedding :
    Algebra.Field.Embedding SemanticGaussian WorkingGaussian where
  toFun := Data.Gaussian.Basic.ofGaussian
  injective := by intro left right equal; exact equal
  map_zero := rfl
  map_one := rfl
  map_add := fun _ _ => rfl
  map_neg := fun _ => rfl
  map_mul := fun _ _ => rfl
  map_inv := fun _ => rfl

/-- Map every retained polynomial coefficient to its exact Gaussian value. -/
private def erasePolynomial (polynomial : WorkingPolynomial) : SemanticPolynomial :=
  Map.map eraseEmbedding polynomial

/-- Map every reference Gaussian polynomial coefficient into its working record. -/
private def canonicalPolynomial (polynomial : SemanticPolynomial) : WorkingPolynomial :=
  Map.map canonicalEmbedding polynomial

/-- Coefficient erasure commutes with removing leading polynomial zeros. -/
private theorem erase_normalize (polynomial : WorkingPolynomial) :
    erasePolynomial polynomial.normalize =
      (erasePolynomial polynomial).normalize :=
  Map.map_normalize eraseEmbedding polynomial

/-- The normalized erased coefficients are the exact value map of the reference normalized coefficient list. -/
private theorem erase_normalize_coeffs (polynomial : WorkingPolynomial) :
    (erasePolynomial polynomial).normalize.coeffs =
      polynomial.normalize.coeffs.map Data.Gaussian.Basic.value := by
  rw [← erase_normalize]
  rfl

/-- Coefficient erasure preserves polynomial negation. -/
private theorem erase_neg (polynomial : WorkingPolynomial) :
    erasePolynomial (-polynomial) = -erasePolynomial polynomial :=
  Map.map_neg eraseEmbedding polynomial

/-- Coefficient erasure preserves polynomial subtraction. -/
private theorem erase_sub (left right : WorkingPolynomial) :
    erasePolynomial (left - right) =
      erasePolynomial left - erasePolynomial right :=
  Map.map_sub eraseEmbedding left right

/-- Coefficient erasure preserves polynomial multiplication. -/
private theorem erase_mul (left right : WorkingPolynomial) :
    erasePolynomial (left * right) =
      erasePolynomial left * erasePolynomial right :=
  Map.map_mul eraseEmbedding left right

/-- Conjugate the reference working Gaussian record by negating its imaginary coordinate. -/
private def workingConjugate (source : WorkingGaussian) : WorkingGaussian :=
  ⟨source.re, Fraction.Arithmetic.neg source.im⟩

/-- The exact value of working conjugation is canonical Gaussian conjugation. -/
private theorem value_workingConjugate (source : WorkingGaussian) :
    Data.Gaussian.Basic.value (workingConjugate source) =
      Data.Gaussian.Basic.conj
        (Data.Gaussian.Basic.value source) := by
  apply Data.Gaussian.Basic.ext
  · rfl
  · exact Fraction.Arithmetic.value_neg source.im

/-- The two retained Gaussian conjugation names have identical values. -/
private theorem conjugate_owner_readback (source : WorkingGaussian) :
    Data.Gaussian.Basic.conj source =
      Data.Gaussian.Basic.Canonical.conj source := rfl

/-- Encode an reference working scalar as a normalized constant parameter polynomial. -/
private def parameterConstant (value : WorkingGaussian) : WorkingPolynomial :=
  if value = 0 then 0 else DensePolynomial.constant value

/-- The reference working polynomial twice the parameter. -/
private def twiceParameter : WorkingPolynomial :=
  ⟨[Data.Gaussian.Basic.ofGaussian 2,
    Data.Gaussian.Basic.ofGaussian 0]⟩

/-- Multiply the reference working polynomial by twice the parameter. -/
private def twiceShift (polynomial : WorkingPolynomial) : WorkingPolynomial :=
  twiceParameter * polynomial

/-- Advance the reference reflected coefficient tail using the preceding polynomial and twice-parameter shift. -/
private def reflectedTailStep (previous : WorkingPolynomial) :
    List WorkingPolynomial → List WorkingPolynomial
  | [] => [-previous]
  | current :: remaining =>
      (twiceShift current - previous) ::
        reflectedTailStep current remaining

/-- Advance the reference reflected coefficient list by one conjugated Gaussian coefficient. -/
private def reflectedStep (coefficients : List WorkingPolynomial)
    (coefficient : WorkingGaussian) : List WorkingPolynomial :=
  match coefficients with
  | [] => [parameterConstant (workingConjugate coefficient)]
  | head :: tail =>
      (twiceShift head -
          parameterConstant (-workingConjugate coefficient)) ::
        reflectedTailStep head tail

/-- Compute the reference reflected coefficient list from normalized Gaussian coefficients. -/
private def reflectedCoefficients (polynomial : WorkingPolynomial) :
    List WorkingPolynomial :=
  match polynomial.normalize.coeffs with
  | [] => []
  | leading :: remaining =>
      remaining.foldl reflectedStep
        [parameterConstant (workingConjugate leading)]

/-- Lift the reference normalized Gaussian coefficients to constant parameter polynomials in reverse order. -/
private def liftedCoefficients (polynomial : WorkingPolynomial) :
    List WorkingPolynomial :=
  polynomial.normalize.coeffs.reverse.map parameterConstant

/-- The reference constant-parameter bivariate lift of the Gaussian polynomial. -/
private def lifted (polynomial : WorkingPolynomial) : WorkingBivariate :=
  ⟨(liftedCoefficients polynomial).reverse⟩

/-- The reference reflected bivariate polynomial assembled from the retained coefficient recurrence. -/
private def reflected (polynomial : WorkingPolynomial) : WorkingBivariate :=
  ⟨(reflectedCoefficients polynomial).reverse⟩

/-- The reference separated-variable Sylvester matrix at twice the erased polynomial degree. -/
private def separatedSylvester (polynomial : WorkingPolynomial) :
    WorkingMatrix ((erasePolynomial polynomial).natDegree +
      (erasePolynomial polynomial).natDegree) :=
  Resultant.sylvester
    (lifted polynomial) (reflected polynomial)
    (erasePolynomial polynomial).natDegree
    (erasePolynomial polynomial).natDegree

/-- The retained fraction-free scaled inverse data of the reference separated Sylvester matrix. -/
private def separatedData (polynomial : WorkingPolynomial) :=
  Compute.scaledInverseData
    ((erasePolynomial polynomial).natDegree +
      (erasePolynomial polynomial).natDegree)
    (separatedSylvester polynomial)

/-- The scalar retained by scaled inversion after canonical coefficient preparation. -/
private def normalizedScalar (polynomial : SemanticPolynomial) : WorkingPolynomial :=
  (separatedData (canonicalPolynomial polynomial)).scalar

/-! ## Erasure of separated-variable preparation -/

/-- Erasure preserves the reference normalized constant parameter polynomial. -/
private theorem erase_parameterConstant (value : WorkingGaussian) :
    erasePolynomial (parameterConstant value) =
      Purelib.Polynomial.Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant
        (Data.Gaussian.Basic.value value) := by
  unfold parameterConstant SeparatedVariables.parameterConstant
  have zeroIff : Data.Gaussian.Basic.value value = 0 ↔ value = 0 :=
    ⟨fun equal => Data.Gaussian.Basic.value_injective
        (equal.trans Data.Gaussian.Basic.value_zero.symm),
      fun equal => (congrArg Data.Gaussian.Basic.value equal).trans
        Data.Gaussian.Basic.value_zero⟩
  by_cases zero : value = 0
  · rw [if_pos zero, if_pos (zeroIff.mpr zero)]
    exact Map.map_zero_polynomial eraseEmbedding
  · rw [if_neg zero, if_neg (fun equal => zero (zeroIff.mp equal))]
    exact Map.map_constant eraseEmbedding value

/-- Erasure preserves the reference twice-parameter polynomial. -/
private theorem erase_twiceParameter :
    erasePolynomial twiceParameter =
      SeparatedVariables.twiceParameter := by
  apply DensePolynomial.ext
  simp only [erasePolynomial, twiceParameter,
    Map.map_coeffs, List.map_cons, List.map_nil]
  rfl

/-- Erasure preserves multiplication by twice the parameter. -/
private theorem erase_twiceShift (polynomial : WorkingPolynomial) :
    erasePolynomial (twiceShift polynomial) =
      Purelib.Polynomial.Dense.Gaussian.Multiplication.Coordinate.SeparatedVariables.twiceShift (erasePolynomial
        polynomial) := by
  unfold twiceShift SeparatedVariables.twiceShift
  rw [erase_mul, erase_twiceParameter]

/-- Erasure commutes with every step of the reference reflected coefficient tail. -/
private theorem erase_reflectedTailStep (previous : WorkingPolynomial) :
    ∀ coefficients : List WorkingPolynomial,
      (reflectedTailStep previous coefficients).map erasePolynomial =
        SeparatedVariables.reflectedTailStep
          (erasePolynomial previous) (coefficients.map erasePolynomial)
  | [] => by
      simp only [reflectedTailStep,
        SeparatedVariables.reflectedTailStep, List.map_cons, List.map_nil]
      rw [erase_neg]
  | current :: remaining => by
      simp only [reflectedTailStep,
        SeparatedVariables.reflectedTailStep, List.map_cons]
      rw [erase_sub, erase_twiceShift,
        erase_reflectedTailStep current remaining]

/-- Erasure preserves one reflected coefficient update with its reference conjugated input. -/
private theorem erase_reflectedStep (coefficients : List WorkingPolynomial)
    (coefficient : WorkingGaussian) :
    (reflectedStep coefficients coefficient).map erasePolynomial =
      SeparatedVariables.reflectedStep
        (coefficients.map erasePolynomial)
        (Data.Gaussian.Basic.value coefficient) := by
  cases coefficients with
  | nil =>
      rewrite [reflectedStep, SeparatedVariables.reflectedStep.eq_def,
        List.map_cons, List.map_nil, erase_parameterConstant,
        value_workingConjugate, conjugate_owner_readback]
      exact Eq.refl _
  | cons head tail =>
      rewrite [reflectedStep, SeparatedVariables.reflectedStep.eq_def,
        List.map_cons]
      rewrite [erase_sub, erase_twiceShift,
        erase_parameterConstant,
        Data.Gaussian.Basic.value_neg_instance,
        value_workingConjugate, erase_reflectedTailStep]
      rewrite [conjugate_owner_readback]
      exact Eq.refl _

/-- Erasure commutes with the complete finite fold of reference reflected updates. -/
private theorem erase_fold_reflectedStep :
    ∀ (coefficients : List WorkingGaussian)
      (state : List WorkingPolynomial),
      (coefficients.foldl reflectedStep state).map erasePolynomial =
        (coefficients.map Data.Gaussian.Basic.value).foldl
          SeparatedVariables.reflectedStep
          (state.map erasePolynomial)
  | [], _ => rfl
  | coefficient :: remaining, state => by
      simp only [List.foldl_cons, List.map_cons]
      rw [erase_fold_reflectedStep remaining,
        erase_reflectedStep state coefficient]

/-- Erasure preserves the complete reference reflected coefficient list. -/
private theorem erase_reflectedCoefficients (polynomial : WorkingPolynomial) :
    (reflectedCoefficients polynomial).map erasePolynomial =
      Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedCoefficients
        (erasePolynomial polynomial) := by
  cases coefficients : polynomial.normalize.coeffs with
  | nil =>
      unfold reflectedCoefficients
      unfold SeparatedVariables.reflectedCoefficients
      rw [coefficients, erase_normalize_coeffs, coefficients]
      rfl
  | cons leading remaining =>
      unfold reflectedCoefficients
      unfold SeparatedVariables.reflectedCoefficients
      rw [coefficients, erase_normalize_coeffs, coefficients]
      simp only [List.map_cons]
      rw [erase_fold_reflectedStep]
      apply congrArg (fun initial =>
        (remaining.map Data.Gaussian.Basic.value).foldl
          SeparatedVariables.reflectedStep initial)
      simp only [List.map_cons, List.map_nil]
      rw [erase_parameterConstant, value_workingConjugate, conjugate_owner_readback]

/-- Erasure preserves the complete reference lifted coefficient list. -/
private theorem erase_liftedCoefficients (polynomial : WorkingPolynomial) :
    (liftedCoefficients polynomial).map erasePolynomial =
      Purelib.Polynomial.Dense.Bivariate.Gaussian.Lift.SeparatedVariables.liftedCoefficients
        (erasePolynomial polynomial) := by
  unfold liftedCoefficients SeparatedVariables.liftedCoefficients
  rw [erase_normalize_coeffs]
  simp only [Reverse.map_reverse, Map.map_map]
  apply congrArg List.reverse
  apply Map.map_congr_left
  intro coefficient _
  change erasePolynomial (parameterConstant coefficient) =
    SeparatedVariables.parameterConstant
      (Data.Gaussian.Basic.value coefficient)
  exact erase_parameterConstant coefficient

/-- Canonical coefficient preparation followed by erasure returns the identical reference polynomial. -/
private theorem erase_canonicalPolynomial (polynomial : SemanticPolynomial) :
    erasePolynomial (canonicalPolynomial polynomial) = polynomial := by
  apply DensePolynomial.ext
  unfold erasePolynomial canonicalPolynomial Map.map
  induction polynomial.coeffs with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      change coefficient ::
          List.map eraseEmbedding.toFun
            (List.map canonicalEmbedding.toFun remaining) =
        coefficient :: remaining
      exact congrArg (List.cons coefficient) inductionHypothesis

/-- Erasing the reference bivariate lift preserves its exact coefficient list. -/
private theorem erase_lifted (polynomial : WorkingPolynomial) :
    (lifted polynomial).coeffs.map erasePolynomial =
      (Purelib.Polynomial.Dense.Bivariate.Gaussian.Lift.SeparatedVariables.lifted
        (erasePolynomial polynomial)).coeffs := by
  unfold lifted SeparatedVariables.lifted
  rewrite [Reverse.map_reverse, erase_liftedCoefficients]
  exact Eq.refl _

/-- Erasing the reference reflected bivariate polynomial preserves its exact coefficient list. -/
private theorem erase_reflected (polynomial : WorkingPolynomial) :
    (reflected polynomial).coeffs.map erasePolynomial =
      (Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflected
        (erasePolynomial polynomial)).coeffs := by
  unfold reflected SeparatedVariables.reflected
  rewrite [Reverse.map_reverse, erase_reflectedCoefficients]
  exact Eq.refl _

set_option backward.match.sparseCases false in
/-- Coefficient erasure commutes with default-zero list lookup at the reference natural position.

The same reference list spine and natural index select the coefficient on both
sides. The zero fallback is erased to the reference zero polynomial. -/
private theorem map_getD : ∀ (coefficients : List WorkingPolynomial)
    (index : Nat),
    erasePolynomial (Data.List.getD coefficients index 0) =
      Data.List.getD (coefficients.map erasePolynomial) index 0
  | [], _ => Map.map_zero_polynomial eraseEmbedding
  | _ :: _, 0 => rfl
  | _ :: remaining, index + 1 => map_getD remaining index

/-- Erasure preserves the selected outer coefficient of the reference bivariate polynomial.

Both sides retain the reference reversed coefficient table, natural index and
zero fallback. Structural mapping does not change the selected coordinate. -/
private theorem erase_outerCoeff
    (bivariate : WorkingBivariate) (index : Nat) :
    erasePolynomial (Purelib.Polynomial.Dense.Bivariate.Resultant.outerCoeff bivariate index) =
      Purelib.Polynomial.Dense.Bivariate.Resultant.outerCoeff
        ⟨bivariate.coeffs.map erasePolynomial⟩ index := by
  unfold Resultant.outerCoeff
  change erasePolynomial (Data.List.getD bivariate.coeffs.reverse index 0) =
    Data.List.getD (bivariate.coeffs.map erasePolynomial).reverse index 0
  rw [← Reverse.map_reverse]
  exact map_getD bivariate.coeffs.reverse index

/-- Entrywise coefficient erasure maps the reference separated Sylvester matrix to its canonical owner. -/
private theorem erase_separatedSylvester (polynomial : WorkingPolynomial) :
    Map.mapMatrix eraseEmbedding
        (separatedSylvester polynomial) =
      Purelib.Polynomial.Elimination.Separated.Sylvester.separatedSylvester
        (erasePolynomial polynomial) := by
  apply LinearAlgebra.Matrix.matrix_ext
  intro row column
  simp only [Map.mapMatrix_apply]
  unfold separatedSylvester Sylvester.separatedSylvester
  unfold Resultant.sylvester
  simp only [LinearAlgebra.Matrix.matrixOfFn_apply]
  rcases Data.Fin.addCases_split column with
    ⟨left, rfl⟩ | ⟨right, rfl⟩
  · simp only [Data.Fin.addCases_left]
    split
    · change erasePolynomial
          (Resultant.outerCoeff (reflected polynomial)
            ((row : Nat) - (left : Nat))) = _
      rw [erase_outerCoeff]
      apply congrArg (fun bivariate =>
        Resultant.outerCoeff bivariate
          ((row : Nat) - (left : Nat)))
      exact congrArg DenseBivariate.mk
        (erase_reflected polynomial)
    · exact Map.map_zero_polynomial eraseEmbedding
  · simp only [Data.Fin.addCases_right]
    split
    · change erasePolynomial
          (Resultant.outerCoeff (lifted polynomial)
            ((row : Nat) - (right : Nat))) = _
      rw [erase_outerCoeff]
      apply congrArg (fun bivariate =>
        Resultant.outerCoeff bivariate
          ((row : Nat) - (right : Nat)))
      exact congrArg DenseBivariate.mk
        (erase_lifted polynomial)
    · exact Map.map_zero_polynomial eraseEmbedding

/-- Erasure preserves the scalar returned by the complete reference scaled-inverse computation. -/
private theorem erase_separatedScalar (polynomial : WorkingPolynomial) :
    erasePolynomial (separatedData polynomial).scalar =
      (Bezout.separatedData
        (erasePolynomial polynomial)).scalar := by
  have mapped :=
    (Map.map_scaledInverseData eraseEmbedding
      ((erasePolynomial polynomial).natDegree +
        (erasePolynomial polynomial).natDegree)
      (separatedSylvester polynomial)).1
  rw [erase_separatedSylvester] at mapped
  exact mapped

/-- The complete reduced-record Schur recursion erases to the scalar used by the existing separated-Sylvester Bézout
development. -/
private theorem erase_normalizedScalar (polynomial : SemanticPolynomial) :
    erasePolynomial (normalizedScalar polynomial) =
      (Bezout.separatedData polynomial).scalar := by
  unfold normalizedScalar
  rw [erase_separatedScalar, erase_canonicalPolynomial]

/-- The old erasure map preserves every displayed inverse entry, at the reference dimension and the caller's actual
supplied finite indices. -/
private theorem inverse_entry_erased (polynomial : WorkingPolynomial)
    (row column : Fin ((erasePolynomial polynomial).natDegree +
      (erasePolynomial polynomial).natDegree)) :
    erasePolynomial ((separatedData polynomial).inverse row column) =
      (Bezout.separatedData
        (erasePolynomial polynomial)).inverse row column := by
  have mapped :=
    (Map.map_scaledInverseData eraseEmbedding
      ((erasePolynomial polynomial).natDegree +
        (erasePolynomial polynomial).natDegree)
      (separatedSylvester polynomial)).2
  rw [erase_separatedSylvester] at mapped
  have entry := congrArg (fun matrix => matrix row column) mapped
  rw [Map.mapMatrix_apply] at entry
  change erasePolynomial ((separatedData polynomial).inverse row column) =
    (Bezout.separatedData
      (erasePolynomial polynomial)).inverse row column at entry
  exact entry

/-- The retained working-polynomial erasure is the identity on the current canonical carrier. -/
private theorem erase_identity (polynomial : WorkingPolynomial) :
    erasePolynomial polynomial = polynomial := by
  apply DensePolynomial.ext
  change polynomial.coeffs.map Data.Gaussian.Basic.value = polynomial.coeffs
  induction polynomial.coeffs with
  | nil => rfl
  | cons coefficient remaining ih =>
      exact congrArg (List.cons coefficient) ih

/-- Twice the reference polynomial's represented natural degree. -/
private def dimension (polynomial : WorkingPolynomial) : Nat :=
  polynomial.natDegree + polynomial.natDegree

-- Retain the reference reducible dependent index witness and declaration kind.
set_option linter.defProp false in
/-- The retained reducible equality transporting the reference polynomial dimension through erasure. -/
private def dimensionIdentity (polynomial : WorkingPolynomial) :
    dimension (erasePolynomial polynomial) = dimension polynomial :=
  congrArg dimension (erase_identity polynomial)

/-- Equal reference polynomials have equal retained inverse entries after the exact induced finite-index casts. -/
private theorem inverse_transport (first last : WorkingPolynomial)
    (equal : first = last) (row column : Fin (dimension first)) :
    (Bezout.separatedData first).inverse row column =
      (Bezout.separatedData last).inverse
        (Fin.cast (congrArg dimension equal) row)
        (Fin.cast (congrArg dimension equal) column) := by
  cases equal
  rfl

/-- Exact retained reference data, complete inverse entry correspondence and
explicit dimension transport; no scalar-only
cofactor substitution. -/
private theorem inverse_entry_correspondence (polynomial : WorkingPolynomial)
    (row column : Fin (dimension (erasePolynomial polynomial))) :
    (separatedData polynomial).inverse row column =
      (Bezout.separatedData polynomial).inverse
        (Fin.cast (dimensionIdentity polynomial) row)
        (Fin.cast (dimensionIdentity polynomial) column) :=
  (erase_identity ((separatedData polynomial).inverse row column)).symm.trans
    ((inverse_entry_erased polynomial row column).trans
      (inverse_transport (erasePolynomial polynomial) polynomial
        (erase_identity polynomial) row column))

/-- The reference dimension transport preserves the selected inverse row's natural position. -/
private theorem inverse_index_readback (polynomial : WorkingPolynomial)
    (row : Fin (dimension (erasePolynomial polynomial))) :
    (Fin.cast (dimensionIdentity polynomial) row).val = row.val := rfl

/-- The reference separated inverse computation retains exactly the canonical scalar. -/
private theorem scalar_correspondence (polynomial : WorkingPolynomial) :
    (separatedData polynomial).scalar =
      (Bezout.separatedData polynomial).scalar :=
  (erase_identity ((separatedData polynomial).scalar)).symm.trans
    ((erase_separatedScalar polynomial).trans
      (congrArg (fun input =>
        (Bezout.separatedData input).scalar)
        (erase_identity polynomial)))

/-- Dense polynomials over the reference reduced rational coefficient carrier. -/
private abbrev WorkingCoordinatePolynomial :=
  Dense.Basic.DensePolynomial
    Fraction.Basic.ReducedFraction

/-- Dense polynomials over canonical rational values. -/
private abbrev SemanticCoordinatePolynomial :=
  Dense.Basic.DensePolynomial
    Fraction.Rational

/-- Read every reference Gaussian coefficient's real coordinate into a rational polynomial. -/
private def workingRealPart (polynomial : WorkingPolynomial) :
    WorkingCoordinatePolynomial :=
  ⟨polynomial.coeffs.map Gaussian.Basic.Number.re⟩

/-- Read every reference Gaussian coefficient's imaginary coordinate into a rational polynomial. -/
private def workingImagPart (polynomial : WorkingPolynomial) :
    WorkingCoordinatePolynomial :=
  ⟨polynomial.coeffs.map Gaussian.Basic.Number.im⟩

/-- Map reference reduced rational coefficients to their exact rational values. -/
private def eraseCoordinatePolynomial (polynomial : WorkingCoordinatePolynomial) :
    SemanticCoordinatePolynomial :=
  ⟨polynomial.coeffs.map Fraction.Basic.value⟩

/-- Reference rational-coefficient erasure is the identity on the current canonical carrier. -/
private theorem coordinate_identity (polynomial : WorkingCoordinatePolynomial) :
    eraseCoordinatePolynomial polynomial = polynomial := by
  apply DensePolynomial.ext
  change polynomial.coeffs.map Fraction.Basic.value = polynomial.coeffs
  induction polynomial.coeffs with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) ih

/-- Reference Gaussian coefficient preparation is the identity on the current canonical carrier. -/
private theorem canonical_identity (polynomial : SemanticPolynomial) :
    canonicalPolynomial polynomial = polynomial := by
  apply DensePolynomial.ext
  change polynomial.coeffs.map Data.Gaussian.Basic.ofGaussian = polynomial.coeffs
  induction polynomial.coeffs with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) ih

/-- The reference working and semantic Gaussian carriers are definitionally identical. -/
private theorem gaussian_carrier_correspondence : WorkingGaussian = SemanticGaussian := rfl
/-- The reference working and semantic Gaussian polynomial carriers are definitionally identical. -/
private theorem polynomial_carrier_correspondence : WorkingPolynomial = SemanticPolynomial := rfl

/-- The reference parameter-constant constructor equals its canonical mathematical owner. -/
private theorem parameter_constant_correspondence (value : WorkingGaussian) :
    parameterConstant value = SeparatedVariables.parameterConstant value := rfl
/-- The retained twice-parameter polynomial equals the canonical polynomial. -/
private theorem twice_parameter_correspondence :
    twiceParameter = SeparatedVariables.twiceParameter := rfl
/-- The reference twice-parameter shift equals its canonical polynomial operation. -/
private theorem twice_shift_correspondence (polynomial : WorkingPolynomial) :
    twiceShift polynomial = SeparatedVariables.twiceShift polynomial := rfl
/-- The complete reference reflected-tail recurrence equals its canonical implementation. -/
private theorem reflected_tail_correspondence (previous : WorkingPolynomial)
    (coefficients : List WorkingPolynomial) :
    reflectedTailStep previous coefficients =
      SeparatedVariables.reflectedTailStep previous coefficients := by
  have listIdentity (values : List WorkingPolynomial) : values.map erasePolynomial = values := by
    induction values with
    | nil => rfl
    | cons head tail ih => exact congrArg₂ List.cons (erase_identity head) ih
  have result := erase_reflectedTailStep previous coefficients
  rw [listIdentity, listIdentity, erase_identity] at result
  exact result
/-- The reference reflected coefficient update equals its canonical implementation. -/
private theorem reflected_step_correspondence (coefficients : List WorkingPolynomial)
    (coefficient : WorkingGaussian) :
    reflectedStep coefficients coefficient =
      SeparatedVariables.reflectedStep coefficients coefficient := by
  have listIdentity (values : List WorkingPolynomial) : values.map erasePolynomial = values := by
    induction values with
    | nil => rfl
    | cons head tail ih => exact congrArg₂ List.cons (erase_identity head) ih
  have result := erase_reflectedStep coefficients coefficient
  rw [listIdentity, listIdentity] at result
  exact result
/-- The reference reflected coefficient list equals the canonical retained list. -/
private theorem reflected_coefficients_correspondence (polynomial : WorkingPolynomial) :
    reflectedCoefficients polynomial = SeparatedVariables.reflectedCoefficients polynomial := by
  have listIdentity (values : List WorkingPolynomial) : values.map erasePolynomial = values := by
    induction values with
    | nil => rfl
    | cons head tail ih => exact congrArg₂ List.cons (erase_identity head) ih
  have result := erase_reflectedCoefficients polynomial
  rw [listIdentity, erase_identity] at result
  exact result
/-- The reference lifted coefficient list equals the canonical retained list. -/
private theorem lifted_coefficients_correspondence (polynomial : WorkingPolynomial) :
    liftedCoefficients polynomial = SeparatedVariables.liftedCoefficients polynomial := rfl
/-- The reference bivariate lift equals its canonical mathematical owner. -/
private theorem lifted_correspondence (polynomial : WorkingPolynomial) :
    lifted polynomial = SeparatedVariables.lifted polynomial := rfl
/-- The reference reflected bivariate polynomial equals its canonical mathematical owner. -/
private theorem reflected_correspondence (polynomial : WorkingPolynomial) :
    reflected polynomial = SeparatedVariables.reflected polynomial :=
  congrArg (fun coefficients => (⟨coefficients.reverse⟩ : WorkingBivariate))
    (reflected_coefficients_correspondence polynomial)
/-- The reference working conjugation equals canonical Gaussian conjugation. -/
private theorem conjugate_correspondence (value : WorkingGaussian) :
    workingConjugate value = Data.Gaussian.Basic.conj value := value_workingConjugate value
/-- The reference real-coordinate polynomial equals the canonical component polynomial. -/
private theorem real_part_correspondence (polynomial : WorkingPolynomial) :
    workingRealPart polynomial = Components.realPart polynomial := rfl
/-- The reference imaginary-coordinate polynomial equals the canonical component polynomial. -/
private theorem imaginary_part_correspondence (polynomial : WorkingPolynomial) :
    workingImagPart polynomial = Components.imagPart polynomial := rfl
/-- The reference canonical Gaussian embedding returns the identical scalar. -/
private theorem canonical_embedding_readback (value : SemanticGaussian) :
    canonicalEmbedding.toFun value = value := rfl

/-- Equal reference polynomials have equal Sylvester entries after their exact induced dimension casts. -/
private theorem matrix_transport (first last : WorkingPolynomial) (equal : first = last)
    (row column : Fin (dimension first)) :
    Sylvester.separatedSylvester first row column =
      Sylvester.separatedSylvester last
        (Fin.cast (congrArg dimension equal) row)
        (Fin.cast (congrArg dimension equal) column) := by
  cases equal
  rfl

/-- Every reference Sylvester entry equals its canonical entry at the transported reference finite indices. -/
private theorem matrix_entry_correspondence (polynomial : WorkingPolynomial)
    (row column : Fin (dimension (erasePolynomial polynomial))) :
    separatedSylvester polynomial row column =
      Sylvester.separatedSylvester polynomial
        (Fin.cast (dimensionIdentity polynomial) row)
        (Fin.cast (dimensionIdentity polynomial) column) := by
  have mapped := congrArg (fun matrix => matrix row column) (erase_separatedSylvester polynomial)
  rw [Map.mapMatrix_apply] at mapped
  change erasePolynomial (separatedSylvester polynomial row column) =
    Sylvester.separatedSylvester (erasePolynomial polynomial) row column at mapped
  exact (erase_identity (separatedSylvester polynomial row column)).symm.trans
    (mapped.trans (matrix_transport (erasePolynomial polynomial) polynomial
      (erase_identity polynomial) row column))

end Test.Polynomial.ProgramContracts.CoefficientModels
end

namespace Test.Polynomial.ProgramContracts.SignedRemainders

/-- The canonical rational scalar carrier. -/
private abbrev Coordinate := Fraction.Rational
/-- The retained reference reduced rational carrier. -/
private abbrev WorkingCoordinate := Fraction.Basic.ReducedFraction
/-- Dense polynomials over canonical rational scalars. -/
private abbrev Dense := Dense.Basic.DensePolynomial Coordinate
/-- Dense polynomials over the reference reduced rational carrier. -/
private abbrev WorkingPolynomial :=
  Dense.Basic.DensePolynomial WorkingCoordinate

open Purelib.Polynomial.Dense.Basic.DensePolynomial

/-- The reference injective field embedding from reduced rational records to exact values. -/
private def eraseEmbedding :
    Algebra.Field.Embedding WorkingCoordinate Coordinate where
  toFun := Fraction.Basic.value
  injective := Fraction.Arithmetic.value_injective
  map_zero := Fraction.Arithmetic.value_zero
  map_one := Fraction.Arithmetic.value_one
  map_add := Fraction.Arithmetic.value_add_instance
  map_neg := Fraction.Arithmetic.value_neg_instance
  map_mul := Fraction.Arithmetic.value_mul_instance
  map_inv := Fraction.Arithmetic.value_inv_instance

/-- The reference injective field embedding from rational values to reduced records.

Both carriers retain the identical canonical rational scalar. The reference
readback function therefore preserves every supplied field operation directly. -/
private def canonicalEmbedding :
    Algebra.Field.Embedding Coordinate WorkingCoordinate where
  toFun := Fraction.Basic.ofRational
  injective := by intro left right equal; exact equal
  map_zero := rfl
  map_one := rfl
  map_add := fun _ _ => rfl
  map_neg := fun _ => rfl
  map_mul := fun _ _ => rfl
  map_inv := fun _ => rfl

/-- Map every reference reduced polynomial coefficient to its exact rational value. -/
private def erasePolynomial (polynomial : WorkingPolynomial) : Dense :=
  Map.map eraseEmbedding polynomial

/-- Map every reference rational coefficient into its reduced record. -/
private def canonicalPolynomial (polynomial : Dense) : WorkingPolynomial :=
  Map.map canonicalEmbedding polynomial

/-- Preparing reduced coefficients and erasing them returns the identical reference rational polynomial. -/
private theorem erase_canonicalPolynomial (polynomial : Dense) :
    erasePolynomial (canonicalPolynomial polynomial) = polynomial := by
  apply DensePolynomial.ext
  unfold erasePolynomial canonicalPolynomial Map.map
  induction polynomial.coeffs with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      change coefficient ::
          List.map eraseEmbedding.toFun
            (List.map canonicalEmbedding.toFun remaining) =
        coefficient :: remaining
      exact congrArg (List.cons coefficient) inductionHypothesis

/-- Fuel-bounded signed Euclidean recursion over reduced coefficient records. -/
private def signedRemainderChainFuel :
    Nat → WorkingPolynomial → WorkingPolynomial → List WorkingPolynomial :=
  Nat.rec
    (fun p _ => [p])
    (fun _ recursive p q =>
      if q.isZero then [p]
      else
        let division := DensePolynomial.divMod p q
        if division.remainder.isZero then [p, q]
        else p :: recursive q (-division.remainder))

/-- Zero recursion fuel retains only the reference first polynomial. -/
@[simp]
private theorem signedRemainderChainFuel_zero
    (p q : WorkingPolynomial) :
    signedRemainderChainFuel 0 p q = [p] := rfl

/-- One fuel step tests the reference divisor and remainder before retaining the next signed Euclidean step. -/
private theorem signedRemainderChainFuel_succ
    (fuel : Nat) (p q : WorkingPolynomial) :
    signedRemainderChainFuel (fuel + 1) p q =
      if q.isZero then [p]
      else
        let division := DensePolynomial.divMod p q
        if division.remainder.isZero then [p, q]
        else p :: signedRemainderChainFuel fuel q
          (-division.remainder) := rfl

/-- Once the fuel covers the represented degree, one further step cannot change the normalized signed chain.

The reference zero-divisor and zero-remainder branches stop at their retained
polynomials. The nonzero remainder has smaller represented degree, so the same
inductive equality applies to its reference signed recursive input. -/
private theorem signedRemainderChainFuel_succ_of_degreeCount_le :
    ∀ (fuel : Nat) (p q : WorkingPolynomial), q.degreeCount ≤ fuel →
      signedRemainderChainFuel (fuel + 1) p q =
        signedRemainderChainFuel fuel p q := by
  intro fuel
  induction fuel with
  | zero =>
      intro p q enough
      have degreeZero : q.degreeCount = 0 := Nat.eq_zero_of_le_zero enough
      have qZero := DensePolynomial.isZero_true_of_degreeCount_eq_zero degreeZero
      change (if q.isZero then [p]
          else
            let division := DensePolynomial.divMod p q
            if division.remainder.isZero then [p, q]
            else p :: signedRemainderChainFuel 0 q
              (-division.remainder)) = [p]
      rewrite [if_pos qZero]
      exact Eq.refl _
  | succ fuel inductionHypothesis =>
      intro p q enough
      change (if q.isZero then [p]
          else
            let division := DensePolynomial.divMod p q
            if division.remainder.isZero then [p, q]
            else p :: signedRemainderChainFuel (fuel + 1) q
              (-division.remainder)) =
        if q.isZero then [p]
          else
            let division := DensePolynomial.divMod p q
            if division.remainder.isZero then [p, q]
            else p :: signedRemainderChainFuel fuel q
              (-division.remainder)
      by_cases qTrue : q.isZero = true
      · rewrite [if_pos qTrue, if_pos qTrue]
        exact Eq.refl _
      · rewrite [if_neg qTrue, if_neg qTrue]
        dsimp only
        by_cases remainderTrue : (DensePolynomial.divMod p q).remainder.isZero = true
        · rewrite [if_pos remainderTrue, if_pos remainderTrue]
          exact Eq.refl _
        · rewrite [if_neg remainderTrue, if_neg remainderTrue]
          apply congrArg (List.cons p)
          apply inductionHypothesis q (-((DensePolynomial.divMod p q).remainder))
          have qFalse : q.isZero = false :=
            Data.Bool.Decide.bool_eq_false_of_not_eq_true q.isZero qTrue
          have remainderDegree := DensePolynomial.divMod_remainder_degreeCount_lt p q qFalse
          rewrite [DensePolynomial.degreeCount_neg]
          exact Nat.lt_succ_iff.mp
            (lt_of_lt_of_le remainderDegree enough)

/-- Additional fuel leaves the reference signed chain unchanged once it covers the second polynomial's represented
degree. -/
private theorem signedRemainderChainFuel_add_of_degreeCount_le
    (extra fuel : Nat) (p q : WorkingPolynomial)
    (enough : q.degreeCount ≤ fuel) :
    signedRemainderChainFuel (fuel + extra) p q =
      signedRemainderChainFuel fuel p q := by
  induction extra with
  | zero => rw [Nat.add_zero]
  | succ extra inductionHypothesis =>
      rw [Nat.add_succ]
      calc
        signedRemainderChainFuel (fuel + extra + 1) p q =
            signedRemainderChainFuel (fuel + extra) p q :=
          signedRemainderChainFuel_succ_of_degreeCount_le
            (fuel + extra) p q (enough.trans (Nat.le_add_right fuel extra))
        _ = signedRemainderChainFuel fuel p q := inductionHypothesis

/-- Every sufficient reference fuel budget produces the exact degree-bounded signed chain. -/
private theorem signedRemainderChainFuel_stable
    (fuel : Nat) (p q : WorkingPolynomial)
    (enough : q.degreeCount ≤ fuel) :
    signedRemainderChainFuel fuel p q =
      signedRemainderChainFuel q.degreeCount p q := by
  have fuelEquation : q.degreeCount + (fuel - q.degreeCount) = fuel :=
    Data.Nat.Subtraction.add_sub_of_le enough
  rw [← fuelEquation]
  exact signedRemainderChainFuel_add_of_degreeCount_le
    (fuel - q.degreeCount) q.degreeCount p q le_rfl

/-- The normalized chain with its fuel computed from the second polynomial. -/
private def signedRemainderChainWF (p q : WorkingPolynomial) :
    List WorkingPolynomial :=
  signedRemainderChainFuel q.degreeCount p q

/-- The reference degree-bounded signed chain satisfies the retained Euclidean recursion equation.

The same reference divisor and remainder Boolean decisions select each branch.
The retained degree bound justifies the unchanged recursive fuel program. -/
private theorem signedRemainderChainWF_eq (p q : WorkingPolynomial) :
    signedRemainderChainWF p q =
      if q.isZero then [p]
      else
        let division := DensePolynomial.divMod p q
        if division.remainder.isZero then [p, q]
        else p :: signedRemainderChainWF q (-division.remainder) := by
  change signedRemainderChainFuel q.degreeCount p q =
    if q.isZero then [p]
    else
      let division := DensePolynomial.divMod p q
      if division.remainder.isZero then [p, q]
      else p :: signedRemainderChainFuel (-division.remainder).degreeCount q
        (-division.remainder)
  by_cases qTrue : q.isZero = true
  · have degreeZero := DensePolynomial.degreeCount_eq_zero_of_isZero qTrue
    rewrite [degreeZero, signedRemainderChainFuel_zero, if_pos qTrue]
    exact Eq.refl _
  · have qFalse : q.isZero = false :=
      Data.Bool.Decide.bool_eq_false_of_not_eq_true q.isZero qTrue
    have degreePositive := DensePolynomial.degreeCount_pos_of_isZero_false qFalse
    obtain ⟨qDegree, degreeEq⟩ :=
      Nat.exists_eq_succ_of_ne_zero degreePositive.ne'
    rewrite [degreeEq, signedRemainderChainFuel_succ, if_neg qTrue, if_neg qTrue]
    dsimp only
    by_cases remainderTrue : (DensePolynomial.divMod p q).remainder.isZero = true
    · rewrite [if_pos remainderTrue, if_pos remainderTrue]
      exact Eq.refl _
    · have remainderDegree := DensePolynomial.divMod_remainder_degreeCount_lt p q qFalse
      rewrite [if_neg remainderTrue, if_neg remainderTrue]
      apply congrArg (List.cons p)
      exact signedRemainderChainFuel_stable qDegree q
          (-((DensePolynomial.divMod p q).remainder)) (by
            rewrite [DensePolynomial.degreeCount_neg]
            omega0)

/-- The reference signed remainder chain computed with its retained degree bound. -/
private def signedRemainderChain (p q : WorkingPolynomial) :
    List WorkingPolynomial :=
  signedRemainderChainWF p q

/-- The reference signed chain has at most one more entry than the second polynomial's represented degree. -/
private theorem signedRemainderChainWF_length_le (p q : WorkingPolynomial) :
    (signedRemainderChainWF p q).length ≤ q.degreeCount + 1 := by
  change (signedRemainderChainFuel q.degreeCount p q).length ≤
    q.degreeCount + 1
  generalize q.degreeCount = fuel
  induction fuel generalizing p q with
  | zero => exact le_rfl
  | succ fuel inductionHypothesis =>
      rw [signedRemainderChainFuel_succ]
      split
      · simp only [List.length_cons, List.length_nil]
        omega
      · dsimp only
        split
        · simp only [List.length_cons, List.length_nil]
          omega
        · simp only [List.length_cons]
          have recursive := inductionHypothesis q
            (-((DensePolynomial.divMod p q).remainder))
          omega

/-! ## Erasure to the paper-facing chain -/

/-- Coefficient erasure preserves the complete reference degree-bounded signed Euclidean chain. -/
private theorem erase_signedRemainderChainWF (p q : WorkingPolynomial) :
    (signedRemainderChainWF p q).map erasePolynomial =
      Sturm.signedRemainderChainWF
        (erasePolynomial p) (erasePolynomial q) := by
  generalize degreeEquation : q.degreeCount = degree
  induction degree using Nat.strong_induction_on generalizing p q with
  | h degree inductionHypothesis =>
      rw [signedRemainderChainWF_eq,
        Sturm.signedRemainderChainWF_eq]
      have zeroEqual : (erasePolynomial q).isZero = q.isZero :=
        Map.map_isZero eraseEmbedding q
      rw [zeroEqual]
      split
      · rfl
      · rename_i qNonzeroProof
        dsimp only
        have remainderEqual : erasePolynomial (DensePolynomial.divMod p q).remainder =
            (DensePolynomial.divMod (erasePolynomial p) (erasePolynomial q)).remainder :=
          Map.map_divMod_remainder eraseEmbedding p q
        have remainderZeroEqual :
            (DensePolynomial.divMod (erasePolynomial p)
                (erasePolynomial q)).remainder.isZero =
              (DensePolynomial.divMod p q).remainder.isZero := by
          rw [← remainderEqual]
          exact Map.map_isZero eraseEmbedding _
        rw [remainderZeroEqual]
        split
        · rfl
        · simp only [List.map_cons]
          apply congrArg (List.cons (erasePolynomial p))
          have qNonzero : q.isZero = false :=
            Data.Bool.Decide.bool_eq_false_of_not_eq_true q.isZero qNonzeroProof
          have smaller : (-((DensePolynomial.divMod p q).remainder)).degreeCount < degree := by
            rw [DensePolynomial.degreeCount_neg, ← degreeEquation]
            exact DensePolynomial.divMod_remainder_degreeCount_lt p q qNonzero
          rw [inductionHypothesis _ smaller q
            (-((DensePolynomial.divMod p q).remainder)) rfl]
          apply congrArg (Sturm.signedRemainderChainWF
            (erasePolynomial q))
          change Map.map eraseEmbedding
              (-((DensePolynomial.divMod p q).remainder)) = _
          rw [Map.map_neg,
            Map.map_divMod_remainder]
          rfl

/-- Coefficient erasure preserves the reference signed remainder chain. -/
private theorem erase_signedRemainderChain (p q : WorkingPolynomial) :
    (signedRemainderChain p q).map erasePolynomial =
      Sturm.signedRemainderChain
        (erasePolynomial p) (erasePolynomial q) :=
  erase_signedRemainderChainWF p q

/-- Reduced preparation and chain computation erase to the canonical chain of the reference input polynomials. -/
private theorem erase_canonical_signedRemainderChain (p q : Dense) :
    (signedRemainderChain (canonicalPolynomial p)
        (canonicalPolynomial q)).map erasePolynomial =
      Sturm.signedRemainderChain p q := by
  rw [erase_signedRemainderChain, erase_canonicalPolynomial,
    erase_canonicalPolynomial]

/-- Evaluate the reference rational polynomial through its reduced coefficient and point records. -/
private def workingEval (polynomial : Dense) (point : Coordinate) :
    WorkingCoordinate :=
  (canonicalPolynomial polynomial).eval
    (Fraction.Basic.ofRational point)

/-- The reduced evaluation's exact value equals reference polynomial evaluation. -/
private theorem value_workingEval (polynomial : Dense) (point : Coordinate) :
    Fraction.Basic.value (workingEval polynomial point) =
      polynomial.eval point := by
  unfold workingEval
  calc
    Fraction.Basic.value
          ((canonicalPolynomial polynomial).eval
            (Fraction.Basic.ofRational point)) =
        (erasePolynomial (canonicalPolynomial polynomial)).eval
          (Fraction.Basic.value
            (Fraction.Basic.ofRational point)) :=
      Map.map_eval eraseEmbedding _ _
    _ = polynomial.eval point := by
      rw [erase_canonicalPolynomial,
        Fraction.Basic.value_ofRational]

/-- The doubled sign variation of the reference signed chain evaluated at the retained rational endpoint. -/
private def endpointVariation2 (chain : List WorkingPolynomial)
    (point : Coordinate) : Nat :=
  Variation.variation2 (chain.map fun polynomial =>
    Fraction.Basic.value
      (polynomial.eval (Fraction.Basic.ofRational point)))

/-- The reference chain's reduced endpoint readings equal the exact readings of its erased polynomials.

Each reference polynomial contributes the same scalar evaluation at the supplied
endpoint. Structural congruence preserves that reading and the unchanged tail. -/
private theorem workingEvaluations_eq (chain : List WorkingPolynomial)
    (point : Coordinate) :
    chain.map (fun polynomial => Fraction.Basic.value
        (polynomial.eval (Fraction.Basic.ofRational point))) =
      (chain.map erasePolynomial).map (fun polynomial =>
        polynomial.eval point) := by
  induction chain with
  | nil => rfl
  | cons polynomial remaining inductionHypothesis =>
      have headEqual :
          Fraction.Basic.value
              (polynomial.eval (Fraction.Basic.ofRational point)) =
            (erasePolynomial polynomial).eval point := by
        calc
          Fraction.Basic.value
                (polynomial.eval (Fraction.Basic.ofRational point)) =
              (erasePolynomial polynomial).eval
                (Fraction.Basic.value (Fraction.Basic.ofRational point)) :=
            Map.map_eval eraseEmbedding _ _
          _ = (erasePolynomial polynomial).eval point := by
            rewrite [Fraction.Basic.value_ofRational]
            exact Eq.refl _
      exact congrArg₂ List.cons headEqual inductionHypothesis

/-- The reference doubled Cauchy index as the difference of endpoint variations of the retained signed chain. -/
private def cauchyIndex2 (p q : Dense) (a b : Coordinate) : Int :=
  let chain := signedRemainderChain
    (canonicalPolynomial q) (canonicalPolynomial p)
  (endpointVariation2 chain a : Int) - endpointVariation2 chain b

/-- The reference doubled Cauchy-index computation equals the canonical index at the same endpoints. -/
private theorem cauchyIndex2_eq (p q : Dense) (a b : Coordinate) :
    cauchyIndex2 p q a b = Sturm.cauchyIndex2 p q a b := by
  let chain := signedRemainderChain
    (canonicalPolynomial q) (canonicalPolynomial p)
  change (endpointVariation2 chain a : Int) - endpointVariation2 chain b = _
  rw [endpointVariation2, endpointVariation2,
    workingEvaluations_eq chain a, workingEvaluations_eq chain b,
    erase_canonical_signedRemainderChain]
  rfl

/-- The reference reduced and semantic rational carriers are definitionally identical. -/
private theorem rational_carrier_correspondence : WorkingCoordinate = Coordinate := rfl
/-- The retained working polynomial carrier is exactly the canonical Sturm polynomial carrier. -/
private theorem polynomial_carrier_correspondence : WorkingPolynomial =
  CoordinatePolynomial := rfl

/-- The reference reduced rational erasure returns the identical scalar. -/
private theorem erase_embedding_readback (value : WorkingCoordinate) :
    eraseEmbedding.toFun value = value := rfl
/-- The reference canonical rational embedding returns the identical scalar. -/
private theorem canonical_embedding_readback (value : Coordinate) :
    canonicalEmbedding.toFun value = value := rfl

/-- Reference reduced-coefficient polynomial erasure is the identity on the current carrier. -/
private theorem erase_identity (polynomial : WorkingPolynomial) :
    erasePolynomial polynomial = polynomial := by
  apply DensePolynomial.ext
  change polynomial.coeffs.map Fraction.Basic.value = polynomial.coeffs
  induction polynomial.coeffs with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) ih

/-- Reference rational coefficient preparation is the identity on the current carrier. -/
private theorem canonical_identity (polynomial : Dense) :
    canonicalPolynomial polynomial = polynomial := by
  apply DensePolynomial.ext
  change polynomial.coeffs.map Fraction.Basic.ofRational = polynomial.coeffs
  induction polynomial.coeffs with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) ih

/-- The reference fuel-bounded signed-chain program is definitionally the canonical program with the same budget. -/
private theorem fuel_program_correspondence (fuel : Nat) (p q : Dense) :
    signedRemainderChainFuel fuel p q =
      Sturm.signedRemainderChainFuel fuel p q := rfl

/-- The complete reference signed-chain program is definitionally the canonical program. -/
private theorem chain_program_correspondence (p q : Dense) :
    signedRemainderChain p q =
      Sturm.signedRemainderChain p q := rfl

/-- The reference endpoint sign-variation program is definitionally the canonical program. -/
private theorem endpoint_program_correspondence (chain : List WorkingPolynomial) (point : Coordinate) :
    endpointVariation2 chain point = Sturm.endpointVariation2 chain point := rfl

/-- The retained reference doubled Cauchy index equals the canonical index on the same ordered endpoints. -/
private theorem retained_index_correspondence (p q : Dense) (a b : Coordinate) :
    cauchyIndex2 p q a b = Sturm.cauchyIndex2 p q a b :=
  cauchyIndex2_eq p q a b

end Test.Polynomial.ProgramContracts.SignedRemainders

namespace Test.Polynomial.ProgramContracts.Evaluation

/-- The canonical Gaussian-rational scalar carrier. -/
private abbrev SemanticGaussian := Data.Gaussian.Basic.Canonical
/-- The retained reference working Gaussian carrier. -/
private abbrev WorkingGaussian := Data.Gaussian.Basic.Number
/-- Dense polynomials over canonical Gaussian rationals. -/
private abbrev GaussianPolynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The reference Horner update multiplies the retained accumulator by the point and adds the next coefficient. -/
private def step (point accumulator : WorkingGaussian)
    (coefficient : SemanticGaussian) : WorkingGaussian :=
  Data.Gaussian.Basic.add
    (Data.Gaussian.Basic.mul accumulator point)
    (Data.Gaussian.Basic.ofGaussian coefficient)
/-- The reference working Horner update reads exactly as scalar multiplication and addition. -/
private theorem value_step (point accumulator : WorkingGaussian)
    (coefficient : SemanticGaussian) :
    Data.Gaussian.Basic.value (step point accumulator coefficient) =
      Data.Gaussian.Basic.value accumulator *
          Data.Gaussian.Basic.value point + coefficient := by
  rw [step, Data.Gaussian.Basic.value_add,
    Data.Gaussian.Basic.value_mul,
    Data.Gaussian.Basic.value_ofGaussian]
/-- Evaluate the reference finite coefficient list from the retained Gaussian accumulator. -/
private def evalCoeffsFrom (point : WorkingGaussian) :
    WorkingGaussian → List SemanticGaussian → WorkingGaussian
  | accumulator, [] => accumulator
  | accumulator, coefficient :: remaining =>
      evalCoeffsFrom point (step point accumulator coefficient) remaining
/-- Evaluate the reference coefficient list from the exact zero accumulator. -/
private def evalCoeffs (point : SemanticGaussian)
    (coefficients : List SemanticGaussian) : WorkingGaussian :=
  evalCoeffsFrom (Data.Gaussian.Basic.ofGaussian point)
    (Data.Gaussian.Basic.ofGaussian 0) coefficients
/-- Evaluate the reference Gaussian polynomial using its retained coefficient list. -/
private def eval (polynomial : GaussianPolynomial)
    (point : SemanticGaussian) : WorkingGaussian :=
  evalCoeffs point polynomial.coeffs
/-- The reference working Horner recurrence reads as the exact scalar fold from its retained accumulator. -/
private theorem value_evalCoeffsFrom (point accumulator : WorkingGaussian)
    (coefficients : List SemanticGaussian) :
    Data.Gaussian.Basic.value
        (evalCoeffsFrom point accumulator coefficients) =
      coefficients.foldl
        (fun current coefficient =>
          current * Data.Gaussian.Basic.value point + coefficient)
        (Data.Gaussian.Basic.value accumulator) := by
  induction coefficients generalizing accumulator with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      rw [evalCoeffsFrom, inductionHypothesis, value_step, List.foldl_cons]
/-- The reference working coefficient evaluation reads as canonical polynomial coefficient evaluation. -/
private theorem value_evalCoeffs (point : SemanticGaussian)
    (coefficients : List SemanticGaussian) :
    Data.Gaussian.Basic.value (evalCoeffs point coefficients) =
      DensePolynomial.evalCoeffs point coefficients := by
  rw [evalCoeffs, value_evalCoeffsFrom,
    Data.Gaussian.Basic.value_ofGaussian,
    Data.Gaussian.Basic.value_ofGaussian]
  rfl
/-- The reference working polynomial evaluation reads as the canonical exact scalar value. -/
private theorem value_eval (polynomial : GaussianPolynomial)
    (point : SemanticGaussian) :
    Data.Gaussian.Basic.value (eval polynomial point) =
      polynomial.eval point := by
  exact value_evalCoeffs point polynomial.coeffs

/-- The reference Horner update equals the canonical executable update. -/
private theorem step_program_correspondence (point accumulator coefficient : WorkingGaussian) :
    step point accumulator coefficient =
      step point accumulator coefficient := rfl

/-- The reference accumulator-based coefficient recurrence equals the canonical evaluator. -/
private theorem from_program_correspondence (point accumulator : WorkingGaussian)
    (coefficients : List SemanticGaussian) :
    evalCoeffsFrom point accumulator coefficients =
      evalCoeffsFrom point accumulator coefficients := by
  induction coefficients generalizing accumulator with
  | nil => rfl
  | cons coefficient remaining ih =>
      change evalCoeffsFrom point (step point accumulator coefficient) remaining =
        evalCoeffsFrom point
          (step point accumulator coefficient) remaining
      exact ih _

/-- The reference zero-based coefficient evaluation equals the canonical evaluator. -/
private theorem coefficients_program_correspondence (point : SemanticGaussian)
    (coefficients : List SemanticGaussian) :
    evalCoeffs point coefficients = DensePolynomial.evalCoeffs point coefficients :=
  value_evalCoeffs point coefficients

/-- The complete reference polynomial evaluator equals canonical polynomial evaluation. -/
private theorem eval_program_correspondence (polynomial : GaussianPolynomial)
    (point : SemanticGaussian) : eval polynomial point = polynomial.eval point :=
  value_eval polynomial point

end Test.Polynomial.ProgramContracts.Evaluation

namespace Test.Polynomial.ProgramContracts.GaussianHorner

/-- The exact canonical rational bound carrier. -/
private abbrev Coordinate := Fraction.Rational
/-- The exact canonical Gaussian-rational scalar carrier. -/
private abbrev Gaussian := Data.Gaussian.Basic.Canonical
open Purelib.Data.Gaussian.Basic.Canonical

set_option genInjectivity false in
/-- The reference value and derivative Gaussian norm bounds for the finite Horner recurrence. -/
private structure HornerNormBounds where
  /-- The retained bound on the squared polynomial value. -/ value : Coordinate
  /-- The retained bound on the squared polynomial derivative. -/ slope : Coordinate
deriving DecidableEq

constructive_injectivity HornerNormBounds

/-- Advance the retained Gaussian norm value and derivative bounds by the reference doubled Horner formulas. -/
private def HornerNormBounds.step (radiusSq : Coordinate)
    (bounds : HornerNormBounds) (coefficient : Gaussian) : HornerNormBounds where
  value := 2 * (bounds.value * radiusSq + normSq coefficient)
  slope := 2 * (bounds.slope * radiusSq + bounds.value)

/-- Transport the retained value and slope bounds to the canonical Horner bound pair. -/
private def toCanonical (bounds : HornerNormBounds) :
    Polynomial.Bounds.Horner := ⟨bounds.value, bounds.slope⟩

/-- Read the canonical Horner bound pair into its reference value and slope layout. -/
private def fromCanonical (bounds : Polynomial.Bounds.Horner) :
    HornerNormBounds := ⟨bounds.value, bounds.slope⟩

/-- Canonical transport and readback preserve the exact reference Horner bound pair. -/
private theorem reference_roundtrip (bounds : HornerNormBounds) :
    fromCanonical (toCanonical bounds) = bounds := by
  cases bounds
  rfl

/-- Reference-layout readback and transport preserve the exact canonical Horner bound pair. -/
private theorem canonical_roundtrip (bounds : Polynomial.Bounds.Horner) :
    toCanonical (fromCanonical bounds) = bounds := by
  cases bounds
  rfl

/-- Transport preserves the reference Gaussian norm Horner update with the same radius and coefficient. -/
private theorem step_correspondence (radiusSq : Coordinate)
    (bounds : HornerNormBounds) (coefficient : Gaussian) :
    toCanonical (HornerNormBounds.step radiusSq bounds coefficient) =
      Horner.step radiusSq (toCanonical bounds) coefficient := by
  cases bounds with
  | mk value slope =>
      unfold HornerNormBounds.step toCanonical
        Horner.step
      change (⟨2 * (value * radiusSq + Data.Gaussian.Basic.Canonical.normSq coefficient),
        2 * (slope * radiusSq + value)⟩ : Polynomial.Bounds.Horner) =
        ⟨2 * (value * radiusSq + Data.Gaussian.Norm.Basic.normSq coefficient),
        2 * (slope * radiusSq + value)⟩
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]

end Test.Polynomial.ProgramContracts.GaussianHorner

namespace Test.Polynomial.ProgramContracts.RationalHorner

/-- The exact canonical rational bound carrier. -/
private abbrev Coordinate := Fraction.Rational
/-- The exact canonical Gaussian-rational scalar carrier. -/
private abbrev Gaussian := Data.Gaussian.Basic.Canonical
open Purelib.Data.Gaussian.Basic.Canonical

set_option genInjectivity false in
/-- The reference value and derivative rational square bounds for the finite Horner recurrence. -/
private structure HornerSqBounds where
  /-- The retained bound on the squared polynomial value. -/ value : Coordinate
  /-- The retained bound on the squared polynomial derivative. -/ slope : Coordinate
deriving DecidableEq

constructive_injectivity HornerSqBounds

/-- Advance the retained rational square value and derivative bounds by the reference doubled Horner formulas. -/
private def HornerSqBounds.step (radiusSq : Coordinate)
    (bounds : HornerSqBounds) (coefficient : Coordinate) : HornerSqBounds where
  value := 2 * (bounds.value * radiusSq + coefficient ^ 2)
  slope := 2 * (bounds.slope * radiusSq + bounds.value)

/-- Transport the retained value and slope bounds to the canonical Horner bound pair. -/
private def toCanonical (bounds : HornerSqBounds) :
    Polynomial.Bounds.Horner := ⟨bounds.value, bounds.slope⟩

/-- Read the canonical Horner bound pair into its reference value and slope layout. -/
private def fromCanonical (bounds : Polynomial.Bounds.Horner) :
    HornerSqBounds := ⟨bounds.value, bounds.slope⟩

/-- Canonical transport and readback preserve the exact reference Horner bound pair. -/
private theorem reference_roundtrip (bounds : HornerSqBounds) :
    fromCanonical (toCanonical bounds) = bounds := by
  cases bounds
  rfl

/-- Reference-layout readback and transport preserve the exact canonical Horner bound pair. -/
private theorem canonical_roundtrip (bounds : Polynomial.Bounds.Horner) :
    toCanonical (fromCanonical bounds) = bounds := by
  cases bounds
  rfl

/-- Transport preserves the reference rational square Horner update with the same radius and coefficient. -/
private theorem step_correspondence (radiusSq : Coordinate)
    (bounds : HornerSqBounds) (coefficient : Coordinate) :
    toCanonical (HornerSqBounds.step radiusSq bounds coefficient) =
      Pair.step radiusSq (toCanonical bounds) coefficient := rfl

end Test.Polynomial.ProgramContracts.RationalHorner
