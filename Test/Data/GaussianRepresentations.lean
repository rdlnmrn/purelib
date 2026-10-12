module

import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Norm.Basic

import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Gaussian.Fraction.NaturalDenominator
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data

open Purelib.Data.ComplexContinuedFraction.Encoding

namespace Test.Data.GaussianRepresentations

set_option genInjectivity false in
/-- Reference Height integer layout, retained only for certified correspondence. -/
@[ext] private structure RetainedHeightInt where
  /-- The retained reference integer real coordinate. -/ re : Int
  /-- The retained reference integer imaginary coordinate. -/ im : Int
deriving DecidableEq

constructive_injectivity RetainedHeightInt

/-- The retained coordinate pair has zero in both integer coordinates. -/
private instance : Zero RetainedHeightInt := ⟨⟨0, 0⟩⟩
/-- The retained integer-pair multiplication uses the reference Gaussian coordinate formulas. -/
private instance : Mul RetainedHeightInt :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im,
    z.re * w.im + z.im * w.re⟩⟩

/-- Transport the retained integer coordinate pair to the canonical Gaussian-integer carrier. -/
private def into (value : RetainedHeightInt) : Data.GaussianInt :=
  ⟨value.re, value.im⟩
/-- Read canonical Gaussian-integer coordinates into the retained reference pair layout. -/
private def outof (value : Data.GaussianInt) : RetainedHeightInt :=
  ⟨value.re, value.im⟩

/-- Canonical transport followed by readback preserves the reference integer pair. -/
private theorem reference_roundtrip (value : RetainedHeightInt) : outof (into value) = value := by
  cases value; rfl
/-- Reference-layout readback followed by transport preserves the canonical Gaussian integer. -/
private theorem canonical_roundtrip (value : Data.GaussianInt) : into (outof value) = value := by
  cases value; rfl
/-- The retained coordinate multiplication is exactly canonical Gaussian-integer multiplication. -/
private theorem product_correspondence (left right : RetainedHeightInt) :
    into (left * right) = into left * into right := rfl
/-- The reference sum-of-squares height is exactly the canonical Gaussian-integer norm. -/
private theorem norm_correspondence (value : RetainedHeightInt) :
    (value.re * value.re + value.im * value.im).natAbs =
      GaussianInt.normNat (into value) := rfl

set_option genInjectivity false in
/-- Reference CCL Gaussian-denominator fields, with their actual nonzero evidence. -/
private structure RetainedCCLFraction where
  /-- The reference displayed Gaussian-integer numerator. -/ num : Data.GaussianInt
  /-- The reference displayed Gaussian-integer denominator. -/ den : Data.GaussianInt
  /-- The retained reference denominator is nonzero. -/ den_ne : den ≠ 0

constructive_injectivity RetainedCCLFraction

/-- Transport the reference displayed Gaussian fraction with its exact numerator, denominator and nonzero witness. -/
private def selected (value : RetainedCCLFraction) : GaussianInt.Fraction :=
  ⟨value.num, value.den, value.den_ne⟩
/-- Read the canonical displayed Gaussian fraction back into its reference field layout. -/
private def retained (value : GaussianInt.Fraction) : RetainedCCLFraction :=
  ⟨value.numerator, value.denominator, value.denominatorNonzero⟩
/-- Evaluate the retained reference numerator times the reciprocal of its retained nonzero denominator. -/
private def referenceValue (value : RetainedCCLFraction) : Data.Gaussian.Basic.Canonical :=
  GaussianInt.toGaussian value.num *
    (GaussianInt.toGaussian value.den)⁻¹

/-- Displayed-fraction transport and readback preserve the reference record and its nonzero evidence. -/
private theorem ccl_reference_roundtrip (value : RetainedCCLFraction) :
    retained (selected value) = value := by cases value; rfl
/-- Reference-layout readback and transport preserve the canonical displayed fraction. -/
private theorem ccl_canonical_roundtrip (value : GaussianInt.Fraction) :
    selected (retained value) = value := by cases value; rfl
/-- Displayed-fraction transport preserves the exact Gaussian value. -/
private theorem ccl_value_correspondence (value : RetainedCCLFraction) :
    (selected value).value = referenceValue value := rfl
/-- Displayed-fraction transport retains the exact reference denominator. -/
private theorem displayed_denominator_correspondence (value : RetainedCCLFraction) :
    (selected value).denominator = value.den := rfl
/-- Displayed-fraction height remains the squared norm of its reference denominator. -/
private theorem displayed_height_correspondence (value : RetainedCCLFraction) :
    (selected value).height = GaussianInt.normNat value.den := rfl

/-- Canonical transport followed by readback preserves the reference integer pair. -/
example (value : RetainedHeightInt) : outof (into value) = value := reference_roundtrip value
/-- Reference-layout readback followed by transport preserves the canonical Gaussian integer. -/
example (value : Data.GaussianInt) : into (outof value) = value := canonical_roundtrip value
/-- The retained coordinate multiplication is exactly canonical Gaussian-integer multiplication. -/
example (left right : RetainedHeightInt) :
    into (left * right) = into left * into right := product_correspondence left right
/-- The reference sum-of-squares height is exactly the canonical Gaussian-integer norm. -/
example (value : RetainedHeightInt) :
    (value.re * value.re + value.im * value.im).natAbs =
      GaussianInt.normNat (into value) := norm_correspondence value
/-- Displayed-fraction transport and readback preserve the reference record and its nonzero evidence. -/
example (value : RetainedCCLFraction) : retained (selected value) = value := ccl_reference_roundtrip value
/-- Reference-layout readback and transport preserve the canonical displayed fraction. -/
example (value : GaussianInt.Fraction) : selected (retained value) = value := ccl_canonical_roundtrip value
/-- Displayed-fraction transport preserves the exact Gaussian value. -/
example (value : RetainedCCLFraction) : (selected value).value = referenceValue value := ccl_value_correspondence value
/-- Displayed-fraction transport retains the exact reference denominator. -/
example (value : RetainedCCLFraction) : (selected value).denominator = value.den := displayed_denominator_correspondence
  value
/-- Displayed-fraction height remains the squared norm of its reference denominator. -/
example (value : RetainedCCLFraction) : (selected value).height = GaussianInt.normNat value.den :=
  displayed_height_correspondence value

/-- A natural-denominator Gaussian fraction displays the exact Gaussian-integer embedding of its reference denominator.
-/
example (value : Data.Gaussian.Basic.Canonical.Fraction.NaturalDenominator) :
    value.toDisplayed.denominator = Data.GaussianInt.ofNat value.denominator := rfl
/-- Displaying a natural-denominator Gaussian fraction preserves its reference height. -/
example (value : Data.Gaussian.Basic.Canonical.Fraction.NaturalDenominator) :
    value.toDisplayed.height = value.height := value.toDisplayed_height
/-- Displaying a natural-denominator Gaussian fraction preserves its exact value. -/
example (value : Data.Gaussian.Basic.Canonical.Fraction.NaturalDenominator) :
    value.toDisplayed.value = value.value := value.toDisplayed_value

set_option genInjectivity false in
/-- The reference Hurwitz displayed fraction layout with its actual Gaussian-integer denominator witness. -/
private structure RetainedHurwitzFraction where
  /-- The reference Hurwitz Gaussian-integer numerator. -/ numerator : Data.GaussianInt
  /-- The reference Hurwitz Gaussian-integer denominator. -/ denominator : Data.GaussianInt
  /-- The retained reference Hurwitz denominator is nonzero. -/ denominatorNonzero : denominator ≠ 0

constructive_injectivity RetainedHurwitzFraction

/-- Transport the retained Hurwitz fraction to the canonical displayed fraction. -/
private def hurwitzInto (value : RetainedHurwitzFraction) : GaussianInt.Fraction :=
  ⟨value.numerator, value.denominator, value.denominatorNonzero⟩
/-- Read the canonical displayed fraction into the retained Hurwitz field layout. -/
private def hurwitzOutof (value : GaussianInt.Fraction) : RetainedHurwitzFraction :=
  ⟨value.numerator, value.denominator, value.denominatorNonzero⟩
/-- Canonical fraction transport and readback preserve the retained Hurwitz record. -/
private theorem hurwitz_reference_roundtrip (value : RetainedHurwitzFraction) :
    hurwitzOutof (hurwitzInto value) = value := by cases value; rfl
/-- Hurwitz-layout readback and transport preserve the canonical displayed fraction. -/
private theorem hurwitz_canonical_roundtrip (value : GaussianInt.Fraction) :
    hurwitzInto (hurwitzOutof value) = value := by cases value; rfl
/-- Hurwitz transport preserves the reference numerator times reciprocal-denominator value. -/
private theorem hurwitz_value_correspondence (value : RetainedHurwitzFraction) :
    (hurwitzInto value).value = GaussianInt.toGaussian value.numerator *
      (GaussianInt.toGaussian value.denominator)⁻¹ := rfl

/-- The retained sector name is an exact alias of the canonical continued-fraction sector. -/
private abbrev RetainedSectorAlias := Data.ComplexContinuedFraction.Encoding.Sector
/-- The retained sector alias has the identical canonical sector type. -/
private theorem sector_alias_correspondence :
    RetainedSectorAlias = Data.ComplexContinuedFraction.Encoding.Sector := rfl
/-- The retained height-number name is an exact alias of the canonical Gaussian-rational carrier. -/
private abbrev RetainedHeightNumber := Data.Gaussian.Basic.Canonical
/-- The retained height-number alias has the identical canonical Gaussian-rational type. -/
private theorem height_number_alias_correspondence :
    RetainedHeightNumber = Data.Gaussian.Basic.Canonical := rfl

end Test.Data.GaussianRepresentations
