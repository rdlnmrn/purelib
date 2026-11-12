module

public import Purelib.Calculus.Jet.Quadratic.Basic

/-! # Exact increment transport of retained quadratic certificates

An equality of the indexed Gaussian increment reindexes the complete
original certificate. No base, slope, output, remainder or factor changes.
-/

public section

namespace Purelib.Calculus.Jet.Quadratic.Basic.Certificate

open Purelib.Data.Gaussian.Basic (Canonical)

variable {first last : Canonical}

/-- Reindex the same whole quadratic certificate along an exact increment equality. -/
@[expose] def castIncrement (equal : first = last) (retained : Certificate first) : Certificate last := by
  cases equal
  exact retained

variable (equal : first = last) (retained : Certificate first)

/-- Increment transport retains the entire original certificate heterogeneously. -/
theorem castIncrement_heq : HEq (retained.castIncrement equal) retained := by
  cases equal
  rfl

/-- Increment transport preserves the original Gaussian base. -/
theorem castIncrement_base : (retained.castIncrement equal).base = retained.base := by
  cases equal
  rfl

/-- Increment transport preserves the original Gaussian slope. -/
theorem castIncrement_slope : (retained.castIncrement equal).slope = retained.slope := by
  cases equal
  rfl

/-- Increment transport preserves the original Gaussian output. -/
theorem castIncrement_output : (retained.castIncrement equal).output = retained.output := by
  cases equal
  rfl

/-- Increment transport preserves the original remainder and its quantitative certificate. -/
theorem castIncrement_remainder : (retained.castIncrement equal).remainder = retained.remainder := by
  cases equal
  rfl

/-- Increment transport preserves the original rational factor exactly. -/
theorem castIncrement_factor : (retained.castIncrement equal).factor = retained.factor := by
  cases equal
  rfl

end Purelib.Calculus.Jet.Quadratic.Basic.Certificate

end
