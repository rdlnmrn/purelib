module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Constants.Inverse
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Power

import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Norm.Basic

section
@[expose] public section

/-!
# Finite raw-prefix parser over constructive Gaussian fractions

The completed-block encoder is not enough for a persistent root name: a
request may stop inside a unary header or after only one or two sector bits.
This module records exactly that unfinished syntax, the finite decoder
product, and the finite list of already completed block constraints.  It is
the state needed by the box/CCL next-bit controller; no stream, completion,
or collection of compatible points is formed.
-/

namespace Purelib.Data.CCL.Encoding.Parser.Semantics.Basic

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
/-- Normalize a Gaussian by the retained parser block kind and gamma exponent.

Initial-low blocks multiply by the gamma power. Initial-high and loop blocks multiply by its reciprocal, preserving
their distinct radial branch semantics. -/
def normalizedValue (kind : Parser.Syntax.BlockKind) (exponent :
  Nat)
    (value : Basic.Canonical) : Basic.Canonical :=
  match kind with
  | .initialLow => Power.natPow Basic.Canonical.gamma exponent * value
  | .initialHigh | .loop => value * (Power.natPow Basic.Canonical.gamma exponent)⁻¹

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Require the retained block's exact half-open radial normalization interval.

Initial-high uses a weak lower and strict upper power-of-two bound. Initial-low scales the squared norm into the
weak-lower, strict-upper unit-to-two interval; loop normalization uses a strict lower and weak upper bound. -/
def radialBracket (kind : Parser.Syntax.BlockKind) (exponent :
  Nat)
    (value : Basic.Canonical) : Prop :=
  match kind with
  | .initialHigh =>
      (2 : Fraction.Rational) ^ exponent ≤ Basic.Canonical.normSq value ∧
        Basic.Canonical.normSq value < (2 : Fraction.Rational) ^ (exponent + 1)
  | .initialLow =>
      1 ≤ (2 : Fraction.Rational) ^ exponent * Basic.Canonical.normSq value ∧
        (2 : Fraction.Rational) ^ exponent * Basic.Canonical.normSq value < 2
  | .loop =>
      (2 : Fraction.Rational) ^ exponent < Basic.Canonical.normSq value ∧
        Basic.Canonical.normSq value ≤ (2 : Fraction.Rational) ^ (exponent + 1)

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
/-- Decide the exact rational radial bounds of the retained parser kind and exponent. -/
instance radialBracketDecidable (kind : Parser.Syntax.BlockKind)
  (exponent : Nat)
    (value : Basic.Canonical) : Decidable (radialBracket kind exponent value) := by
  cases kind <;> simp only [radialBracket] <;> infer_instance

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Data.Gaussian
/-- Require the retained radial bracket and selected sector condition for the exact normalized value. -/
def fullBlockHolds (kind : Parser.Syntax.BlockKind) (exponent :
  Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector)
    (value : Basic.Canonical) : Prop :=
  radialBracket kind exponent value ∧
    sector.Holds (normalizedValue kind exponent value)

/-- Decide the retained completed block's radial and sector conditions. -/
instance fullBlockHoldsDecidable (kind :
  Parser.Syntax.BlockKind) (exponent : Nat)
    (sector : Data.ComplexContinuedFraction.Encoding.Sector) (value : Basic.Canonical) :
    Decidable (fullBlockHolds kind exponent sector value) := by
  unfold fullBlockHolds
  infer_instance

end

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Interpret the unfinished parser phase as exact Gaussian norm and sector-candidate conditions.

Unary phases retain their current lower or upper bound, including the separate zero low counter. A sector phase requires
its completed radial bracket and a matching sector among the candidates for the exact bits already read. -/
def activeHolds : Parser.Syntax.Phase → Basic.Canonical → Prop
  | .initial, _ => True
  | .highUnary count, value => (2 : Fraction.Rational) ^ count ≤ Basic.Canonical.normSq value
  | .lowUnary 0, value => Basic.Canonical.normSq value < 2
  | .lowUnary (count + 1), value =>
      (2 : Fraction.Rational) ^ count * Basic.Canonical.normSq value < 1
  | .loopUnary count, value => (2 : Fraction.Rational) ^ count < Basic.Canonical.normSq value
  | .sector kind exponent bits, value =>
      radialBracket kind exponent value ∧
        ∃ sector ∈ Sector.Code.sectorCandidates bits,
          sector.Holds (normalizedValue kind exponent value)

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
/-- Decide the retained phase's norm bounds and finite sector-candidate conditions. -/
instance activeHoldsDecidable (phase : Parser.Syntax.Phase)
  (value : Basic.Canonical) :
    Decidable (activeHolds phase value) := by
  cases phase with
  | initial => simp only [activeHolds]; infer_instance
  | highUnary count => simp only [activeHolds]; infer_instance
  | lowUnary count =>
      cases count <;> simp only [activeHolds] <;> infer_instance
  | loopUnary count => simp only [activeHolds]; infer_instance
  | sector kind exponent bits => simp only [activeHolds]; infer_instance
end Purelib.Data.CCL.Encoding.Parser.Semantics.Basic

end

section
@[expose] public section

/-!
# Exact projective semantics of progressive arithmetic cursors

The raw `Machine` remains the original bit-only cursor.  This module adds a
separate proof wrapper relating its quantitative mode to the ordinary raw
parser matrix.  In particular, residual modes are interpreted homogeneously
as `[1 : γr]`; this is an affine inverse tail when `r ≠ 0` and is exactly
`ω` when `r = 0`.  No equality decision on a completed value is needed.
-/

namespace Purelib.Data.CCL.Encoding.Parser.Semantics.Basic

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
/-- Initial-low normalization cancels the retained reciprocal gamma-power scaling exactly. -/
public theorem lowNormalized_unscaled (count : Nat) (value :
  Basic.Canonical) :
    normalizedValue .initialLow count
        ((Power.natPow Basic.Canonical.gamma count)⁻¹ * value) = value := by
  let power := Power.natPow Basic.Canonical.gamma count
  have powerNonzero : power ≠ 0 :=
    Power.natPow_ne_zero_direct Basic.Canonical.gamma Constants.Inverse.gamma_ne count
  have cancellation : power * power⁻¹ = 1 :=
    Basic.Canonical.mul_inv_cancel power powerNonzero
  simp only [normalizedValue]
  calc
    power * (power⁻¹ * value) = (power * power⁻¹) * value :=
      (Basic.mul_assoc _ _ _).symm
    _ = value := by
      rw [cancellation, Basic.one_mul]

end Purelib.Data.CCL.Encoding.Parser.Semantics.Basic

end
