module
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic
import Purelib.Calculus.Jet.Quadratic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

section
@[expose] public section

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Trace
section Trace

/-! ## Exact specialization -/

open Purelib.Data in
open Purelib.Calculus.Jet.Quadratic.Basic in
/-- Sum the quadrances of the increment and four fields of a displayed certificate. -/
def certificateBound {increment :
  Canonical}
    (certificate : Certificate increment) : Rat.Fraction.Rational :=
  Canonical.normSq increment + Canonical.normSq certificate.base +
    Canonical.normSq certificate.output +
    Canonical.normSq certificate.slope + Canonical.normSq certificate.remainder

section
open Purelib.Data
open Purelib.Calculus.Jet.Quadratic.Basic
/-- The sum of the five displayed quadrances is nonnegative. -/
theorem certificateBound_nonneg {increment :
  Canonical}
    (certificate : Certificate increment) :
    0 ≤ certificateBound certificate := by
  unfold certificateBound
  exact add_nonneg (add_nonneg (add_nonneg
    (add_nonneg (Canonical.normSq_nonneg increment) (Canonical.normSq_nonneg
      certificate.base))
      (Canonical.normSq_nonneg certificate.output)) (Canonical.normSq_nonneg
        certificate.slope))
    (Canonical.normSq_nonneg certificate.remainder)

/-- The increment quadrance is bounded by the sum of all five quadrances. -/
private theorem first_le_certificateBound {increment
  : Canonical}
    (certificate : Certificate increment) :
    Canonical.normSq increment ≤ certificateBound certificate := by
  unfold certificateBound
  let rest := Canonical.normSq certificate.base + Canonical.normSq certificate.output +
    Canonical.normSq certificate.slope + Canonical.normSq certificate.remainder
  have restNonnegative : 0 ≤ rest := by
    dsimp only [rest]
    exact add_nonneg (add_nonneg (add_nonneg
      (Canonical.normSq_nonneg certificate.base) (Canonical.normSq_nonneg
        certificate.output))
      (Canonical.normSq_nonneg certificate.slope)) (Canonical.normSq_nonneg
        certificate.remainder)
  calc
    Canonical.normSq increment ≤ Canonical.normSq increment + rest :=
      le_add_of_nonneg_right restNonnegative
    _ = Canonical.normSq increment + Canonical.normSq certificate.base +
        Canonical.normSq certificate.output + Canonical.normSq certificate.slope +
        Canonical.normSq certificate.remainder := by
      dsimp only [rest]
      ring1

/-- The base quadrance is bounded by the sum of all five quadrances. -/
private theorem base_le_certificateBound {increment
  : Canonical}
    (certificate : Certificate increment) :
    Canonical.normSq certificate.base ≤ certificateBound certificate := by
  unfold certificateBound
  calc
    Canonical.normSq certificate.base ≤ Canonical.normSq increment +
      Canonical.normSq certificate.base :=
      le_add_of_nonneg_left (Canonical.normSq_nonneg increment)
    _ ≤ (Canonical.normSq increment + Canonical.normSq certificate.base) +
        (Canonical.normSq certificate.output + Canonical.normSq certificate.slope +
          Canonical.normSq certificate.remainder) :=
      le_add_of_nonneg_right
        (add_nonneg (add_nonneg (Canonical.normSq_nonneg certificate.output)
          (Canonical.normSq_nonneg certificate.slope))
          (Canonical.normSq_nonneg certificate.remainder))
    _ = _ := by ring1

/-- The output quadrance is bounded by the sum of all five quadrances. -/
private theorem output_le_certificateBound
  {increment : Canonical}
    (certificate : Certificate increment) :
    Canonical.normSq certificate.output ≤ certificateBound certificate := by
  unfold certificateBound
  calc
    Canonical.normSq certificate.output ≤
        Canonical.normSq increment + Canonical.normSq certificate.base +
          Canonical.normSq certificate.output :=
      le_add_of_nonneg_left
        (add_nonneg (Canonical.normSq_nonneg increment) (Canonical.normSq_nonneg
          certificate.base))
    _ ≤ (Canonical.normSq increment + Canonical.normSq certificate.base +
          Canonical.normSq certificate.output) +
        (Canonical.normSq certificate.slope + Canonical.normSq certificate.remainder) :=
      le_add_of_nonneg_right
        (add_nonneg (Canonical.normSq_nonneg certificate.slope)
          (Canonical.normSq_nonneg certificate.remainder))
    _ = _ := by ring1

/-- The slope quadrance is bounded by the sum of all five quadrances. -/
private theorem slope_le_certificateBound {increment
  : Canonical}
    (certificate : Certificate increment) :
    Canonical.normSq certificate.slope ≤ certificateBound certificate := by
  unfold certificateBound
  calc
    Canonical.normSq certificate.slope ≤
        Canonical.normSq increment + Canonical.normSq certificate.base +
          Canonical.normSq certificate.output + Canonical.normSq certificate.slope :=
      le_add_of_nonneg_left (add_nonneg
        (add_nonneg (Canonical.normSq_nonneg increment) (Canonical.normSq_nonneg
          certificate.base))
        (Canonical.normSq_nonneg certificate.output))
    _ ≤ _ := le_add_of_nonneg_right (Canonical.normSq_nonneg certificate.remainder)

/-- The remainder quadrance is bounded by the sum of all five quadrances. -/
private theorem remainder_le_certificateBound
  {increment : Canonical}
    (certificate : Certificate increment) :
    Canonical.normSq certificate.remainder ≤ certificateBound certificate := by
  unfold certificateBound
  exact le_add_of_nonneg_left (add_nonneg
    (add_nonneg (add_nonneg (Canonical.normSq_nonneg increment)
      (Canonical.normSq_nonneg certificate.base)) (Canonical.normSq_nonneg
        certificate.output))
    (Canonical.normSq_nonneg certificate.slope))

end

open Purelib.Approximation in
open Purelib.Data in
open Purelib.Calculus.Jet.Quadratic.Basic in
/-- Make a constant quadratic trace from one displayed certificate.

Every index retains the same certificate and increment. The geometric error scale is zero, and the sum of the five
quadrances supplies a common center bound. -/
def exact {increment : Canonical}
  (certificate : Certificate increment) :
    Trace (fun _ => increment) where
  certificate _ := certificate
  errorScale := 0
  errorScale_nonneg := le_rfl
  increment_later_close := by
    intro earlier later order
    rw [_root_.sub_self, Canonical.normSq_zero,
      Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
      Rat.Fraction.Field.zero_mul_direct]
  base_later_close := by
    intro earlier later order
    rw [_root_.sub_self, Canonical.normSq_zero,
      Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
      Rat.Fraction.Field.zero_mul_direct]
  output_later_close := by
    intro earlier later order
    rw [_root_.sub_self, Canonical.normSq_zero,
      Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
      Rat.Fraction.Field.zero_mul_direct]
  slope_later_close := by
    intro earlier later order
    rw [_root_.sub_self, Canonical.normSq_zero,
      Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
      Rat.Fraction.Field.zero_mul_direct]
  remainder_later_close := by
    intro earlier later order
    rw [_root_.sub_self, Canonical.normSq_zero,
      Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
      Rat.Fraction.Field.zero_mul_direct]
  centerBound := certificateBound certificate
  centerBound_nonneg := certificateBound_nonneg certificate
  increment_bounded _ := by exact first_le_certificateBound certificate
  base_bounded _ := by exact base_le_certificateBound certificate
  output_bounded _ := by exact output_le_certificateBound certificate
  slope_bounded _ := by exact slope_le_certificateBound certificate
  remainder_bounded _ := by exact remainder_le_certificateBound certificate

open Purelib.Data in
open Purelib.Calculus.Jet.Quadratic.Basic in
/-- Every index of the constant trace returns the original certificate. -/
@[simp] theorem exact_certificate {increment :
  Canonical}
    (certificate : Certificate increment) (index : Nat) :
    (exact certificate).certificate index = certificate := rfl
end Trace

end Purelib.Calculus.Jet.Progressive.Quadratic.Trace

end
