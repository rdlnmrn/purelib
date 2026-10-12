module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
public import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Riemann.Periods.PeriodMatrix
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Data.Rat

open Purelib.Riemann.Normalization

open Purelib.Riemann.Periods

@[expose] public section

/-! Uniform reciprocal basis ceilings selected before any polynomial sampling. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data (Vector)
open _root_.Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_zero sumFin_congr sumFin_sub sumFin_mul_left sumFin_mul_right)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {data : Data cap}

set_option genInjectivity false in
/-- Cache every uniform basis ceiling before choosing the polynomial stage. -/
structure BasisBounds (bounds : ReciprocalPaddedInverse.UniformBounds data) where
  /-- The cached original uniform coefficient ceiling for each standard differential. -/ entries :
    Data.Vector InverseRootPolynomial.Coordinate genus
  /-- Every retained entry equals the original inverse bound's standard-differential ceiling. -/ entries_eq : ∀ row,
    entries row = bounds.coefficientUpper (PeriodMatrix.standardDifferential row)
  /-- The cached genus-weighted sum of all original basis coefficient ceilings. -/ coefficient :
    InverseRootPolynomial.Coordinate
  /-- The retained aggregate ceiling is exactly the genus times the original finite entry sum. -/ coefficient_eq :
    coefficient = (genus : InverseRootPolynomial.Coordinate) * FiniteSum.Fin.sumFin entries

constructive_injectivity BasisBounds

namespace BasisBounds

variable {bounds : UniformBounds data}

/-- Cache every original standard-differential coefficient ceiling and their exact genus-weighted sum. -/
def build (bounds : ReciprocalPaddedInverse.UniformBounds data) :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds :=
  let entries := Data.Vector.Basic.vectorOfFn (fun row => bounds.coefficientUpper (PeriodMatrix.standardDifferential
    row))
  ⟨entries, fun row => Data.Vector.Basic.vectorOfFn_apply _ row,
    Aggregate.countCoordinate genus * FiniteSum.Fin.sumFin entries, by rw [Aggregate.countCoordinate_eq]⟩

/-- The retained aggregate basis coefficient ceiling is nonnegative. -/
theorem coefficient_nonnegative (basis : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds
  bounds) : 0 ≤ basis.coefficient := by
  rw [basis.coefficient_eq]
  apply Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
  exact FiniteSum.Fin.sumFin_zero.symm.trans_le (Order.Positivity.sumFin_mono (fun _ => (0 :
    InverseRootPolynomial.Coordinate)) _
    (fun row => (bounds.coefficientUpper_nonnegative (PeriodMatrix.standardDifferential row)).trans_eq (basis.entries_eq
      row).symm))

end BasisBounds
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
