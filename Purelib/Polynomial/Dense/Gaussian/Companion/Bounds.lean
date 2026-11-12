module

public import Purelib.Polynomial.Dense.Companion
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Horner
public import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Vector.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cached disk bounds for original companion powers and source residuals

The original degree determines every power-bound position. One stored table
and its finite total bound every retained power read. The same original source
polynomial supplies its Horner value bound and leading normalization.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Companion

open Purelib.Data.Rat.Fraction
open Purelib
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Algebra.FiniteSum
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

set_option genInjectivity false in
/-- Original companion data with one squared-radius request and its actual cached power and source bounds. -/
structure Bounds {polynomial : DensePolynomial Canonical} (companion : Dense.Companion polynomial)
    (radiusSq : Fraction.Rational) where
  /-- The requested squared disk radius is nonnegative. -/
  radius_nonnegative : 0 ≤ radiusSq
  /-- The actual finite table of squared-radius powers at the original polynomial degree. -/
  powers : Data.Vector Fraction.Rational polynomial.natDegree
  /-- Every retained table entry is the corresponding original bounded radius power. -/
  powers_eq : ∀ index, powers index = radiusSq ^ index.val
  /-- The actual total of the same retained power table. -/
  powerTotal : Fraction.Rational
  /-- The total consumes those same retained powers. -/
  powerTotal_eq : powerTotal = Fin.sumFin (fun index => powers index)
  /-- The positive common ceiling for all original power-vector entries. -/
  powerBound : Fraction.Rational
  /-- The common ceiling is one plus the same stored total. -/
  powerBound_eq : powerBound = 1 + powerTotal
  /-- The original source polynomial's actual disk Horner bounds. -/
  source : Polynomial.Bounds.Horner
  /-- The source bounds were computed on the original polynomial and requested radius. -/
  source_eq : source = Gaussian.Bounds.Horner.onDisk polynomial radiusSq
  /-- The original leading inverse's squared norm used by every normalized residual. -/
  leadingInverse : Fraction.Rational
  /-- The normalization reading belongs to the original polynomial's leading inverse. -/
  leadingInverse_eq : leadingInverse = Norm.Basic.normSq polynomial.leadingCoeff⁻¹

constructive_injectivity Bounds

/-- Compute the original degree-sized power table, its total and the original source Horner bound once. -/
def Bounds.prepare {polynomial : DensePolynomial Canonical} (companion : Dense.Companion polynomial)
    (radiusSq : Fraction.Rational) (nonnegative : 0 ≤ radiusSq) : Bounds companion radiusSq :=
  let powers := vectorOfFn fun index : Fin polynomial.natDegree => radiusSq ^ index.val
  let powerTotal := Fin.sumFin fun index => powers index
  let powerBound := 1 + powerTotal
  let source := Gaussian.Bounds.Horner.onDisk polynomial radiusSq
  let leadingInverse := Norm.Basic.normSq companion.leadingInverse
  ⟨nonnegative, powers, fun index => vectorOfFn_apply _ index, powerTotal, rfl,
    powerBound, rfl, source, rfl, leadingInverse, congrArg Norm.Basic.normSq companion.leadingInverse_eq⟩

namespace Bounds

variable {polynomial : DensePolynomial Canonical} {companion : Dense.Companion polynomial}
variable {radiusSq : Fraction.Rational}

/-- Each retained squared-radius power is nonnegative. -/
theorem powers_nonnegative (bounds : Bounds companion radiusSq) (index : Fin polynomial.natDegree) :
    0 ≤ bounds.powers index := by
  rewrite [bounds.powers_eq index]
  exact Order.Arithmetic.pow_nonneg_direct bounds.radius_nonnegative index.val

/-- The original finite power total is nonnegative. -/
theorem powerTotal_nonnegative (bounds : Bounds companion radiusSq) : 0 ≤ bounds.powerTotal := by
  rewrite [bounds.powerTotal_eq]
  exact Rational.Order.weight_sum_nonnegative _ bounds.powers_nonnegative

/-- The common original power ceiling is positive because it retains its unit floor. -/
theorem powerBound_positive (bounds : Bounds companion radiusSq) : 0 < bounds.powerBound := by
  rewrite [bounds.powerBound_eq]
  have floor : (1 : Fraction.Rational) ≤ 1 + bounds.powerTotal := by
    have ordered := Order.Arithmetic.add_le_add_direct
      (show (1 : Fraction.Rational) ≤ 1 from le_rfl) bounds.powerTotal_nonnegative
    rewrite [add_zero] at ordered
    exact ordered
  exact (by decide : (0 : Fraction.Rational) < 1).trans_le floor

/-- Every original power-vector reading in the requested disk is bounded by the same retained finite ceiling. -/
theorem normSq_power_le (bounds : Bounds companion radiusSq) (point : Canonical)
    (inside : Norm.Basic.normSq point ≤ radiusSq) (index : Fin polynomial.natDegree) :
    Norm.Basic.normSq (companion.powers point index) ≤ bounds.powerBound := by
  rewrite [companion.powers_apply, Power.normSq_pow]
  have power := Order.Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg point) inside index.val
  have retained : radiusSq ^ index.val ≤ bounds.powerTotal := by
    rewrite [← bounds.powers_eq index, bounds.powerTotal_eq]
    exact Rational.Order.entry_le_sumFin _ bounds.powers_nonnegative index
  have total : bounds.powerTotal ≤ bounds.powerBound := by
    rewrite [bounds.powerBound_eq]
    have ordered := Order.Arithmetic.add_le_add_direct
      (by decide : (0 : Fraction.Rational) ≤ 1) (show bounds.powerTotal ≤ bounds.powerTotal from le_rfl)
    rewrite [Fraction.zero_add] at ordered
    exact ordered
  exact power.trans (retained.trans total)

/-- The retained leading normalization is nonnegative. -/
theorem leadingInverse_nonnegative (bounds : Bounds companion radiusSq) : 0 ≤ bounds.leadingInverse := by
  rewrite [bounds.leadingInverse_eq]
  exact Norm.Basic.normSq_nonneg _

/-- The retained source Horner value is nonnegative. -/
theorem source_nonnegative (bounds : Bounds companion radiusSq) : 0 ≤ bounds.source.value := by
  rewrite [bounds.source_eq]
  exact (Gaussian.Bounds.Horner.onDisk_nonnegative polynomial radiusSq bounds.radius_nonnegative).1

/-- The original normalized terminal residual is bounded by the actual source reading and retained leading factor. -/
theorem normSq_residual_le (bounds : Bounds companion radiusSq) (point : Canonical)
    (index : Fin polynomial.natDegree) :
    Norm.Basic.normSq (companion.residual point index) ≤
      Norm.Basic.normSq (polynomial.eval point) * bounds.leadingInverse := by
  unfold Dense.Companion.residual
  split
  · rewrite [Norm.Basic.normSq_mul, companion.leadingInverse_eq, bounds.leadingInverse_eq]
    exact le_rfl
  · rewrite [Norm.Basic.normSq_zero]
    exact Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg _) bounds.leadingInverse_nonnegative

/-- The same original source disk bound controls every normalized residual reading in that disk. -/
theorem normSq_residual_le_source (bounds : Bounds companion radiusSq) (point : Canonical)
    (inside : Norm.Basic.normSq point ≤ radiusSq) (index : Fin polynomial.natDegree) :
    Norm.Basic.normSq (companion.residual point index) ≤ bounds.source.value * bounds.leadingInverse := by
  have source : Norm.Basic.normSq (polynomial.eval point) ≤ bounds.source.value := by
    rewrite [bounds.source_eq]
    exact Gaussian.Bounds.Horner.normSq_eval_le_onDisk polynomial radiusSq bounds.radius_nonnegative point inside
  exact (bounds.normSq_residual_le point index).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct source bounds.leadingInverse_nonnegative)

end Bounds

end Purelib.Polynomial.Dense.Gaussian.Companion

end
