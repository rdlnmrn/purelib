module

public import Purelib.Data.Gaussian.Norm.Separation
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Same-sheet product sums and prepared-reading perturbations

An exact first ordinate and a nearby second ordinate retain a signed sum
floor. A paid cofactor spread transfers that floor to their full product sum.
A separately paid discrepancy on one actual reading preserves a quarter of
the resulting full-product norm floor.
-/

public section

namespace Purelib.Data.Gaussian.Norm.Bounds

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- A nine-radius normalized sum and paid original cofactor spread give a full-product sum floor. -/
theorem cofactor_sum_lower (firstCofactor lastCofactor firstOrdinate lastOrdinate : Canonical)
    {cofactorFloor radiusSq : Fraction.Rational} (cofactorNonnegative : 0 ≤ cofactorFloor)
    (radiusNonnegative : 0 ≤ radiusSq) (firstLower : cofactorFloor ≤ Norm.Basic.normSq firstCofactor)
    (sumLower : 9 * radiusSq ≤ Norm.Basic.normSq (firstOrdinate + lastOrdinate))
    (lastUpper : Norm.Basic.normSq lastOrdinate ≤ 20 * radiusSq)
    (cofactorClose : Norm.Basic.normSq (firstCofactor - lastCofactor) ≤ cofactorFloor / 10) :
    cofactorFloor * radiusSq ≤
      Norm.Basic.normSq (firstCofactor * firstOrdinate + lastCofactor * lastOrdinate) := by
  let floor := cofactorFloor * radiusSq
  let perturbation := (firstCofactor - lastCofactor) * lastOrdinate
  let value := firstCofactor * firstOrdinate + lastCofactor * lastOrdinate
  have floorNonnegative : 0 ≤ floor := Arithmetic.mul_nonneg_direct cofactorNonnegative radiusNonnegative
  have mainLower : 9 * floor ≤ Norm.Basic.normSq (firstCofactor * (firstOrdinate + lastOrdinate)) := by
    rewrite [Norm.Basic.normSq_mul]
    exact (show 9 * floor = cofactorFloor * (9 * radiusSq) by dsimp only [floor]; ring1).trans_le
      (Arithmetic.mul_le_mul_direct firstLower sumLower
        (Arithmetic.mul_nonneg_direct (by decide +kernel) radiusNonnegative)
        (Norm.Basic.normSq_nonneg _))
  have perturbationUpper : Norm.Basic.normSq perturbation ≤ 2 * floor := by
    rewrite [Norm.Basic.normSq_mul]
    calc
      _ ≤ (cofactorFloor / 10) * (20 * radiusSq) :=
        Arithmetic.mul_le_mul_direct cofactorClose lastUpper (Norm.Basic.normSq_nonneg _)
          (Fraction.Order.Field.div_nonneg_direct cofactorNonnegative (by decide +kernel))
      _ = 2 * floor := by
        dsimp only [floor]
        have paid : (cofactorFloor / 10) * 10 = cofactorFloor :=
          Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)
        calc
          _ = ((cofactorFloor / 10) * 10) * (2 * radiusSq) := by ring1
          _ = _ := by rewrite [paid]; ring1
  have combined : 4 * (2 * floor) ≤ Norm.Basic.normSq (perturbation + value) := by
    have ordered := Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide +kernel : (8 : Fraction.Rational) ≤ 9) floorNonnegative
    exact (show 4 * (2 * floor) = 8 * floor by ring1).trans_le
      ((ordered.trans mainLower).trans_eq (congrArg Norm.Basic.normSq (show
        firstCofactor * (firstOrdinate + lastOrdinate) = perturbation + value by
          dsimp only [perturbation, value]; ring1)))
  exact (show floor ≤ 2 * floor from by
    have doubled := Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide +kernel : (1 : Fraction.Rational) ≤ 2) floorNonnegative
    exact (Fraction.Field.one_mul _).symm.trans_le doubled).trans
      (other_normSq_lower_of_sum perturbation value (2 * floor) combined perturbationUpper)

/-- A paid source-reading discrepancy preserves one quarter of a full-product sum norm floor. -/
theorem prepared_sum_lower (original prepared target : Canonical) {floor : Fraction.Rational}
    (floorNonnegative : 0 ≤ floor) (sumLower : floor ≤ Norm.Basic.normSq (original + target))
    (sourceClose : Norm.Basic.normSq (prepared - original) ≤ floor / 16) :
    floor / 4 ≤ Norm.Basic.normSq (prepared + target) := by
  have quarterFloor : floor / 4 ≤ Norm.Basic.normSq (original + target) / 4 := by
    change floor * (4 : Fraction.Rational)⁻¹ ≤ Norm.Basic.normSq (original + target) * (4 : Fraction.Rational)⁻¹
    exact Arithmetic.mul_le_mul_of_nonneg_right_direct sumLower (by decide +kernel)
  have close : Norm.Basic.normSq ((original + target) - (prepared + target)) ≤
      Norm.Basic.normSq (original + target) / 4 := by
    rewrite [show (original + target) - (prepared + target) = original - prepared by ring1,
      normSq_sub_symm original prepared]
    exact sourceClose.trans ((Fraction.Order.Field.div_le_div_of_nonneg_left_direct
      floorNonnegative (by decide +kernel : (0 : Fraction.Rational) < 4)
      (by decide +kernel : (4 : Fraction.Rational) ≤ 16)).trans quarterFloor)
  exact quarterFloor.trans (quarter_normSq_le_of_close (original + target) (prepared + target) close)

end Purelib.Data.Gaussian.Norm.Bounds
