module

public import Purelib.Data.Gaussian.Power
public import Purelib.Algebra.FiniteSum.Rational.Order
public import Purelib.Data.Vector.Scan
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Fin
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cached finite power bounds at a fixed Gaussian radius

Two structural scans retain the powers of the squared-radius bound and the
corresponding squared-error growth factor. Their stored totals bound every
requested original finite power without repeating either scan.
-/

public section

namespace Purelib.Data.Gaussian.Power

open Purelib.Data.Rat.Fraction
open Purelib.Data.Vector.Basic
open Purelib.Data.Vector.Scan
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Algebra.FiniteSum.Rational.Order

set_option genInjectivity false in
/-- Cached finite powers and their totals for one nonnegative squared-radius bound.

The radius and finite count remain indices. Both power tables retain the
initial unit and their final successor entry; each total sums exactly the
first displayed count of entries.
-/
structure Radius (count : Nat) (radius : Rational) where
  /-- The original squared-radius bound is nonnegative. -/
  nonnegative : 0 ≤ radius
  /-- The materialized successive powers of the same fixed radius. -/
  powers : Vector Rational (count + 1)
  /-- Each retained radius power has its same bounded exponent. -/
  powers_eq : ∀ index, powers index = radius ^ index.val
  /-- The stored sum of the first original radius powers. -/
  powerTotal : Rational
  /-- The radius total consumes the same stored finite table. -/
  powerTotal_eq : powerTotal = sumFin (fun index : Fin count => powers index.castSucc)
  /-- The stored squared-error growth factor for this same radius. -/
  growth : Rational
  /-- The stored growth factor has its original rational expression. -/
  growth_eq : growth = 2 * (1 + radius)
  /-- The materialized successive powers of the stored growth factor. -/
  growthPowers : Vector Rational (count + 1)
  /-- Each retained growth power has its same bounded exponent. -/
  growthPowers_eq : ∀ index, growthPowers index = growth ^ index.val
  /-- The stored sum of the first original growth powers. -/
  growthTotal : Rational
  /-- The growth total consumes the same stored finite table. -/
  growthTotal_eq : growthTotal = sumFin (fun index : Fin count => growthPowers index.castSucc)

constructive_injectivity Radius

namespace Radius

/-- The original structural scan reads the same natural power at every bounded position. -/
theorem scan_power (base : Rational) {count : Nat} (edges : Vector Unit count)
    (index : Fin (count + 1)) :
    scan (fun value (_ : Unit) => value * base) 1 edges index = base ^ index.val := by
  refine Purelib.Data.Fin.induction (motive := fun index =>
    scan (fun value (_ : Unit) => value * base) 1 edges index = base ^ index.val) ?_ ?_ index
  · exact (scan_zero _ _ _).trans (pow_zero base).symm
  · intro previous inductionHypothesis
    rewrite [scan_step, inductionHypothesis]
    exact (pow_succ base previous.val).symm

/-- Materialize both original finite power scans and sum their stored entries once. -/
@[expose] def prepare (count : Nat) (radius : Rational) (nonnegative : 0 ≤ radius) : Radius count radius :=
  let edges := vectorOfFn (fun _ : Fin count => Unit.unit)
  let powers := scan (fun value (_ : Unit) => value * radius) 1 edges
  let growth := 2 * (1 + radius)
  let growthPowers := scan (fun value (_ : Unit) => value * growth) 1 edges
  { nonnegative
    powers
    powers_eq := scan_power radius edges
    powerTotal := sumFin (fun index : Fin count => powers index.castSucc)
    powerTotal_eq := rfl
    growth
    growth_eq := rfl
    growthPowers
    growthPowers_eq := scan_power growth edges
    growthTotal := sumFin (fun index : Fin count => growthPowers index.castSucc)
    growthTotal_eq := rfl }

variable {count : Nat} {radius : Rational}

/-- Every stored radius power is nonnegative. -/
theorem power_nonnegative (bounds : Radius count radius) (index : Fin (count + 1)) :
    0 ≤ bounds.powers index := by
  rewrite [bounds.powers_eq index]
  exact Order.Arithmetic.pow_nonneg_direct bounds.nonnegative index.val

/-- The stored radius-power total is nonnegative. -/
theorem powerTotal_nonnegative (bounds : Radius count radius) : 0 ≤ bounds.powerTotal := by
  rewrite [bounds.powerTotal_eq]
  exact weight_sum_nonnegative _ (fun index => bounds.power_nonnegative index.castSucc)

/-- The same stored squared-error growth factor is nonnegative. -/
theorem growth_nonnegative (bounds : Radius count radius) : 0 ≤ bounds.growth := by
  rewrite [bounds.growth_eq]
  exact Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Rational) ≤ 2)
    (Order.Arithmetic.add_le_add_direct (by decide : (0 : Rational) ≤ 1) bounds.nonnegative)

/-- Every stored growth power is nonnegative. -/
theorem growthPower_nonnegative (bounds : Radius count radius) (index : Fin (count + 1)) :
    0 ≤ bounds.growthPowers index := by
  rewrite [bounds.growthPowers_eq index]
  exact Order.Arithmetic.pow_nonneg_direct bounds.growth_nonnegative index.val

/-- The stored growth-power total is nonnegative. -/
theorem growthTotal_nonnegative (bounds : Radius count radius) : 0 ≤ bounds.growthTotal := by
  rewrite [bounds.growthTotal_eq]
  exact weight_sum_nonnegative _ (fun index => bounds.growthPower_nonnegative index.castSucc)

/-- One original radius power below the displayed count is bounded by the stored total. -/
theorem power_le_total (bounds : Radius count radius) (index : Fin count) :
    radius ^ index.val ≤ bounds.powerTotal := by
  apply (bounds.powers_eq index.castSucc).symm.le.trans
  rewrite [bounds.powerTotal_eq]
  exact entry_le_sumFin _ (fun selected => bounds.power_nonnegative selected.castSucc) index

/-- One original growth power below the displayed count is bounded by the stored total. -/
theorem growth_pow_le_total (bounds : Radius count radius) (index : Fin count) :
    (2 * (1 + radius)) ^ index.val ≤ bounds.growthTotal := by
  have original : (2 * (1 + radius)) ^ index.val = bounds.growthPowers index.castSucc :=
    (congrArg (fun base : Rational => base ^ index.val) bounds.growth_eq).symm.trans
      (bounds.growthPowers_eq index.castSucc).symm
  apply original.le.trans
  rewrite [bounds.growthTotal_eq]
  exact entry_le_sumFin _ (fun selected => bounds.growthPower_nonnegative selected.castSucc) index

/-- Every bounded power of the same radius-controlled Gaussian has its norm bounded by the stored radius total. -/
theorem normSq_pow_le (bounds : Radius count radius) (point : Basic.Canonical)
    (bounded : Norm.Basic.normSq point ≤ radius) (index : Fin count) :
    Norm.Basic.normSq (point ^ index.val) ≤ bounds.powerTotal := by
  rewrite [normSq_pow]
  exact (Order.Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg point) bounded index.val).trans
    (bounds.power_le_total index)

end Radius

end Purelib.Data.Gaussian.Power

end
