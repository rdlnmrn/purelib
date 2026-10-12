module
import Purelib.Algebra.FiniteSum.Fin.Rational
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.LinearAlgebra.Matrix.Basic

public import Purelib.Riemann.Periods.PeriodMatrix

@[expose] public section

/-! Cached uniform magnitude bounds for the actual displayed A/B samples. -/
namespace Purelib.Riemann.Periods

open Purelib.Riemann.Periods.PeriodMatrix
open Purelib.LinearAlgebra.Gaussian.QuadraticForm

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_ite_eq)
open Purelib.LinearAlgebra.Matrix (matrixOfFn matrixOfFn_apply)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus}

open Purelib.Algebra in
open Purelib.Approximation in
open Purelib.LinearAlgebra in
set_option genInjectivity false in
/-- Cached quadrance bounds for every retained A/B period name and their finite aggregate.

Both matrices read the center bounds of the actual sampling approximations. The aggregate sums all entries and bounds
every displayed sample at every stage. -/
structure PeriodSampleBounds (data : PeriodData curve) where
  /-- The cached matrix of A-period approximation center bounds. -/ a : Purelib.LinearAlgebra.Matrix Coordinate genus
  /-- The cached matrix of B-period approximation center bounds. -/ b : Purelib.LinearAlgebra.Matrix Coordinate genus
  /-- Each A bound is the center bound of the corresponding retained name's approximation. -/ a_eq : ∀ row cycle, a row
    cycle = (Gaussian.Name.Sampling.approximation (data.aMatrix row cycle).name).centerBound
  /-- Each B bound is the center bound of the corresponding retained name's approximation. -/ b_eq : ∀ row cycle, b row
    cycle = (Gaussian.Name.Sampling.approximation (data.bMatrix row cycle).name).centerBound
  /-- The cached total of all A and B center bounds. -/ magnitude : Coordinate
  /-- The total equals the nested finite sum of the two retained bound matrices. -/ magnitude_eq : magnitude =
    FiniteSum.Fin.sumFin (fun row => FiniteSum.Fin.sumFin (fun cycle => a row cycle + b row cycle))

constructive_injectivity PeriodSampleBounds

namespace PeriodSampleBounds

open Purelib.Algebra in
open Purelib.Approximation in
open Purelib.LinearAlgebra in
/-- Cache the actual A/B sampling center bounds and their aggregate once. -/
def build (data : PeriodData curve) : PeriodSampleBounds data :=
  let a := Matrix.matrixOfFn fun row cycle => (Gaussian.Name.Sampling.approximation
    (data.aMatrix row cycle).name).centerBound
  let b := Matrix.matrixOfFn fun row cycle => (Gaussian.Name.Sampling.approximation
    (data.bMatrix row cycle).name).centerBound
  ⟨a, b, Matrix.matrixOfFn_apply _, Matrix.matrixOfFn_apply _,
    FiniteSum.Fin.sumFin (fun row => FiniteSum.Fin.sumFin (fun cycle => a row cycle + b row cycle)), rfl⟩

variable {data : PeriodData curve} (bounds : PeriodSampleBounds data)

section
open Purelib.Algebra
/-- A finite sum of nonnegative rational values is nonnegative. -/
private theorem sum_nonnegative {count : Nat} {values : Fin count → Coordinate}
    (nonnegative : ∀ index, 0 ≤ values index) : 0 ≤ FiniteSum.Fin.sumFin values :=
  FiniteSum.Fin.sumFin_zero.symm.trans_le (FiniteSum.Rational.Order.IndexedBudget.sumFin_le nonnegative)

end

section
open Purelib.Approximation
/-- Every retained A-period center bound is nonnegative. -/
theorem a_nonnegative (row cycle : Fin genus) : 0 ≤ bounds.a row cycle :=
  (bounds.a_eq row cycle).symm ▸ (Gaussian.Name.Sampling.approximation (data.aMatrix row cycle).name).centerBound_nonneg

/-- Every retained B-period center bound is nonnegative. -/
theorem b_nonnegative (row cycle : Fin genus) : 0 ≤ bounds.b row cycle :=
  (bounds.b_eq row cycle).symm ▸ (Gaussian.Name.Sampling.approximation (data.bMatrix row cycle).name).centerBound_nonneg

end

/-- The cached aggregate period bound is nonnegative. -/
theorem magnitude_nonnegative : 0 ≤ bounds.magnitude := by
  rw [bounds.magnitude_eq]
  exact sum_nonnegative fun row => sum_nonnegative fun cycle => add_nonneg (bounds.a_nonnegative row cycle)
    (bounds.b_nonnegative row cycle)

open Purelib.Algebra in
/-- Each A/B pair of center bounds is at most the retained aggregate. -/
private theorem entry_le_magnitude (row cycle : Fin genus) : bounds.a row cycle + bounds.b row cycle ≤ bounds.magnitude
  := by
  rw [bounds.magnitude_eq]
  have each := fun row cycle => add_nonneg (bounds.a_nonnegative row cycle) (bounds.b_nonnegative row cycle)
  exact (FiniteSum.Fin.Rational.entry_le_sum
    (fun cycle => bounds.a row cycle + bounds.b row cycle) (each row) cycle).trans
    (FiniteSum.Fin.Rational.entry_le_sum
      (fun row => FiniteSum.Fin.sumFin (fun cycle => bounds.a row cycle + bounds.b row cycle))
      (fun row => sum_nonnegative (each row)) row)

open Purelib.Approximation
open Purelib.Data
/-- Every actual A-period sample has quadrance at most the cached aggregate bound. -/
theorem a_bounded (stage : Nat) (row cycle : Fin genus) :
    Data.Gaussian.Norm.Basic.normSq (sampledMatrix data.aMatrix stage row cycle) ≤ bounds.magnitude := by
  rw [sampledMatrix_apply]
  exact ((Gaussian.Name.Sampling.approximation (data.aMatrix row cycle).name).sample_bounded stage).trans
    ((bounds.a_eq row cycle).symm.trans_le
      ((le_add_of_nonneg_right (bounds.b_nonnegative row cycle)).trans (bounds.entry_le_magnitude row cycle)))

/-- Every actual B-period sample has quadrance at most the cached aggregate bound. -/
theorem b_bounded (stage : Nat) (row cycle : Fin genus) :
    Data.Gaussian.Norm.Basic.normSq (sampledMatrix data.bMatrix stage row cycle) ≤ bounds.magnitude := by
  rw [sampledMatrix_apply]
  exact ((Gaussian.Name.Sampling.approximation (data.bMatrix row cycle).name).sample_bounded stage).trans
    ((bounds.b_eq row cycle).symm.trans_le
      ((le_add_of_nonneg_left (bounds.a_nonnegative row cycle)).trans (bounds.entry_le_magnitude row cycle)))

end PeriodSampleBounds
end Purelib.Riemann.Periods
