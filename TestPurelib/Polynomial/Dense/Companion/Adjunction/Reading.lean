module

import Purelib.Polynomial.Dense.Companion.Adjunction.Reading
import Purelib.Data.Gaussian.Field

/-!
# Exact quotient readings at nonroot candidates

The retained quadratic root algebra reads at `3/4`, whose square is not the
original root relation. Its quotient still reads exactly as the original
Gaussian quotient at that candidate. The linear source keeps its determined
root `1/2` and the candidate's explicit residual separately.
-/

namespace TestPurelib.Polynomial.Dense.Companion.Adjunction.Reading

open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Division
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Algebra.Monogenic

/-- The same rational candidate is deliberately not either original source root. -/
private def candidate : Canonical := 3 / 4

/-- The original irrational-root source is a normalized quadratic. -/
private def quadratic : DensePolynomial Canonical := ⟨[1, 0, -(1 / 2)]⟩

/-- The original quadratic companion retains its displayed leading inverse once. -/
private def quadraticCompanion : Companion quadratic :=
  Companion.ofUnit quadratic (by decide +kernel) 1 (by decide +kernel)

/-- The actual original quadratic adjunction retains its one source, root and stripping result. -/
private def quadraticAdjunction := quadraticCompanion.adjoin

/-- The same original quadratic coefficient reading is prepared once for its actual source companion. -/
private def quadraticReading : Companion.Reading quadraticAdjunction.companion id 1 :=
  Companion.Reading.prepare quadraticAdjunction.companion id 1 rfl rfl (fun _ => rfl)
    (fun value => by change value * 1 = value * 1; rfl)

/-- The actual retained quadratic quotient reads as the same original Gaussian synthetic division. -/
private theorem quadratic_quotient :
    Map.map (Cyclic.Element.evaluate id candidate) quadraticAdjunction.division.quotient =
      (Synthetic.divide (Map.map id quadratic) candidate).quotient :=
  quadraticAdjunction.quotient_reading (by decide +kernel) id rfl (fun _ _ => rfl) candidate

/-- The whole actual quadratic quotient coefficient table has the independently displayed target values. -/
private theorem quadratic_quotient_table :
    Map.map (Cyclic.Element.evaluate id candidate) quadraticAdjunction.division.quotient =
      (⟨[1, 3 / 4]⟩ : DensePolynomial Canonical) := by
  rewrite [quadratic_quotient]
  decide +kernel

/-- In the quadratic algebra the same retained generator reads exactly as the nonroot candidate. -/
private theorem quadratic_root_reading : Cyclic.Element.evaluate id candidate quadraticAdjunction.root = candidate :=
  quadraticAdjunction.root_reading_of_two_le quadraticReading rfl candidate (by decide +kernel)

/-- The same candidate interpretation does not preserve the original quadratic generator product. -/
private theorem quadratic_nonmultiplicative :
    Cyclic.Element.evaluate id candidate (quadraticAdjunction.root * quadraticAdjunction.root) ≠
      Cyclic.Element.evaluate id candidate quadraticAdjunction.root *
        Cyclic.Element.evaluate id candidate quadraticAdjunction.root := by
  change (1 / 2 : Canonical) ≠ (3 / 4 : Canonical) * (3 / 4 : Canonical)
  decide +kernel

/-- The original linear source has a nonmonic displayed leading coefficient. -/
private def linear : DensePolynomial Canonical := ⟨[2, -1]⟩

/-- Its original leading inverse is the same exact one half. -/
private def linearCompanion : Companion linear :=
  Companion.ofUnit linear (by decide +kernel) (1 / 2) (by decide +kernel)

/-- The original degree-one adjunction retains the forced root separately from the supplied candidate. -/
private def linearAdjunction := linearCompanion.adjoin

/-- The same original linear companion has its once-prepared Gaussian coefficient reading. -/
private def linearReading : Companion.Reading linearAdjunction.companion id (1 / 2) :=
  Companion.Reading.prepare linearAdjunction.companion id (1 / 2) rfl rfl (fun _ => rfl)
    (fun value => by change value * (1 / 2) = value * (1 / 2); rfl)

/-- The linear actual cached quotient reads the same constant quotient at the candidate. -/
private theorem linear_quotient :
    Map.map (Cyclic.Element.evaluate id candidate) linearAdjunction.division.quotient =
      (⟨[2]⟩ : DensePolynomial Canonical) := by
  rewrite [linearAdjunction.quotient_reading (by decide +kernel) id rfl (fun _ _ => rfl) candidate]
  decide +kernel

/-- The actual degree-one root reading is one half even though the supplied candidate is three quarters. -/
private theorem linear_root_reading :
    Cyclic.Element.evaluate id candidate linearAdjunction.root = (1 / 2 : Canonical) := by
  rewrite [linearAdjunction.root_reading_of_degree_one linearReading rfl candidate (by decide +kernel)]
  decide +kernel

/-- The same degree-one generator-candidate error retains the independently displayed negative quarter. -/
private theorem linear_error :
    Cyclic.Element.evaluate id candidate linearAdjunction.root - candidate = -(1 / 4 : Canonical) := by
  rewrite [linear_root_reading]
  decide +kernel

/-- The all-input error estimate uses the same actual observed source value and retained inverse image. -/
private theorem linear_error_bound :
    Norm.Basic.normSq (Cyclic.Element.evaluate id candidate linearAdjunction.root - candidate) ≤
      (1 / 4 : Purelib.Data.Rat.Fraction.Rational) * Norm.Basic.normSq (1 / 2 : Canonical) :=
  linearAdjunction.root_reading_error_normSq_le linearReading rfl candidate (1 / 4) (by decide +kernel)

end TestPurelib.Polynomial.Dense.Companion.Adjunction.Reading
