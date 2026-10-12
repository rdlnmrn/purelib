module
import Purelib.Algebra.Ring.IntCast
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Integration.Energy.Polygon

public import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Cut.CoordinatePairing
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Executable two-coordinate tests recover entries of an integer alternating matrix. -/
namespace Purelib.Riemann.Readings.EnergyMatrixEntries

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_ite_eq sumFin_mul_right)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Gaussian.Basic (conj_add)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)
open Purelib.Topology.Surface.Word.Pairing (contract contract_zero contract_add)

open Purelib.Data in
/-- Construct the two-coordinate Gaussian probe with one at the first index and i at the last. -/
@[expose] def entryProbe {count : Nat} (first last index : Fin count) : Gaussian.Basic.Canonical :=
  (if index = first then 1 else 0) + (if index = last then (⟨0, 1⟩ : Gaussian.Basic.Canonical) else 0)

/-- The entry probe vanishes away from both retained indices. -/
theorem entryProbe_zero {count : Nat} {first last index : Fin count}
    (notFirst : index ≠ first) (notLast : index ≠ last) : entryProbe first last index = 0 := by
  rw [entryProbe, if_neg notFirst, if_neg notLast, add_zero]

section
open Purelib.Algebra
open Purelib.Data
/-- A weighted probe sum reads the first weight plus i times the last weight. -/
theorem sum_entryProbe {count : Nat} (first last : Fin count) (weights : Fin count → Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun index => weights index * entryProbe first last index) =
      weights first + weights last * (⟨0, 1⟩ : Gaussian.Basic.Canonical) := by
  have each (index : Fin count) : weights index * entryProbe first last index =
      (if index = first then weights index else 0) +
      (if index = last then weights index * (⟨0, 1⟩ : Gaussian.Basic.Canonical) else 0) := by
    unfold entryProbe
    by_cases atFirst : index = first <;>
      (first | simp only [if_pos atFirst, -eq_self, -iff_self] | simp only [if_neg atFirst, -eq_self, -iff_self]) <;>
      by_cases atLast : index = last <;>
      (first | simp only [if_pos atLast, -eq_self, -iff_self] | simp only [if_neg atLast, -eq_self, -iff_self]) <;>
      simp only [mul_add, mul_one, mul_zero, -eq_self, -iff_self] <;> rfl
  exact (FiniteSum.Fin.sumFin_congr each).trans ((FiniteSum.Fin.sumFin_add _ _).trans
    (congrArg₂ (· + ·) (FiniteSum.Fin.sumFin_ite_eq first _) (FiniteSum.Fin.sumFin_ite_eq last _)))

/-- A weighted conjugate-probe sum reads the first weight minus i times the last weight. -/
theorem sum_conj_entryProbe {count : Nat} (first last : Fin count) (weights : Fin count → Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun index => weights index * Data.Gaussian.Basic.conj (entryProbe first last index)) =
      weights first - weights last * (⟨0, 1⟩ : Gaussian.Basic.Canonical) := by
  have each (index : Fin count) : weights index * Data.Gaussian.Basic.conj (entryProbe first last index) =
      (if index = first then weights index else 0) +
      (if index = last then -(weights index * (⟨0, 1⟩ : Gaussian.Basic.Canonical)) else 0) := by
    have oneConj : Data.Gaussian.Basic.conj (1 : Gaussian.Basic.Canonical) = 1 := by decide
    have imagConj : Data.Gaussian.Basic.conj (⟨0, 1⟩ : Gaussian.Basic.Canonical) = -(⟨0, 1⟩ :
      Gaussian.Basic.Canonical) := by decide
    unfold entryProbe
    rw [Gaussian.Basic.conj_add]
    by_cases atFirst : index = first <;>
      (first | simp only [if_pos atFirst, -eq_self, -iff_self] | simp only [if_neg atFirst, -eq_self, -iff_self]) <;>
      by_cases atLast : index = last <;>
      (first | simp only [if_pos atLast, -eq_self, -iff_self] | simp only [if_neg atLast, -eq_self, -iff_self]) <;>
      simp only [ oneConj, imagConj,
        Gaussian.Basic.conj_zero, mul_add, mul_one, mul_zero, mul_neg, -eq_self, -iff_self] <;> rfl
  exact (FiniteSum.Fin.sumFin_congr each).trans ((FiniteSum.Fin.sumFin_add _ _).trans
    ((congrArg₂ (· + ·) (FiniteSum.Fin.sumFin_ite_eq first _) (FiniteSum.Fin.sumFin_ite_eq last _)).trans
      (sub_eq_add_neg _ _).symm))

end

open Purelib.Algebra in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
/-- Evaluate an integer matrix contraction on the two-coordinate energy probe.

The exact result retains the four matrix entries at the selected pair of indices, including both diagonal entries. -/
theorem contract_entryProbe {count : Nat} (matrix : Fin count → Fin count → Int) (first last : Fin count) :
    Surface.Word.Pairing.contract matrix (fun index => Energy.Polygon.energyPrimitivePoint (entryProbe first last
      index)) =
      ((matrix first first : Gaussian.Basic.Canonical) - (matrix last first : Gaussian.Basic.Canonical) * (⟨0, 1⟩ :
        Gaussian.Basic.Canonical)) +
      ((matrix first last : Gaussian.Basic.Canonical) - (matrix last last : Gaussian.Basic.Canonical) * (⟨0, 1⟩ :
        Gaussian.Basic.Canonical)) * (⟨0, 1⟩ : Gaussian.Basic.Canonical) := by
  have inner (row : Fin count) := sum_entryProbe first last
    (fun column => (matrix row column : Gaussian.Basic.Canonical) * Data.Gaussian.Basic.conj (entryProbe first last
      row))
  change FiniteSum.Fin.sumFin (fun row => FiniteSum.Fin.sumFin (fun column => (matrix row column :
    Gaussian.Basic.Canonical) *
    Data.Gaussian.Basic.conj (entryProbe first last row) * entryProbe first last column)) = _
  rw [FiniteSum.Fin.sumFin_congr inner, FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_mul_right, sum_conj_entryProbe,
    sum_conj_entryProbe]

section
open Purelib.Integration
open Purelib.Topology
open Purelib.Data
/-- A skew integer matrix's energy-probe contraction equals twice i times its selected entry.

Skewness forces the diagonal entries to vanish and identifies the two off-diagonal terms. -/
theorem contract_entryProbe_skew {count : Nat} (matrix : Fin count → Fin count → Int)
    (skew : ∀ first last, matrix first last = -matrix last first) (first last : Fin count) :
    Surface.Word.Pairing.contract matrix (fun index => Energy.Polygon.energyPrimitivePoint (entryProbe first last
      index)) =
      (⟨0, 2⟩ : Gaussian.Basic.Canonical) * (matrix first last : Gaussian.Basic.Canonical) := by
  have diagonal (index : Fin count) : matrix index index = 0 := by
    have equal := skew index index
    omega
  have negativeCast : ((-matrix first last : Int) : Gaussian.Basic.Canonical) = -(matrix first last :
    Gaussian.Basic.Canonical) := by
    change ((Int.neg (matrix first last) : Int) : Gaussian.Basic.Canonical) = _
    exact Purelib.Algebra.Ring.IntCast.neg _
  rw [contract_entryProbe, diagonal first, diagonal last, skew last first, negativeCast,
    Purelib.Algebra.Ring.IntCast.cast_zero]
  have twice : (2 : Gaussian.Basic.Canonical) * (⟨0, 1⟩ : Gaussian.Basic.Canonical) = ⟨0, 2⟩ := by decide
  rw [← twice]
  ring1
/-- Equal two-coordinate probe contractions give equal selected entries of two skew integer matrices.

The exact Gaussian factor twice i is canceled, and injectivity of the rational integer cast recovers the integer entry.
-/
theorem entry_eq_of_probe {count : Nat} (firstMatrix lastMatrix : Fin count → Fin count → Int)
    (firstSkew : ∀ first last, firstMatrix first last = -firstMatrix last first)
    (lastSkew : ∀ first last, lastMatrix first last = -lastMatrix last first)
    (first last : Fin count)
    (equal : Surface.Word.Pairing.contract firstMatrix (fun index => Energy.Polygon.energyPrimitivePoint (entryProbe
      first last index)) =
      Surface.Word.Pairing.contract lastMatrix (fun index => Energy.Polygon.energyPrimitivePoint (entryProbe first last
        index))) :
    firstMatrix first last = lastMatrix first last := by
  rw [contract_entryProbe_skew firstMatrix firstSkew, contract_entryProbe_skew lastMatrix lastSkew] at equal
  have scaled := congrArg (fun value : Gaussian.Basic.Canonical => (⟨0, -(1 / 2)⟩ : Gaussian.Basic.Canonical) * value)
    equal
  have cancel (value : Gaussian.Basic.Canonical) :
      (⟨0, -(1 / 2)⟩ : Gaussian.Basic.Canonical) * ((⟨0, 2⟩ : Gaussian.Basic.Canonical) * value) = value := by
    rw [← mul_assoc]
    have scalar : (⟨0, -(1 / 2)⟩ : Gaussian.Basic.Canonical) * (⟨0, 2⟩ : Gaussian.Basic.Canonical) = 1 := by decide
    rw [scalar, one_mul]
  have castEqual := (cancel _).symm.trans (scaled.trans (cancel _))
  apply Rat.Fraction.Cast.Compatibility.intCast_injective_direct
  exact (Gaussian.Cast.gaussian_int_re _).symm.trans
    ((congrArg Gaussian.Basic.re castEqual).trans (Gaussian.Cast.gaussian_int_re _))

end

open Purelib.Algebra
open Purelib.Topology
/-- Pointwise equal integer matrices have equal contractions on the same primitive values. -/
theorem contract_congr {count : Nat} {first last : Fin count → Fin count → Int}
    (equal : ∀ row column, first row column = last row column) (values : Fin count → PrimitivePoint) :
    Surface.Word.Pairing.contract first values = Surface.Word.Pairing.contract last values := by
  apply FiniteSum.Fin.sumFin_congr
  intro row
  apply FiniteSum.Fin.sumFin_congr
  intro column
  rw [equal]

/-- A finite sum of integer matrices contracts to the sum of their individual contractions. -/
theorem contract_sum {count terms : Nat} (matrices : Fin terms → Fin count → Fin count → Int)
    (values : Fin count → PrimitivePoint) :
    Surface.Word.Pairing.contract (fun first last => FiniteSum.Fin.sumFin (fun term => matrices term first last)) values
      =
      FiniteSum.Fin.sumFin (fun term => Surface.Word.Pairing.contract (matrices term) values) := by
  induction terms with
  | zero => exact Surface.Word.Pairing.contract_zero values
  | succ terms ih =>
      apply (contract_congr (fun row column => FiniteSum.Fin.sumFin_succ
        (fun term => matrices term row column)) values).trans
      rw [Surface.Word.Pairing.contract_add, ih, FiniteSum.Fin.sumFin_succ]

end Purelib.Riemann.Readings.EnergyMatrixEntries
