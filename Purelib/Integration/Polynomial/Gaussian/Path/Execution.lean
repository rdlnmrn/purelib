module
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Fold
public import Purelib.Data.List.Split.Alternating
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
import Purelib.Tactic.Ring

section
public section

/-!
# Progressive finite integration with Gaussian coefficients

This is the period-facing integration kernel.  Every model is still a finite
list of rationally parameterized cells, but its local polynomial coefficients
are Gaussian rationals.  Hence a cell can approximate a genuinely complex
coefficient before multiplication by the complex path displacement.
-/

namespace Purelib.Integration.Polynomial.Gaussian.Path.Basic
namespace PathModel

open Purelib.Data.List.Split

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Accumulate the original path cells' integral samples with a left fold from zero. -/
@[expose] def tailIntegralSample (path :
  Basic.PathModel) : Basic.Canonical :=
  path.cells.foldl (fun total cell => total + cell.integralSample) 0

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- The original integral-sample left fold equals its initial accumulator plus the original right-fold sum. -/
private theorem foldl_integralSample_eq : forall
    (cells : List Basic.CellModel) (initial : Basic.Canonical),
    cells.foldl (fun total cell => total + cell.integralSample) initial =
      initial + cells.foldr (fun cell total => cell.integralSample + total) 0
  | [], initial => by
      simp only [List.foldl_nil, List.foldr_nil]
      exact (Basic.add_zero initial).symm
  | cell :: cells, initial => by
      change
        cells.foldl (fun total cell => total + cell.integralSample)
            (initial + cell.integralSample) =
          initial +
            (cell.integralSample +
              cells.foldr (fun cell total => cell.integralSample + total) 0)
      rw [foldl_integralSample_eq cells]
      apply Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im] <;> ring1

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The original path integral sample equals its tail-recursive accumulation. -/
theorem integralSample_eq_tailIntegralSample (path :
  Basic.PathModel) :
    path.integralSample = path.tailIntegralSample := by
  unfold Basic.PathModel.integralSample tailIntegralSample
  rw [foldl_integralSample_eq path.cells 0]
  exact (Basic.zero_add _).symm

section
open Purelib.Data.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Cell
/-- Accumulate model samples directly over the original input list with a left fold.

The original model function is evaluated at each retained entry without constructing an intermediate mapped cell list.
-/
@[expose] def tailMappedIntegralSample {Data : Type}
    (values : List Data) (model : Data -> Basic.CellModel) : Basic.Canonical :=
  values.foldl (fun total value => total + (model value).integralSample) 0

/-- Mapping the original models before sample accumulation equals accumulating their samples directly. -/
private theorem foldl_integralSample_map {Data :
  Type}
    (model : Data -> Basic.CellModel) :
    forall (values : List Data) (initial : Basic.Canonical),
      (values.map model).foldl
          (fun total cell => total + cell.integralSample) initial =
        values.foldl
          (fun total value => total + (model value).integralSample) initial
  | [], _initial => rfl
  | _value :: remaining, initial =>
      foldl_integralSample_map model remaining
        (initial + (model _value).integralSample)

end

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The mapped original path's tail-recursive sample equals direct accumulation over the original data. -/
theorem tailIntegralSample_map {Data : Type}
    (values : List Data) (model : Data -> Basic.CellModel) :
    (Basic.PathModel.mk (values.map model)).tailIntegralSample =
      tailMappedIntegralSample values model := by
  unfold tailIntegralSample tailMappedIntegralSample
  exact foldl_integralSample_map model values 0

open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Accumulate the original path cells' weighted allowances with a left fold from zero. -/
@[expose] def tailTotalWeightedAllowance (path :
  Basic.PathModel) : Fraction.Rational :=
  path.cells.foldl (fun total cell => total + cell.weightedAllowance) 0

section
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Cell
/-- Accumulate weighted allowances directly over the original input list with a left fold. -/
@[expose] def tailMappedWeightedAllowance {Data :
  Type}
    (values : List Data) (model : Data -> Basic.CellModel) : Fraction.Rational :=
  values.foldl (fun total value => total + (model value).weightedAllowance) 0

/-- Mapping original cell models before allowance accumulation equals direct accumulation over the original data. -/
private theorem foldl_weightedAllowance_map {Data :
  Type}
    (model : Data -> Basic.CellModel) :
    forall (values : List Data) (initial : Fraction.Rational),
      (values.map model).foldl
          (fun total cell => total + cell.weightedAllowance) initial =
        values.foldl
          (fun total value => total + (model value).weightedAllowance) initial
  | [], _initial => rfl
  | value :: remaining, initial =>
      foldl_weightedAllowance_map model remaining
        (initial + (model value).weightedAllowance)

end

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The mapped original path's tail-recursive allowance equals direct mapped allowance accumulation. -/
theorem tailTotalWeightedAllowance_map {Data : Type}
    (values : List Data) (model : Data -> Basic.CellModel) :
    (Basic.PathModel.mk (values.map model)).tailTotalWeightedAllowance =
      tailMappedWeightedAllowance values model := by
  unfold tailTotalWeightedAllowance tailMappedWeightedAllowance
  exact foldl_weightedAllowance_map model values 0

open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The original mapped allowance fold equals its initial accumulator plus its zero-based accumulation. -/
private theorem foldl_mappedWeightedAllowance_eq
  {Data : Type}
    (model : Data -> Basic.CellModel) :
    forall (values : List Data) (initial : Fraction.Rational),
      values.foldl
          (fun total value => total + (model value).weightedAllowance) initial =
        initial + tailMappedWeightedAllowance values model
  | [], initial => by
      unfold tailMappedWeightedAllowance
      simp only [List.foldl_nil]
      exact (_root_.add_zero initial).symm
  | value :: remaining, initial => by
      change
        remaining.foldl
            (fun total value => total + (model value).weightedAllowance)
            (initial + (model value).weightedAllowance) =
          initial +
            remaining.foldl
              (fun total value => total + (model value).weightedAllowance)
              (0 + (model value).weightedAllowance)
      rw [foldl_mappedWeightedAllowance_eq model remaining,
        foldl_mappedWeightedAllowance_eq model remaining]
      ring1

open Purelib.Data.List in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Allowance accumulation over concatenated original data equals the sum of the two original accumulations. -/
theorem tailMappedWeightedAllowance_append {Data :
  Type}
    (first second : List Data) (model : Data -> Basic.CellModel) :
    tailMappedWeightedAllowance (first ++ second) model =
      tailMappedWeightedAllowance first model +
        tailMappedWeightedAllowance second model := by
  change
    (first ++ second).foldl
        (fun total value => total + (model value).weightedAllowance) 0 =
      first.foldl
          (fun total value => total + (model value).weightedAllowance) 0 +
        second.foldl
          (fun total value => total + (model value).weightedAllowance) 0
  rw [Fold.foldl_append,
    foldl_mappedWeightedAllowance_eq model second,
    foldl_mappedWeightedAllowance_eq model second]
  ring1

section
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Prepending an original entry adds its model's weighted allowance to the retained tail accumulation. -/
private theorem tailMappedWeightedAllowance_cons
  {Data : Type}
    (value : Data) (remaining : List Data) (model : Data -> Basic.CellModel) :
    tailMappedWeightedAllowance (value :: remaining) model =
      (model value).weightedAllowance +
        tailMappedWeightedAllowance remaining model := by
  change
    remaining.foldl
        (fun total value => total + (model value).weightedAllowance)
        (0 + (model value).weightedAllowance) =
      (model value).weightedAllowance +
        remaining.foldl
          (fun total value => total + (model value).weightedAllowance) 0
  rw [foldl_mappedWeightedAllowance_eq model remaining,
    foldl_mappedWeightedAllowance_eq model remaining]
  ring1

/-- The original alternating split preserves the sum of mapped weighted allowances. -/
private theorem alternatingSplit_allowance {Data :
  Type}
    (model : Data -> Basic.CellModel) : forall (values : List Data),
    tailMappedWeightedAllowance (Alternating.split values).1 model +
        tailMappedWeightedAllowance (Alternating.split values).2 model =
      tailMappedWeightedAllowance values model
  | [] => by
      simp only [Alternating.split]
      unfold tailMappedWeightedAllowance
      simp only [List.foldl_nil]
      ring1
  | [value] => by
      simp only [Alternating.split, tailMappedWeightedAllowance_cons]
      unfold tailMappedWeightedAllowance
      simp only [List.foldl_nil]
      ring1
  | first :: second :: remaining => by
      have tail := alternatingSplit_allowance model
        remaining
      simp only [Alternating.split, tailMappedWeightedAllowance_cons]
      calc
        (model first).weightedAllowance +
              tailMappedWeightedAllowance (Alternating.split remaining).1 model +
            ((model second).weightedAllowance +
              tailMappedWeightedAllowance
                (Alternating.split remaining).2 model) =
            (model first).weightedAllowance +
              (model second).weightedAllowance +
                (tailMappedWeightedAllowance
                    (Alternating.split remaining).1 model +
                  tailMappedWeightedAllowance
                    (Alternating.split remaining).2 model) := by ring1
        _ = (model first).weightedAllowance +
              (model second).weightedAllowance +
                tailMappedWeightedAllowance remaining model := by rw [tail]
        _ = (model first).weightedAllowance +
              ((model second).weightedAllowance +
                tailMappedWeightedAllowance remaining model) := by ring1

end

open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Accumulate original mapped allowances through a fuel-bounded tree of alternating splits.

At zero fuel the exact remaining list uses tail accumulation; recursive branches retain the two original split lists and
unchanged model function. -/
@[expose] def balancedMappedWeightedAllowance {Data
  : Type} :
    Nat -> List Data -> (Data -> Basic.CellModel) -> Fraction.Rational
  | 0, values, model => tailMappedWeightedAllowance values model
  | fuel + 1, values, model =>
      let halves := Alternating.split values
      balancedMappedWeightedAllowance fuel halves.1 model +
        balancedMappedWeightedAllowance fuel halves.2 model

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Every fuel depth gives the same mapped allowance as direct accumulation of the original list. -/
theorem balancedMappedWeightedAllowance_eq {Data :
  Type}
    (model : Data -> Basic.CellModel) : forall (fuel : Nat) (values : List Data),
    balancedMappedWeightedAllowance fuel values model =
      tailMappedWeightedAllowance values model
  | 0, _values => rfl
  | fuel + 1, values => by
      change
        balancedMappedWeightedAllowance fuel
              (Alternating.split values).1 model +
            balancedMappedWeightedAllowance fuel
              (Alternating.split values).2 model =
          tailMappedWeightedAllowance values model
      rw [balancedMappedWeightedAllowance_eq model fuel,
        balancedMappedWeightedAllowance_eq model fuel]
      exact alternatingSplit_allowance model values

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The original mapped sample fold equals its initial accumulator plus its zero-based accumulation. -/
private theorem foldl_mappedIntegralSample_eq {Data
  : Type}
    (model : Data -> Basic.CellModel) :
    forall (values : List Data) (initial : Basic.Canonical),
      values.foldl
          (fun total value => total + (model value).integralSample) initial =
        initial + tailMappedIntegralSample values model
  | [], initial => by
      unfold tailMappedIntegralSample
      simp only [List.foldl_nil]
      exact (Basic.add_zero initial).symm
  | value :: remaining, initial => by
      change
        remaining.foldl
            (fun total value => total + (model value).integralSample)
            (initial + (model value).integralSample) =
          initial +
            remaining.foldl
              (fun total value => total + (model value).integralSample)
              (0 + (model value).integralSample)
      rw [foldl_mappedIntegralSample_eq model remaining,
        foldl_mappedIntegralSample_eq model remaining]
      apply Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im, Basic.zero_re, Basic.zero_im] <;> ring1

open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Sample accumulation over concatenated original data equals the sum of the two original accumulations. -/
theorem tailMappedIntegralSample_append {Data :
  Type}
    (first second : List Data) (model : Data -> Basic.CellModel) :
    tailMappedIntegralSample (first ++ second) model =
      tailMappedIntegralSample first model +
        tailMappedIntegralSample second model := by
  change
    (first ++ second).foldl
        (fun total value => total + (model value).integralSample) 0 =
      first.foldl
          (fun total value => total + (model value).integralSample) 0 +
        second.foldl
          (fun total value => total + (model value).integralSample) 0
  rw [Fold.foldl_append,
    foldl_mappedIntegralSample_eq model second,
    foldl_mappedIntegralSample_eq model second]
  apply Basic.ext <;>
    simp only [Basic.add_re, Basic.add_im, Basic.zero_re, Basic.zero_im] <;> ring1

section
open Purelib.Data.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Prepending an original entry adds its model sample to the retained tail accumulation. -/
private theorem tailMappedIntegralSample_cons {Data
  : Type}
    (value : Data) (remaining : List Data) (model : Data -> Basic.CellModel) :
    tailMappedIntegralSample (value :: remaining) model =
      (model value).integralSample +
        tailMappedIntegralSample remaining model := by
  change
    remaining.foldl
        (fun total value => total + (model value).integralSample)
        (0 + (model value).integralSample) =
      (model value).integralSample +
        remaining.foldl
          (fun total value => total + (model value).integralSample) 0
  rw [foldl_mappedIntegralSample_eq model remaining,
    foldl_mappedIntegralSample_eq model remaining]
  apply Basic.ext <;>
    simp only [Basic.add_re, Basic.add_im, Basic.zero_re, Basic.zero_im] <;> ring1

/-- The original alternating split preserves the sum of mapped integral samples. -/
private theorem alternatingSplit_integralSample
  {Data : Type}
    (model : Data -> Basic.CellModel) : forall (values : List Data),
    tailMappedIntegralSample (Alternating.split values).1 model +
        tailMappedIntegralSample (Alternating.split values).2 model =
      tailMappedIntegralSample values model
  | [] => by
      simp only [Alternating.split]
      unfold tailMappedIntegralSample
      simp only [List.foldl_nil]
      exact Basic.add_zero 0
  | [value] => by
      simp only [Alternating.split, tailMappedIntegralSample_cons]
      unfold tailMappedIntegralSample
      simp only [List.foldl_nil]
      apply Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im, Basic.zero_re, Basic.zero_im] <;> ring1
  | first :: second :: remaining => by
      have tail := alternatingSplit_integralSample model
        remaining
      simp only [Alternating.split, tailMappedIntegralSample_cons]
      rw [← tail]
      apply Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im] <;> ring1

/-- Accumulate original mapped samples through a fuel-bounded tree of alternating splits.

At zero fuel the exact remaining list uses tail accumulation; the original entries and model function remain unchanged
in both branches. -/
@[expose] def balancedMappedIntegralSample {Data :
  Type} :
    Nat -> List Data -> (Data -> Basic.CellModel) -> Basic.Canonical
  | 0, values, model => tailMappedIntegralSample values model
  | fuel + 1, values, model =>
      let halves := Alternating.split values
      balancedMappedIntegralSample fuel halves.1 model +
        balancedMappedIntegralSample fuel halves.2 model

end

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Every fuel depth gives the same mapped sample as direct accumulation of the original list. -/
theorem balancedMappedIntegralSample_eq {Data :
  Type}
    (model : Data -> Basic.CellModel) : forall (fuel : Nat) (values : List Data),
    balancedMappedIntegralSample fuel values model =
      tailMappedIntegralSample values model
  | 0, _values => rfl
  | fuel + 1, values => by
      change
        balancedMappedIntegralSample fuel
              (Alternating.split values).1 model +
            balancedMappedIntegralSample fuel
              (Alternating.split values).2 model =
          tailMappedIntegralSample values model
      rw [balancedMappedIntegralSample_eq model fuel,
        balancedMappedIntegralSample_eq model fuel]
      exact alternatingSplit_integralSample model values

open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The original cell allowance fold equals its initial accumulator plus the original weighted-allowance sum. -/
private theorem foldl_weightedAllowance_eq :
    forall (cells : List Basic.CellModel) (initial : Fraction.Rational),
      cells.foldl (fun total cell => total + cell.weightedAllowance) initial =
        initial + (Basic.PathModel.mk cells).totalWeightedAllowance
  | [], initial => by
      simp only [List.foldl_nil, Basic.PathModel.totalWeightedAllowance, List.foldr_nil]
      exact (_root_.add_zero initial).symm
  | cell :: remaining, initial => by
      simp only [List.foldl_cons]
      rw [foldl_weightedAllowance_eq remaining
        (initial + cell.weightedAllowance)]
      simp only [Basic.PathModel.totalWeightedAllowance, List.foldr_cons]
      ring1

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The original path's tail-recursive allowance equals its specified total weighted allowance. -/
theorem tailTotalWeightedAllowance_eq (path :
  Basic.PathModel) :
    path.tailTotalWeightedAllowance = path.totalWeightedAllowance := by
  unfold tailTotalWeightedAllowance
  rw [foldl_weightedAllowance_eq]
  exact _root_.zero_add path.totalWeightedAllowance

open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The original aggregate allowance is the exact cell count times its tail-recursive weighted allowance. -/
theorem aggregateAllowance_eq_tail (path :
  Basic.PathModel) :
    path.aggregateAllowance =
      (path.cells.length : Fraction.Rational) * path.tailTotalWeightedAllowance := by
  unfold Basic.PathModel.aggregateAllowance
  rw [path.tailTotalWeightedAllowance_eq]
end PathModel

end Purelib.Integration.Polynomial.Gaussian.Path.Basic

end

public section
namespace Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel

open Purelib.Integration.Polynomial.Gaussian
open Purelib.Data

/-- Equal model readbacks on a retained list give the same accumulated integral sample.

The original ordered entries and initial zero accumulator are retained. Equality is required only at those entries, so
no function equality or values outside the list are used. -/
theorem tailMappedIntegralSample_congr {Data : Type}
    (values : List Data)
    (first second : Data → Cell.Basic.CellModel)
    (equal : ∀ value ∈ values, first value = second value) :
    tailMappedIntegralSample
        values first =
      tailMappedIntegralSample
        values second := by
  unfold tailMappedIntegralSample
  have foldEqual : forall (remaining : List Data)
      (subset : ∀ value ∈ remaining, first value = second value)
      (initial : Gaussian.Basic.Canonical),
      remaining.foldl
          (fun total value => total + (first value).integralSample) initial =
        remaining.foldl
          (fun total value => total + (second value).integralSample) initial := by
    intro remaining
    induction remaining with
    | nil => intro _subset _initial; rfl
    | cons head tail induction =>
        intro subset initial
        rw [List.foldl_cons, List.foldl_cons,
          subset head (List.Mem.head _)]
        apply induction
        intro value membership
        exact subset value (List.Mem.tail _ membership)
  exact foldEqual values equal 0

end Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel
end
