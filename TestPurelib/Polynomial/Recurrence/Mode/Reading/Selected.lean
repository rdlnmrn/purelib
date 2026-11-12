module

import Purelib.Polynomial.Recurrence.Mode.Reading.Selected
import Purelib.Algebra.Monogenic.Coordinates.Reading
import Purelib.Polynomial.Dense.Companion.Adjunction
import Purelib.Data.Gaussian.Field

/-!
# Selected repeated and zero modes under an actual nonmultiplicative reading

The original quadratic coefficient algebra contains an exact root of one
quarter and has zero divisors. Its same root is repeated in a cubic bank
alongside zero. A nearby nonroot Gaussian reading pays one source-fixed
schedule for all selected generalized occurrences; an empty selection
retains the positive default endpoint tolerance.
-/

namespace TestPurelib.Polynomial.Recurrence.Mode.Reading.Selected

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense (Companion)
open Purelib.Polynomial.Dense.Roots
open Purelib.Polynomial.Recurrence
open Purelib.Polynomial.Recurrence.Mode.Reading (Selected)
open Purelib.Algebra.Monogenic (Cyclic)
open Purelib.Algebra.Ring (GaussianReading)
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix

/-- The original quadratic retains the formal relation `r^2=1/4`. -/
private def quadratic : DensePolynomial Canonical := ⟨[1, 0, -(1 / 4)]⟩

/-- The actual original companion and adjunction produce the same finite coefficient algebra. -/
private def adjunction := (Companion.ofUnit quadratic (by decide +kernel) 1 (by decide +kernel)).adjoin

/-- The actual formal coefficient carrier is the original cyclic element algebra. -/
private abbrev Scalar := Cyclic.Element adjunction.table

/-- The same original formal root occurs twice and the original zero root occurs once. -/
private def blocks : List (Block Scalar) := [⟨adjunction.root, 2, by decide⟩, ⟨0, 1, by decide⟩]

/-- The actual cubic retains precisely those repeated and transient modes. -/
private def source : DensePolynomial Scalar := ⟨[1, -2 * adjunction.root, adjunction.root ^ 2, 0]⟩

/-- The original root relation supplies both ordered root-difference inverses. -/
private def differences : SquareMatrix Scalar blocks.length :=
  .cons (.cons 0 (.cons (4 * adjunction.root) .nil))
    (.cons (.cons (-4 * adjunction.root) (.cons 0 .nil)) .nil)

/-- Both original ordered root differences have the displayed actual unit inverses. -/
private theorem difference_units : ∀ first second : Fin blocks.length, first ≠ second →
    ((blocks[first.val]'first.isLt).point - (blocks[second.val]'second.isLt).point) *
      differences first second = 1 := by
  intro first
  refine Fin.cases ?_ ?_ first
  · intro second
    refine Fin.cases ?_ ?_ second
    · intro different
      exact (different rfl).elim
    · intro second
      refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) second
      intro _
      change adjunction.root * (4 * adjunction.root) = 1
      decide +kernel
  · intro first
    refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) first
    intro second
    refine Fin.cases ?_ ?_ second
    · intro _
      change (0 - adjunction.root) * (-4 * adjunction.root) = 1
      decide +kernel
    · intro second
      refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) second
      intro different
      exact (different rfl).elim

/-- The original block multiplicities exhaust the independently displayed cubic degree. -/
private theorem degree : totalMultiplicity blocks = source.natDegree := by decide +kernel

/-- The actual independent cubic coefficient table is precisely the displayed original repeated-root product. -/
private theorem factorization : source.normalize = DensePolynomial.scale source.leadingCoeff (product blocks) :=
  by decide +kernel

/-- The original cubic bank retains those same literal degree, coefficient and difference certificates. -/
private def bank : Bank source where
  blocks := blocks
  count_eq := degree
  monicProduct := product blocks
  product_eq := rfl
  factorization := factorization
  differenceInverses := differences
  difference_unit := difference_units

/-- Every original block is selected through the original weighted-word producer. -/
private def selection := Word.Selection.prepare bank (vectorOfFn fun _ => true)

/-- The same original occurrence cache supplies both repeated generalized orders and the zero startup order. -/
private def occurrences := Occurrences.prepare selection.word

/-- The fixed original-block quadrance ceilings are chosen before observing the reading. -/
private def ceilings : Vec Rational bank.blocks.length := .cons (1 / 4) (.cons 0 .nil)

/-- The original cyclic gain and radius are fixed independently of the candidate. -/
private def cyclicParameters :=
  Cyclic.Element.Reading.Parameters.prepare adjunction.table Norm.weight 1 1 (by decide) (by decide)

/-- One original schedule retains all three mode requests before any candidate observation. -/
private def schedule := Selected.prepare selection occurrences
  (Cyclic.Element.weight adjunction.table Norm.weight) cyclicParameters.gain cyclicParameters.gain_nonnegative
  ceilings (by decide +kernel) (by decide +kernel) 1 (by decide) 2

/-- The actual selected word and generalized orders preserve the independent expected original coordinates. -/
private theorem original_orders :
    selection.word.map Fin.val = [0, 0, 1] ∧
      List.ofFn (fun column => occurrences.orders column) = [0, 1, 0] := by decide +kernel

/-- The original coefficient algebra has actual zero divisors, rather than a field interpretation. -/
private theorem zero_divisors :
    (2 * adjunction.root - 1) * (2 * adjunction.root + 1) = 0 ∧
      2 * adjunction.root - 1 ≠ 0 ∧ 2 * adjunction.root + 1 ≠ 0 := by decide +kernel

/-- A nearby nonroot is selected only after all original finite mode requests have been fixed. -/
private def candidate : Canonical := ⟨1 / 2 - 1 / (2 : Rational) ^ 256, 0⟩

/-- The same original source evaluator computes the actual candidate residual. -/
private def residual := Norm.Basic.normSq (quadratic.eval candidate)

/-- The actual original cyclic constructor retains a genuinely nonmultiplicative reading. -/
private def reading := cyclicParameters.toReading GaussianReading.identity rfl candidate (by decide +kernel)
  residual (Norm.Basic.normSq_nonneg _) (by decide +kernel)

/-- The same formal root reads as the nonroot, with positive multiplication error and a failed squared reading. -/
private theorem actual_reading :
    reading.read adjunction.root = candidate ∧ 0 < reading.error ∧
      reading.read (adjunction.root ^ 2) ≠ reading.read adjunction.root ^ 2 := by decide +kernel

/-- The actual reading pays the independently prepared common original endpoint tolerance. -/
private theorem paid : reading.error ≤ schedule.tolerance := by decide +kernel

/-- The repeated-root generalized mode pays the common request throughout its actual finite tail. -/
private theorem repeated_tail (offset : Fin 2) :
    Norm.Basic.normSq (reading.read (Mode.window adjunction.root 1
      ((schedule.entryAt ⟨1, by decide⟩).inside.index + 2)
      ((schedule.entryAt ⟨1, by decide⟩).index offset))) < 1 :=
  schedule.window_lt reading rfl paid ⟨1, by decide⟩ (by decide +kernel) offset

/-- The same actual zero-root transient is controlled without dropping its selected original column. -/
private theorem zero_tail (offset : Fin 2) :
    Norm.Basic.normSq (reading.read (Mode.window (0 : Scalar) 0
      ((schedule.entryAt ⟨2, by decide⟩).inside.index + 2)
      ((schedule.entryAt ⟨2, by decide⟩).index offset))) < 1 :=
  schedule.window_lt reading rfl paid ⟨2, by decide⟩ (by decide +kernel) offset

/-- An empty original selection uses the same bank and performs no per-mode request construction. -/
private def emptySelection := Word.Selection.prepare bank (vectorOfFn fun _ => false)

/-- The original empty-word occurrence cache is retained directly. -/
private def emptyOccurrences := Occurrences.prepare emptySelection.word

/-- The actual empty schedule still has a positive source-fixed endpoint tolerance. -/
private def emptySchedule := Selected.prepare emptySelection emptyOccurrences
  (Cyclic.Element.weight adjunction.table Norm.weight) cyclicParameters.gain cyclicParameters.gain_nonnegative
  ceilings (by decide +kernel) (by decide +kernel) 1 (by decide) 2

/-- The empty original word has no displayed requests and retains the independently expected default one. -/
private theorem empty_default :
    emptySelection.word = [] ∧ emptySchedule.tolerances = [] ∧ emptySchedule.tolerance = 1 := by decide +kernel

end TestPurelib.Polynomial.Recurrence.Mode.Reading.Selected
