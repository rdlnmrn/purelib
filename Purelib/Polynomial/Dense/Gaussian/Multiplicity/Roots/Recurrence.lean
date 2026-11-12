module

public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Bank
public import Purelib.Polynomial.Recurrence.Mode.Hermite.Solution
public import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Companion
import Purelib.Polynomial.Dense.Map.Ring
import Purelib.Polynomial.Dense.Roots.Word
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Complete source recurrences in the original prepared root-bank basis

The same original positive multiplicity input supplies a mapped leading unit
and its actual source companion. One original full word and Hermite inverse
give complete finite recurrence coordinates. Selected or padded boundary
bases do not replace the original full characteristic basis.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.Vector
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Roots
open Purelib.Polynomial.Recurrence
open Purelib.LinearAlgebra.Matrix

variable {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}

namespace Recurrence

/-- The original prepared source has the same positive degree in its retained final coefficient algebra. -/
theorem degree_eq (prepared : Prepared input) : prepared.mapped.natDegree = source.natDegree :=
  (congrArg DensePolynomial.natDegree prepared.mapped_eq).trans
    (Map.map_natDegree (Stages.Images.coefficientMap prepared.separation.prepared.stages)
      (Stages.Images.coefficientMap_zero _ rfl)
      (Stages.Images.coefficientMap_injective _ (fun _ _ equal => equal)) source)

/-- The original positive preprocessing proves that same mapped source has positive degree. -/
theorem positive (prepared : Prepared input) : 0 < prepared.mapped.natDegree :=
  (degree_eq prepared).symm ▸ input.preprocessing.degreePositive

/-- The mapped source retains the image of the same original Gaussian leading coefficient. -/
theorem leading_eq (prepared : Prepared input) : prepared.mapped.leadingCoeff =
    Stages.Images.coefficientMap prepared.separation.prepared.stages source.leadingCoeff :=
  (congrArg DensePolynomial.leadingCoeff prepared.mapped_eq).trans
    (Map.map_leadingCoeff (Stages.Images.coefficientMap prepared.separation.prepared.stages)
      (Stages.Images.coefficientMap_zero _ rfl)
      (Stages.Images.coefficientMap_injective _ (fun _ _ equal => equal)) source)

/-- Mapping the same original Gaussian leading reciprocal gives an actual unit in the retained final algebra. -/
theorem leading_unit (prepared : Prepared input) (coefficientInverse : Canonical)
    (coefficientInverseEq : coefficientInverse = source.leadingCoeff⁻¹)
    (inverse : prepared.separation.Scalar)
    (inverseEq : inverse = Stages.Images.coefficientMap prepared.separation.prepared.stages coefficientInverse) :
    prepared.mapped.leadingCoeff * inverse = 1 := by
  cases coefficientInverseEq
  rewrite [leading_eq prepared, inverseEq]
  exact (Stages.Images.coefficientMap_mul _ (fun _ _ => rfl) _ _).symm.trans
    ((congrArg (Stages.Images.coefficientMap prepared.separation.prepared.stages)
      (Canonical.mul_inv_cancel _ (DensePolynomial.leadingCoeff_ne_zero input.preprocessing.nonzero))).trans
        (Stages.Images.coefficientMap_one _ rfl))

/-- The original full Hermite owner at a retained word over this same prepared bank. -/
abbrev Basis (prepared : Prepared input) (word : List (Fin prepared.bank.blocks.length)) :=
  Mode.Hermite prepared.bank.blocks prepared.bank.differenceInverses word

/-- Complete agreement with the original automatic full-bank basis at the same retained word.

The word equality transports only its original finite bounds. The equation
compares the full original Hermite value, including the actual matrix and
scaled inverse, rather than a list of selected scalar readbacks.
-/
abbrev BasisEquation (prepared : Prepared input) (word : List (Fin prepared.bank.blocks.length))
    (wordEq : word = Word.expand prepared.bank.blocks) (basis : Basis prepared word) : Prop :=
  basis = (show Basis prepared word from wordEq.symm ▸ Mode.Hermite.ofBank prepared.bank)

end Recurrence

set_option genInjectivity false in
/-- The actual source companion and complete characteristic basis of the same original prepared bank.

The original Gaussian leading inverse and its mapped image are materialized
once. The original companion, full word and complete Hermite inverse retain
their canonical constructor equalities. All finite-horizon operations consume
those exact caches, without rebuilding roots or a selected boundary basis.
-/
structure Recurrence (prepared : Prepared input) where
  /-- The original source-leading Gaussian reciprocal computed once. -/
  coefficientInverse : Canonical
  /-- The reciprocal belongs to the same original source leading coefficient. -/
  coefficientInverse_eq : coefficientInverse = source.leadingCoeff⁻¹
  /-- The once-mapped original leading reciprocal in the retained final coefficient algebra. -/
  leadingInverse : prepared.separation.Scalar
  /-- The inverse uses the same original stage coefficient map and retained Gaussian reciprocal. -/
  leadingInverse_eq : leadingInverse =
    Stages.Images.coefficientMap prepared.separation.prepared.stages coefficientInverse
  /-- The same retained leading coefficient and reciprocal are an actual unit pair. -/
  leadingUnit : prepared.mapped.leadingCoeff * leadingInverse = 1
  /-- The actual original companion of the same full mapped source. -/
  companion : Companion prepared.mapped
  /-- The original companion consumes the same retained mapped leading reciprocal. -/
  companion_eq : companion = Companion.ofUnit prepared.mapped (Recurrence.positive prepared) leadingInverse leadingUnit
  /-- The original full characteristic word is materialized once. -/
  fullWord : List (Fin prepared.bank.blocks.length)
  /-- The retained word is precisely the full original multiplicity expansion. -/
  fullWord_eq : fullWord = Word.expand prepared.bank.blocks
  /-- The same original complete Hermite matrix and inverse at the retained full word. -/
  basis : Recurrence.Basis prepared fullWord
  /-- The complete basis is the same original automatic full-bank producer. -/
  basis_eq : Recurrence.BasisEquation prepared fullWord fullWord_eq basis

constructive_injectivity Recurrence

namespace Recurrence

/-- Retain checked original leading, companion, full-word and basis caches without rerunning their producers. -/
@[expose] def ofCaches (prepared : Prepared input) (coefficientInverse : Canonical)
    (coefficientInverseEq : coefficientInverse = source.leadingCoeff⁻¹)
    (inverse : prepared.separation.Scalar)
    (inverseEq : inverse = Stages.Images.coefficientMap prepared.separation.prepared.stages coefficientInverse)
    (unit : prepared.mapped.leadingCoeff * inverse = 1) (companion : Companion prepared.mapped)
    (companionEq : companion = Companion.ofUnit prepared.mapped (positive prepared) inverse unit)
    (word : List (Fin prepared.bank.blocks.length)) (wordEq : word = Word.expand prepared.bank.blocks)
    (basis : Basis prepared word) (basisEq : BasisEquation prepared word wordEq basis) : Recurrence prepared :=
  { coefficientInverse, coefficientInverse_eq := coefficientInverseEq, leadingInverse := inverse
    leadingInverse_eq := inverseEq, leadingUnit := unit, companion, companion_eq := companionEq
    fullWord := word, fullWord_eq := wordEq, basis, basis_eq := basisEq }

/-- Prepare the original source companion and full characteristic basis from a retained original word.

The same original Gaussian leading reciprocal is mapped once. The actual
full word is supplied with its original expansion equation. The original
Hermite producer consumes that retained word directly, without expanding it
again; its complete canonical equality is proof-only.
-/
@[expose] def ofWord (prepared : Prepared input) (word : List (Fin prepared.bank.blocks.length))
    (wordEq : word = Word.expand prepared.bank.blocks) : Recurrence prepared :=
  let coefficientInverse := source.leadingCoeff⁻¹
  let inverse := Stages.Images.coefficientMap prepared.separation.prepared.stages coefficientInverse
  let unit := leading_unit prepared coefficientInverse rfl inverse rfl
  let companion := Companion.ofUnit prepared.mapped (positive prepared) inverse unit
  let basis := Mode.Hermite.prepare prepared.bank.blocks prepared.bank.differenceInverses
    prepared.bank.difference_unit word
  ofCaches prepared coefficientInverse rfl inverse rfl unit companion rfl word wordEq basis (by
    cases wordEq
    rfl)

/-- Prepare the original full-source recurrence companion and one complete characteristic basis. -/
@[expose] def prepare (prepared : Prepared input) : Recurrence prepared :=
  ofWord prepared (Word.expand prepared.bank.blocks) rfl

/-- A checked retained full word gives the complete same original automatic recurrence construction. -/
theorem ofWord_eq_prepare (prepared : Prepared input) (word : List (Fin prepared.bank.blocks.length))
    (wordEq : word = Word.expand prepared.bank.blocks) : ofWord prepared word wordEq = prepare prepared := by
  cases wordEq
  rfl

/-- The actual full-source constructor retains the supplied original word without repeating its expansion. -/
theorem ofWord_fullWord (prepared : Prepared input) (word : List (Fin prepared.bank.blocks.length))
    (wordEq : word = Word.expand prepared.bank.blocks) : (ofWord prepared word wordEq).fullWord = word := rfl

variable {prepared : Prepared input}

/-- The retained companion uses that same actual mapped source-leading inverse. -/
theorem companion_inverse (retained : Recurrence prepared) :
    retained.companion.leadingInverse = retained.leadingInverse :=
  (congrArg Companion.leadingInverse retained.companion_eq).trans (Companion.ofUnit_leadingInverse _ _ _ _)

/-- The actual full characteristic word has exactly the same original mapped source degree. -/
theorem full_count (retained : Recurrence prepared) : retained.fullWord.length = prepared.mapped.natDegree :=
  (congrArg List.length retained.fullWord_eq).trans (Mode.Hermite.ofBank_count prepared.bank)

/-- The same actual full characteristic word also retains the original Gaussian source degree. -/
theorem source_count (retained : Recurrence prepared) : retained.fullWord.length = source.natDegree :=
  retained.full_count.trans (degree_eq prepared)

/-- Each retained original generalized order is below the same original full-bank block multiplicity. -/
theorem order_lt (retained : Recurrence prepared) (column : Fin retained.fullWord.length) :
    retained.basis.occurrences.orders column <
      (prepared.bank.block (retained.fullWord[column.val]'column.isLt)).multiplicity := by
  cases retained with
  | mk coefficientInverse coefficientInverseEq inverse inverseEq unit companion companionEq word wordEq basis basisEq =>
      cases wordEq
      cases basisEq
      exact Mode.Hermite.ofBank_order_lt prepared.bank column

/-- Every finite combination of the same complete source-basis columns satisfies the original source companion. -/
theorem horizon_satisfies (retained : Recurrence prepared) (count : Nat)
    (coefficients : Vec prepared.separation.Scalar retained.fullWord.length) :
    retained.companion.Satisfies (Rectangular.apply (retained.basis.horizon count) coefficients) :=
  Mode.Hermite.horizon_satisfies prepared.bank retained.companion retained.basis retained.order_lt count coefficients

/-- The same full initial inverse reconstructs every complete finite source recurrence solution. -/
theorem horizon_reconstruct (retained : Recurrence prepared) {count : Nat}
    (values : Vec prepared.separation.Scalar count) (enough : retained.fullWord.length ≤ count)
    (equations : retained.companion.Satisfies values) :
    Rectangular.apply (retained.basis.horizon count)
      (retained.basis.coordinates (Split.take enough values)) = values :=
  Mode.Hermite.horizon_reconstruct prepared.bank retained.companion retained.basis retained.full_count
    retained.order_lt values enough equations

/-- The same complete source basis reconstructs every finite horizon, including shorter original prefixes. -/
theorem horizon_reconstruct_any (retained : Recurrence prepared) {count : Nat}
    (values : Vec prepared.separation.Scalar count) (equations : retained.companion.Satisfies values) :
    Rectangular.apply (retained.basis.horizon count) (retained.basis.coordinatesOfHorizon values) = values :=
  Mode.Hermite.horizon_reconstruct_any prepared.bank retained.companion retained.basis retained.full_count
    retained.order_lt values equations

/-- Equal finite full-source mode combinations determine their same original coefficient vectors uniquely. -/
theorem horizon_independent (retained : Recurrence prepared) (count : Nat) (enough : retained.fullWord.length ≤ count)
    (first second : Vec prepared.separation.Scalar retained.fullWord.length)
    (equal : Rectangular.apply (retained.basis.horizon count) first =
      Rectangular.apply (retained.basis.horizon count) second) : first = second :=
  retained.basis.horizon_independent count enough first second equal

/-- Checked original caches recover the complete original full-source recurrence construction. -/
theorem ofCaches_eq_prepare (prepared : Prepared input) (coefficientInverse : Canonical)
    (coefficientInverseEq : coefficientInverse = source.leadingCoeff⁻¹)
    (inverse : prepared.separation.Scalar)
    (inverseEq : inverse = Stages.Images.coefficientMap prepared.separation.prepared.stages coefficientInverse)
    (unit : prepared.mapped.leadingCoeff * inverse = 1) (companion : Companion prepared.mapped)
    (companionEq : companion = Companion.ofUnit prepared.mapped (positive prepared) inverse unit)
    (word : List (Fin prepared.bank.blocks.length)) (wordEq : word = Word.expand prepared.bank.blocks)
    (basis : Basis prepared word) (basisEq : BasisEquation prepared word wordEq basis) :
    ofCaches prepared coefficientInverse coefficientInverseEq inverse inverseEq unit companion companionEq
      word wordEq basis basisEq = prepare prepared := by
  cases coefficientInverseEq
  cases inverseEq
  cases companionEq
  cases wordEq
  cases basisEq
  rfl

/-- The complete retained full-source recurrence cache restores its same original preparation. -/
theorem restore (retained : Recurrence prepared) : retained = prepare prepared := by
  cases retained with
  | mk coefficientInverse coefficientInverseEq inverse inverseEq unit companion companionEq word wordEq basis basisEq =>
      exact ofCaches_eq_prepare prepared coefficientInverse coefficientInverseEq inverse inverseEq unit
        companion companionEq word wordEq basis basisEq

end Recurrence
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots

end
