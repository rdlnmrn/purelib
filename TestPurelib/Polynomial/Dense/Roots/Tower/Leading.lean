module

import Purelib.Polynomial.Dense.Roots.Tower.Leading
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Leading
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute
import Purelib.Polynomial.Dense.Companion.Adjunction.Reading
import Purelib.Polynomial.Dense.Division.Synthetic
import Purelib.Polynomial.Dense.Map.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.Monogenic.Coordinates.Reading
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.System.IO

/-!
# Nonmonic original tower inverses under nonmultiplicative readings

The original polynomial `2x²-2` produces its original two-stage tower. Its
first root algebra has the actual zero divisors `theta-1` and `theta+1`.
Reading at `3/4` has nonzero multiplication discrepancy, while the same
scalar-leading invariant prepares both original companion readings with
exact leading inverse `1/2` and no supplied inverse-image witness.
-/

namespace TestPurelib.Polynomial.Dense.Roots.Tower.Leading

open Purelib
open Polynomial.Dense.Basic (DensePolynomial)
open Data.Gaussian.Basic (Canonical)
open Data.Gaussian
open Data.Rat.Fraction (Rational)
open Data.Rat.Fraction.Order
open Algebra.Monogenic
open Algebra.FiniteSum.Fin
open Algebra.Ring (GaussianReading)
open Polynomial.Dense (Companion)
open Polynomial.Dense.Roots
open Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots (Stages)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)

/-- The original nonmonic source whose first root algebra has nonzero zero divisors. -/
private def source : DensePolynomial Canonical := ⟨[2, 0, -2]⟩

/-- The same original source is already normalized. -/
private theorem normalized : source.normalize = source := by decide +kernel

/-- The original degree-derived producer retains its complete two-stage tower. -/
private def tower := Tower.prepare source normalized (1 / 2) (by decide +kernel)

/-- The proof-only scalar-leading invariant concerns that identical original tower. -/
private theorem leading : Tower.Leading tower id 2 :=
  Tower.Leading.ofSource tower id 2 normalized (by decide +kernel) rfl rfl (fun _ _ => rfl)

/-- Check the next actual retained companion using the same nonmultiplicative parent reading. -/
private def checkNext (adjunction : Companion.Adjunction source)
    (remaining : Tower (Tower.StageScalar adjunction) inferInstance inferInstance adjunction.division.quotient)
    (leading : Tower.Leading remaining (Cyclic.Element.scalar adjunction.table) 2)
    (parent : GaussianReading (Cyclic.Element.weight adjunction.table Norm.weight)
      (Cyclic.Element.scalar adjunction.table))
    (observed : DensePolynomial Canonical)
    (observedEq : observed = Polynomial.Dense.Map.map parent.read adjunction.division.quotient) : IO Unit := by
  cases remaining with
  | constant _ _ => exact throw (IO.userError "the original quadratic tower lost its second adjunction")
  | step next decreases final =>
      exact do
        let reading := leading.readingObserved parent observed observedEq
        unless reading.observed.coeffs == [2, 3 / 2] && reading.target.leadingInverse == 1 / 2 &&
            parent.read next.companion.leadingInverse == 1 / 2 &&
            reading.target.matrix ⟨0, reading.target.positive⟩ ⟨0, reading.target.positive⟩ == -3 / 4 do
          throw (IO.userError "the original quotient companion lost its Gaussian scalar leading inverse")
        let root := adjunction.root
        unless decide ((root - 1) * (root + 1) = 0) && decide (root - 1 ≠ 0) && decide (root + 1 ≠ 0) &&
            parent.read (root * root) - parent.read root * parent.read root == 7 / 16 do
          throw (IO.userError "the original zero divisors or nonmultiplicative parent reading changed")
        System.IO.println "Original nonmonic tower: two inverse readings1/2, quotient[2,3/2], \
          zero divisors, defect7/16."

/-- Read the first same original stage, then extend its parent model at the retained rational candidate. -/
private def check (retained : Tower Canonical inferInstance inferInstance source)
    (leading : Tower.Leading retained id 2) : IO Unit := by
  cases retained with
  | constant _ _ => exact throw (IO.userError "the original positive-degree source became constant")
  | step adjunction decreases remaining =>
      exact do
        let reading := leading.reading GaussianReading.identity
        unless reading.observed.coeffs == [2, 0, -2] && reading.target.leadingInverse == 1 / 2 do
          throw (IO.userError "the first original nonmonic companion reading changed")
        let parameters := Cyclic.Element.Reading.Parameters.prepare adjunction.table Norm.weight 1 1
          (by decide) (by decide)
        let point : Canonical := 3 / 4
        let epsilon := Norm.Basic.normSq (reading.observed.eval point)
        let residual := epsilon * Norm.Basic.normSq ((2 : Canonical)⁻¹)
        have residualNonnegative : 0 ≤ residual := Arithmetic.mul_nonneg_direct
          (Norm.Basic.normSq_nonneg _) (Norm.Basic.normSq_nonneg _)
        have columnBound (column : Fin source.natDegree) :
            Norm.Basic.normSq (sumFin (fun row => GaussianReading.identity.read
              ((LinearAlgebra.Matrix.Rectangular.transpose adjunction.companion.matrix) row column) *
                point ^ row.val) - point * point ^ column.val) ≤ residual :=
          reading.transpose_action_error_normSq_le point column epsilon
            (Purelib.Data.Rat.Fraction.Order.Basic.le_refl _)
        let parent := parameters.toReading GaussianReading.identity rfl point
          (by decide +kernel : Norm.Basic.normSq (3 / 4 : Canonical) ≤ (1 : Rational))
          residual residualNonnegative columnBound
        let cached := Polynomial.Dense.Division.Synthetic.divide reading.observed point
        have observedEq : cached.quotient = Polynomial.Dense.Map.map parent.read adjunction.division.quotient := by
          have quotient := adjunction.quotient_reading leading.normalized GaussianReading.identity.read
            GaussianReading.identity.mapZero GaussianReading.identity.mapAdd point
          have original := congrArg (fun polynomial : DensePolynomial Canonical =>
            (Polynomial.Dense.Division.Synthetic.divide polynomial point).quotient) reading.observed_eq
          exact original.trans quotient.symm
        checkNext adjunction remaining leading.next parent cached.quotient observedEq

/-- The original coefficient preprocessing sees the source's nonzero leading coefficient. -/
private theorem source_nonzero : source.isZero = false := by decide +kernel

/-- The same original source has positive degree two. -/
private theorem source_degree : source.natDegree = 2 := by decide +kernel

/-- The same original source supplies its actual automatic positive multiplicity preprocessing. -/
private def preprocessing : Squarefree.Decomposition.Compute.PositivePreprocessing source :=
  match Squarefree.Decomposition.Compute.preprocess source with
  | .positive retained => retained
  | .zero zero => False.elim (Bool.noConfusion (source_nonzero.symm.trans zero))
  | .constant _ degreeZero => False.elim (by
      have impossible : (2 : Nat) = 0 := source_degree.symm.trans degreeZero
      cases impossible)

/-- The original source and constant opposite retain their original positive-side input. -/
private def input : PositiveSideInput source (DensePolynomial.constant 1) :=
  { sourceNormalized := normalized
    preprocessing := preprocessing
    oppositeNonzero := by decide +kernel
    sourceOppositeCoprime := Coprime.Operations.CoprimeCertificate.constantRight source_nonzero }

/-- Construct a companion reading using only the automatically derived original stage invariant. -/
private def checkStage {contexts : List (PositiveContext input.entries)} {indices : List (Fin contexts.length)}
    (stages : Stages contexts indices Canonical inferInstance inferInstance id)
    (leading : Stages.Leading stages) : IO Unit := by
  cases stages with
  | done => exact throw (IO.userError "the original positive preprocessing lost its factor stages")
  | adjoin mapped mappedEq normalized degree tower roots rootsEq remaining =>
      have localLeading := leading.current
      cases tower with
      | constant _ _ => exact throw (IO.userError "the positive original factor tower became constant")
      | step adjunction decreases tail =>
          exact do
            let reading := localLeading.readingObserved GaussianReading.identity mapped
              (Polynomial.Dense.Map.map_id mapped).symm
            unless reading.observed.coeffs == [2, 0, -2] && reading.target.leadingInverse == 1 / 2 &&
                reading.target.matrix ⟨0, reading.target.positive⟩ ⟨0, reading.target.positive⟩ == 0 do
              throw (IO.userError "automatic original stage leading ownership did not supply its companion reading")
            System.IO.println "Original multiplicity stage: retained nonmonic factor[2,0,-2], inverse1/2."

/-- Execute both original nonmonic readings and the same source's automatic multiplicity-stage adapter. -/
public def run : IO Unit := do
  check tower leading
  let prepared := Stages.prepareInput input
  checkStage prepared.stages prepared.leading

end TestPurelib.Polynomial.Dense.Roots.Tower.Leading
