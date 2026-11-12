module

import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading.Source
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Leading
import Purelib.Polynomial.Dense.Roots.Tower.Reading.Realization
import Purelib.Polynomial.Dense.Companion.Reading.Scalar
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute
import Purelib.Data.Gaussian.Field
import Purelib.System.IO

/-!
# Original factor readback after nonmultiplicative quadratic readings

The original source `(z²-1)³(2z-1)²` supplies a quadratic factor followed by
a different linear factor. Reading the first tower at `3/4` and `-3/4`
retains a nonzero multiplication discrepancy. The next original factor
nevertheless supplies its complete unchanged observed coefficient cache.
-/

namespace TestPurelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Source

open Purelib
open Polynomial.Dense.Basic (DensePolynomial)
open Polynomial.Dense.Roots (Tower)
open Polynomial.Dense.Roots.Tower.Reading renaming Parameters → TowerParameters, Endpoint → TowerEndpoint
open Polynomial.Dense.Gaussian.Multiplicity.Roots
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Polynomial.Dense.Gaussian
open Algebra.Monogenic
open Algebra.FiniteSum.Fin
open Algebra.Ring (Weight GaussianReading)
open Data.Gaussian.Basic (Canonical)
open Data.Gaussian
open Data.Rat.Fraction (Rational)
open Data.Rat.Fraction.Order

universe u

/-- The original mixed source has two distinct positive multiplicity contexts. -/
private def source : DensePolynomial Canonical := ⟨[4, -4, -11, 12, 9, -12, -1, 4, -1]⟩

/-- The original source retains its nonzero normalized leading coefficient. -/
private theorem normalized : source.normalize = source := by decide +kernel

/-- The original mixed source is nonzero. -/
private theorem nonzero : source.isZero = false := by decide +kernel

/-- The original mixed source has positive degree eight. -/
private theorem degree : source.natDegree = 8 := by decide +kernel

/-- Retain the same original automatic preprocessing of the mixed source. -/
private def preprocessing : Squarefree.Decomposition.Compute.PositivePreprocessing source :=
  match Squarefree.Decomposition.Compute.preprocess source with
  | .positive retained => retained
  | .zero zero => False.elim (Bool.noConfusion (nonzero.symm.trans zero))
  | .constant _ degreeZero => False.elim (by
      have impossible : (8 : Nat) = 0 := degree.symm.trans degreeZero
      cases impossible)

/-- The original mixed source and constant opposite retain their original positive-side input. -/
private def input : PositiveSideInput source (DensePolynomial.constant 1) :=
  { sourceNormalized := normalized
    preprocessing := preprocessing
    oppositeNonzero := by decide +kernel
    sourceOppositeCoprime := Coprime.Operations.CoprimeCertificate.constantRight nonzero }

/-- Read each original tower stage at the first positive and then negative retained candidate. -/
private def model {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
    {parent : Weight K} {gain : Rational} {function : Canonical → K} {coefficient : Canonical}
    (leading : Tower.Leading tower function coefficient) (parameters : TowerParameters tower parent gain 1)
    (reading : GaussianReading parent function) (gainEq : reading.gain = gain) (negative : Bool) :
    { endpoint : TowerEndpoint parameters function // endpoint.gain = parameters.finalGain } :=
  match tower, parameters with
  | .constant _ _, .constant _ _ _ => ⟨reading, gainEq⟩
  | .step adjunction _ _, .step current next =>
      let observed := leading.reading reading
      let point : Canonical := if negative then -(3 / 4) else 3 / 4
      have pointBound : Norm.Basic.normSq point ≤ (1 : Rational) := by cases negative <;> decide +kernel
      let epsilon := Norm.Basic.normSq (observed.observed.eval point)
      let residual := epsilon * Norm.Basic.normSq coefficient⁻¹
      have residualNonnegative : 0 ≤ residual :=
        Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg _) (Norm.Basic.normSq_nonneg _)
      have columns (column : Fin polynomial.natDegree) :
          Norm.Basic.normSq (sumFin (fun row => reading.read
            ((LinearAlgebra.Matrix.Rectangular.transpose adjunction.companion.matrix) row column) *
              point ^ row.val) - point * point ^ column.val) ≤ residual :=
        observed.transpose_action_error_normSq_le point column epsilon (Basic.le_refl _)
      let child := current.toReading reading gainEq point pointBound residual residualNonnegative columns
      model leading.next next child rfl true

/-- The original next factor is consumed directly as the same companion's observed cache. -/
private def checkNext {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}
    {indices : List (Fin contexts.length)} {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {function : Canonical → K} {parent : Weight K}
    (stages : Stages contexts indices K ring equality function) (leading : Stages.Leading stages)
    (reading : GaussianReading parent function) : IO Unit := by
  cases stages with
  | done => exact throw (IO.userError "the original mixed source lost its second factor")
  | @adjoin K ring equality function index indices mapped mappedEq normalized degree tower roots rootsEq remaining =>
      have cacheEq := Stages.Reading.factor_eq_map reading mappedEq
      cases tower with
      | constant _ _ => exact throw (IO.userError "the second original positive factor became constant")
      | step adjunction decreases tail =>
          exact do
            let cached := factor contexts index
            let observed := leading.current.readingObserved reading cached cacheEq
            unless observed.observed.coeffs == cached.coeffs &&
                observed.target.leadingInverse == cached.leadingCoeff⁻¹ && cached.natDegree == 1 do
              throw (IO.userError "the original next factor lost its unchanged Gaussian coefficient cache")
            System.IO.println "Original second factor cache and Gaussian leading inverse retained exactly."

/-- Inspect the same original quadratic tower before consuming the retained second factor. -/
private def check {contexts : List (PositiveContext input.entries)} {indices : List (Fin contexts.length)}
    (stages : Stages contexts indices Canonical inferInstance inferInstance id)
    (leading : Stages.Leading stages) : IO Unit := by
  cases stages with
  | done => exact throw (IO.userError "the original mixed preprocessing lost its factor stages")
  | @adjoin K ring equality function index indices mapped mappedEq normalized degree tower roots rootsEq remaining =>
      exact do
        let parameters := TowerParameters.prepare tower Norm.weight 1 1 (by decide) (by decide)
        let observed := model leading.current parameters GaussianReading.identity rfl false
        if rootExists : 0 < roots.length then
          let root := roots[0]'rootExists
          let discrepancy := observed.val.read (root.point * root.point) -
            observed.val.read root.point * observed.val.read root.point
          let sample : DensePolynomial Canonical := ⟨[⟨2, 1⟩, 0, ⟨-3, 2⟩]⟩
          let mappedSample := Polynomial.Dense.Map.map tower.embed sample
          have sampleCache := Polynomial.Dense.Map.source_eq_read observed.val sample mappedSample rfl
          unless contexts.length == 2 && tower.steps == 2 && discrepancy == 7 / 16 &&
              (Polynomial.Dense.Map.map observed.val.read mappedSample).coeffs == sample.coeffs do
            throw (IO.userError "the preceding original quadratic reading or nonmonic scalar-table readback changed")
          checkNext remaining leading.next observed.val
        else throw (IO.userError "the original quadratic tower lost its retained roots")

/-- Run the original mixed preprocessing and complete quadratic-to-linear source-cache construction. -/
public def run : IO Unit :=
  let prepared := Stages.prepareInput input
  check prepared.stages prepared.leading

end TestPurelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Source
