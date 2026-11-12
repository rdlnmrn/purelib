module

import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading.Realization
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Leading
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute
import Purelib.Data.Gaussian.Field
import Purelib.System.IO

/-!
# Paid readings of mixed original multiplicity contexts

The same original preprocessing of `z²(z-2)³` supplies two different linear
factor towers. Their zero and nonzero exact candidates pay the backward
context budget, retaining all original coefficients in one final reading.
-/

namespace TestPurelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading

open Purelib
open Polynomial.Dense.Basic (DensePolynomial)
open Polynomial.Dense.Roots (Tower)
open Polynomial.Dense (Companion)
open Polynomial.Dense.Roots.Tower.Reading renaming
  Parameters → TowerParameters, Budget → TowerBudget, Realization → TowerRealization
open Polynomial.Dense.Gaussian.Multiplicity.Roots
open Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Polynomial.Dense.Gaussian
open Algebra.Monogenic
open Algebra.Monogenic.Cyclic.Element.Reading (ColumnBound)
open Algebra.Monogenic.Cyclic.Element.Reading renaming Observation → CyclicObservation
open Algebra.Ring (Weight GaussianReading)
open Data.Gaussian.Basic (Canonical)
open Data.Gaussian
open Data.Rat.Fraction (Rational)
open Data.Rat.Fraction.Order

universe u

/-- The same degree-five mixed source has a double zero and a triple root at two. -/
private def source : DensePolynomial Canonical := ⟨[1, -6, 12, -8, 0, 0]⟩

/-- The original source is already normalized. -/
private theorem normalized : source.normalize = source := by decide +kernel

/-- The original source has a nonzero leading coefficient. -/
private theorem nonzero : source.isZero = false := by decide +kernel

/-- The original source has positive degree five. -/
private theorem degree : source.natDegree = 5 := by decide +kernel

/-- Retain the actual automatic positive preprocessing of the mixed source. -/
private def preprocessing : Squarefree.Decomposition.Compute.PositivePreprocessing source :=
  match Squarefree.Decomposition.Compute.preprocess source with
  | .positive retained => retained
  | .zero zero => False.elim (Bool.noConfusion (nonzero.symm.trans zero))
  | .constant _ degreeZero => False.elim (by
      have impossible : (5 : Nat) = 0 := degree.symm.trans degreeZero
      cases impossible)

/-- The original source and constant opposite retain their original coprime input. -/
private def input : PositiveSideInput source (DensePolynomial.constant 1) :=
  { sourceNormalized := normalized
    preprocessing := preprocessing
    oppositeNonzero := by decide +kernel
    sourceOppositeCoprime := Coprime.Operations.CoprimeCertificate.constantRight nonzero }

/-- Build paid exact observations for a retained linear-factor tower, rejecting any nonzero column residual. -/
private def linearTower {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
    {parent : Weight K} {gain radius target tolerance : Rational} {embed : Canonical → K} {coefficient : Canonical}
    (leading : Tower.Leading tower embed coefficient) (parameters : TowerParameters tower parent gain radius)
    (budget : TowerBudget parameters target tolerance) (reading : GaussianReading parent embed)
    (gainEq : reading.gain = gain) : Except String (TowerRealization budget reading gainEq) :=
  match tower, parameters, target, tolerance, budget with
  | .constant _ _, .constant _ _ _, _, _, .constant positive =>
      pure (TowerRealization.constant reading gainEq positive)
  | .step adjunction _ _, .step current next, _, _, .step tail request => do
      let observed := leading.reading reading
      let point := -(observed.observed.eval 0) * observed.target.leadingInverse
      haveI : Decidable (ColumnBound (LinearAlgebra.Matrix.Rectangular.transpose adjunction.companion.matrix)
          reading point 0) := by unfold ColumnBound; infer_instance
      if pointBound : Norm.Basic.normSq point ≤ radius then do
        if columns : ColumnBound (LinearAlgebra.Matrix.Rectangular.transpose adjunction.companion.matrix)
            reading point 0 then do
          let observation := CyclicObservation.prepare current reading gainEq point pointBound
            0 (Basic.le_refl _) columns
          let rest ← linearTower leading.next next tail observation.child observation.gain_eq
          pure (TowerRealization.step tail request observation request.tolerance_positive.le rest)
        else throw "the retained exact linear root has a nonzero original column residual"
      else throw "the retained exact root exceeded its original context radius"

/-- Feed each same cached factor endpoint into the next original context's actual realization. -/
private def linearContexts {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}
    {indices : List (Fin contexts.length)} {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {function : Canonical → K} {stages : Stages contexts indices K ring equality function}
    {radii : Fin contexts.length → Rational} {parent : Weight K} {gain target tolerance : Rational}
    (leading : Stages.Leading stages) (parameters : Parameters radii stages parent gain)
    (budget : Budget parameters target tolerance) (reading : GaussianReading parent function)
    (gainEq : reading.gain = gain) : Except String (Realization budget reading gainEq) :=
  match indices, stages, parameters, target, tolerance, budget with
  | [], .done, .done _, _, _, .done positive => pure (Realization.done reading gainEq positive)
  | _ :: _, .adjoin _ _ _ _ _ _ _ _, .adjoin current next, _, _, .adjoin tail request => do
      let observation ← linearTower leading.current current request.budget reading gainEq
      let rest ← linearContexts leading.next next tail observation.finalReading observation.final_gain
      pure (Realization.adjoin tail request observation rest)

/-- Inspect the actual cached original mixed context chain and its paid common endpoint. -/
private def check (prepared : Stages.Prepared input) : IO Unit := do
  let radii := fun index : Fin prepared.contexts.length => if index.val = 0 then (4 : Rational) else 1
  have radiiNonnegative (index : Fin prepared.contexts.length) : 0 ≤ radii index := by
    unfold radii
    split <;> decide
  let parameters := Parameters.prepare prepared.stages Norm.weight 1 radii (by decide) radiiNonnegative
  let request := Request.prepare parameters 1 (by decide)
  match linearContexts prepared.leading parameters request.budget GaussianReading.identity rfl with
  | .error message => throw (IO.userError message)
  | .ok realized =>
      have fixedGain := realized.final_gain
      have sufficient := realized.error_lt request.positive
      have sourceRead := realized.final_read_embed (⟨3, 1⟩ : Canonical)
      unless prepared.contexts.length == 2 && parameters.factors == 2 &&
          parameters.finalGain == 4 && realized.finalReading.gain == 4 &&
          realized.finalReading.error == 0 && decide (0 < request.tolerance) &&
          realized.finalReading.read (prepared.stages.embed (⟨3, 1⟩ : Canonical)) == (⟨3, 1⟩ : Canonical) do
        throw (IO.userError "the original mixed contexts lost their fixed gain, \
          sufficient error or coefficient reading")
      System.IO.println "Original mixed context readings: two towers, radii4/1, \
        gain4, error0, exact original coefficients."

/-- Execute the complete same original automatic preprocessing and both retained factor realizations. -/
public def run : IO Unit := check (Stages.prepareInput input)

end TestPurelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading
