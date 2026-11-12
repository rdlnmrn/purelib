module

public import Purelib.Polynomial.Dense.Roots.Tower.Reading.Realization
public import Purelib.Polynomial.Dense.Roots.Tower.Reading.Sources
public import Purelib.Polynomial.Dense.Roots.Tower.Factorization
public import Purelib.Polynomial.Dense.Companion.Adjunction.Reading
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Paid source samples read the same original tower

The same retained Gaussian expansion constructs every original cyclic child.
Each tail consumes its original retained quotient and the preceding cached
reading. The resulting original formal roots stay quantitatively close to
their corresponding ordered samples, including the terminal linear correction.
-/

public section

namespace Purelib.Polynomial.Dense.Roots.Tower.Reading

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Algebra.Monogenic
open Purelib.LinearAlgebra
open Purelib.Algebra.Ring (Weight GaussianReading)
open Purelib.Algebra.Monogenic.Cyclic.Element.Reading renaming Observation → CyclicObservation
open Purelib.Algebra.Monogenic.Cyclic.Element.Reading (ColumnBound)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction

universe u

/-- Every same ordered formal root reading stays within its corresponding original sample's paid bound. -/
inductive Matched {K : Type u} (read : K → Canonical) (bound : Rational) :
    List (Block K) → List Canonical → Prop
  /-- The original constant endpoint has no formal root or sample. -/
  | nil : Matched read bound [] []
  /-- Retain the current original root-sample bound and the same ordered tail. -/
  | cons {root : Block K} {roots : List (Block K)} {point : Canonical} {points : List Canonical}
      (current : Norm.Basic.normSq (read root.point - point) ≤ bound)
      (remaining : Matched read bound roots points) : Matched read bound (root :: roots) (point :: points)

set_option genInjectivity false in
/-- An actual original tower reading together with its ordered original sample correspondence. -/
structure Sampled {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
    {parent : Weight K} {gain radius target tolerance : Rational} {parameters : Parameters tower parent gain radius}
    (budget : Budget parameters target tolerance) {embed : Canonical → K}
    (reading : GaussianReading parent embed) (gain_eq : reading.gain = gain)
    (nodes : List Canonical) (bound : Rational) where
  /-- The same paid original observations and their cached common final reading. -/
  realization : Realization budget reading gain_eq
  /-- The original tower blocks correspond in order to these same retained original samples. -/
  matched : Matched realization.finalReading.read bound tower.blocks nodes

constructive_injectivity Sampled

namespace Sampled

section Current

variable {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {polynomial : DensePolynomial K}
variable {adjunction : Companion.Adjunction polynomial}
variable {decreases : adjunction.division.quotient.natDegree + 1 = polynomial.natDegree}
variable {remaining : Tower (StageScalar adjunction) inferInstance inferInstance adjunction.division.quotient}
variable {parent : Weight K} {gain radius : Rational} {embed : Canonical → K} {coefficient : Canonical}
variable {parameters : Cyclic.Element.Reading.Parameters adjunction.table parent gain radius}
variable {reading : GaussianReading parent embed} {gain_eq : reading.gain = gain}

/-- The retained source table and inverse give the same original companion without remapping coefficients. -/
@[expose] def sourceCompanion (leading : Leading (.step adjunction decreases remaining) embed coefficient)
    (reading : GaussianReading parent embed) (inverse : Canonical) (inverseEq : inverse = coefficient⁻¹)
    (observed : DensePolynomial Canonical) (observedEq : observed = Map.map reading.read polynomial) :
    Companion.Reading adjunction.companion reading.read inverse :=
  Companion.Reading.ofObserved adjunction.companion reading.read inverse observed observedEq
    reading.mapZero reading.mapOne reading.mapNeg (fun value =>
      (Companion.Reading.scale_leadingInverse adjunction.companion reading coefficient
        leading.scalar_zero leading.scalar_one leading.scalar_mul leading.coefficient_eq value).trans
          (congrArg (fun inverseValue : Canonical => reading.read value * inverseValue) inverseEq.symm))

/-- One cached original remainder supplies one actual original cyclic observation. -/
@[expose] def sourceObservation (leading : Leading (.step adjunction decreases remaining) embed coefficient)
    (parameters : Cyclic.Element.Reading.Parameters adjunction.table parent gain radius)
    (reading : GaussianReading parent embed) (gain_eq : reading.gain = gain)
    (inverse : Canonical) (inverseEq : inverse = coefficient⁻¹) (inverseNorm : Rational)
    (inverseNormEq : inverseNorm = Norm.Basic.normSq inverse)
    (observed : DensePolynomial Canonical) (observedEq : observed = Map.map reading.read polynomial)
    (point : Canonical) (pointBound : Norm.Basic.normSq point ≤ radius)
    (remainder : Canonical) (remainderEq : remainder = observed.eval point) :
    CyclicObservation parameters reading gain_eq :=
  let sourceResidual := Norm.Basic.normSq remainder
  let residual := sourceResidual * inverseNorm
  have nonnegative : 0 ≤ residual := Order.Arithmetic.mul_nonneg_direct
    (Norm.Basic.normSq_nonneg remainder) (inverseNormEq.symm ▸ Norm.Basic.normSq_nonneg inverse)
  have columns : ColumnBound _ reading point residual := by
    intro column
    have current := sourceCompanion leading reading inverse inverseEq observed observedEq
    have currentEq : current.observed = observed := current.observed_eq.trans observedEq.symm
    have sourceBound : Norm.Basic.normSq (current.observed.eval point) ≤ sourceResidual :=
      ((congrArg (fun source : DensePolynomial Canonical => Norm.Basic.normSq (source.eval point)) currentEq).trans
        (congrArg Norm.Basic.normSq remainderEq.symm)).le
    have bounded := current.transpose_action_error_normSq_le point column sourceResidual
      sourceBound
    exact bounded.trans_eq (congrArg (fun value => sourceResidual * value) inverseNormEq.symm)
  have generatorEq : adjunction.root.matrix =
      Matrix.Rectangular.transpose adjunction.companion.matrix :=
    (congrArg Cyclic.Element.matrix adjunction.root_eq).trans (Cyclic.Element.root_matrix adjunction.table)
  CyclicObservation.prepareGenerator adjunction.root.matrix generatorEq
    parameters reading gain_eq point pointBound residual nonnegative columns

/-- The same retained child reads the original formal quotient as the same retained Gaussian quotient. -/
theorem sourceQuotient_eq (leading : Leading (.step adjunction decreases remaining) embed coefficient)
    (observation : CyclicObservation parameters reading gain_eq) (observed : DensePolynomial Canonical)
    (observedEq : observed = Map.map reading.read polynomial) {points : List Canonical}
    (expansion : Interpolation.Expansion observed (observation.point :: points)) :
    expansion.first.quotient = Map.map observation.child.read adjunction.division.quotient := by
  have retained := congrArg (fun result : Division.Synthetic.Result observed observation.point => result.quotient)
    expansion.first_eq
  have source := congrArg (fun source : DensePolynomial Canonical =>
    (Division.Synthetic.divide source observation.point).quotient) observedEq
  have original := adjunction.quotient_reading leading.normalized reading.read
    reading.mapZero reading.mapAdd observation.point
  have entries : Map.map observation.child.read adjunction.division.quotient =
      Map.map (Cyclic.Element.evaluate reading.read observation.point) adjunction.division.quotient :=
    DensePolynomial.ext (Purelib.Data.List.Map.map_congr_left (fun value _ => observation.read_apply value))
  exact retained.trans (source.trans (original.symm.trans entries.symm))

end Current

/-- Read every original stage from its same paid source expansion, retaining terminal root corrections.

The inverse, its norm and the sufficient scale are shared input caches. Every
recursive call consumes the same actual expansion tail and original budget
tail; no source evaluation, division, formal coefficient map or parameter
preparation is repeated to explain the resulting reading.
-/
@[expose] def ofExpansion {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
    {parent : Weight K} {gain radius target tolerance : Rational} {parameters : Parameters tower parent gain radius}
    (budget : Budget parameters target tolerance) {embed : Canonical → K} {coefficient : Canonical}
    (leading : Leading tower embed coefficient) (reading : GaussianReading parent embed)
    (gain_eq : reading.gain = gain) (inverse : Canonical) (inverseEq : inverse = coefficient⁻¹)
    (inverseNorm : Rational) (inverseNormEq : inverseNorm = Norm.Basic.normSq inverse)
    (scale cap : Rational) (scaleBound : scale * inverseNorm ≤ 1)
    (observed : DensePolynomial Canonical) (observedEq : observed = Map.map reading.read polynomial)
    (nodes : List Canonical) (expansion : Interpolation.Expansion observed nodes)
    (bounded : ∀ point ∈ nodes, Norm.Basic.normSq point ≤ radius)
    (paid : expansion.Pays (budget.targets scale cap)) : Sampled budget reading gain_eq nodes (cap * inverseNorm) :=
  match tower, parameters, target, tolerance, budget, nodes with
  | .constant _ _, .constant _ _ _, _, _, .constant positive, [] =>
      { realization := Realization.constant reading gain_eq positive, matched := .nil }
  | .constant _ _, .constant _ _ _, _, _, .constant _, _ :: _ =>
      False.elim (Nat.noConfusion paid.length)
  | .step _ _ _, .step _ _, _, _, .step _ _, [] =>
      False.elim (Nat.noConfusion paid.length)
  | .step adjunction decreases remaining, .step current next, _, _, .step tail request, point :: points =>
      let observation := sourceObservation leading current reading gain_eq inverse inverseEq inverseNorm inverseNormEq
        observed observedEq point (bounded point List.mem_cons_self)
        expansion.first.remainder expansion.first.remainder_eval
      have residualPaid : observation.residual ≤ request.tolerance := by
        have source := paid.head.trans (Order.Basic.min_le_left _ _)
        have estimate := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct source
          (inverseNormEq.symm ▸ Norm.Basic.normSq_nonneg inverse)
        change Norm.Basic.normSq expansion.first.remainder * inverseNorm ≤ request.tolerance
        calc
          _ ≤ (scale * request.tolerance) * inverseNorm := estimate
          _ = (scale * inverseNorm) * request.tolerance := by
            rewrite [Fraction.mul_assoc, Fraction.mul_comm request.tolerance inverseNorm,
              ← Fraction.mul_assoc]
            rfl
          _ ≤ 1 * request.tolerance := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            scaleBound request.tolerance_positive.le
          _ = request.tolerance := Fraction.one_mul _
      let rest := ofExpansion tail leading.next observation.child observation.gain_eq inverse inverseEq
        inverseNorm inverseNormEq scale cap scaleBound expansion.first.quotient
        (sourceQuotient_eq leading observation observed observedEq expansion) points expansion.next
        (fun next member => bounded next (List.mem_cons_of_mem point member)) paid.next
      let realization : Realization (.step tail request : Budget
          (.step current next : Parameters (.step adjunction decreases remaining) parent gain radius)
            _ request.tolerance) reading gain_eq :=
        Realization.step tail request observation residualPaid rest.realization
      have currentBound : Norm.Basic.normSq
          (realization.finalReading.read (remaining.embed adjunction.root) - point) ≤ cap * inverseNorm := by
        change Norm.Basic.normSq
          (rest.realization.finalReading.read (remaining.embed adjunction.root) - point) ≤ cap * inverseNorm
        have readback := (rest.realization.final_read_embed adjunction.root).trans
          (observation.read_apply adjunction.root)
        rewrite [readback]
        have sourcePaid := paid.head_eval.trans (Order.Basic.min_le_right _ _)
        have current := sourceCompanion leading reading inverse inverseEq observed observedEq
        have currentEq : current.observed = observed := current.observed_eq.trans observedEq.symm
        have currentPaid : Norm.Basic.normSq (current.observed.eval point) ≤ cap :=
          (congrArg (fun source : DensePolynomial Canonical => Norm.Basic.normSq (source.eval point))
            currentEq).symm ▸ sourcePaid
        have bound := adjunction.root_reading_error_normSq_le current reading.mapZero point cap currentPaid
        exact bound.trans_eq (congrArg (fun value => cap * value) inverseNormEq.symm)
      { realization, matched := .cons currentBound rest.matched }
termination_by structural budget

end Sampled

namespace Sources

/-- The same pre-observation source requests automatically read all original adjunctions from their paid expansion. -/
@[expose] def realize {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
    {parent : Weight K} {gain radius target tolerance : Rational} {parameters : Parameters tower parent gain radius}
    {budget : Budget parameters target tolerance} {embed : Canonical → K} {coefficient : Canonical}
    {leading : Leading tower embed coefficient} {separation cap : Rational}
    (sources : Sources budget leading separation cap) (reading : GaussianReading parent embed)
    (gain_eq : reading.gain = gain) (observed : DensePolynomial Canonical)
    (observedEq : observed = Map.map reading.read polynomial) (nodes : List Canonical)
    (expansion : Interpolation.Expansion observed nodes)
    (bounded : ∀ point ∈ nodes, Norm.Basic.normSq point ≤ radius) (paid : expansion.Pays sources.targets) :
    Sampled budget reading gain_eq nodes (cap * sources.inverseNorm) :=
  Sampled.ofExpansion budget leading reading gain_eq sources.coefficientInverse sources.coefficientInverse_eq
    sources.inverseNorm sources.inverseNorm_eq sources.scale cap sources.scale_mul_norm_le_one
    observed observedEq nodes expansion bounded (sources.targets_eq ▸ paid)

end Sources

end Purelib.Polynomial.Dense.Roots.Tower.Reading

end
