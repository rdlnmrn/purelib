module

import Purelib.LinearAlgebra.Matrix.Reading.Power
import Purelib.Algebra.Monogenic.Coordinates.Reading
import Purelib.Polynomial.Dense.Companion.Adjunction
import Purelib.Data.Gaussian.Field
import Purelib.System.IO

/-!
# Actual finite matrix discrepancies over an original zero-divisor algebra

One original quadratic algebra has a genuinely nonmultiplicative Gaussian
reading. The same source-weight caches pay actual rectangular actions,
products and perturbed inputs. A singular original transition tests the
bound-only propagation table and retained power readbacks without inverses.
-/

namespace TestPurelib.LinearAlgebra.Matrix.Reading

open Purelib.Algebra.Ring (GaussianReading)
open Purelib.Algebra.Monogenic (Cyclic)
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense (Companion)
open Purelib.LinearAlgebra.Matrix

/-- The original coefficient table retains the relation `root^2=1`. -/
private def source : DensePolynomial Canonical := ⟨[1, 0, -1]⟩

/-- The same original companion produces the actual coefficient algebra. -/
private def adjunction := (Companion.ofUnit source (by decide +kernel) 1 (by decide +kernel)).adjoin

/-- The actual coefficient carrier is the original cyclic element type. -/
private abbrev Scalar := Cyclic.Element adjunction.table

/-- The same original finite scalar weight is retained independently of observations. -/
private def sourceWeight := Cyclic.Element.weight adjunction.table Norm.weight

/-- Fixed original cyclic gain and radius parameters precede all observations. -/
private def cyclicParameters :=
  Cyclic.Element.Reading.Parameters.prepare adjunction.table Norm.weight 1 1 (by decide) (by decide)

/-- The original source matrix contains the same formal root and exact unit entries. -/
private def matrix : Rectangular Scalar 2 2 := .cons (.cons adjunction.root (.cons 1 .nil))
  (.cons (.cons 1 (.cons 0 .nil)) .nil)

/-- The original coefficient vector is retained as source data before observations. -/
private def initial : Vec Scalar 2 := .cons adjunction.root (.cons 1 .nil)

/-- The original matrix weights are materialized exactly once. -/
private def matrixWeights := Rectangular.ofFn fun row column => sourceWeight.value (matrix row column)

/-- The original coefficient weights are materialized once and shared by both matrix-action requests. -/
private def initialWeights := vectorOfFn fun column => sourceWeight.value (initial column)

/-- The actual matrix action consumes the same certified source-weight caches. -/
private def application := Reading.Application.prepare sourceWeight matrix initial matrixWeights
  (fun row column => (Rectangular.ofFn_apply
    (fun row column : Fin 2 => sourceWeight.value (matrix row column)) row column).symm.le) initialWeights
  (fun column => (vectorOfFn_apply (fun column : Fin 2 => sourceWeight.value (initial column)) column).symm.le)

/-- Fixed nonnegative input-error coefficients do not depend on any observed model. -/
private def errors : Vec Rational 2 := .cons 0 (.cons 1 .nil)

/-- The perturbed-input request reuses the same complete original application cache. -/
private def perturbation := Reading.Perturbation.prepare application cyclicParameters.gain
  cyclicParameters.gain_nonnegative errors (by decide +kernel)

/-- A singular original transition retains a genuine zero mode. -/
private def transition : Rectangular Scalar 2 2 := .cons (.cons 0 (.cons 1 .nil))
  (.cons (.cons 0 (.cons adjunction.root .nil)) .nil)

/-- The same transition's source weights are computed once before its bound-only power request. -/
private def transitionWeights := Rectangular.ofFn fun row column => sourceWeight.value (transition row column)

/-- The transition request shares the original initial-vector weight cache. -/
private def transitionApplication := Reading.Application.prepare sourceWeight transition initial transitionWeights
  (fun row column => (Rectangular.ofFn_apply
    (fun row column : Fin 2 => sourceWeight.value (transition row column)) row column).symm.le) initialWeights
  (fun column => (vectorOfFn_apply (fun column : Fin 2 => sourceWeight.value (initial column)) column).symm.le)

/-- The source-fixed rational propagation table precedes its actual Gaussian observation. -/
private def powers := Reading.Power.Parameters.prepare transitionApplication cyclicParameters.gain
  cyclicParameters.gain_nonnegative 4

/-- The observed rational is deliberately not a root of the same source. -/
private def candidate : Canonical := ⟨3/4, 0⟩

/-- The original polynomial evaluator provides the actual retained source residual. -/
private def residual := Norm.Basic.normSq (source.eval candidate)

/-- The same original cyclic constructor supplies its actual additive Gaussian reading. -/
private def reading := cyclicParameters.toReading GaussianReading.identity rfl candidate (by decide +kernel)
  residual (Norm.Basic.normSq_nonneg _) (by decide +kernel)

/-- Both the actual product discrepancy and the multiplication-error allowance are genuinely nonzero. -/
private theorem nonmultiplicative : reading.read (Rectangular.apply matrix initial 0) = 2 ∧
    sumFin (fun column : Fin 2 => reading.read (matrix 0 column) * reading.read (initial column)) = 25/16 ∧
      0 < reading.error := by decide +kernel

/-- The same actual formal matrix action pays its original cached coefficient. -/
private theorem actual_action : Norm.Basic.normSq (reading.read (Rectangular.apply matrix initial 0) -
    sumFin (fun column : Fin 2 => reading.read (matrix 0 column) * reading.read (initial column))) ≤
      reading.error * application.coefficients 0 := application.bound reading 0

/-- The actual original action is retained once before its coordinate readings are collected. -/
private def actualValues := Rectangular.apply matrix initial

/-- The same actual action's coordinate readings form a cached Gaussian output vector. -/
private def actualReadings := vectorOfFn fun row => reading.read (actualValues row)

/-- Exact same-action readback requires no additional output-error allowance. -/
private def outputErrors : Vec Rational 2 := .cons 0 (.cons 0 .nil)

/-- The output-comparison cache combines the original application and fixed output allowances once. -/
private def outputCoefficients := application.outputCoefficients outputErrors

/-- A genuinely inexact physical product is compared with the same actual original action's readings. -/
private theorem actual_output : Norm.Basic.normSq
    (sumFin (fun column : Fin 2 => reading.read (matrix 0 column) * reading.read (initial column)) -
      actualReadings 0) ≤ reading.error * outputCoefficients 0 :=
  application.output_bound reading actualReadings outputErrors (by decide +kernel) 0

/-- A different Gaussian input is selected only after the original perturbation request. -/
private def model : Vec Canonical 2 := .cons candidate (.cons 0 .nil)

/-- The actual same-reading input errors pay the original fixed nonnegative coefficient table. -/
private theorem input_paid : ∀ column : Fin 2,
    Norm.Basic.normSq (reading.read (initial column) - model column) ≤ reading.error * errors column :=
  by decide +kernel

/-- Both actual product and input-model errors are paid for the same original formal matrix action. -/
private theorem perturbed_action : Norm.Basic.normSq (reading.read (Rectangular.apply matrix initial 0) -
    sumFin (fun column : Fin 2 => reading.read (matrix 0 column) * model column)) ≤
      reading.error * perturbation.coefficients 0 := perturbation.bound reading rfl model input_paid 0

/-- The matrix-product coefficient table is computed only from its same retained source-weight tables. -/
private def productErrors := Reading.productCoefficients matrixWeights matrixWeights

/-- The original matrix product also pays its retained finite coefficient despite nonmultiplicative reading. -/
private theorem actual_product : Norm.Basic.normSq (reading.read (Rectangular.mul matrix matrix 0 0) -
    sumFin (fun index : Fin 2 => reading.read (matrix 0 index) * reading.read (matrix index 0))) ≤
      reading.error * productErrors 0 0 := Reading.product_bound reading matrix matrix matrixWeights matrixWeights
        (fun row column => (Rectangular.ofFn_apply
          (fun row column : Fin 2 => sourceWeight.value (matrix row column)) row column).symm.le)
        (fun row column => (Rectangular.ofFn_apply
          (fun row column : Fin 2 => sourceWeight.value (matrix row column)) row column).symm.le) 0 0

/-- The singular source transition kills a nonzero original vector; no inverse premise is available. -/
private theorem singular : Rectangular.apply transition (.cons 1 (.cons 0 .nil)) = .cons 0 (.cons 0 .nil) ∧
    (.cons (1 : Scalar) (.cons 0 .nil) : Vec Scalar 2) ≠ .cons 0 (.cons 0 .nil) := by
  constructor
  · apply vector_ext
    exact (by decide +kernel : ∀ index : Fin 2,
      Rectangular.apply transition (.cons 1 (.cons 0 .nil)) index = (.cons 0 (.cons 0 .nil) : Vec Scalar 2) index)
  · intro same
    have scalar := congrArg (fun values : Vec Scalar 2 => values 0) same
    exact (by decide +kernel : (1 : Scalar) ≠ 0) scalar

/-- Cache the original Gaussian transition readback once. -/
private def observedTransition := Rectangular.ofFn fun row column => reading.read (transition row column)

/-- Cache the same original coefficient readings once. -/
private def observedInitial := vectorOfFn fun column => reading.read (initial column)

/-- The original formal power is computed once for the actual retained finite trajectory. -/
private def originalPower := Arithmetic.power transition 3

/-- The actual original finite vector action consumes that same retained source power. -/
private def originalValues := Rectangular.apply originalPower initial

/-- The Gaussian power is computed once from the same retained observed transition. -/
private def observedPower := Arithmetic.power observedTransition 3

/-- The Gaussian trajectory consumes the same retained observed matrix and coefficient vector. -/
private def observedValues := Rectangular.apply observedPower observedInitial

/-- The cached source and physical powers disagree, so exact multiplicative interpretation would be false. -/
private theorem powers_nonexact : reading.read (originalValues 0) = 1 ∧ observedValues 0 = 9/16 := by decide +kernel

/-- Exact cache readbacks pay the original finite propagation bound without producing another power. -/
private theorem actual_power : Norm.Basic.normSq (reading.read (originalValues 0) - observedValues 0) ≤
    reading.error * (powers.table ⟨3, by decide⟩).2 :=
  powers.bound_of_trajectories reading rfl observedTransition (Rectangular.ofFn_apply _)
    observedInitial (vectorOfFn_apply _) ⟨3, by decide⟩ originalValues rfl observedValues rfl 0

/-- A zero propagation horizon retains its same original initial weight and zero discrepancy. -/
private def zeroHorizon := Reading.Power.Parameters.prepare transitionApplication cyclicParameters.gain
  cyclicParameters.gain_nonnegative 0

/-- The original empty-step request has no transition error at its only retained state. -/
private theorem zero_horizon : (zeroHorizon.table ⟨0, by decide⟩).2 = 0 := rfl

/-- The same source-weight API supports an empty matrix and coefficient vector. -/
private def emptyApplication := Reading.Application.prepare sourceWeight
  (.nil : Rectangular Scalar 0 0) .nil .nil (fun row => Fin.elim0 row) .nil (fun column => Fin.elim0 column)

/-- A positive number of empty-dimensional steps still performs only the rational bound scan. -/
private def emptyPowers := Reading.Power.Parameters.prepare emptyApplication cyclicParameters.gain
  cyclicParameters.gain_nonnegative 2

/-- Every empty-dimensional trajectory has zero total weight and zero paid discrepancy coefficient. -/
private theorem empty_power : emptyPowers.table ⟨2, by decide⟩ = (0, 0) := by decide +kernel

/-- A nonzero formal zero-divisor coefficient can have zero physical reading in the same original algebra. -/
private theorem physical_zero : adjunction.root - 1 ≠ 0 ∧
    (cyclicParameters.toReading GaussianReading.identity rfl 1 (by decide +kernel) 0 (by decide)
      (by decide +kernel)).read (adjunction.root - 1) = 0 := by decide +kernel

/-- Execute the same nonmultiplicative matrix actions, singular powers and cached error payments. -/
public def run : IO Unit := do
  unless reading.read (actualValues 0) == 2 &&
      sumFin (fun column : Fin 2 => reading.read (matrix 0 column) * reading.read (initial column)) == 25/16 &&
      decide (0 < reading.error) do
    throw (IO.userError "the original quadratic reading lost its genuine multiplication discrepancy")
  for row in List.ofFn (fun row : Fin 2 => row) do
    let physical := sumFin (fun column : Fin 2 => reading.read (matrix row column) * reading.read (initial column))
    let perturbed := sumFin (fun column : Fin 2 => reading.read (matrix row column) * model column)
    unless decide ((reading.read (actualValues row) - physical).normSq ≤
        reading.error * application.coefficients row) &&
        decide ((physical - actualReadings row).normSq ≤ reading.error * outputCoefficients row) &&
        decide ((reading.read (actualValues row) - perturbed).normSq ≤ reading.error * perturbation.coefficients row) &&
        decide ((reading.read (originalValues row) - observedValues row).normSq ≤
          reading.error * (powers.table ⟨3, by decide⟩).2) do
      throw (IO.userError "an actual original matrix action exceeded its retained paid error cache")
    for column in List.ofFn (fun column : Fin 2 => column) do
      let product := sumFin (fun index : Fin 2 => reading.read (matrix row index) * reading.read (matrix index column))
      unless decide ((reading.read (Rectangular.mul matrix matrix row column) - product).normSq ≤
          reading.error * productErrors row column) do
        throw (IO.userError "an actual original matrix product exceeded its same-table error cache")
  unless reading.read (originalValues 0) == 1 && observedValues 0 == 9/16 &&
      (zeroHorizon.table ⟨0, by decide⟩).2 == 0 && emptyPowers.table ⟨2, by decide⟩ == (0, 0) do
    throw (IO.userError "the singular power or empty-dimensional request changed its original boundary behavior")
  let exactReading := cyclicParameters.toReading GaussianReading.identity rfl 1 (by decide +kernel) 0
    (by decide) (by decide +kernel)
  unless decide (adjunction.root - 1 ≠ 0) && exactReading.read (adjunction.root - 1) == 0 do
    throw (IO.userError "a formal nonzero coefficient was mistaken for a nonzero physical reading")
  Purelib.System.IO.println "Paid original matrix actions/products and singular power3: nonmultiplicative reading, \
    retained source-weight caches, empty horizon/dimension and physical-zero coefficient checked."

end TestPurelib.LinearAlgebra.Matrix.Reading
