module

import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Rational
import Purelib.LinearAlgebra.Matrix.Integral.Word
import Purelib.LinearAlgebra.Matrix.Multiplication
meta import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Rational
meta import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
meta import Purelib.LinearAlgebra.Matrix.Basic
meta import Purelib.LinearAlgebra.Matrix.Multiplication
meta import Purelib.Data.Gaussian.Basic
meta import Purelib.Data.Rat.Fraction

open Purelib.Approximation.Gaussian.Name.Coherent

/-!
# Exact ordered rational domains and hidden intermediate poles

An inverse pair of shear matrices has identity final product. At minus one
half its first step is undefined, while the ordered inspection succeeds at
one and returns the exact original value. A later pole retains its successful
first step and reports the next original index.
-/

namespace TestPurelib.Curves.Legendre.RationalWords

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.LinearAlgebra.Matrix
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)
open Purelib.Data.Gaussian.Basic (Canonical)

/-- The original integer shear with one signed off-diagonal coefficient. -/
private def shear (coefficient : Int) : IntegralMatrix := matrixOfFn fun row column =>
  if row.val = 0 then if column.val = 0 then 1 else coefficient
  else if column.val = 0 then 0 else 1

example : Integral.Word.matrixProduct [shear 2, shear (-2)] = Multiplication.identity := by
  apply matrix_ext
  intro row column
  refine Fin.cases ?_ (fun tail => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) tail) row
  · refine Fin.cases ?_ (fun tail => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) tail) column
    · decide +kernel
    · decide +kernel
  · refine Fin.cases ?_ (fun tail => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) tail) column
    · decide +kernel
    · decide +kernel

example {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} (execution : Rational.Execution input matrices) (index : Nat)
    (failed : execution.firstUndefined = some index) :
    let stopped := execution.stopped index failed
    stopped.reading.value = 0 ∧ execution.prefix.length = index :=
  let stopped := execution.stopped index failed
  ⟨stopped.zero, stopped.index_eq⟩

example {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} (execution : Rational.Execution input matrices)
    (completed : execution.firstUndefined = none) (other : Step.StepPreparations tau matrices) :
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent execution.output.name
      (Step.stepAction tau matrices other).name := execution.agrees_with_preparations completed other

example {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} (execution : Rational.Execution input matrices)
    (completed : execution.firstUndefined = none) (other : Fold.Basic.FoldPreparations tau matrices) :
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent execution.output.name
      (Fold.Basic.foldAction tau matrices other).name := execution.agrees_with_fold completed other

example {tau : CoherentNamed} {input : RationalSidecar tau}
    {first second : List IntegralMatrix} (execution : Rational.Execution input first)
    (completed : execution.firstUndefined = none) (next : Rational.Execution execution.reading second) :
    (execution.append completed next).output = next.output := execution.append_output completed next

example {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} (execution : Rational.Execution input matrices)
    (completed : execution.firstUndefined = none) :
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent execution.output.name
      (Purelib.Riemann.Integration.LegendreModularMonodromy.fractionalLinear
        (Integral.Word.matrixProduct matrices) tau
        (Fold.Basic.FoldPreparations.combined matrices (execution.fullFoldPreparations completed))).name :=
  execution.agrees_with_folded_output completed

example {tau : CoherentNamed} {input : RationalSidecar tau}
    {forward reverse : List IntegralMatrix} (execution : Rational.Execution input forward)
    (completed : execution.firstUndefined = none) (next : Rational.Execution execution.reading reverse)
    (reverseComplete : next.firstUndefined = none)
    (inverse : Multiplication.mul (Integral.Word.matrixProduct reverse) (Integral.Word.matrixProduct forward) =
      Multiplication.identity) :
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent next.output.name tau.name :=
  execution.reversal completed next reverseComplete inverse

/-- Exercise the actual ordered inspector at successful, initially blocked and later-blocked rational inputs. -/
private meta def checkDomains : IO Unit := do
  let matrix := fun coefficient : Int => matrixOfFn fun (row column : Fin 2) =>
    if row.val = 0 then if column.val = 0 then (1 : Int) else coefficient
    else if column.val = 0 then 0 else 1
  let forward := matrix 2
  let inverse := matrix (-2)
  let pole := RationalSidecar.exact (-1 / 2 : Canonical)
  let blocked := Rational.inspect pole [forward, inverse]
  unless blocked.firstUndefined = some 0 ∧ blocked.prefix.length = 0 ∧ blocked.remaining.length = 2 do
    throw (IO.userError "the identity final matrix hid its undefined first step")
  let source := RationalSidecar.exact (1 : Canonical)
  let completed := Rational.inspect source [forward, inverse]
  unless completed.firstUndefined = none ∧ completed.prefix.length = 2 ∧ completed.reading.value = 1 do
    throw (IO.userError "the prepared rational inverse pair did not return its original value")
  unless blocked.foldData.1.value = 1 do
    throw (IO.userError "folding a blocked prefix crossed its undefined first step")
  let later := Rational.inspect pole [matrix 0, forward, inverse]
  unless later.firstUndefined = some 1 ∧ later.prefix.length = 1 ∧ later.remaining.length = 2 do
    throw (IO.userError "the later pole lost its exact prepared prefix or original index")
  let first := Rational.inspect source [forward]
  if completed : first.firstUndefined = none then
    let next := Rational.inspect first.reading [inverse]
    let joined := first.append completed next
    let folded := joined.foldData
    unless folded.1.value = 1 do
      throw (IO.userError "combined denominator did not consume the cached successful row readings")
    unless joined.firstUndefined = none ∧ joined.prefix.length = 2 ∧ joined.reading.value = 1 do
      throw (IO.userError "cached continuation did not retain the completed original prefix")
    let continued := first.continue completed [inverse]
    unless continued.firstUndefined = none ∧ continued.reading.value = 1 do
      throw (IO.userError "continuation did not inspect the new request at the cached output")
  else throw (IO.userError "the first cached continuation step was not productive")

#eval checkDomains

end TestPurelib.Curves.Legendre.RationalWords
