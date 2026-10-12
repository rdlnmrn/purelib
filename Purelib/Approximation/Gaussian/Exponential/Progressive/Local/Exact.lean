module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Exponential.Horner.Addition.Law
import Purelib.Approximation.Gaussian.Exponential.Horner.Addition.Sequence
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
import Purelib.Approximation.Gaussian.Exponential.Horner.Sequence
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.UnitDisk
public import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
public import Purelib.Approximation.Gaussian.Sequence.Equivalence
public import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Exact

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Exponential.Horner
open Purelib.Approximation.Gaussian.Exponential.Horner.Addition
open Purelib.Approximation.Gaussian.Exponential.Progressive.Local
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.UnitDisk
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication
open Purelib.Approximation.Gaussian.Sequence.Name

public section

/-!
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

/-- The progressive local-exponential approximation at an exact Gaussian input in the unit disk. -/
@[expose] def exactLocalExpApproximation (value : Data.Gaussian.Basic.Canonical)
    (unit : Data.Gaussian.Norm.Basic.normSq value ≤ 1) : Gaussian.Sequence.ApproximationData :=
  Name.approximation
    (Named.exact value)
    (Name.UnitDisk.exact value unit)

/-- The productive name generated from the exact-input local-exponential approximation. -/
@[expose] def exactLocalExpNamed (value : Data.Gaussian.Basic.Canonical) (unit :
  Data.Gaussian.Norm.Basic.normSq value ≤ 1) :
    Gaussian.Name.Basic.Named :=
  (Approximation.Gaussian.Exponential.Progressive.Local.Exact.exactLocalExpApproximation value unit).toNamed

/-- The exact-input progressive exponential sample is the finite Horner exponential at the same index. -/
@[simp] theorem exactLocalExpApproximation_sample
    (value : Data.Gaussian.Basic.Canonical) (unit : Data.Gaussian.Norm.Basic.normSq value ≤ 1) (index : Nat) :
    (Approximation.Gaussian.Exponential.Progressive.Local.Exact.exactLocalExpApproximation value unit).sample index =
      Gaussian.Exponential.Horner.Sample.sample value index :=
  rfl

/-- The local exponential addition theorem now stated for the actual arithmetic expression tree: the left side is
`Named.mul` of the two local progressive exponential outputs, not a separately wrapped product stream. -/
@[expose] def localExp_add_actual_named_equivalent {x y : Data.Gaussian.Basic.Canonical}
    (xUnit : Data.Gaussian.Norm.Basic.normSq x ≤ 1) (yUnit : Data.Gaussian.Norm.Basic.normSq y ≤ 1)
    (sumUnit : Data.Gaussian.Norm.Basic.normSq (x + y) ≤ 1) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        (Approximation.Gaussian.Exponential.Progressive.Local.Exact.exactLocalExpNamed x xUnit)
          (Approximation.Gaussian.Exponential.Progressive.Local.Exact.exactLocalExpNamed y yUnit))
      (Approximation.Gaussian.Exponential.Progressive.Local.Exact.exactLocalExpNamed (x + y) sumUnit) := by
  let leftApproximation := Approximation.Gaussian.Exponential.Progressive.Local.Exact.exactLocalExpApproximation x xUnit
  let rightApproximation := Approximation.Gaussian.Exponential.Progressive.Local.Exact.exactLocalExpApproximation y
    yUnit
  let productApproximation :=
    Sequence.expProductApproximation
      x y xUnit yUnit
  let sumApproximation :=
    Sequence.approximation (x + y) sumUnit
  have arithmeticBridge :
      Gaussian.Equivalence.NamedEquivalent
        (Named.mul
          leftApproximation.toNamed rightApproximation.toNamed)
        productApproximation.toNamed :=
    Bridge.mulToNamed_equivalent_pointwise leftApproximation rightApproximation
      productApproximation (by intro index; rfl)
  have analyticLaw :
      Gaussian.Equivalence.NamedEquivalent productApproximation.toNamed sumApproximation.toNamed :=
    Law.exp_add_named_equivalent
      xUnit yUnit sumUnit
  have sumSamples : ∀ index,
      sumApproximation.sample index =
        (Approximation.Gaussian.Exponential.Progressive.Local.Exact.exactLocalExpApproximation (x + y) sumUnit).sample
          index := by
    intro index
    rfl
  exact NamedEquivalent.trans
    arithmeticBridge
    (NamedEquivalent.trans analyticLaw
      (Equivalence.approximationEquivalent_toNamed
        (Equivalence.approximationEquivalentOfSamplesEq sumApproximation
          (Approximation.Gaussian.Exponential.Progressive.Local.Exact.exactLocalExpApproximation (x + y) sumUnit)
            sumSamples)))

end

end Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Exact
