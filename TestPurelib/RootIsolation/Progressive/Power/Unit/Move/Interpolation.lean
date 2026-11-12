module

import Purelib.RootIsolation.Progressive.Power.Unit.Move.Interpolation
import TestPurelib.Riemann.RootReconditioning
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Data.Gaussian.Field
import Purelib.System.IO

/-!
# Original unit-move interpolation regularity regressions

The quantified cases refer to the literal original bridge and its ownerAt.
The finite native checks use both original consecutive cubic circuit vertices
and the complete squarefree producer at zero, one half and one.
-/

namespace TestPurelib.RootIsolation.Progressive.Power.Unit.Move.Interpolation

open Purelib.RootIsolation
open Purelib.RootIsolation.Progressive.Power.Unit.Move.Interpolation
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational
open Purelib.Polynomial

section

variable {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : Power.Unit.Move.Budget.UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame
      (Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeTwo).Index)
    (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1)

/-- Every original bridge occurrence receives squarefree evidence at its exact original parameter reading. -/
example : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
    ((Progressive.Power.Unit.Move.Overlap.unitMoveBridge sourceUnit targetUnit degree degreeTwo small
      index).connection.polynomialAt time) :=
  (unitMoveBridge_input sourceUnit targetUnit degree degreeTwo small index time inside).squarefree

/-- Regularity is indexed by the original bridge ownerAt, with no replacement numerical owner. -/
example :
    (Progressive.Power.Unit.Move.Overlap.unitMoveBridge sourceUnit targetUnit degree degreeTwo small index).box =
      ((Progressive.Power.Unit.Move.Overlap.unitMoveBridge sourceUnit targetUnit degree degreeTwo small
        index).ownerAt time inside).box :=
  (Owner.Bridge.Basic.OwnerBridge.ownerAt_box _ time inside).symm

/-- The exact original input retains the actual original degree bound for every parameter and occurrence. -/
example : 2 ≤ (Power.Gaussian.rootPolynomial (Affine.line source (target - source) time) degree).natDegree := by
  have bound := (unitMoveBridge_input sourceUnit targetUnit degree degreeTwo small index time inside).degreeAtLeastTwo
  rw [unitMoveBridge_polynomialAt] at bound
  exact bound

end

/-- Check the finite regularity producer on the same original first cubic move at one rational parameter. -/
private def checkAt (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) : IO Unit := do
  let degree : RootDegree := ⟨3, by decide⟩
  let degreeTwo : 2 ≤ degree.value := by decide
  let source := TestPurelib.Riemann.RootReconditioning.sourceVertex degree degreeTwo
  let target := TestPurelib.Riemann.RootReconditioning.targetVertex degree degreeTwo
  let small := TestPurelib.Riemann.RootReconditioning.smallMove degree degreeTwo
  let frame := Progressive.Power.Unit.Frame.robustChamberFrame
    (Norm.Nonzero.nonzero_of_normSq_eq_one source.unit) source.unit degree degreeTwo
  let index : frame.Index := ⟨0, (by decide : 0 < 2).trans_le frame.chamber.degreeAtLeastTwo⟩
  let input := unitMoveBridge_input source.unit target.unit degree degreeTwo small index time inside
  let certificate := input.squarefree
  let polynomial := Power.Gaussian.rootPolynomial (Affine.line source.value (target.value - source.value) time) degree
  if certificate.unit == 0 then
    throw (IO.userError "original interpolated cubic squarefree producer returned zero gcd unit")
  if certificate.result.gcd != Dense.Basic.DensePolynomial.constant certificate.unit then
    throw (IO.userError "original interpolated cubic squarefree producer lost its retained gcd")
  for point in ([0, 1, ⟨1, 1⟩] : List Canonical) do
    if certificate.left.eval point * polynomial.eval point +
        certificate.right.eval point * (Dense.Gaussian.GCD.derivative polynomial).eval point != 1 then
      throw (IO.userError "original interpolated cubic retained Bezout coefficients failed")

/-- Execute the unchanged first cubic parameter move's exact regularity producer at both endpoints and its midpoint. -/
public def check : IO Unit := do
  checkAt 0 ⟨by decide, by decide⟩
  checkAt (1 / 2) ⟨by decide, by decide⟩
  checkAt 1 ⟨by decide, by decide⟩
  Purelib.System.IO.println "original unit-move interpolation: exact endpoint/midpoint squarefree inputs checked"

end TestPurelib.RootIsolation.Progressive.Power.Unit.Move.Interpolation
