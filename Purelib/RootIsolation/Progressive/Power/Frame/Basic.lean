module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Power.Gaussian
public import Purelib.Polynomial.Power.Gaussian.Progressive.Coefficients
import Purelib.RootIsolation.Owner.Family.Basic
public import Purelib.RootIsolation.Owner.Family.FTA
public import Purelib.RootIsolation.Owner.Family.Transport
public import Purelib.RootIsolation.Power.Isolation
public import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Target
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.Transport
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.Progressive.Chamber.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data
open Purelib.Polynomial
open Purelib.RootIsolation

/-!
# Retained exact chamber frames for power polynomials

The exact coefficient table and independently isolated root-owner family
retain their common polynomial and finite degree through the original transports.
-/

namespace Purelib.RootIsolation.Progressive.Power.Frame.Basic

/-- The exact coefficient table and its computed complete root-owner family
as a finite-monodromy chamber frame.

The retained reference table and independently computed root owners refer
to the same parameter and positive degree. Polynomial/count transports
retain those exact owners, their maximality and their coefficient allowances. -/
@[expose] public def chamberFrame
    {parameter : Gaussian.Basic.Canonical} (parameterNonzero : parameter ≠ 0)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    Progressive.Chamber.Frame.ChamberFrame where
  reference := Power.Gaussian.Progressive.Coefficients.coefficientTable parameter degree
  chamber := by
    let result := Power.Isolation.isolationResult parameterNonzero degree degreeAtLeastTwo
    let rawOwners :=
      Owner.Family.Basic.OwnerFamily.ofResult result
    have countSame : (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree).natDegree =
        (Power.Gaussian.Progressive.Coefficients.coefficientTable parameter degree).degree := by
      rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree,
        Power.Gaussian.Progressive.Coefficients.coefficientTable_degree]
    let owners : Owner.Family.Basic.OwnerFamily
        (Power.Gaussian.Progressive.Coefficients.coefficientTable parameter degree).polynomial
        (Power.Gaussian.Progressive.Coefficients.coefficientTable parameter degree).degree :=
      Owner.Family.Transport.castOwnerFamilyFull
        (Power.Gaussian.Progressive.Coefficients.coefficientTable_polynomial parameter degree).symm countSame rawOwners
    let squarefreeCertificate :=
      Power.Gaussian.Progressive.Coefficients.coefficientTableSquarefree parameterNonzero degree
    have tableDegreeAtLeastTwo :
        2 ≤ (Power.Gaussian.Progressive.Coefficients.coefficientTable parameter degree).degree := by
      rw [Power.Gaussian.Progressive.Coefficients.coefficientTable_degree]
      exact degreeAtLeastTwo
    exact
      { degreeAtLeastTwo := tableDegreeAtLeastTwo
        squarefree := squarefreeCertificate
        owners := owners
        referenceSmall := Power.Gaussian.Progressive.Coefficients.coefficientTable_allowances_lt parameter degree
          (Progressive.Chamber.Target.simpleRootChamberTarget_pos
            (Power.Gaussian.Progressive.Coefficients.coefficientTable parameter degree) squarefreeCertificate owners)
        referenceMaximality := by
          intro familyCount family pairwise
          let rawFamily : Fin familyCount →
              Track.Basic.WindingOneTrack
                (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree)
                (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
                  (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree)) := fun index =>
            Track.Transport.castWindingOneTrack
              (Power.Gaussian.Progressive.Coefficients.coefficientTable_polynomial parameter degree)
              (congrArg Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
                (Power.Gaussian.Progressive.Coefficients.coefficientTable_polynomial parameter degree))
              (family index)
          have rawPairwise : ∀ left right, left ≠ right →
              (rawFamily left).initial.box.Separated
                (rawFamily right).initial.box := by
            intro left right different
            simpa only [rawFamily,
              Track.Transport.castWindingOneTrack_initial_box] using
              pairwise left right different
          have bound := result.boxes.maximality rawFamily rawPairwise
          exact bound.trans_eq countSame }

/-- The constructed power-polynomial chamber frame retains the supplied root degree exactly.

The reference table has one exact state per original non-leading
coefficient. Its retained count is the same supplied positive root degree. -/
@[simp] public theorem chamberFrame_degree
    {parameter : Gaussian.Basic.Canonical} (parameterNonzero : parameter ≠ 0)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    (Progressive.Power.Frame.Basic.chamberFrame parameterNonzero degree degreeAtLeastTwo).degree =
      degree.value := by
  exact Power.Gaussian.Progressive.Coefficients.coefficientTable_degree parameter degree

/-- The constructed chamber frame's polynomial is exactly the original power polynomial at the supplied parameter.

The reference table retains the exact original non-leading coefficient
list. Reading its monic polynomial gives the same parameter and degree
power polynomial used by the independently computed owners. -/
@[simp] public theorem chamberFrame_polynomial
    {parameter : Gaussian.Basic.Canonical} (parameterNonzero : parameter ≠ 0)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    (Progressive.Power.Frame.Basic.chamberFrame parameterNonzero degree degreeAtLeastTwo).polynomial =
      Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree := by
  exact Power.Gaussian.Progressive.Coefficients.coefficientTable_polynomial parameter degree

end Purelib.RootIsolation.Progressive.Power.Frame.Basic
