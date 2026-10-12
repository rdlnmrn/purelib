module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Projective.Hermitian.Atom
public import Purelib.Geometry.Projective.Hermitian.Atom.Equality
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
import Purelib.RationalFunctions.Curve.Coordinates
import Purelib.RootIsolation.Curve.Boundary.Analysis
import Purelib.RootIsolation.Curve.Boundary.Complete.Basic
import Purelib.RootIsolation.Curve.Boundary.Complete.Sample
public import Purelib.RootIsolation.Curve.Boundary.Winding.Persistence
public import Purelib.RootIsolation.Curve.Boundary.Winding.Resolution
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Denominator
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Family.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.SignTest
import Purelib.Data.Rat.SignTest.Equality
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Boundary.Event.Basic
import Purelib.RootIsolation.Curve.Boundary.Profile.Boundary
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Basic

open Purelib.RootIsolation.Curve.Boundary.Complete.Basic (BoundaryCompleteRequestEntry)

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Comparing complete CCL profile children with winding-one states

The complete profile refinement is parameterized by an arbitrary finite
pairwise-separated box family.  This module instantiates that interface with
the boxes carried by explicit finite winding-one states.  Every retained
profile child is then compared with the actual numerical states, not with an
unrelated list of boxes.

An owned result records only a displayed Gaussian-rational curve sample in
one state, together with its small polynomial residual and nonzero derivative.
The sample-owner comparison remains pointwise and is never promoted to root
existence.  A separate affine-family scan preserves the stronger semantics
already computed for each profile: either displayed rational factor zeros are
inside the dispatched box, or the complete rational non-pole event cylinder
is outside it.  Neither alternative asserts that a factor zero exists.
-/

namespace Purelib.RootIsolation.CCL.Persistent.Event.Atom
section Boundary

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
variable {denominatorMargin : Fraction.Rational}
variable {marginPositive : 0 < denominatorMargin}
variable {atom : Geometry.Projective.Hermitian.Atom}
variable {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
  marginPositive atom}

/-- Exact weak/strict equality ownership of the retained rational event
sample.  The result concerns the unresolved CCL atom only; it does not claim
that the sample is a zero of the polynomial. -/
inductive PersistentDescendantAtomClassification
    {epsilon : Fraction.Rational}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient)
    (ownerIndex : Fin family.boxes.length)
    (later : State.WindingOne.Basic.WindingOneState p ambient) where
  /-- The actual retained persistent descendant sample satisfies the dispatched Hermitian atom. -/ | owned
      (holds : atom.Holds
        (entry.parent.parent.chart.parameterization.curve.point
          (Curve.Boundary.Winding.Persistence.persistentDescendantSample squarefree entry family ownerIndex
            later).parameter))
  /-- The actual retained persistent descendant sample fails the dispatched Hermitian atom. -/ | excluded
      (fails : ¬atom.Holds
        (entry.parent.parent.chart.parameterization.curve.point
          (Curve.Boundary.Winding.Persistence.persistentDescendantSample squarefree entry family ownerIndex
            later).parameter))

/-- Execute the atom's six-way equality convention at the exact rational
boundary sample. -/
def classifyPersistentDescendantAtom
    {epsilon : Fraction.Rational}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient)
    (ownerIndex : Fin family.boxes.length)
    (later : State.WindingOne.Basic.WindingOneState p ambient) :
    PersistentDescendantAtomClassification squarefree entry family ownerIndex
      later := by
  let point := entry.parent.parent.chart.parameterization.curve.point
    (Curve.Boundary.Winding.Persistence.persistentDescendantSample squarefree entry family ownerIndex later).parameter
  have onBoundary : atom.form.eval point = 0 := by
    simpa only [point] using
      Curve.Boundary.Winding.Persistence.persistentDescendantSample_onBoundary squarefree entry family ownerIndex
        later
  match decision :
      Geometry.Projective.Hermitian.atomEqualityDecision atom with
  | .owned holds =>
      exact .owned
        (Geometry.Projective.Hermitian.atom_holds_of_boundary onBoundary
          holds decision)
  | .excluded fails =>
      exact .excluded
        (Geometry.Projective.Hermitian.atom_not_holds_of_boundary onBoundary
          fails decision)

/-- Exact weak/strict equality ownership of the explicit near-box sample.
This classifies the dispatched CCL atom only and does not classify the sample
as a polynomial root. -/
inductive NearBoxDescendantAtomClassification
    {epsilon : Fraction.Rational}
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (denominator :
      Curve.Event.Profile.Complete.Denominator.ProfileDenominatorRelation
        entry.parent.event.1)
    (apart : Dense.Rational.Bezout.Basic.CoprimeCertificate
      entry.parent.event.1.profile.factor.polynomial
        (Curve.Coordinates.denominatorNormSq
          entry.parent.parent.chart.parameterization.curve))
    (radius : Fraction.Rational) where
  /-- The actual retained near-box descendant sample satisfies the dispatched Hermitian atom. -/ | owned
      (holds : atom.Holds
        (entry.parent.parent.chart.parameterization.curve.point
          (Curve.Boundary.Complete.Sample.nearBoxDescendantSample
            entry denominator apart radius).parameter))
  /-- The actual retained near-box descendant sample fails the dispatched Hermitian atom. -/ | excluded
      (fails : ¬atom.Holds
        (entry.parent.parent.chart.parameterization.curve.point
          (Curve.Boundary.Complete.Sample.nearBoxDescendantSample
            entry denominator apart radius).parameter))

/-- Execute the atom's finite equality convention at the near-box sample. -/
def classifyNearBoxDescendantAtom
    {epsilon : Fraction.Rational}
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (denominator :
      Curve.Event.Profile.Complete.Denominator.ProfileDenominatorRelation
        entry.parent.event.1)
    (apart : Dense.Rational.Bezout.Basic.CoprimeCertificate
      entry.parent.event.1.profile.factor.polynomial
        (Curve.Coordinates.denominatorNormSq
          entry.parent.parent.chart.parameterization.curve))
    (radius : Fraction.Rational) :
    NearBoxDescendantAtomClassification entry denominator apart radius := by
  let point := entry.parent.parent.chart.parameterization.curve.point
    (Curve.Boundary.Complete.Sample.nearBoxDescendantSample
      entry denominator apart radius).parameter
  have onBoundary : atom.form.eval point = 0 := by
    simpa only [point] using
      Curve.Boundary.Winding.Resolution.nearBoxDescendantSample_onBoundary entry denominator apart radius
  match decision :
      Geometry.Projective.Hermitian.atomEqualityDecision atom with
  | .owned holds =>
      exact .owned
        (Geometry.Projective.Hermitian.atom_holds_of_boundary onBoundary
          holds decision)
  | .excluded fails =>
      exact .excluded
        (Geometry.Projective.Hermitian.atom_not_holds_of_boundary onBoundary
          fails decision)
end Boundary

end Purelib.RootIsolation.CCL.Persistent.Event.Atom

end
