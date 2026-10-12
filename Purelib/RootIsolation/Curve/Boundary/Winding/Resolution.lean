module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Interior
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Basic
import Purelib.RationalFunctions.Curve.Coordinates
import Purelib.RootIsolation.Curve.Boundary.Analysis
import Purelib.RootIsolation.Curve.Boundary.Complete.Basic
import Purelib.RootIsolation.Curve.Boundary.Complete.Sample
import Purelib.RootIsolation.Curve.Boundary.Winding.Budget
public import Purelib.RootIsolation.Curve.Boundary.Winding.Pole
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Classification
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Denominator
import Purelib.RootIsolation.State.WindingOne.Family.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Factorization.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Boundary.Complete.Control
import Purelib.RootIsolation.Curve.Boundary.Complete.Ownership
import Purelib.RootIsolation.Curve.Boundary.Event.Basic
import Purelib.RootIsolation.Curve.Boundary.Profile.Boundary
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Classification
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic

open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)
open Purelib.Polynomial.Dense.Rational.Bezout.Basic (CoprimeCertificate)
open Purelib.RootIsolation.Curve.Boundary.Winding.Budget (ClassifiedChild)
open Purelib.RootIsolation.State.WindingOne.Family.Basic (WindingFamily)

open Purelib.Data

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

namespace Purelib.RootIsolation.Curve.Boundary.Winding.Resolution
section Boundary

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
variable {reference : LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current :
  Box}
variable {denominatorMargin : Fraction.Rational}
variable {marginPositive : 0 < denominatorMargin}
variable {atom : Geometry.Projective.Hermitian.Atom}
variable {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
  marginPositive atom}

/-! ## Whole-event affine resolution before rational sample ownership -/

set_option genInjectivity false in
/-- Strong semantic alternative for a finite list of classified children.
The retained branch identifies a profile whose every displayed rational
factor zero lies in the dispatched box.  The outside branch excludes every
rational non-pole parameter of every listed child from that box.  Neither
branch asserts that a factor zero exists. -/
inductive BoundaryAffineResolution
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    List (ClassifiedChild (boundary := boundary) squarefree family) → Type
  /-- A retained child has an apart denominator and nonnegative conditions, and every displayed nonpole factor zero lies
    in the dispatched box. -/ | inside
      {values : List
        (ClassifiedChild (boundary := boundary) squarefree family)}
      (child : ClassifiedChild (boundary := boundary) squarefree family)
      (member : child ∈ values)
      (denominatorCertificate :
        CoprimeCertificate
          child.entry.parent.event.1.profile.factor.polynomial
          (Curve.Coordinates.denominatorNormSq
            child.entry.parent.parent.chart.parameterization.curve))
      (denominatorRelationEq :
        (Curve.Event.Profile.Complete.Denominator.profileDenominatorRelation
          child.entry.parent.event.1).relation =
            Dense.Rational.Factorization.ConditionRelation.apart
              denominatorCertificate)
      (denominatorLower : ∀ parameter : Fraction.Rational,
        child.entry.child.cell.interval.Contains parameter →
        (Curve.Event.Profile.Complete.Denominator.profileDenominatorRelation
          child.entry.parent.event.1).apartLower denominatorCertificate ≤
          Data.Gaussian.Norm.Basic.normSq
            (child.entry.parent.parent.chart.parameterization.curve.denominatorAt
              parameter))
      (relationsNonnegative : ∀ relation ∈
        child.entry.parent.event.1.profile.relations,
        Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.ConditionNonnegative
          child.entry.child relation)
      (contains : ∀ parameter : Fraction.Rational,
        child.entry.child.cell.interval.Contains parameter →
        child.entry.parent.event.1.profile.factor.polynomial.eval parameter =
          0 →
        child.entry.parent.parent.chart.parameterization.curve.denominatorAt
          parameter ≠ 0 →
        current.Contains
          (child.entry.parent.parent.chart.parameterization.curve.point
            parameter)) :
      BoundaryAffineResolution squarefree family values
  /-- Every displayed nonpole parameter in every listed child lies outside the dispatched box. -/ | outside
      {values : List
        (ClassifiedChild (boundary := boundary) squarefree family)}
      (excludes : ∀ child ∈ values, ∀ parameter : Fraction.Rational,
        child.entry.child.cell.interval.Contains parameter →
        child.entry.parent.parent.chart.parameterization.curve.denominatorAt
          parameter ≠ 0 →
        ¬current.Contains
          (child.entry.parent.parent.chart.parameterization.curve.point
            parameter)) :
      BoundaryAffineResolution squarefree family values

constructive_injectivity BoundaryAffineResolution

/-- Execute the finite first-inside/whole-event-outside scan using each
child's exact affine profile classification. -/
def resolveAffineChildren
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    (values : List
      (ClassifiedChild (boundary := boundary) squarefree family)) →
      BoundaryAffineResolution squarefree family values
  | [] => .outside (by intro child member; exact (List.not_mem_nil member).elim)
  | head :: tail =>
      match head.denominatorClassification with
      | .pole cofactor factorization relationEq =>
          let headExcludes := Curve.Boundary.Winding.Pole.pole_child_excludes_current squarefree family
            head cofactor factorization relationEq
          match resolveAffineChildren squarefree family tail
            with
          | .inside child member denominatorCertificate denominatorRelationEq
              denominatorLower relationsNonnegative contains =>
              .inside child (List.mem_cons_of_mem head member)
                denominatorCertificate denominatorRelationEq denominatorLower
                relationsNonnegative contains
          | .outside tailExcludes =>
              .outside (by
                intro child member
                rcases Data.List.Membership.mem_cons.mp member with rfl | tailMember
                · exact headExcludes
                · exact tailExcludes child tailMember)
      | .apart denominatorCertificate denominatorRelationEq denominatorLower =>
          match head.boxClassification with
          | .inside relationsNonnegative =>
              .inside head List.mem_cons_self denominatorCertificate
                denominatorRelationEq denominatorLower relationsNonnegative
                (head.entry.child.contains_of_relations_nonnegative
                  relationsNonnegative)
          | .outside relation member negative =>
              let headExcludes :=
                head.entry.child.excludes_of_relation_negative relation member
                  negative
              match resolveAffineChildren squarefree family tail
                with
              | .inside child member certificate relationEq lower
                  relationsNonnegative contains =>
                  .inside child (List.mem_cons_of_mem head member) certificate
                    relationEq lower relationsNonnegative contains
              | .outside tailExcludes =>
                  .outside (by
                    intro child member
                    rcases Data.List.Membership.mem_cons.mp member with rfl | tailMember
                    · exact headExcludes
                    · exact tailExcludes child tailMember)

/-- Strong initial resolution of the complete winding request family.  Its
outside result concerns every rational non-pole point of every retained event
cylinder, rather than one arbitrarily chosen sample per child. -/
def resolveWindingAffineFamily
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    BoundaryAffineResolution squarefree family
      (Curve.Boundary.Winding.Budget.classifiedWindingRequestFamily (boundary := boundary) squarefree
        family) :=
  resolveAffineChildren squarefree family
    (Curve.Boundary.Winding.Budget.classifiedWindingRequestFamily (boundary := boundary) squarefree family)

/-! ## Explicit rational sample from the strong affine resolution -/

set_option genInjectivity false in
/-- Strengthening of the semantic affine resolution against a supplied outer
box.  An inside result carries one bounded-search rational sample in the
outer box; the outside result keeps whole-cylinder exclusion.  The inside
constructor does not assert that the profile factor, or `p`, vanishes at the
sample. -/
inductive BoundaryNearBoxResolution
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (outer : Box) (strict : current.StrictInterior outer) :
    List (ClassifiedChild (boundary := boundary) squarefree family) → Type
  /-- A retained child has a computed nonpole descendant sample in the supplied strict outer box. -/ | inside
      {values : List
        (ClassifiedChild (boundary := boundary) squarefree family)}
      (child : ClassifiedChild (boundary := boundary) squarefree family)
      (member : child ∈ values)
      (denominatorCertificate :
        CoprimeCertificate
          child.entry.parent.event.1.profile.factor.polynomial
          (Curve.Coordinates.denominatorNormSq
            child.entry.parent.parent.chart.parameterization.curve))
      (denominatorRelationEq :
        (Curve.Event.Profile.Complete.Denominator.profileDenominatorRelation
          child.entry.parent.event.1).relation =
            Dense.Rational.Factorization.ConditionRelation.apart
              denominatorCertificate)
      (relationsNonnegative : ∀ relation ∈
        child.entry.parent.event.1.profile.relations,
        Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.ConditionNonnegative
          child.entry.child relation)
      (sampleInside : outer.Contains
        (child.entry.parent.parent.chart.parameterization.curve.point
          (Curve.Boundary.Complete.Sample.nearBoxDescendantSample
            child.entry
            (Curve.Event.Profile.Complete.Denominator.profileDenominatorRelation
              child.entry.parent.event.1)
            denominatorCertificate
            (Box.Interior.strictBoxGap current
              outer)).parameter)) :
      BoundaryNearBoxResolution squarefree family outer strict
        values
  /-- Every displayed nonpole parameter of every listed child remains outside the dispatched box. -/ | outside
      {values : List
        (ClassifiedChild (boundary := boundary) squarefree family)}
      (excludes : ∀ child ∈ values, ∀ parameter : Fraction.Rational,
        child.entry.child.cell.interval.Contains parameter →
        child.entry.parent.parent.chart.parameterization.curve.denominatorAt
          parameter ≠ 0 →
        ¬current.Contains
          (child.entry.parent.parent.chart.parameterization.curve.point
            parameter)) :
      BoundaryNearBoxResolution squarefree family outer strict
        values

constructive_injectivity BoundaryNearBoxResolution

/-- Convert the strong finite affine scan into either its whole-cylinder
outside proof or an explicit rational sample in any supplied strict outer
box. -/
def BoundaryAffineResolution.toNearBox
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    {values : List
      (ClassifiedChild (boundary := boundary) squarefree family)}
    (resolution : BoundaryAffineResolution squarefree family values)
    (outer : Box) (strict : current.StrictInterior outer) :
    BoundaryNearBoxResolution squarefree family outer strict values := by
  cases resolution with
  | inside child member denominatorCertificate denominatorRelationEq
      denominatorLower relationsNonnegative _contains =>
      let denominator :=
        Curve.Event.Profile.Complete.Denominator.profileDenominatorRelation
          child.entry.parent.event.1
      let radius :=
        Box.Interior.strictBoxGap current outer
      have radiusPositive : 0 < radius := by
        simpa only [radius] using
          Box.Interior.strictBoxGap_pos strict
      have near :=
        Curve.Boundary.Complete.Sample.nearBoxDescendantSample_within_radius
          child.entry denominator denominatorCertificate denominatorLower
            relationsNonnegative radiusPositive
      exact .inside child member denominatorCertificate denominatorRelationEq
        relationsNonnegative
        (Box.Interior.contains_of_within_strictBoxGap
          (inner := current)
          (by simpa only [denominator, radius] using near))
  | outside excludes =>
      exact .outside excludes

/-- Execute the complete winding-family scan and, in its inside branch,
construct the displayed rational near-event sample in a supplied strict outer
box. -/
def resolveWindingNearBoxFamily
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (outer : Box) (strict : current.StrictInterior outer) :
    BoundaryNearBoxResolution squarefree family outer strict
      (Curve.Boundary.Winding.Budget.classifiedWindingRequestFamily (boundary := boundary) squarefree
        family) :=
  (resolveWindingAffineFamily (boundary := boundary) squarefree family).toNearBox
    squarefree family outer strict

/-- The bounded-search near-box sample lies exactly on the dispatched
Hermitian boundary because every parameter of its rational chart does. -/
theorem nearBoxDescendantSample_onBoundary
    {epsilon : Fraction.Rational}
    (entry :
      Curve.Boundary.Complete.Basic.BoundaryCompleteRequestEntry
        boundary epsilon)
    (denominator :
      Curve.Event.Profile.Complete.Denominator.ProfileDenominatorRelation
        entry.parent.event.1)
    (apart : CoprimeCertificate
      entry.parent.event.1.profile.factor.polynomial
        (Curve.Coordinates.denominatorNormSq
          entry.parent.parent.chart.parameterization.curve))
    (radius : Fraction.Rational) :
    atom.form.eval
        (entry.parent.parent.chart.parameterization.curve.point
          (Curve.Boundary.Complete.Sample.nearBoxDescendantSample
            entry denominator apart radius).parameter) = 0 :=
  entry.parent.parent.chart.parameterization.onBoundary
    (Curve.Boundary.Complete.Sample.nearBoxDescendantSample
      entry denominator apart radius).parameter
    (Curve.Boundary.Complete.Sample.nearBoxDescendantSample
      entry denominator apart radius).denominatorNonzero
end Boundary

end Purelib.RootIsolation.Curve.Boundary.Winding.Resolution

end
