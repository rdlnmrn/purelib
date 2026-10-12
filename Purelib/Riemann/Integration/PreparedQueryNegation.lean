module
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Value
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.RootContinuation.ClearBoxRootNegation
import Purelib.Polynomial.Clearance.Box.Region

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.RootIsolation.SquareRoot.Owner.Transport

public import Purelib.RootIsolation.SquareRoot.Preparation.FaceNegation
public import Purelib.Riemann.RootContinuation.SquareRootDifferentialNegation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Opposite root and coefficient channels of retained prepared queries

Queries at a common rational point retain their direct owners. Exact endpoint
casts align their parameter types without changing those owners. The existing
face-prefix certificates then construct cached opposite-root evidence and
the operational zero sum of the coefficients used by the integrator.
-/

namespace Purelib.Riemann.Integration.PreparedQueryNegation.PreparedEdge
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge (rootName)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.Value (differentialValue)
open Purelib.Approximation.Gaussian.Name.Coherent.Power (namedPower)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision parameterAt)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}

open Purelib.Data.Rat in
open Purelib.Riemann.Branches in
/-- The original prepared-edge query parameter evaluates to its retained geometric point. -/
theorem query_point_eq (parent : PreparedEdge curve differential) (fraction : Fraction.Rational) :
    parent.segment.pointAt (parameterAt parent.left parent.request fraction) = parent.point fraction :=
  PreparedSheetContinuation.pointAt_parameterAt parent.segment parent.within parent.left parent.request fraction

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.RootIsolation in
/-- Transport the actual direct-query root owner along the exact original point equality. -/
def ownerAtPoint (parent : PreparedEdge curve differential) (fraction : Fraction.Rational)
    (inside : 0 ≤ fraction ∧ fraction ≤ 1) (point : Basic.Canonical) (equal : parent.point fraction = point) :
    Owner (curve.polynomial.eval point) :=
  SquareRoot.Owner.Transport.castOwnerParameter (congrArg curve.polynomial.eval ((query_point_eq parent fraction).trans
    equal))
    (parent.directQueryOwner fraction inside)

open Purelib.Data.Gaussian in
open Purelib.RootIsolation in
/-- Exact parameter transport preserves the original root owner's name. -/
private theorem ownerName_cast {first last : Basic.Canonical} (equal : first = last) (owner : Owner first) :
    ownerName (SquareRoot.Owner.Transport.castOwnerParameter equal owner) = ownerName owner := by
  cases equal
  rfl

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The transported query owner retains the original edge root name at that fraction. -/
theorem ownerAtPoint_name (parent : PreparedEdge curve differential) (fraction : Fraction.Rational)
    (inside : 0 ≤ fraction ∧ fraction ≤ 1) (point : Basic.Canonical) (equal : parent.point fraction = point) :
    ownerName (ownerAtPoint parent fraction inside point equal) = parent.rootName fraction inside := by
  rw [ownerAtPoint, ownerName_cast, parent.rootName_eq_directQueryOwnerRootName]
  rfl

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Original differential coefficients at the same point cancel when their queried roots are opposite-equivalent.

Both coefficients use their actual cached root certificates, and the coordinate equality identifies the common original
differential numerator. -/
def coefficient_sum_zero_of_root_negation (first second : PreparedEdge curve differential)
    (left right : Fraction.Rational) (leftInside : 0 ≤ left ∧ left ≤ 1) (rightInside : 0 ≤ right ∧ right ≤ 1)
    (point_eq : first.point left = second.point right)
    (roots : Equivalence.NamedEquivalent (Name.Basic.Named.neg (first.rootName left leftInside))
      (second.rootName right rightInside)) :
    Equivalence.NamedEquivalent ((first.coefficient left leftInside).add (second.coefficient right rightInside)).name
      (Name.Basic.Named.exact 0) := by
  let firstRoot := Differentials.PreparedModels.rootAtCached curve first.segment first.within first.left first.owner
    first.request first.cached first.ordered first.small left leftInside
  let secondRoot := Differentials.PreparedModels.rootAtCached curve second.segment second.within second.left
    second.owner
    second.request second.cached second.ordered second.small right rightInside
  have negative : Equivalence.NamedEquivalent firstRoot.value.neg.name secondRoot.value.name := by
    unfold rootName at roots
    exact roots
  have cancelled := SquareRootDifferentialNegation.CertifiedSquareRoot.Certificate.quotient_sum_zero firstRoot
    secondRoot
    (Name.Coherent.Power.namedPower (Name.Coherent.CoherentNamed.Coherence.exact (second.point right))
      differential.exponent) negative
  change Equivalence.NamedEquivalent
    ((Differentials.Value.differentialValue differential (first.point left) firstRoot.value firstRoot.apart).add
      (Differentials.Value.differentialValue differential (second.point right) secondRoot.value secondRoot.apart)).name
        _
  rw [point_eq]
  exact cancelled

end Purelib.Riemann.Integration.PreparedQueryNegation.PreparedEdge

namespace Purelib.Riemann.Integration.PreparedQueryNegation.PreparedFaceTracePrefixes

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (ParentReached Reached)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedQueryNegation.PreparedEdge (query_point_eq ownerAtPoint ownerAtPoint_name
  coefficient_sum_zero_of_root_negation)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {box : Box} {base : Purelib.Data.Gaussian.Basic.Canonical} {source :
    OwnerFrame (curve.polynomial.eval base)} {sheet : Fin 2}
  {first second : CenteredEdge curve differential}

open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- A reached original parent's interior query remains in its retained face box. -/
theorem ParentReached.query_inside (reached : Observation.PreparedFaceTracePrefixes.ParentReached box (source.owners
  sheet) first)
    (fraction : Fraction.Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) : box.Contains (first.edge.point fraction) :=
      by
  have left := reached.first_inside
  have right := reached.last_inside
  rw [PreparedConstantModels.PreparedEdge.point_zero] at left
  rw [PreparedConstantModels.PreparedEdge.point_one] at right
  change box.Contains (first.edge.localSegment.pointAt fraction)
  rw [PreparedPathWinding.ClearSegment.pointAt_eq_line]
  exact Box.contains_line left right inside

open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
open Purelib.RootIsolation in
/-- The exact transported query owner remains reached from the original source owner. -/
theorem ParentReached.ownerAtPoint_reached (reached : Observation.PreparedFaceTracePrefixes.ParentReached box
  (source.owners sheet) first)
    (fraction : Fraction.Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1)
    (point : Basic.Canonical) (equal : first.edge.point fraction = point) :
    Observation.PreparedFaceTracePrefixes.Reached box (source.owners sheet)
      (PreparedQueryNegation.PreparedEdge.ownerAtPoint first.edge fraction inside point equal) :=
  (reached.query_reached fraction inside).castFinish ((PreparedQueryNegation.PreparedEdge.query_point_eq first.edge
    fraction).trans equal)
    (SquareRoot.Owner.Transport.castOwnerParameter_heq _ _).symm

open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
open Purelib.Riemann.RootContinuation in
/-- Opposite-owner evidence for the original two edge queries at their shared point.

The retained fractions, interval witnesses, exact point equality and frame index the actual transported query owners. -/
abbrev QueryNegation (first second : CenteredEdge curve differential)
    (left right : Fraction.Rational) (leftInside : 0 ≤ left ∧ left ≤ 1) (rightInside : 0 ≤ right ∧ right ≤ 1)
    (point_eq : first.edge.point left = second.edge.point right)
    (frame : OwnerFrame (curve.polynomial.eval (first.edge.point left))) :=
  ClearBoxRootNegation.SquareRootTrace.OwnerFrame.OppositeOwners frame (PreparedQueryNegation.PreparedEdge.ownerAtPoint
    first.edge left leftInside _ rfl)
    (PreparedQueryNegation.PreparedEdge.ownerAtPoint second.edge right rightInside _ point_eq.symm)

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Rat in
open Purelib.Polynomial.Clearance.Box in
open Purelib.RootIsolation in
/-- Construct opposite-owner evidence for original reached parent queries in the same clear face box.

The source sheets remain opposite, and the original reached traces, base containment, shared point and winding-one
reference determine the retained comparison. -/
def ParentReached.queryNegation (leftReached : Observation.PreparedFaceTracePrefixes.ParentReached box (source.owners
  sheet) first)
    (rightReached : Observation.PreparedFaceTracePrefixes.ParentReached box (source.owners (BranchCutLifts.otherSheet
      sheet)) second)
    (clearance : Region.RegionClearance curve.polynomial box)
    (reference : WindingOneLoop curve.polynomial base) (baseInside : box.Contains base)
    (left right : Fraction.Rational) (leftInside : 0 ≤ left ∧ left ≤ 1) (rightInside : 0 ≤ right ∧ right ≤ 1)
    (point_eq : first.edge.point left = second.edge.point right)
    (frame : OwnerFrame (curve.polynomial.eval (first.edge.point left))) :
    QueryNegation first second left right leftInside rightInside point_eq frame :=
  SquareRoot.Preparation.FaceNegation.oppositeOfReached (source := source) (sheet := sheet) frame clearance
    (BranchIsolation.degreePositive curve) reference baseInside
    (ParentReached.query_inside leftReached left leftInside)
    (ParentReached.ownerAtPoint_reached leftReached left leftInside _ rfl)
    (ParentReached.ownerAtPoint_reached rightReached right rightInside _ point_eq.symm)

open Purelib.Approximation.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
open Purelib.Riemann.RootContinuation in
/-- Read the retained negative-root equivalence at the original edge-query names. -/
def QueryNegation.root_equivalent {left right : Fraction.Rational}
    {leftInside : 0 ≤ left ∧ left ≤ 1} {rightInside : 0 ≤ right ∧ right ≤ 1}
    {point_eq : first.edge.point left = second.edge.point right}
    {frame : OwnerFrame (curve.polynomial.eval (first.edge.point left))}
    (data : QueryNegation first second left right leftInside rightInside point_eq frame) :
    Equivalence.NamedEquivalent (Name.Basic.Named.neg (first.edge.rootName left leftInside))
      (second.edge.rootName right rightInside) := by
  have equivalent := ClearBoxRootNegation.SquareRootTrace.OwnerFrame.OppositeOwners.equivalent data
  rw [PreparedQueryNegation.PreparedEdge.ownerAtPoint_name,
      PreparedQueryNegation.PreparedEdge.ownerAtPoint_name] at equivalent
  exact equivalent

open Purelib.Approximation.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
/-- The original queried differential coefficients cancel by their retained opposite-owner evidence. -/
def QueryNegation.coefficient_sum_zero {left right : Fraction.Rational}
    {leftInside : 0 ≤ left ∧ left ≤ 1} {rightInside : 0 ≤ right ∧ right ≤ 1}
    {point_eq : first.edge.point left = second.edge.point right}
    {frame : OwnerFrame (curve.polynomial.eval (first.edge.point left))}
    (data : QueryNegation first second left right leftInside rightInside point_eq frame) :
    Equivalence.NamedEquivalent ((first.edge.coefficient left leftInside).add (second.edge.coefficient right
      rightInside)).name
      (Name.Basic.Named.exact 0) :=
  PreparedQueryNegation.PreparedEdge.coefficient_sum_zero_of_root_negation first.edge second.edge left right leftInside
    rightInside point_eq
    (QueryNegation.root_equivalent data)

end Purelib.Riemann.Integration.PreparedQueryNegation.PreparedFaceTracePrefixes
