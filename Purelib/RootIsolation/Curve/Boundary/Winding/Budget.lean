module
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.List.Minimum
import Purelib.Geometry.Projective.Chordal.Box.Interior
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.RootIsolation.Curve.Boundary.Analysis
import Purelib.RootIsolation.Curve.Boundary.Complete.Basic
import Purelib.RootIsolation.Curve.Boundary.Complete.Control
public import Purelib.RootIsolation.Curve.Boundary.Complete.Ownership
import Purelib.RootIsolation.Curve.Boundary.Profile.Boundary
import Purelib.RootIsolation.Curve.Boundary.Profile.Family
import Purelib.RootIsolation.State.WindingOne.Family.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.RootIsolation.State.WindingOne.Family.Clearance
public import Purelib.RootIsolation.State.WindingOne.Family.Interior
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.RootIsolation.Curve.Boundary.Event.Basic

open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)
open Purelib.RootIsolation.State.WindingOne.Family.Basic (WindingFamily)

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

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

namespace Purelib.RootIsolation.Curve.Boundary.Winding.Budget
section Boundary

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
variable {reference : LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current :
  Box}
variable {denominatorMargin : Fraction.Rational}
variable {marginPositive : 0 < denominatorMargin}
variable {atom : Geometry.Projective.Hermitian.Atom}
variable {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
  marginPositive atom}

/-- Finite chart/box targets making a denominator-equality profile
projectively closer to `ω` than any point of the corresponding finite winding
box. -/
@[expose] def poleExclusionTargets
    (family : WindingFamily p ambient) : List Fraction.Rational :=
  (Curve.Boundary.Profile.Family.boundaryProfileEventFamily
    boundary).flatMap fun parent =>
      (parent.parent.chart.parameterization.weightLower *
        Geometry.Projective.Chordal.Box.Interior.infinityBoxGap current) ^ 2 ::
        family.boxes.map fun targetBox =>
          (parent.parent.chart.parameterization.weightLower *
            Geometry.Projective.Chordal.Box.Interior.infinityBoxGap targetBox) ^ 2

/-- Every finite chart-and-box pole-exclusion target is positive. -/
theorem poleExclusionTargets_positive
    (family : WindingFamily p ambient) :
    ∀ target ∈ poleExclusionTargets (boundary := boundary) family,
      0 < target := by
  intro target member
  dsimp only [poleExclusionTargets] at member
  have member := Data.List.Flatten.mem_flatMap.mp member
  rcases member with ⟨parent, _parentMember, targetMember⟩
  rcases Data.List.Membership.mem_cons.mp targetMember with rfl | targetMember
  · exact Fraction.Order.Arithmetic.pow_pos_direct
      (Fraction.Order.Arithmetic.mul_pos_direct
        parent.parent.chart.parameterization.weightLowerPositive
        (Geometry.Projective.Chordal.Box.Interior.infinityBoxGap_pos current))
      2
  have targetMember := Data.List.Map.mem_map.mp targetMember
  rcases targetMember with ⟨targetBox, _boxMember, rfl⟩
  exact Fraction.Order.Arithmetic.pow_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct
      parent.parent.chart.parameterization.weightLowerPositive
      (Geometry.Projective.Chordal.Box.Interior.infinityBoxGap_pos targetBox))
    2

/-- One positive rational target below every finite chart/box pole-exclusion
target. -/
@[expose] def poleExclusionTarget
    (family : WindingFamily p ambient) : Fraction.Rational :=
  Data.Rat.List.Minimum.RegionOwnership.positiveMinimum
    (poleExclusionTargets (boundary := boundary) family)

/-- The common target below all retained pole-exclusion requests is positive. -/
theorem poleExclusionTarget_pos
    (family : WindingFamily p ambient) :
    0 < poleExclusionTarget (boundary := boundary) family :=
  Data.Rat.List.Minimum.RegionOwnership.positiveMinimum_pos _
    (poleExclusionTargets_positive (boundary := boundary) family)

/-- The common pole-exclusion target is no larger than the target for the supplied retained chart and family box. -/
theorem poleExclusionTarget_le
    (family : WindingFamily p ambient)
    (parent : RootIsolation.Curve.Boundary.Profile.BoundaryProfileEventEntry
      boundary)
    (parentMember : parent ∈
      Curve.Boundary.Profile.Family.boundaryProfileEventFamily
        boundary)
    (index : Fin family.boxes.length) :
    poleExclusionTarget (boundary := boundary) family ≤
      (parent.parent.chart.parameterization.weightLower *
        Geometry.Projective.Chordal.Box.Interior.infinityBoxGap
          (family.boxes.get index)) ^ 2 := by
  apply
    Data.Rat.List.Minimum.RegionOwnership.positiveMinimum_le_of_mem
  dsimp only [poleExclusionTargets]
  apply Data.List.Flatten.mem_flatMap.mpr
  refine ⟨parent, parentMember, ?_⟩
  exact List.mem_cons_of_mem _ (Data.List.Map.mem_map.mpr
    ⟨family.boxes.get index, List.get_mem family.boxes index, rfl⟩)

/-- The common pole-exclusion target also covers the boundary's dispatched
box itself, independently of the auxiliary winding family. -/
theorem poleExclusionTarget_le_current
    (family : WindingFamily p ambient)
    (parent : RootIsolation.Curve.Boundary.Profile.BoundaryProfileEventEntry
      boundary)
    (parentMember : parent ∈
      Curve.Boundary.Profile.Family.boundaryProfileEventFamily
        boundary) :
    poleExclusionTarget (boundary := boundary) family ≤
      (parent.parent.chart.parameterization.weightLower *
        Geometry.Projective.Chordal.Box.Interior.infinityBoxGap current) ^ 2 := by
  apply
    Data.Rat.List.Minimum.RegionOwnership.positiveMinimum_le_of_mem
  dsimp only [poleExclusionTargets]
  apply Data.List.Flatten.mem_flatMap.mpr
  exact ⟨parent, parentMember, List.mem_cons_self⟩

/-- One target simultaneously below the squarefree derivative threshold, one
quarter of every state clearance, every state's uniform projective interior
gap, and every chart/box pole-exclusion target. -/
@[expose] def windingTarget
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) : Fraction.Rational :=
  min (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree ambient)
    (min (family.clearanceTarget / 4)
      (min family.interiorGapTarget
        (poleExclusionTarget (boundary := boundary) family)))

/-- The shared derivative, clearance, interior-gap and pole-exclusion target is positive. -/
theorem windingTarget_pos
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    0 < windingTarget (boundary := boundary) squarefree family :=
  Fraction.Order.Basic.lt_min
    (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold_pos squarefree ambient)
    (Fraction.Order.Basic.lt_min
      (Fraction.Order.Field.div_pos_direct family.clearanceTarget_pos
        (by decide))
      (Fraction.Order.Basic.lt_min family.interiorGapTarget_pos
        (poleExclusionTarget_pos (boundary := boundary) family)))

/-- The shared winding target satisfies the squarefree derivative threshold on the original ambient box. -/
theorem windingTarget_le_derivativeThreshold
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    windingTarget (boundary := boundary) squarefree family ≤
      Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree ambient :=
  Fraction.Order.Basic.min_le_left _ _

/-- The shared winding target is no larger than one quarter of the family's retained clearance target. -/
theorem windingTarget_le_clearanceQuarter
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    windingTarget (boundary := boundary) squarefree family ≤
      family.clearanceTarget / 4 :=
  (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)

/-- The shared winding target satisfies the family's original projective interior-gap target. -/
theorem windingTarget_le_interiorGap
    (squarefree : SquarefreeCertificate p)
  (family : WindingFamily p ambient) :
    windingTarget (boundary := boundary) squarefree family ≤
      family.interiorGapTarget :=
  (Fraction.Order.Basic.min_le_right _ _).trans
    ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))

/-- The shared winding target satisfies every retained chart-and-box pole-exclusion requirement. -/
theorem windingTarget_le_poleExclusion
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    windingTarget (boundary := boundary) squarefree family ≤
      poleExclusionTarget (boundary := boundary) family :=
  (Fraction.Order.Basic.min_le_right _ _).trans
    ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _))

/-- Shared request width specialized to all derivative, strict-interior,
projective-cylinder, and separated-family requirements. -/
@[expose] def windingRequestWidth
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) : Fraction.Rational :=
  Curve.Boundary.Complete.Control.boundaryControlledRequestWidth
    boundary family.boxes family.boxes_pairwise
      (windingTarget (boundary := boundary) squarefree family)

/-- The shared boundary request width for the retained winding family is positive. -/
theorem windingRequestWidth_pos
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    0 < windingRequestWidth (boundary := boundary) squarefree family :=
  Curve.Boundary.Complete.Control.boundaryControlledRequestWidth_pos
    boundary family.boxes family.boxes_pairwise
      (windingTarget_pos (boundary := boundary) squarefree family)

/-- Complete sibling-preserving profile family at the winding comparison
width. -/
@[expose] def windingRequestFamily
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    List (Curve.Boundary.Complete.Basic.BoundaryCompleteRequestEntry
      boundary
      (windingRequestWidth (boundary := boundary) squarefree family)) :=
  Curve.Boundary.Complete.Control.controlledBoundaryCompleteRequestFamily
    boundary family.boxes family.boxes_pairwise
      (windingTarget (boundary := boundary) squarefree family)

/-- Fully classified complete children before translating box indices back to
winding states. -/
@[expose] def classifiedWindingRequestFamily
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :=
  Curve.Boundary.Complete.Ownership.classifiedControlledBoundaryFamily
    boundary family.boxes family.boxes_pairwise
      (windingTarget (boundary := boundary) squarefree family)
      (windingTarget_pos (boundary := boundary) squarefree family)

/-- A complete retained boundary child with its box, denominator and actual sample classifications at the common winding
target. -/
abbrev ClassifiedChild
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :=
  Curve.Boundary.Complete.Ownership.ClassifiedControlledBoundaryChild
    boundary family.boxes family.boxes_pairwise
      (windingTarget (boundary := boundary) squarefree family)
      (windingTarget_pos (boundary := boundary) squarefree family)
end Boundary

end Purelib.RootIsolation.Curve.Boundary.Winding.Budget

end
