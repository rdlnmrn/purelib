module
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic

import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Curves.Hyperelliptic.Differentials.SubedgeOverlap
public import Purelib.Riemann.Integration.ContinuedPrimitiveOverlap
import Purelib.Riemann.Paths.PreparedPrimitivePaths
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveRefinement
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
public import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Topology.Polygon.Stokes
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Sewn contact rates from actual prepared polynomial patches

The root-safe descendant map supplies sheet agreement. Covered parent and
child geometry supplies endpoint containment. The resulting fixed budget
bounds the retained primitive increments at every pair of later indices and
produces the contact-rate certificate consumed by whole-tree refinement.
No exact root, sign choice, Taylor charge, or successful accuracy test is an
additional premise. Global construction of the face-to-patch assignment is
separate from this contact-level bridge.
-/

namespace Purelib.Riemann.Integration.PreparedSubedgePrimitiveContacts

open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier of the original primitive contacts. -/
private abbrev Gaussian := Basic.Canonical
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Polygon.Stokes (OrientedTriangle)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceContact SourceEdge)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveRefinement (ContactRate)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (corner)
open Purelib.Riemann.Integration.ContinuedPrimitiveOverlap (PrimitivePairGeometry PrimitivePairBudget)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedge)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Data.Rat in
/-- The rational coordinate carrier of the retained contact error bounds. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Polynomial.Dense.Gaussian in
/-- The original dense Gaussian numerator polynomial carrier. -/
private abbrev Polynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent child : CenteredEdge curve differential}

open Purelib.Polynomial.Dense.Gaussian in
/-- Original parent and child primitive neighborhoods compared on the child's exact endpoint segment.

The two neighborhood counts and shared numerator remain explicit, with the original pair geometry and quantitative
overlap budget. -/
abbrev PrimitiveOverlap (parentPatch : PreparedPatch parent) (childPatch : PreparedPatch child)
    (parentCount childCount : Nat) (numerator :
      Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :=
  PrimitivePairGeometry (parentPatch.neighborhood parentCount) (childPatch.neighborhood childCount)
    numerator (child.edge.point 0) (child.edge.point 1)

namespace PrimitiveOverlap

variable {parentPatch : PreparedPatch parent} {childPatch : PreparedPatch child}
  {parentCount childCount : Nat} {numerator :
    Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}

open Purelib.Data.Rat in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
/-- Build primitive overlap geometry from an original root-subedge relation and retained endpoint containments.

The child's locations in the original parent parameter interval supply parent-neighborhood containment; the pair budget
retains both exact neighborhoods and numerator. -/
def build (relation : RootSubedge parent child) (parentPatch : PreparedPatch parent) (childPatch : PreparedPatch child)
    (parentCount childCount : Nat) (numerator :
      Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (parentFinish : (parentPatch.neighborhood parentCount).box.Contains (parent.edge.point 1))
    (childFinish : (childPatch.neighborhood childCount).box.Contains (child.edge.point 1)) :
    PrimitiveOverlap parentPatch childPatch parentCount childCount numerator :=
  have contained (fraction : Fraction.Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
      (parentPatch.neighborhood parentCount).box.Contains (child.edge.point fraction) := by
    rw [← (relation.location fraction inside).point_eq]
    exact PreparedPrimitivePaths.point_inside_of_endpoints parent _ (parentPatch.start_inside parentCount)
      parentFinish (relation.location fraction inside).inside
  ⟨contained 0 child.edge.baseInside, contained 1 (by decide), childPatch.start_inside childCount, childFinish,
    PrimitivePairBudget.build (parentPatch.neighborhood parentCount) (childPatch.neighborhood childCount)
      numerator (child.edge.point 0) (child.edge.point 1)⟩

open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Meshes in
/-- Build the original primitive overlap using exact parent/child mesh membership for endpoint containment. -/
def ofMeshes (relation : RootSubedge parent child) (parentPatch : PreparedPatch parent) (childPatch : PreparedPatch
  child)
    (parentCount childCount : Nat) (numerator :
      Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (parentMesh : UniformPrimitiveMesh.Mesh parentPatch.bounds)
    (parentMember : parent.parameterEdge ∈ parentMesh.edges)
    (childMesh : UniformPrimitiveMesh.Mesh childPatch.bounds)
    (childMember : child.parameterEdge ∈ childMesh.edges) :
    PrimitiveOverlap parentPatch childPatch parentCount childCount numerator :=
  build relation parentPatch childPatch parentCount childCount numerator
    (parentPatch.finish_inside_of_mesh parentCount parentMesh parentMember)
    (childPatch.finish_inside_of_mesh childCount childMesh childMember)

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
/-- The original parent and child primitive increments disagree by at most their retained quarter-radius budget.

Both model indices must be above the comparison stage; the exact root-subedge transition identifies the continued roots
on the original child segment. -/
theorem increment_le (overlap : PrimitiveOverlap parentPatch childPatch parentCount childCount numerator)
    (relation : RootSubedge parent child) {parentIndex childIndex : Nat}
    (first : PrimitiveModel (parentPatch.neighborhood parentCount) parentIndex numerator)
    (second : PrimitiveModel (childPatch.neighborhood childCount) childIndex numerator)
    (index : Nat) (parentLater : index ≤ parentIndex) (childLater : index ≤ childIndex) :
    normSq (first.primitive.value.eval (child.edge.point 1) - first.primitive.value.eval (child.edge.point 0) +
      (second.primitive.value.eval (child.edge.point 0) - second.primitive.value.eval (child.edge.point 1))) ≤
      Geometric.Basic.quarterRadius overlap.budget.scale index := by
  let edge := Differentials.SubedgeOverlap.polynomialTransition relation parentPatch childPatch parentCount childCount
    parentIndex childIndex
    overlap.leftStart overlap.leftFinish overlap.rightFinish
    ((parentPatch.neighborhood parentCount).base.refine parentIndex)
    ((childPatch.neighborhood childCount).base.refine childIndex) rfl rfl
  exact overlap.budget.increment_le first second edge rfl index parentLater childLater

open Purelib.Data.Gaussian in
open Purelib.Topology.Surface in
/-- Construct a sewn contact rate from the original parent/child primitive overlap.

The retained source contact fixes opposite edge orientations; exact family readbacks and separate parent/child stage
floors give the same overlap-budget decay at every stage. -/
def contactRate (overlap : PrimitiveOverlap parentPatch childPatch parentCount childCount numerator)
    (relation : RootSubedge parent child)
    {vertexCount faceCount : Nat} {faces : Fin faceCount → OrientedTriangle vertexCount}
    (coordinate : Fin vertexCount → Basic.Canonical) (contact : Sewing.SewnPrimitiveContacts.SourceContact faces)
    (start_eq : coordinate (contact.left.project faces).start = child.edge.point 0)
    (finish_eq : coordinate (contact.left.project faces).finish = child.edge.point 1)
    (parentFloor childFloor : Nat)
    (first : ∀ index, PrimitiveModel (parentPatch.neighborhood parentCount) (index + parentFloor) numerator)
    (second : ∀ index, PrimitiveModel (childPatch.neighborhood childCount) (index + childFloor) numerator)
    (family : Nat → Fin faceCount → Sewing.PrimitiveSewing.PrimitiveValues 3)
    (first_eq : ∀ index position, family index contact.left.source position =
      (first index).primitive.value.eval (coordinate (Sewing.SewnPrimitiveFaces.corner (faces contact.left.source)
        position)))
    (second_eq : ∀ index position, family index contact.right.source position =
      (second index).primitive.value.eval (coordinate (Sewing.SewnPrimitiveFaces.corner (faces contact.right.source)
        position))) :
    Sewing.SewnPrimitiveRefinement.ContactRate faces family where
  contact := contact
  scale := overlap.budget.scale
  nonnegative := overlap.budget.scale_nonnegative
  bounded := by
    intro index
    have rightStart : coordinate (contact.right.project faces).start = child.edge.point 1 :=
      (congrArg (fun edge => coordinate edge.start) contact.opposite).trans finish_eq
    have rightFinish : coordinate (contact.right.project faces).finish = child.edge.point 0 :=
      (congrArg (fun edge => coordinate edge.finish) contact.opposite).trans start_eq
    have firstStart := first_eq index contact.left.first
    have firstFinish := first_eq index contact.left.last
    have secondStart := second_eq index contact.right.first
    have secondFinish := second_eq index contact.right.last
    change _ = (first index).primitive.value.eval (coordinate (contact.left.project faces).start) at firstStart
    change _ = (first index).primitive.value.eval (coordinate (contact.left.project faces).finish) at firstFinish
    change _ = (second index).primitive.value.eval (coordinate (contact.right.project faces).start) at secondStart
    change _ = (second index).primitive.value.eval (coordinate (contact.right.project faces).finish) at secondFinish
    rw [start_eq] at firstStart
    rw [finish_eq] at firstFinish
    rw [rightStart] at secondStart
    rw [rightFinish] at secondFinish
    unfold Sewing.SewnPrimitiveContacts.SourceContact.mismatch Sewing.SewnPrimitiveContacts.SourceEdge.increment
    rw [firstStart, firstFinish, secondStart, secondFinish]
    simpa only [Norm.Basic.normSq_eq_canonical] using
      overlap.increment_le relation (first index) (second index) index (Nat.le_add_right _ _) (Nat.le_add_right _ _)

end PrimitiveOverlap

end Purelib.Riemann.Integration.PreparedSubedgePrimitiveContacts
