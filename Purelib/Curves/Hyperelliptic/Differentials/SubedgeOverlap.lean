module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.ContinuedInverseRoot
public import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.ContinuedInverseRootOverlap
public import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
public import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Init.Prelude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot

open Purelib

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.ContinuedInverseRoot

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.Normalization.InverseRootPolynomial

@[expose] public section

/-!
# Polynomial overlap on actual prepared descendants

The retained root-safe subedge map identifies parent and child polynomial
patches, including after nested refinement. Operational sheet agreement is
supplied by that map and the uniform patch construction, not by a new sign
or root-comparison premise. Cached generated polynomials may use independent
refinement indices and need only agree with their specifications at the anchor.
-/

namespace Purelib.Curves.Hyperelliptic.Differentials.SubedgeOverlap

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedge)
open Purelib.Riemann.Normalization.InverseModelOverlap (OverlapSample)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent child : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}

/-- Every query on the actual child has the same polynomial sheet as its retained parent occurrence. Point owners appear
only in the erased proof. -/
theorem polynomial_nearest (relation : PreparedSubedgeRootQueries.RootSubedge parent child)
    (parentPatch : UniformPrimitiveSheetCompatibility.PreparedPatch parent) (childPatch :
      UniformPrimitiveSheetCompatibility.PreparedPatch child)
    (parentCount childCount parentIndex childIndex : Nat)
    (fraction : InverseRootPolynomial.Coordinate) (inside : 0 ≤ fraction ∧ fraction ≤ 1)
    (parentInside : (parentPatch.neighborhood parentCount).box.Contains (child.edge.point fraction))
    (childInside : (childPatch.neighborhood childCount).box.Contains (child.edge.point fraction)) :
    Data.Gaussian.Norm.Basic.normSq (((parentPatch.neighborhood parentCount).base.refine
      parentIndex).value.eval (child.edge.point fraction) -
      ((childPatch.neighborhood childCount).base.refine childIndex).value.eval (child.edge.point fraction)) ≤
    Data.Gaussian.Norm.Basic.normSq (((parentPatch.neighborhood parentCount).base.refine
      parentIndex).value.eval (child.edge.point fraction) +
      ((childPatch.neighborhood childCount).base.refine childIndex).value.eval (child.edge.point fraction)) := by
  let first := ContinuedNeighborhood.Point.acquire (parentPatch.neighborhood parentCount) (child.edge.point fraction)
    parentInside
  let second := ContinuedNeighborhood.Point.acquire (childPatch.neighborhood childCount) (child.edge.point fraction)
    childInside
  let location := relation.location fraction inside
  let firstEquivalent := parentPatch.point_equivalent_at parentCount location.fraction location.inside location.point_eq
    parentInside first
  let secondEquivalent := childPatch.point_equivalent childCount fraction inside childInside second
  simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  exact ContinuedNeighborhood.Point.equivalent_nearest first second parentInside childInside
    (firstEquivalent.symm.trans ((relation.equivalent fraction inside).trans secondEquivalent)) parentIndex childIndex

/-- Only the checked polynomial evaluations survive at runtime. In particular, this does not reacquire either patch or
execute root comparisons. -/
def polynomialOverlap (relation : PreparedSubedgeRootQueries.RootSubedge parent child)
    (parentPatch : UniformPrimitiveSheetCompatibility.PreparedPatch parent) (childPatch :
      UniformPrimitiveSheetCompatibility.PreparedPatch child)
    (parentCount childCount parentIndex childIndex : Nat)
    (fraction : InverseRootPolynomial.Coordinate) (inside : 0 ≤ fraction ∧ fraction ≤ 1)
    (parentInside : (parentPatch.neighborhood parentCount).box.Contains (child.edge.point fraction))
    (childInside : (childPatch.neighborhood childCount).box.Contains (child.edge.point fraction))
    (parentModel : InverseRootPolynomial.Model curve.polynomial (parentPatch.neighborhood parentCount).base.box)
    (childModel : InverseRootPolynomial.Model curve.polynomial (childPatch.neighborhood childCount).base.box)
    (parentEq : parentModel.value.eval (child.edge.point fraction) =
      ((parentPatch.neighborhood parentCount).base.refine parentIndex).value.eval (child.edge.point fraction))
    (childEq : childModel.value.eval (child.edge.point fraction) =
      ((childPatch.neighborhood childCount).base.refine childIndex).value.eval (child.edge.point fraction)) :
    InverseModelOverlap.OverlapSample parentModel childModel (child.edge.point fraction) :=
  let first := parentModel.value.eval (child.edge.point fraction)
  let second := childModel.value.eval (child.edge.point fraction)
  ⟨first, rfl, second, rfl, ⟨false, second, rfl, by
    dsimp only [first, second]
    rw [parentEq, childEq]
    have scalar := Curves.Hyperelliptic.Differentials.SubedgeOverlap.polynomial_nearest relation parentPatch childPatch
      parentCount childCount parentIndex childIndex
      fraction inside parentInside childInside
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using scalar⟩⟩

/-- Root-safe refinement fixes the transition on the full child edge from its start occurrence. The four containments
are geometric, not sheet premises. -/
def polynomialTransition (relation : PreparedSubedgeRootQueries.RootSubedge parent child)
    (parentPatch : UniformPrimitiveSheetCompatibility.PreparedPatch parent) (childPatch :
      UniformPrimitiveSheetCompatibility.PreparedPatch child)
    (parentCount childCount parentIndex childIndex : Nat)
    (parentStart : (parentPatch.neighborhood parentCount).box.Contains (child.edge.point 0))
    (parentFinish : (parentPatch.neighborhood parentCount).box.Contains (child.edge.point 1))
    (childFinish : (childPatch.neighborhood childCount).box.Contains (child.edge.point 1))
    (parentModel : InverseRootPolynomial.Model curve.polynomial (parentPatch.neighborhood parentCount).base.box)
    (childModel : InverseRootPolynomial.Model curve.polynomial (childPatch.neighborhood childCount).base.box)
    (parentEq : parentModel.value.eval (child.edge.point 0) =
      ((parentPatch.neighborhood parentCount).base.refine parentIndex).value.eval (child.edge.point 0))
    (childEq : childModel.value.eval (child.edge.point 0) =
      ((childPatch.neighborhood childCount).base.refine childIndex).value.eval (child.edge.point 0)) :
    InverseModelEdgeTransition.EdgeTransition parentModel childModel (child.edge.point 0) (child.edge.point 1) where
  leftStart := (parentPatch.neighborhood parentCount).box_refines.contains parentStart
  leftFinish := (parentPatch.neighborhood parentCount).box_refines.contains parentFinish
  rightStart := (childPatch.neighborhood childCount).box_refines.contains (childPatch.start_inside childCount)
  rightFinish := (childPatch.neighborhood childCount).box_refines.contains childFinish
  sample := Curves.Hyperelliptic.Differentials.SubedgeOverlap.polynomialOverlap relation parentPatch childPatch
    parentCount childCount parentIndex childIndex
    0 child.edge.baseInside parentStart (childPatch.start_inside childCount) parentModel childModel parentEq childEq

end Purelib.Curves.Hyperelliptic.Differentials.SubedgeOverlap
