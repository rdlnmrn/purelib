module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Normalization.RegularFaceInverseModels
public import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison
import Purelib.Riemann.Normalization.ContinuedInverseRootNegation
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.Normalization.AlignedInverseRootSeed
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Riemann.Integration.ContinuedPrimitiveOverlap

public section

/-!
# Opposite signs of actual transported face models

The auxiliary neighborhoods in this proof reuse the two retained aligned
seeds. They are erased proof data. All polynomial values in the conclusion
belong to the existing transported cells, at independent refinement indices.
-/

namespace Purelib.Integration.Algebraic.Primitive.TransportedPrimitiveNegation
open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Paths
open Purelib.Riemann.Readings

open Purelib.Riemann.Normalization.InverseRootPolynomial

/-- Opposite named root owners make the sum of the transported-cell and neighborhood samples no larger than their
difference.

The squared-norm comparison retains the original cell, point certificate, containment evidence and separate refinement
indices. -/
theorem opposite_point_nearest {polynomial : InverseRootPolynomial.Polynomial} {box inner : InverseRootPolynomial.Box}
    {clearance : RegularFaceInverseModels.Clearance polynomial box} {bounds : RegularFaceInverseModels.Bounds clearance}
    {source : OwnerSeededInverseRoot.Owner (polynomial.eval box.anchor)} (cell :
      TransportedFaceInverseModels.TransportedCell bounds source inner)
    {count : Nat} {patch : ContinuedInverseRoot.ContinuedNeighborhood polynomial count}
    (sample : ContinuedInverseRoot.ContinuedNeighborhood.Point patch inner.anchor) (inside : patch.box.Contains
      inner.anchor)
    (roots : Equivalence.NamedEquivalent (Name.Basic.Named.neg (OwnerTraceReadings.ownerName cell.aligned.seed.owner))
      sample.certificate.value.name) (leftIndex rightIndex : Nat) :
    Data.Gaussian.Norm.Basic.normSq ((cell.model.refine leftIndex).value.eval inner.anchor +
      (patch.base.refine rightIndex).value.eval inner.anchor) ≤
    Data.Gaussian.Norm.Basic.normSq ((cell.model.refine leftIndex).value.eval inner.anchor -
      (patch.base.refine rightIndex).value.eval inner.anchor) := by
  let site := PreparedObservationNeighborhoods.ObservationNeighborhood.ofPoint polynomial 0 inner.anchor
    cell.traced.finishOwner.parameterNonzero
  let auxiliary := ContinuedInverseRoot.ContinuedNeighborhood.ofAligned site cell.aligned
  let first : ContinuedInverseRoot.ContinuedNeighborhood.Point auxiliary inner.anchor :=
    ContinuedInverseRoot.ContinuedNeighborhood.Point.ofOwner cell.aligned.seed.owner (Box.refines_refl
      _)
  have equal : cell.model.value.eval inner.anchor = auxiliary.base.model.value.eval inner.anchor := by
    rw [cell.value_eq, auxiliary.base.model_value_eq]
    rfl
  rw [InverseRootPolynomial.Model.refine_eval_eq cell.model auxiliary.base.model inner.anchor equal leftIndex]
  have scalar := ContinuedInverseRootNegation.ContinuedNeighborhood.Point.negative_nearest
    first sample auxiliary.center_inside inside roots leftIndex rightIndex
  simpa only [Norm.Basic.normSq_eq_canonical, OwnerSeededInverseRoot.SeededNeighborhood.refine] using scalar

/-- At equal original anchors, opposite transported-cell owners satisfy the corresponding sum-versus-difference norm
comparison.

The two cells and refinement indices remain distinct; anchor transport changes only the point index used to compare
their retained root names. -/
theorem opposite_anchor_nearest {polynomial : InverseRootPolynomial.Polynomial} {leftBox rightBox leftInner rightInner :
  InverseRootPolynomial.Box}
    {leftClearance : RegularFaceInverseModels.Clearance polynomial leftBox} {rightClearance :
      RegularFaceInverseModels.Clearance polynomial rightBox}
    {leftBounds : RegularFaceInverseModels.Bounds leftClearance} {rightBounds : RegularFaceInverseModels.Bounds
      rightClearance}
    {leftSource : OwnerSeededInverseRoot.Owner (polynomial.eval leftBox.anchor)} {rightSource :
      OwnerSeededInverseRoot.Owner (polynomial.eval rightBox.anchor)}
    (first : TransportedFaceInverseModels.TransportedCell leftBounds leftSource leftInner)
    (second : TransportedFaceInverseModels.TransportedCell rightBounds rightSource rightInner)
    (anchor : leftInner.anchor = rightInner.anchor)
    (roots : Equivalence.NamedEquivalent (Name.Basic.Named.neg (OwnerTraceReadings.ownerName first.aligned.seed.owner))
      (OwnerTraceReadings.ownerName second.aligned.seed.owner)) (leftIndex rightIndex : Nat) :
    Data.Gaussian.Norm.Basic.normSq ((first.model.refine leftIndex).value.eval leftInner.anchor +
      (second.model.refine rightIndex).value.eval leftInner.anchor) ≤
    Data.Gaussian.Norm.Basic.normSq ((first.model.refine leftIndex).value.eval leftInner.anchor -
      (second.model.refine rightIndex).value.eval leftInner.anchor) := by
  let leftSite := PreparedObservationNeighborhoods.ObservationNeighborhood.ofPoint polynomial 0 leftInner.anchor
    first.traced.finishOwner.parameterNonzero
  let rightSite := PreparedObservationNeighborhoods.ObservationNeighborhood.ofPoint polynomial 0 rightInner.anchor
    second.traced.finishOwner.parameterNonzero
  let left := ContinuedInverseRoot.ContinuedNeighborhood.ofAligned leftSite first.aligned
  let right := ContinuedInverseRoot.ContinuedNeighborhood.ofAligned rightSite second.aligned
  let firstPoint : ContinuedInverseRoot.ContinuedNeighborhood.Point left leftInner.anchor :=
    ContinuedInverseRoot.ContinuedNeighborhood.Point.ofOwner first.aligned.seed.owner (Box.refines_refl
      _)
  let secondPoint : ContinuedInverseRoot.ContinuedNeighborhood.Point right rightInner.anchor :=
    ContinuedInverseRoot.ContinuedNeighborhood.Point.ofOwner second.aligned.seed.owner (Box.refines_refl
      _)
  have leftEq : first.model.value.eval leftInner.anchor = left.base.model.value.eval leftInner.anchor := by
    rw [first.value_eq, left.base.model_value_eq]
    rfl
  have rightEq : second.model.value.eval leftInner.anchor = right.base.model.value.eval leftInner.anchor := by
    rw [second.value_eq, right.base.model_value_eq]
    rfl
  rw [InverseRootPolynomial.Model.refine_eval_eq first.model left.base.model _ leftEq leftIndex,
    InverseRootPolynomial.Model.refine_eval_eq second.model right.base.model _ rightEq rightIndex]
  have scalar := ContinuedInverseRootNegation.ContinuedNeighborhood.Point.negative_nearest
    firstPoint (ContinuedInverseRoot.ContinuedNeighborhood.Point.castPoint anchor secondPoint) left.center_inside
    (anchor.symm ▸ right.center_inside) (by
      rw [ContinuedInverseRoot.ContinuedNeighborhood.Point.castPoint_name]
      exact roots) leftIndex rightIndex
  simpa only [Norm.Basic.normSq_eq_canonical, OwnerSeededInverseRoot.SeededNeighborhood.refine] using scalar

end Purelib.Integration.Algebraic.Primitive.TransportedPrimitiveNegation
