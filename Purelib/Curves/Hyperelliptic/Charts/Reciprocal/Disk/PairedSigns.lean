module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment
import Purelib.Riemann.Normalization.InverseModelRootAgreement
import Purelib.Riemann.Normalization.InverseModelEquivalentSigns
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PrimitiveSamples

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.InverseModelOverlap

open Purelib.Riemann.Normalization.InverseModelOverlapCocycle

open Purelib.Riemann.Topology

@[expose] public section

/-!
# Retained root joins align two differential cap signs

The existing join retains a comparison of quotient coordinates. Reconstruct
the supplied reciprocal roots with the same global regular root, then apply
finite model-root sign agreement. No endpoint channel is reacquired.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSigns

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseModelOverlap (SignAlignment)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Point Join)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (mul)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : ParameterEdge} {cell :
    Cell data edge}
  {model : RootModel cell} {parameter :
    Coordinate}
  {otherCount : Nat} {otherDifferential : Differential genus}
  {otherParent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve otherDifferential}
  {otherPatch : PreparedPatch otherParent} {otherData :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {otherEdge : ParameterEdge} {otherCell :
    Cell otherData otherEdge}
  {otherModel : RootModel otherCell}
    {otherParameter : Coordinate}
  {first : Point cap model parameter} {last :
    Point cap otherModel otherParameter}

/-- Reconstruct an operational comparison of the original reciprocal roots from equal physical points and retained
cap-coordinate equivalence. -/
public def paired_roots_of_coordinates {firstPoint lastPoint : InverseRootPolynomial.Gaussian}
    {firstOwner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval firstPoint)}
    {lastOwner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval lastPoint)}
    (first : Coordinates.Overlap cap firstPoint firstOwner)
    (last : Coordinates.Overlap cap lastPoint lastOwner) (same : firstPoint = lastPoint)
    (coordinates : Gaussian.Equivalence.NamedEquivalent first.coordinate.prepared.denominator.name
      last.coordinate.prepared.denominator.name) :
    Gaussian.Equivalence.NamedEquivalent first.reciprocal.value.name last.reciprocal.value.name := by
  cases same
  have regular := InverseModelRootAgreement.equivalent_of_value
    first.regular.channel last.regular.channel rfl
  exact first.coordinate.reconstruct.symm.trans
    ((Congruence.coherentMul_respects first.coordinate.prepared.denominator last.coordinate.prepared.denominator
      first.regular.certificate.value last.regular.certificate.value coordinates regular).trans
        last.coordinate.reconstruct)

/-- Reconstruct the original polynomial root channels from the join's retained coordinate comparison and the shared
regular root. -/
def Join.pairedRootEquivalent (joined : ArcOwners.Join first last) :
    Gaussian.Equivalence.NamedEquivalent first.root.channel.certificate.value.name
      last.root.channel.certificate.value.name := by
  have owned := paired_roots_of_coordinates
    first.coordinates last.coordinates (congrArg Inv.inv joined.point_eq) joined.coordinate
  rw [first.coordinates.reciprocal_eq, last.coordinates.reciprocal_eq] at owned
  exact first.root.channel.owner_equivalent.symm.trans (owned.trans last.root.channel.owner_equivalent)

variable {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell}
  {otherComparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular otherCell}
  {index : Nat} {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {before : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample}
  {otherBox : Purelib.Geometry.Rational.Box} {otherCapSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap otherDifferential index otherBox}
  {after : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample otherComparison otherCapSample}

/-- An actual retained root join forces the two parent cells to select the same regular-cap sheet. The common polynomial
stage is supplied by the existing shared sample, and two preparation stages suffice. -/
theorem Join.paired_same_sign (joined : ArcOwners.Join first last)
    (left : SheetAlignment.RegularAlignment before)
    (right : SheetAlignment.RegularAlignment after) (later : 2 ≤ index) :
    left.first.flip = right.first.flip := by
  have shifted : 2 + (index - 2) = index := by omega0
  have beforeEq : before.retained.inverse = cell.model.refine index := by
    rw [before.retained.inverse_eq, before.cell_eq]
  have afterEq : after.retained.inverse = otherCell.model.refine index := by
    rw [after.retained.inverse_eq, after.cell_eq]
  have nearest := InverseModelEquivalentSigns.equivalent_nearest_at first.root.channel last.root.channel
    (congrArg Inv.inv joined.point_eq)
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSigns.Join.pairedRootEquivalent joined) (index - 2) (index - 2)
  rw [model.refine_eq, otherModel.refine_eq, shifted, ← beforeEq, ← afterEq, joined.point_eq] at nearest
  let firstValue := before.retained.inverse.value.eval (otherParent.edge.point otherParameter)⁻¹
  let lastValue := after.retained.inverse.value.eval (otherParent.edge.point otherParameter)⁻¹
  let shared := capSample.inverse.value.eval (otherParent.edge.point otherParameter)⁻¹
  have firstResidual : Data.Gaussian.Basic.Canonical.normSq (1 - (HyperellipticReciprocal.polynomial curve).eval
    (otherParent.edge.point otherParameter)⁻¹ *
      firstValue ^ 2) ≤ before.retained.inverse.bound := by
    have bounded := before.retained.inverse.residualBound (parent.edge.point parameter)⁻¹
      (cell.contains parameter first.root.between)
    rw [before.retained.inverse.residual_eq, joined.point_eq] at bounded
    exact bounded
  have lastResidual : Data.Gaussian.Basic.Canonical.normSq (1 - (HyperellipticReciprocal.polynomial curve).eval
    (otherParent.edge.point otherParameter)⁻¹ *
      lastValue ^ 2) ≤ after.retained.inverse.bound := by
    rw [← after.retained.inverse.residual_eq]
    exact after.retained.inverse.residualBound _ (otherCell.contains otherParameter last.root.between)
  have sharedResidual : Data.Gaussian.Norm.Basic.normSq (1 - (HyperellipticReciprocal.polynomial curve).eval
    (otherParent.edge.point otherParameter)⁻¹ *
      shared ^ 2) ≤ Geometric.Basic.quarterRadius (1 / 256) index := by
    have same : (HyperellipticReciprocal.polynomial curve).eval (otherParent.edge.point otherParameter)⁻¹ =
        cap.polynomial.eval (otherParent.edge.point otherParameter)⁻¹ := by
      rw [HyperellipticReciprocal.polynomial_eval, right.regular_chart, pow_zero, _root_.mul_one, cap.polynomial_eq]
    rw [same, ← capSample.inverse.residual_eq]
    exact capSample.disk_residual_bound last.coordinates.regular.inside
  have firstSmall : before.retained.inverse.bound ≤ 1 / 256 := by
    have bounded := ((model.model.refine_bound (index - 2)).trans_le
      (Geometric.Basic.quarterRadius_le_scale model.model.bound_nonnegative (index - 2))).trans model.small
    rw [model.refine_eq, shifted, ← beforeEq] at bounded
    exact bounded
  have lastSmall : after.retained.inverse.bound ≤ 1 / 256 := by
    have bounded := ((otherModel.model.refine_bound (index - 2)).trans_le
      (Geometric.Basic.quarterRadius_le_scale otherModel.model.bound_nonnegative (index - 2))).trans otherModel.small
    rw [otherModel.refine_eq, shifted, ← afterEq] at bounded
    exact bounded
  have sharedSmall : Geometric.Basic.quarterRadius (1 / 256) index ≤ (1 / 256 : InverseRootPolynomial.Coordinate) :=
    Geometric.Basic.quarterRadius_le_scale (by decide +kernel) index
  let connecting : InverseModelOverlap.SignAlignment firstValue lastValue := ⟨false, lastValue, rfl, nearest⟩
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at sharedResidual
  have composed := SignAlignment.cocycle connecting (SignAlignment.build lastValue shared) (SignAlignment.build
    firstValue shared)
    firstResidual lastResidual sharedResidual firstSmall lastSmall sharedSmall
  have firstBit := left.same_flip parameter first.root.between
  rw [joined.point_eq] at firstBit
  have lastBit := right.same_flip otherParameter last.root.between
  have sharedInverse : otherCapSample.inverse = capSample.inverse := otherCapSample.inverse_eq.trans
    capSample.inverse_eq.symm
  have bitEq := congrArg (fun inverse : InverseRootPolynomial.Model cap.polynomial collar.box =>
    (SignAlignment.build lastValue (inverse.value.eval (otherParent.edge.point otherParameter)⁻¹)).flip) sharedInverse
  exact firstBit.symm.trans (composed.trans (bitEq.symm.trans lastBit))

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSigns
