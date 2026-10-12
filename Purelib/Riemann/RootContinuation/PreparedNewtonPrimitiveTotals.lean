module
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Paths.PathArea
import Purelib.RootIsolation.State.Raw
import Purelib.Topology.Polygon.Stokes

import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives
public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedRootBank
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Integration.PreparedPairedModelAccuracy
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedModelAccuracy
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Whole-side primitive errors refer to the retained root-certified child lists. -/
namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.NewtonBandBounds.PairedParentPrimitives

open Purelib
open Purelib.Data.Rat
open Purelib.RootIsolation.Newton.Band
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank (PairedBoundaryParents)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.NewtonBandBounds (PairedParentPrimitives)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
variable {genus count index : Nat} {curve : HyperellipticCurve genus} {differential
  other : Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational} {request : PreparedBandRequest fixed target}

open Purelib.Data.Gaussian in
/-- Read the stored first primitive increments in original parent order. -/
@[expose] def firstReadings : {parents : List (CenteredEdge curve differential)} →
    {bank : PairedBoundaryParents request other parents} → PairedParentPrimitives count bank →
      List Basic.Canonical
  | _, _, .nil => []
  | _, _, .cons first _ rest => first.2.2.increment :: rest.firstReadings

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Read first-row differences between the original stored primitive and numerical increments. -/
@[expose] def firstErrors : {parents : List (CenteredEdge curve differential)} →
    {bank : PairedBoundaryParents request other parents} → PairedParentPrimitives count bank →
      List Basic.Canonical
  | _, _, .nil => []
  | _, .cons head _, .cons first _ rest =>
      (first.2.2.increment -
        (Basic.PathModel.mk (head.refinement.first.block.children.map CenteredEdge.model)).integralSample) ::
          rest.firstErrors

open Purelib.Data.Rat in
/-- Take the maximum retained first-row bound, with zero for an empty bank. -/
@[expose] def firstBound : {parents : List (CenteredEdge curve differential)} →
    {bank : PairedBoundaryParents request other parents} → PairedParentPrimitives count bank → Fraction.Rational
  | _, _, .nil => 0
  | _, _, .cons first _ rest => max first.2.2.bound rest.firstBound

/-- The original first-error list has exactly one entry per retained parent. -/
theorem firstErrors_length {parents : List (CenteredEdge curve differential)}
    {bank : PairedBoundaryParents request other parents} (values : PairedParentPrimitives count bank) :
    values.firstErrors.length = parents.length := by
  induction values with
  | nil => rfl
  | cons first second rest ih => exact congrArg Nat.succ ih

open Purelib.Data.Gaussian in
/-- Every original first-row error satisfies the retained maximum bound. -/
theorem firstErrors_bounded {parents : List (CenteredEdge curve differential)}
    {bank : PairedBoundaryParents request other parents} (values : PairedParentPrimitives count bank) :
    ∀ error ∈ values.firstErrors, Data.Gaussian.Norm.Basic.normSq error ≤ values.firstBound := by
  induction values with
  | nil => intro error member; cases member
  | cons first second rest ih =>
    intro error member
    rcases Data.List.Membership.mem_cons.mp member with rfl | member
    · exact first.2.2.bounded.trans (Fraction.Order.Basic.le_max_left _ _)
    · exact (ih error member).trans (Fraction.Order.Basic.le_max_right _ _)

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Paths in
open Purelib.Riemann.RootContinuation in
/-- The original first-error sum is the primitive reading sum minus the exact first child-sample sum. -/
theorem firstErrors_sum {parents : List (CenteredEdge curve differential)}
    {bank : PairedBoundaryParents request other parents} (values : PairedParentPrimitives count bank) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum values.firstErrors = Data.Gaussian.Norm.Sum.Basic.gaussianSum
      values.firstReadings -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((PreparedNewtonPairedRootBank.PairedBoundaryParents.firstChildren
        bank).map (fun
        child => child.model.integralSample)) := by
  induction values with
  | nil => change (0 : Basic.Canonical) = 0 - 0; ring1
  | @cons parent parents head tail index first second rest ih =>
    simp only [firstErrors, firstReadings, PreparedNewtonPairedRootBank.PairedBoundaryParents.firstChildren,
      Data.List.Map.map_append, IncrementArea.sum_append, Data.Gaussian.Norm.Sum.Basic.gaussianSum, -eq_self, -iff_self]
    rw [ih]
    have sample := PathArea.increments_sum
      (Basic.PathModel.mk (head.refinement.first.block.children.map CenteredEdge.model))
    simp only [PathArea.increments, Data.List.Map.map_map, Function.comp_def, -eq_self, -iff_self] at sample
    rw [sample]
    ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Bound the original first total discrepancy by parent count squared times its retained maximum error. -/
theorem first_total_error_le {parents : List (CenteredEdge curve differential)}
    {bank : PairedBoundaryParents request other parents} (values : PairedParentPrimitives count bank) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum values.firstReadings -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((PreparedNewtonPairedRootBank.PairedBoundaryParents.firstChildren
        bank).map (fun
        child => child.model.integralSample))) ≤
        (parents.length : Fraction.Rational) * ((parents.length : Fraction.Rational) * values.firstBound) := by
  rw [← values.firstErrors_sum]
  have bounded := Norm.Sum.Bounds.normSq_sum_le values.firstErrors values.firstBound values.firstErrors_bounded
  rwa [values.firstErrors_length] at bounded

open Purelib.Data.Gaussian in
/-- Read the stored second primitive increments in original parent order. -/
@[expose] def secondReadings : {parents : List (CenteredEdge curve differential)} →
    {bank : PairedBoundaryParents request other parents} → PairedParentPrimitives count bank →
      List Basic.Canonical
  | _, _, .nil => []
  | _, _, .cons _ second rest => second.2.2.increment :: rest.secondReadings

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Read second-row differences between the original stored primitive and numerical increments. -/
@[expose] def secondErrors : {parents : List (CenteredEdge curve differential)} →
    {bank : PairedBoundaryParents request other parents} → PairedParentPrimitives count bank →
      List Basic.Canonical
  | _, _, .nil => []
  | _, .cons head _, .cons _ second rest =>
      (second.2.2.increment -
        (Basic.PathModel.mk (head.refinement.second.block.children.map CenteredEdge.model)).integralSample) ::
          rest.secondErrors

open Purelib.Data.Rat in
/-- Take the maximum retained second-row bound, with zero for an empty bank. -/
@[expose] def secondBound : {parents : List (CenteredEdge curve differential)} →
    {bank : PairedBoundaryParents request other parents} → PairedParentPrimitives count bank → Fraction.Rational
  | _, _, .nil => 0
  | _, _, .cons _ second rest => max second.2.2.bound rest.secondBound

/-- The original second-error list has exactly one entry per retained parent. -/
theorem secondErrors_length {parents : List (CenteredEdge curve differential)}
    {bank : PairedBoundaryParents request other parents} (values : PairedParentPrimitives count bank) :
    values.secondErrors.length = parents.length := by
  induction values with
  | nil => rfl
  | cons first second rest ih => exact congrArg Nat.succ ih

open Purelib.Data.Gaussian in
/-- Every original second-row error satisfies the retained maximum bound. -/
theorem secondErrors_bounded {parents : List (CenteredEdge curve differential)}
    {bank : PairedBoundaryParents request other parents} (values : PairedParentPrimitives count bank) :
    ∀ error ∈ values.secondErrors, Data.Gaussian.Norm.Basic.normSq error ≤ values.secondBound := by
  induction values with
  | nil => intro error member; cases member
  | cons first second rest ih =>
    intro error member
    rcases Data.List.Membership.mem_cons.mp member with rfl | member
    · exact second.2.2.bounded.trans (Fraction.Order.Basic.le_max_left _ _)
    · exact (ih error member).trans (Fraction.Order.Basic.le_max_right _ _)

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Paths in
open Purelib.Riemann.RootContinuation in
/-- The original second-error sum is the primitive reading sum minus the exact second child-sample sum. -/
theorem secondErrors_sum {parents : List (CenteredEdge curve differential)}
    {bank : PairedBoundaryParents request other parents} (values : PairedParentPrimitives count bank) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum values.secondErrors = Data.Gaussian.Norm.Sum.Basic.gaussianSum
      values.secondReadings -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((PreparedNewtonPairedRootBank.PairedBoundaryParents.secondChildren
        bank).map (fun
        child => child.model.integralSample)) := by
  induction values with
  | nil => change (0 : Basic.Canonical) = 0 - 0; ring1
  | @cons parent parents head tail index first second rest ih =>
    simp only [secondErrors, secondReadings, PreparedNewtonPairedRootBank.PairedBoundaryParents.secondChildren,
      Data.List.Map.map_append, IncrementArea.sum_append, Data.Gaussian.Norm.Sum.Basic.gaussianSum, -eq_self, -iff_self]
    rw [ih]
    have sample := PathArea.increments_sum
      (Basic.PathModel.mk (head.refinement.second.block.children.map CenteredEdge.model))
    simp only [PathArea.increments, Data.List.Map.map_map, Function.comp_def, -eq_self, -iff_self] at sample
    rw [sample]
    ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Bound the original second total discrepancy by parent count squared times its retained maximum error. -/
theorem second_total_error_le {parents : List (CenteredEdge curve differential)}
    {bank : PairedBoundaryParents request other parents} (values : PairedParentPrimitives count bank) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum values.secondReadings -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((PreparedNewtonPairedRootBank.PairedBoundaryParents.secondChildren
        bank).map (fun
        child => child.model.integralSample))) ≤
        (parents.length : Fraction.Rational) * ((parents.length : Fraction.Rational) * values.secondBound) := by
  rw [← values.secondErrors_sum]
  have bounded := Norm.Sum.Bounds.normSq_sum_le values.secondErrors values.secondBound values.secondErrors_bounded
  rwa [values.secondErrors_length] at bounded

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Riemann.RootContinuation
open Purelib.Topology.Polygon
/-- The original first primitive reading sum is close to the left coordinate of the retained paired total. -/
theorem first_sample_error_le {parents : List (CenteredEdge curve differential)}
    {bank : PairedBoundaryParents request other parents} (values : PairedParentPrimitives count bank) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum values.firstReadings -
      (PairedIncrementArea.total bank.incrementBlocks.flatten).left) ≤
        (parents.length : Fraction.Rational) * ((parents.length : Fraction.Rational) * values.firstBound) := by
  change Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum values.firstReadings -
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (bank.incrementBlocks.flatten.map Stokes.PrimitivePoint.left)) ≤ _
  rw [PreparedNewtonPairedRootBank.PairedBoundaryParents.increments_left bank]
  exact values.first_total_error_le

/-- The original second primitive reading sum is close to the right coordinate of the retained paired total. -/
theorem second_sample_error_le {parents : List (CenteredEdge curve differential)}
    {bank : PairedBoundaryParents request other parents} (values : PairedParentPrimitives count bank) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum values.secondReadings -
      (PairedIncrementArea.total bank.incrementBlocks.flatten).right) ≤
        (parents.length : Fraction.Rational) * ((parents.length : Fraction.Rational) * values.secondBound) := by
  change Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum values.secondReadings -
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (bank.incrementBlocks.flatten.map Stokes.PrimitivePoint.right)) ≤ _
  rw [PreparedNewtonPairedRootBank.PairedBoundaryParents.increments_right bank]
  exact values.second_total_error_le

end Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.NewtonBandBounds.PairedParentPrimitives
