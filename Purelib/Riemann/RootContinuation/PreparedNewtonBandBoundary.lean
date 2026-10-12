module

import Purelib.Data.List.Membership

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
public import Purelib.Riemann.RootContinuation.PreparedNewtonBandSides
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Executable complete Newton-band boundary traversals

Four actual side preparations pass their terminal root owners onward. Their
cached refinements and integral models are concatenated in counterclockwise
order. The estimate pays all four side sums, independently of the mesh sizes.
A traversal closes in base coordinates; it does not assert that monodromy
around the enclosed branch point fixes the starting root occurrence.
-/

namespace Purelib.Riemann.RootContinuation.PreparedNewtonBandBoundary

open Purelib.RootIsolation.Newton.Band
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (Owner)
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSides (RefinedBoundarySide)
open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
private abbrev Coordinate := Fraction.Rational
/-- The original rational Gaussian box carrier. -/
private abbrev Box := Purelib.Geometry.Rational.Box
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational}

namespace PreparedBandRequest

variable (request : PreparedBandRequest fixed target)

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
/-- The original cleared bottom band side, oriented from lower left to lower right. -/
@[expose] def bottomSegment : Geometry.ClearPath.ClearSegment curve.polynomial request.sample.output.box
    request.sample.output.box.anchor (Components.Basic.point request.sample.output.box.xUpper
      request.sample.output.box.yLower) :=
  .horizontal _ _ _ le_rfl request.sample.output.box.x_valid request.sample.output.box.x_valid le_rfl
    (request.sample.output.bottomLineClearance.restrict (Geometry.Rational.Box.Refinement.StrictInterior.refines
      request.sample.output.strictCurrent))

/-- The original cleared right band side, oriented from lower right to upper right. -/
@[expose] def rightSegment : Geometry.ClearPath.ClearSegment curve.polynomial request.sample.output.box
    (Components.Basic.point request.sample.output.box.xUpper request.sample.output.box.yLower)
    (Components.Basic.point request.sample.output.box.xUpper request.sample.output.box.yUpper) :=
  .vertical _ _ _ le_rfl request.sample.output.box.y_valid request.sample.output.box.y_valid le_rfl
    (request.sample.output.rightLineClearance.restrict (Geometry.Rational.Box.Refinement.StrictInterior.refines
      request.sample.output.strictCurrent))

/-- The original cleared top band side, oriented from upper right to upper left. -/
@[expose] def topSegment : Geometry.ClearPath.ClearSegment curve.polynomial request.sample.output.box
    (Components.Basic.point request.sample.output.box.xUpper request.sample.output.box.yUpper)
    (Components.Basic.point request.sample.output.box.xLower request.sample.output.box.yUpper) :=
  .horizontal _ _ _ request.sample.output.box.x_valid le_rfl le_rfl request.sample.output.box.x_valid
    (request.sample.output.topLineClearance.restrict (Geometry.Rational.Box.Refinement.StrictInterior.refines
      request.sample.output.strictCurrent))

/-- The original cleared left band side, oriented from upper left to lower left. -/
@[expose] def leftSegment : Geometry.ClearPath.ClearSegment curve.polynomial request.sample.output.box
    (Components.Basic.point request.sample.output.box.xLower request.sample.output.box.yUpper)
      request.sample.output.box.anchor :=
  .vertical _ _ _ request.sample.output.box.y_valid le_rfl le_rfl request.sample.output.box.y_valid
    (request.sample.output.leftLineClearance.restrict (Geometry.Rational.Box.Refinement.StrictInterior.refines
      request.sample.output.strictCurrent))

end

section
open Purelib.Riemann.RootContinuation
/-- The original retained bottom segment lies in its band box. -/
theorem bottom_within : (PreparedNewtonBandBoundary.PreparedBandRequest.bottomSegment request).WithinAmbient := ⟨le_rfl,
  request.sample.output.box.y_valid⟩
/-- The original retained right segment lies in its band box. -/
theorem right_within : (PreparedNewtonBandBoundary.PreparedBandRequest.rightSegment request).WithinAmbient :=
  ⟨request.sample.output.box.x_valid, le_rfl⟩
/-- The original retained top segment lies in its band box. -/
theorem top_within : (PreparedNewtonBandBoundary.PreparedBandRequest.topSegment request).WithinAmbient :=
  ⟨request.sample.output.box.y_valid, le_rfl⟩
/-- The original retained left segment lies in its band box. -/
theorem left_within : (PreparedNewtonBandBoundary.PreparedBandRequest.leftSegment request).WithinAmbient := ⟨le_rfl,
  request.sample.output.box.x_valid⟩

end

section
open Purelib.Data.Gaussian
/-- The original bottom endpoints share the retained lower imaginary boundary. -/
theorem bottom_side : SameSide request.sample.output.box request.sample.output.box.anchor
    (Components.Basic.point request.sample.output.box.xUpper request.sample.output.box.yLower) := Or.inr (Or.inr (Or.inl
      ⟨rfl, rfl⟩))
/-- The original right endpoints share the retained upper real boundary. -/
theorem right_side : SameSide request.sample.output.box
    (Components.Basic.point request.sample.output.box.xUpper request.sample.output.box.yLower)
    (Components.Basic.point request.sample.output.box.xUpper request.sample.output.box.yUpper) := Or.inr (Or.inl ⟨rfl,
      rfl⟩)
/-- The original top endpoints share the retained upper imaginary boundary. -/
theorem top_side : SameSide request.sample.output.box
    (Components.Basic.point request.sample.output.box.xUpper request.sample.output.box.yUpper)
    (Components.Basic.point request.sample.output.box.xLower request.sample.output.box.yUpper) := Or.inr (Or.inr (Or.inr
      ⟨rfl, rfl⟩))
/-- The original left endpoints share the retained lower real boundary. -/
theorem left_side : SameSide request.sample.output.box
    (Components.Basic.point request.sample.output.box.xLower request.sample.output.box.yUpper)
      request.sample.output.box.anchor := Or.inl ⟨rfl, rfl⟩

end

open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Riemann.RootContinuation in
open Purelib.Riemann.Topology in
/-- Choose the original independent root owner at the retained band anchor on the requested sheet. -/
@[expose] def boundaryOwner (sheet : Fin 2) : Observation.UniformPreparedMesh.Owner (curve.polynomial.eval
  request.sample.output.box.anchor) :=
  SquareRootContinuationChain.Owner.independent
    (PreparedNewtonBandBoundary.PreparedBandRequest.bottomSegment request).start_eval_ne_zero sheet

end PreparedBandRequest

set_option genInjectivity false in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.RootContinuation in
/-- Four original prepared band sides with exact successive terminal-owner dependence and a cached concatenated model.

The traversal keeps the original starting owner and nominal sheet index. Each subsequent side consumes the preceding
side's exact retained finish owner. -/
structure PreparedBoundaryTraversal (request : PreparedBandRequest fixed target)
    (owner : Observation.UniformPreparedMesh.Owner (curve.polynomial.eval request.sample.output.box.anchor)) (sheet :
      Fin 2) where
  /-- The original prepared bottom side starting at the supplied owner. -/ bottom : RefinedBoundarySide request
    (PreparedNewtonBandBoundary.PreparedBandRequest.bottomSegment request)
    (PreparedNewtonBandBoundary.PreparedBandRequest.bottom_within request) owner sheet
  /-- The original prepared right side starting at the exact bottom finish owner. -/ right : RefinedBoundarySide request
    (PreparedNewtonBandBoundary.PreparedBandRequest.rightSegment request)
    (PreparedNewtonBandBoundary.PreparedBandRequest.right_within request) bottom.finishOwner sheet
  /-- The original prepared top side starting at the exact right finish owner. -/ top : RefinedBoundarySide request
    (PreparedNewtonBandBoundary.PreparedBandRequest.topSegment request)
    (PreparedNewtonBandBoundary.PreparedBandRequest.top_within request) right.finishOwner sheet
  /-- The original prepared left side starting at the exact top finish owner. -/ left : RefinedBoundarySide request
    (PreparedNewtonBandBoundary.PreparedBandRequest.leftSegment request)
    (PreparedNewtonBandBoundary.PreparedBandRequest.left_within request) top.finishOwner sheet
  /-- The cached exact concatenation of the four original side models. -/ model : Basic.PathModel
  /-- The cache equals the original bottom/right/top/left model concatenation. -/ model_eq : model = bottom.model.concat
    (right.model.concat (top.model.concat left.model))

constructive_injectivity PreparedBoundaryTraversal

namespace PreparedBoundaryTraversal

open Purelib.Data.List

variable {request : PreparedBandRequest fixed target}
  {owner : Owner (curve.polynomial.eval
    request.sample.output.box.anchor)} {sheet : Fin 2}

open Purelib.Riemann.RootContinuation in
/-- Retain the original four connected prepared sides and their exact concatenated path model. -/
@[expose] def ofSides (bottom : RefinedBoundarySide request
  (PreparedNewtonBandBoundary.PreparedBandRequest.bottomSegment request)
  (PreparedNewtonBandBoundary.PreparedBandRequest.bottom_within request) owner sheet)
    (right : RefinedBoundarySide request (PreparedNewtonBandBoundary.PreparedBandRequest.rightSegment request)
      (PreparedNewtonBandBoundary.PreparedBandRequest.right_within request) bottom.finishOwner sheet)
    (top : RefinedBoundarySide request (PreparedNewtonBandBoundary.PreparedBandRequest.topSegment request)
      (PreparedNewtonBandBoundary.PreparedBandRequest.top_within request) right.finishOwner sheet)
    (left : RefinedBoundarySide request (PreparedNewtonBandBoundary.PreparedBandRequest.leftSegment request)
      (PreparedNewtonBandBoundary.PreparedBandRequest.left_within request) top.finishOwner sheet) :
    PreparedBoundaryTraversal request owner sheet where
  bottom := bottom
  right := right
  top := top
  left := left
  model := bottom.model.concat (right.model.concat (top.model.concat left.model))
  model_eq := rfl

open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Riemann.RootContinuation in
/-- Prepare the original band boundary in bottom, right, top and left order.

Each original side passes its exact cached finish owner to the next, and the retained traversal consumes those same
prepared side models. -/
@[expose] def build (request : PreparedBandRequest fixed target)
    (owner : Observation.UniformPreparedMesh.Owner (curve.polynomial.eval request.sample.output.box.anchor)) (sheet :
      Fin 2) :
    PreparedBoundaryTraversal request owner sheet :=
  let bottom := RefinedBoundarySide.build request (PreparedNewtonBandBoundary.PreparedBandRequest.bottomSegment request)
    (PreparedNewtonBandBoundary.PreparedBandRequest.bottom_within request)
    (PreparedNewtonBandBoundary.PreparedBandRequest.bottom_side request) owner sheet
  let right := RefinedBoundarySide.build request (PreparedNewtonBandBoundary.PreparedBandRequest.rightSegment request)
    (PreparedNewtonBandBoundary.PreparedBandRequest.right_within request)
    (PreparedNewtonBandBoundary.PreparedBandRequest.right_side request) bottom.finishOwner sheet
  let top := RefinedBoundarySide.build request (PreparedNewtonBandBoundary.PreparedBandRequest.topSegment request)
    (PreparedNewtonBandBoundary.PreparedBandRequest.top_within request)
    (PreparedNewtonBandBoundary.PreparedBandRequest.top_side request) right.finishOwner sheet
  let left := RefinedBoundarySide.build request (PreparedNewtonBandBoundary.PreparedBandRequest.leftSegment request)
    (PreparedNewtonBandBoundary.PreparedBandRequest.left_within request)
    (PreparedNewtonBandBoundary.PreparedBandRequest.left_side request) top.finishOwner sheet
  ofSides bottom right top left

open Purelib.Curves.Hyperelliptic.Integration in
/-- The exact original terminal owner after the retained four-side traversal. -/
@[expose] def finishOwner (boundary : PreparedBoundaryTraversal request owner sheet) :
    Observation.UniformPreparedMesh.Owner (curve.polynomial.eval request.sample.output.box.anchor) :=
      boundary.left.finishOwner

open Purelib.Geometry.Path.Gaussian in
/-- Concatenate the four original retained algebraic side lifts around the band boundary. -/
@[expose] def lifted (boundary : PreparedBoundaryTraversal request owner sheet) :
    Lifted.Basic.LiftedPath 2 { coordinate := request.sample.output.box.anchor, sheet := sheet }
      { coordinate := request.sample.output.box.anchor, sheet := sheet } :=
  boundary.bottom.lifted.append (boundary.right.lifted.append (boundary.top.lifted.append boundary.left.lifted))

open Purelib.Curves.Hyperelliptic.Integration in
/-- Concatenate the original uniform side certificates for the exact retained boundary model and lift. -/
@[expose] def certificates (boundary : PreparedBoundaryTraversal request owner sheet) :
    Algebraic.Path.Basis.UniformPathCertificates curve differential boundary.model.cells boundary.lifted := by
  rw [boundary.model_eq]
  exact Algebraic.Path.Basis.UniformPathCertificates.append boundary.bottom.lifted boundary.bottom.certificates
    (Algebraic.Path.Basis.UniformPathCertificates.append boundary.right.lifted boundary.right.certificates
      (Algebraic.Path.Basis.UniformPathCertificates.append boundary.top.lifted boundary.top.certificates
        boundary.left.certificates))

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The retained boundary-model integral equals the exact ordered sum of the four original side integrals. -/
theorem integralSample_eq (boundary : PreparedBoundaryTraversal request owner sheet) :
    boundary.model.integralSample = Data.Gaussian.Norm.Sum.Basic.gaussianSum [boundary.bottom.model.integralSample,
      boundary.right.model.integralSample,
      boundary.top.model.integralSample, boundary.left.model.integralSample] := by
  rw [boundary.model_eq]
  rw [Basic.PathModel.integralSample_concat, Basic.PathModel.integralSample_concat,
    Basic.PathModel.integralSample_concat]
  change _ = _ + (_ + (_ + (_ + 0)))
  rw [Basic.add_zero]

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The retained four-side boundary integral has squared norm at most sixteen times the original side target. -/
theorem bound (boundary : PreparedBoundaryTraversal request owner sheet) :
    normSq boundary.model.integralSample ≤ 16 * target := by
  rw [boundary.integralSample_eq]
  rw [← Norm.Basic.normSq_eq_canonical]
  have bounded := Norm.Sum.Bounds.normSq_sum_le
    [boundary.bottom.model.integralSample, boundary.right.model.integralSample,
      boundary.top.model.integralSample, boundary.left.model.integralSample] target (by
        intro value member
        rcases Membership.mem_cons.mp member with rfl | member
        · rw [Norm.Basic.normSq_eq_canonical]
          exact boundary.bottom.bound
        rcases Membership.mem_cons.mp member with rfl | member
        · rw [Norm.Basic.normSq_eq_canonical]
          exact boundary.right.bound
        rcases Membership.mem_cons.mp member with rfl | member
        · rw [Norm.Basic.normSq_eq_canonical]
          exact boundary.top.bound
        have same := Membership.mem_singleton.mp member
        subst value
        rw [Norm.Basic.normSq_eq_canonical]
        exact boundary.left.bound)
  apply bounded.trans_eq
  change (4 : Fraction.Rational) * (4 * target) = 16 * target
  ring1

end PreparedBoundaryTraversal

set_option genInjectivity false in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Rat in
/-- A retained prepared boundary with a side target of one sixteenth the original target and exact final payment.

The stored request, anchor owner and traversal share their original dependent identities, and the payment bounds the
actual retained integral. -/
structure RequestedPreparedBoundary (fixed : DifferentialProfile profile differential.exponent)
    (target : Fraction.Rational) (sheet : Fin 2) where
  /-- The original retained band request with target divided by sixteen. -/ request : PreparedBandRequest fixed (target
    / 16)
  /-- The original anchor root owner retained for the boundary traversal. -/ owner :
    Observation.UniformPreparedMesh.Owner (curve.polynomial.eval request.sample.output.box.anchor)
  /-- The exact original four-side traversal from the retained anchor owner. -/ traversal : PreparedBoundaryTraversal
    request owner sheet
  /-- The actual retained boundary integral satisfies the original target. -/ paid : normSq
    traversal.model.integralSample ≤ target

constructive_injectivity RequestedPreparedBoundary

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- Acquire an original prepared band boundary paying the positive requested integral target.

The side request uses one sixteenth of that target, then its original anchor owner and exact four-side traversal supply
the retained total payment. -/
@[expose] def DifferentialProfile.requestBoundary (fixed : DifferentialProfile profile differential.exponent)
    {degreeBound : Nat} (degreeAtLeastTwo : 2 ≤ curve.polynomial.natDegree)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate curve.polynomial degreeBound)
      {target : Fraction.Rational}
    (positive : 0 < target) (sheet : Fin 2) : RequestedPreparedBoundary fixed target sheet := by
  let request := PreparedNewtonBandSamples.DifferentialProfile.requestPrepared
    fixed degreeAtLeastTwo elimination
    (Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 16))
  let owner := PreparedNewtonBandBoundary.PreparedBandRequest.boundaryOwner request sheet
  let traversal := PreparedBoundaryTraversal.build request owner sheet
  have paid : normSq traversal.model.integralSample ≤ target := traversal.bound.trans_eq (by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne target 16 (by decide))
  exact ⟨request, owner, traversal, paid⟩

end Purelib.Riemann.RootContinuation.PreparedNewtonBandBoundary
