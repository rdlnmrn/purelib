module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBudget
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.State.Raw

public import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedTotals
public import Purelib.Riemann.RootContinuation.PreparedNewtonBandBoundary
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data

public section

/-! Four paired sides retain actual endpoint owners and all internal area. -/
namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedBoundary

open Purelib.RootIsolation.Newton.Band
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandBoundary.PreparedBandRequest (bottomSegment rightSegment
  topSegment leftSegment bottom_within right_within top_within left_within bottom_side right_side top_side left_side)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide (PairedBoundarySide)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedBudget (PairedBandSelection)
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Integration.Path.PairedIncrementArea (Summary area total)
open Purelib.Integration.Path.PairedAreaBlocks (blocks_area_bound)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Curves.Hyperelliptic in
open Purelib.Integration.Path in
set_option genInjectivity false in
/-- Four sequential paired sides around a retained Newton band.

Each side starts at the previous side's actual finish owner; the cached summary describes their ordered
bottom/right/top/left increment concatenation. -/
structure PairedBoundaryTraversal (request : PreparedBandRequest fixed target) (other : Differentials.Basic.Differential
  genus)
    (owner : Owner (curve.polynomial.eval request.sample.output.box.anchor)) (sheet : Fin 2) where
  /-- First paired side from the original anchor owner. -/ bottom : PairedBoundarySide request other (bottomSegment
    request) (bottom_within request) owner sheet
  /-- Right side starting at the bottom side's actual finish owner. -/ right : PairedBoundarySide request other
    (rightSegment request) (right_within request) bottom.finishOwner sheet
  /-- Top side starting at the right side's actual finish owner. -/ top : PairedBoundarySide request other (topSegment
    request) (top_within request) right.finishOwner sheet
  /-- Left side starting at the top side's actual finish owner. -/ left : PairedBoundarySide request other (leftSegment
    request) (left_within request) top.finishOwner sheet
  /-- Cached summary of the exact four-side ordered increment list. -/ summary : PairedIncrementArea.Summary
    [bottom.refined.incrementBlocks.flatten, right.refined.incrementBlocks.flatten,
      top.refined.incrementBlocks.flatten, left.refined.incrementBlocks.flatten].flatten

constructive_injectivity PairedBoundaryTraversal

namespace PairedBoundaryTraversal
variable {request : PreparedBandRequest fixed target} {other :
  Differential genus}
  {owner : Owner (curve.polynomial.eval request.sample.output.box.anchor)} {sheet : Fin 2}

open Purelib.Curves.Hyperelliptic in
open Purelib.Integration.Path in
/-- Build the four paired boundary sides and append their cached summaries.

Retains the original request, second differential and sheet while passing each actual finish owner into the next side
construction. -/
@[expose] def build (request : PreparedBandRequest fixed target) (other : Differentials.Basic.Differential genus)
    (owner : Owner (curve.polynomial.eval request.sample.output.box.anchor)) (sheet : Fin 2) :
    PairedBoundaryTraversal request other owner sheet :=
  let bottom := PairedBoundarySide.build request other (bottomSegment request) (bottom_within request) (bottom_side
    request) owner sheet
  let right := PairedBoundarySide.build request other (rightSegment request) (right_within request) (right_side request)
    bottom.finishOwner sheet
  let top := PairedBoundarySide.build request other (topSegment request) (top_within request) (top_side request)
    right.finishOwner sheet
  let left := PairedBoundarySide.build request other (leftSegment request) (left_within request) (left_side request)
    top.finishOwner sheet
  ⟨bottom, right, top, left, PairedAreaBlocks.Summary.append bottom.summary
    (PairedAreaBlocks.Summary.append right.summary
      (PairedAreaBlocks.Summary.append top.summary
        (PairedAreaBlocks.Summary.append left.summary (PairedIncrementArea.Summary.build []))))⟩

/-- Actual root owner after the final left side of the boundary traversal. -/
@[expose] def finishOwner (boundary : PairedBoundaryTraversal request other owner sheet) :
    Owner (curve.polynomial.eval request.sample.output.box.anchor) := boundary.left.finishOwner

end PairedBoundaryTraversal
namespace PairedBandSelection
variable {other : Differential genus} {right : DifferentialProfile
  profile other.exponent} {radius : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- Bound a retained paired traversal area by 2560 times the squared target.

Applies the four original side area and total certificates to the block-area bound, retaining the exact increment order
and summary readback. -/
theorem traversal_area_bound (selection : PairedBandSelection fixed right target radius)
    {owner : Owner (curve.polynomial.eval selection.sample.output.box.anchor)} {sheet : Fin 2}
    (boundary : PairedBoundaryTraversal selection.sourceRequest other owner sheet) :
    normSq boundary.summary.areaValue ≤ 2560 * target^2 := by
  let blocks := [boundary.bottom.refined.incrementBlocks.flatten, boundary.right.refined.incrementBlocks.flatten,
    boundary.top.refined.incrementBlocks.flatten, boundary.left.refined.incrementBlocks.flatten]
  have areas : ∀ block ∈ blocks, normSq (PairedIncrementArea.area block) ≤ 16 * target^2 := by
    intro block member
    dsimp only [blocks] at member
    cases member with
    | head =>
        rw [← boundary.bottom.summary.area_eq]
        simpa only [Norm.Basic.normSq_eq_canonical] using
          selection.side_area_bound boundary.bottom
    | tail _ member =>
        cases member with
        | head =>
            rw [← boundary.right.summary.area_eq]
            simpa only [Norm.Basic.normSq_eq_canonical] using
              selection.side_area_bound boundary.right
        | tail _ member =>
            cases member with
            | head =>
                rw [← boundary.top.summary.area_eq]
                simpa only [Norm.Basic.normSq_eq_canonical] using
                  selection.side_area_bound boundary.top
            | tail _ member =>
                cases member with
                | head =>
                    rw [← boundary.left.summary.area_eq]
                    simpa only [Norm.Basic.normSq_eq_canonical] using
                      selection.side_area_bound boundary.left
                | tail _ member =>
                    cases member
  have totals : ∀ block ∈ blocks, Bounded (PairedIncrementArea.total block) target := by
    intro block member
    dsimp only [blocks] at member
    cases member with
    | head =>
        rw [← boundary.bottom.summary.total_eq]
        simpa only [Norm.Basic.normSq_eq_canonical] using
          selection.side_total_bound boundary.bottom
    | tail _ member =>
        cases member with
        | head =>
            rw [← boundary.right.summary.total_eq]
            simpa only [Norm.Basic.normSq_eq_canonical] using
              selection.side_total_bound boundary.right
        | tail _ member =>
            cases member with
            | head =>
                rw [← boundary.top.summary.total_eq]
                simpa only [Norm.Basic.normSq_eq_canonical] using
                  selection.side_total_bound boundary.top
            | tail _ member =>
                cases member with
                | head =>
                    rw [← boundary.left.summary.total_eq]
                    simpa only [Norm.Basic.normSq_eq_canonical] using
                      selection.side_total_bound boundary.left
                | tail _ member =>
                    cases member
  have nonnegative : 0 ≤ target := (Basic.Canonical.normSq_nonneg boundary.bottom.summary.totalValue.left).trans
    (selection.side_total_bound boundary.bottom).1
  have areasOld : ∀ block ∈ blocks,
      Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area block) ≤
        16 * target^2 := by
    intro block member
    simpa only [Norm.Basic.normSq_eq_canonical] using areas block member
  have estimate := PairedAreaBlocks.blocks_area_bound blocks nonnegative areasOld totals
  have converted : normSq (PairedIncrementArea.area blocks.flatten) ≤
      2 * ((blocks.length : Fraction.Rational)^2 * (16 * target^2) +
        4 * ((blocks.length : Fraction.Rational)^2 * target)^2) := by
    simpa only [Norm.Basic.normSq_eq_canonical] using estimate
  rw [boundary.summary.area_eq]
  exact converted.trans_eq (by
      change 2 * ((4 : Fraction.Rational)^2 * (16 * target^2) + 4 * ((4 : Fraction.Rational)^2 * target)^2) = _;
      ring1)

end PairedBandSelection
end Purelib.Riemann.RootContinuation.PreparedNewtonPairedBoundary
