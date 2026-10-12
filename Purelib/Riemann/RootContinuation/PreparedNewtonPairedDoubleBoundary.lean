module
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBudget
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.State.Raw

import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBoundary
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.RootContinuation.PreparedNewtonBandBoundary
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedTotals

open Purelib.Data

public section

/-! Two actual laps inherit owners and retain the complete paired area. -/
section

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
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedBoundary (PairedBoundaryTraversal)
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

namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedBoundary.PairedBoundaryTraversal

open Purelib.Curves.Hyperelliptic in
/-- Ordered concatenation of the retained traversal's four paired side lists. -/
@[expose] def increments
  {request : PreparedBandRequest fixed target} {other : Differentials.Basic.Differential genus}
    {owner : Owner (curve.polynomial.eval request.sample.output.box.anchor)} {sheet : Fin 2}
    (boundary : PairedBoundaryTraversal request other owner sheet) :=
  [boundary.bottom.refined.incrementBlocks.flatten, boundary.right.refined.incrementBlocks.flatten,
    boundary.top.refined.incrementBlocks.flatten, boundary.left.refined.incrementBlocks.flatten].flatten

end Purelib.Riemann.RootContinuation.PreparedNewtonPairedBoundary.PairedBoundaryTraversal

namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedDoubleBoundary

open Purelib.Curves.Hyperelliptic in
open Purelib.Integration.Path in
set_option genInjectivity false in
/-- Two sequential traversals of a retained paired band boundary.

The second traversal starts at the first's actual finish owner, and the cached summary retains the exact concatenation
of both increment lists. -/
structure PairedDoubleBoundary (request : PreparedBandRequest fixed target) (other : Differentials.Basic.Differential
  genus)
    (owner : Owner (curve.polynomial.eval request.sample.output.box.anchor)) (sheet : Fin 2) where
  /-- First traversal starting at the original owner. -/ first : PairedBoundaryTraversal request other owner sheet
  /-- Second traversal starting at the first traversal's actual finish owner. -/ second : PairedBoundaryTraversal
    request other first.finishOwner sheet
  /-- Cached summary of the exact first-then-second increment concatenation. -/ summary : PairedIncrementArea.Summary
    (first.increments ++ second.increments)

constructive_injectivity PairedDoubleBoundary

end Purelib.Riemann.RootContinuation.PreparedNewtonPairedDoubleBoundary

section
variable {request : PreparedBandRequest fixed target} {other :
  Differential genus}
  {owner : Owner (curve.polynomial.eval request.sample.output.box.anchor)} {sheet : Fin 2}

namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedDoubleBoundary.PairedDoubleBoundary

open Purelib.Curves.Hyperelliptic in
open Purelib.Integration.Path in
/-- Build two sequential paired traversals and append their cached summaries.

Keeps the same request, second differential and sheet while passing the actual first finish owner into the second
traversal. -/
@[expose] def build (request : PreparedBandRequest fixed target) (other : Differentials.Basic.Differential genus)
    (owner : Owner (curve.polynomial.eval request.sample.output.box.anchor)) (sheet : Fin 2) :
    PreparedNewtonPairedDoubleBoundary.PairedDoubleBoundary request other owner sheet :=
  let first := PairedBoundaryTraversal.build request other owner sheet
  let second := PairedBoundaryTraversal.build request other first.finishOwner sheet
  ⟨first, second, PairedAreaBlocks.Summary.append first.summary second.summary⟩

/-- Actual root owner after the second retained boundary traversal. -/
@[expose] def finishOwner
    (boundary : PreparedNewtonPairedDoubleBoundary.PairedDoubleBoundary request other owner sheet) :
    Owner (curve.polynomial.eval request.sample.output.box.anchor) := boundary.second.finishOwner

end Purelib.Riemann.RootContinuation.PreparedNewtonPairedDoubleBoundary.PairedDoubleBoundary

end
section
variable {other : Differential genus} {right : DifferentialProfile
  profile other.exponent} {radius : Purelib.Data.Rat.Fraction.Rational}

namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedBudget.PairedBandSelection

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- Bound a retained double traversal area by 34816 times the squared target.

Applies the eight side area and total certificates to the original block-area estimate, keeping the exact two-traversal
increment order and cached summary. -/
theorem double_area_bound
  (selection : PairedBandSelection fixed right target radius)
    {owner : Owner (curve.polynomial.eval selection.sample.output.box.anchor)} {sheet : Fin 2}
    (boundary : PreparedNewtonPairedDoubleBoundary.PairedDoubleBoundary selection.sourceRequest other owner sheet) :
    normSq boundary.summary.areaValue ≤ 34816 * target^2 := by
  let blocks := [boundary.first.bottom.refined.incrementBlocks.flatten,
    boundary.first.right.refined.incrementBlocks.flatten,
    boundary.first.top.refined.incrementBlocks.flatten,
    boundary.first.left.refined.incrementBlocks.flatten,
    boundary.second.bottom.refined.incrementBlocks.flatten,
    boundary.second.right.refined.incrementBlocks.flatten,
    boundary.second.top.refined.incrementBlocks.flatten,
    boundary.second.left.refined.incrementBlocks.flatten]
  have flatten : blocks.flatten = boundary.first.increments ++ boundary.second.increments := by
    simp only [blocks, PairedBoundaryTraversal.increments, List.flatten_cons, List.flatten_nil, List.Append.append_nil,
      List.Append.append_assoc, -eq_self, -iff_self]
    rfl
  have areas : ∀ block ∈ blocks, normSq (PairedIncrementArea.area block) ≤ 16 * target^2 := by
    intro block member
    dsimp only [blocks] at member
    cases member with
    | head =>
        rw [← boundary.first.bottom.summary.area_eq]
        simpa only [Norm.Basic.normSq_eq_canonical] using
          selection.side_area_bound boundary.first.bottom
    | tail _ member =>
        cases member with
        | head =>
            rw [← boundary.first.right.summary.area_eq]
            simpa only [Norm.Basic.normSq_eq_canonical] using
              selection.side_area_bound boundary.first.right
        | tail _ member =>
            cases member with
            | head =>
                rw [← boundary.first.top.summary.area_eq]
                simpa only [Norm.Basic.normSq_eq_canonical] using
                  selection.side_area_bound boundary.first.top
            | tail _ member =>
                cases member with
                | head =>
                    rw [← boundary.first.left.summary.area_eq]
                    simpa only [Norm.Basic.normSq_eq_canonical] using
                      selection.side_area_bound boundary.first.left
                | tail _ member =>
                    cases member with
                    | head =>
                        rw [← boundary.second.bottom.summary.area_eq]
                        simpa only [Norm.Basic.normSq_eq_canonical] using
                          selection.side_area_bound boundary.second.bottom
                    | tail _ member =>
                        cases member with
                        | head =>
                            rw [← boundary.second.right.summary.area_eq]
                            simpa only [Norm.Basic.normSq_eq_canonical] using
                              selection.side_area_bound boundary.second.right
                        | tail _ member =>
                            cases member with
                            | head =>
                                rw [← boundary.second.top.summary.area_eq]
                                simpa only [Norm.Basic.normSq_eq_canonical] using
                                  selection.side_area_bound boundary.second.top
                            | tail _ member =>
                                cases member with
                                | head =>
                                    rw [← boundary.second.left.summary.area_eq]
                                    simpa only [Norm.Basic.normSq_eq_canonical] using
                                      selection.side_area_bound boundary.second.left
                                | tail _ member =>
                                    cases member
  have totals : ∀ block ∈ blocks, Bounded (PairedIncrementArea.total block) target := by
    intro block member
    dsimp only [blocks] at member
    cases member with
    | head =>
        rw [← boundary.first.bottom.summary.total_eq]
        simpa only [Norm.Basic.normSq_eq_canonical] using
          selection.side_total_bound boundary.first.bottom
    | tail _ member =>
        cases member with
        | head =>
            rw [← boundary.first.right.summary.total_eq]
            simpa only [Norm.Basic.normSq_eq_canonical] using
              selection.side_total_bound boundary.first.right
        | tail _ member =>
            cases member with
            | head =>
                rw [← boundary.first.top.summary.total_eq]
                simpa only [Norm.Basic.normSq_eq_canonical] using
                  selection.side_total_bound boundary.first.top
            | tail _ member =>
                cases member with
                | head =>
                    rw [← boundary.first.left.summary.total_eq]
                    simpa only [Norm.Basic.normSq_eq_canonical] using
                      selection.side_total_bound boundary.first.left
                | tail _ member =>
                    cases member with
                    | head =>
                        rw [← boundary.second.bottom.summary.total_eq]
                        simpa only [Norm.Basic.normSq_eq_canonical] using
                          selection.side_total_bound boundary.second.bottom
                    | tail _ member =>
                        cases member with
                        | head =>
                            rw [← boundary.second.right.summary.total_eq]
                            simpa only [Norm.Basic.normSq_eq_canonical] using
                              selection.side_total_bound boundary.second.right
                        | tail _ member =>
                            cases member with
                            | head =>
                                rw [← boundary.second.top.summary.total_eq]
                                simpa only [Norm.Basic.normSq_eq_canonical] using
                                  selection.side_total_bound boundary.second.top
                            | tail _ member =>
                                cases member with
                                | head =>
                                    rw [← boundary.second.left.summary.total_eq]
                                    simpa only [Norm.Basic.normSq_eq_canonical] using
                                      selection.side_total_bound boundary.second.left
                                | tail _ member =>
                                    cases member
  have nonnegative : 0 ≤ target := (Basic.Canonical.normSq_nonneg boundary.first.bottom.summary.totalValue.left).trans
    (selection.side_total_bound boundary.first.bottom).1
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
  rw [boundary.summary.area_eq, ← flatten]
  exact converted.trans_eq (by
      change 2 * ((8 : Fraction.Rational)^2 * (16 * target^2) + 4 * ((8 : Fraction.Rational)^2 * target)^2) = _;
      ring1)

end Purelib.Riemann.RootContinuation.PreparedNewtonPairedBudget.PairedBandSelection

end
end
