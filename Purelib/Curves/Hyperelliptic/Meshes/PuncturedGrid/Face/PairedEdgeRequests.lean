module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveNegation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Riemann.Paths.RectangularPairedSegments
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.RegularFaceInverseModels
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

section

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveNegation

open Purelib.Data.Rat

open Purelib.Riemann.Comparison

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.RectangularPairedSegments

open Purelib.Riemann.Readings

public section

/-!
# One finite request for opposite-sheet comparison on a whole face edge

The retained two-domain split determines the actual fragment count. Cache
every local model bound and index once, together with both grid ownership
budgets. One common lower index works for independently refined primitives.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomains)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Riemann.Paths.RectangularPairedSegments (PairedSegmentPiece PairedSegmentSplit)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds PrimitiveEdgeAccuracy)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank}

namespace PairedEdgeRequest

set_option genInjectivity false in
/-- A cached opposite-sheet primitive request on one actual retained paired segment piece.

The request keeps both numerical models, their source charts and exact
endpoints. Its stage and accuracy certificate belong to that same piece. -/
structure Local (domains : DomainBanks.FaceDomains frames face) (differential : Differentials.Basic.Differential genus)
    (piece : RectangularPairedSegments.PairedSegmentPiece (domains.domain 0).geometry (domains.domain 1).geometry)
      (target : Fraction.Rational) where
  /-- The cached overlap bounds on the actual first-sheet model cell and supplied differential. -/ bounds :
    PrimitiveEdgeComparison.PrimitiveOverlapBounds
    (face.clearance.restrict ((domains.domain 0).patch.transported.cell piece.leftColumn
      piece.leftRow).geometry.refines)
    (PreparedPrimitiveSamples.differentialNumerator differential)
  /-- The cached primitive-increment request on these exact two retained models and endpoints. -/ request :
    PrimitiveEdgeComparison.PrimitiveEdgeAccuracy bounds ((domains.domain 0).patch.models.ready piece.leftColumn
    piece.leftRow).model
    ((domains.domain 1).patch.models.ready piece.rightColumn piece.rightRow).model piece.first piece.last target

constructive_injectivity Local

/-- Cache the overlap bound and local accuracy request for these exact two retained models and segment endpoints. -/
@[expose] def Local.build (domains : DomainBanks.FaceDomains frames face) (differential :
  Differentials.Basic.Differential genus)
    (piece : RectangularPairedSegments.PairedSegmentPiece (domains.domain 0).geometry (domains.domain 1).geometry)
    (target : Fraction.Rational) (positive : 0 < target) :
      Local domains differential
      piece target :=
  let bounds := PrimitiveOverlapBounds.build
    (face.clearance.restrict ((domains.domain 0).patch.transported.cell piece.leftColumn
      piece.leftRow).geometry.refines)
    (PreparedPrimitiveSamples.differentialNumerator differential)
  ⟨bounds, PrimitiveEdgeAccuracy.build bounds _ _ _ _ target positive⟩

set_option genInjectivity false in
/-- A complete dependent list of local requests on the exact retained two-domain split.

The head request and tail spine retain the original split-piece order,
including repetitions, with each request attached to its actual piece. -/
inductive Locals (domains : DomainBanks.FaceDomains frames face) (differential : Differentials.Basic.Differential genus)
  (target : Fraction.Rational) :
    List (RectangularPairedSegments.PairedSegmentPiece (domains.domain 0).geometry (domains.domain 1).geometry) → Type
  /-- The empty local request bank for an empty retained piece list. -/ | nil :
    Locals domains
    differential target []
  /-- Retain the request for the actual first piece and the exact dependent tail. -/ | cons {piece rest} (localRequest :
    Local domains differential piece
    target)
      (tail : Locals domains
        differential target rest) :
        Locals domains
        differential target (piece :: rest)

constructive_injectivity Locals

namespace Locals

variable {domains : FaceDomains frames face}
  {differential : Differential genus} {target :
  Rational}

/-- Prepare every actual paired split piece at the supplied positive local target. -/
@[expose] def build (domains : DomainBanks.FaceDomains frames face) (differential : Differentials.Basic.Differential
  genus) (target : Fraction.Rational) (positive : 0 < target) :
    (pieces : List (RectangularPairedSegments.PairedSegmentPiece (domains.domain 0).geometry (domains.domain
      1).geometry)) →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests.PairedEdgeRequest.Locals domains differential
        target pieces
  | [] => .nil
  | piece :: rest => .cons
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests.PairedEdgeRequest.Local.build domains
    differential piece target positive)
      (build domains
        differential target positive rest)

/-- Read the common maximum of all retained local model indices. -/
@[expose] def index : {pieces : List (RectangularPairedSegments.PairedSegmentPiece (domains.domain 0).geometry
  (domains.domain 1).geometry)} →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests.PairedEdgeRequest.Locals domains differential
      target pieces → Nat
  | _, .nil => 0
  | _, .cons head tail => max head.request.index tail.index

/-- Every actual retained paired piece satisfies its paid opposite-sheet primitive-sum error at independently later
indices. -/
theorem accurate {pieces : List (RectangularPairedSegments.PairedSegmentPiece (domains.domain 0).geometry
  (domains.domain 1).geometry)}
    (requests : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests.PairedEdgeRequest.Locals domains
      differential target pieces) {leftIndex rightIndex : Nat}
    (first : PrimitiveData.DomainPrimitives (domains.domain 0) differential leftIndex)
    (second : PrimitiveData.DomainPrimitives (domains.domain 1) differential rightIndex)
    (leftLater : requests.index ≤ leftIndex) (rightLater : requests.index ≤ rightIndex)
    (piece : RectangularPairedSegments.PairedSegmentPiece (domains.domain 0).geometry (domains.domain 1).geometry)
      (member : piece ∈ pieces) :
    Data.Gaussian.Norm.Basic.normSq ((first.primitives.value piece.leftColumn piece.leftRow piece.last -
        first.primitives.value piece.leftColumn piece.leftRow piece.first) +
      (second.primitives.value piece.rightColumn piece.rightRow piece.last -
        second.primitives.value piece.rightColumn piece.rightRow piece.first)) < target := by
  induction requests with
  | nil => exact (List.not_mem_nil member).elim
  | cons head tail ih =>
      rcases Data.List.Membership.mem_cons.mp member with rfl | remaining
      · exact FaceDomains.cell_primitive_sum_accurate domains _ _ _ _ head.request first second
          piece.leftFirst piece.leftLast piece.rightFirst piece.rightLast
          ((Data.Nat.Order.le_max_left _ _).trans leftLater) ((Data.Nat.Order.le_max_left _ _).trans rightLater)
      · exact ih ((Data.Nat.Order.le_max_right _ _).trans leftLater) ((Data.Nat.Order.le_max_right _ _).trans
          rightLater) remaining

end Locals
end PairedEdgeRequest

set_option genInjectivity false in
/-- A finite opposite-sheet comparison request for one whole retained face edge.

The actual split count pays each local fragment and both grid-owner errors, and the common index preserves the two
original domain caches. -/
structure PairedEdgeRequest (domains : DomainBanks.FaceDomains frames face) (differential :
  Differentials.Basic.Differential genus)
    (first last : Data.Gaussian.Basic.Canonical) (target : Fraction.Rational) where
  /-- The supplied whole-edge target is positive. -/ positive : 0 < target
  /-- The cached split of the original endpoints across both retained sheet-domain grids. -/ split :
    RectangularPairedSegments.PairedSegmentSplit (domains.domain 0).cuts (domains.domain 1).cuts first last
  /-- The cached count-dependent target for each actual split piece. -/ perPiece : Fraction.Rational
  /-- The per-piece target is the finite allocation from one quarter of the whole-edge target. -/ perPiece_eq : perPiece
    = Aggregate.perTerm (target / 4) split.count
  /-- The cached whole-face primitive overlap bounds for the supplied differential. -/ globalBounds :
    PrimitiveEdgeComparison.PrimitiveOverlapBounds face.clearance (PreparedPrimitiveSamples.differentialNumerator
    differential)
  /-- The retained first-sheet ownership accuracy request. -/ leftGrid :
    RectangularPrimitiveAccuracy.GridPrimitiveAccuracy globalBounds (domains.domain 0).steps (perPiece / 256)
  /-- The retained second-sheet ownership accuracy request. -/ rightGrid :
    RectangularPrimitiveAccuracy.GridPrimitiveAccuracy globalBounds (domains.domain 1).steps (perPiece / 256)
  /-- The cached local opposite-sheet primitive comparisons on the exact split pieces. -/ locals :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests.PairedEdgeRequest.Locals domains differential
    (perPiece / 4) split.pieces
  /-- The cached common lower index for both ownership requests and all local comparisons. -/ index : Nat
  /-- The common index is exactly the maximum of both grid requests and the retained local request bank. -/ index_eq :
    index = max (max leftGrid.index rightGrid.index) locals.index

constructive_injectivity PairedEdgeRequest

namespace PairedEdgeRequest

/-- Cache the actual two-domain split, both ownership budgets and every local primitive request before selecting a
shared stage. -/
@[expose] def build (domains : DomainBanks.FaceDomains frames face) (differential : Differentials.Basic.Differential
  genus) (first last : Data.Gaussian.Basic.Canonical)
    (firstInside : face.cell.box.Contains first) (lastInside : face.cell.box.Contains last)
    (target : Fraction.Rational) (positive : 0 < target) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests.PairedEdgeRequest domains differential first
      last target :=
  let split := PairedSegmentSplit.build (domains.domain 0).cuts (domains.domain 1).cuts first last
    ((domains.domain 0).covers firstInside) ((domains.domain 0).covers lastInside)
    ((domains.domain 1).covers firstInside) ((domains.domain 1).covers lastInside)
  let perPiece := Aggregate.perTerm (target / 4) split.count
  have perPositive : 0 < perPiece := Aggregate.perTerm_positive
    (Fraction.Order.Field.div_pos_direct positive (by decide)) _
  let globalBounds := PrimitiveOverlapBounds.build
    face.clearance (PreparedPrimitiveSamples.differentialNumerator differential)
  let leftGrid := GridPrimitiveAccuracy.build globalBounds (domains.domain 0).steps (perPiece / 256)
    (Fraction.Order.Field.div_pos_direct perPositive (by decide +kernel))
  let rightGrid := GridPrimitiveAccuracy.build globalBounds (domains.domain 1).steps (perPiece / 256)
    (Fraction.Order.Field.div_pos_direct perPositive (by decide +kernel))
  let locals := Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests.PairedEdgeRequest.Locals.build domains
    differential (perPiece / 4)
    (Fraction.Order.Field.div_pos_direct perPositive (by decide)) split.pieces
  ⟨positive, split, perPiece, rfl, globalBounds, leftGrid, rightGrid, locals,
    max (max leftGrid.index rightGrid.index) locals.index, rfl⟩

variable {domains : FaceDomains frames face}
  {differential : Differential genus} {first last :
  Purelib.Data.Gaussian.Basic.Canonical} {target : Rational}

/-- The retained count-dependent piece allocation is positive. -/
theorem perPiece_positive (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests.PairedEdgeRequest
  domains differential first last target) : 0 < request.perPiece := by
  rw [request.perPiece_eq]
  exact Aggregate.perTerm_positive (Fraction.Order.Field.div_pos_direct request.positive (by decide)) _

/-- The common request index bounds the retained first-sheet ownership index. -/
theorem left_later (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests.PairedEdgeRequest
  domains differential first last target) : request.leftGrid.index ≤ request.index := by
  rw [request.index_eq]
  exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _)

/-- The common request index bounds the retained second-sheet ownership index. -/
theorem right_later (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests.PairedEdgeRequest
  domains differential first last target) : request.rightGrid.index ≤ request.index := by
  rw [request.index_eq]
  exact (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_left _ _)

/-- The common request index bounds every retained local primitive comparison. -/
theorem locals_later (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests.PairedEdgeRequest
  domains differential first last target) : request.locals.index ≤ request.index := by
  rw [request.index_eq]
  exact Data.Nat.Order.le_max_right _ _

end PairedEdgeRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests

end
