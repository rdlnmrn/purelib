module
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonCapOrigins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSigns
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonBlockArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonSignChain
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.AreaRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSigns
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
open Purelib.Geometry.Path.Gaussian
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Topology
open Purelib.Topology.Chain
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes

/-! Endpoint root joins propagate the common reciprocal sheet sign between
whole retained parents, even when their common covers have different depths. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily (CommonRibbonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest (Entry Evaluation)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
variable {genus count otherCount : Nat} {curve : HyperellipticCurve genus}
  {differential other : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : CenteredEdge curve differential} {patch :
    PreparedPatch parent}
  {otherPatch : PreparedPatch
    (Purelib.Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {firstCover : Cover data} {secondCover :
    Cover otherData}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {common :
    CommonCover firstCover secondCover}
  {target : Coordinate} {minimum stage depth : Nat} {box otherBox :
    Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {source : SourcePrimitive data stage}
    {otherSource : SourcePrimitive otherData
    stage}
  {request : CommonRibbonRequest regular common
    target minimum}

/-- A retained interval path with distinct endpoints contains an actual first interval at its original starting
parameter. -/
private theorem path_first (entries : List (CommonRibbonRequest.Entry request sample otherSample source otherSource
  depth))
    {start finish : InverseRootPolynomial.Coordinate}
    (path : PathBoundary.PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter)
      (entries.map (fun entry => entry.plan.interval.edge)) start finish) (different : start ≠ finish) :
    ∃ entry ∈ entries, entry.plan.interval.edge.left.parameter = start := by
  cases entries with
  | nil => cases path; exact False.elim (different rfl)
  | cons head tail => cases path; exact ⟨head, List.mem_cons_self, rfl⟩

/-- A nonempty retained interval path contains an actual last interval at its original finishing parameter. -/
private theorem path_last (entries : List (CommonRibbonRequest.Entry request sample otherSample source otherSource
  depth))
    {start finish : InverseRootPolynomial.Coordinate}
    (path : PathBoundary.PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter)
      (entries.map (fun entry => entry.plan.interval.edge)) start finish) (nonempty : entries ≠ []) :
    ∃ entry ∈ entries, entry.plan.interval.edge.right.parameter = finish := by
  induction entries generalizing start with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail ih =>
      cases path with
      | cons tailPath =>
          cases tail with
          | nil => cases tailPath; exact ⟨head, List.mem_cons_self, rfl⟩
          | cons next rest =>
              obtain ⟨entry, member, endpoint⟩ := ih tailPath (by intro empty; cases empty)
              exact ⟨entry, List.mem_cons_of_mem head member, endpoint⟩

/-- The actual common-ribbon evaluation contains an original interval beginning at parameter zero. -/
theorem Evaluation.first_entry (evaluated : CommonRibbonRequest.Evaluation request sample otherSample source otherSource
  depth) :
    ∃ entry ∈ evaluated.entries, entry.plan.interval.edge.left.parameter = 0 :=
  path_first evaluated.entries
    evaluated.parameterPath (by decide)

/-- The actual common-ribbon evaluation contains an original interval ending at parameter one. -/
theorem Evaluation.last_entry (evaluated : CommonRibbonRequest.Evaluation request sample otherSample source otherSource
  depth) :
    ∃ entry ∈ evaluated.entries, entry.plan.interval.edge.right.parameter = 1 := by
  have nonempty : evaluated.entries ≠ [] := by
    intro empty
    obtain ⟨entry, member, _⟩ := evaluated.first_entry
    rw [empty] at member
    exact List.not_mem_nil member
  exact path_last evaluated.entries
    evaluated.parameterPath nonempty

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request (Entry)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
variable {genus : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {parents : List
    (CenteredEdge curve differential)}
  {target : Coordinate} {minimum stage fine : Nat} {box otherBox :
    Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {request : Request regular other parents
    target minimum}

/-- Original endpoint coordinate and root-name agreement identify the same retained reciprocal sheet sign across
adjacent parents. -/
theorem Entry.adjacent_sign (first last : PairedParentRequest.Request.Entry request sample otherSample fine)
    (same : first.plan.parent.edge.point 1 = last.plan.parent.edge.point 0)
    (roots : Gaussian.Equivalence.NamedEquivalent (first.plan.parent.edge.rootName 1 (by decide))
      (last.plan.parent.edge.rootName 0 last.plan.parent.edge.baseInside)) :
    first.certified.shared.flip = last.certified.shared.flip := by
  obtain ⟨left, leftMember, leftEnd⟩ := first.certified.ribbons.last_entry
  obtain ⟨right, rightMember, rightStart⟩ := last.certified.ribbons.first_entry
  have leftInside : left.plan.interval.first.owner.left.parameter ≤ 1 ∧
      1 ≤ left.plan.interval.first.owner.right.parameter := by
    rw [← leftEnd]
    exact ⟨left.plan.interval.first.lower.trans left.plan.interval.ordered, left.plan.interval.first.upper⟩
  have rightInside : right.plan.interval.first.owner.left.parameter ≤ 0 ∧
      0 ≤ right.plan.interval.first.owner.right.parameter := by
    rw [← rightStart]
    exact ⟨right.plan.interval.first.lower, right.plan.interval.ordered.trans right.plan.interval.first.upper⟩
  let leftPoint := ArcOwners.Point.build cap (RootModel.build left.plan.interval.first.cell) 1 leftInside
  let rightPoint := ArcOwners.Point.build cap (RootModel.build right.plan.interval.first.cell) 0 rightInside
  let joined := SourceJoin.build leftPoint.root rightPoint.root
    (first.plan.parent.edge.point 1) rfl same.symm roots
  have sign := Join.paired_same_sign
    (Join.ofRoots leftPoint rightPoint same
      (SourceJoin.rootEquivalent joined))
    left.left right.left first.ready
  have leftSign := (first.certified.ribbons.shared_signs first.ready left leftMember).1
  have rightSign := (last.certified.ribbons.shared_signs last.ready right rightMember).1
  exact first.certified.shared.flip_eq.trans (leftSign.symm.trans (sign.trans
    (rightSign.trans last.certified.shared.flip_eq.symm)))

/-- Read the first actual retained paired-parent sign, using the unsigned sign for an empty bank. -/
@[expose] def firstFlip : List (PairedParentRequest.Request.Entry request sample otherSample fine) → Bool
  | [] => false
  | head :: _ => head.certified.shared.flip

/-- The actual direct parent chain begins at its first retained parent's original starting point. -/
private theorem chain_start {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential}
    {tail : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {start finish :
      Lifted.Basic.LiftedPoint 2}
    (chain : PreparedDirectDyadicRefinements.DirectPathChain (parent :: tail) (start := start) (finish := finish)) :
    start.coordinate = parent.edge.point 0 := by
  cases chain
  exact parent.edge.point_zero.symm

/-- The original coordinate and root chains identify one retained sheet sign throughout all actual parent entries. -/
private theorem path_signs (entries : List (PairedParentRequest.Request.Entry request sample otherSample fine))
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : PreparedDirectDyadicRefinements.DirectPathChain (entries.map (fun entry => entry.plan.parent)) (start :=
      start) (finish := finish))
    {first last : Gaussian.Name.Basic.Named}
    (roots : PreparedRefinementRootChains.RootChain (entries.map (fun entry => entry.plan.parent)) first last) :
    ∀ entry ∈ entries, entry.certified.shared.flip =
      firstFlip entries := by
  induction entries generalizing start first with
  | nil => intro entry member; exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
      cases chain with
      | cons parent chain =>
          cases roots with
          | cons parent entryRoot roots =>
              intro entry member
              rcases Data.List.Membership.mem_cons.mp member with same | member
              · subst entry; rfl
              · cases tail with
                | nil => exact False.elim (List.not_mem_nil member)
                | cons next rest =>
                    have physical : head.plan.parent.edge.point 1 = next.plan.parent.edge.point 0 :=
                      head.plan.parent.edge.point_one.trans
                        (chain_start chain)
                    have rootJoin : Gaussian.Equivalence.NamedEquivalent (head.plan.parent.edge.rootName 1 (by decide))
                        (next.plan.parent.edge.rootName 0 next.plan.parent.edge.baseInside) :=
                      match roots with
                      | .cons _ joined _ => joined
                    exact (ih chain roots entry member).trans (head.adjacent_sign next physical rootJoin).symm

/-- The original cached path and root chain identify one sheet bit across every retained parent. No caller equality
between separately prepared signs is needed, and the count-paid evaluator keeps its original samples. -/
theorem Evaluation.shared_signs (evaluated : PairedParentRequest.Request.Evaluation request sample otherSample fine)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named} (roots : PreparedRefinementRootChains.RootChain parents first last) :
    ∀ entry ∈ evaluated.retained, entry.certified.shared.flip =
      firstFlip evaluated.retained := by
  have parentsEq := (congrArg (List.map Plan.parent) evaluated.plans_eq).trans request.parents_eq
  rw [Data.List.Map.map_map] at parentsEq
  obtain ⟨chain⟩ := chain
  exact path_signs evaluated.retained
    (parentsEq.symm ▸ chain) (parentsEq.symm ▸ roots)

/-- Negate both components of the original paired primitive point. -/
private def negate (point : Stokes.PrimitivePoint) : PrimitivePoint := ⟨-point.left, -point.right⟩

/-- Negating every original paired increment negates its exact complete total. -/
private theorem total_negate (points : List Stokes.PrimitivePoint) :
    PairedIncrementArea.total (points.map
      negate) =
      negate (PairedIncrementArea.total points)
      := by
  induction points with
  | nil => apply congrArg₂ PrimitivePoint.mk <;> exact (neg_zero).symm
  | cons head tail ih =>
      change (negate head).add
        (PairedIncrementArea.total (tail.map
        negate)) =
        negate (head.add
          (PairedIncrementArea.total tail))
      rw [ih]
      apply congrArg₂ PrimitivePoint.mk <;> dsimp only
        [negate, PrimitivePoint.add] <;> ring1

/-- Negating both components of every original paired increment preserves the complete path area. -/
private theorem area_negate (points : List Stokes.PrimitivePoint) :
    PairedIncrementArea.area (points.map negate)
      = PairedIncrementArea.area points := by
  induction points with
  | nil => rfl
  | cons head tail ih =>
      rw [List.map_cons, PairedAreaBlocks.area_cons, PairedAreaBlocks.area_cons,
        total_negate, ih]
      simp only [Stokes.edgeArea, negate,
        -eq_self, -iff_self]
      ring1

/-- The actual retained signed cap total is the original unsigned cap-path total with its exact cached common sign. -/
private theorem Entry.signed_total (entry : PairedParentRequest.Request.Entry request sample otherSample fine) :
    entry.certified.compared.secondSummary.totalValue =
      if entry.certified.shared.flip then negate
        (PairedIncrementArea.total entry.pair.2)
      else PairedIncrementArea.total entry.pair.2 := by
  rw [entry.certified.compared.secondSummary.total_eq, (Certified.cap_path entry.certified)]
  change PairedIncrementArea.total (DyadicPairedPrimitivePaths.increments _ _ 0 1) =
    if entry.certified.shared.flip then negate
      (PairedIncrementArea.total (DyadicPairedPrimitivePaths.increments _ _ 0 1))
    else PairedIncrementArea.total (DyadicPairedPrimitivePaths.increments _ _ 0 1)
  rw [DyadicPairedPrimitivePaths.increments_total, DyadicPairedPrimitivePaths.increments_total]
  cases bit : entry.certified.shared.flip with
  | false =>
      have point (parameter : InverseRootPolynomial.Coordinate) : entry.certified.shared.values parameter =
          CommonRibbonRequest.capValues (parent := entry.plan.parent) sample otherSample parameter := by
        apply congrArg₂ PrimitivePoint.mk <;>
          simp only [entry.certified.shared.first_eq, entry.certified.shared.second_eq, bit, if_neg (show ¬ (false =
            true) from by decide), -eq_self, -iff_self] <;> rfl
      rw [point 0, point 1]
      rfl
  | true =>
      have point (parameter : InverseRootPolynomial.Coordinate) : entry.certified.shared.values parameter =
          negate (CommonRibbonRequest.capValues
            (parent := entry.plan.parent) sample otherSample parameter) := by
        apply congrArg₂ PrimitivePoint.mk <;>
          simp only [CommonRibbonRequest.capValues, entry.certified.shared.first_eq,
            entry.certified.shared.second_eq, bit, if_pos (Eq.refl true), DensePolynomial.eval_neg, -eq_self, -iff_self]
              <;> rfl
      rw [point 0, point 1]
      apply congrArg₂ PrimitivePoint.mk <;> dsimp only
        [negate, PrimitivePoint.sub] <;> ring1

/-- The polygon of cached signed cap totals is exactly the unsigned cap polygon once the actual parent root chain has
propagated the common sign. -/
theorem Evaluation.cap_polygon_unsigned (evaluated : PairedParentRequest.Request.Evaluation request sample otherSample
  fine)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named} (roots : PreparedRefinementRootChains.RootChain parents first last) :
    PairedIncrementArea.area (evaluated.retained.map (fun entry => entry.certified.compared.secondSummary.totalValue)) =
      PairedIncrementArea.area ((evaluated.pairs.map Prod.snd).map PairedIncrementArea.total) := by
  have signs := evaluated.shared_signs chain roots
  have values : evaluated.retained.map (fun entry => entry.certified.compared.secondSummary.totalValue) =
      evaluated.retained.map (fun entry => if
        firstFlip evaluated.retained then
        negate (PairedIncrementArea.total
          entry.pair.2) else PairedIncrementArea.total entry.pair.2) := by
    generalize fixed : firstFlip
      evaluated.retained = bit at signs ⊢
    generalize retainedEq : evaluated.retained = retained at signs ⊢
    clear retainedEq
    induction retained with
    | nil => rfl
    | cons head tail ih =>
        apply congrArg₂ List.cons
        · change head.certified.compared.secondSummary.totalValue =
            if bit then negate
              (PairedIncrementArea.total head.pair.2) else PairedIncrementArea.total head.pair.2
          rw [head.signed_total, signs head List.mem_cons_self]
        · exact ih (fun entry member => signs entry (List.mem_cons_of_mem head member))
  rw [values, evaluated.pairs_eq]
  cases bit : firstFlip evaluated.retained with
  | false =>
      change PairedIncrementArea.area (evaluated.retained.map (fun entry => PairedIncrementArea.total entry.pair.2)) = _
      simp only [Data.List.Map.map_map, -eq_self, -iff_self]
      rfl
  | true =>
      change PairedIncrementArea.area (evaluated.retained.map (fun entry =>
        negate (PairedIncrementArea.total
        entry.pair.2))) = _
      have result :=
        area_negate (evaluated.retained.map (fun
          entry => PairedIncrementArea.total entry.pair.2))
      simp only [Data.List.Map.map_map, -eq_self, -iff_self] at result ⊢
      dsimp only [Function.comp_def] at result ⊢
      exact result

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request
