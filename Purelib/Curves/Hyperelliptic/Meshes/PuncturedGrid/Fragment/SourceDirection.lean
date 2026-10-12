module
import Purelib.Algebra.Group.Basic
public import Purelib.Algebra.Group.Negation
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordJunctions
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation
public import Purelib.Riemann.Paths.PreparedSegmentSources
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

public section

/-!
# Original source direction determines the fragment route lookup

Moving fragments on the same original segment have positive displacement
factors. When their containing edge endpoints agree, their actual rational
edge parameters therefore choose the same oriented route. Stationary
fragments are handled by exact zero increments separately.
-/

section

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.RootIsolation

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : SquareRoot.Grid.RootFrames base.bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {source : Hyperelliptic.Differentials.Basic.Differential genus} {axes :
    Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveAxes base.bank.grid}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars} {mesh :
    Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Fraction.Rational}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection

/-- An affine source-segment displacement is its parameter difference times the original endpoint displacement. -/
private theorem segment_difference {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish) (first last : Fraction.Rational) :
    segment.pointAt last - segment.pointAt first = (⟨last - first, 0⟩ : Gaussian.Basic.Canonical) * (finish - start) :=
      by
  apply Gaussian.Basic.ext <;>
    simp only [Geometry.ClearPath.ClearSegment.pointAt, Gaussian.Basic.add_re,
      Gaussian.Basic.add_im, Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im, Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im, Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, -eq_self, -iff_self] <;> ring1

/-- The actual fragment displacement is its retained interval width times the original parent displacement. -/
private theorem parent_difference (piece : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes
  domains mesh source count target) :
    piece.last - piece.first = (⟨piece.interval.upper - piece.interval.lower, 0⟩ : Gaussian.Basic.Canonical) *
      (piece.parent.edge.point 1 - piece.parent.edge.point 0) := by
  change piece.fragment.located.last - piece.fragment.located.first = _
  rw [piece.fragment.located.last_eq, piece.fragment.located.first_eq]
  apply Gaussian.Basic.ext <;>
    simp only [Integration.PreparedConstantModels.PreparedEdge.point, Geometry.ClearPath.ClearSegment.pointAt,
      Gaussian.Basic.add_re, Gaussian.Basic.add_im,
      Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
      Gaussian.Basic.mul_re, Gaussian.Basic.mul_im,
      Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, -eq_self, -iff_self] <;> ring1

/-- The actual fragment displacement equals its original containing-edge displacement times its retained parameter
difference. -/
private theorem edge_difference (piece : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes
  domains mesh source count target) :
    piece.last - piece.first =
      (⟨piece.fragment.source.last.parameter - piece.fragment.source.first.parameter, 0⟩ : Gaussian.Basic.Canonical) *
        (piece.fragment.source.finish - piece.fragment.source.start) := by
  change piece.fragment.located.last - piece.fragment.located.first = _
  exact (congrArg₂ (fun a b : Gaussian.Basic.Canonical => a - b) piece.fragment.source.last.point_eq
    piece.fragment.source.first.point_eq).symm.trans
      (Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.segment_difference _ _ _)

/-- Positive movement along the exact original segment; the factor comes
from its retained endpoint parameters and the actual fragment interval. -/
theorem source_displacement (piece : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains
  mesh source count target)
    {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    (original : Paths.PreparedSegmentSources.SegmentSource segment piece.parent) (moving : piece.last ≠ piece.first) :
    ∃ factor : Fraction.Rational, 0 < factor ∧ piece.last - piece.first = (⟨factor, 0⟩ : Gaussian.Basic.Canonical) *
      (finish - start) := by
  obtain ⟨first, last, nonnegative, ordered, bounded, firstEq, lastEq⟩ := original
  let factor := (piece.interval.upper - piece.interval.lower) * (last - first)
  have factorNonnegative : 0 ≤ factor := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.sub_nonneg_direct piece.interval.ordered.le)
    (Fraction.Order.Arithmetic.sub_nonneg_direct ordered)
  have movement : piece.last - piece.first = (⟨factor, 0⟩ : Gaussian.Basic.Canonical) * (finish - start) := by
    rw [Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.parent_difference, firstEq, lastEq,
      Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.segment_difference]
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.mul_re, Gaussian.Basic.mul_im,
        Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, factor, -eq_self, -iff_self] <;> ring1
  have factorNonzero : factor ≠ 0 := by
    intro zero
    rw [zero] at movement
    have vanished : piece.last - piece.first = 0 := by
      change _ = (0 : Gaussian.Basic.Canonical) * _ at movement
      simpa only [zero_mul, -eq_self, -iff_self] using movement
    exact moving (Algebra.Group.eq_of_sub_eq_zero vanished)
  exact ⟨factor, lt_of_le_of_ne factorNonnegative factorNonzero.symm, movement⟩

/-- Embedding a rational product into Gaussian scalars preserves multiplication. -/
private theorem scalar_product (a b : Fraction.Rational) :
    (⟨a * b, 0⟩ : Gaussian.Basic.Canonical) = (⟨a, 0⟩ : Gaussian.Basic.Canonical) * (⟨b, 0⟩ : Gaussian.Basic.Canonical)
      := by
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, -eq_self, -iff_self] <;> ring1

/-- Positive proportional movement along one nonzero original edge forces the two rational direction factors to have the
same sign. -/
private theorem scalar_nonnegative_iff {a b k l : Fraction.Rational} {edgeDelta sourceDelta : Gaussian.Basic.Canonical}
    (kPositive : 0 < k) (lPositive : 0 < l) (edgeNonzero : edgeDelta ≠ 0)
    (first : (⟨a, 0⟩ : Gaussian.Basic.Canonical) * edgeDelta = (⟨k, 0⟩ : Gaussian.Basic.Canonical) * sourceDelta)
    (last : (⟨b, 0⟩ : Gaussian.Basic.Canonical) * edgeDelta = (⟨l, 0⟩ : Gaussian.Basic.Canonical) * sourceDelta) :
    0 ≤ a ↔ 0 ≤ b := by
  have scaled : (⟨a * l, 0⟩ : Gaussian.Basic.Canonical) * edgeDelta = (⟨b * k, 0⟩ : Gaussian.Basic.Canonical) *
    edgeDelta := by
    rw [Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.scalar_product a l,
      Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.scalar_product b k]
    calc
      _ = (⟨l, 0⟩ : Gaussian.Basic.Canonical) * ((⟨a, 0⟩ : Gaussian.Basic.Canonical) * edgeDelta) := by ring1
      _ = (⟨k, 0⟩ : Gaussian.Basic.Canonical) * ((⟨l, 0⟩ : Gaussian.Basic.Canonical) * sourceDelta) := by
        rw [first];
        ring1
      _ = _ := by rw [← last]; ring1
  have equal : a * l = b * k := congrArg Gaussian.Basic.re
    (Gaussian.Field.mul_right_cancel_of_ne edgeNonzero scaled)
  constructor
  · intro nonnegative
    have bound := Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative lPositive.le
    rw [equal] at bound
    exact Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (by simpa only [Fraction.Field.zero_mul_direct, -eq_self, -iff_self] using bound) kPositive
  · intro nonnegative
    have bound := Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative kPositive.le
    rw [← equal] at bound
    exact Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (by simpa only [Fraction.Field.zero_mul_direct, -eq_self, -iff_self] using bound) lPositive

/-- Direction agreement is derived from the actual original source data,
including fragments from different descendant parents. -/
theorem routeForward_eq_of_source {left right : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment
  axes domains mesh source count target}
    {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    (leftSource : Paths.PreparedSegmentSources.SegmentSource segment left.parent) (rightSource :
      Paths.PreparedSegmentSources.SegmentSource segment right.parent)
    (leftMoving : left.last ≠ left.first) (rightMoving : right.last ≠ right.first)
    (startEq : left.fragment.source.start = right.fragment.source.start)
    (finishEq : left.fragment.source.finish = right.fragment.source.finish) :
      (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.routeForward left) =
      (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.routeForward right) := by
  obtain ⟨k, kPositive, leftMovement⟩ :=
    (Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.source_displacement left) leftSource leftMoving
  obtain ⟨l, lPositive, rightMovement⟩ :=
    (Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.source_displacement right) rightSource rightMoving
  have edgeNonzero : left.fragment.source.finish - left.fragment.source.start ≠ 0 := by
    intro zero
    have movement := Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.edge_difference left
    rw [zero, mul_zero] at movement
    exact leftMoving (Algebra.Group.eq_of_sub_eq_zero movement)
  have first := (Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.edge_difference left).symm.trans
    leftMovement
  have last := (Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.edge_difference right).symm.trans
    rightMovement
  have lastSame := (congrArg
    (fun delta : Gaussian.Basic.Canonical => (⟨right.fragment.source.last.parameter -
      right.fragment.source.first.parameter, 0⟩ : Gaussian.Basic.Canonical) * delta)
    (congrArg₂ (fun a b : Gaussian.Basic.Canonical => a - b) finishEq startEq)).trans last
  have ordered := Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.scalar_nonnegative_iff kPositive lPositive
    edgeNonzero first lastSame
  have sameOrder :
      (left.fragment.source.first.parameter ≤ left.fragment.source.last.parameter) ↔
      (right.fragment.source.first.parameter ≤ right.fragment.source.last.parameter) :=
    ⟨fun h => Fraction.Order.Boundary.sub_nonnegative_iff.mp
        (ordered.mp (Fraction.Order.Arithmetic.sub_nonneg_direct h)),
      fun h => Fraction.Order.Boundary.sub_nonnegative_iff.mp
        (ordered.mpr (Fraction.Order.Arithmetic.sub_nonneg_direct h))⟩
  change decide _ = decide _
  by_cases firstOrder : left.fragment.source.first.parameter ≤ left.fragment.source.last.parameter
  · exact (decide_eq_true firstOrder).trans (decide_eq_true (sameOrder.mp firstOrder)).symm
  · exact (decide_eq_false firstOrder).trans
      (decide_eq_false (fun lastOrder => firstOrder (sameOrder.mpr lastOrder))).symm

/-- Opposite presentations of the same containing edge select opposite
flags, as forced by their moving original source segments. -/
theorem routeForward_reverse_of_source {left right :
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains mesh source count target}
    {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    (leftSource : Paths.PreparedSegmentSources.SegmentSource segment left.parent) (rightSource :
      Paths.PreparedSegmentSources.SegmentSource segment right.parent)
    (leftMoving : left.last ≠ left.first) (rightMoving : right.last ≠ right.first)
    (startEq : left.fragment.source.start = right.fragment.source.finish)
    (finishEq : left.fragment.source.finish = right.fragment.source.start) :
      (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.routeForward left) =
      !(Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.routeForward right) := by
  obtain ⟨k, kPositive, leftMovement⟩ :=
    (Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.source_displacement left) leftSource leftMoving
  obtain ⟨l, lPositive, rightMovement⟩ :=
    (Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.source_displacement right) rightSource rightMoving
  have edgeNonzero : left.fragment.source.finish - left.fragment.source.start ≠ 0 := by
    intro zero
    have movement := Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.edge_difference left
    rw [zero, mul_zero] at movement
    exact leftMoving (Algebra.Group.eq_of_sub_eq_zero movement)
  have first := (Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.edge_difference left).symm.trans
    leftMovement
  have last : (⟨right.fragment.source.first.parameter - right.fragment.source.last.parameter, 0⟩ :
    Gaussian.Basic.Canonical) *
      (left.fragment.source.finish - left.fragment.source.start) = (⟨l, 0⟩ : Gaussian.Basic.Canonical) * (finish -
        start) := by
    rw [finishEq, startEq]
    calc
      _ = (⟨right.fragment.source.last.parameter - right.fragment.source.first.parameter, 0⟩ : Gaussian.Basic.Canonical)
        *
          (right.fragment.source.finish - right.fragment.source.start) := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.mul_re, Gaussian.Basic.mul_im,
            Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, -eq_self, -iff_self] <;> ring1
      _ = _ := (Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.edge_difference right).symm.trans
        rightMovement
  have ordered := Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.scalar_nonnegative_iff kPositive lPositive
    edgeNonzero first last
  have different : right.fragment.source.first.parameter ≠ right.fragment.source.last.parameter := by
    intro same
    have movement := Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.edge_difference right
    rw [same, sub_self] at movement
    change right.last - right.first = (0 : Gaussian.Basic.Canonical) * _ at movement
    rw [zero_mul] at movement
    exact rightMoving (Algebra.Group.eq_of_sub_eq_zero movement)
  by_cases forward : right.fragment.source.first.parameter ≤ right.fragment.source.last.parameter
  · have backward : ¬left.fragment.source.first.parameter ≤ left.fragment.source.last.parameter := by
      intro leftForward
      have reverseOrder := Fraction.Order.Boundary.sub_nonnegative_iff.mp (ordered.mp
        (Fraction.Order.Arithmetic.sub_nonneg_direct leftForward))
      exact different (le_antisymm forward reverseOrder)
    unfold Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.routeForward
    rewrite [decide_eq_false backward, decide_eq_true forward]
    rfl
  · have reverseOrder : right.fragment.source.last.parameter ≤ right.fragment.source.first.parameter :=
      (le_total _ _).resolve_left forward
    have leftForward := Fraction.Order.Boundary.sub_nonnegative_iff.mp (ordered.mpr
      (Fraction.Order.Arithmetic.sub_nonneg_direct reverseOrder))
    unfold Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.routeForward
    rewrite [decide_eq_true leftForward, decide_eq_false forward]
    rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection

variable {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational} {index : Nat}
  {budgets : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceMeshBudgets source points tolerance domains}
    {numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank source index domains}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.RootedWord

/-- The actual rooted group and original segment sources discharge the
route agreement needed by the endpoint telescope. -/
theorem source_telescope {head : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains
  mesh source count target}
    {pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains mesh source
      count target)}
    {first last : Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    (word : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.RootedWord (head :: pieces) first
      firstName last lastName)
    (original : ∀ piece ∈ head :: pieces, Paths.PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ head :: pieces, piece.last ≠ piece.first)
    (same : ∀ piece ∈ pieces, head.fragment.source.start = piece.fragment.source.start ∧
      head.fragment.source.finish = piece.fragment.source.finish)
    (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((head :: pieces).map (fun piece =>
      (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts.routeValue piece)
      (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.canonicalRoute piece) shared)) =
      (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation.canonicalPoint head) shared last -
        (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation.canonicalPoint head) shared first := by
  apply Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation.RootedWord.canonical_telescope word _ shared
  intro piece member
  have present := List.mem_cons_of_mem head member
  exact ⟨(same piece member).1, (same piece member).2,
    Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.routeForward_eq_of_source (original head
      List.mem_cons_self) (original piece present)
      (moving head List.mem_cons_self) (moving piece present) (same piece member).1 (same piece member).2⟩

/-- Once an original source group covers the complete edge, its partial
readings equal that edge's cached increment, with the displayed orientation. -/
theorem source_edge_increment {head : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes
  domains mesh source count target}
    {pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains mesh source
      count target)}
    {first last : Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    (word : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.RootedWord (head :: pieces) first
      firstName last lastName)
    (original : ∀ piece ∈ head :: pieces, Paths.PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ head :: pieces, piece.last ≠ piece.first)
    (same : ∀ piece ∈ pieces, head.fragment.source.start = piece.fragment.source.start ∧
      head.fragment.source.finish = piece.fragment.source.finish)
    (forward : Bool)
    (firstEq : first = vertices.coordinate (if forward then head.occurrence.side.edge.start else
      head.occurrence.side.edge.finish))
    (lastEq : last = vertices.coordinate (if forward then head.occurrence.side.edge.finish else
      head.occurrence.side.edge.start))
    (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((head :: pieces).map (fun piece =>
      (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts.routeValue piece)
      (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.canonicalRoute piece) shared)) =
      if forward then Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.FaceSharedMeshes.edgeIncrement shared
        (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.canonicalRoute head) else
        -Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.FaceSharedMeshes.edgeIncrement shared
        (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.canonicalRoute head) := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.RootedWord.source_telescope word original moving same
    shared, firstEq, lastEq]
  cases forward
  · change ((Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation.canonicalPoint head) shared
      (vertices.coordinate head.occurrence.side.edge.start) -
        (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation.canonicalPoint head) shared (vertices.coordinate
          head.occurrence.side.edge.finish)) =
      -((Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation.canonicalPoint head) shared (vertices.coordinate
        head.occurrence.side.edge.finish) -
        (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation.canonicalPoint head) shared (vertices.coordinate
          head.occurrence.side.edge.start))
    ring1
  · rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.RootedWord

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.Junction

/-- An adjacent pair in the actual rooted word has equal cached junction
readings when its moving pieces belong to the same original segment and
containing edge. No root-equivalence premise is left to the consumer. -/
theorem canonical_join {left right : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains
  mesh source count target}
    (joined : Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordJunctions.Junction left right)
    {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    (leftSource : Paths.PreparedSegmentSources.SegmentSource segment left.parent) (rightSource :
      Paths.PreparedSegmentSources.SegmentSource segment right.parent)
    (leftMoving : left.last ≠ left.first) (rightMoving : right.last ≠ right.first)
    (startEq : left.fragment.source.start = right.fragment.source.start)
    (finishEq : left.fragment.source.finish = right.fragment.source.finish)
    (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation.canonicalPoint left) shared left.last =
      (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation.canonicalPoint right) shared right.first :=
  (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation.canonicalPoint_eq (joined.2.2 startEq finishEq)
    (Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.routeForward_eq_of_source leftSource rightSource
      leftMoving rightMoving startEq finishEq) shared left.last).trans
      (congrArg ((Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation.canonicalPoint right) shared) joined.1)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection.Junction

end
