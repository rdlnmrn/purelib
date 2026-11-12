module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
public import Purelib.Integration.Path.Dyadic.SourceListResampling
import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Integration.Path.DyadicConjugateIncrementComparison
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Integration.Path.Dyadic.SourceDyadicResampling
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateParentArea
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Integration.Path

public section

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib

/-! Resample a complete retained source parent onto its actual cap-reference
path. Only the finite parameter mesh changes; primitive models stay fixed. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceResampling

open Purelib.Riemann.Normalization

open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : InverseRootPolynomial.Coordinate} {minimum stage fine index :
    Nat}
  {box otherBox : Rational.Box}
  {sample : Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : PairedSourceReferences.PairedSourcePlan occurrence other target
    minimum}

/-- Conjugating the first component of each retained list increment agrees with incrementing the conjugated values. -/
private theorem conjugate_list_increments (values : InverseRootPolynomial.Coordinate →
  Topology.Polygon.Stokes.PrimitivePoint)
    (first : InverseRootPolynomial.Coordinate) (points : List
      InverseRootPolynomial.Coordinate) :
    (Dyadic.SourceListResampling.increments values first points).map
      ConjugateIncrementComparison.conjugateFirst =
      Dyadic.SourceListResampling.increments (fun parameter => ConjugateIncrementComparison.conjugateFirst
        (values parameter)) first points := by
  induction points generalizing first with
  | nil => rfl
  | cons next rest ih =>
    exact congrArg₂ List.cons (DyadicConjugateIncrementComparison.PairedIncrementArea.conjugateFirst_sub _ _) (ih
      next)

namespace SourceEntry

/-- Both retained source increments are bounded by their common slope and squared displacement throughout the unit
parameter interval. -/
private theorem unit_increment (entry : PairedFragmentQueries.SourceEntry
  plan sample otherSample fine)
    (first last : InverseRootPolynomial.Coordinate) (fl : 0 ≤ first) (fu : first ≤ 1) (ll : 0 ≤ last) (lu
      : last ≤ 1) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      ((PairedFragmentValues.sourceValues entry last).sub
        (PairedFragmentValues.sourceValues entry first))
        (PairedFragmentValues.sourceDensity entry * (last - first)^2) := by
  have left := entry.certified.source.increment_bound ⟨fl, fu⟩ ⟨ll, lu⟩
  have right := entry.certified.otherSource.increment_bound ⟨fl, fu⟩ ⟨ll, lu⟩
  exact ⟨by
      change Basic.LessEqual _ _
      have h := left.trans (Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Basic.le_max_left entry.plan.data.sourceSlope entry.plan.otherData.sourceSlope)
        (Arithmetic.sq_nonneg_direct _))
      change Basic.LessEqual _ _ at h
      simpa only [PairedFragmentValues.sourceValues,
        PairedFragmentValues.sourceDensity,
        Topology.Polygon.Stokes.PrimitivePoint.sub,
        Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using h,
    by
      change Basic.LessEqual _ _
      have h := right.trans (Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Basic.le_max_right entry.plan.data.sourceSlope entry.plan.otherData.sourceSlope)
        (Arithmetic.sq_nonneg_direct _))
      change Basic.LessEqual _ _ at h
      have recastPoint (parameter : InverseRootPolynomial.Coordinate) :
          (Integration.PreparedEdgeRecasting.recastCenteredEdge other entry.plan.parent).edge.point parameter =
            entry.plan.parent.edge.point parameter := rfl
      simpa only [PairedFragmentValues.sourceValues,
        PairedFragmentValues.sourceDensity,
        Topology.Polygon.Stokes.PrimitivePoint.sub,
        Gaussian.Norm.Basic.normSq_eq_canonical, recastPoint, -eq_self, -iff_self] using h⟩

/-- The retained first path is exactly the dyadic increment path of the original paired source values at its cached
combined depth. -/
theorem reference_path (entry : PairedFragmentQueries.SourceEntry plan
  sample otherSample fine) :
    entry.pair.1 = Dyadic.DyadicPairedPrimitivePaths.increments
      (PairedFragmentValues.sourceValues entry) (plan.parents.depth + fine)
      0 1 := by
  change entry.certified.compared.firstPath = _
  rw [Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.AreaRequest.Certified.source_path
    entry.certified, entry.depth_eq]
  rfl

/-- The bound pays both the physical mesh width and the original dyadic
reference depth, with no count of physical vertices in the coefficient. -/
theorem conjugate_resampling_bound (entry :
  PairedFragmentQueries.SourceEntry plan sample otherSample fine)
    {points : List InverseRootPolynomial.Coordinate} {width :
      InverseRootPolynomial.Coordinate}
    (actual : List Topology.Polygon.Stokes.PrimitivePoint)
    (readback : actual = Dyadic.SourceListResampling.increments
      (PairedFragmentValues.sourceValues entry) 0 points)
    (chain : Dyadic.SourceResampling.Chain 0 points 1)
    (steps : Dyadic.SourceResampling.widths 0 points width) :
    Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (actual.map
      ConjugateIncrementComparison.conjugateFirst) - PairedIncrementArea.area (entry.pair.1.map
      ConjugateIncrementComparison.conjugateFirst)) ≤
      16 * (PairedFragmentValues.sourceDensity entry)^2 * (max width ((1 / 2
        : InverseRootPolynomial.Coordinate)^(plan.parents.depth + fine)))^2 := by
  rw [readback, ConjugateSourceResampling.conjugate_list_increments,
    SourceEntry.reference_path entry,
    DyadicConjugateIncrementComparison.Bilinear.increments_conjugate]
  exact Dyadic.SourceDyadicResampling.dyadic_resampling_bound _
    (fun a b al au bl bu => ConjugateIncrementComparison.conjugateFirst_error
      (SourceEntry.unit_increment entry a b al au
      bl bu)) chain steps _

/-- Equal endpoints identify the totals exactly; internal areas still need
resampling and must not be replaced by endpoint chords. -/
theorem conjugate_resampling_total (entry :
  PairedFragmentQueries.SourceEntry plan sample otherSample fine)
    {points : List InverseRootPolynomial.Coordinate} (actual : List
      Topology.Polygon.Stokes.PrimitivePoint)
    (readback : actual = Dyadic.SourceListResampling.increments
      (PairedFragmentValues.sourceValues entry) 0 points)
    (chain : Dyadic.SourceResampling.Chain 0 points 1) :
    PairedIncrementArea.total (actual.map ConjugateIncrementComparison.conjugateFirst) =
      PairedIncrementArea.total (entry.pair.1.map ConjugateIncrementComparison.conjugateFirst) := by
  rw [DyadicConjugateIncrementComparison.PairedIncrementArea.total_conjugate,
    DyadicConjugateIncrementComparison.PairedIncrementArea.total_conjugate, readback,
    SourceEntry.reference_path entry,
    Dyadic.SourceListResampling.increments_total, Dyadic.SourceListResampling.Chain.terminal_eq chain,
    Dyadic.DyadicPairedPrimitivePaths.increments_total]

/-- A physical source run compares with the same retained parent's unsigned
cap path. Both finite errors are kept, rather than asserting source-area decay. -/
theorem conjugate_cap_resampling_bound (evaluated :
  PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (entry : PairedFragmentQueries.SourceEntry plan sample otherSample fine)
      (member : entry ∈ evaluated.retained)
    (later : plan.parents.index ≤ stage)
    {points : List InverseRootPolynomial.Coordinate} {width :
      InverseRootPolynomial.Coordinate} (actual : List Topology.Polygon.Stokes.PrimitivePoint)
    (readback : actual = Dyadic.SourceListResampling.increments
      (PairedFragmentValues.sourceValues entry) 0 points)
    (chain : Dyadic.SourceResampling.Chain 0 points 1)
    (steps : Dyadic.SourceResampling.widths 0 points width) :
    Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (actual.map
      ConjugateIncrementComparison.conjugateFirst) - PairedIncrementArea.area (entry.pair.2.map
      ConjugateIncrementComparison.conjugateFirst)) <
      2 * (16 * (PairedFragmentValues.sourceDensity entry)^2 * (max width
        ((1 / 2 : InverseRootPolynomial.Coordinate)^(plan.parents.depth + fine)))^2 +
        plan.parents.allowance) := by
  have present : entry.plan ∈ plan.parents.plans :=
    Eq.mp (congrArg (fun plans => entry.plan ∈ plans) evaluated.plans_eq)
      (List.Map.mem_map_of_mem (f := fun entry => entry.plan) member)
  have resampled :=
    SourceEntry.conjugate_resampling_bound entry
    actual readback chain steps
  have capBound := Charts.Reciprocal.Disk.ConjugateParentArea.Entry.conjugate_accurate entry present later
  have split : PairedIncrementArea.area (actual.map ConjugateIncrementComparison.conjugateFirst) -
    PairedIncrementArea.area (entry.pair.2.map ConjugateIncrementComparison.conjugateFirst) =
      (PairedIncrementArea.area (actual.map ConjugateIncrementComparison.conjugateFirst) -
        PairedIncrementArea.area (entry.pair.1.map ConjugateIncrementComparison.conjugateFirst)) +
        (PairedIncrementArea.area (entry.pair.1.map ConjugateIncrementComparison.conjugateFirst) -
          PairedIncrementArea.area (entry.pair.2.map ConjugateIncrementComparison.conjugateFirst)) := by ring1
  rw [split]
  have sumBound := (Arithmetic.add_le_add_direct resampled le_rfl).trans_lt
    (Arithmetic.add_lt_add_left_direct capBound _)
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt (Arithmetic.mul_lt_mul_of_pos_left_direct
    (by decide) sumBound)

end SourceEntry
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceResampling
