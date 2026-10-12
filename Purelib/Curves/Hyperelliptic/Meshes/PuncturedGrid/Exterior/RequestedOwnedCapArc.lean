module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OwnedCapArcComparison
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Tactic.Ring

public section

/-! Pay the whole-side cap comparison using the retained owner error and
the automatically selected source-run refinement. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RequestedOwnedCapArc

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OwnedCapArcComparison
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Integration.Path.JoinedTrace
open Purelib.Riemann.Periods
open Purelib.Topology.Polygon
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies (JoinedFragmentFamily)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OwnedCapArcComparison (GroupedSourceFragments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns (ResampledSourceRun)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement (sourceRunDensity
  sourceRunRefinement_accurate)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior (SourceRunRefinement)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid base} {differential other :
    Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum stage fine
    index : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other
    target minimum}

variable {evaluated :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan
  sample otherSample fine}
  {data : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index} {otherData
    : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index}

open Purelib.Integration.Path.PairedIncrementArea (area)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)

/-- The retained one-eighth owner and source allowances and one-quarter cap allowance pay the complete weighted
comparison error. -/
private theorem total_paid {owner source cap target : InverseRootPolynomial.Coordinate}
    (ownerLe : owner ≤ target / 8) (sourceLe : source ≤ target / 8) (capLe : cap ≤ target / 4) :
    2 * (owner + 2 * (source + cap / 4)) ≤ target := by
  have bound := Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ownerLe (by
          decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sourceLe (by
          decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4))) capLe
  have rearrange : 2 * (owner + 2 * (source + cap / 4)) =
      2 * owner + 4 * source + (cap / 4) * 4 := by ring1
  rw [Fraction.Field.div_mul_cancel_of_ne cap 4 (by decide)] at rearrange
  have paid : 2 * (target / 8) + 4 * (target / 8) + target / 4 = target := by
    have factor : 2 * (target / 8) + 4 * (target / 8) + target / 4 =
        (6 * (8 : InverseRootPolynomial.Coordinate)⁻¹ + (4 : InverseRootPolynomial.Coordinate)⁻¹) * target := by
      simp only [Algebra.Field.ExplicitField.div_eq_mul_inv, -eq_self, -iff_self]
      ring1
    rw [factor, show (6 : InverseRootPolynomial.Coordinate) * 8⁻¹ + 4⁻¹ = 1 by decide +kernel, Fraction.Field.one_mul]
  exact rearrange.trans_le (bound.trans_eq paid)

/-- The paid request compares the original owned sample with the literal cap arc minus its endpoint chord. Both paths
retain their actual sample owners. -/
theorem JoinedFragmentFamily.conjugate_cap_arc_requested {Vertex : Type} {count : Nat}
    {values : Vertex → Stokes.PrimitivePoint} {traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex}
    (family : FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated) (data := data) (otherData := otherData)
      values traces)
    (groups : List (OwnedCapArcComparison.GroupedSourceFragments evaluated data otherData))
    (partition : (groups.map GroupedSourceFragments.fragments).flatten = family.fragments)
    (parentOrder : groups.map GroupedSourceFragments.entry = evaluated.retained)
    {whole : JoinedTrace.VertexTrace Vertex}
    (original : CenteredBilinearPath.Sample (fun vertex => ConjugateIncrementComparison.conjugateFirst (values
      (whole.indexed vertex))))
    (traceEq : whole = VertexTrace.concatenate traces) (later : plan.parents.index ≤ stage)
    {requested : InverseRootPolynomial.Coordinate} {floor : Nat}
    (request : SourceRunRefinement plan.parents.plans.length (SourceRunRefinement.sourceRunDensity
      plan) (requested / 8) floor)
    (widths : ∀ group ∈ groups, group.width ≤ request.width)
    (refined : request.depth ≤ plan.parents.depth + fine)
    (ownerPaid : family.error ≤ requested / 8) (capPaid : target ≤ requested / 4) :
    Data.Gaussian.Norm.Basic.normSq (original.centeredArea -
      (Bilinear.arcArea
        (fun point => ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval point,
          otherSample.primitive.value.eval point⟩)
        (occurrence.piece.mesh.depth + (plan.parents.depth + fine)) occurrence.start occurrence.finish -
      Stokes.edgeArea
        (ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval occurrence.start⁻¹,
          otherSample.primitive.value.eval occurrence.start⁻¹⟩)
        (ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval occurrence.finish⁻¹,
          otherSample.primitive.value.eval occurrence.finish⁻¹⟩))) < requested := by
  have ordered : (groups.map GroupedSourceFragments.resampled).map ResampledSourceRun.entry = evaluated.retained := by
    rw [Data.List.Map.map_map]
    exact parentOrder
  have widthLe : ∀ run ∈ groups.map GroupedSourceFragments.resampled, run.width ≤ request.width := by
    intro run member
    obtain ⟨group, present, rfl⟩ := Map.mem_map.mp member
    exact widths group present
  have sourcePaid := SourceRunRefinement.sourceRunRefinement_accurate evaluated request
    (groups.map GroupedSourceFragments.resampled) ordered widthLe refined
  exact (JoinedFragmentFamily.conjugate_cap_arc_bound
    family groups partition parentOrder original traceEq later).trans_le
    (total_paid ownerPaid sourcePaid.le capPaid)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RequestedOwnedCapArc
