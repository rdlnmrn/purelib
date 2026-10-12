module
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateFragmentBlocks
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
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
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Tactic.Ring

public section

/-! Whole-side conjugate energy reaches the actual cap arc through a
geometric grouping of the retained fragments, with both finite errors kept. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OwnedCapArcComparison

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateFragmentBlocks
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries (SourceEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (OwnedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies (JoinedFragmentFamily
  fragmentSourcePath)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns (SourceFragmentChain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns (ResampledSourceRun
  conjugateSourceRunError conjugate_source_runs_arc_bound)
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

set_option genInjectivity false in
/-- A complete forward source chain of original owned fragments retaining one source entry and its actual
parameter-width bound. -/
structure GroupedSourceFragments (evaluated : PairedSourcePlan.ParentEvaluation plan sample otherSample fine)
    (data : PairedFragmentValues.FirstData occurrence index) (otherData : PairedFragmentValues.SecondData occurrence
      other index) where
  /-- The exact original source entry retained by every fragment in the group. -/ entry :
    PairedFragmentQueries.SourceEntry plan sample otherSample fine
  /-- The original owned fragments in their retained physical order. -/ fragments : List
    (PairedFragmentBlocks.OwnedFragment evaluated data otherData)
  /-- The common bound on the retained source parameter steps. -/ width : InverseRootPolynomial.Coordinate
  /-- The original fragments form a complete adjacent source chain from zero to one. -/ chain :
    SourceFragmentRuns.SourceFragmentChain entry width fragments 0 1

constructive_injectivity GroupedSourceFragments

/-- Build the source-resampling input from the group's exact retained fragment path and geometric chain. -/
@[expose] def GroupedSourceFragments.resampled (group :
  GroupedSourceFragments evaluated data
  otherData) :
    ConjugateSourceRuns.ResampledSourceRun plan sample otherSample fine :=
  ResampledSourceRun.ofFragments
    group.entry group.fragments group.width group.chain

/-- The source path of concatenated retained fragments is the concatenation of their original source paths. -/
private theorem sourcePath_append (left right : List (PairedFragmentBlocks.OwnedFragment evaluated data otherData)) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.fragmentSourcePath (left ++ right) =
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.fragmentSourcePath left ++
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.fragmentSourcePath right := by
  unfold FragmentFamilies.fragmentSourcePath
  rw [Data.List.Map.map_append, Data.List.Map.map_append, Data.List.Flatten.flatten_append]

/-- The grouped resampled conjugate paths equal the conjugation of the exact flattened original fragment source path. -/
private theorem grouped_source_path (groups : List
  (GroupedSourceFragments evaluated data
  otherData)) :
    ((groups.map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OwnedCapArcComparison.GroupedSourceFragments.resampled).map
      ResampledSourceRun.conjugatePath).flatten =
      (FragmentFamilies.fragmentSourcePath (groups.map
        GroupedSourceFragments.fragments).flatten).map
        conjugateFirst := by
  induction groups with
  | nil => rfl
  | cons group tail ih =>
    change (FragmentFamilies.fragmentSourcePath group.fragments).map ConjugateIncrementComparison.conjugateFirst ++ _ =
      (FragmentFamilies.fragmentSourcePath (group.fragments ++ (tail.map
        GroupedSourceFragments.fragments).flatten)).map
        ConjugateIncrementComparison.conjugateFirst
    rw [sourcePath_append,
      Data.List.Map.map_append, ih]

/-- All geometric groups are consumed in physical order. The source-path readback is proved from their cached fragments,
not supplied as an area claim. -/
theorem JoinedFragmentFamily.conjugate_cap_arc_bound {Vertex : Type} {count : Nat}
    {values : Vertex → Stokes.PrimitivePoint} {traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex}
    (family : FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated) (data := data) (otherData := otherData)
      values traces)
    (groups : List (GroupedSourceFragments
      evaluated data otherData))
    (partition : (groups.map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OwnedCapArcComparison.GroupedSourceFragments.fragments).flatten
      = family.fragments)
    (parentOrder : groups.map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OwnedCapArcComparison.GroupedSourceFragments.entry =
      evaluated.retained)
    {whole : JoinedTrace.VertexTrace Vertex}
    (original : CenteredBilinearPath.Sample (fun vertex => ConjugateIncrementComparison.conjugateFirst (values
      (whole.indexed vertex))))
    (traceEq : whole = VertexTrace.concatenate traces) (later : plan.parents.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (original.centeredArea -
      (Bilinear.arcArea
        (fun point => ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval point,
          otherSample.primitive.value.eval point⟩)
        (occurrence.piece.mesh.depth + (plan.parents.depth + fine)) occurrence.start occurrence.finish -
      Stokes.edgeArea
        (ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval occurrence.start⁻¹,
          otherSample.primitive.value.eval occurrence.start⁻¹⟩)
        (ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval occurrence.finish⁻¹,
          otherSample.primitive.value.eval occurrence.finish⁻¹⟩))) <
      2 * (family.error + 2 * (ConjugateSourceRuns.conjugateSourceRunError (groups.map
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OwnedCapArcComparison.GroupedSourceFragments.resampled) +
        target / 4)) := by
  have ordered : (groups.map
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OwnedCapArcComparison.GroupedSourceFragments.resampled).map
    ResampledSourceRun.entry = evaluated.retained := by
    rw [Data.List.Map.map_map]
    exact parentOrder
  have capBound := ConjugateSourceRuns.conjugate_source_runs_arc_bound evaluated (groups.map
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OwnedCapArcComparison.GroupedSourceFragments.resampled) ordered
    later
  have paths := grouped_source_path groups
  rw [partition, ← family.source_eq] at paths
  rw [paths] at capBound
  have ownerBound := JoinedFragmentFamily.conjugate_area_bound family original traceEq
  have split (a b c : InverseRootPolynomial.Gaussian) : a - c = (a - b) + (b - c) := by ring1
  rw [split _ (PairedIncrementArea.area (family.sourceIncrements.map ConjugateIncrementComparison.conjugateFirst))]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
      ((Fraction.Order.Arithmetic.add_le_add_direct ownerBound le_rfl).trans_lt
        (Fraction.Order.Arithmetic.add_lt_add_left_direct capBound _)))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OwnedCapArcComparison
