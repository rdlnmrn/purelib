module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Reverse
import Purelib.Data.List.Flatten
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
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
import Purelib.Integration.Path.PairedAreaReversal
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentRuns
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

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateFragmentBlocks
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentRuns
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Integration.Path.JoinedTrace
open Purelib.Riemann.Periods
open Purelib.Topology.Polygon

/-! Reversed complete side comparisons preserve the entire parent polygon. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseOwnedCapArc
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentRuns (ReverseSourceFragmentChain)
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
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Coordinate} {minimum
    stage fine index : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : PairedSourcePlan occurrence
    other target minimum}

variable {evaluated :
  ParentEvaluation
  plan sample otherSample fine}
  {data : FirstData occurrence index}
    {otherData : SecondData occurrence
    other index}

open Purelib.Integration.Path.PairedIncrementArea (area)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)

set_option genInjectivity false in
/-- One complete descending physical run on its original source parent. -/
structure ReverseGroupedSourceFragments (evaluated : PairedSourcePlan.ParentEvaluation plan sample otherSample fine)
    (data : PairedFragmentValues.FirstData occurrence index) (otherData : PairedFragmentValues.SecondData occurrence
      other index) where
  /-- The exact original source entry retained by every fragment of this descending group. -/ entry :
    PairedFragmentQueries.SourceEntry plan sample otherSample fine
  /-- The actual retained descending physical fragments in their original order. -/ fragments : List
    (PairedFragmentBlocks.OwnedFragment evaluated data otherData)
  /-- The common upper bound on the original descending source parameter steps. -/ width :
    InverseRootPolynomial.Coordinate
  /-- The retained fragments form a complete descending chain on the identical source entry from one to zero. -/ chain :
    ReverseFragmentRuns.ReverseSourceFragmentChain entry width fragments 1 0

constructive_injectivity ReverseGroupedSourceFragments

/-- Reuse the original descending fragments as an ascending resampling input by reversing their complete cached source
increments. -/
@[expose] def ReverseGroupedSourceFragments.resampled (group :
  ReverseGroupedSourceFragments evaluated data
  otherData) :
    ConjugateSourceRuns.ResampledSourceRun plan sample otherSample fine :=
  ResampledSourceRun.ofReverseFragments group.entry group.fragments group.width group.chain

/-- The source path of concatenated original fragments equals the concatenation of their retained source paths. -/
private theorem sourcePath_append (left right : List (PairedFragmentBlocks.OwnedFragment evaluated data otherData)) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.fragmentSourcePath (left ++ right) =
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.fragmentSourcePath left ++
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.fragmentSourcePath right := by
  unfold FragmentFamilies.fragmentSourcePath
  rw [Data.List.Map.map_append, Data.List.Map.map_append, Data.List.Flatten.flatten_append]

/-- Reverse the order of the runs as well as every run's increments. This retains the cross-parent polygon in the exact
full-path identity. -/
theorem ReverseGroupedSourceFragments.source_path (groups : List
  (ReverseGroupedSourceFragments evaluated data
  otherData)) :
    ((groups.reverse.map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseOwnedCapArc.ReverseGroupedSourceFragments.resampled).map
      ResampledSourceRun.conjugatePath).flatten =
      (PairedAreaReversal.reverseIncrements
        (FragmentFamilies.fragmentSourcePath (groups.map
          ReverseGroupedSourceFragments.fragments).flatten)).map
          conjugateFirst := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
    rw [Data.List.Reverse.reverse_cons, Data.List.Map.map_append, Data.List.Map.map_append,
      Data.List.Flatten.flatten_append, ih]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, Data.List.Append.append_nil, -eq_self,
      -iff_self]
    change _ ++ (PairedAreaReversal.reverseIncrements (FragmentFamilies.fragmentSourcePath group.fragments)).map
      ConjugateIncrementComparison.conjugateFirst =
      (PairedAreaReversal.reverseIncrements
        (FragmentFamilies.fragmentSourcePath (group.fragments ++ (rest.map
          ReverseGroupedSourceFragments.fragments).flatten))).map
          ConjugateIncrementComparison.conjugateFirst
    rw [sourcePath_append,
      PairedAreaReversal.reverseIncrements_append, Data.List.Map.map_append]

/-- The retained descending physical area approximates the negative original conjugate cap arc minus its endpoint chord.

The complete reversed parent order and exact fragment partition retain the owner, resampling and cap errors separately.
-/
theorem JoinedFragmentFamily.reverse_conjugate_cap_arc_bound {Vertex : Type} {count : Nat}
    {values : Vertex → Stokes.PrimitivePoint} {traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex}
    (family : FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated) (data := data) (otherData := otherData)
      values traces)
    (groups : List (ReverseGroupedSourceFragments
      evaluated data otherData))
    (partition : (groups.map
      ReverseGroupedSourceFragments.fragments).flatten
      = family.fragments)
    (parentOrder : groups.reverse.map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseOwnedCapArc.ReverseGroupedSourceFragments.entry =
      evaluated.retained)
    {whole : JoinedTrace.VertexTrace Vertex}
    (original : CenteredBilinearPath.Sample (fun vertex => ConjugateIncrementComparison.conjugateFirst (values
      (whole.indexed vertex))))
    (traceEq : whole = VertexTrace.concatenate traces) (later : plan.parents.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (original.centeredArea +
      (Bilinear.arcArea
        (fun point => ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval point,
          otherSample.primitive.value.eval point⟩)
        (occurrence.piece.mesh.depth + (plan.parents.depth + fine)) occurrence.start occurrence.finish -
      Stokes.edgeArea
        (ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval occurrence.start⁻¹,
          otherSample.primitive.value.eval occurrence.start⁻¹⟩)
        (ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval occurrence.finish⁻¹,
          otherSample.primitive.value.eval occurrence.finish⁻¹⟩))) <
      2 * (family.error + 2 * (ConjugateSourceRuns.conjugateSourceRunError (groups.reverse.map
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseOwnedCapArc.ReverseGroupedSourceFragments.resampled) +
        target / 4)) := by
  have ordered : (groups.reverse.map
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseOwnedCapArc.ReverseGroupedSourceFragments.resampled).map
    ResampledSourceRun.entry = evaluated.retained := by
    rw [Data.List.Map.map_map]
    exact parentOrder
  have capBound := ConjugateSourceRuns.conjugate_source_runs_arc_bound evaluated
    (groups.reverse.map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseOwnedCapArc.ReverseGroupedSourceFragments.resampled)
      ordered later
  have paths :=
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseOwnedCapArc.ReverseGroupedSourceFragments.source_path
    groups
  rw [partition, ← family.source_eq] at paths
  rw [paths, PairedAreaReversal.conjugate_area_reverseIncrements] at capBound
  have negative (a b : InverseRootPolynomial.Gaussian) : -a - b = -(a + b) := by ring1
  rw [negative, Data.Gaussian.Norm.Basic.normSq_neg] at capBound
  have ownerBound := JoinedFragmentFamily.conjugate_area_bound
    family original traceEq
  have split (a b c : InverseRootPolynomial.Gaussian) : a + c = (a - b) + (b + c) := by ring1
  rw [split _ (PairedIncrementArea.area (family.sourceIncrements.map ConjugateIncrementComparison.conjugateFirst))]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
      ((Fraction.Order.Arithmetic.add_le_add_direct ownerBound le_rfl).trans_lt
        (Fraction.Order.Arithmetic.add_lt_add_left_direct capBound _)))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseOwnedCapArc
