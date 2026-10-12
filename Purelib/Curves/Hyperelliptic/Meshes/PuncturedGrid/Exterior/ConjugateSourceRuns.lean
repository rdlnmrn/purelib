module
import Purelib.Data.List.Flatten
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.Group.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.ConjugateIncrementComparison
public import Purelib.Integration.Path.Dyadic.SourceListResampling
import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceResampling
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Riemann.Integration.PreparedConjugateParentCapReadback
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
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Tactic.Ring

public section

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib

/-! Assemble nonuniform source runs in the retained parent order. Exact
parent totals preserve the entire polygon while local resampling errors add. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Riemann.Normalization
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Normalization.InverseRootPolynomial.Coordinate} {minimum stage fine index :
    Nat}
  {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other target
    minimum}

open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)

set_option genInjectivity false in
/-- One complete physical source run, retaining the original primitive owner
and the parameter mesh that certifies its increments. -/
structure ResampledSourceRun (plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  occurrence other target minimum)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox) (fine : Nat) where
  /-- The original retained source entry for this complete physical run. -/ entry :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan sample otherSample fine
  /-- The actual retained parameter mesh of the run. -/ parameters : List Normalization.InverseRootPolynomial.Coordinate
  /-- The bound on every original parameter step. -/ width : Normalization.InverseRootPolynomial.Coordinate
  /-- The cached original primitive increments on the physical parameter mesh. -/ actual : List
    Topology.Polygon.Stokes.PrimitivePoint
  /-- The cached increments are exactly those computed from this original source entry and mesh. -/ actual_eq : actual =
    Path.Dyadic.SourceListResampling.increments
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues entry) 0 parameters
  /-- The retained parameters traverse the complete unit interval from zero to one. -/ chain :
    Path.Dyadic.SourceResampling.Chain 0 parameters 1
  /-- Every retained parameter step is bounded by the supplied width. -/ steps : Path.Dyadic.SourceResampling.widths 0
    parameters width

constructive_injectivity ResampledSourceRun

namespace ResampledSourceRun

/-- Conjugate the first coordinate of each actual retained source increment. -/
@[expose] def conjugatePath (run : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun
  plan sample otherSample fine) : List PrimitivePoint :=
  run.actual.map Path.ConjugateIncrementComparison.conjugateFirst

/-- Conjugate the first coordinate of the original retained parent reference increments. -/
@[expose] def referencePath (run : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun
  plan sample otherSample fine) : List PrimitivePoint :=
  run.entry.pair.1.map Path.ConjugateIncrementComparison.conjugateFirst

/-- Compute the complete local conjugate resampling error from source density, physical width and reference depth. -/
@[expose] def error (run : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun plan
  sample otherSample fine) : Coordinate :=
  16 * (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceDensity run.entry)^2 * (max run.width ((1
    / 2 : Normalization.InverseRootPolynomial.Coordinate)^(plan.parents.depth + fine)))^2

/-- The actual and original reference conjugate areas differ by at most the computed local error. -/
theorem accurate (run : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun plan sample
  otherSample fine) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area run.conjugatePath - Path.PairedIncrementArea.area
      run.referencePath) ≤ run.error :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceResampling.SourceEntry.conjugate_resampling_bound run.entry
    run.actual run.actual_eq run.chain run.steps

/-- The complete actual conjugate run has exactly its original reference parent's total increment. -/
theorem total_eq (run : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun plan sample
  otherSample fine) :
    Path.PairedIncrementArea.total run.conjugatePath = Path.PairedIncrementArea.total run.referencePath :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceResampling.SourceEntry.conjugate_resampling_total run.entry
    run.actual run.actual_eq run.chain

end ResampledSourceRun

/-- The cross-parent polygon is equal on both sides because every actual
run has the same total as its own retained reference parent. -/
theorem conjugate_source_runs_difference (runs : List
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun plan sample otherSample fine)) :
    Path.PairedIncrementArea.area (runs.map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun.conjugatePath).flatten -
      Path.PairedIncrementArea.area (runs.map
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun.referencePath).flatten =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (runs.map (fun run => Path.PairedIncrementArea.area run.conjugatePath -
      Path.PairedIncrementArea.area run.referencePath)) := by
  have totals : (runs.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun.conjugatePath).map
    Path.PairedIncrementArea.total =
      (runs.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun.referencePath).map
        Path.PairedIncrementArea.total := by
    rw [Data.List.Map.map_map, Data.List.Map.map_map]
    exact Data.List.Map.map_congr_left (fun run _ => run.total_eq)
  rw [Path.PairedAreaBlocks.area_flatten, Path.PairedAreaBlocks.area_flatten, totals,
    Algebra.Group.add_sub_add_right_eq_sub, Data.List.Map.map_map, Data.List.Map.map_map]
  exact (Purelib.Data.Gaussian.Norm.Sum.Basic.gaussianSum_map_sub runs _ _).symm

/-- Computed resampling cost uses original parent count, not the count of
fine vertices. Each local cost retains its physical width and reference depth. -/
@[expose] def conjugateSourceRunError (runs : List
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun plan sample otherSample fine)) :
  Coordinate :=
  (runs.length : Normalization.InverseRootPolynomial.Coordinate)^2 *
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun.error runs

/-- Read back all original conjugate parent references in the retained evaluation order. -/
private theorem reference_readback (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (runs : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun plan sample
      otherSample fine))
    (ordered : runs.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun.entry =
      evaluated.retained) :
    (runs.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun.referencePath).flatten
      =
      (evaluated.pairs.map Prod.fst).flatten.map conjugateFirst := by
  rw [evaluated.pairs_eq, ← ordered, Data.List.Map.map_map]
  change (runs.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun.referencePath).flatten =
    ((runs.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun.entry).map (fun entry
      => entry.pair.1)).flatten.map Path.ConjugateIncrementComparison.conjugateFirst
  rw [Data.List.Map.map_map]
  have maps : runs.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun.referencePath
    =
      (runs.map (fun run => run.entry.pair.1)).map (List.map Path.ConjugateIncrementComparison.conjugateFirst) := by
    rw [Data.List.Map.map_map]
    rfl
  rw [maps, ← Data.List.Flatten.map_flatten]
  rfl

/-- Bound the complete physical conjugate source area against the original retained parent evaluation.

Exact parent totals retain the cross-parent polygon, while the squared original run count pays the maximum local
resampling error. -/
theorem conjugate_source_runs_bound (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (runs : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun plan sample
      otherSample fine))
    (ordered : runs.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun.entry =
      evaluated.retained) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (runs.map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun.conjugatePath).flatten -
      Path.PairedIncrementArea.area ((evaluated.pairs.map Prod.fst).flatten.map
        Path.ConjugateIncrementComparison.conjugateFirst)) ≤
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.conjugateSourceRunError runs := by
  rw [← Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.reference_readback evaluated runs ordered,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.conjugate_source_runs_difference]
  have bound := Gaussian.Norm.Sum.Bounds.normSq_sum_le
    (runs.map (fun run => Path.PairedIncrementArea.area run.conjugatePath - Path.PairedIncrementArea.area
      run.referencePath))
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun.error runs) (by
      intro value member
      obtain ⟨run, present, rfl⟩ := Data.List.Map.mem_map.mp member
      exact run.accurate.trans (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum _ present))
  rw [Data.List.Map.length_map] at bound
  exact bound.trans_eq (by
      unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.conjugateSourceRunError;
      ring1)

/-- Compare the physical source runs to the actual cap arc. The endpoint
chord and both resampling and cap-comparison budgets remain explicit. -/
theorem conjugate_source_runs_arc_bound (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (runs : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun plan sample
      otherSample fine))
    (ordered : runs.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun.entry =
      evaluated.retained)
    (later : plan.parents.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (runs.map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun.conjugatePath).flatten -
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
        (fun point => Path.ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval point,
          otherSample.primitive.value.eval point⟩)
        (occurrence.piece.mesh.depth + (plan.parents.depth + fine)) occurrence.start occurrence.finish -
      Topology.Polygon.Stokes.edgeArea
        (Path.ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval occurrence.start⁻¹,
          otherSample.primitive.value.eval occurrence.start⁻¹⟩)
        (Path.ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval occurrence.finish⁻¹,
          otherSample.primitive.value.eval occurrence.finish⁻¹⟩))) <
      2 * (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.conjugateSourceRunError runs + target / 4) :=
        open Purelib.Data.Rat in by
  have first := Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.conjugate_source_runs_bound evaluated
    runs ordered
  have last := Integration.PreparedConjugateParentCapReadback.conjugate_arc_error
    occurrence evaluated later
  unfold Integration.PreparedConjugateParentCapReadback.ConjugateArcError at last
  have split (a b c : Normalization.InverseRootPolynomial.Gaussian) : a - c = (a - b) + (b - c) := by ring1
  rw [split _ (Path.PairedIncrementArea.area ((evaluated.pairs.map Prod.fst).flatten.map
    Path.ConjugateIncrementComparison.conjugateFirst))]
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
      ((Fraction.Order.Arithmetic.add_le_add_direct first le_rfl).trans_lt
        (Fraction.Order.Arithmetic.add_lt_add_left_direct last _)))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns
