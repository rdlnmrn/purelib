module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.CenteredPathIncrements
public import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.DyadicConjugateIncrementComparison
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.PairedBlockComparison
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Polynomial.Rectangle.JoinedSampleBlocks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateOwnedFragments
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Surface.Cut.PrimitiveJumps

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
open Purelib.Data.List
open Purelib.Integration.Path
open Purelib.Integration.Path.DyadicConjugateIncrementComparison
open Purelib.Integration.Path.JoinedTrace
open Purelib.Integration.Polynomial.Rectangle
open Purelib.Riemann.Periods
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Topology.Polygon

/-! Conjugate energy on the retained nonuniform fragment lists, including
all cross-fragment endpoint terms. No primitive readings are recomputed. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateFragmentBlocks
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData sourceValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (OwnedFragment fragmentBlockError
  fragmentLocalTolerance fragmentBlockError_lt maximum_nonnegative le_maximum)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments (ownedValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateOwnedFragments
  (conjugate_owned_fragment_area_bound)
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

open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst conjugateFirst_error conjugateFirst_bounded)
open Purelib.Integration.Path.DyadicConjugateIncrementComparison.PairedIncrementArea (conjugateFirst_sub
  total_conjugate)

/-- Conjugating the first coordinate commutes with the original centered sample's increment list. -/
private theorem conjugate_sample_increments {count : Nat}
    {values : Fin (count + 1) → Stokes.PrimitivePoint} (original : CenteredBilinearPath.Sample values)
    (changed : CenteredBilinearPath.Sample (fun vertex => ConjugateIncrementComparison.conjugateFirst (values vertex)))
      :
    (CenteredPathIncrements.Sample.increments original).map ConjugateIncrementComparison.conjugateFirst =
      (CenteredPathIncrements.Sample.increments changed) := by
  rw [CenteredPathIncrements.Sample.increments_raw original, CenteredPathIncrements.Sample.increments_raw changed]
  unfold CenteredPathIncrements.increments
  rw [OfFn.Basic.map_ofFn]
  apply OfFn.Basic.ofFn_congr
  intro edge
  exact PairedIncrementArea.conjugateFirst_sub _ _

namespace OwnedFragment
variable {evaluated :
  ParentEvaluation
  plan sample otherSample fine}
  {data : FirstData occurrence index}
    {otherData : SecondData occurrence
    other index}

/-- Transform the retained increment lists, preserving each owner junction. -/
@[expose] def conjugatePair (fragment : PairedFragmentBlocks.OwnedFragment evaluated data otherData) :
    List Stokes.PrimitivePoint × List PrimitivePoint :=
  ((CenteredPathIncrements.Sample.increments fragment.owned).map ConjugateIncrementComparison.conjugateFirst,
    (CenteredPathIncrements.Sample.increments fragment.source).map ConjugateIncrementComparison.conjugateFirst)

/-- The conjugated original owned and source fragment areas satisfy the retained area-error bound. -/
theorem conjugate_area_accurate (fragment : PairedFragmentBlocks.OwnedFragment evaluated data otherData) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area
      (conjugatePair
      fragment).1 -
      PairedIncrementArea.area
        (conjugatePair
        fragment).2) ≤ fragment.areaError := by
  let owned := CenteredBilinearPath.Sample.build (fun vertex => ConjugateIncrementComparison.conjugateFirst
    (PairedOwnedFragments.ownedValues fragment.first fragment.second vertex))
  let source := CenteredBilinearPath.Sample.build (fun vertex => ConjugateIncrementComparison.conjugateFirst
    (PairedFragmentValues.sourceValues fragment.entry (fragment.parameters vertex)))
  change Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area ((CenteredPathIncrements.Sample.increments
    fragment.owned).map ConjugateIncrementComparison.conjugateFirst) -
    PairedIncrementArea.area ((CenteredPathIncrements.Sample.increments fragment.source).map
      ConjugateIncrementComparison.conjugateFirst)) ≤ _
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateFragmentBlocks.conjugate_sample_increments
    fragment.owned owned,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateFragmentBlocks.conjugate_sample_increments
    fragment.source source,
    CenteredPathIncrements.Sample.increments_area owned, CenteredPathIncrements.Sample.increments_area source]
  exact ConjugateOwnedFragments.conjugate_owned_fragment_area_bound evaluated fragment.entry fragment.member
    fragment.piece data otherData
    fragment.parameters fragment.inside fragment.forward fragment.ordered fragment.budget fragment.owners fragment.later
    fragment.first fragment.second owned source

/-- The conjugated original fragment displacement difference satisfies the retained total-error bound. -/
theorem conjugate_total_accurate (fragment : PairedFragmentBlocks.OwnedFragment evaluated data otherData) :
    PrimitivePoint.Bounded
      ((PairedIncrementArea.total
        (conjugatePair
        fragment).1).sub
        (PairedIncrementArea.total
          (conjugatePair
          fragment).2)) fragment.totalError := by
  change PrimitivePoint.Bounded
    ((PairedIncrementArea.total ((CenteredPathIncrements.Sample.increments fragment.owned).map
      ConjugateIncrementComparison.conjugateFirst)).sub
      (PairedIncrementArea.total ((CenteredPathIncrements.Sample.increments fragment.source).map
        ConjugateIncrementComparison.conjugateFirst))) _
  rw [PairedIncrementArea.total_conjugate, PairedIncrementArea.total_conjugate]
  exact ConjugateIncrementComparison.conjugateFirst_error (OwnedFragment.total_accurate fragment)

/-- The conjugated original owned fragment displacement satisfies its retained magnitude bound. -/
theorem conjugate_owned_bounded (fragment : PairedFragmentBlocks.OwnedFragment evaluated data otherData) :
    PrimitivePoint.Bounded
      (PairedIncrementArea.total
        (conjugatePair
        fragment).1) fragment.totalBound := by
  change PrimitivePoint.Bounded
    (PairedIncrementArea.total ((CenteredPathIncrements.Sample.increments fragment.owned).map
      ConjugateIncrementComparison.conjugateFirst)) _
  rw [PairedIncrementArea.total_conjugate]
  exact ConjugateIncrementComparison.conjugateFirst_bounded (OwnedFragment.owned_bounded fragment)

/-- The conjugated original source fragment displacement satisfies its retained magnitude bound. -/
theorem conjugate_source_bounded (fragment : PairedFragmentBlocks.OwnedFragment evaluated data otherData) :
    PrimitivePoint.Bounded
      (PairedIncrementArea.total
        (conjugatePair
        fragment).2) fragment.totalBound := by
  change PrimitivePoint.Bounded
    (PairedIncrementArea.total ((CenteredPathIncrements.Sample.increments fragment.source).map
      ConjugateIncrementComparison.conjugateFirst)) _
  rw [PairedIncrementArea.total_conjugate]
  exact ConjugateIncrementComparison.conjugateFirst_bounded (OwnedFragment.source_bounded_total fragment)

end OwnedFragment

/-- Full flattened path comparison, including its cross-fragment polygon. The finite maxima are computed from the proved
local bounds; no analytic estimate or equality of differently owned endpoints is an input. -/
theorem conjugate_owned_fragments_area_bound {evaluated : PairedSourcePlan.ParentEvaluation plan sample otherSample
  fine}
    {data : PairedFragmentValues.FirstData occurrence index} {otherData : PairedFragmentValues.SecondData occurrence
      other index}
    (fragments : List (PairedFragmentBlocks.OwnedFragment evaluated data otherData)) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area ((fragments.map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateFragmentBlocks.OwnedFragment.conjugatePair).map
      Prod.fst).flatten -
      PairedIncrementArea.area ((fragments.map
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateFragmentBlocks.OwnedFragment.conjugatePair).map
        Prod.snd).flatten) ≤
      PairedFragmentBlocks.fragmentBlockError fragments := by
  have estimate := PairedBlockComparison.blocks_area_difference_bound (fragments.map
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateFragmentBlocks.OwnedFragment.conjugatePair)
    (PairedFragmentBlocks.maximum_nonnegative OwnedFragment.totalError fragments)
      (PairedFragmentBlocks.maximum_nonnegative OwnedFragment.totalBound fragments)
    (by
      intro pair member
      obtain ⟨fragment, present, rfl⟩ := Map.mem_map.mp member
      exact
        (OwnedFragment.conjugate_area_accurate
        fragment).trans (PairedFragmentBlocks.le_maximum _ present))
    (by
      intro pair member
      obtain ⟨fragment, present, rfl⟩ := Map.mem_map.mp member
      exact
        ⟨(OwnedFragment.conjugate_total_accurate
        fragment).1.trans (PairedFragmentBlocks.le_maximum _ present),
        (OwnedFragment.conjugate_total_accurate
        fragment).2.trans (PairedFragmentBlocks.le_maximum _ present)⟩)
    (by
      intro pair member
      obtain ⟨fragment, present, rfl⟩ := Map.mem_map.mp member
      exact
        ⟨(OwnedFragment.conjugate_owned_bounded
        fragment).1.trans (PairedFragmentBlocks.le_maximum _ present),
        (OwnedFragment.conjugate_owned_bounded
        fragment).2.trans (PairedFragmentBlocks.le_maximum _ present)⟩)
    (by
      intro pair member
      obtain ⟨fragment, present, rfl⟩ := Map.mem_map.mp member
      exact
        ⟨(OwnedFragment.conjugate_source_bounded
        fragment).1.trans (PairedFragmentBlocks.le_maximum _ present),
        (OwnedFragment.conjugate_source_bounded
        fragment).2.trans (PairedFragmentBlocks.le_maximum _ present)⟩)
  rwa [Data.List.Map.length_map] at estimate

/-- The existing local allocation pays the conjugate full-path error too. -/
theorem conjugate_owned_fragments_area_lt {evaluated : PairedSourcePlan.ParentEvaluation plan sample otherSample fine}
    {data : PairedFragmentValues.FirstData occurrence index} {otherData : PairedFragmentValues.SecondData occurrence
      other index}
    (fragments : List (PairedFragmentBlocks.OwnedFragment evaluated data otherData)) {bound target :
      InverseRootPolynomial.Coordinate}
    (nonnegative : 0 ≤ bound) (positive : 0 < target)
    (areas : ∀ fragment ∈ fragments, fragment.areaError ≤ PairedFragmentBlocks.fragmentLocalTolerance fragments.length
      bound target)
    (errors : ∀ fragment ∈ fragments, fragment.totalError ≤ PairedFragmentBlocks.fragmentLocalTolerance fragments.length
      bound target)
    (totals : ∀ fragment ∈ fragments, fragment.totalBound ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area ((fragments.map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateFragmentBlocks.OwnedFragment.conjugatePair).map
      Prod.fst).flatten -
      PairedIncrementArea.area ((fragments.map
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateFragmentBlocks.OwnedFragment.conjugatePair).map
        Prod.snd).flatten) < target :=
  (conjugate_owned_fragments_area_bound
    fragments).trans_lt
    (PairedFragmentBlocks.fragmentBlockError_lt fragments nonnegative positive areas errors totals)

/-- Conjugating every retained fragment pair gives the conjugation of the complete original owned and source increment
lists. -/
private theorem conjugate_blocks {evaluated : PairedSourcePlan.ParentEvaluation plan sample otherSample fine}
    {data : PairedFragmentValues.FirstData occurrence index} {otherData : PairedFragmentValues.SecondData occurrence
      other index}
    (fragments : List (PairedFragmentBlocks.OwnedFragment evaluated data otherData)) :
    ((fragments.map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateFragmentBlocks.OwnedFragment.conjugatePair).map
      Prod.fst).flatten =
      (((fragments.map OwnedFragment.pair).map Prod.fst).flatten).map ConjugateIncrementComparison.conjugateFirst ∧
    ((fragments.map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateFragmentBlocks.OwnedFragment.conjugatePair).map
      Prod.snd).flatten =
      (FragmentFamilies.fragmentSourcePath fragments).map conjugateFirst := by
  induction fragments with
  | nil => exact ⟨rfl, rfl⟩
  | cons fragment rest ih =>
    constructor
    · change (CenteredPathIncrements.Sample.increments fragment.owned).map ConjugateIncrementComparison.conjugateFirst
        ++ _ =
        ((CenteredPathIncrements.Sample.increments fragment.owned) ++ _).map ConjugateIncrementComparison.conjugateFirst
      rw [Data.List.Map.map_append, ih.1]
    · change (CenteredPathIncrements.Sample.increments fragment.source).map ConjugateIncrementComparison.conjugateFirst
        ++ _ =
        ((CenteredPathIncrements.Sample.increments fragment.source) ++ _).map
          ConjugateIncrementComparison.conjugateFirst
      rw [Data.List.Map.map_append, ih.2]
      rfl

/-- Compare the actual whole-side conjugate sample with the retained source path. The intervening owner junctions and
complete polygon are preserved. -/
theorem JoinedFragmentFamily.conjugate_area_bound
    {evaluated : PairedSourcePlan.ParentEvaluation plan sample otherSample fine}
    {data : PairedFragmentValues.FirstData occurrence index} {otherData : PairedFragmentValues.SecondData occurrence
      other index}
    {Vertex : Type} {count : Nat}
    {values : Vertex → Stokes.PrimitivePoint}
    {traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex}
    (family : FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated) (data := data) (otherData := otherData)
      values traces)
    {whole : JoinedTrace.VertexTrace Vertex}
    (original : CenteredBilinearPath.Sample (fun vertex => ConjugateIncrementComparison.conjugateFirst (values
      (whole.indexed vertex))))
    (traceEq : whole = VertexTrace.concatenate traces) :
    Data.Gaussian.Norm.Basic.normSq (original.centeredArea - PairedIncrementArea.area
      (family.sourceIncrements.map ConjugateIncrementComparison.conjugateFirst)) ≤ family.error := by
  let raw := CenteredBilinearPath.Sample.build (fun vertex => values (whole.indexed vertex))
  have bound :=
    conjugate_owned_fragments_area_bound
    family.fragments
  have blocks := conjugate_blocks
    family.fragments
  rw [blocks.1, blocks.2, ← family.source_eq] at bound
  have owned := JoinedFragmentComparison.interleave_owned values traces (fun position => family.pieces.get position)
    (fun position => family.junctions.get position)
  have joined : ((family.fragments.map OwnedFragment.pair).map Prod.fst).flatten =
    (CenteredPathIncrements.Sample.increments raw) := by
    rw [family.fragments_eq]
    change (((JoinedFragmentComparison.interleaveFragments _ _).map OwnedFragment.pair).map Prod.fst).flatten =
      (CenteredPathIncrements.Sample.increments raw)
    rw [owned]
    exact JoinedSampleBlocks.sampledBlocks_flatten values traces _ _ raw traceEq
  rw [joined, conjugate_sample_increments raw
    original, CenteredPathIncrements.Sample.increments_area original] at bound
  exact bound.trans_eq family.error_eq.symm

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateFragmentBlocks
