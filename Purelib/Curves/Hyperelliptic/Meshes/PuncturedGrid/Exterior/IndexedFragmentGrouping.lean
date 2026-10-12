module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Topology.Polygon.Stokes

public section

/-! Group retained owned fragments by executable parent indices. Comparing
indices never requires equality tests on primitive models or proof payloads. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
open Purelib.Data.List
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (OwnedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies (fragmentSourcePath)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits (indexedEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
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

set_option genInjectivity false in
/-- An original owned fragment retaining the bounded position of its exact source parent.

The entry certificate identifies the retained source at that position; equal parent payloads at different indices remain
distinct. -/
structure IndexedOwnedFragment (evaluated : PairedSourcePlan.ParentEvaluation plan sample otherSample fine)
    (data : PairedFragmentValues.FirstData occurrence index) (otherData : PairedFragmentValues.SecondData occurrence
      other index) where
  /-- The original parent's retained bounded position in the evaluated source bank. -/ parent : Fin
    evaluated.retained.length
  /-- The actual retained owned fragment and its original numerical certificates. -/ fragment :
    PairedFragmentBlocks.OwnedFragment evaluated data otherData
  /-- The fragment's source entry is exactly the retained bank entry at its parent position. -/ entry_eq :
    fragment.entry = IndexedSourceSplits.indexedEntry evaluated parent

constructive_injectivity IndexedOwnedFragment

set_option genInjectivity false in
/-- A nonempty consecutive run of original owned fragments with one retained parent position.

The first occurrence and unchanged ordered tail each carry the exact parent-position equality, so no occurrence is
reconstructed or reordered. -/
structure IndexedOwnedRun (evaluated : PairedSourcePlan.ParentEvaluation plan sample otherSample fine)
    (data : PairedFragmentValues.FirstData occurrence index) (otherData : PairedFragmentValues.SecondData occurrence
      other index) where
  /-- The original parent's retained bounded position in the evaluated source bank. -/ parent : Fin
    evaluated.retained.length
  /-- The first original indexed fragment of this nonempty run. -/ first :
    IndexedOwnedFragment evaluated data
    otherData
  /-- The remaining original indexed fragments in their retained order. -/ rest : List
    (IndexedOwnedFragment evaluated data
    otherData)
  /-- The first fragment has the run's retained parent position. -/ first_parent : first.parent = parent
  /-- Every remaining fragment has that identical retained parent position. -/ rest_parent : ∀ item ∈ rest, item.parent
    = parent

constructive_injectivity IndexedOwnedRun

namespace IndexedOwnedRun

/-- Read the complete original indexed fragment list of the nonempty run. -/
@[expose] def items (run : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun
  evaluated data otherData) : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedFragment evaluated data
  otherData) :=
  run.first :: run.rest

/-- Read the original owned fragments in the run's retained order. -/
@[expose] def fragments (run :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun evaluated data otherData) :
  List (PairedFragmentBlocks.OwnedFragment evaluated data otherData) :=
  run.items.map Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedFragment.fragment

/-- Every original indexed fragment in the run has the run's retained parent position. -/
theorem parent_eq (run : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun
  evaluated data otherData)
    {item : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedFragment evaluated
      data otherData} (member : item ∈ run.items) : item.parent = run.parent := by
  rcases Data.List.Membership.mem_cons.mp member with rfl | member
  · exact run.first_parent
  · exact run.rest_parent item member

/-- Every original owned fragment in a run retains the exact source entry at its common parent position. -/
theorem entry_eq (run : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun
  evaluated data otherData)
    {fragment : PairedFragmentBlocks.OwnedFragment evaluated data otherData} (member : fragment ∈ run.fragments) :
    fragment.entry = IndexedSourceSplits.indexedEntry evaluated run.parent := by
  obtain ⟨item, present, rfl⟩ := Map.mem_map.mp member
  exact item.entry_eq.trans (congrArg (IndexedSourceSplits.indexedEntry evaluated) (run.parent_eq present))

/-- The supplied parent position differs from the first retained run position, when a run exists. -/
@[expose] def startsApart (parent : Fin evaluated.retained.length) : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun evaluated data otherData)
  → Prop
  | [] => True
  | run :: _ => parent ≠ run.parent

/-- Every adjacent pair of retained runs has distinct parent positions. -/
@[expose] def separated : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun evaluated data otherData)
  → Prop
  | [] => True
  | run :: rest =>
    startsApart run.parent
    rest ∧ separated
    rest

/-- Form the singleton run retaining the original indexed fragment and parent position. -/
@[expose] def single (item :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedFragment evaluated data
  otherData) : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun evaluated data
  otherData :=
  ⟨item.parent, item, [], rfl, by intro _ member; cases member⟩

/-- Prepend an original fragment to a run with the identical retained parent position. -/
@[expose] def prepend (item :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedFragment evaluated data
  otherData)
    (run : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun evaluated data
      otherData) (same : item.parent = run.parent) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun evaluated data otherData
      :=
  ⟨run.parent, item, run.items, same, fun _ member => run.parent_eq member⟩

/-- Prepend an original fragment, extending the first run exactly when its retained parent position agrees. -/
@[expose] def insert (item :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedFragment evaluated data
  otherData) :
    List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun evaluated data
      otherData) → List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun
      evaluated data otherData)
  | [] => [single item]
  | run :: rest => if same : item.parent = run.parent then
    prepend item run same ::
    rest
      else single item :: run
        :: rest

/-- Group the original indexed fragments into maximal consecutive runs by executable parent-position equality. -/
@[expose] def group : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedFragment evaluated data
  otherData) → List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun
  evaluated data otherData)
  | [] => []
  | item :: rest => insert
    item (group rest)

/-- Inserting a retained indexed fragment preserves its exact position before the original flattened runs. -/
private theorem insert_flatten (item :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedFragment evaluated data
  otherData)
    (runs : List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun evaluated
      data otherData)) :
    ((insert item runs).map
      items).flatten = item :: (runs.map items).flatten := by
  cases runs with
  | nil => rfl
  | cons run rest =>
    if same : item.parent = run.parent then
      rw [insert, dif_pos
        same]
      rfl
    else
      rw [insert, dif_neg
        same]
      rfl

/-- Flattening the grouped runs returns every original indexed fragment in its exact order. -/
theorem group_flatten (items : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedFragment evaluated data
  otherData)) :
    ((group items).map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun.items).flatten = items
      := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    exact (insert_flatten
      item (group
      rest)).trans (congrArg (List.cons item) ih)

/-- Inserting one original fragment preserves distinct parent positions between adjacent runs. -/
private theorem insert_separated (item :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedFragment evaluated data
  otherData)
    (runs : List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun evaluated
      data otherData)) (apart :
      separated runs) :
      separated
      (insert item runs) :=
      by
  cases runs with
  | nil => exact ⟨True.intro, True.intro⟩
  | cons run rest =>
    if same : item.parent = run.parent then
      rw [insert, dif_pos
        same]
      exact apart
    else
      rw [insert, dif_neg
        same]
      exact ⟨same, apart⟩

/-- Adjacent grouped runs have distinct retained parent positions. -/
theorem group_separated (items : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedFragment evaluated data
  otherData)) : separated
  (group items) := by
  induction items with
  | nil => exact True.intro
  | cons item rest ih =>
    exact insert_separated
      item (group rest) ih

/-- Reading original owned fragments commutes with flattening the retained runs. -/
private theorem fragments_flatten (runs : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun evaluated data otherData))
  :
    (runs.map
      fragments).flatten =
      ((runs.map items).flatten).map IndexedOwnedFragment.fragment := by
  induction runs with
  | nil => rfl
  | cons run rest ih =>
    change run.fragments ++ _ = (run.items ++ _).map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedFragment.fragment
    rw [Data.List.Map.map_append, ih]
    rfl

/-- Every original indexed fragment's parent position occurs as the retained parent of a run. -/
private theorem parent_present (runs : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun evaluated data otherData))
    {item : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedFragment evaluated
      data otherData} (member : item ∈ (runs.map items).flatten) :
    ∃ run ∈ runs, run.parent = item.parent := by
  induction runs with
  | nil => cases member
  | cons run rest ih =>
    rcases Data.List.Membership.mem_append.mp member with here | there
    · exact ⟨run, List.mem_cons_self, (run.parent_eq here).symm⟩
    · obtain ⟨found, present, same⟩ := ih there
      exact ⟨found, List.mem_cons_of_mem run present, same⟩

/-- Concatenating retained run source paths equals the source path of their exact flattened fragment list. -/
private theorem source_paths_flatten (runs : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun evaluated data otherData))
  :
    (runs.map (fun run => Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.fragmentSourcePath
      run.fragments)).flatten =
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.fragmentSourcePath (runs.map
        fragments).flatten :=
        by
  induction runs with
  | nil => rfl
  | cons run rest ih =>
    change FragmentFamilies.fragmentSourcePath run.fragments ++ _ = FragmentFamilies.fragmentSourcePath (run.fragments
      ++ _)
    rw [ih]
    unfold FragmentFamilies.fragmentSourcePath
    rw [Data.List.Map.map_append, Data.List.Map.map_append, Data.List.Flatten.flatten_append]

end IndexedOwnedRun

set_option genInjectivity false in
/-- The executable grouping retains every fragment occurrence and certifies maximal consecutive runs.

The cached run list flattens to the exact ordered input and has distinct adjacent parent indices. Equal parent payloads
at different indices stay distinct. -/
structure IndexedOwnedGrouping (evaluated : PairedSourcePlan.ParentEvaluation plan sample otherSample fine)
    (data : PairedFragmentValues.FirstData occurrence index) (otherData : PairedFragmentValues.SecondData occurrence
      other index)
    (items : List (IndexedOwnedFragment
      evaluated data otherData)) where
  /-- The cached maximal consecutive runs of the original indexed fragment list. -/ runs : List
    (IndexedOwnedRun evaluated data
    otherData)
  /-- Flattening the cached runs returns the exact original indexed fragment list. -/ flattened : (runs.map
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun.items).flatten = items
  /-- The cached consecutive runs have distinct retained parent positions at every junction. -/ separated :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun.separated runs

constructive_injectivity IndexedOwnedGrouping

namespace IndexedOwnedGrouping
variable {items : List
  (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedFragment evaluated
  data otherData)}

/-- Compute the maximal consecutive runs and retain exact flattening and adjacent-parent separation certificates. -/
@[expose] def build (items : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedFragment evaluated data
  otherData)) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedGrouping evaluated data
      otherData items :=
  ⟨IndexedOwnedRun.group items,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun.group_flatten items,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun.group_separated items⟩

/-- Flattening the cached run fragments preserves the original owned fragment list exactly. -/
theorem fragments_eq (grouped :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedGrouping evaluated data
  otherData items) :
    (grouped.runs.map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun.fragments).flatten =
      items.map IndexedOwnedFragment.fragment :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun.fragments_flatten
    grouped.runs).trans
    (congrArg (List.map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedFragment.fragment)
      grouped.flattened)

/-- Every original indexed fragment's parent position occurs as the retained parent of a run. -/
theorem parent_present (grouped :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedGrouping evaluated data
  otherData items)
    {item : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedFragment evaluated
      data otherData} (member : item ∈ items) :
    ∃ run ∈ grouped.runs, run.parent = item.parent := by
  rw [← grouped.flattened] at member
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun.parent_present
    grouped.runs member

/-- Regrouping preserves the full increment path, including internal area and owner junctions; endpoint totals alone are
not the readback. -/
theorem source_paths_eq (grouped :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedGrouping evaluated data
  otherData items) :
    (grouped.runs.map (fun run => FragmentFamilies.fragmentSourcePath run.fragments)).flatten =
      FragmentFamilies.fragmentSourcePath (items.map
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedFragment.fragment) :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedRun.source_paths_flatten
    grouped.runs).trans (congrArg FragmentFamilies.fragmentSourcePath grouped.fragments_eq)

end IndexedOwnedGrouping
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping

end
