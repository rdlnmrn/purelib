module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
import Init.Data.List.Lemmas
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Topology.Polygon.Stokes

public section

/-! Group common-basis fragments without changing their retained paths. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
open Purelib
open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation (CommonBasisPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices (parentIndex parentIndex_read
  occurrenceAt)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks (ParentBlock cacheParent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection (SelectedInput)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (NumericalBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments (OwnedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries (RowData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks (BlockSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments (IndexedFragment ParentFragment)
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted
    differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

variable (retained : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation
  prepared) {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length) {faceIndex : Nat}
  (data : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) faceIndex)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

set_option genInjectivity false in
/-- A nonempty consecutive fragment run retaining one original parent position and the exact indexed fragments belonging
to it.

The bounded parent position is shared by the first fragment and each retained tail member. The nonempty run preserves
their order and their source-indexed cached fragments. -/
structure IndexedRun where
  /-- The run's original bounded parent position. -/ parent : Fin (ParentIndices.occurrenceAt prepared.occurrences
    outer).compared.entered.cache.parents.length
  /-- The first original indexed fragment of the nonempty run. -/ first : IndexedFragments.IndexedFragment retained
    inputs outer data coefficients
  /-- The remaining original indexed fragments in their retained order. -/ rest : List (IndexedFragments.IndexedFragment
    retained inputs outer data coefficients)
  /-- The first fragment retains the run's original parent position. -/ first_parent : first.parent = parent
  /-- Every remaining original fragment retains that identical parent position. -/ rest_parent : ∀ item ∈ rest,
    item.parent = parent

constructive_injectivity IndexedRun

variable {retained inputs outer data coefficients}
namespace IndexedRun

/-- Read all original indexed fragments of the retained nonempty run.

The first fragment precedes the retained tail without rebuilding any fragment or changing its parent certificate. -/
@[expose] def items (run : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun retained
  inputs outer data coefficients) : List (IndexedFragments.IndexedFragment retained inputs outer data coefficients) :=
  run.first :: run.rest

/-- Every indexed fragment in the run retains its certified original parent position.

Membership is decomposed at the retained head or tail. The corresponding stored parent certificate supplies the
identical bounded parent position. -/
theorem parent_eq (run : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun retained
  inputs outer data coefficients)
    {item : IndexedFragments.IndexedFragment retained inputs outer data coefficients} (member : item ∈ run.items) :
      item.parent = run.parent := by
  rcases Membership.mem_cons.mp member with rfl | member
  · exact run.first_parent
  · exact run.rest_parent item member

/-- The supplied parent position differs from the first retained run's position, when present.

The empty list has no adjacent boundary; a nonempty list compares only its first retained parent with the supplied
position. -/
@[expose] def startsApart (parent : Fin (ParentIndices.occurrenceAt prepared.occurrences
  outer).compared.entered.cache.parents.length) : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun retained inputs outer data
  coefficients) → Prop
  | [] => True
  | run :: _ => parent ≠ run.parent

/-- Every pair of adjacent retained runs has distinct original parent positions.

Each consecutive boundary carries the inequality of its two bounded parent positions. The remaining boundaries follow
the retained list tail. -/
@[expose] def separated : List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun
  retained inputs outer data coefficients) → Prop
  | [] => True
  | run :: rest => Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.startsApart
    run.parent rest ∧
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.separated rest

/-- Form a singleton run retaining the original indexed fragment and parent position.

The supplied fragment supplies both the retained parent and the first run member. The tail is empty and its parent
condition is vacuous. -/
@[expose] def single (item : IndexedFragments.IndexedFragment retained inputs outer data coefficients) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun retained inputs outer data
  coefficients :=
  ⟨item.parent, item, [], rfl, by intro _ member; cases member⟩

/-- Prepend an original indexed fragment to a run with the identical retained parent position.

The supplied parent equality transports only the parent certificate. The previous run items remain the new retained tail
in the same order. -/
@[expose] def prepend (item : IndexedFragments.IndexedFragment retained inputs outer data coefficients)
    (run : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun retained inputs outer
      data coefficients) (same : item.parent = run.parent) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun retained inputs outer data
      coefficients :=
  ⟨run.parent, item, run.items, same, fun _ member => run.parent_eq member⟩

/-- Prepend the original indexed fragment, extending the first run precisely when its retained parent position agrees.

The first run is extended exactly when its bounded parent agrees with the supplied fragment. Otherwise a singleton run
is placed before the unchanged run list. -/
@[expose] def insert (item : IndexedFragments.IndexedFragment retained inputs outer data coefficients) :
    List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun retained inputs outer
      data coefficients) → List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun
      retained inputs outer data coefficients)
  | [] => [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.single item]
  | run :: rest => if same : item.parent = run.parent then
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.prepend item run same :: rest
      else Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.single item :: run ::
        rest

/-- Group the original indexed fragments into maximal consecutive runs by executable parent-position equality.

The retained suffix is grouped before inserting its head. The executable equality test keeps every fragment in its
supplied order. -/
@[expose] def group : List (IndexedFragments.IndexedFragment retained inputs outer data coefficients) → List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun retained inputs outer data
  coefficients)
  | [] => []
  | item :: rest => Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.insert item
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.group rest)

/-- Inserting an indexed fragment preserves its exact position before the original flattened run list.

Both results of the parent equality test retain the inserted head before the unchanged flattened suffix. -/
private theorem insert_flatten (item : IndexedFragments.IndexedFragment retained inputs outer data coefficients)
    (runs : List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun retained inputs
      outer data coefficients)) :
    ((Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.insert item runs).map
      items).flatten = item :: (runs.map items).flatten := by
  cases runs with
  | nil => rfl
  | cons run rest =>
    if same : item.parent = run.parent then
      rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.insert, dif_pos same]
      rfl
    else
      rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.insert, dif_neg same]
      rfl

/-- Flattening the grouped runs returns every original indexed fragment in exact order.

Structural induction follows the original fragment list. Each insertion preserves its head before the identical
flattened tail. -/
theorem group_flatten (items : List (IndexedFragments.IndexedFragment retained inputs outer data coefficients)) :
    ((Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.group items).map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.items).flatten = items := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    exact (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.insert_flatten item
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.group rest)).trans (congrArg
      (List.cons item) ih)

/-- Inserting an original indexed fragment preserves distinct parent positions between adjacent runs.

Extending an equal-parent run keeps its old boundary certificate. Creating a singleton run supplies the new parent
inequality before the unchanged boundaries. -/
private theorem insert_separated (item : IndexedFragments.IndexedFragment retained inputs outer data coefficients)
    (runs : List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun retained inputs
      outer data coefficients)) (apart :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.separated runs) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.separated
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.insert item runs) := by
  cases runs with
  | nil => exact ⟨True.intro, True.intro⟩
  | cons run rest =>
    if same : item.parent = run.parent then
      rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.insert, dif_pos same]
      exact apart
    else
      rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.insert, dif_neg same]
      exact ⟨same, apart⟩

/-- Adjacent grouped fragment runs have distinct retained parent positions.

Each recursive insertion retains the separation certificates of the suffix and supplies any new adjacent boundary
inequality. -/
theorem group_separated (items : List (IndexedFragments.IndexedFragment retained inputs outer data coefficients)) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.separated
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.group items) := by
  induction items with
  | nil => exact True.intro
  | cons item rest ih =>
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.insert_separated item
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.group rest) ih

/-- Transport a list to its shared numerical owner, preserving all cached data.

The supplied parent equalities transport the retained fragments one at a time. Their cached values, source owners and
order are unchanged. -/
@[expose] def fragmentsAt (parent : Fin (ParentIndices.occurrenceAt prepared.occurrences
  outer).compared.entered.cache.parents.length) :
    (items : List (IndexedFragments.IndexedFragment retained inputs outer data coefficients)) →
    (∀ item ∈ items, item.parent = parent) → List (IndexedFragments.ParentFragment retained inputs outer data
      coefficients parent)
  | [], _ => []
  | item :: rest, same => item.fragment.castParent (same item List.mem_cons_self) ::
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.fragmentsAt parent
        rest (fun found member => same found (List.mem_cons_of_mem item member))

/-- Transporting fragments to the identical retained parent preserves their exact physical/source increment pairs.

Parent transport retains each physical and source increment pair. Scalar head congruence preserves the unchanged
transported tail. -/
theorem fragmentsAt_pairs (parent : Fin (ParentIndices.occurrenceAt prepared.occurrences
  outer).compared.entered.cache.parents.length)
    (items : List (IndexedFragments.IndexedFragment retained inputs outer data coefficients))
    (same : ∀ item ∈ items, item.parent = parent) :
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.fragmentsAt parent items
      same).map OwnedFragment.pair = items.map IndexedFragment.pair := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    exact congrArg₂ List.cons (ParentFragment.castParent_pair _ item.fragment) (ih _)

/-- Transport the original run fragments to their shared retained parent without replacing cached values or samples.

The run's stored parent certificates transport its existing items to the one bounded parent position without recomputing
their samples. -/
@[expose] def fragments (run : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun
  retained inputs outer data coefficients) :
    List (IndexedFragments.ParentFragment retained inputs outer data coefficients run.parent) :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.fragmentsAt run.parent run.items
    (fun _ member => run.parent_eq member)

/-- The retained parent-transported run has exactly the original indexed increment pairs.

Each transported fragment retains its physical and source increment pair at the identical parent position. -/
theorem fragments_pairs (run : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun
  retained inputs outer data coefficients) :
    run.fragments.map OwnedFragment.pair = run.items.map IndexedFragment.pair :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.fragmentsAt_pairs run.parent
    run.items _

/-- Flattening the transported run pairs preserves the complete original indexed pair list.

Structural recursion preserves each run's increment pairs and concatenates the unchanged suffix in retained order. -/
private theorem pairs_flatten (runs : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun retained inputs outer data
  coefficients)) :
    (runs.map (fun run => run.fragments.map OwnedFragment.pair)).flatten =
      ((runs.map items).flatten).map IndexedFragment.pair := by
  induction runs with
  | nil => rfl
  | cons run rest ih =>
    change run.fragments.map OwnedFragment.pair ++ _ = (run.items ++ _).map IndexedFragment.pair
    rw [Map.map_append, run.fragments_pairs, ih]

end IndexedRun

set_option genInjectivity false in
/-- Maximal consecutive parent groups retain the original order and multiplicity.

Its cached nonempty runs flatten to the supplied indexed fragment list. Adjacent runs retain distinct parent positions,
so grouping preserves multiplicity as well as order. -/
structure IndexedGrouping (retained : Preparation.CommonBasisPreparation prepared) {index : Nat} (inputs :
  retained.Inputs index)
    (outer : Fin prepared.occurrences.length) {faceIndex : Nat}
    (data : FragmentQueries.RowData (ParentIndices.occurrenceAt prepared.occurrences outer) faceIndex)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (items : List (IndexedFragments.IndexedFragment retained inputs outer data coefficients)) where
  /-- The cached maximal consecutive runs of the original indexed fragments. -/ runs : List
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun retained inputs outer data
    coefficients)
  /-- Flattening the cached runs returns the identical original indexed fragment list. -/ flattened : (runs.map
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.items).flatten = items
  /-- The cached runs have distinct original parent positions at every adjacent boundary. -/ separated :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.separated runs

constructive_injectivity IndexedGrouping

namespace IndexedGrouping
variable {items : List
  (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment retained inputs
  outer data coefficients)}

/-- Compute the maximal consecutive original-parent runs once and retain their exact flattening and adjacent-parent
separation certificates.

The grouping algorithm is evaluated once. Its flattening and adjacent-parent certificates refer to those same cached
runs. -/
@[expose] def build (items : List (IndexedFragments.IndexedFragment retained inputs outer data coefficients)) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping retained inputs outer data
      coefficients items :=
  ⟨IndexedRun.group items,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.group_flatten items,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.group_separated items⟩

/-- Both paths, including junction increments, survive transport and grouping.

The cached flattening certificate identifies the supplied original fragment list. Parent transport preserves its
physical and source increment pairs. -/
theorem pairs_eq (grouped : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping
  retained inputs outer data coefficients items) :
    (grouped.runs.map (fun run => run.fragments.map OwnedFragment.pair)).flatten =
      items.map IndexedFragment.pair :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun.pairs_flatten
    grouped.runs).trans (congrArg (List.map IndexedFragment.pair) grouped.flattened)

end IndexedGrouping

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
