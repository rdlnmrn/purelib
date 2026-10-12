module
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
public import Purelib.Riemann.Paths.PreparedSegmentSources
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.PuncturedGridFaces

/-!
# Parent grouping of the actual flattened fragment word

Read the already retained fragment spine, keeping each parent's exact
coordinate and root endpoints. Splitting at a parent boundary preserves the
same pieces and root chain; no path preparation or owner query is repeated.
-/

namespace Purelib.Riemann.Topology.PreparedRefinementRootChains.RootChain

public section

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveFragments.SheetEntries

open Purelib.Geometry

open Purelib.Geometry.Rectangle.Partition

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Integration

open Purelib.Riemann.Paths

open Purelib.Riemann.Readings

open Purelib.Riemann.Topology

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)

variable {genus : Nat} {curve : HyperellipticCurve genus} {source :
  Differential genus}

/-- Proof-local splitting of the actual root chain at an existing boundary.

Finite recursion on the supplied prefix retains an actual intermediate name and both original subchains. The same
original parent occurrences and endpoint root equivalences determine the split. -/
theorem split : ∀ (before : List (CenteredEdge curve source))
    {after : List (CenteredEdge curve source)} {first last : Named}, RootChain (before ++ after) first last →
      ∃ middle, Nonempty (RootChain before first middle) ∧ Nonempty (RootChain after middle last)
  | [], _, first, _, roots => ⟨first, ⟨.nil (NamedEquivalent.refl _)⟩, ⟨roots⟩⟩
  | parent :: before, _, _, _, .cons _ entry tail => by
      obtain ⟨middle, ⟨left⟩, ⟨right⟩⟩ := split before tail
      exact ⟨middle, ⟨.cons parent entry left⟩, ⟨right⟩⟩

end
end Purelib.Riemann.Topology.PreparedRefinementRootChains.RootChain

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords

public section

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveFragments.SheetEntries

open Purelib.Geometry

open Purelib.Geometry.Rectangle.Partition

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Integration

open Purelib.Riemann.Paths

open Purelib.Riemann.Readings

open Purelib.Riemann.Topology

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open _root_.Purelib.Geometry.Rectangle renaming AxisPartition -> Partition
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest RequestedParents)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragments
  RegularPrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open
  PuncturedGrid.Fragment.LiftedReadings.ClearGrid.RegularPrimitiveFragments.SheetEntries
  (LiftedSources)
open
  PuncturedGrid.Fragment.LiftedReadings.ClearGrid.RegularPrimitiveSplits.SheetEntries
  (LiftedSources)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Paths.PreparedSegmentSources (SegmentSource)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {source : Differential genus} {axes :
    PrimitiveAxes base.bank.grid}
  {domains : FaceDomainBank frames
    base.faces.regulars} {mesh : LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Rational}

namespace LiftedFragment

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment in
/-- Split an existing rooted word without searching for or replacing its middle owner. The actual junction coordinate
and root name are retained.

The supplied prefix determines a boundary of the same original word. Its coordinate and root name are retained in the
two resulting certificates, together with all original junction witnesses. -/
theorem RootedWord.split : ∀ (before : List (RootedWords.LiftedFragment axes domains mesh source count target))
    {after : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named},
    LiftedFragment.RootedWord (before ++ after) first firstName last lastName →
      ∃ middle middleName, LiftedFragment.RootedWord before first firstName middle middleName ∧
        LiftedFragment.RootedWord after middle middleName last lastName
  | [], _, first, _, firstName, _, word =>
      ⟨first, firstName, .nil rfl ⟨NamedEquivalent.refl _⟩, word⟩
  | _ :: before, _, _, _, _, _, .cons piece coordinate root tail => by
      obtain ⟨middle, middleName, left, right⟩ := split before tail
      exact ⟨middle, middleName, .cons piece coordinate root left, right⟩

/-- Each actual parent retains its original fragment occurrences and exact endpoint root names, before any regrouping by
original path segments.

Each head group carries the original parent identity of every fragment and its rooted endpoint word. The dependent tail
preserves the remaining parents and ordered occurrences. -/
inductive ParentGroups : List (PreparedSubdivisionModelCore.CenteredEdge curve source) →
    List (RootedWords.LiftedFragment axes domains mesh source count target) → Prop
  /-- The empty original parent list retains an empty fragment grouping. -/ | nil :
    ParentGroups [] []
  /-- Retain one actual parent's ordered fragments and original endpoint-root chain before the remaining parent groups.
  -/
  | cons {parent : PreparedSubdivisionModelCore.CenteredEdge curve source} {parents : List
    (PreparedSubdivisionModelCore.CenteredEdge curve source)}
      {block pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
      (original : ∀ piece ∈ block, piece.parent = parent)
      (word : LiftedFragment.RootedWord block (parent.edge.point 0) (parent.edge.rootName 0 parent.edge.baseInside)
        (parent.edge.point 1) (parent.edge.rootName 1 (by decide)))
      (tail : ParentGroups parents
        pieces) : ParentGroups
        (parent :: parents) (block ++ pieces)

namespace ParentGroups

/-- The split changes only the grouping of the retained list.

Finite recursion follows the supplied original parent prefix. The output concatenation equation retains exactly the same
fragment occurrences, with both original grouped tails. -/
theorem split : ∀ (before : List (PreparedSubdivisionModelCore.CenteredEdge curve source))
    {after : List (PreparedSubdivisionModelCore.CenteredEdge curve source)} {pieces : List (RootedWords.LiftedFragment
      axes domains mesh source count target)},
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.ParentGroups (before ++ after) pieces
      → ∃ left right, pieces = left ++ right ∧
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.ParentGroups before left ∧
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.ParentGroups after right
  | [], _, pieces, groups => ⟨[], pieces, rfl, .nil, groups⟩
  | _ :: before, _, _, .cons (block := block) original word tail => by
      obtain ⟨left, right, equal, firstPart, lastPart⟩ :=
        split before
        tail
      exact ⟨block ++ left, right, (congrArg (List.append block) equal).trans (Append.append_assoc _ _ _).symm,
        .cons original word firstPart, lastPart⟩

/-- Original source membership passes to the actual pieces, without requiring equality or decidable comparison of
prepared-parent records.

The retained grouping supplies each piece's original parent identity. Membership of that same parent in the supplied
source chain transports its original segment-source certificate. -/
theorem segment_sources {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    (groups : Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.ParentGroups parents pieces)
      {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    {segment : ClearPath.ClearSegment curve.polynomial ambient start finish}
    (original : ∀ parent ∈ parents, PreparedSegmentSources.SegmentSource segment parent) :
    ∀ piece ∈ pieces, PreparedSegmentSources.SegmentSource segment piece.parent := by
  induction groups with
  | nil => intro piece member; exact (List.not_mem_nil member).elim
  | @cons parent parents block pieces same word tail ih =>
      intro piece member
      rcases Membership.mem_append.mp member with member | member
      · exact (congrArg (PreparedSegmentSources.SegmentSource segment) (same piece member)).mpr (original parent
          List.mem_cons_self)
      · exact ih (fun parent member => original parent (List.mem_cons_of_mem _ member)) piece member

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment in
/-- Reassemble original root junctions over exactly the same grouped word.

The supplied parent coordinate and root chains align the original head word with its retained tail. Concatenation keeps
those same intermediate owners and every original fragment occurrence. -/
theorem rooted {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    (groups : Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.ParentGroups parents pieces)
      {first last : Data.Gaussian.Basic.Canonical}
    {firstName lastName : Gaussian.Name.Basic.Named}
    (coordinates : RootedWords.ParentCoordinates parents first last) (roots : PreparedRefinementRootChains.RootChain
      parents firstName lastName) :
    LiftedFragment.RootedWord pieces first firstName last lastName := by
  induction groups generalizing first last firstName lastName with
  | nil =>
      cases coordinates
      cases roots with
      | nil equivalent => exact .nil rfl ⟨equivalent⟩
  | cons original word tail ih =>
      cases coordinates with
      | cons _ tailCoordinates =>
          cases roots with
          | cons _ entry tailRoots =>
              exact (word.changeStart rfl ⟨entry⟩).append (ih tailCoordinates tailRoots)

end ParentGroups
end LiftedFragment

namespace RegularPrimitiveFragments.SheetEntries.LiftedSources

open
  SheetEntries.LiftedSources
  in
/-- Every actual fragment in the retained single-parent source spine preserves that exact original parent owner.

Structural membership in the retained source spine identifies each original head or tail fragment. Their parent field is
the same supplied centered edge. -/
private theorem parent_eq {parent : PreparedSubdivisionModelCore.CenteredEdge curve source} {partition :
  Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)}
    {request : UniformPreparedRequests.LocalRequest parent count target} {intervals : List
      PreparedAxisPartitions.Interval}
    {fragments : RegularFaces.RegularPrimitiveFragments axes parent partition intervals}
    {entries : FragmentSheets domains request fragments}
    (sources : LiftedSources mesh entries) : ∀ piece ∈ pieces sources, piece.parent = parent := by
  induction sources with
  | nil => intro piece member; exact (List.not_mem_nil member).elim
  | cons first rest ih =>
      intro piece member
      rcases Membership.mem_cons.mp member with rfl | member
      · rfl
      · exact ih piece member

end RegularPrimitiveFragments.SheetEntries.LiftedSources

namespace RegularPrimitiveSplits.SheetEntries.LiftedSources

open
  SheetEntries.LiftedSources
  in
/-- The certificate is read directly from the cached nested source spine.

Each head source bank supplies its original parent identities and rooted interval walk. The remaining cached source
spine gives the ordered tail grouping. -/
theorem parentGroups {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)} {splits :
  PreparedPrimitiveSplits.PrimitiveSplits axes parents}
    {fragments : RegularFaces.RegularPrimitiveSplits (base := base) axes splits} {requests :
      UniformPreparedRequests.RequestedParents count target parents}
    {entries : SplitSheets domains fragments requests} (sources : LiftedSources mesh entries) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.ParentGroups parents (pieces sources)
      := by
  induction sources with
  | nil => exact .nil
  | @cons parent parents partition splits head tail request requests firstEntries restEntries firstSources restSources
    ih =>
      exact .cons
        (RegularPrimitiveFragments.SheetEntries.LiftedSources.parent_eq
        firstSources)
        (LiftedSources.rooted_of_walk firstSources partition.walk partition.walk_edges.symm parent.edge.baseInside (by
          decide)) ih

end RegularPrimitiveSplits.SheetEntries.LiftedSources
end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
