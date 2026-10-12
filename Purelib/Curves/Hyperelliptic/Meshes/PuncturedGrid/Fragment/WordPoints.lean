module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial

/-! Endpoint inclusion for every occurrence of the cached original word. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordPoints.SegmentSplit
public section
open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks.RegularPrimitiveFragments
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks.RegularPrimitiveSplits
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveFragments.SheetEntries
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Paths
open Purelib.Riemann.Readings
open Purelib.Data.List

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts SegmentSplit)
open Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts (point_zero point_one)

/-- Both original endpoints of the retained segment belong to its complete cached split-point list. -/
theorem endpoints_mem {columns rows : Nat} {geometry : RectangularInverseModels.Geometry columns rows}
    {cuts : RectangularSegmentSplitting.GridCuts geometry} {first last : Data.Gaussian.Basic.Canonical} (split :
      RectangularSegmentSplitting.SegmentSplit cuts first last) :
    first ∈ split.points ∧ last ∈ split.points := by
  obtain ⟨left, leftMem, leftInside⟩ := split.covers 0 (by decide)
  obtain ⟨right, rightMem, rightInside⟩ := split.covers 1 (by decide)
  have leftEq := left.first_eq
  rw [le_antisymm leftInside.1 left.within.1, PreparedSegmentCuts.point_zero first last] at leftEq
  have rightEq := right.last_eq
  rw [le_antisymm right.within.2 rightInside.2, PreparedSegmentCuts.point_one first last] at rightEq
  have firstMem := (split.points_mem leftMem).1
  have lastMem := (split.points_mem rightMem).2
  rw [leftEq] at firstMem
  rw [rightEq] at lastMem
  exact ⟨firstMem, lastMem⟩

end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordPoints.SegmentSplit

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordPoints.ClearGrid
public section
open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks.RegularPrimitiveFragments
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks.RegularPrimitiveSplits
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveFragments.SheetEntries
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Paths
open Purelib.Riemann.Readings
open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open _root_.Purelib.Geometry.Rectangle renaming AxisPartition -> Partition
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest RequestedParents)
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
open
  PuncturedGrid.Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries.LiftedSources
  (Rooted)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)

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

namespace RegularPrimitiveFragments.SheetEntries.LiftedSources

variable {parent : CenteredEdge curve source} {partition :
  Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)}
  {request : LocalRequest parent count target}

/-- Both endpoints of every actual retained fragment occurrence belong to its original cached point bank.

The proof follows membership in the retained list through its original head, tail or concatenation, preserving the
supplied occurrence witness. -/
theorem endpoints_mem {intervals : List PreparedAxisPartitions.Interval}
    {fragments : RegularFaces.RegularPrimitiveFragments axes parent partition intervals}
    {entries : FragmentSheets domains request fragments} (sources : LiftedSources mesh entries) :
    ∀ piece ∈ (LiftedSources.pieces sources), piece.first ∈ (SheetEntries.points entries) ∧ piece.last ∈
      (SheetEntries.points entries) := by
  induction sources with
  | nil => intro piece member; exact (List.not_mem_nil member).elim
  | @cons interval intervals fragment fragments assigned entries first rest ih =>
      intro piece member
      rcases Membership.mem_cons.mp member with rfl | member
      · have ends := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordPoints.SegmentSplit.endpoints_mem
          assigned.split
        exact ⟨List.mem_append_left _ ends.1, List.mem_append_left _ ends.2⟩
      · have ends := ih piece member
        exact ⟨List.mem_append_right _ ends.1, List.mem_append_right _ ends.2⟩

end RegularPrimitiveFragments.SheetEntries.LiftedSources

namespace RegularPrimitiveSplits.SheetEntries.LiftedSources

/-- Both endpoints of every actual retained fragment occurrence belong to its original cached point bank.

The proof follows membership in the retained list through its original head, tail or concatenation, preserving the
supplied occurrence witness. -/
theorem endpoints_mem {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)} {splits :
  PreparedPrimitiveSplits.PrimitiveSplits axes parents}
    {fragments : RegularFaces.RegularPrimitiveSplits (base := base) axes splits} {requests :
      UniformPreparedRequests.RequestedParents count target parents}
    {entries : SplitSheets domains fragments requests} (sources : LiftedSources mesh entries) :
    ∀ piece ∈ (LiftedSources.pieces sources), piece.first ∈ (SheetEntries.points entries) ∧ piece.last ∈
      (SheetEntries.points entries) := by
  induction sources with
  | nil => intro piece member; exact (List.not_mem_nil member).elim
  | cons first rest ih =>
      intro piece member
      rcases Membership.mem_append.mp member with member | member
      · have ends :=
          RegularPrimitiveFragments.SheetEntries.LiftedSources.endpoints_mem
          first piece member
        exact ⟨List.mem_append_left _ ends.1, List.mem_append_left _ ends.2⟩
      · have ends := ih piece member
        exact ⟨List.mem_append_right _ ends.1, List.mem_append_right _ ends.2⟩

namespace Rooted

/-- Both endpoints of every actual retained fragment occurrence belong to its original cached point bank. -/
theorem endpoints_mem {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)} {splits :
  PreparedPrimitiveSplits.PrimitiveSplits axes parents}
    {fragments : RegularFaces.RegularPrimitiveSplits (base := base) axes splits} {requests :
      UniformPreparedRequests.RequestedParents count target parents}
    {entries : SplitSheets domains fragments requests}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedSources.Rooted entries mesh first firstName last lastName)
    {piece : RootedWords.LiftedFragment axes domains mesh source count target} (member : piece ∈ word.pieces) :
    piece.first ∈ (SheetEntries.points entries) ∧ piece.last ∈ (SheetEntries.points entries) :=

    PuncturedGrid.Fragment.WordPoints.ClearGrid.RegularPrimitiveSplits.SheetEntries.LiftedSources.endpoints_mem
      word.sources piece (word.pieces_eq ▸ member)

end Rooted
end RegularPrimitiveSplits.SheetEntries.LiftedSources
end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordPoints.ClearGrid
