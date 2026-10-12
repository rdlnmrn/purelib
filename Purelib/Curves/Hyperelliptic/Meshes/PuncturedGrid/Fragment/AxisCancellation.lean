module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.PreparedSegmentSources
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceGeometry
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring

public section

/-! Exact cancellation of whole original rooted groups on one retained axis
interval. The actual fragments may present their containing edge either way. -/

section

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
open Purelib.Data.Gaussian
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Riemann.Paths

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment (RootedWord)
open Purelib.Riemann.Paths.PreparedSegmentSources (SegmentSource)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords (canonicalRoute)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts (routeValue)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation (canonicalPoint)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceGeometry (Presents
  canonicalPoint_eq_of_presentations)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Interval HorizontalLine VerticalLine)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

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
  {ambient : Purelib.Geometry.Rational.Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
    {segment : ClearSegment curve.polynomial ambient start finish}
  {points : List Purelib.Data.Gaussian.Basic.Canonical} {tolerance : Rational} {index : Nat}
  {budgets : FaceMeshBudgets source points tolerance
    domains} {numerics : FacePrimitiveBank source
    index domains}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisCancellation

/-- The actual remaining rooted fragment group telescopes in the preceding fragment's retained canonical point readings.

Every source ancestry, moving-fragment witness and root junction is retained across either containing-edge orientation.
-/
private theorem tail_telescope (previous : RootedWords.LiftedFragment axes domains mesh source count target)
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {last : Data.Gaussian.Basic.Canonical} {lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces previous.last previous.lastName last lastName)
    (previousSource : PreparedSegmentSources.SegmentSource segment previous.parent) (previousMoving : previous.last ≠
      previous.first)
    {lower upper : Data.Gaussian.Basic.Canonical} (previousGeometry : (SourceGeometry.Presents previous) lower upper)
    (original : ∀ piece ∈ pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first)
    (geometry : ∀ piece ∈ pieces, (SourceGeometry.Presents piece) lower upper)
    (shared : CommonMeshes.FaceSharedMeshes budgets numerics) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (pieces.map (fun piece => (RouteContacts.routeValue piece)
      (RouteWords.canonicalRoute piece) shared)) =
      (RouteCancellation.canonicalPoint previous) shared last - (RouteCancellation.canonicalPoint previous) shared
        previous.last := by
  cases word with
  | nil coordinate root =>
      change (0 : Data.Gaussian.Basic.Canonical) = _ - _
      rw [coordinate]
      ring1
  | @cons piece rest first last firstName lastName joined roots tail =>
      obtain ⟨roots⟩ := roots
      have equal := SourceGeometry.canonicalPoint_eq_of_presentations joined roots previousSource (original piece
        List.mem_cons_self)
        previousMoving (moving piece List.mem_cons_self) previousGeometry (geometry piece List.mem_cons_self) shared
      have remaining := tail_telescope piece
        tail (original piece List.mem_cons_self) (moving piece List.mem_cons_self)
        (geometry piece List.mem_cons_self)
        (fun child member => original child (List.mem_cons_of_mem _ member))
        (fun child member => moving child (List.mem_cons_of_mem _ member))
        (fun child member => geometry child (List.mem_cons_of_mem _ member)) shared
      change (RouteContacts.routeValue piece) (RouteWords.canonicalRoute piece) shared +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum _ = _
      rw [remaining, RouteCancellation.routeValue_eq, ← equal, ← equal, ← equal, joined]
      ring1
termination_by pieces.length
decreasing_by
  subst pieces
  exact Nat.lt_succ_self _

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisCancellation

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisCancellation.RootedWord

/-- Telescope a retained rooted group with a common unordered containing edge. Every original root junction is used,
including across parents. -/
theorem presentations_telescope {head : RootedWords.LiftedFragment axes domains mesh source count target}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord (head :: pieces) first firstName last lastName)
    (original : ∀ piece ∈ head :: pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ head :: pieces, piece.last ≠ piece.first)
    {lower upper : Data.Gaussian.Basic.Canonical} (geometry : ∀ piece ∈ head :: pieces, (SourceGeometry.Presents piece)
      lower upper)
    (shared : CommonMeshes.FaceSharedMeshes budgets numerics) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((head :: pieces).map (fun piece => (RouteContacts.routeValue piece)
      (RouteWords.canonicalRoute piece) shared)) =
      (RouteCancellation.canonicalPoint head) shared last - (RouteCancellation.canonicalPoint head) shared first := by
  cases word with
  | cons head coordinate root tail =>
      have remaining := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisCancellation.tail_telescope head tail
        (original head List.mem_cons_self) (moving head List.mem_cons_self)
        (geometry head List.mem_cons_self)
        (fun child member => original child (List.mem_cons_of_mem _ member))
        (fun child member => moving child (List.mem_cons_of_mem _ member))
        (fun child member => geometry child (List.mem_cons_of_mem _ member)) shared
      change (RouteContacts.routeValue head) (RouteWords.canonicalRoute head) shared +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum _ = _
      rw [remaining, RouteCancellation.routeValue_eq, coordinate]
      ring1

/-- The retained horizontal interval group supplies all containing-edge geometry needed by exact cancellation. -/
theorem horizontal_telescope {head : RootedWords.LiftedFragment axes domains mesh source count target}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord (head :: pieces) first firstName last lastName)
    (original : ∀ piece ∈ head :: pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ head :: pieces, piece.last ≠ piece.first) (horizontal : start.im = finish.im)
    {span : ClearGrid.Interval (VerticalLine.coordinate (polynomial := curve.polynomial) (ambient := Cuts.Ambient
      curve))}
    (same : ∀ piece ∈ head :: pieces, piece.fragment.located.cell.horizontal = span)
    (shared : CommonMeshes.FaceSharedMeshes budgets numerics) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((head :: pieces).map (fun piece => (RouteContacts.routeValue piece)
      (RouteWords.canonicalRoute piece) shared)) =
      (RouteCancellation.canonicalPoint head) shared last - (RouteCancellation.canonicalPoint head) shared first := by
  apply presentations_telescope word
    original moving
    (lower := Components.Basic.point span.lower.coordinate start.im)
    (upper := Components.Basic.point span.upper.coordinate start.im) _ shared
  intro piece member
  have geometry := SourceGeometry.horizontal_source_geometry piece (original piece member) (moving piece member)
    horizontal
  rw [same piece member] at geometry
  exact geometry

/-- The same cancellation applies to an actual vertical interval group. -/
theorem vertical_telescope {head : RootedWords.LiftedFragment axes domains mesh source count target}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord (head :: pieces) first firstName last lastName)
    (original : ∀ piece ∈ head :: pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ head :: pieces, piece.last ≠ piece.first) (vertical : start.re = finish.re)
    {span : ClearGrid.Interval (HorizontalLine.coordinate (polynomial := curve.polynomial) (ambient := Cuts.Ambient
      curve))}
    (same : ∀ piece ∈ head :: pieces, piece.fragment.located.cell.vertical = span)
    (shared : CommonMeshes.FaceSharedMeshes budgets numerics) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((head :: pieces).map (fun piece => (RouteContacts.routeValue piece)
      (RouteWords.canonicalRoute piece) shared)) =
      (RouteCancellation.canonicalPoint head) shared last - (RouteCancellation.canonicalPoint head) shared first := by
  apply presentations_telescope word
    original moving
    (lower := Components.Basic.point start.re span.lower.coordinate)
    (upper := Components.Basic.point start.re span.upper.coordinate) _ shared
  intro piece member
  have geometry := SourceGeometry.vertical_source_geometry piece (original piece member) (moving piece member) vertical
  rw [same piece member] at geometry
  exact geometry

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisCancellation.RootedWord

end
