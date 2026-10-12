module
import Purelib.Data.List.Reverse
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
public import Purelib.Polynomial.Geometry.Grid.Axis.Partial
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
public import Purelib.Riemann.Paths.PreparedSegmentSources
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ParentGroups
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces

public section

/-! Read complete interval sums from subwords of the actual retained rooted
word. Original roots are recovered by splitting, and coordinate coverage is
read from the existing partial walk certificate. -/

section

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisCancellation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.Axis
open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Riemann.Paths

open Purelib.Data.List

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
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Interval Cell HorizontalLine VerticalLine)
open Purelib.Riemann.Paths.PreparedSegmentSources (SegmentSource)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords (canonicalRoute)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts (routeValue)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation (canonicalPoint)

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

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.CompleteGroups

/-- The first retained piece of a nonempty partial walk starts at its original lower endpoint. -/
private theorem partial_start {Alpha : Type u} {Piece : Type v} {key : Alpha → Fraction.Rational}
    {span : Piece → ClearGrid.Interval key} {first last : Piece → Fraction.Rational} {intervals : List
      (ClearGrid.Interval key)}
    {head : Piece} {pieces : List Piece} {a b : Fraction.Rational}
    (path : Partial.PartialWalk span first last intervals (head :: pieces) a b) : first head = a := by
  cases path
  rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.CompleteGroups

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.CompleteGroups.RootedWord

/-- The original rooted word's last coordinate is the endpoint retained by its partial walk certificate. -/
theorem partial_finish {Alpha : Type} {key : Alpha → Fraction.Rational}
    (coordinate : Data.Gaussian.Basic.Canonical → Fraction.Rational)
    (span : RootedWords.LiftedFragment axes domains mesh source count target → ClearGrid.Interval key)
    {intervals : List (ClearGrid.Interval key)}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces first firstName last lastName)
    {a b : Fraction.Rational}
    (path : Partial.PartialWalk span (fun piece => coordinate piece.first) (fun piece => coordinate piece.last)
      intervals pieces a b)
    (firstEq : coordinate first = a) : coordinate last = b := by
  induction word generalizing a b with
  | nil equal root => cases path; exact (congrArg coordinate equal).symm.trans firstEq
  | cons piece equal root tail ih =>
      cases path with
      | cons _ member moving inside rest => exact ih rest rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.CompleteGroups.RootedWord

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.CompleteGroups

/-- Split an actual partial walk at the supplied original list prefix while retaining a common intermediate coordinate.
-/
private theorem partial_split {Alpha : Type u} {Piece : Type v} {key : Alpha → Fraction.Rational}
    {span : Piece → ClearGrid.Interval key} {first last : Piece → Fraction.Rational} {intervals : List
      (ClearGrid.Interval key)} :
    ∀ (before : List Piece) {after : List Piece} {a b : Fraction.Rational},
    Partial.PartialWalk span first last intervals (before ++ after) a b →
      ∃ middle, Partial.PartialWalk span first last intervals before a middle ∧
        Partial.PartialWalk span first last intervals after middle b
  | [], _, a, _, path => ⟨a, .nil a, path⟩
  | head :: rest, _, _, _, .cons _ member moving inside tail => by
      obtain ⟨middle, before, after⟩ :=
        partial_split rest tail
      exact ⟨middle, .cons head member moving inside before, after⟩

/-- The final piece of an actual partial walk ends at the certificate's retained endpoint. -/
private theorem partial_snoc_finish {Alpha : Type u} {Piece : Type v} {key : Alpha → Fraction.Rational}
    {span : Piece → ClearGrid.Interval key} {first last : Piece → Fraction.Rational} {intervals : List
      (ClearGrid.Interval key)}
    {head : Piece} {pieces : List Piece} {a b : Fraction.Rational}
    (path : Partial.PartialWalk span first last intervals (pieces ++ [head]) a b) : last head = b := by
  obtain ⟨middle, _, ending⟩ := partial_split pieces
    path
  cases ending with
  | cons _ member moving inside tail => cases tail; rfl

/-- Reverse-ordered coverage determines the original rooted word's last coordinate without reversing its retained root
owners. -/
private theorem reverse_partial_finish {Alpha : Type} {key : Alpha → Fraction.Rational}
    (coordinate : Data.Gaussian.Basic.Canonical → Fraction.Rational)
    (span : RootedWords.LiftedFragment axes domains mesh source count target → ClearGrid.Interval key)
    {intervals : List (ClearGrid.Interval key)}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces first firstName last lastName)
    {a b : Fraction.Rational}
    (path : Partial.PartialWalk span (fun piece => coordinate piece.last) (fun piece => coordinate piece.first)
      intervals pieces.reverse a b)
    (firstEq : coordinate first = b) : coordinate last = a := by
  induction word generalizing a b with
  | nil equal root => cases path; exact (congrArg coordinate equal).symm.trans firstEq
  | cons piece equal root tail ih =>
      rw [Reverse.reverse_cons] at path
      obtain ⟨middle, before, ending⟩ := partial_split
        _ path
      have startEq := partial_start (head := piece)
        ending
      exact ih before startEq

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.CompleteGroups

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.CompleteGroups.RootedWord

/-- A coordinate fixed on the original start and every retained fragment endpoint remains fixed at the original word
end. -/
theorem constant_finish (coordinate : Data.Gaussian.Basic.Canonical → Fraction.Rational)
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces first firstName last lastName) {value : Fraction.Rational}
    (firstEq : coordinate first = value) (fixed : ∀ piece ∈ pieces, coordinate piece.last = value) : coordinate last =
      value := by
  induction word with
  | nil equal root => exact (congrArg coordinate equal).symm.trans firstEq
  | cons piece equal root tail ih =>
      exact ih (fixed piece List.mem_cons_self) (fun child member => fixed child (List.mem_cons_of_mem _ member))

/-- Read the initial coordinate from coverage presented in reverse order, while keeping the original rooted word
unchanged. -/
theorem reverse_partial_start {Alpha : Type} {key : Alpha → Fraction.Rational}
    (coordinate : Data.Gaussian.Basic.Canonical → Fraction.Rational)
    (span : RootedWords.LiftedFragment axes domains mesh source count target → ClearGrid.Interval key)
    {intervals : List (ClearGrid.Interval key)}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces first firstName last lastName)
    {a b : Fraction.Rational}
    (path : Partial.PartialWalk span (fun piece => coordinate piece.last) (fun piece => coordinate piece.first)
      intervals pieces.reverse a b)
    (lastEq : coordinate last = a) : coordinate first = b := by
  cases word with
  | nil equal root => cases path; exact (congrArg coordinate equal).trans lastEq
  | cons piece equal root tail =>
      rw [Reverse.reverse_cons] at path
      exact (congrArg coordinate equal).trans
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.CompleteGroups.partial_snoc_finish (head := piece) path)

/-- Read a fixed coordinate at the start of the actual rooted word. -/
theorem constant_start (coordinate : Data.Gaussian.Basic.Canonical → Fraction.Rational)
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces first firstName last lastName) {value : Fraction.Rational}
    (lastEq : coordinate last = value) (fixed : ∀ piece ∈ pieces, coordinate piece.first = value) : coordinate first =
      value := by
  cases word with
  | nil equal root => exact (congrArg coordinate equal).trans lastEq
  | cons piece equal root tail => exact (congrArg coordinate equal).trans (fixed piece List.mem_cons_self)

/-- A complete increasing horizontal group reads exactly its two retained axis endpoints in its actual canonical
primitive chart. -/
theorem horizontal_complete_sum {head : RootedWords.LiftedFragment axes domains mesh source count target}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord (head :: pieces) first firstName last lastName)
    (original : ∀ piece ∈ head :: pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ head :: pieces, piece.last ≠ piece.first) (horizontal : start.im = finish.im)
    {span : ClearGrid.Interval (VerticalLine.coordinate (polynomial := curve.polynomial) (ambient := Cuts.Ambient
      curve))}
    (same : ∀ piece ∈ head :: pieces, piece.fragment.located.cell.horizontal = span)
    (path : Partial.PartialWalk (fun piece => piece.fragment.located.cell.horizontal)
      (fun piece => piece.first.re) (fun piece => piece.last.re) base.bank.grid.xIntervals
      (head :: pieces) span.lower.coordinate span.upper.coordinate)
    (shared : CommonMeshes.FaceSharedMeshes budgets numerics) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((head :: pieces).map (fun piece => (RouteContacts.routeValue piece)
      (RouteWords.canonicalRoute piece) shared)) =
      (RouteCancellation.canonicalPoint head) shared (Components.Basic.point span.upper.coordinate start.im) -
        (RouteCancellation.canonicalPoint head) shared (Components.Basic.point span.lower.coordinate start.im) := by
  have firstCoordinate : first = head.first := by cases word; assumption
  have firstRe : first.re = span.lower.coordinate := by
    rw [firstCoordinate]
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.CompleteGroups.partial_start (head := head) path
  have firstIm := (congrArg Data.Gaussian.Basic.im firstCoordinate).trans
    (SourceGeometry.horizontal_source_queries head (original head List.mem_cons_self) horizontal).1
  have lastRe := partial_finish
    Data.Gaussian.Basic.re _ word path firstRe
  have lastIm := constant_finish
    Data.Gaussian.Basic.im word firstIm
    (fun piece member => (SourceGeometry.horizontal_source_queries piece (original piece member) horizontal).2)
  have firstEq : first = Components.Basic.point span.lower.coordinate start.im := Data.Gaussian.Basic.ext firstRe
    firstIm
  have lastEq : last = Components.Basic.point span.upper.coordinate start.im := Data.Gaussian.Basic.ext lastRe lastIm
  rw [RootedWord.horizontal_telescope word original moving horizontal same shared]
  exact congrArg₂ (fun a b : Data.Gaussian.Basic.Canonical => (RouteCancellation.canonicalPoint head) shared a -
    (RouteCancellation.canonicalPoint head) shared b) lastEq firstEq

/-- The vertical complete group retains the original primitive chart too. -/
theorem vertical_complete_sum {head : RootedWords.LiftedFragment axes domains mesh source count target}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord (head :: pieces) first firstName last lastName)
    (original : ∀ piece ∈ head :: pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ head :: pieces, piece.last ≠ piece.first) (vertical : start.re = finish.re)
    {span : ClearGrid.Interval (HorizontalLine.coordinate (polynomial := curve.polynomial) (ambient := Cuts.Ambient
      curve))}
    (same : ∀ piece ∈ head :: pieces, piece.fragment.located.cell.vertical = span)
    (path : Partial.PartialWalk (fun piece => piece.fragment.located.cell.vertical)
      (fun piece => piece.first.im) (fun piece => piece.last.im) base.bank.grid.yIntervals
      (head :: pieces) span.lower.coordinate span.upper.coordinate)
    (shared : CommonMeshes.FaceSharedMeshes budgets numerics) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((head :: pieces).map (fun piece => (RouteContacts.routeValue piece)
      (RouteWords.canonicalRoute piece) shared)) =
      (RouteCancellation.canonicalPoint head) shared (Components.Basic.point start.re span.upper.coordinate) -
        (RouteCancellation.canonicalPoint head) shared (Components.Basic.point start.re span.lower.coordinate) := by
  have firstCoordinate : first = head.first := by cases word; assumption
  have firstIm : first.im = span.lower.coordinate := by
    rw [firstCoordinate]
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.CompleteGroups.partial_start (head := head) path
  have firstRe := (congrArg Data.Gaussian.Basic.re firstCoordinate).trans
    (SourceGeometry.vertical_source_queries head (original head List.mem_cons_self) vertical).1
  have lastIm := partial_finish
    Data.Gaussian.Basic.im _ word path firstIm
  have lastRe := constant_finish
    Data.Gaussian.Basic.re word firstRe
    (fun piece member => (SourceGeometry.vertical_source_queries piece (original piece member) vertical).2)
  have firstEq : first = Components.Basic.point start.re span.lower.coordinate := Data.Gaussian.Basic.ext firstRe
    firstIm
  have lastEq : last = Components.Basic.point start.re span.upper.coordinate := Data.Gaussian.Basic.ext lastRe lastIm
  rw [RootedWord.vertical_telescope word original moving vertical same shared]
  exact congrArg₂ (fun a b : Data.Gaussian.Basic.Canonical => (RouteCancellation.canonicalPoint head) shared a -
    (RouteCancellation.canonicalPoint head) shared b) lastEq firstEq

/-- A complete decreasing horizontal group reads exactly its two retained axis endpoints in its actual canonical
primitive chart. -/
theorem horizontal_reverse_complete_sum {head : RootedWords.LiftedFragment axes domains mesh source count target}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord (head :: pieces) first firstName last lastName)
    (original : ∀ piece ∈ head :: pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ head :: pieces, piece.last ≠ piece.first) (horizontal : start.im = finish.im)
    {span : ClearGrid.Interval (VerticalLine.coordinate (polynomial := curve.polynomial) (ambient := Cuts.Ambient
      curve))}
    (same : ∀ piece ∈ head :: pieces, piece.fragment.located.cell.horizontal = span)
    (path : Partial.PartialWalk (fun piece => piece.fragment.located.cell.horizontal)
      (fun piece => piece.last.re) (fun piece => piece.first.re) base.bank.grid.xIntervals
      (head :: pieces).reverse span.lower.coordinate span.upper.coordinate)
    (shared : CommonMeshes.FaceSharedMeshes budgets numerics) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((head :: pieces).map (fun piece => (RouteContacts.routeValue piece)
      (RouteWords.canonicalRoute piece) shared)) =
      (RouteCancellation.canonicalPoint head) shared (Components.Basic.point span.lower.coordinate start.im) -
        (RouteCancellation.canonicalPoint head) shared (Components.Basic.point span.upper.coordinate start.im) := by
  have firstCoordinate : first = head.first := by cases word; assumption
  have firstRe : first.re = span.upper.coordinate := by
    rw [firstCoordinate]
    have ending := path
    rw [Reverse.reverse_cons] at ending
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.CompleteGroups.partial_snoc_finish (head := head) ending
  have firstIm := (congrArg Data.Gaussian.Basic.im firstCoordinate).trans
    (SourceGeometry.horizontal_source_queries head (original head List.mem_cons_self) horizontal).1
  have lastRe := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.CompleteGroups.reverse_partial_finish
    Data.Gaussian.Basic.re _ word path firstRe
  have lastIm := constant_finish
    Data.Gaussian.Basic.im word firstIm
    (fun piece member => (SourceGeometry.horizontal_source_queries piece (original piece member) horizontal).2)
  have firstEq : first = Components.Basic.point span.upper.coordinate start.im := Data.Gaussian.Basic.ext firstRe
    firstIm
  have lastEq : last = Components.Basic.point span.lower.coordinate start.im := Data.Gaussian.Basic.ext lastRe lastIm
  rw [RootedWord.horizontal_telescope word original moving horizontal same shared]
  exact congrArg₂ (fun a b : Data.Gaussian.Basic.Canonical => (RouteCancellation.canonicalPoint head) shared a -
    (RouteCancellation.canonicalPoint head) shared b) lastEq firstEq

/-- The decreasing vertical complete group retains the original primitive chart too. -/
theorem vertical_reverse_complete_sum {head : RootedWords.LiftedFragment axes domains mesh source count target}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord (head :: pieces) first firstName last lastName)
    (original : ∀ piece ∈ head :: pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ head :: pieces, piece.last ≠ piece.first) (vertical : start.re = finish.re)
    {span : ClearGrid.Interval (HorizontalLine.coordinate (polynomial := curve.polynomial) (ambient := Cuts.Ambient
      curve))}
    (same : ∀ piece ∈ head :: pieces, piece.fragment.located.cell.vertical = span)
    (path : Partial.PartialWalk (fun piece => piece.fragment.located.cell.vertical)
      (fun piece => piece.last.im) (fun piece => piece.first.im) base.bank.grid.yIntervals
      (head :: pieces).reverse span.lower.coordinate span.upper.coordinate)
    (shared : CommonMeshes.FaceSharedMeshes budgets numerics) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((head :: pieces).map (fun piece => (RouteContacts.routeValue piece)
      (RouteWords.canonicalRoute piece) shared)) =
      (RouteCancellation.canonicalPoint head) shared (Components.Basic.point start.re span.lower.coordinate) -
        (RouteCancellation.canonicalPoint head) shared (Components.Basic.point start.re span.upper.coordinate) := by
  have firstCoordinate : first = head.first := by cases word; assumption
  have firstIm : first.im = span.upper.coordinate := by
    rw [firstCoordinate]
    have ending := path
    rw [Reverse.reverse_cons] at ending
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.CompleteGroups.partial_snoc_finish (head := head) ending
  have firstRe := (congrArg Data.Gaussian.Basic.re firstCoordinate).trans
    (SourceGeometry.vertical_source_queries head (original head List.mem_cons_self) vertical).1
  have lastIm := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.CompleteGroups.reverse_partial_finish
    Data.Gaussian.Basic.im _ word path firstIm
  have lastRe := constant_finish
    Data.Gaussian.Basic.re word firstRe
    (fun piece member => (SourceGeometry.vertical_source_queries piece (original piece member) vertical).2)
  have firstEq : first = Components.Basic.point start.re span.upper.coordinate := Data.Gaussian.Basic.ext firstRe
    firstIm
  have lastEq : last = Components.Basic.point start.re span.lower.coordinate := Data.Gaussian.Basic.ext lastRe lastIm
  rw [RootedWord.vertical_telescope word original moving vertical same shared]
  exact congrArg₂ (fun a b : Data.Gaussian.Basic.Canonical => (RouteCancellation.canonicalPoint head) shared a -
    (RouteCancellation.canonicalPoint head) shared b) lastEq firstEq

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.CompleteGroups.RootedWord

end
