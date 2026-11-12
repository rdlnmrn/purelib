module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
public import Purelib.Riemann.Paths.PreparedSegmentSources
import Purelib.Riemann.Periods.StandardPeriodGridLines
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EdgeGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ReverseRoutes
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ReverseJunctions

public section

/-! Original segment ancestry identifies both coordinates of a containing
edge from the actual cached cell interval, allowing either orientation. -/

section

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EdgeGeometry
open Purelib.Data.Gaussian
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Paths
open Purelib.Riemann.Periods.StandardPeriodGridLines.Grid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Riemann.Paths.PreparedSegmentSources (SegmentSource)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid} {edges :
    RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {source : Differential genus} {axes :
    PrimitiveAxes base.bank.grid}
  {domains : FaceDomainBank frames
    base.faces.regulars} {mesh : LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Fraction.Rational}
  {ambient : Geometry.Rational.Box} {start finish : Basic.Canonical}
    {segment : ClearSegment curve.polynomial ambient start finish}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceGeometry

/-- Both interval owners of the actual located fragment cell belong to the original grid interval lists. -/
private theorem cell_intervals (piece : LiftedFragment axes domains mesh source count target) :
    piece.fragment.located.cell.horizontal ∈ base.bank.grid.xIntervals ∧
      piece.fragment.located.cell.vertical ∈ base.bank.grid.yIntervals := by
  obtain ⟨horizontal, member, row⟩ := Flatten.mem_flatMap.mp piece.fragment.located.cell_member
  obtain ⟨vertical, present, equal⟩ := Map.mem_map.mp row
  exact ⟨(congrArg Cell.horizontal equal) ▸ member, (congrArg Cell.vertical equal) ▸ present⟩

/-- Both actual fragment query points retain the fixed imaginary coordinate of their original horizontal source. -/
theorem horizontal_source_queries (piece : LiftedFragment axes domains mesh source count target)
    (original : SegmentSource segment piece.parent) (horizontal : start.im = finish.im) :
    piece.first.im = start.im ∧ piece.last.im = start.im := by
  obtain ⟨first, last, _, _, _, firstEq, lastEq⟩ := original
  have fixed (parameter : Fraction.Rational) : (segment.pointAt parameter).im = start.im := by
    change start.im + parameter * (finish.im - start.im) = _
    rw [horizontal]
    ring1
  have a := (congrArg Basic.im firstEq).trans (fixed first)
  have b := (congrArg Basic.im lastEq).trans (fixed last)
  exact ⟨(congrArg Basic.im piece.fragment.located.first_eq).trans
      ((ParentOnLine.horizontal piece.parent (b.trans a.symm) _).trans a),
    (congrArg Basic.im piece.fragment.located.last_eq).trans
      ((ParentOnLine.horizontal piece.parent (b.trans a.symm) _).trans a)⟩

/-- Both actual fragment query points retain the fixed real coordinate of their original vertical source. -/
theorem vertical_source_queries (piece : LiftedFragment axes domains mesh source count target)
    (original : SegmentSource segment piece.parent) (vertical : start.re = finish.re) :
    piece.first.re = start.re ∧ piece.last.re = start.re := by
  obtain ⟨first, last, _, _, _, firstEq, lastEq⟩ := original
  have fixed (parameter : Fraction.Rational) : (segment.pointAt parameter).re = start.re := by
    change start.re + parameter * (finish.re - start.re) = _
    rw [vertical]
    ring1
  have a := (congrArg Basic.re firstEq).trans (fixed first)
  have b := (congrArg Basic.re lastEq).trans (fixed last)
  exact ⟨(congrArg Basic.re piece.fragment.located.first_eq).trans
      ((ParentOnLine.vertical piece.parent (b.trans a.symm) _).trans a),
    (congrArg Basic.re piece.fragment.located.last_eq).trans
      ((ParentOnLine.vertical piece.parent (b.trans a.symm) _).trans a)⟩

/-- The full source edge presents these two geometric endpoints in either order. -/
@[expose] def Presents (piece : LiftedFragment axes domains mesh source count target) (lower upper :
  Basic.Canonical) : Prop :=
    (piece.fragment.source.start = lower ∧ piece.fragment.source.finish = upper) ∨
    (piece.fragment.source.finish = lower ∧ piece.fragment.source.start = upper)

/-- A moving fragment of an original horizontal source presents the endpoints of its retained cell interval in one of
the two orientations. -/
theorem horizontal_source_geometry (piece : LiftedFragment axes domains mesh source count target)
    (original : SegmentSource segment piece.parent) (moving : piece.last ≠ piece.first)
    (horizontal : start.im = finish.im) :
    Presents piece (Components.Basic.point
      piece.fragment.located.cell.horizontal.lower.coordinate start.im)
      (Components.Basic.point piece.fragment.located.cell.horizontal.upper.coordinate start.im) := by
  have fixed := SourceGeometry.horizontal_source_queries piece
    original horizontal
  have different : piece.first.re ≠ piece.last.re := by
    intro equal
    exact moving (Basic.ext equal.symm (fixed.2.trans fixed.1.symm))
  have geometry := Edge.horizontal_endpoints
    (SourceGeometry.cell_intervals piece).1 different
    ⟨piece.fragment.located.first_inside.1, piece.fragment.located.first_inside.2.1⟩
    ⟨piece.fragment.located.last_inside.1, piece.fragment.located.last_inside.2.1⟩
    piece.fragment.source.edge piece.fragment.source.first piece.fragment.source.last
  change _ ∨ _ at geometry
  rw [fixed.1] at geometry
  exact geometry

/-- A moving fragment of an original vertical source presents the endpoints of its retained cell interval in one of the
two orientations. -/
theorem vertical_source_geometry (piece : LiftedFragment axes domains mesh source count target)
    (original : SegmentSource segment piece.parent) (moving : piece.last ≠ piece.first)
    (vertical : start.re = finish.re) :
    Presents piece (Components.Basic.point start.re
      piece.fragment.located.cell.vertical.lower.coordinate)
      (Components.Basic.point start.re piece.fragment.located.cell.vertical.upper.coordinate) := by
  have fixed := SourceGeometry.vertical_source_queries piece original
    vertical
  have different : piece.first.im ≠ piece.last.im := by
    intro equal
    exact moving (Basic.ext (fixed.2.trans fixed.1.symm) equal.symm)
  have geometry := Edge.vertical_endpoints
    (SourceGeometry.cell_intervals piece).2 different
    piece.fragment.located.first_inside.2.2 piece.fragment.located.last_inside.2.2
    piece.fragment.source.edge piece.fragment.source.first piece.fragment.source.last
  change _ ∨ _ at geometry
  rw [fixed.1] at geometry
  exact geometry

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceGeometry

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

variable {numerator : CoefficientPolynomial}
  {points : List Basic.Canonical} {tolerance : Fraction.Rational} {index :
  Nat}
  {budgets : FaceMeshBudgets source points tolerance (numerator := numerator)
    domains} {numerics : FacePrimitiveBank source
    index (numerator := numerator) domains}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceGeometry

/-- Both possible source presentations select the same cached point readings at an original rooted junction. -/
theorem canonicalPoint_eq_of_presentations {left right : LiftedFragment axes domains mesh source count
  target}
    (joined : left.last = right.first)
    (roots : Gaussian.Equivalence.NamedEquivalent left.lastName right.firstName)
    (leftSource : SegmentSource segment left.parent) (rightSource :
      SegmentSource segment right.parent)
    (leftMoving : left.last ≠ left.first) (rightMoving : right.last ≠ right.first)
    {lower upper : Basic.Canonical} (leftGeometry :
      Presents left lower upper) (rightGeometry :
      Presents right lower upper)
    (shared : FaceSharedMeshes budgets numerics) (point : Basic.Canonical) :
    RouteCancellation.canonicalPoint left shared point = RouteCancellation.canonicalPoint right shared point := by
  have same (first : left.fragment.source.start = right.fragment.source.start)
      (last : left.fragment.source.finish = right.fragment.source.finish) :=
    RouteCancellation.canonicalPoint_eq_of_junction joined roots first last
      (SourceDirection.routeForward_eq_of_source leftSource rightSource leftMoving rightMoving first last) shared point
  have opposite (first : left.fragment.source.start = right.fragment.source.finish)
      (last : left.fragment.source.finish = right.fragment.source.start) :=
    ReverseRoutes.canonicalPoint_eq_reverse (left.occurrence.edge_eq_of_reverse_query_junction right.occurrence joined
      roots first last)
      (SourceDirection.routeForward_reverse_of_source leftSource rightSource leftMoving rightMoving first last) shared
        point
  rcases leftGeometry with leftGeometry | leftGeometry <;> rcases rightGeometry with rightGeometry | rightGeometry
  · exact same (leftGeometry.1.trans rightGeometry.1.symm) (leftGeometry.2.trans rightGeometry.2.symm)
  · exact opposite (leftGeometry.1.trans rightGeometry.1.symm) (leftGeometry.2.trans rightGeometry.2.symm)
  · exact opposite (leftGeometry.2.trans rightGeometry.2.symm) (leftGeometry.1.trans rightGeometry.1.symm)
  · exact same (leftGeometry.2.trans rightGeometry.2.symm) (leftGeometry.1.trans rightGeometry.1.symm)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceGeometry

end
