module
import Purelib.Data.List.Membership
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchCutCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchRelations
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.GeneratorValuation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.CutIntersection
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.List.Append
open Purelib.Algebra.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchCutCoordinates

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchRelations

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Data.Gaussian

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing

@[expose] public section

/-! Actual reference-pair word relations induce the corresponding integer intersection relations. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchIntersectionRelations

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Pair)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchCutCoordinates (ReferenceCutBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchCutCoordinates.Pair (CutCoordinates)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (ClosedCoordinates)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing

/-- The real coordinate of an integer cast to Gaussian rationals is its original rational integer cast. -/
private theorem gaussian_int_re (value : Int) :
    (value : Data.Gaussian.Basic.Canonical).re = (value : Fraction.Rational) := by
  cases value with
  | ofNat value =>
      change (((value : Nat) : Int) : Data.Gaussian.Basic.Canonical).re = (((value : Nat) : Int) : Fraction.Rational)
      rw [Int.cast_natCast, Cast.natCast_re, Int.cast_natCast]
  | negSucc value => rw [IntCast.cast_negSucc, Data.Gaussian.Basic.neg_re,
      Cast.natCast_re, IntCast.cast_negSucc]

/-- Equality of the actual Gaussian integer casts implies equality of the original integers. -/
private theorem gaussian_int_injective {first last : Int} (same : (first : Data.Gaussian.Basic.Canonical) = (last :
  Data.Gaussian.Basic.Canonical)) : first = last := by
  apply Fraction.Cast.Compatibility.intCast_injective_direct
  have realPart := congrArg Data.Gaussian.Basic.Canonical.re same
  rw [gaussian_int_re,
    gaussian_int_re] at realPart
  exact realPart

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
  {first last reference : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {sheet : Fin 2}

namespace Pair.CutCoordinates
variable {pair :
  Pair bank first
  last sheet} {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord
  lifted.cutBoundaryWord}

/-- Reuse the exact route, integer row and spanning certificate of the retained pair. -/
def asClosed (coordinates : Pair.CutCoordinates pair integral) : PeriodCoordinates.ClosedCoordinates pair.closed.indexed
  integral :=
  ⟨coordinates.route, coordinates.coordinates, coordinates.span⟩

end Pair.CutCoordinates

namespace Pair

/-- The actual repeated branch-pair word has zero generator valuation because its original physical boundary loop is
certified zero. -/
theorem repeated_value_zero (pair : BasedBranchBank.Pair bank last last sheet)
    {values : Data.Vector Data.Gaussian.Basic.Canonical lifted.cutBoundaryWord.alphabet.count}
    (valuation : Cut.GeneratorValuation lifted values) : SewingRetraction.wordValue valuation.value
      pair.closed.indexed = 0 := by
  match base.faces.locateCell (base.bank.cell last) (base.bank.cell_mem last) with
  | .regular found => exact (found.face.unassigned last found.cell_eq).elim
  | .hole found =>
      have equal : found.hole.index = last := FaceKind.branch_unique found.hole.cell_eq found.cell_eq
      have retained : found.hole ∈ base.faces.holes := by
        rw [← found.indexed]
        exact List.getElem_mem found.index.isLt
      have boundaryMember : found.hole.liftedBoundary lifted.vertices lifted.edges ∈ lifted.boundaryLoops :=
        Membership.mem_append.mpr (Or.inr (Map.mem_map_of_mem retained))
      have zero := valuation.boundary_zero _ boundaryMember
      have move (index : BranchIsolation.Data.Index branches) (same : found.hole.index = index)
          (loop : BasedBranchBank.Pair bank index index sheet) : SewingRetraction.wordValue valuation.value
            loop.closed.indexed = 0 := by
        cases same
        rw [Pair.repeated_hole_value
          found.hole loop valuation.value valuation.value_reverse, zero, neg_zero]
      exact move last equal pair

/-- The physical double branch circuit is eliminated by its actual boundary-loop certificate. -/
theorem reference_value_closed (pair : BasedBranchBank.Pair bank first last sheet)
    (firstReference : BasedBranchBank.Pair bank first reference sheet) (lastReference : BasedBranchBank.Pair bank last
      reference sheet)
    {values : Data.Vector Data.Gaussian.Basic.Canonical lifted.cutBoundaryWord.alphabet.count}
    (valuation : Cut.GeneratorValuation lifted values) :
    SewingRetraction.wordValue valuation.value pair.closed.indexed = SewingRetraction.wordValue valuation.value
      firstReference.closed.indexed -
      SewingRetraction.wordValue valuation.value lastReference.closed.indexed := by
  rw [Pair.reference_value pair firstReference lastReference (bank.pair last last sheet),
    repeated_value_zero
      (bank.pair last last sheet) valuation, add_zero]

end Pair

namespace ReferenceCutBank
variable (cut : ReferenceCutBank bank
  reference sheet)
  {word : List (Purelib.Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count)}
  (right : ClosedCoordinates word
    cut.integral)

/-- This is the integer intersection relation of the actual pair words, with their face corrections discharged. -/
theorem reference_intersection (pair : BasedBranchBank.Pair bank first last sheet) (coordinates : Pair.CutCoordinates
  pair cut.integral) :
    SpanningCoordinates.intersection coordinates.span right.span = SpanningCoordinates.intersection (cut.rows.get
      first).cut.span right.span -
      SpanningCoordinates.intersection (cut.rows.get last).cut.span right.span := by
  have relation :=
    Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchIntersectionRelations.Pair.reference_value_closed pair
    (cut.rows.get first).pair (cut.rows.get last).pair (ClosedCoordinates.dualValuation right)
  rw [ClosedCoordinates.intersection_value right
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchIntersectionRelations.Pair.CutCoordinates.asClosed
        coordinates),
    ClosedCoordinates.intersection_value right
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchIntersectionRelations.Pair.CutCoordinates.asClosed
        (cut.rows.get first).cut),
    ClosedCoordinates.intersection_value right
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchIntersectionRelations.Pair.CutCoordinates.asClosed
        (cut.rows.get last).cut)] at relation
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchIntersectionRelations.gaussian_int_injective
  rw [IntCast.sub]
  exact relation

end ReferenceCutBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchIntersectionRelations

