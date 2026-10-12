module
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Flatten

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
public import Purelib.Riemann.RootContinuation.NewtonOmittedHoleDecisions
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Polynomial.Dense.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Materialized omitted-hole decisions for every retained regular face,
with one common reference stage and both oriented sheet-side occurrences. -/
namespace Purelib.Riemann.RootContinuation.NewtonOmittedHoleBank

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests (PerimeterTraceBank)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched (FacePerimeters)
open Purelib.Riemann.RootContinuation.NewtonOmittedHoleDecisions (OmittedHoleDecision)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandSideReferences (BandSideReference)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}
  {grid : NewtonGrid preparation target radius} {lifted : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank lifted.frames
    grid.faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
  {meshTarget : Rational} {i j : Fin genus}
  {request : TwoSheetRequest (fun sheet =>
    RegularMeshes.build domains cuts sheet
    coarseDepth) fixed meshTarget}

open Purelib.Curves.Hyperelliptic in
set_option genInjectivity false in
/-- The four retained omitted-hole decisions for one original regular face. -/
structure OmittedHoleRow (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (traces :
  Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request)
    (i j : Fin genus) (position : Fin grid.faces.regulars.length) where
  /-- The retained original bottom-side omitted-hole decision. -/ bottom : OmittedHoleDecision excision traces i j
    position .bottom
  /-- The retained original right-side omitted-hole decision. -/ right : OmittedHoleDecision excision traces i j
    position .right
  /-- The retained original top-side omitted-hole decision. -/ top : OmittedHoleDecision excision traces i j position
    .top
  /-- The retained original left-side omitted-hole decision. -/ left : OmittedHoleDecision excision traces i j position
    .left

constructive_injectivity OmittedHoleRow

namespace OmittedHoleRow
variable {excision : AllHoleExcision grid lifted} {traces :
  PerimeterTraceBank request}
  {position : Fin grid.faces.regulars.length}

/-- Read the exact retained omitted-hole decision at the original selected side. -/
@[expose] def sideDecision (row : OmittedHoleRow excision traces i j position) : (side : GridSide) → OmittedHoleDecision
  excision traces i j position side
  | .bottom => row.bottom
  | .right => row.right
  | .top => row.top
  | .left => row.left

/-- The maximum stage of the original row's four retained side decisions. -/
@[expose] def index (row : OmittedHoleRow excision traces i j position) : Nat :=
  max (max row.bottom.index row.right.index) (max row.top.index row.left.index)

/-- Every original side-decision stage is bounded by the retained row stage. -/
theorem index_le (row : OmittedHoleRow excision traces i j position) (side : GridSide) : (row.sideDecision side).index ≤
  row.index := by
  cases side with
  | bottom => exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _)
  | right => exact (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_left _ _)
  | top => exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)
  | left => exact (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)

section
open Purelib.Curves.Hyperelliptic
/-- Construct the four original side decisions from the exact retained face-neighbor row. -/
@[expose] def build (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (traces :
  Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request) (i j : Fin genus)
    (position : Fin grid.faces.regulars.length) (neighbors : PuncturedFaces.FaceNeighbors grid.faces
      (grid.faces.regulars[position.val]'position.isLt)) :
    OmittedHoleRow excision traces i j position :=
  ⟨OmittedHoleDecision.build excision traces i j position .bottom neighbors.bottom,
    OmittedHoleDecision.build excision traces i j position .right neighbors.right,
    OmittedHoleDecision.build excision traces i j position .top neighbors.top,
    OmittedHoleDecision.build excision traces i j position .left neighbors.left⟩

/-- Read both sheets' original signed side occurrences in bottom, right, negative top, negative left order. -/
@[expose] def values {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (row : OmittedHoleRow excision traces i j position) (perimeters :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize i j) : List
      Gaussian :=
  [row.bottom.value perimeters 0, row.right.value perimeters 0, -row.top.value perimeters 0, -row.left.value perimeters
    0,
   row.bottom.value perimeters 1, row.right.value perimeters 1, -row.top.value perimeters 1, -row.left.value perimeters
     1]

/-- The retained original face row contributes exactly eight signed sheet-side occurrences. -/
theorem values_length {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (row : OmittedHoleRow excision traces i j position) (perimeters :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize i j) :
    (row.values perimeters).length = 8 := rfl

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A bound for each original side and sheet controls every retained signed row occurrence. -/
theorem values_bound {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (row : OmittedHoleRow excision traces i j position) (perimeters :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize i j)
    {bound : Fraction.Rational} (bounded : ∀ side sheet, Data.Gaussian.Norm.Basic.normSq ((row.sideDecision side).value
      perimeters sheet) ≤ bound) :
    ∀ value ∈ row.values perimeters, Data.Gaussian.Norm.Basic.normSq value ≤ bound := by
  intro value member
  rcases Data.List.Membership.mem_cons.mp member with rfl | member
  · exact bounded .bottom 0
  rcases Data.List.Membership.mem_cons.mp member with rfl | member
  · exact bounded .right 0
  rcases Data.List.Membership.mem_cons.mp member with rfl | member
  · rw [Norm.Basic.normSq_neg]; exact bounded .top 0
  rcases Data.List.Membership.mem_cons.mp member with rfl | member
  · rw [Norm.Basic.normSq_neg]; exact bounded .left 0
  rcases Data.List.Membership.mem_cons.mp member with rfl | member
  · exact bounded .bottom 1
  rcases Data.List.Membership.mem_cons.mp member with rfl | member
  · exact bounded .right 1
  rcases Data.List.Membership.mem_cons.mp member with rfl | member
  · rw [Norm.Basic.normSq_neg]; exact bounded .top 1
  rcases Data.List.Membership.mem_cons.mp member with rfl | member
  · rw [Norm.Basic.normSq_neg]; exact bounded .left 1
  cases member

end OmittedHoleRow

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
set_option genInjectivity false in
/-- A retained omitted-hole decision row for every original regular face with one common reference stage.

The dependent vector preserves original face indices, and the common stage bounds the exact retained stage of every row.
-/
structure OmittedHoleBank (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (traces :
  Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request) (i j : Fin genus) where
  /-- The dependent decision rows indexed by original regular faces. -/ rows : Vector.DependentVector (OmittedHoleRow
    excision traces i j)
  /-- The retained stage covering every exact original row request. -/ index : Nat
  /-- Each retained original row stage is at most the common bank stage. -/ index_ge : ∀ position, (rows.get
    position).index ≤ index

constructive_injectivity OmittedHoleBank

namespace OmittedHoleBank
variable {excision : AllHoleExcision grid lifted} {traces :
  PerimeterTraceBank request}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
/-- Cache the original face-neighbor decisions and retain a stage covering every exact row request. -/
@[expose] def build (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (traces :
  Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request) (i j : Fin genus)
    (neighbors : PuncturedFaces.NeighborBank grid.faces) : OmittedHoleBank excision traces i j :=
  let rows := Vector.DependentVector.ofFn (fun position => OmittedHoleRow.build excision traces i j position
    (neighbors.entries.get position))
  ⟨rows, rows.maximum (fun _ row => row.index), rows.get_le_maximum (fun _ row => row.index)⟩

section
open Purelib.Curves.Hyperelliptic
/-- Flatten the original regular faces' signed sheet-side occurrences in retained finite-index order. -/
@[expose] def values {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (bank : OmittedHoleBank excision traces i j) (perimeters :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize i j) : List
      Gaussian :=
  (List.finRange grid.faces.regulars.length).flatMap (fun p => (bank.rows.get p).values perimeters)

/-- The retained omitted-hole bank contributes exactly eight signed occurrences per original regular face. -/
theorem values_length {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (bank : OmittedHoleBank excision traces i j) (perimeters :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize i j) :
    (bank.values perimeters).length = 8 * grid.faces.regulars.length := by
  have count (positions : List (Fin grid.faces.regulars.length)) :
      (positions.flatMap (fun p => (bank.rows.get p).values perimeters)).length = 8 * positions.length := by
    induction positions with
    | nil => rfl
    | cons p tail ih =>
      rw [Data.List.Flatten.flatMap_cons, Data.List.Append.length_append, OmittedHoleRow.values_length, ih,
        List.length_cons]
      omega
  exact (count _).trans (congrArg (8 * ·) (Data.List.OfFn.Basic.length_ofFn (function := fun i : Fin
    grid.faces.regulars.length => i)))

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
/-- A bound for every original face, side and sheet controls every retained signed bank occurrence. -/
theorem values_bound {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (bank : OmittedHoleBank excision traces i j) (perimeters :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize i j)
    {bound : Fraction.Rational} (bounded : ∀ position side sheet, Data.Gaussian.Norm.Basic.normSq (((bank.rows.get
      position).sideDecision side).value perimeters sheet) ≤ bound) :
    ∀ value ∈ bank.values perimeters, Data.Gaussian.Norm.Basic.normSq value ≤ bound := by
  intro value member
  obtain ⟨position, _, belongs⟩ := Flatten.mem_flatMap.mp member
  exact (bank.rows.get position).values_bound perimeters (bounded position) value belongs

end OmittedHoleBank
end Purelib.Riemann.RootContinuation.NewtonOmittedHoleBank
