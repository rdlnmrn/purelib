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
public import Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceDecisions
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Materialized selected-interface decisions for every retained regular face,
with one common reference stage and both oriented sheet-side occurrences. -/
namespace Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceBank

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
open Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceDecisions (InterfaceDecision)
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
/-- The four retained interface decisions of one original regular face.

Each side retains its own exact classification, neighboring face and allocated request under the same original excision,
trace owner and differential pair. -/
structure InterfaceRow (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (traces :
  Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request)
    (i j : Fin genus) (position : Fin grid.faces.regulars.length) where
  /-- The retained original bottom-side interface decision. -/ bottom : InterfaceDecision excision traces i j position
    .bottom
  /-- The retained original right-side interface decision. -/ right : InterfaceDecision excision traces i j position
    .right
  /-- The retained original top-side interface decision. -/ top : InterfaceDecision excision traces i j position .top
  /-- The retained original left-side interface decision. -/ left : InterfaceDecision excision traces i j position .left

constructive_injectivity InterfaceRow

namespace InterfaceRow
variable {excision : AllHoleExcision grid lifted} {traces :
  PerimeterTraceBank request}
  {position : Fin grid.faces.regulars.length}

/-- Select the retained decision for the requested original side. -/
@[expose] def sideDecision (row : InterfaceRow excision traces i j position) : (side : GridSide) → InterfaceDecision
  excision traces i j position side
  | .bottom => row.bottom
  | .right => row.right
  | .top => row.top
  | .left => row.left

/-- Take a common stage covering all four retained side decisions. -/
@[expose] def index (row : InterfaceRow excision traces i j position) : Nat :=
  max (max row.bottom.index row.right.index) (max row.top.index row.left.index)

/-- Each original side decision's stage is bounded by the retained row stage. -/
theorem index_le (row : InterfaceRow excision traces i j position) (side : GridSide) : (row.sideDecision side).index ≤
  row.index := by
  cases side with
  | bottom => exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _)
  | right => exact (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_left _ _)
  | top => exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)
  | left => exact (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)

section
open Purelib.Curves.Hyperelliptic
/-- Classify all four original side neighbors and retain their exact interface decisions. -/
@[expose] def build (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (traces :
  Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request) (i j : Fin genus)
    (position : Fin grid.faces.regulars.length) (neighbors : PuncturedFaces.FaceNeighbors grid.faces
      (grid.faces.regulars[position.val]'position.isLt)) :
    InterfaceRow excision traces i j position :=
  ⟨InterfaceDecision.build excision traces i j position .bottom neighbors.bottom,
    InterfaceDecision.build excision traces i j position .right neighbors.right,
    InterfaceDecision.build excision traces i j position .top neighbors.top,
    InterfaceDecision.build excision traces i j position .left neighbors.left⟩

/-- Read the eight signed original side occurrences, with sheet zero followed by sheet one. -/
@[expose] def values {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (row : InterfaceRow excision traces i j position) (perimeters :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize i j) : List
      Gaussian :=
  [row.bottom.value perimeters 0, row.right.value perimeters 0, -row.top.value perimeters 0, -row.left.value perimeters
    0,
   row.bottom.value perimeters 1, row.right.value perimeters 1, -row.top.value perimeters 1, -row.left.value perimeters
     1]

/-- The original interface row contains exactly eight signed sheet-side occurrences. -/
theorem values_length {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (row : InterfaceRow excision traces i j position) (perimeters :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize i j) :
    (row.values perimeters).length = 8 := rfl

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A common bound for the four original decisions on both sheets bounds every signed row occurrence. -/
theorem values_bound {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (row : InterfaceRow excision traces i j position) (perimeters :
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

end InterfaceRow

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
set_option genInjectivity false in
/-- Dependent interface rows indexed by the original regular faces and a retained common stage.

The bank preserves each exact face index and certifies that its cached common stage covers every original row. -/
structure InterfaceBank (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (traces :
  Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request) (i j : Fin genus) where
  /-- The dependent cached interface rows at the exact original face indices. -/ rows : Vector.DependentVector
    (InterfaceRow excision traces i j)
  /-- The retained common stage for all original interface rows. -/ index : Nat
  /-- Each exact cached row's stage lies below the retained common stage. -/ index_ge : ∀ position, (rows.get
    position).index ≤ index

constructive_injectivity InterfaceBank

namespace InterfaceBank
variable {excision : AllHoleExcision grid lifted} {traces :
  PerimeterTraceBank request}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
/-- Build the dependent original face rows and retain their exact maximum request stage.

Every row consumes the corresponding retained neighbor entry, preserving the original bounded face index and both
differential owners. -/
@[expose] def build (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (traces :
  Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request) (i j : Fin genus)
    (neighbors : PuncturedFaces.NeighborBank grid.faces) : InterfaceBank excision traces i j :=
  let rows := Vector.DependentVector.ofFn (fun position => InterfaceRow.build excision traces i j position
    (neighbors.entries.get position))
  ⟨rows, rows.maximum (fun _ row => row.index), rows.get_le_maximum (fun _ row => row.index)⟩

section
open Purelib.Curves.Hyperelliptic
/-- Flatten the exact cached rows in original bounded-face order, preserving all signed sheet-side occurrences. -/
@[expose] def values {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (bank : InterfaceBank excision traces i j) (perimeters :
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
      (request := request) cache.normalize i j) : List Gaussian :=
  (List.finRange grid.faces.regulars.length).flatMap (fun p => (bank.rows.get p).values perimeters)

/-- The retained bank contains eight signed occurrences per original regular face. -/
theorem values_length {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (bank : InterfaceBank excision traces i j) (perimeters :
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
      (request := request) cache.normalize i j) :
    (bank.values perimeters).length = 8 * grid.faces.regulars.length := by
  have count (positions : List (Fin grid.faces.regulars.length)) :
      (positions.flatMap (fun p => (bank.rows.get p).values perimeters)).length = 8 * positions.length := by
    induction positions with
    | nil => rfl
    | cons p tail ih =>
      rw [Data.List.Flatten.flatMap_cons, Data.List.Append.length_append, InterfaceRow.values_length, ih,
        List.length_cons]
      omega
  exact (count _).trans (congrArg (8 * ·) (Data.List.OfFn.Basic.length_ofFn (function := fun i : Fin
    grid.faces.regulars.length => i)))

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
/-- The common original face, side and sheet bound controls every occurrence in the retained bank. -/
theorem values_bound {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (bank : InterfaceBank excision traces i j) (perimeters :
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
      (request := request) cache.normalize i j)
    {bound : Fraction.Rational} (bounded : ∀ position side sheet, Data.Gaussian.Norm.Basic.normSq (((bank.rows.get
      position).sideDecision side).value perimeters sheet) ≤ bound) :
    ∀ value ∈ bank.values perimeters, Data.Gaussian.Norm.Basic.normSq value ≤ bound := by
  intro value member
  obtain ⟨position, _, belongs⟩ := Flatten.mem_flatMap.mp member
  exact (bank.rows.get position).values_bound perimeters (bounded position) value belongs

end InterfaceBank
end Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceBank
