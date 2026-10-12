module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Mesh.RetracingWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleAreaRequests
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchRemainders
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

open Purelib.Riemann

public section

/-! Look up the existing physical hole for each branch label and retain one
area request per hole. A proved reindexing identifies the resulting sum with
the entire physical-hole list, not an unrelated enumeration of boundaries. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleBank

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- The original physical hole and its paid area request for one retained branch label.

The certified location and branch equality keep the request tied to the actual physical-hole list. -/
structure HoleRowRequest (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  differential) (target : Fraction.Rational)
    (branch : Hyperelliptic.Branches.BranchIsolation.Data.Index branches) where
  /-- The actual physical-hole location in the original face list. -/ location : Meshes.PuncturedGridFaces.HoleLocation
    base.faces.holes (base.bank.cell branch)
  /-- The retained physical hole has the requested original branch label. -/ branch_eq : location.hole.index = branch
  /-- The paid area request on that exact retained physical hole. -/ request :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleAreaRequests.HoleAreaRequest fixed location.hole target

constructive_injectivity HoleRowRequest

namespace HoleRowRequest

variable {fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential} {target
  : Fraction.Rational} {branch : Hyperelliptic.Branches.BranchIsolation.Data.Index branches}

/-- Find the original physical hole for the branch label and prepare its paid area request. -/
@[expose] def build (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  differential) (target : Fraction.Rational) (positive : 0 < target)
    (branch : Hyperelliptic.Branches.BranchIsolation.Data.Index branches) :
      Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleBank.HoleRowRequest fixed target branch :=
  match base.faces.locateCell (base.bank.cell branch) (base.bank.cell_mem branch) with
  | .regular found => (found.face.unassigned branch found.cell_eq).elim
  | .hole found => ⟨found, Hyperelliptic.Branches.BranchFaceClassification.FaceKind.branch_unique found.hole.cell_eq
    found.cell_eq, Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleAreaRequests.HoleAreaRequest.build fixed found.hole
    target positive⟩

/-- The selected physical hole belongs to the original complete hole list. -/
theorem retained (row : Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleBank.HoleRowRequest fixed target branch) :
  row.location.hole ∈ base.faces.holes :=
  row.location.indexed ▸ List.getElem_mem row.location.index.isLt

/-- Original holes with the same branch label have the same lifted physical boundary. -/
private theorem boundary_eq {first last : Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank} (same :
  first.index = last.index) :
    first.liftedBoundary lifted.vertices lifted.edges = last.liftedBoundary lifted.vertices lifted.edges := by
  rcases first with ⟨index, cell, member, cellEq, state, boxEq⟩
  rcases last with ⟨other, otherCell, otherMember, otherEq, otherState, otherBoxEq⟩
  change index = other at same
  cases same
  cases cellEq
  cases otherEq
  rfl

/-- The retained request's physical boundary equals that of any original hole with the same branch label. -/
theorem boundary_readback (row : Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleBank.HoleRowRequest fixed target branch)
  (hole : Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank)
    (same : hole.index = branch) :
    row.location.hole.liftedBoundary lifted.vertices lifted.edges = hole.liftedBoundary lifted.vertices lifted.edges :=
  Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleBank.HoleRowRequest.boundary_eq (row.branch_eq.trans same.symm)

/-- Twice the retained branch hole area plus its original clockwise physical boundary area meets the requested target at
every sufficient stage. -/
theorem accurate (row : Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleBank.HoleRowRequest fixed target branch) (bank :
  Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted) (sheet : Fin 2)
    {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage
      domains} (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
      lifted.mesh)
    (later : row.request.index ≤ stage) :
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.values
    Data.Gaussian.Norm.Basic.normSq (bank.holeArea value branch sheet + bank.holeArea value branch sheet +
      Topology.Mesh.RetracingWords.wordArea value (row.location.hole.liftedBoundary lifted.vertices lifted.edges)) ≤
        target := by
  have bound := row.request.corrected_accurate row.retained bank sheet readings later
  dsimp only at bound ⊢
  rw [row.branch_eq] at bound
  change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
  simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using bound

end HoleRowRequest

set_option genInjectivity false in
/-- One retained physical-hole area request per original branch label, with a cached common sufficient stage. -/
structure HoleRequestBank (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  differential) (target : Fraction.Rational) where
  /-- The dependent bank of original hole requests indexed by branch labels. -/ rows : Data.Vector.DependentVector (fun
    branch : Hyperelliptic.Branches.BranchIsolation.Data.Index branches =>
    Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleBank.HoleRowRequest fixed target branch)
  /-- The cached common sufficient stage. -/ index : Nat
  /-- The sufficient stage is exactly the maximum of all retained row stages. -/ index_eq : index = rows.maximum (fun _
    row => row.request.index)

constructive_injectivity HoleRequestBank

namespace HoleRequestBank

variable {fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential} {target
  : Fraction.Rational}

/-- Prepare every original branch hole request and cache their maximum sufficient stage. -/
@[expose] def build (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  differential) (target : Fraction.Rational) (positive : 0 < target) :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleBank.HoleRequestBank fixed target :=
  let rows := Data.Vector.DependentVector.ofFn (Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleBank.HoleRowRequest.build
    fixed target positive)
  ⟨rows, rows.maximum (fun _ row => row.request.index), rfl⟩

/-- Every retained row request is ready by the common bank stage. -/
theorem index_ge (requests : Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleBank.HoleRequestBank fixed target) (branch :
  Hyperelliptic.Branches.BranchIsolation.Data.Index branches) :
    (requests.rows.get branch).request.index ≤ requests.index := by
  rw [requests.index_eq]
  exact requests.rows.get_le_maximum (fun _ row => row.request.index) branch

/-- Read the actual lifted physical boundary area of the retained hole for a branch label. -/
@[expose] def physicalArea (requests : Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleBank.HoleRequestBank fixed target)
  (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (branch : Hyperelliptic.Branches.BranchIsolation.Data.Index branches) : Gaussian :=
  Topology.Mesh.RetracingWords.wordArea value ((requests.rows.get branch).location.hole.liftedBoundary lifted.vertices
    lifted.edges)

/-- A finite indicator sum over distinct keys returns the supplied value when the requested key occurs. -/
private theorem sum_unique {Alpha : Type} {count : Nat} (key : Alpha → Fin count) (index : Fin count) (value :
  Gaussian.Basic.Canonical) :
    ∀ (entries : List Alpha), entries.Pairwise (fun first second => key first ≠ key second) →
      (∃ entry ∈ entries, key entry = index) →
      Geometry.Grid.CellBoundary.sumValues (fun entry => if key entry = index then value else 0) entries = value
  | [], _, found => by obtain ⟨_, member, _⟩ := found; cases member
  | head :: tail, unique, found => by
      by_cases same : key head = index
      · rw [Geometry.Grid.CellBoundary.sumValues, if_pos same]
        have tailZero : Geometry.Grid.CellBoundary.sumValues (fun entry => if key entry = index then value else 0) tail
          = 0 := by
          rw [Geometry.Grid.CellBoundary.sumValues_congr _ (fun _ => 0) tail (by
            intro entry member
            have different : key entry ≠ index := fun equal =>
              (List.pairwise_cons.mp unique).1 entry member (same.trans equal.symm)
            rw [if_neg different]), Geometry.Grid.CellBoundary.sumValues_zero]
        rw [tailZero, add_zero]
      · rw [Geometry.Grid.CellBoundary.sumValues, if_neg same, zero_add]
        apply Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleBank.HoleRequestBank.sum_unique key index
          value tail (List.pairwise_cons.mp unique).2
        obtain ⟨entry, member, equal⟩ := found
        rcases Data.List.Membership.mem_cons.mp member with rfl | member
        · exact (same equal).elim
        · exact ⟨entry, member, equal⟩

/-- Completeness and uniqueness of both retained lists, not their lengths,
justify the sum reindexing. Only finite indicator sums are used. -/
theorem physical_sum (requests : Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleBank.HoleRequestBank fixed target) (value
  : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    {bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin
      2} (ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
      sheet) :
    Geometry.Grid.CellBoundary.sumValues (requests.physicalArea value) ordered.prepared.labels =
      Geometry.Grid.CellBoundary.sumValues (fun hole => Topology.Mesh.RetracingWords.wordArea value (hole.liftedBoundary
        lifted.vertices lifted.edges)) base.faces.holes := by
  have expand (branch : Hyperelliptic.Branches.BranchIsolation.Data.Index branches) :
      requests.physicalArea value branch = Geometry.Grid.CellBoundary.sumValues
        (fun hole => if hole.index = branch then requests.physicalArea value branch else 0) base.faces.holes :=
    (Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleBank.HoleRequestBank.sum_unique (fun hole => hole.index) branch _
      base.faces.holes base.faces.holes_pairwise (base.faces.hole_complete branch)).symm
  rw [Geometry.Grid.CellBoundary.sumValues_congr _ _ ordered.prepared.labels (fun branch _ => expand branch),
    Geometry.Grid.CellBoundary.sumValues_swap]
  apply Geometry.Grid.CellBoundary.sumValues_congr
  intro hole _
  have scalar : Geometry.Grid.CellBoundary.sumValues (fun branch => if hole.index = branch then requests.physicalArea
    value branch else 0) ordered.prepared.labels =
      Geometry.Grid.CellBoundary.sumValues (fun branch => if branch = hole.index then requests.physicalArea value
        hole.index else 0) ordered.prepared.labels := by
    apply Geometry.Grid.CellBoundary.sumValues_congr
    intro branch _
    by_cases same : branch = hole.index
    · cases same
      rw [if_pos rfl]
    · rw [if_neg same, if_neg (Ne.symm same)]
  rw [scalar, Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleBank.HoleRequestBank.sum_unique (fun branch => branch)
    hole.index _ ordered.prepared.labels ordered.prepared.unique
    ⟨hole.index, ordered.complete hole.index, rfl⟩]
  exact congrArg (Topology.Mesh.RetracingWords.wordArea value) ((requests.rows.get hole.index).boundary_readback hole
    rfl)

end HoleRequestBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleBank
