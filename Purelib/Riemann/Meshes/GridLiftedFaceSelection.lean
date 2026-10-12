module
meta import Purelib.Elab.ConstructiveInjectivity
-- The exposed partition builder retains the original filter cache certificates.
public import Purelib.Data.List.Filter
import Purelib.Data.List.Membership
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Selecting faces from a retained two-sheeted mesh

The selection copies the original lifted quadrilaterals. It does not rebuild
root frames, edge transports or corner sheet assignments. Both membership
and the exact complementary triangle sum refer to the original mesh data.
-/

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
namespace Purelib.Riemann.Meshes.GridLiftedFaceSelection

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (OrientedTriangle)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedFaces)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

/-- Transport retained face lifts along equality of their original ordered face lists. -/
def reindex {faces other : List (RegularFace bank)} (lifts : LiftedFaces vertices edges faces) (equal : faces = other) :
    LiftedFaces vertices edges other := equal ▸ lifts

/-- Exact face-list transport preserves the original retained triangle list. -/
theorem reindex_triangles {faces other : List (RegularFace bank)} (lifts : LiftedFaces vertices edges faces) (equal :
  faces = other) :
    (reindex lifts equal).triangles = lifts.triangles := by
  cases equal
  rfl

open Purelib.RootIsolation in
set_option genInjectivity false in
/-- A predicate partition of original lifted faces retaining both selected and rejected lifts.

The cached face lists equal the original positive and negative filters, and both sides reuse the exact original sheet
lifts in order. -/
structure Selection (vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid) (edges :
  SquareRoot.Grid.RootEdgeBank frames)
    (keep : RegularFace bank → Bool) (faces : List (RegularFace bank)) where
  /-- The cached original faces satisfying the retained predicate, in order. -/ kept : List (RegularFace bank)
  /-- The kept cache equals the exact original positive filter. -/ kept_eq : kept = faces.filter keep
  /-- The cached original faces failing the retained predicate, in order. -/ discarded : List (RegularFace bank)
  /-- The discarded cache equals the exact original negative filter. -/ discarded_eq : discarded = faces.filter (fun
    face => !(keep face))
  /-- Both original sheet lifts for the exact kept face list. -/ selected : LiftedFaces vertices edges kept
  /-- Both original sheet lifts for the exact discarded face list. -/ rejected : LiftedFaces vertices edges discarded

constructive_injectivity Selection

/-- Partition original lifted faces by a Boolean predicate while retaining both original sheet lifts on the chosen side.

Each recursive branch keeps the exact filtered face-list equation and reuses the retained head quadrilaterals and tail
selections. -/
def select (keep : RegularFace bank → Bool) : {faces : List (RegularFace bank)} →
    LiftedFaces vertices edges faces → Selection vertices edges keep faces
  | _, .nil => ⟨[], rfl, [], rfl, .nil, .nil⟩
  | face :: _, .cons zero one tail =>
      let rest := select keep tail
      if kept : keep face then
        { kept := face :: rest.kept
          kept_eq := (congrArg (List.cons face) rest.kept_eq).trans
            (Filter.filter_cons_of_pos kept).symm
          discarded := rest.discarded
          discarded_eq := by
            have rejected : (!(keep face)) ≠ true := by
              rw [kept]
              intro impossible
              nomatch impossible
            exact rest.discarded_eq.trans (Filter.filter_cons_of_neg (predicate := fun item => !(keep item)) (head :=
              face) rejected).symm
          selected := .cons zero one rest.selected
          rejected := rest.rejected }
      else
        { kept := rest.kept
          kept_eq := rest.kept_eq.trans (Filter.filter_cons_of_neg kept).symm
          discarded := face :: rest.discarded
          discarded_eq := by
            have accepted : (!(keep face)) = true := by
              cases selected : keep face with
              | false => rfl
              | true => exact (kept selected).elim
            exact (congrArg (List.cons face) rest.discarded_eq).trans
              (Filter.filter_cons_of_pos (predicate := fun item => !(keep item)) (head := face) accepted).symm
          selected := rest.selected
          rejected := .cons zero one rest.rejected }

section
open Purelib.Riemann.Meshes
/-- The original selected triangle list keeps all four head triangles exactly when its face satisfies the predicate. -/
private theorem selected_cons_eq (keep : RegularFace bank → Bool) {face : RegularFace bank} {faces : List (RegularFace
  bank)}
    (zero : GridLiftedFaces.BranchCellBank.LiftedFace vertices edges face 0)
    (one : GridLiftedFaces.BranchCellBank.LiftedFace vertices edges face 1) (tail : LiftedFaces vertices edges faces) :
    (select keep (.cons zero one tail)).selected.triangles =
      if keep face then zero.quad.firstTriangle :: zero.quad.secondTriangle :: one.quad.firstTriangle ::
        one.quad.secondTriangle :: (select keep tail).selected.triangles else (select keep tail).selected.triangles :=
          by
  by_cases kept : keep face = true
  · have equal := congrArg (fun result : Selection vertices edges keep (face :: faces) => result.selected.triangles)
      (show select keep (.cons zero one tail) = _ from dif_pos kept)
    exact equal.trans (if_pos kept).symm
  · have equal := congrArg (fun result : Selection vertices edges keep (face :: faces) => result.selected.triangles)
      (show select keep (.cons zero one tail) = _ from dif_neg kept)
    exact equal.trans (if_neg kept).symm

/-- The original rejected triangle list keeps all four head triangles exactly when its face fails the predicate. -/
private theorem rejected_cons_eq (keep : RegularFace bank → Bool) {face : RegularFace bank} {faces : List (RegularFace
  bank)}
    (zero : GridLiftedFaces.BranchCellBank.LiftedFace vertices edges face 0)
    (one : GridLiftedFaces.BranchCellBank.LiftedFace vertices edges face 1) (tail : LiftedFaces vertices edges faces) :
    (select keep (.cons zero one tail)).rejected.triangles =
      if keep face then (select keep tail).rejected.triangles else
        zero.quad.firstTriangle :: zero.quad.secondTriangle :: one.quad.firstTriangle ::
          one.quad.secondTriangle :: (select keep tail).rejected.triangles := by
  by_cases kept : keep face = true
  · have equal := congrArg (fun result : Selection vertices edges keep (face :: faces) => result.rejected.triangles)
      (show select keep (.cons zero one tail) = _ from dif_pos kept)
    exact equal.trans (if_pos kept).symm
  · have equal := congrArg (fun result : Selection vertices edges keep (face :: faces) => result.rejected.triangles)
      (show select keep (.cons zero one tail) = _ from dif_neg kept)
    exact equal.trans (if_neg kept).symm

end

/-- Every retained selected triangle belongs to the original lifted triangle list.

Structural membership retains the selected original head triangles or the
unchanged selected tail. Every occurrence therefore keeps its original mesh
triangle witness. -/
theorem select_triangle_mem (keep : RegularFace bank → Bool) :
    {faces : List (RegularFace bank)} → (lifts : LiftedFaces vertices edges faces) →
      ∀ triangle ∈ (select keep lifts).selected.triangles, triangle ∈ lifts.triangles
  | _, .nil, _, member => (List.not_mem_nil member).elim
  | face :: _, .cons zero one tail, triangle, member => by
      rw [selected_cons_eq] at member
      by_cases kept : keep face = true
      · rw [if_pos kept] at member
        change triangle ∈ _ :: _ :: _ :: _ :: tail.triangles
        rcases Membership.mem_cons.mp member with rfl | member
        · exact List.mem_cons_self
        apply List.mem_cons_of_mem
        rcases Membership.mem_cons.mp member with rfl | member
        · exact List.mem_cons_self
        apply List.mem_cons_of_mem
        rcases Membership.mem_cons.mp member with rfl | member
        · exact List.mem_cons_self
        apply List.mem_cons_of_mem
        rcases Membership.mem_cons.mp member with rfl | member
        · exact List.mem_cons_self
        exact List.mem_cons_of_mem _ (select_triangle_mem keep tail triangle member)
      · rw [if_neg kept] at member
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (select_triangle_mem keep tail triangle member))))

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Meshes in
/-- Selected and rejected original triangle sums add to the complete retained triangle sum. -/
theorem select_sum (keep : RegularFace bank → Bool) (value : OrientedTriangle vertices.count → Basic.Canonical) :
    {faces : List (RegularFace bank)} → (lifts : LiftedFaces vertices edges faces) →
      Geometry.Grid.CellBoundary.sumValues value (select keep lifts).selected.triangles +
        Geometry.Grid.CellBoundary.sumValues value (select keep lifts).rejected.triangles =
          Geometry.Grid.CellBoundary.sumValues value lifts.triangles
  | _, .nil => by change (0 : Basic.Canonical) + 0 = 0; exact zero_add _
  | face :: _, .cons zero one tail => by
      rw [selected_cons_eq, rejected_cons_eq]
      by_cases kept : keep face = true
      · simp only [if_pos kept, GridLiftedMesh.LiftedFaces.triangles,
          Geometry.Grid.CellBoundary.sumValues, -eq_self, -iff_self]
        rw [← select_sum keep value tail]
        ring1
      · simp only [if_neg kept, GridLiftedMesh.LiftedFaces.triangles,
          Geometry.Grid.CellBoundary.sumValues, -eq_self, -iff_self]
        rw [← select_sum keep value tail]
        ring1

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- For disjoint original face predicates, their union's triangle sum equals the two separate selected sums.

The two disjoint tests retain the original four triangles in at most one
selection at each head. Scalar Boolean splitting preserves the original
selected tails and their exact triangle sums. -/
theorem select_or_sum (first second : RegularFace bank → Bool)
    (disjoint : ∀ face, first face = true → second face = true → False)
    (value : OrientedTriangle vertices.count → Basic.Canonical) :
    {faces : List (RegularFace bank)} → (lifts : LiftedFaces vertices edges faces) →
      Geometry.Grid.CellBoundary.sumValues value (select (fun face => first face || second face)
        lifts).selected.triangles =
        Geometry.Grid.CellBoundary.sumValues value (select first lifts).selected.triangles +
          Geometry.Grid.CellBoundary.sumValues value (select second lifts).selected.triangles
  | _, .nil => by change (0 : Basic.Canonical) = 0 + 0; exact (zero_add _).symm
  | face :: _, .cons zero one tail => by
      rw [selected_cons_eq, selected_cons_eq, selected_cons_eq]
      cases left : first face with
      | false =>
          cases right : second face with
          | false =>
              simp only [Bool.false_or, if_neg Bool.false_ne_true]
              exact select_or_sum first second disjoint value tail
          | true =>
              simp only [Bool.false_or, if_neg Bool.false_ne_true,
                if_pos rfl, Geometry.Grid.CellBoundary.sumValues, -eq_self, -iff_self]
              rw [select_or_sum first second disjoint value tail]
              ring1
      | true =>
          cases right : second face with
          | false =>
              simp only [Bool.or_false, if_neg Bool.false_ne_true,
                if_pos rfl, Geometry.Grid.CellBoundary.sumValues, -eq_self, -iff_self]
              rw [select_or_sum first second disjoint value tail]
              ring1
          | true => exact (disjoint face left right).elim

/-- The constantly false face predicate retains no original triangles. -/
private theorem select_false_triangles : {faces : List (RegularFace bank)} →
    (lifts : LiftedFaces vertices edges faces) → (select (fun _ => false) lifts).selected.triangles = []
  | _, .nil => rfl
  | _, .cons zero one tail => by
      rw [selected_cons_eq, if_neg Bool.false_ne_true]
      exact select_false_triangles tail

/-- A true finite-list Boolean search has an explicit original member satisfying the test. -/
private theorem any_true_witness {Label : Type} (test : Label → Bool) :
    (labels : List Label) → labels.any test = true → ∃ label ∈ labels, test label = true
  | [], found => Bool.noConfusion found
  | head :: tail, found => by
      by_cases kept : test head = true
      · exact ⟨head, List.mem_cons_self, kept⟩
      · have no : test head = false := Bool.eq_false_iff.mpr kept
        have rest : tail.any test = true := by
          change (test head || tail.any test) = true at found
          rw [no] at found
          exact found
        obtain ⟨label, member, kept⟩ := any_true_witness test tail rest
        exact ⟨label, List.mem_cons_of_mem _ member, kept⟩

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- A finite pairwise disjoint family of face predicates partitions the union's original selected triangle sum.

The proof keeps the original label list and each selection's retained triangles, combining finite sums through disjoint
unions. -/
theorem select_family_sum {Label : Type} (keep : Label → RegularFace bank → Bool)
    (value : OrientedTriangle vertices.count → Basic.Canonical) (labels : List Label)
    (disjoint : labels.Pairwise (fun first second => ∀ face,
      keep first face = true → keep second face = true → False))
    {faces : List (RegularFace bank)} (lifts : LiftedFaces vertices edges faces) :
    Geometry.Grid.CellBoundary.sumValues value (select (fun face => labels.any (fun label => keep label face))
      lifts).selected.triangles =
      Geometry.Grid.CellBoundary.sumValues (fun label => Geometry.Grid.CellBoundary.sumValues value (select (keep label)
        lifts).selected.triangles) labels := by
  induction labels with
  | nil => exact congrArg (Geometry.Grid.CellBoundary.sumValues value) (select_false_triangles lifts)
  | cons head tail ih =>
      have separate : ∀ face, keep head face = true → tail.any (fun label => keep label face) = true → False := by
        intro face kept found
        obtain ⟨label, member, keptTail⟩ := any_true_witness (fun label => keep label face) tail found
        exact (List.pairwise_cons.mp disjoint).1 label member face kept keptTail
      change Geometry.Grid.CellBoundary.sumValues value (select (fun face => keep head face || tail.any (fun label =>
        keep label face)) lifts).selected.triangles = _
      rw [select_or_sum _ _ separate value lifts, ih (List.pairwise_cons.mp disjoint).2]
      rfl

end Purelib.Riemann.Meshes.GridLiftedFaceSelection
