module

import Purelib.Data.List.Flatten
import Purelib.Data.List.Append
import Purelib.Data.List.OfFn.Basic

public import Purelib.Curves.Hyperelliptic.Topology.BranchProfile
import Purelib.Topology.BranchedCover
public import Purelib.Topology.BranchedCover.Double.Attachment
import Init.Data.List.OfFn
import Init.Prelude
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Curves.Hyperelliptic.Topology

open Purelib.Data.List

open Purelib.Topology.BranchedCover.Double

open Purelib.Topology.BranchedCover.Double.Attachment

public section

/-!
# Explicit hyperelliptic double-cover attaching data

The count-only model is refined here to an actual finite combinatorial
attaching model.  The base sphere is cut along an equatorial polygon.  Every
base edge has two labelled lifts.  Upper-hemisphere boundaries retain the
sheet label; lower-hemisphere boundaries use an explicit alternating sheet
trivialization.  At a ramified vertex the two labels have one common fibre
vertex, while at the unramified even-degree point at infinity they remain
separate.

Each face boundary is represented by a finite cyclic edge family with a
proof that the target of every displayed edge is the source of its successor.
Thus the model carries attaching incidence, not only Euler counts.
-/

namespace Purelib.Curves.Hyperelliptic.Topology.Cells

open Purelib.Topology.BranchedCover

/-! ## Odd degree: every displayed base vertex is ramified -/

/-- The number of ramified polygon vertices in the odd-degree double cover. -/
@[expose] def oddBaseCount (genus : Nat) : Nat := 2 * genus + 2

/-- The odd-degree base polygon has at least one vertex. -/
theorem oddBasePositive (genus : Nat) : 0 < oddBaseCount genus := by
  unfold oddBaseCount
  omega0

/-- The finite labels of the odd-degree ramified vertices. -/
abbrev OddVertex (genus : Nat) := Fin (oddBaseCount genus)

/-- Both sheet labels meet at the retained ramified base vertex. -/
@[expose] def oddVertexAbove {genus : Nat} (base : Fin (oddBaseCount genus))
    (_sheet : Attachment.Sheet) : OddVertex genus :=
  base

/-- Read the source vertex of an odd-degree lifted polygon edge. -/
@[expose] def oddEdgeStart {genus : Nat} (edge : Attachment.Edge (oddBaseCount genus)) :
    OddVertex genus :=
  oddVertexAbove edge.base edge.sheet

/-- Read the cyclic successor vertex of an odd-degree lifted polygon edge. -/
@[expose] def oddEdgeFinish {genus : Nat} (edge : Attachment.Edge (oddBaseCount genus)) :
    OddVertex genus :=
  oddVertexAbove
    (Attachment.cyclicSucc (oddBasePositive genus) edge.base) edge.sheet

/-- The alternating lower-hemisphere sheet along one base edge. -/
@[expose] def oddLowerSheet {genus : Nat} (edge : Fin (oddBaseCount genus)) : Attachment.Sheet :=
  if edge.val % 2 = 0 then Attachment.sheetZero else Attachment.sheetOne

/-- Select the lifted edge sheet from the hemisphere and retained face lift. -/
@[expose] def oddFaceSheet {genus : Nat} (face : Attachment.Face)
    (edge : Fin (oddBaseCount genus)) : Attachment.Sheet :=
  match face.hemisphere with
  | .upper => face.lift
  | .lower => Attachment.selectLift (oddLowerSheet edge) face.lift

/-- Construct the cyclic edge attachment for one odd-degree lifted face.

The upper hemisphere retains its face lift and the lower hemisphere uses alternating sheet labels; ramification
identifies the adjacent endpoint vertices. -/
@[expose] def oddFaceAttachment (genus : Nat) (face : Attachment.Face) :
    Attachment.CyclicAttachment (oddBaseCount genus) (OddVertex genus)
      oddEdgeStart oddEdgeFinish where
  basePositive := oddBasePositive genus
  edgeAt := fun index => ⟨index, oddFaceSheet face index⟩
  followsBase := fun _ => rfl
  continuous := by
    intro index
    rfl

/-- The upper occurrence of a lifted edge uses its sheet as the face-lift label. -/
theorem odd_upper_edgeAt (genus : Nat)
    (base : Fin (oddBaseCount genus)) (sheet : Attachment.Sheet) :
    (oddFaceAttachment genus { hemisphere := .upper, lift := sheet }).edgeAt
        base =
      { base := base, sheet := sheet } := by
  rfl

/-- The matching lower face is computed explicitly. Its occurrence at the same base index is the very same lifted edge;
the lower hemisphere supplies the opposite surface orientation. -/
theorem odd_matchingLower_edgeAt (genus : Nat)
    (base : Fin (oddBaseCount genus)) (sheet : Attachment.Sheet) :
    (oddFaceAttachment genus
      { hemisphere := .lower
        lift := Attachment.selectLift (oddLowerSheet base) sheet }).edgeAt base =
      { base := base, sheet := sheet } := by
  change Edge.mk base
      (Attachment.selectLift (oddLowerSheet base)
        (Attachment.selectLift (oddLowerSheet base) sheet)) = Edge.mk base sheet
  rw [Attachment.selectLift_involutive]

/-- The two explicitly paired odd-model face occurrences have the same underlying lifted edge and hence opposite induced
boundary orientations. -/
theorem odd_pairedFaceOccurrences (genus : Nat)
    (base : Fin (oddBaseCount genus)) (sheet : Attachment.Sheet) :
    (oddFaceAttachment genus { hemisphere := .upper, lift := sheet }).edgeAt
        base =
      (oddFaceAttachment genus
        { hemisphere := .lower
          lift := Attachment.selectLift (oddLowerSheet base) sheet }).edgeAt base :=
  (odd_upper_edgeAt genus base sheet).trans
    (odd_matchingLower_edgeAt genus base sheet).symm

/-! ## Even degree: infinity is unramified and placed at base vertex zero -/

/-- The number of finite ramified vertices in the even-degree double cover. -/
@[expose] def branchCount (genus : Nat) : Nat := 2 * genus + 2
/-- The finite branch count plus the separate unramified infinity base vertex. -/
@[expose] def evenBaseCount (genus : Nat) : Nat := branchCount genus + 1

/-- The even-degree base polygon has at least one vertex. -/
theorem evenBasePositive (genus : Nat) : 0 < evenBaseCount genus := by
  unfold evenBaseCount branchCount
  omega0

set_option genInjectivity false in
/-- Two vertices over infinity, followed by one vertex over every finite ramified point. -/
inductive EvenVertex (genus : Nat) : Type
  /-- One of the two separate sheet vertices above unramified infinity. -/ | infinity (sheet : Attachment.Sheet)
  /-- The common vertex above a finite ramification label. -/ | ramified (index : Fin (branchCount genus))
  deriving DecidableEq

constructive_injectivity EvenVertex

/-- Fibre vertex selected by a base vertex and sheet. Base vertex zero is infinity; every positive base label is a
finite ramification point. -/
@[expose] def evenVertexAbove {genus : Nat} (base : Fin (evenBaseCount genus))
    (sheet : Attachment.Sheet) : EvenVertex genus :=
  if zero : base.val = 0 then
    .infinity sheet
  else
    .ramified ⟨base.val - 1, by
      have baseLt := base.isLt
      unfold evenBaseCount at baseLt
      omega0⟩

/-- Base vertex zero selects the specified sheet vertex at infinity. -/
theorem evenVertexAbove_zero {genus : Nat} (sheet : Attachment.Sheet) :
    evenVertexAbove (genus := genus)
      (⟨0, evenBasePositive genus⟩) sheet =
        .infinity sheet := by
  unfold evenVertexAbove
  rw [dif_pos rfl]

/-- At every nonzero base vertex, both sheet labels identify the same ramified vertex. -/
theorem evenVertexAbove_independent {genus : Nat}
    (base : Fin (evenBaseCount genus)) (nonzero : base.val ≠ 0)
    (left right : Attachment.Sheet) :
    evenVertexAbove base left = evenVertexAbove base right := by
  unfold evenVertexAbove
  rw [dif_neg nonzero, dif_neg nonzero]

/-- Read the source vertex of an even-degree lifted polygon edge. -/
@[expose] def evenEdgeStart {genus : Nat} (edge : Attachment.Edge (evenBaseCount genus)) :
    EvenVertex genus :=
  evenVertexAbove edge.base edge.sheet

/-- Read the cyclic successor vertex of an even-degree lifted polygon edge. -/
@[expose] def evenEdgeFinish {genus : Nat} (edge : Attachment.Edge (evenBaseCount genus)) :
    EvenVertex genus :=
  evenVertexAbove
    (Attachment.cyclicSucc (evenBasePositive genus) edge.base)
    edge.sheet

/-- Alternate on all nonterminal edges. The terminal edge and edge zero both use sheet zero, which is exactly the
no-switch condition at unramified infinity. -/
@[expose] def evenLowerSheet {genus : Nat} (edge : Fin (evenBaseCount genus)) : Attachment.Sheet :=
  if _terminal : edge.val + 1 < evenBaseCount genus then
    if edge.val % 2 = 0 then Attachment.sheetZero else Attachment.sheetOne
  else
    Attachment.sheetZero

/-- The lower sheet does not switch across the cyclic transition through unramified infinity. -/
theorem evenLowerSheet_continuous_at_infinity {genus : Nat}
    (edge : Fin (evenBaseCount genus))
    (nextZero : (Purelib.Topology.BranchedCover.Double.Attachment.cyclicSucc
      (evenBasePositive genus) edge).val = 0) :
    evenLowerSheet edge = evenLowerSheet
      (Purelib.Topology.BranchedCover.Double.Attachment.cyclicSucc (evenBasePositive genus) edge) := by
  by_cases below : edge.val + 1 < evenBaseCount genus
  · have successorValue :
        (Attachment.cyclicSucc (evenBasePositive genus) edge).val = edge.val + 1 := by
      unfold Attachment.cyclicSucc
      rw [dif_pos below]
    rw [successorValue] at nextZero
    omega0
  · have successorEqual : Attachment.cyclicSucc (evenBasePositive genus) edge =
        (⟨0, evenBasePositive genus⟩ : Fin (evenBaseCount genus)) := by
      unfold Attachment.cyclicSucc
      rw [dif_neg below]
    rw [successorEqual]
    unfold evenLowerSheet
    rw [dif_neg below]
    have zeroBelow : 0 + 1 < evenBaseCount genus := by
      unfold evenBaseCount branchCount
      omega0
    rw [dif_pos zeroBelow]
    rfl

/-- Select the even-degree lifted edge sheet using the hemisphere and its retained face lift. -/
@[expose] def evenFaceSheet {genus : Nat} (face : Attachment.Face)
    (edge : Fin (evenBaseCount genus)) : Attachment.Sheet :=
  match face.hemisphere with
  | .upper => face.lift
  | .lower => Attachment.selectLift (evenLowerSheet edge) face.lift

/-- Consecutive edge sheet choices give the same intervening vertex, including the separate infinity sheets. -/
theorem evenFaceSheet_continuous {genus : Nat} (face : Attachment.Face)
    (edge : Fin (evenBaseCount genus)) :
    evenVertexAbove
        (Attachment.cyclicSucc (evenBasePositive genus) edge)
        (evenFaceSheet face edge) =
      evenVertexAbove
        (Attachment.cyclicSucc (evenBasePositive genus) edge)
        (evenFaceSheet face
          (Attachment.cyclicSucc
            (evenBasePositive genus) edge)) := by
  let next := Attachment.cyclicSucc
    (evenBasePositive genus) edge
  by_cases nextZero : next.val = 0
  · have lowerContinuous := evenLowerSheet_continuous_at_infinity edge nextZero
    cases face with
    | mk hemisphere lift =>
        cases hemisphere with
        | upper => rfl
        | lower =>
            apply congrArg (evenVertexAbove next)
            exact Attachment.selectLift_congr lowerContinuous lift
  · exact evenVertexAbove_independent next nextZero _ _

/-- Construct one even-degree lifted face with its cyclic endpoint incidence.

Alternating lower sheets meet at ramified vertices, while the terminal and initial edges keep the same sheet at
unramified infinity. -/
@[expose] def evenFaceAttachment (genus : Nat) (face : Attachment.Face) :
    Attachment.CyclicAttachment (evenBaseCount genus) (EvenVertex genus)
      evenEdgeStart evenEdgeFinish where
  basePositive := evenBasePositive genus
  edgeAt := fun index => ⟨index, evenFaceSheet face index⟩
  followsBase := fun _ => rfl
  continuous := by
    intro index
    exact evenFaceSheet_continuous face index

/-- The upper occurrence of every even-model lifted edge is literal. -/
theorem even_upper_edgeAt (genus : Nat)
    (base : Fin (evenBaseCount genus)) (sheet : Attachment.Sheet) :
    (evenFaceAttachment genus { hemisphere := .upper, lift := sheet }).edgeAt
        base =
      { base := base, sheet := sheet } := by
  rfl

/-- Every even-model lifted edge has one explicitly computed matching lower occurrence, including the terminal edge at
unramified infinity. -/
theorem even_matchingLower_edgeAt (genus : Nat)
    (base : Fin (evenBaseCount genus)) (sheet : Attachment.Sheet) :
    (evenFaceAttachment genus
      { hemisphere := .lower
        lift := Attachment.selectLift (evenLowerSheet base) sheet }).edgeAt base =
      { base := base, sheet := sheet } := by
  change Edge.mk base
      (Attachment.selectLift (evenLowerSheet base)
        (Attachment.selectLift (evenLowerSheet base) sheet)) = Edge.mk base sheet
  rw [Attachment.selectLift_involutive]

/-- The same explicit pairing covers every even-model edge, including the unramified edge at infinity. -/
theorem even_pairedFaceOccurrences (genus : Nat)
    (base : Fin (evenBaseCount genus)) (sheet : Attachment.Sheet) :
    (evenFaceAttachment genus { hemisphere := .upper, lift := sheet }).edgeAt
        base =
      (evenFaceAttachment genus
        { hemisphere := .lower
          lift := Attachment.selectLift (evenLowerSheet base) sheet }).edgeAt base :=
  (even_upper_edgeAt genus base sheet).trans
    (even_matchingLower_edgeAt genus base sheet).symm

/-! ## Finite cell-model packages and count comparison -/

set_option genInjectivity false in
/-- Explicit attaching data for the four faces of an odd-degree double cover. -/
structure OddCellComplex (genus : Nat) where
  /-- The explicit finite list of ramified odd-degree vertices. -/ vertices : List (OddVertex genus)
  /-- The explicit finite list of base edges paired with both sheet labels. -/ edges : List (Attachment.Edge
    (oddBaseCount genus))
  /-- The explicit four hemisphere and sheet-lift face labels. -/ faces : List Attachment.Face
  /-- The cyclic lifted-edge attachment retained for each face. -/ faceBoundary : Attachment.Face ->
    Attachment.CyclicAttachment (oddBaseCount genus)
    (OddVertex genus) oddEdgeStart oddEdgeFinish

constructive_injectivity OddCellComplex

/-- Enumerate all odd-degree vertices, lifted edges and four faces with their explicit boundary attachments. -/
@[expose] def oddCellComplex (genus : Nat) : OddCellComplex genus where
  vertices := List.ofFn fun index : OddVertex genus => index
  edges := (List.ofFn fun base : Fin (oddBaseCount genus) =>
    (List.ofFn fun sheet : Attachment.Sheet => Edge.mk base sheet)).flatten
  faces := (List.ofFn fun hemisphere : Fin 2 =>
    List.ofFn fun lift : Attachment.Sheet =>
      { hemisphere := if hemisphere.val = 0 then .upper else .lower
        lift := lift }).flatten
  faceBoundary := oddFaceAttachment genus

set_option genInjectivity false in
/-- Explicit attaching data for the four faces of an even-degree double cover. -/
structure EvenCellComplex (genus : Nat) where
  /-- The two distinct sheet labels above unramified infinity. -/ infinityVertices : List Attachment.Sheet
  /-- The explicit finite list of ramified even-degree vertices. -/ ramifiedVertices : List (Fin (branchCount genus))
  /-- The explicit finite list of base edges paired with both sheet labels. -/ edges : List (Attachment.Edge
    (evenBaseCount genus))
  /-- The explicit four hemisphere and sheet-lift face labels. -/ faces : List Attachment.Face
  /-- The cyclic lifted-edge attachment retained for each face. -/ faceBoundary : Attachment.Face ->
    Attachment.CyclicAttachment (evenBaseCount genus)
    (EvenVertex genus) evenEdgeStart evenEdgeFinish

constructive_injectivity EvenCellComplex

/-- Enumerate the separate infinity vertices, ramified vertices, lifted edges and four cyclic face attachments. -/
@[expose] def evenCellComplex (genus : Nat) : EvenCellComplex genus where
  infinityVertices := List.ofFn fun sheet : Attachment.Sheet => sheet
  ramifiedVertices := List.ofFn fun index => index
  edges := (List.ofFn fun base : Fin (evenBaseCount genus) =>
    (List.ofFn fun sheet : Attachment.Sheet => Edge.mk base sheet)).flatten
  faces := (List.ofFn fun hemisphere : Fin 2 =>
    List.ofFn fun lift : Attachment.Sheet =>
      { hemisphere := if hemisphere.val = 0 then .upper else .lower
        lift := lift }).flatten
  faceBoundary := evenFaceAttachment genus

/-- The explicit odd-degree complex has one vertex per ramified base label. -/
@[simp] theorem oddCellComplex_vertexCount (genus : Nat) :
    (oddCellComplex genus).vertices.length = oddBaseCount genus := by
  exact OfFn.Basic.length_ofFn

/-- The explicit odd-degree complex has two lifted edges per base edge. -/
@[simp] theorem oddCellComplex_edgeCount (genus : Nat) :
    (oddCellComplex genus).edges.length = oddBaseCount genus * 2 := by
  exact Flatten.length_flatten_ofFn _

/-- The explicit odd-degree complex has four lifted hemisphere faces. -/
@[simp] theorem oddCellComplex_faceCount (genus : Nat) :
    (oddCellComplex genus).faces.length = 4 := by
  change ((List.ofFn fun hemisphere : Fin 2 =>
    List.ofFn fun lift : Attachment.Sheet =>
      { hemisphere := if hemisphere.val = 0 then Hemisphere.upper
          else Hemisphere.lower
        lift := lift }).flatten).length = 4
  rw [Flatten.length_flatten_ofFn]

/-- Count the separate infinity vertices together with the finite ramified vertices. -/
@[expose] def EvenCellComplex.vertexCount {genus : Nat}
    (complex : EvenCellComplex genus) : Nat :=
  complex.infinityVertices.length + complex.ramifiedVertices.length

/-- The explicit even-degree complex has the finite branch count plus two infinity vertices. -/
@[simp] theorem evenCellComplex_vertexCount (genus : Nat) :
    (evenCellComplex genus).vertexCount = branchCount genus + 2 := by
  unfold Cells.EvenCellComplex.vertexCount evenCellComplex
  simp only [OfFn.Basic.length_ofFn]
  omega0

/-- The explicit even-degree complex has two lifted edges per base edge. -/
@[simp] theorem evenCellComplex_edgeCount (genus : Nat) :
    (evenCellComplex genus).edges.length = evenBaseCount genus * 2 := by
  exact Flatten.length_flatten_ofFn _

/-- The explicit even-degree complex has four lifted hemisphere faces. -/
@[simp] theorem evenCellComplex_faceCount (genus : Nat) :
    (evenCellComplex genus).faces.length = 4 := by
  change ((List.ofFn fun hemisphere : Fin 2 =>
    List.ofFn fun lift : Attachment.Sheet =>
      { hemisphere := if hemisphere.val = 0 then Hemisphere.upper
          else Hemisphere.lower
        lift := lift }).flatten).length = 4
  rw [Flatten.length_flatten_ofFn]

/-- The explicit odd attaching model uses exactly the cells counted by the Riemann--Hurwitz model. -/
theorem oddCellComplex_matches_countModel (genus : Nat) :
    (oddCellComplex genus).vertices.length =
        (BranchProfile.oddDegreeModel genus).vertices.length /\
      (oddCellComplex genus).edges.length =
        (BranchProfile.oddDegreeModel genus).edges.length /\
      (oddCellComplex genus).faces.length =
        (BranchProfile.oddDegreeModel genus).faces.length := by
  constructor
  · rw [oddCellComplex_vertexCount,
      BranchedCellModel.vertexCount]
    change oddBaseCount genus =
      total (BranchProfile.oddDegreeProfile genus).cycles
    unfold BranchProfile.oddDegreeProfile
    rw [total_replicate, Nat.mul_one]
    unfold oddBaseCount
    rfl
  · constructor
    · rw [oddCellComplex_edgeCount,
        BranchedCellModel.edgeCount]
      change oddBaseCount genus * 2 =
        (BranchProfile.oddDegreeProfile genus).cycles.length * 2
      rw [BranchProfile.oddDegreeProfile_cycleCount]
      unfold oddBaseCount
      rfl
    · rw [oddCellComplex_faceCount,
        BranchedCellModel.faceCount]
      change 4 = 2 * 2
      rfl

/-- The even attaching model likewise realizes the count model, including the two distinct vertices above unramified
infinity. -/
theorem evenCellComplex_matches_countModel (genus : Nat) :
    (evenCellComplex genus).vertexCount =
        (BranchProfile.evenDegreeModel genus).vertices.length /\
      (evenCellComplex genus).edges.length =
        (BranchProfile.evenDegreeModel genus).edges.length /\
      (evenCellComplex genus).faces.length =
        (BranchProfile.evenDegreeModel genus).faces.length := by
  constructor
  · rw [evenCellComplex_vertexCount,
      BranchedCellModel.vertexCount]
    change branchCount genus + 2 =
      total (BranchProfile.evenDegreeProfile genus).cycles
    unfold BranchProfile.evenDegreeProfile
    rw [total_append, total_replicate]
    change branchCount genus + 2 =
      (2 * genus + 2) * 1 + (2 + 0)
    unfold branchCount
    omega0
  · constructor
    · rw [evenCellComplex_edgeCount,
        BranchedCellModel.edgeCount]
      change evenBaseCount genus * 2 =
        (BranchProfile.evenDegreeProfile genus).cycles.length * 2
      rw [BranchProfile.evenDegreeProfile_cycleCount]
      unfold evenBaseCount branchCount
      omega0
    · rw [evenCellComplex_faceCount,
        BranchedCellModel.faceCount]
      change 4 = 2 * 2
      rfl

end Purelib.Curves.Hyperelliptic.Topology.Cells

end
