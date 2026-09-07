import CCL.Riemann.HyperellipticTopology
import mathlib.Data.ConstructiveList

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

namespace CCL.Riemann.HyperellipticCells

/-- The next label in a nonempty cyclic finite range. -/
def cyclicSucc {count : Nat} (positive : 0 < count)
    (index : Fin count) : Fin count :=
  if below : index.val + 1 < count then
    ⟨index.val + 1, below⟩
  else
    ⟨0, positive⟩

/-- The two sheet labels. -/
abbrev Sheet := Fin 2

def sheetZero : Sheet := ⟨0, by decide⟩
def sheetOne : Sheet := ⟨1, by decide⟩

/-- Exchange the two displayed sheet labels. -/
def toggleSheet (sheet : Sheet) : Sheet :=
  if sheet.val = 0 then sheetOne else sheetZero

theorem toggleSheet_zero : toggleSheet sheetZero = sheetOne := by
  rfl

theorem toggleSheet_one : toggleSheet sheetOne = sheetZero := by
  rfl

theorem sheet_eq_zero_or_one (sheet : Sheet) :
    sheet = sheetZero \/ sheet = sheetOne := by
  refine Fin.cases (Or.inl rfl) (fun tail => ?_) sheet
  exact Fin.cases (Or.inr rfl) (fun impossible => Fin.elim0 impossible) tail

theorem toggleSheet_injective : Function.Injective toggleSheet := by
  intro left right equal
  rcases sheet_eq_zero_or_one left with leftZero | leftOne <;>
    rcases sheet_eq_zero_or_one right with rightZero | rightOne
  · exact leftZero.trans rightZero.symm
  · rw [leftZero, rightOne, toggleSheet_zero, toggleSheet_one] at equal
    have valueEqual := congrArg Fin.val equal
    change (1 : Nat) = 0 at valueEqual
    omega0
  · rw [leftOne, rightZero, toggleSheet_one, toggleSheet_zero] at equal
    have valueEqual := congrArg Fin.val equal
    change (0 : Nat) = 1 at valueEqual
    omega0
  · exact leftOne.trans rightOne.symm

/-- Select one of a sheet and its complement by a displayed lift label. -/
def selectLift (base lift : Sheet) : Sheet :=
  if lift.val = 0 then base else toggleSheet base

theorem selectLift_congr {left right : Sheet} (equal : left = right)
    (lift : Sheet) : selectLift left lift = selectLift right lift := by
  subst right
  rfl

/-- For either base sheet, selecting one of it and its complement is its own
inverse as a function of the two-valued lift label. -/
theorem selectLift_involutive (base lift : Sheet) :
    selectLift base (selectLift base lift) = lift := by
  rcases sheet_eq_zero_or_one base with rfl | rfl <;>
    rcases sheet_eq_zero_or_one lift with rfl | rfl <;> rfl

/-- A lifted equatorial edge has a base-edge label and a sheet label. -/
structure Edge (baseCount : Nat) where
  base : Fin baseCount
  sheet : Sheet

/-- Four lifted faces: upper/lower hemisphere and either lift. -/
inductive Hemisphere : Type
  | upper
  | lower

structure Face where
  hemisphere : Hemisphere
  lift : Sheet

/-- A finite cyclic attaching walk.  Its successor function is explicitly
displayed, and the incidence equation is checked at every bounded index. -/
structure CyclicAttachment (baseCount : Nat) (Vertex : Type)
    (edgeStart edgeFinish : Edge baseCount -> Vertex) where
  basePositive : 0 < baseCount
  edgeAt : Fin baseCount -> Edge baseCount
  followsBase : forall index, (edgeAt index).base = index
  continuous : forall index,
    edgeFinish (edgeAt index) =
      edgeStart (edgeAt (cyclicSucc basePositive index))

namespace CyclicAttachment

/-- Materialize the attaching word as an ordinary finite list. -/
def edges {baseCount : Nat} {Vertex : Type}
    {edgeStart edgeFinish : Edge baseCount -> Vertex}
    (attachment : CyclicAttachment baseCount Vertex edgeStart edgeFinish) :
    List (Edge baseCount) :=
  List.ofFn attachment.edgeAt

@[simp] theorem edges_length {baseCount : Nat} {Vertex : Type}
    {edgeStart edgeFinish : Edge baseCount -> Vertex}
    (attachment : CyclicAttachment baseCount Vertex edgeStart edgeFinish) :
    attachment.edges.length = baseCount := by
  exact List.length_ofFn

end CyclicAttachment

/-! ## Odd degree: every displayed base vertex is ramified -/

def oddBaseCount (genus : Nat) : Nat := 2 * genus + 2

theorem oddBasePositive (genus : Nat) : 0 < oddBaseCount genus := by
  unfold oddBaseCount
  omega0

abbrev OddVertex (genus : Nat) := Fin (oddBaseCount genus)

def oddVertexAbove {genus : Nat} (base : Fin (oddBaseCount genus))
    (_sheet : Sheet) : OddVertex genus :=
  base

def oddEdgeStart {genus : Nat} (edge : Edge (oddBaseCount genus)) :
    OddVertex genus :=
  oddVertexAbove edge.base edge.sheet

def oddEdgeFinish {genus : Nat} (edge : Edge (oddBaseCount genus)) :
    OddVertex genus :=
  oddVertexAbove
    (cyclicSucc (oddBasePositive genus) edge.base) edge.sheet

/-- The alternating lower-hemisphere sheet along one base edge. -/
def oddLowerSheet {genus : Nat} (edge : Fin (oddBaseCount genus)) : Sheet :=
  if edge.val % 2 = 0 then sheetZero else sheetOne

def oddFaceSheet {genus : Nat} (face : Face)
    (edge : Fin (oddBaseCount genus)) : Sheet :=
  match face.hemisphere with
  | .upper => face.lift
  | .lower => selectLift (oddLowerSheet edge) face.lift

def oddFaceAttachment (genus : Nat) (face : Face) :
    CyclicAttachment (oddBaseCount genus) (OddVertex genus)
      oddEdgeStart oddEdgeFinish where
  basePositive := oddBasePositive genus
  edgeAt := fun index => ⟨index, oddFaceSheet face index⟩
  followsBase := fun _ => rfl
  continuous := by
    intro index
    rfl

/-- The upper occurrence of a lifted edge uses its sheet as the face-lift
label. -/
theorem odd_upper_edgeAt (genus : Nat)
    (base : Fin (oddBaseCount genus)) (sheet : Sheet) :
    (oddFaceAttachment genus { hemisphere := .upper, lift := sheet }).edgeAt
        base =
      { base := base, sheet := sheet } := by
  rfl

/-- The matching lower face is computed explicitly.  Its occurrence at the
same base index is the very same lifted edge; the lower hemisphere supplies
the opposite surface orientation. -/
theorem odd_matchingLower_edgeAt (genus : Nat)
    (base : Fin (oddBaseCount genus)) (sheet : Sheet) :
    (oddFaceAttachment genus
      { hemisphere := .lower
        lift := selectLift (oddLowerSheet base) sheet }).edgeAt base =
      { base := base, sheet := sheet } := by
  change Edge.mk base
      (selectLift (oddLowerSheet base)
        (selectLift (oddLowerSheet base) sheet)) = Edge.mk base sheet
  rw [selectLift_involutive]

/-- The two explicitly paired odd-model face occurrences have the same
underlying lifted edge and hence opposite induced boundary orientations. -/
theorem odd_pairedFaceOccurrences (genus : Nat)
    (base : Fin (oddBaseCount genus)) (sheet : Sheet) :
    (oddFaceAttachment genus { hemisphere := .upper, lift := sheet }).edgeAt
        base =
      (oddFaceAttachment genus
        { hemisphere := .lower
          lift := selectLift (oddLowerSheet base) sheet }).edgeAt base :=
  (odd_upper_edgeAt genus base sheet).trans
    (odd_matchingLower_edgeAt genus base sheet).symm

/-! ## Even degree: infinity is unramified and placed at base vertex zero -/

def finiteBranchCount (genus : Nat) : Nat := 2 * genus + 2
def evenBaseCount (genus : Nat) : Nat := finiteBranchCount genus + 1

theorem evenBasePositive (genus : Nat) : 0 < evenBaseCount genus := by
  unfold evenBaseCount finiteBranchCount
  omega0

/-- Two vertices over infinity, followed by one vertex over every finite
ramified point. -/
inductive EvenVertex (genus : Nat) : Type
  | infinity (sheet : Sheet)
  | ramified (index : Fin (finiteBranchCount genus))
  deriving DecidableEq

/-- Fibre vertex selected by a base vertex and sheet.  Base vertex zero is
infinity; every positive base label is a finite ramification point. -/
def evenVertexAbove {genus : Nat} (base : Fin (evenBaseCount genus))
    (sheet : Sheet) : EvenVertex genus :=
  if zero : base.val = 0 then
    .infinity sheet
  else
    .ramified ⟨base.val - 1, by
      have baseLt := base.isLt
      unfold evenBaseCount at baseLt
      omega0⟩

theorem evenVertexAbove_zero {genus : Nat} (sheet : Sheet) :
    evenVertexAbove (genus := genus)
      (⟨0, evenBasePositive genus⟩) sheet =
        .infinity sheet := by
  unfold evenVertexAbove
  rw [dif_pos rfl]

theorem evenVertexAbove_independent {genus : Nat}
    (base : Fin (evenBaseCount genus)) (nonzero : base.val ≠ 0)
    (left right : Sheet) :
    evenVertexAbove base left = evenVertexAbove base right := by
  unfold evenVertexAbove
  rw [dif_neg nonzero, dif_neg nonzero]

def evenEdgeStart {genus : Nat} (edge : Edge (evenBaseCount genus)) :
    EvenVertex genus :=
  evenVertexAbove edge.base edge.sheet

def evenEdgeFinish {genus : Nat} (edge : Edge (evenBaseCount genus)) :
    EvenVertex genus :=
  evenVertexAbove
    (cyclicSucc (evenBasePositive genus) edge.base)
    edge.sheet

/-- Alternate on all nonterminal edges.  The terminal edge and edge zero both
use sheet zero, which is exactly the no-switch condition at unramified
infinity. -/
def evenLowerSheet {genus : Nat} (edge : Fin (evenBaseCount genus)) : Sheet :=
  if _terminal : edge.val + 1 < evenBaseCount genus then
    if edge.val % 2 = 0 then sheetZero else sheetOne
  else
    sheetZero

theorem evenLowerSheet_continuous_at_infinity {genus : Nat}
    (edge : Fin (evenBaseCount genus))
    (nextZero : (cyclicSucc
      (evenBasePositive genus) edge).val = 0) :
    evenLowerSheet edge = evenLowerSheet
      (cyclicSucc (evenBasePositive genus) edge) := by
  by_cases below : edge.val + 1 < evenBaseCount genus
  · have successorValue :
        (cyclicSucc (evenBasePositive genus) edge).val = edge.val + 1 := by
      unfold cyclicSucc
      rw [dif_pos below]
    rw [successorValue] at nextZero
    omega0
  · have successorEqual : cyclicSucc (evenBasePositive genus) edge =
        (⟨0, evenBasePositive genus⟩ : Fin (evenBaseCount genus)) := by
      unfold cyclicSucc
      rw [dif_neg below]
    rw [successorEqual]
    unfold evenLowerSheet
    rw [dif_neg below]
    have zeroBelow : 0 + 1 < evenBaseCount genus := by
      unfold evenBaseCount finiteBranchCount
      omega0
    rw [dif_pos zeroBelow]
    rfl

def evenFaceSheet {genus : Nat} (face : Face)
    (edge : Fin (evenBaseCount genus)) : Sheet :=
  match face.hemisphere with
  | .upper => face.lift
  | .lower => selectLift (evenLowerSheet edge) face.lift

theorem evenFaceSheet_continuous {genus : Nat} (face : Face)
    (edge : Fin (evenBaseCount genus)) :
    evenVertexAbove
        (cyclicSucc (evenBasePositive genus) edge)
        (evenFaceSheet face edge) =
      evenVertexAbove
        (cyclicSucc (evenBasePositive genus) edge)
        (evenFaceSheet face
          (cyclicSucc
            (evenBasePositive genus) edge)) := by
  let next := cyclicSucc
    (evenBasePositive genus) edge
  by_cases nextZero : next.val = 0
  · have lowerContinuous := evenLowerSheet_continuous_at_infinity edge nextZero
    cases face with
    | mk hemisphere lift =>
        cases hemisphere with
        | upper => rfl
        | lower =>
            apply congrArg (evenVertexAbove next)
            exact selectLift_congr lowerContinuous lift
  · exact evenVertexAbove_independent next nextZero _ _

def evenFaceAttachment (genus : Nat) (face : Face) :
    CyclicAttachment (evenBaseCount genus) (EvenVertex genus)
      evenEdgeStart evenEdgeFinish where
  basePositive := evenBasePositive genus
  edgeAt := fun index => ⟨index, evenFaceSheet face index⟩
  followsBase := fun _ => rfl
  continuous := by
    intro index
    exact evenFaceSheet_continuous face index

/-- The upper occurrence of every even-model lifted edge is literal. -/
theorem even_upper_edgeAt (genus : Nat)
    (base : Fin (evenBaseCount genus)) (sheet : Sheet) :
    (evenFaceAttachment genus { hemisphere := .upper, lift := sheet }).edgeAt
        base =
      { base := base, sheet := sheet } := by
  rfl

/-- Every even-model lifted edge has one explicitly computed matching lower
occurrence, including the terminal edge at unramified infinity. -/
theorem even_matchingLower_edgeAt (genus : Nat)
    (base : Fin (evenBaseCount genus)) (sheet : Sheet) :
    (evenFaceAttachment genus
      { hemisphere := .lower
        lift := selectLift (evenLowerSheet base) sheet }).edgeAt base =
      { base := base, sheet := sheet } := by
  change Edge.mk base
      (selectLift (evenLowerSheet base)
        (selectLift (evenLowerSheet base) sheet)) = Edge.mk base sheet
  rw [selectLift_involutive]

/-- The same explicit pairing covers every even-model edge, including the
unramified edge at infinity. -/
theorem even_pairedFaceOccurrences (genus : Nat)
    (base : Fin (evenBaseCount genus)) (sheet : Sheet) :
    (evenFaceAttachment genus { hemisphere := .upper, lift := sheet }).edgeAt
        base =
      (evenFaceAttachment genus
        { hemisphere := .lower
          lift := selectLift (evenLowerSheet base) sheet }).edgeAt base :=
  (even_upper_edgeAt genus base sheet).trans
    (even_matchingLower_edgeAt genus base sheet).symm

/-! ## Finite cell-model packages and count comparison -/

/-- Explicit attaching data for the four faces of an odd-degree double
cover. -/
structure OddCellComplex (genus : Nat) where
  vertices : List (OddVertex genus)
  edges : List (Edge (oddBaseCount genus))
  faces : List Face
  faceBoundary : Face -> CyclicAttachment (oddBaseCount genus)
    (OddVertex genus) oddEdgeStart oddEdgeFinish

def oddCellComplex (genus : Nat) : OddCellComplex genus where
  vertices := List.ofFn fun index : OddVertex genus => index
  edges := (List.ofFn fun base : Fin (oddBaseCount genus) =>
    (List.ofFn fun sheet : Sheet => Edge.mk base sheet)).flatten
  faces := (List.ofFn fun hemisphere : Fin 2 =>
    List.ofFn fun lift : Sheet =>
      { hemisphere := if hemisphere.val = 0 then .upper else .lower
        lift := lift }).flatten
  faceBoundary := oddFaceAttachment genus

/-- Explicit attaching data for the four faces of an even-degree double
cover. -/
structure EvenCellComplex (genus : Nat) where
  infinityVertices : List Sheet
  ramifiedVertices : List (Fin (finiteBranchCount genus))
  edges : List (Edge (evenBaseCount genus))
  faces : List Face
  faceBoundary : Face -> CyclicAttachment (evenBaseCount genus)
    (EvenVertex genus) evenEdgeStart evenEdgeFinish

def evenCellComplex (genus : Nat) : EvenCellComplex genus where
  infinityVertices := List.ofFn fun sheet : Sheet => sheet
  ramifiedVertices := List.ofFn fun index => index
  edges := (List.ofFn fun base : Fin (evenBaseCount genus) =>
    (List.ofFn fun sheet : Sheet => Edge.mk base sheet)).flatten
  faces := (List.ofFn fun hemisphere : Fin 2 =>
    List.ofFn fun lift : Sheet =>
      { hemisphere := if hemisphere.val = 0 then .upper else .lower
        lift := lift }).flatten
  faceBoundary := evenFaceAttachment genus

/-- Length of a rectangular finite table materialized as nested lists. -/
theorem length_flatten_ofFn {outer inner : Nat}
    (entries : Fin outer -> Fin inner -> Alpha) :
    ((List.ofFn fun row : Fin outer =>
      List.ofFn fun column : Fin inner => entries row column).flatten).length =
        outer * inner := by
  induction outer with
  | zero =>
      rw [List.ofFn_zero]
      simp only [List.flatten_nil, List.length_nil, Nat.zero_mul]
  | succ outer inductionHypothesis =>
      rw [QuotientFreeList.ofFn_succ, List.flatten_cons,
        List.length_append, List.length_ofFn]
      rw [inductionHypothesis]
      rw [Nat.succ_mul]
      exact Nat.add_comm _ _

@[simp] theorem oddCellComplex_vertexCount (genus : Nat) :
    (oddCellComplex genus).vertices.length = oddBaseCount genus := by
  exact List.length_ofFn

@[simp] theorem oddCellComplex_edgeCount (genus : Nat) :
    (oddCellComplex genus).edges.length = oddBaseCount genus * 2 := by
  exact length_flatten_ofFn _

@[simp] theorem oddCellComplex_faceCount (genus : Nat) :
    (oddCellComplex genus).faces.length = 4 := by
  change ((List.ofFn fun hemisphere : Fin 2 =>
    List.ofFn fun lift : Sheet =>
      { hemisphere := if hemisphere.val = 0 then Hemisphere.upper
          else Hemisphere.lower
        lift := lift }).flatten).length = 4
  rw [length_flatten_ofFn]

def EvenCellComplex.vertexCount {genus : Nat}
    (complex : EvenCellComplex genus) : Nat :=
  complex.infinityVertices.length + complex.ramifiedVertices.length

@[simp] theorem evenCellComplex_vertexCount (genus : Nat) :
    (evenCellComplex genus).vertexCount = finiteBranchCount genus + 2 := by
  unfold EvenCellComplex.vertexCount evenCellComplex
  simp only [List.length_ofFn]
  omega0

@[simp] theorem evenCellComplex_edgeCount (genus : Nat) :
    (evenCellComplex genus).edges.length = evenBaseCount genus * 2 := by
  exact length_flatten_ofFn _

@[simp] theorem evenCellComplex_faceCount (genus : Nat) :
    (evenCellComplex genus).faces.length = 4 := by
  change ((List.ofFn fun hemisphere : Fin 2 =>
    List.ofFn fun lift : Sheet =>
      { hemisphere := if hemisphere.val = 0 then Hemisphere.upper
          else Hemisphere.lower
        lift := lift }).flatten).length = 4
  rw [length_flatten_ofFn]

/-- The explicit odd attaching model uses exactly the cells counted by the
Riemann--Hurwitz model. -/
theorem oddCellComplex_matches_countModel (genus : Nat) :
    (oddCellComplex genus).vertices.length =
        (CCL.Riemann.Hyperelliptic.oddDegreeModel genus).vertices.length /\
      (oddCellComplex genus).edges.length =
        (CCL.Riemann.Hyperelliptic.oddDegreeModel genus).edges.length /\
      (oddCellComplex genus).faces.length =
        (CCL.Riemann.Hyperelliptic.oddDegreeModel genus).faces.length := by
  constructor
  · rw [oddCellComplex_vertexCount,
      CCL.Riemann.BranchedCellModel.vertexCount]
    change oddBaseCount genus =
      total (CCL.Riemann.Hyperelliptic.oddDegreeProfile genus).cycles
    unfold CCL.Riemann.Hyperelliptic.oddDegreeProfile
    rw [total_replicate, Nat.mul_one]
    unfold oddBaseCount
    rfl
  · constructor
    · rw [oddCellComplex_edgeCount,
        CCL.Riemann.BranchedCellModel.edgeCount]
      change oddBaseCount genus * 2 =
        (CCL.Riemann.Hyperelliptic.oddDegreeProfile genus).cycles.length * 2
      rw [CCL.Riemann.Hyperelliptic.oddDegreeProfile_cycleCount]
      unfold oddBaseCount
      rfl
    · rw [oddCellComplex_faceCount,
        CCL.Riemann.BranchedCellModel.faceCount]
      change 4 = 2 * 2
      rfl

/-- The even attaching model likewise realizes the count model, including
the two distinct vertices above unramified infinity. -/
theorem evenCellComplex_matches_countModel (genus : Nat) :
    (evenCellComplex genus).vertexCount =
        (CCL.Riemann.Hyperelliptic.evenDegreeModel genus).vertices.length /\
      (evenCellComplex genus).edges.length =
        (CCL.Riemann.Hyperelliptic.evenDegreeModel genus).edges.length /\
      (evenCellComplex genus).faces.length =
        (CCL.Riemann.Hyperelliptic.evenDegreeModel genus).faces.length := by
  constructor
  · rw [evenCellComplex_vertexCount,
      CCL.Riemann.BranchedCellModel.vertexCount]
    change finiteBranchCount genus + 2 =
      total (CCL.Riemann.Hyperelliptic.evenDegreeProfile genus).cycles
    unfold CCL.Riemann.Hyperelliptic.evenDegreeProfile
    rw [total_append, total_replicate]
    change finiteBranchCount genus + 2 =
      (2 * genus + 2) * 1 + (2 + 0)
    unfold finiteBranchCount
    omega0
  · constructor
    · rw [evenCellComplex_edgeCount,
        CCL.Riemann.BranchedCellModel.edgeCount]
      change evenBaseCount genus * 2 =
        (CCL.Riemann.Hyperelliptic.evenDegreeProfile genus).cycles.length * 2
      rw [CCL.Riemann.Hyperelliptic.evenDegreeProfile_cycleCount]
      unfold evenBaseCount finiteBranchCount
      omega0
    · rw [evenCellComplex_faceCount,
        CCL.Riemann.BranchedCellModel.faceCount]
      change 4 = 2 * 2
      rfl

end CCL.Riemann.HyperellipticCells
