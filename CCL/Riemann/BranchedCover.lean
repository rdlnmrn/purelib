import mathlib.Tactic.QuotientFreeOmega

/-!
# Finite cell counts for cyclic branched covers

This file starts the finite Riemann-period development with the topological
data that later path lifting and integration consume.  A branch profile lists,
for every displayed base vertex, the number of cycles in its sheet
permutation.  Thus the fibre above that vertex has exactly that many cells.
Open edges and faces are unramified and have one copy on every labelled sheet.

All cell carriers below are concrete finite lists.  The Riemann--Hurwitz
identity is proved by counting those lists; no completed surface or infinite
topological object is introduced.
-/

namespace CCL.Riemann

/-- A direct recursive sum over displayed natural-number data. -/
def total : List Nat -> Nat
  | [] => 0
  | head :: tail => head + total tail

@[simp] theorem total_nil : total [] = 0 := rfl

@[simp] theorem total_cons (head : Nat) (tail : List Nat) :
    total (head :: tail) = head + total tail := rfl

theorem total_append : forall left right : List Nat,
    total (left ++ right) = total left + total right
  | [], right => by
      simp only [List.nil_append, total_nil, Nat.zero_add]
  | head :: tail, right => by
      rw [List.cons_append, total_cons, total_cons,
        total_append tail right, Nat.add_assoc]

/-- Give every cell in every displayed group its group label and local label. -/
def labelledCellsFrom : Nat -> List Nat -> List (Nat × Nat)
  | _, [] => []
  | firstLabel, count :: counts =>
      (List.range count).map (fun localLabel => (firstLabel, localLabel)) ++
        labelledCellsFrom (firstLabel + 1) counts

def labelledCells (counts : List Nat) : List (Nat × Nat) :=
  labelledCellsFrom 0 counts

theorem length_labelledCellsFrom (firstLabel : Nat) :
    forall counts : List Nat,
      (labelledCellsFrom firstLabel counts).length = total counts
  | [] => rfl
  | count :: counts => by
      simp only [labelledCellsFrom, List.length_append, List.length_map,
        List.length_range, total_cons]
      rw [length_labelledCellsFrom (firstLabel + 1) counts]

@[simp] theorem length_labelledCells (counts : List Nat) :
    (labelledCells counts).length = total counts :=
  length_labelledCellsFrom 0 counts

theorem total_replicate (count value : Nat) :
    total (List.replicate count value) = count * value := by
  induction count with
  | zero => simp only [List.replicate_zero, total_nil, Nat.zero_mul]
  | succ count inductionHypothesis =>
      simp only [List.replicate_succ, total_cons, inductionHypothesis,
        Nat.succ_mul]
      exact Nat.add_comm _ _

/-- Finite local monodromy data for a cyclic cover.  A value `c` in `cycles`
means that the permutation of the displayed sheets around that base vertex
has exactly `c` cycles. -/
structure BranchProfile where
  sheets : Nat
  sheetsAtLeastTwo : 2 <= sheets
  cycles : List Nat
  cyclesPositive : forall cyclesAtVertex,
    cyclesAtVertex ∈ cycles -> 0 < cyclesAtVertex
  cyclesAtMostSheets : forall cyclesAtVertex,
    cyclesAtVertex ∈ cycles -> cyclesAtVertex <= sheets

namespace BranchProfile

/-- Total ramification defect `sum_v (m - c_v)` of a displayed profile. -/
def totalDefect (profile : BranchProfile) : Nat :=
  total (profile.cycles.map fun cyclesAtVertex =>
    profile.sheets - cyclesAtVertex)

theorem total_map_sub_add_total : forall (sheets : Nat) (cycles : List Nat),
    (forall cyclesAtVertex,
      cyclesAtVertex ∈ cycles -> cyclesAtVertex <= sheets) ->
    total cycles + total (cycles.map fun cyclesAtVertex =>
      sheets - cyclesAtVertex) = cycles.length * sheets
  | sheets, [], _ => by
      simp only [List.map_nil, total_nil, List.length_nil, Nat.zero_mul,
        Nat.zero_add]
  | sheets, head :: tail, bounded => by
      have headBound : head <= sheets := bounded head (by simp)
      have tailBound : forall cyclesAtVertex,
          cyclesAtVertex ∈ tail -> cyclesAtVertex <= sheets := by
        intro cyclesAtVertex membership
        exact bounded cyclesAtVertex (by simp only [List.mem_cons]; exact Or.inr membership)
      simp only [List.map_cons, total_cons, List.length_cons, Nat.succ_mul]
      have tailIdentity := total_map_sub_add_total sheets tail tailBound
      omega0

theorem totalCycles_add_totalDefect (profile : BranchProfile) :
    total profile.cycles + profile.totalDefect =
      profile.cycles.length * profile.sheets := by
  exact total_map_sub_add_total profile.sheets profile.cycles
    profile.cyclesAtMostSheets

end BranchProfile

/-- A finite sphere cellulation whose displayed vertices are precisely the
vertices carrying branch-profile entries. -/
structure SphereCellulation (vertexCount : Nat) where
  edgeCount : Nat
  faceCount : Nat
  sphereEuler : vertexCount + faceCount = edgeCount + 2

/-- The equatorial polygon cellulation has one edge per displayed vertex and
two complementary faces. -/
def spherePolygonCellulation (vertexCount : Nat) :
    SphereCellulation vertexCount where
  edgeCount := vertexCount
  faceCount := 2
  sphereEuler := rfl

/-- The finite sheeted cell model obtained by lifting open base edges and
faces to every sheet and replacing each base vertex by its monodromy cycles. -/
structure BranchedCellModel where
  profile : BranchProfile
  base : SphereCellulation profile.cycles.length

namespace BranchedCellModel

def vertices (model : BranchedCellModel) : List (Nat × Nat) :=
  labelledCells model.profile.cycles

def edges (model : BranchedCellModel) : List (Nat × Nat) :=
  labelledCells (List.replicate model.base.edgeCount model.profile.sheets)

def faces (model : BranchedCellModel) : List (Nat × Nat) :=
  labelledCells (List.replicate model.base.faceCount model.profile.sheets)

@[simp] theorem vertexCount (model : BranchedCellModel) :
    model.vertices.length = total model.profile.cycles := by
  exact length_labelledCells model.profile.cycles

@[simp] theorem edgeCount (model : BranchedCellModel) :
    model.edges.length = model.base.edgeCount * model.profile.sheets := by
  rw [edges, length_labelledCells, total_replicate]

@[simp] theorem faceCount (model : BranchedCellModel) :
    model.faces.length = model.base.faceCount * model.profile.sheets := by
  rw [faces, length_labelledCells, total_replicate]

/-- The integer Euler characteristic computed from the three concrete finite
cell lists. -/
def eulerCharacteristic (model : BranchedCellModel) : Int :=
  (model.vertices.length : Int) - (model.edges.length : Int) +
    (model.faces.length : Int)

/-- Nat-valued count form of Riemann--Hurwitz.  Keeping every term
nonnegative makes the primary counting argument directly executable. -/
theorem cellCount_riemannHurwitz (model : BranchedCellModel) :
    model.vertices.length + model.faces.length + model.profile.totalDefect =
      model.edges.length + 2 * model.profile.sheets := by
  rw [vertexCount, edgeCount, faceCount]
  have profileCount := model.profile.totalCycles_add_totalDefect
  have baseCount := congrArg (fun count => count * model.profile.sheets)
    model.base.sphereEuler
  simp only [Nat.add_mul] at baseCount
  omega0

/-- Integer Riemann--Hurwitz for the finite sheeted cell model. -/
theorem eulerCharacteristic_eq_riemannHurwitz
    (model : BranchedCellModel) :
    model.eulerCharacteristic =
      (2 : Int) * (model.profile.sheets : Int) -
        (model.profile.totalDefect : Int) := by
  have countIdentity := model.cellCount_riemannHurwitz
  unfold eulerCharacteristic
  omega0

end BranchedCellModel

/-- Finite evidence that Riemann--Hurwitz has a nonnegative even genus
numerator.  Both fields are decidable arithmetic checks. -/
structure GenusCertificate (profile : BranchProfile) : Type where
  enoughDefect : 2 * profile.sheets <= profile.totalDefect + 2
  evenNumerator :
    (profile.totalDefect + 2 - 2 * profile.sheets) % 2 = 0

namespace GenusCertificate

def numerator {profile : BranchProfile} (_certificate : GenusCertificate profile) : Nat :=
  profile.totalDefect + 2 - 2 * profile.sheets

/-- The genus is computed by ordinary finite natural-number division. -/
def genus {profile : BranchProfile} (certificate : GenusCertificate profile) : Nat :=
  certificate.numerator / 2

theorem twice_genus_eq_numerator {profile : BranchProfile}
    (certificate : GenusCertificate profile) :
    2 * certificate.genus = certificate.numerator := by
  have remainderZero : certificate.numerator % 2 = 0 :=
    certificate.evenNumerator
  have divisionIdentity := Nat.mod_add_div certificate.numerator 2
  rw [remainderZero] at divisionIdentity
  unfold genus
  simpa only [zero_add] using divisionIdentity

/-- The computed genus recovers the finite cell Euler characteristic. -/
theorem eulerCharacteristic_eq_two_sub_twice_genus
    {profile : BranchProfile} (certificate : GenusCertificate profile)
    (base : SphereCellulation profile.cycles.length) :
    (BranchedCellModel.mk profile base).eulerCharacteristic =
      (2 : Int) - 2 * certificate.genus := by
  let model := BranchedCellModel.mk profile base
  have riemannHurwitz := model.eulerCharacteristic_eq_riemannHurwitz
  dsimp only [model] at riemannHurwitz
  have numeratorAdd : certificate.numerator + 2 * profile.sheets =
      profile.totalDefect + 2 := by
    exact Nat.sub_add_cancel certificate.enoughDefect
  have twiceGenus := certificate.twice_genus_eq_numerator
  exact riemannHurwitz.trans (by omega0)

end GenusCertificate

/-- Executably validate the two arithmetic conditions needed to extract a
genus from a branch profile. -/
def genusCertificate? (profile : BranchProfile) :
    Option (GenusCertificate profile) :=
  if enoughDefect : 2 * profile.sheets <= profile.totalDefect + 2 then
    if evenNumerator :
        (profile.totalDefect + 2 - 2 * profile.sheets) % 2 = 0 then
      some { enoughDefect := enoughDefect, evenNumerator := evenNumerator }
    else none
  else none

theorem genusCertificate?_isSome (profile : BranchProfile)
    (certificate : GenusCertificate profile) :
    (genusCertificate? profile).isSome = true := by
  unfold genusCertificate?
  rw [dif_pos certificate.enoughDefect, dif_pos certificate.evenNumerator]
  rfl

/-- A canonical finite model for any branch profile, using the equatorial
polygon cellulation of the base sphere. -/
def finiteBranchedCover (profile : BranchProfile) : BranchedCellModel where
  profile := profile
  base := spherePolygonCellulation profile.cycles.length

end CCL.Riemann
