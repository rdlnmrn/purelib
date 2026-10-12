module

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs

import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Range.Basic
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Division
import Purelib.Data.Nat.Multiplication
import Purelib.Data.Nat.Subtraction
meta import Purelib.Elab.ConstructiveInjectivity

public section

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

namespace Purelib.Topology.BranchedCover

open Purelib.Data.List
open Purelib.Data.Nat

/-- Sum the displayed natural numbers by structural recursion. -/
@[expose] def total : List Nat -> Nat
  | [] => 0
  | head :: tail => head + total tail

/-- The sum of the empty list is zero. -/
@[simp] theorem total_nil : total [] = 0 := rfl

/-- The sum of a nonempty list is its head plus its tail sum. -/
@[simp] theorem total_cons (head : Nat) (tail : List Nat) :
    total (head :: tail) = head + total tail := rfl

/-- Summation takes list concatenation to addition.

The identity holds for any two displayed natural-number lists, by structural recursion on the first list. -/
theorem total_append : forall left right : List Nat,
    total (left ++ right) = total left + total right
  | [], right => by
      exact (Nat.zero_add (total right)).symm
  | head :: tail, right => by
      rw [List.cons_append, total_cons, total_cons,
        total_append tail right, Nat.add_assoc]

/-- Enumerate groups of cells with consecutive group labels.

Each count supplies its local labels from zero up to that count. Group labels start at the supplied offset and increase
by one for each list entry. -/
@[expose] def labelledCellsFrom : Nat -> List Nat -> List (Nat × Nat)
  | _, [] => []
  | firstLabel, count :: counts =>
      (List.range count).map (fun localLabel => (firstLabel, localLabel)) ++
        labelledCellsFrom (firstLabel + 1) counts

/-- Enumerate grouped cells with group labels starting at zero. -/
@[expose] def labelledCells (counts : List Nat) : List (Nat × Nat) :=
  labelledCellsFrom 0 counts

/-- The number of labelled cells is the sum of the group sizes.

The starting group label changes cell labels but leaves the total number of enumerated pairs unchanged. -/
theorem length_labelledCellsFrom (firstLabel : Nat) :
    forall counts : List Nat,
      (labelledCellsFrom firstLabel counts).length = total counts
  | [] => rfl
  | count :: counts => by
      simp only [labelledCellsFrom, Append.length_append, Map.length_map,
        Range.Basic.length_range, total_cons, -eq_self, -iff_self]
      rw [length_labelledCellsFrom (firstLabel + 1) counts]

/-- The labelled cell list has length equal to the total count. -/
@[simp] theorem length_labelledCells (counts : List Nat) :
    (labelledCells counts).length = total counts :=
  length_labelledCellsFrom 0 counts

/-- The sum of a repeated natural value is the repetition count times that value. -/
theorem total_replicate (count value : Nat) :
    total (List.replicate count value) = count * value := by
  induction count with
  | zero => exact (Nat.zero_mul value).symm
  | succ count inductionHypothesis =>
      simp only [List.replicate_succ, total_cons, inductionHypothesis,
        Nat.succ_mul]
      exact Nat.add_comm _ _

set_option genInjectivity false in
/-- Finite sheet and local cycle counts for a branched cover.

There are at least two sheets. Each displayed vertex has a positive cycle count bounded by the sheet count, so its
ramification defect is a natural difference. -/
structure BranchProfile where
  /-- The number of labelled sheets. -/ sheets : Nat
  /-- The cover has at least two sheets. -/ sheetsAtLeastTwo : 2 <= sheets
  /-- The local monodromy cycle count at each displayed base vertex. -/ cycles : List Nat
  /-- Every displayed vertex has at least one monodromy cycle. -/ cyclesPositive : forall cyclesAtVertex,
    cyclesAtVertex ∈ cycles -> 0 < cyclesAtVertex
  /-- Every local cycle count is bounded by the sheet count. -/ cyclesAtMostSheets : forall cyclesAtVertex,
    cyclesAtVertex ∈ cycles -> cyclesAtVertex <= sheets

constructive_injectivity BranchProfile

namespace BranchProfile

/-- Sum the local ramification defects of the displayed branch profile.

At each vertex the defect is the sheet count minus the cycle count, whose retained bound makes the subtraction exact. -/
@[expose] def totalDefect (profile : BranchProfile) : Nat :=
  total (profile.cycles.map fun cyclesAtVertex =>
    profile.sheets - cyclesAtVertex)

/-- Bounded cycle counts and their deficits sum to the full sheet count at every entry.

Each listed count must be at most the common sheet bound. Summing counts and truncated differences then gives list
length times that bound. -/
theorem total_map_sub_add_total : forall (sheets : Nat) (cycles : List Nat),
    (forall cyclesAtVertex,
      cyclesAtVertex ∈ cycles -> cyclesAtVertex <= sheets) ->
    total cycles + total (cycles.map fun cyclesAtVertex =>
      sheets - cyclesAtVertex) = cycles.length * sheets
  | sheets, [], _ => by
      simp only [List.map_nil, total_nil, List.length_nil, Nat.zero_mul,
        Nat.zero_add, -eq_self, -iff_self]
      rfl
  | sheets, head :: tail, bounded => by
      have headBound : head <= sheets := bounded head (List.Mem.head tail)
      have tailBound : forall cyclesAtVertex,
          cyclesAtVertex ∈ tail -> cyclesAtVertex <= sheets := by
        intro cyclesAtVertex membership
        exact bounded cyclesAtVertex (List.Mem.tail head membership)
      simp only [List.map_cons, total_cons, List.length_cons, Nat.succ_mul]
      have tailIdentity := total_map_sub_add_total sheets tail tailBound
      omega0

/-- Total cycle count plus ramification defect equals vertex count times sheet count. -/
theorem totalCycles_add_totalDefect (profile : BranchProfile) :
    total profile.cycles + profile.totalDefect =
      profile.cycles.length * profile.sheets := by
  exact total_map_sub_add_total profile.sheets profile.cycles
    profile.cyclesAtMostSheets

end BranchProfile

set_option genInjectivity false in
/-- Finite edge and face counts satisfying the sphere Euler equation.

The vertex count is an index of the structure; the retained equality states vertices plus faces equals edges plus two.
-/
structure SphereCellulation (vertexCount : Nat) where
  /-- The number of displayed base edges. -/ edgeCount : Nat
  /-- The number of displayed base faces. -/ faceCount : Nat
  /-- The base cell counts have sphere Euler characteristic two. -/ sphereEuler : vertexCount + faceCount = edgeCount +
    2

constructive_injectivity SphereCellulation

/-- The equatorial polygon cellulation with one edge per vertex and two faces. -/
@[expose] def spherePolygonCellulation (vertexCount : Nat) :
    SphereCellulation vertexCount where
  edgeCount := vertexCount
  faceCount := 2
  sphereEuler := rfl

set_option genInjectivity false in
/-- A finite lifted cell model with a branch profile and sphere base counts.

The base vertex count is the length of the retained cycle list, so each branch entry belongs to one displayed base
vertex. -/
structure BranchedCellModel where
  /-- The retained sheet count and local monodromy cycle data. -/ profile : BranchProfile
  /-- A sphere cellulation indexed by the number of branch-profile entries. -/ base : SphereCellulation
    profile.cycles.length

constructive_injectivity BranchedCellModel

namespace BranchedCellModel

/-- Enumerate one lifted vertex for each local monodromy cycle. -/
@[expose] def vertices (model : BranchedCellModel) : List (Nat × Nat) :=
  labelledCells model.profile.cycles

/-- Enumerate one lift of every base edge on every sheet. -/
@[expose] def edges (model : BranchedCellModel) : List (Nat × Nat) :=
  labelledCells (List.replicate model.base.edgeCount model.profile.sheets)

/-- Enumerate one lift of every base face on every sheet. -/
@[expose] def faces (model : BranchedCellModel) : List (Nat × Nat) :=
  labelledCells (List.replicate model.base.faceCount model.profile.sheets)

/-- The lifted vertex count is the total local cycle count. -/
@[simp] theorem vertexCount (model : BranchedCellModel) :
    model.vertices.length = total model.profile.cycles := by
  exact length_labelledCells model.profile.cycles

/-- The lifted edge count is the base edge count times the sheet count. -/
@[simp] theorem edgeCount (model : BranchedCellModel) :
    model.edges.length = model.base.edgeCount * model.profile.sheets := by
  rw [edges, length_labelledCells, total_replicate]

/-- The lifted face count is the base face count times the sheet count. -/
@[simp] theorem faceCount (model : BranchedCellModel) :
    model.faces.length = model.base.faceCount * model.profile.sheets := by
  rw [faces, length_labelledCells, total_replicate]

/-- Compute vertices minus edges plus faces from the concrete cell lists. -/
@[expose] def eulerCharacteristic (model : BranchedCellModel) : Int :=
  (model.vertices.length : Int) - (model.edges.length : Int) +
    (model.faces.length : Int)

/-- The lifted cell counts satisfy the natural-number Riemann--Hurwitz equation.

Adding ramification defect to vertices plus faces gives edges plus twice the sheet count; all terms remain natural
numbers. -/
theorem cellCount_riemannHurwitz (model : BranchedCellModel) :
    model.vertices.length + model.faces.length + model.profile.totalDefect =
      model.edges.length + 2 * model.profile.sheets := by
  rw [vertexCount, edgeCount, faceCount]
  have profileCount := model.profile.totalCycles_add_totalDefect
  have baseCount := congrArg (fun count => count * model.profile.sheets)
    model.base.sphereEuler
  rewrite [Multiplication.right_distrib, Multiplication.right_distrib] at baseCount
  omega0

/-- The finite Euler characteristic equals twice the sheet count minus the ramification defect.

This is the integer form of the cell-count equation for the retained branch profile and sphere cellulation. -/
theorem eulerCharacteristic_eq_riemannHurwitz
    (model : BranchedCellModel) :
    model.eulerCharacteristic =
      (2 : Int) * (model.profile.sheets : Int) -
        (model.profile.totalDefect : Int) := by
  have countIdentity := model.cellCount_riemannHurwitz
  unfold eulerCharacteristic
  omega0

end BranchedCellModel

/-- Arithmetic evidence that the genus numerator is nonnegative and even.

The defect plus two must be at least twice the sheet count. The remaining natural difference must have remainder zero
modulo two. -/
structure GenusCertificate (profile : BranchProfile) : Type where
  /-- Defect plus two is at least twice the sheet count, so the genus numerator is nonnegative. -/ enoughDefect : 2 *
    profile.sheets <= profile.totalDefect + 2
  /-- The nonnegative genus numerator has remainder zero modulo two. -/ evenNumerator :
    (profile.totalDefect + 2 - 2 * profile.sheets) % 2 = 0

namespace GenusCertificate

/-- The nonnegative genus numerator certified by the branch profile evidence. -/
@[expose] def numerator {profile : BranchProfile} (_certificate : GenusCertificate profile) : Nat :=
  profile.totalDefect + 2 - 2 * profile.sheets

/-- Compute the genus by dividing the certified numerator by two. -/
@[expose] def genus {profile : BranchProfile} (certificate : GenusCertificate profile) : Nat :=
  certificate.numerator / 2

/-- Twice the computed genus equals its certified even numerator. -/
theorem twice_genus_eq_numerator {profile : BranchProfile}
    (certificate : GenusCertificate profile) :
    2 * certificate.genus = certificate.numerator := by
  have remainderZero : certificate.numerator % 2 = 0 :=
    certificate.evenNumerator
  have divisionIdentity := Division.mod_add_div certificate.numerator 2
  rw [remainderZero] at divisionIdentity
  unfold genus
  exact (Nat.zero_add (2 * (certificate.numerator / 2))).symm.trans divisionIdentity

/-- The certified genus gives Euler characteristic two minus twice the genus.

The identity holds for any sphere cellulation indexed by the profile, using its retained count equation and the
certificate arithmetic. -/
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
    exact Subtraction.sub_add_cancel certificate.enoughDefect
  have twiceGenus := certificate.twice_genus_eq_numerator
  exact riemannHurwitz.trans (by omega0)

end GenusCertificate

/-- Check the nonnegativity and parity conditions for a genus certificate.

Return the two arithmetic proofs when both conditions hold, or none when either check fails. -/
@[expose] def genusCertificate? (profile : BranchProfile) :
    Option (GenusCertificate profile) :=
  if enoughDefect : 2 * profile.sheets <= profile.totalDefect + 2 then
    if evenNumerator :
        (profile.totalDefect + 2 - 2 * profile.sheets) % 2 = 0 then
      some { enoughDefect := enoughDefect, evenNumerator := evenNumerator }
    else none
  else none

/-- A profile with a genus certificate passes the executable certificate check. -/
theorem genusCertificate?_isSome (profile : BranchProfile)
    (certificate : GenusCertificate profile) :
    (genusCertificate? profile).isSome = true := by
  unfold genusCertificate?
  rw [dif_pos certificate.enoughDefect, dif_pos certificate.evenNumerator]
  rfl

/-- Construct the canonical finite cover model over the equatorial polygon.

The supplied branch profile is retained unchanged; its number of cycle entries determines the base polygon vertex count.
-/
@[expose] def branchedCover (profile : BranchProfile) : BranchedCellModel where
  profile := profile
  base := spherePolygonCellulation profile.cycles.length

end Purelib.Topology.BranchedCover
