module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Fin.Bijection.Search
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic

public import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.Winding
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathClosure
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.RootContinuation.RootPathTransport
public import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootEdges
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Riemann.Paths
open Purelib.Polynomial.Geometry.Grid

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry.Grid.FromStates (ContainsVertex)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)

open Purelib

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Actual lifted walks from the shared edge bank

Walk queries compose stored two-sheet maps.  Their proof traces use the same
edge preparations and proved same-root handoffs.  The trace winding is the
winding of the original grid walk, so regular face boundaries act as the
identity and branch-hole boundaries act as the swap on these shared maps.
-/

namespace Purelib.RootIsolation.SquareRoot.Grid.EdgeBank.RootEdgeBank

open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  Polynomial.Geometry.Grid.ClearGrid polynomial ambient}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid}

/-- This query consumes cached targets only; it never materializes root
readings, joins, or new integration subdivisions. -/
def target
    (bank : RootEdgeBank frames) : {start finish : Canonical} →
      Walk grid start finish → Fin 2 → Fin 2
  | _, _, .nil _, sheet => sheet
  | _, _, .cons edge tail, sheet => target bank tail
    ((bank.edge edge).forward.target sheet)

/-- Follow the original grid walk through its cached root-edge connections.

The owner path starts at the supplied retained sheet and ends at the cached target in the original terminal frame. -/
def trace
    (bank : RootEdgeBank frames) : {start finish : Canonical} → (walk :
      Walk grid start finish) →
    (first : ContainsVertex grid start) → (last :
      ContainsVertex grid finish) → (sheet : Fin 2) →
      OwnerPath polynomial start ((frames.frameAt start first).owners sheet)
        finish ((frames.frameAt finish last).owners (target bank walk sheet))
  | _, _, .nil base, first, _, sheet => .nil base ((frames.frameAt base first).owners sheet)
  | _, _, .cons edge tail, _, last, sheet =>
      let connection := bank.edge edge
      (connection.trace sheet).append (trace bank tail
        edge.vertices.2 last (connection.forward.target sheet))

/-- The retained owner trace has exactly the raw winding of the original grid walk. -/
theorem trace_winding
    (bank : RootEdgeBank frames) : {start finish : Canonical} → (walk :
      Walk grid start finish) →
    (first : ContainsVertex grid start) → (last :
      ContainsVertex grid finish) → (sheet : Fin 2) →
      Winding.Polygon.Basic.chainRaw polynomial start (trace bank walk first last
        sheet).vertices = PreparedPathWinding.ClearPath.rawWinding walk.path
  | _, _, .nil _, _, _, _ => rfl
  | _, _, .cons edge tail, _, last, sheet =>
      (Riemann.RootContinuation.RootPathTransport.OwnerPath.append_winding _ _).trans
        (congrArg₂ (fun left right : Int => left + right) ((bank.edge edge).trace_winding sheet)
          (trace_winding bank tail edge.vertices.2 last
            ((bank.edge edge).forward.target sheet)))

/-- The cached target along an appended walk is the composition of the two original target maps. -/
theorem target_append
    (bank : RootEdgeBank frames) : {start middle finish : Canonical} →
    (left : Walk grid start middle) → (right : Walk grid middle finish) → (sheet
      : Fin 2) →
      target bank (left.append right) sheet =
        target bank right (target bank left
        sheet)
  | _, _, _, .nil _, _, _ => rfl
  | _, _, _, .cons edge tail, right, sheet =>
      target_append bank tail right ((bank.edge
        edge).forward.target sheet)

/-- The even return acts on the actual shared frame, independently of the
canonical ordering used by the auxiliary root-classification proof. -/
theorem target_even
    (bank : RootEdgeBank frames) {base : Canonical} (reference :
      WindingOneLoop polynomial base)
    (walk : Walk grid base base) (member : ContainsVertex grid
      base)
      (turns : Int)
    (winding : PreparedPathWinding.ClearPath.rawWinding walk.path = 8 * turns) (sheet : Fin 2) :
      target bank walk sheet = sheet :=
  (frames.frameAt base member).distinguish _ _
    (Riemann.Paths.OwnerLoopMonodromy.OwnerPath.rootEquivalent_of_even_with_reference reference
      (trace bank walk member member sheet) turns
      ((trace_winding bank walk member member sheet).trans winding))

/-- A retained walk out of the reference base is undone by its actual reverse target map.

The reference may keep a different ambient from the grid. Only the original
anchor is used for the zero-winding closed owner-path comparison.
-/
theorem target_reverse_at_reference (bank : RootEdgeBank frames)
    {anchor finish : Canonical} (reference : WindingOneLoop polynomial anchor)
    (stem : Walk grid anchor finish) (member : ContainsVertex grid anchor) (sheet : Fin 2) :
    target bank stem.reverse (target bank stem sheet) = sheet := by
  have winding : PreparedPathWinding.ClearPath.rawWinding
      (stem.append stem.reverse).path = 8 * (0 : Int) := by
    rw [Winding.Walk.append_winding, Winding.Walk.reverse_winding]
    omega
  exact (target_append bank stem stem.reverse sheet).symm.trans
    (target_even bank reference (stem.append stem.reverse) member 0 winding sheet)

/-- The actual reverse target is also a right inverse, using finite surjectivity without choosing a new map.

An unchanged retained forward map is injective by its proved left inverse.
Constructive bounded finite surjectivity supplies a witness only inside this
proposition-valued proof; the stored reverse target remains the actual map.
-/
theorem target_forward_reverse_at_reference (bank : RootEdgeBank frames)
    {anchor finish : Canonical} (reference : WindingOneLoop polynomial anchor)
    (stem : Walk grid anchor finish) (member : ContainsVertex grid anchor) (sheet : Fin 2) :
    target bank stem (target bank stem.reverse sheet) = sheet := by
  have injective : Function.Injective (target bank stem) := by
    intro left right equal
    exact (target_reverse_at_reference bank reference stem member left).symm.trans
      ((congrArg (target bank stem.reverse) equal).trans
        (target_reverse_at_reference bank reference stem member right))
  obtain ⟨source, equal⟩ := Data.Fin.Bijection.fin_surjective_of_injective (target bank stem) injective sheet
  exact (congrArg (fun value : Fin 2 => target bank stem (target bank stem.reverse value)) equal.symm).trans
    ((congrArg (target bank stem) (target_reverse_at_reference bank reference stem member source)).trans equal)

/-- An even loop at any actual reached vertex fixes its original retained frame indices.

Conjugation uses the SAME grid stem and its actual reverse. The sole
winding-one reference stays at the old anchor; no new-vertex reference loop
or supplied signed-return relation is needed.
-/
theorem target_even_from_reference (bank : RootEdgeBank frames)
    {anchor base : Canonical} (reference : WindingOneLoop polynomial anchor)
    (stem : Walk grid anchor base) (member : ContainsVertex grid anchor)
    (loop : Walk grid base base) (turns : Int)
    (winding : PreparedPathWinding.ClearPath.rawWinding loop.path = 8 * turns)
    (sheet : Fin 2) : target bank loop sheet = sheet := by
  have injective : Function.Injective (target bank stem) := by
    intro left right equal
    exact (target_reverse_at_reference bank reference stem member left).symm.trans
      ((congrArg (target bank stem.reverse) equal).trans
        (target_reverse_at_reference bank reference stem member right))
  obtain ⟨source, equal⟩ := Data.Fin.Bijection.fin_surjective_of_injective (target bank stem) injective sheet
  have basedWinding : PreparedPathWinding.ClearPath.rawWinding
      (stem.append (loop.append stem.reverse)).path = 8 * turns := by
    rw [Winding.Walk.append_winding, Winding.Walk.append_winding,
      Winding.Walk.reverse_winding, winding]
    omega
  have returned := target_even bank reference (stem.append (loop.append stem.reverse)) member turns basedWinding source
  have expanded := ((target_append bank stem (loop.append stem.reverse) source).trans
    (target_append bank loop stem.reverse (target bank stem source))).symm.trans returned
  have atSheet : target bank stem.reverse (target bank loop sheet) = source :=
    Eq.mp (congrArg (fun value : Fin 2 =>
      target bank stem.reverse (target bank loop value) = source) equal) expanded
  have forward := congrArg (target bank stem) atSheet
  exact (target_forward_reverse_at_reference bank reference stem member (target bank loop sheet)).symm.trans
    (forward.trans equal)

/-- Reversal of any reached walk reads inverse target maps of the SAME retained local bank.

The closed walk is based at the actual stem endpoint. Its zero winding is
transported to the old anchor by the preceding even-return theorem.
-/
theorem target_reverse_from_reference (bank : RootEdgeBank frames)
    {anchor start finish : Canonical} (reference : WindingOneLoop polynomial anchor)
    (stem : Walk grid anchor start) (member : ContainsVertex grid anchor)
    (walk : Walk grid start finish) (sheet : Fin 2) :
    target bank walk.reverse (target bank walk sheet) = sheet := by
  have winding : PreparedPathWinding.ClearPath.rawWinding
      (walk.append walk.reverse).path = 8 * (0 : Int) := by
    rw [Winding.Walk.append_winding, Winding.Walk.reverse_winding]
    omega
  exact (target_append bank walk walk.reverse sheet).symm.trans
    (target_even_from_reference bank reference stem member (walk.append walk.reverse) 0 winding sheet)

/-- A reached edge's actual retained forward/backward maps form the original two-sheet bijection.

Both inverse proofs use the one old anchor reference. The returned forward
and backward functions are the SAME cached edge transports; no new edge,
root selection, comparison observation or inverse-search map is prepared.
-/
def edgeBijectionFromReference (bank : RootEdgeBank frames)
    {anchor start finish : Canonical} (reference : WindingOneLoop polynomial anchor)
    (stem : Walk grid anchor start) (member : ContainsVertex grid anchor)
    (edge : Geometry.Grid.Walks.Edge grid start finish) : Data.Fin.Bijection 2 2 :=
  let connection := bank.edge edge
  { forward := connection.forward.target
    backward := connection.backward.target
    backward_forward := by
      intro sheet
      have inverse := target_reverse_from_reference bank reference stem member (.cons edge (.nil finish)) sheet
      change connection.backward.target (connection.forward.target sheet) = sheet at inverse
      exact inverse
    forward_backward := by
      intro sheet
      let nextStem := stem.append (.cons edge (.nil finish))
      have inverse := target_reverse_from_reference bank reference nextStem member
        (.cons (.reverse edge) (.nil start)) sheet
      change connection.forward.target (connection.backward.target sheet) = sheet at inverse
      exact inverse }

/-- The anchored edge bijection keeps the SAME cached forward target function. -/
theorem edgeBijectionFromReference_forward (bank : RootEdgeBank frames)
    {anchor start finish : Canonical} (reference : WindingOneLoop polynomial anchor)
    (stem : Walk grid anchor start) (member : ContainsVertex grid anchor)
    (edge : Geometry.Grid.Walks.Edge grid start finish) (sheet : Fin 2) :
    (edgeBijectionFromReference bank reference stem member edge).forward sheet =
      (bank.edge edge).forward.target sheet := by rfl

/-- The anchored edge bijection keeps the SAME cached backward target function. -/
theorem edgeBijectionFromReference_backward (bank : RootEdgeBank frames)
    {anchor start finish : Canonical} (reference : WindingOneLoop polynomial anchor)
    (stem : Walk grid anchor start) (member : ContainsVertex grid anchor)
    (edge : Geometry.Grid.Walks.Edge grid start finish) (sheet : Fin 2) :
    (edgeBijectionFromReference bank reference stem member edge).backward sheet =
      (bank.edge edge).backward.target sheet := by rfl

/-- Any actual grid walk has inverse retained target maps from the one old anchor reference.

A nonempty walk derives its first actual vertex from its original head edge.
Its reference stem is the original two-axis grid connector. The empty case
keeps the old identity map even when its point was never certified on-grid.
No root preparation or comparison observation is rerun.
-/
theorem target_reverse_anchored (bank : RootEdgeBank frames)
    {anchor : Canonical} (reference : WindingOneLoop polynomial anchor)
    (member : ContainsVertex grid anchor) :
    {start finish : Canonical} → (walk : Walk grid start finish) → (sheet : Fin 2) →
    target bank walk.reverse (target bank walk sheet) = sheet
  | _, _, .nil _, _ => rfl
  | start, _, .cons edge tail, sheet =>
      target_reverse_from_reference bank reference
        (LoopMonodromy.Grid.connect grid anchor start
          member edge.vertices.1) member (.cons edge tail) sheet

/-- The original cached row maps of every actual grid edge are inverse from the one old anchor reference. -/
def edgeBijectionAnchored (bank : RootEdgeBank frames)
    {anchor start finish : Canonical} (reference : WindingOneLoop polynomial anchor)
    (member : ContainsVertex grid anchor) (edge : Geometry.Grid.Walks.Edge grid start finish) :
    Data.Fin.Bijection 2 2 :=
  let connection := bank.edge edge
  { forward := connection.forward.target
    backward := connection.backward.target
    backward_forward := by
      intro sheet
      have inverse := target_reverse_anchored bank reference member (.cons edge (.nil finish)) sheet
      change connection.backward.target (connection.forward.target sheet) = sheet at inverse
      exact inverse
    forward_backward := by
      intro sheet
      have inverse := target_reverse_anchored bank reference member (.cons (.reverse edge) (.nil start)) sheet
      change connection.forward.target (connection.backward.target sheet) = sheet at inverse
      exact inverse }

/-- Each retained edge's forward map undoes its actual backward map from the one old reference.

Only the original cached target maps occur in this scalar readback. No
new edge, trace, selector or stationary join is acquired by the proof.
-/
theorem edge_forward_backward_anchored (bank : RootEdgeBank frames)
    {anchor start finish : Canonical} (reference : WindingOneLoop polynomial anchor)
    (member : ContainsVertex grid anchor) (edge : Geometry.Grid.Walks.Edge grid start finish) (sheet : Fin 2) :
    (bank.edge edge).forward.target ((bank.edge edge).backward.target sheet) = sheet :=
  (edgeBijectionAnchored bank reference member edge).forward_backward sheet

/-- Every actual bank target map is injective from its retained anchored reverse map. -/
theorem target_injective_anchored (bank : RootEdgeBank frames)
    {anchor start finish : Canonical} (reference : WindingOneLoop polynomial anchor)
    (member : ContainsVertex grid anchor) (walk : Walk grid start finish) :
    Function.Injective (target bank walk) := by
  intro left right equal
  exact (target_reverse_anchored bank reference member walk left).symm.trans
    ((congrArg (target bank walk.reverse) equal).trans
      (target_reverse_anchored bank reference member walk right))

/-- Equal actual raw windings give equal bank targets using only the one old anchor reference.

The original reached source vertex supplies its actual connector in the
SAME grid. The difference loop is even; inverse maps remain the original
retained bank maps, including both empty and reversed walks.
-/
theorem target_eq_of_winding_anchored (bank : RootEdgeBank frames)
    {anchor start finish : Canonical} (reference : WindingOneLoop polynomial anchor)
    (anchorMember : ContainsVertex grid anchor) (first last : Walk grid start finish)
    (member : ContainsVertex grid start)
    (winding : PreparedPathWinding.ClearPath.rawWinding first.path =
      PreparedPathWinding.ClearPath.rawWinding last.path) (sheet : Fin 2) :
    target bank first sheet = target bank last sheet := by
  have raw : PreparedPathWinding.ClearPath.rawWinding
      (first.append last.reverse).path = 8 * (0 : Int) := by
    rw [Winding.Walk.append_winding, Winding.Walk.reverse_winding, winding]
    omega
  have returned := target_even_from_reference bank reference
    (LoopMonodromy.Grid.connect grid anchor start anchorMember member)
    anchorMember (first.append last.reverse) 0 raw sheet
  rw [target_append] at returned
  apply target_injective_anchored bank reference anchorMember last.reverse
  rw [returned, target_reverse_anchored bank reference anchorMember last]

/-- Reversing first and then following the original walk restores the actual finishing sheet. -/
theorem target_reverse_right_anchored (bank : RootEdgeBank frames)
    {anchor start finish : Canonical} (reference : WindingOneLoop polynomial anchor)
    (member : ContainsVertex grid anchor) (walk : Walk grid start finish) (sheet : Fin 2) :
    target bank walk (target bank walk.reverse sheet) = sheet := by
  apply target_injective_anchored bank reference member walk.reverse
  exact target_reverse_anchored bank reference member walk (target bank walk.reverse sheet)

/-- A closed walk of odd winding cannot return to its original retained sheet. -/
theorem target_odd_ne
    (bank : RootEdgeBank frames) {base : Canonical}
    (walk : Walk grid base base) (member : ContainsVertex grid
      base)
      (turns : Int)
    (winding : PreparedPathWinding.ClearPath.rawWinding walk.path = 4 * (2 * turns + 1)) (sheet : Fin 2) :
      target bank walk sheet ≠ sheet := open Purelib.Approximation.Gaussian in by
  intro equal
  let actual := trace bank walk member member sheet
  have returned : Equivalence.NamedEquivalent (ownerName ((frames.frameAt base member).owners
    (target bank walk sheet)))
      (ownerName ((frames.frameAt base member).owners sheet)) := by
    rw [equal]
    exact Equivalence.NamedEquivalent.refl _
  exact actual.not_odd_of_return returned turns
    ((Riemann.Paths.PreparedPathClosure.SquareRootTrace.OwnerPath.closedRaw_eq_chainRaw actual).trans
      ((trace_winding bank walk member member sheet).trans winding))

/-- There are exactly two distinct actual owners in the frame, so the
proved nonreturn identifies the result with its other retained owner. -/
theorem target_odd
    (bank : RootEdgeBank frames) {base : Canonical}
    (walk : Walk grid base base) (member : ContainsVertex grid
      base)
      (turns : Int)
    (winding : PreparedPathWinding.ClearPath.rawWinding walk.path = 4 * (2 * turns + 1)) (sheet : Fin 2) :
    target bank walk sheet =
      Curves.Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet := by
  have different := target_odd_ne bank walk member turns winding sheet
  have values : (target bank walk sheet).val ≠ sheet.val := fun same => different
    (Fin.ext same)
  have firstBound := sheet.isLt
  have lastBound := (target bank walk sheet).isLt
  apply Fin.ext
  change (target bank walk sheet).val = 1 - sheet.val
  omega

end Purelib.RootIsolation.SquareRoot.Grid.EdgeBank.RootEdgeBank

namespace Purelib.Riemann.RootContinuation.GridRootWalks.BranchCellBank

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}
end Purelib.Riemann.RootContinuation.GridRootWalks.BranchCellBank

end
