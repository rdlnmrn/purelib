module
import Purelib.Data.Gaussian.Basic
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
        sheet).vertices = Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding walk.path
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
    (winding : Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding walk.path = 8 * turns) (sheet : Fin 2) :
      target bank walk sheet = sheet :=
  (frames.frameAt base member).distinguish _ _
    (Riemann.Paths.OwnerLoopMonodromy.OwnerPath.rootEquivalent_of_even_with_reference reference
      (trace bank walk member member sheet) turns
      ((trace_winding bank walk member member sheet).trans winding))

/-- A closed walk of odd winding cannot return to its original retained sheet. -/
theorem target_odd_ne
    (bank : RootEdgeBank frames) {base : Canonical}
    (walk : Walk grid base base) (member : ContainsVertex grid
      base)
      (turns : Int)
    (winding : Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding walk.path = 4 * (2 * turns + 1)) (sheet : Fin 2) :
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
    (winding : Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding walk.path = 4 * (2 * turns + 1)) (sheet : Fin 2) :
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
