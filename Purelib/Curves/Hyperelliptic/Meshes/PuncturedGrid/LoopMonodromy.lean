module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
public import Purelib.Polynomial.Geometry.Grid.Winding
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathClosure
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Meshes.FramedPuncturedGrid
public import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Init.Core
import Init.Data.Bool
import Init.Data.Int.Basic
import Init.Prelude
import Init.SimpLemmas
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
public import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.Exact.Ownership.Basic
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.Residual.Global.Assignment
import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.QuotientFreeOmega
meta import Mathlib.Tactic.Linter.Lint

public section

/-!
# Actual loop monodromy on the punctured branch grid

Every grid vertex has a constructed winding-one reference loop: travel to
one retained branch face, traverse its actual boundary, and return on the
reversed connector.  Thus zero-winding regular faces close operationally,
while each branch hole swaps the two actual square-root occurrences.

This is the loop-consistency layer for two-sheet gluing.  It does not yet
construct the shared edge-transport bank or its lifted face incidence.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.CellBoundary
open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Polynomial.Geometry.Grid.FromStates
open Purelib.Polynomial.Geometry.Grid.Winding
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerLoopMonodromy
open Purelib.Riemann.Paths.PreparedPathClosure
open Purelib.Riemann.Paths.PreparedPathTrace
open Purelib.Riemann.Paths.PreparedPathWinding
open Purelib.Riemann.Paths.PreparedPathWinding.PreparedClearPathModels
open Purelib.Riemann.Topology

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop windingSheet)
open Purelib.Riemann.RootContinuation
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open _root_.Purelib.Polynomial.Geometry.Grid.FromStates (ContainsVertex)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank FramedBranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace BranchHole)
open Purelib.Riemann.Paths.PreparedPathWinding.ClearPath (rawWinding)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

section Grid

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Geometry.Rational.Box}

namespace LoopMonodromy.Grid

/-- A two-leg connector on retained grid lines. Both endpoint owners can be continued along these actual adjacent edges,
not a diagonal chord. -/
@[expose] def connect (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) (start finish :
  Data.Gaussian.Basic.Canonical)
    (first : Polynomial.Geometry.Grid.FromStates.ContainsVertex grid start) (last :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex grid finish) : Walks.Walk grid start finish :=
  let horizontal := Walks.horizontalWalk grid start.re finish.re start.im first.1 last.1 first.2
  let vertical := Walks.verticalWalk grid finish.re start.im finish.im last.1 first.2 last.2
  (horizontal.append vertical).castEndpoints (by rfl) (by rfl)

end LoopMonodromy.Grid

namespace LoopMonodromy.Grid

set_option genInjectivity false in
/-- A retained actual grid loop, usable as a parity reference at its base.

The displayed loop remains based at the retained vertex and follows actual grid edges. Its raw winding certificate fixes
the finite parity reference while preserving the original walk. -/
structure WindingOneReference (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) (base :
  Data.Gaussian.Basic.Canonical) where
  /-- The retained actual grid loop based at the original vertex. -/ walk : Walks.Walk grid base base
  /-- The retained actual reference loop has raw winding four. -/ winding : ClearPath.rawWinding walk.path = 4

constructive_injectivity WindingOneReference

end LoopMonodromy.Grid

namespace LoopMonodromy.Grid.WindingOneReference

/-- Package the same retained grid reference loop with its ambient containment and winding-one certificate.

The displayed loop remains based at the retained vertex and follows actual grid edges. Its raw winding certificate fixes
the finite parity reference while preserving the original walk. -/
@[expose] def toLoop {grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient} {base :
  Data.Gaussian.Basic.Canonical}
    (reference : Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.Grid.WindingOneReference grid base) :
      OwnerLoopMonodromy.WindingOneLoop polynomial base :=
  ⟨ambient, reference.walk.path, reference.walk.withinAmbient, reference.winding⟩

end LoopMonodromy.Grid.WindingOneReference

set_option genInjectivity false in
/-- Retain the actual integration preparation and a checked sheet action. Consumers read the cached bit rather than
rerunning owner classification.

The cached trace and integer winding belong to the same original closed walk. The retained parity bit determines the
exact finishing-owner sheet assignment without executing another reference path. -/
structure LoopMonodromy {grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient} {base :
  Data.Gaussian.Basic.Canonical}
    (walk : Walks.Walk grid base base) (owner : SquareRootContinuationChain.Owner (polynomial.eval base)) where
  /-- The cached actual continuation trace of the original closed grid walk. -/ traced : PreparedPathTrace.TracedPath
    walk.path owner
  /-- The retained integral winding of the original grid loop. -/ winding : Int
  /-- The original path raw winding is exactly four times the retained integral winding. -/ winding_eq :
    ClearPath.rawWinding walk.path = 4 * winding
  /-- The cached parity bit giving the original loop's two-sheet action. -/ flip : Bool
  /-- The retained action bit is exactly the nonzero parity test of the original winding. -/ flip_eq : flip = decide
    (winding % 2 ≠ 0)
  /-- The retained finishing owner has the parity-selected original sheet assignment. -/ assignment :
    (SquareRootReconditioning.assignment owner.parameterNonzero traced.finishOwner).owner.owner =
    if flip then BranchCutLifts.otherSheet (SquareRootReconditioning.assignment owner.parameterNonzero
      owner).owner.owner
    else (SquareRootReconditioning.assignment owner.parameterNonzero owner).owner.owner

constructive_injectivity LoopMonodromy

namespace LoopMonodromy

variable {grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient} {base :
  Purelib.Data.Gaussian.Basic.Canonical} {walk : Walk grid base base}
  {owner : Owner (polynomial.eval base)}

/-- Attach the proved action to an already retained trace. The reference appears only in the erased parity proof, so no
auxiliary path is executed. -/
@[expose] def ofTraced (reference : Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.Grid.WindingOneReference
  grid base) (traced : PreparedPathTrace.TracedPath walk.path owner)
    (winding : Int) (raw : ClearPath.rawWinding walk.path = 4 * winding) :
      LoopMonodromy walk owner :=
  { traced := traced
    winding := winding
    winding_eq := raw
    flip := decide (winding % 2 ≠ 0)
    flip_eq := rfl
    assignment := by
      have equality := OwnerPath.assignment_windingSheet
        reference.toLoop traced.trace.get winding
        ((TracedPath.winding_original traced).trans raw)
      by_cases even : winding % 2 = 0
      · have negative : decide (winding % 2 ≠ 0) = false := decide_eq_false (by intro opposite; exact opposite even)
        unfold OwnerLoopMonodromy.windingSheet at equality
        rewrite [if_pos even] at equality
        rewrite [negative, if_neg (by intro impossible; cases impossible)]
        exact equality
      · have positive : decide (winding % 2 ≠ 0) = true := decide_eq_true even
        unfold OwnerLoopMonodromy.windingSheet at equality
        rewrite [if_neg even] at equality
        rewrite [positive, if_pos (Eq.refl true)]
        exact equality }

/-- Canonical preparation is available, but geometry consumers with retained or generated traces use `ofTraced` without
repeating it. -/
@[expose] def build (reference : Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.Grid.WindingOneReference grid
  base) (walk : Walks.Walk grid base base)
    (owner : SquareRootContinuationChain.Owner (polynomial.eval base)) (winding : Int) (raw : ClearPath.rawWinding
      walk.path = 4 * winding) :
    LoopMonodromy walk owner :=
  ofTraced reference (TracedPath.build
    walk.path walk.withinAmbient owner) winding raw

/-- Apply the retained loop parity action to the original two-sheet index. -/
@[expose] def action (monodromy : LoopMonodromy walk owner)
  (sheet : Fin 2) : Fin 2 :=
  if monodromy.flip then BranchCutLifts.otherSheet sheet else sheet

/-- An even action supplies an actual operational return, with a finite comparison constructor rather than a mere
equality of attached labels. -/
@[expose] def returned (monodromy : LoopMonodromy walk
  owner) (even : monodromy.flip = false) :
    Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName monodromy.traced.finishOwner)
      (OwnerTraceReadings.ownerName owner) :=
  SquareRootTrace.rootEquivalent_of_assignment_eq
    owner.parameterNonzero owner monodromy.traced.finishOwner
    (by
      have assignment := monodromy.assignment
      rewrite [even, if_neg (by intro impossible; cases impossible)] at assignment
      exact assignment)

/-- A retained odd loop cannot return an operationally equivalent original owner channel. -/
theorem not_returned (monodromy : LoopMonodromy walk owner)
  (odd : monodromy.flip = true) :
    Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName monodromy.traced.finishOwner)
      (OwnerTraceReadings.ownerName owner) → False := by
  have remainder : monodromy.winding % 2 ≠ 0 := of_decide_eq_true (monodromy.flip_eq.symm.trans odd)
  apply TracedPath.root_not_equivalent_of_original_odd
    monodromy.traced (monodromy.winding / 2)
  have raw := monodromy.winding_eq
  omega

end LoopMonodromy
end Grid

namespace LoopMonodromy.BranchCellBank

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}

/-- Use the first cached branch face. Positive degree supplies its index; the branch bank is not recomputed or
re-isolated. -/
@[expose] def referenceAt (bank : Branches.BranchCellBank curve branches higher) (base : Data.Gaussian.Basic.Canonical)
  (member : Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid base) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.Grid.WindingOneReference bank.grid base :=
  let index : Data.Index branches := ⟨0, by have count := branches.count_eq; omega⟩
  let cell := bank.cell index
  let connector := Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.Grid.connect bank.grid base cell.box.anchor
    member
    (Cell.anchor_mem cell (bank.cell_mem index))
  let loop := Cell.boundaryWalk cell (bank.cell_mem index)
  { walk := connector.append (loop.append connector.reverse)
    winding := by
      rw [Walk.append_winding,
        Walk.append_winding,
        Walk.reverse_winding,
        Cell.boundaryWalk_winding,
        BranchCellWinding.selected_winding_four]
      omega }

namespace RegularFace

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.RegularFace

variable {bank : BranchCellBank curve branches higher}

/-- Attach the trivial winding action to the retained trace around the original regular face. -/
@[expose] def monodromy (face : PuncturedGridFaces.RegularFace bank) {owner : SquareRootContinuationChain.Owner
  (curve.polynomial.eval face.cell.box.anchor)}
    (traced : PreparedPathTrace.TracedPath face.boundary.path owner) :
      LoopMonodromy face.boundary owner :=
  .ofTraced (Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt bank _
    (Cell.anchor_mem face.cell face.member))
    traced 0 face.boundary_winding

/-- The original regular-face loop has trivial sheet action. -/
theorem monodromy_flip (face : PuncturedGridFaces.RegularFace bank) {owner : SquareRootContinuationChain.Owner
  (curve.polynomial.eval face.cell.box.anchor)}
    (traced : PreparedPathTrace.TracedPath face.boundary.path owner) : (monodromy face traced).flip = false := rfl

/-- Construct operational return equivalence for the actual retained regular-face trace. -/
@[expose] def returned (face : PuncturedGridFaces.RegularFace bank) {owner : SquareRootContinuationChain.Owner
  (curve.polynomial.eval face.cell.box.anchor)}
    (traced : PreparedPathTrace.TracedPath face.boundary.path owner) : Gaussian.Equivalence.NamedEquivalent
      (OwnerTraceReadings.ownerName traced.finishOwner) (OwnerTraceReadings.ownerName owner) :=
  (monodromy face traced).returned
    (monodromy_flip face traced)

end RegularFace

namespace BranchHole

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.BranchHole

variable {bank : BranchCellBank curve branches higher}

/-- A removed hole is traversed clockwise, so its winding is minus one; parity still gives the genuine nontrivial
two-sheet action. -/
@[expose] def monodromy (hole : PuncturedGridFaces.BranchHole bank) {owner : SquareRootContinuationChain.Owner
  (curve.polynomial.eval hole.cell.box.anchor)}
    (traced : PreparedPathTrace.TracedPath hole.inwardBoundary.path owner) :
      LoopMonodromy hole.inwardBoundary owner :=
  .ofTraced (Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt bank _
    (Cell.anchor_mem hole.cell hole.member)) traced (-1)
    (hole.inwardBoundary_winding.trans (by decide))

/-- The original clockwise branch-hole loop exchanges the two sheets. -/
theorem monodromy_flip (hole : PuncturedGridFaces.BranchHole bank) {owner : SquareRootContinuationChain.Owner
  (curve.polynomial.eval hole.cell.box.anchor)}
    (traced : PreparedPathTrace.TracedPath hole.inwardBoundary.path owner) : (monodromy hole traced).flip = true := rfl

/-- A retained odd loop cannot return an operationally equivalent original owner channel. -/
theorem not_returned (hole : PuncturedGridFaces.BranchHole bank) {owner : SquareRootContinuationChain.Owner
  (curve.polynomial.eval hole.cell.box.anchor)}
    (traced : PreparedPathTrace.TracedPath hole.inwardBoundary.path owner) : Gaussian.Equivalence.NamedEquivalent
      (OwnerTraceReadings.ownerName traced.finishOwner) (OwnerTraceReadings.ownerName owner) → False :=
  (monodromy hole traced).not_returned
    (monodromy_flip hole traced)

end BranchHole
end LoopMonodromy.BranchCellBank

namespace LoopMonodromy.FramedBranchCellBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.FramedBranchCellBank

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}

/-- The actual ambient exterior recovers the degree-dependent monodromy at infinity, not an independently assigned
compactification label. -/
@[expose] def monodromy (bank : Branches.FramedBranchCellBank curve branches higher)
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval (Cuts.Ambient curve).anchor)}
    (traced : PreparedPathTrace.TracedPath bank.exterior.path owner) :
      LoopMonodromy bank.exterior owner :=
  .ofTraced (Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt bank.toBranchCellBank _
    ⟨bank.frame.xLower, bank.frame.yLower⟩) traced
    curve.polynomial.natDegree bank.exterior_winding

/-- The original framed exterior loop flips sheets when the curve degree is twice the genus plus one. -/
theorem monodromy_odd (bank : Branches.FramedBranchCellBank curve branches higher)
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval (Cuts.Ambient curve).anchor)}
    (traced : PreparedPathTrace.TracedPath bank.exterior.path owner) (degree : curve.polynomial.natDegree = 2 * genus +
      1) :
    (monodromy bank traced).flip = true := by
  change decide ((curve.polynomial.natDegree : Int) % 2 ≠ 0) = true
  apply decide_eq_true
  omega

/-- The original framed exterior loop preserves sheets when the curve degree is twice the genus plus two. -/
theorem monodromy_even (bank : Branches.FramedBranchCellBank curve branches higher)
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval (Cuts.Ambient curve).anchor)}
    (traced : PreparedPathTrace.TracedPath bank.exterior.path owner) (degree : curve.polynomial.natDegree = 2 * genus +
      2) :
    (monodromy bank traced).flip = false := by
  change decide ((curve.polynomial.natDegree : Int) % 2 ≠ 0) = false
  apply decide_eq_false
  omega

end LoopMonodromy.FramedBranchCellBank

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
