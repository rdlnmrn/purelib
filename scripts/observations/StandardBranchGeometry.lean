module
import Purelib.Data.Fin

import Purelib.System.IO
import Purelib.System.FilePath

import Purelib.Data.Json.Codec
import Purelib.Data.Json.Basic
import Purelib.Data.Json.Printer
import Purelib.Data.String.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Substitution.QuarterTurn
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Elimination.Separated.Sylvester
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.Exact.LargeSquare
import Purelib.Polynomial.Elimination.Axis.Replay
public import Purelib.RootIsolation.Exact.Replay.Elimination

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Riemann.Periods.PeriodCurves
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolationReplay
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBankReplay
public import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBankReplay
import scripts.checkpoint.InitialExtraction
public import scripts.checkpoint.SquareRootFamily
import Init.Data.Fin.Basic
import Init.Data.Fin.Lemmas
import Init.Data.List.OfFn
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Replay
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.SquareRoot.Grid.Branch.Location
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Track.Newton.Canonical
import Purelib.RootIsolation.Track.Newton.Refinement
import scripts.checkpoint.Integration
import scripts.checkpoint.RootRefinement
import scripts.checkpoint.RootState

-- Use complete constructor eliminators for the original match arms.
set_option backward.match.sparseCases false

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Polynomial.Dense.Gaussian.Bounds

open Purelib.Polynomial.Dense.Gaussian.Substitution

open Purelib.Polynomial.Elimination.Axis

open Purelib.Polynomial.Elimination.Axis.Certificate

open Purelib.Polynomial.Elimination.Separated

open Purelib.Riemann.Meshes

open Purelib.Riemann.Periods

open Purelib.RootIsolation

open Purelib.RootIsolation.Exact

open Purelib.RootIsolation.Exact.Replay

open Purelib.Data (Json)
open scoped Purelib.Data.String
open Purelib.Data.Json (toJson)

public section

/-!
Inspect the actual canonical branch enumeration of the named genus-two
curves before making a standard-tour intersection claim. Ordered extraction
checkpoints reconstruct the original isolation and complete branch-interface
equality. The optional cells modes restore the original unframed branch-cell
bank; framed modes additionally restore the enclosing frame and its classified
faces. Roots modes restore the canonical endpoint frames on that grid.
These modes do not report edge transport or a period certificate.
Exhausted initial seeds enter the canonical total Newton-band extraction.

Polynomial inverse stages, Newton and rounding proposals are saved atomically.
`replay` forbids all stage and proposal generators. Local polynomial equations,
winding and clearance validation still run on reload; those checks are not cached.
Run PolynomialInverseCheckpointHarness's self-test and the existing root
trace-self-test before a long run. The cells modes also require the native
canonical-isolation harness Newton restart regression. Execute runs in a systemd
memory scope with an explicit SIGKILL timeout. Existing ordered-extraction
checkpoints remain valid; resume adds the missing axis-stage files beside them.
-/

namespace StandardBranchGeometryHarness

open Purelib.Riemann
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Branches Purelib.Riemann.Integration Purelib.Riemann.Topology
open IntegrationCheckpoint

/-- Collect an ordered finite vector of values while retaining every exact source equation.

Each dependent IO result is consumed once and the output preserves the original Fin indexing. -/
@[expose] def collect {m : Type → Type} [Monad m] {K : Type} : {n : Nat} → (spec : Fin n → K) →
    ((index : Fin n) → m {value : K // value = spec index}) →
    m {values : Data.Vector K n // ∀ index, values index = spec index}
  | 0, _, _ => pure ⟨.nil, fun index => Fin.elim0 index⟩
  | _ + 1, spec, fetch => do
      let head ← fetch 0
      let tail ← collect (fun index => spec index.succ) (fun index => fetch index.succ)
      return ⟨.cons head.val tail.val, by
        intro index
        refine Data.Fin.cases_induction head.property (fun next => ?_) index
        exact tail.property next⟩

/-- Each branch reuses the restored eliminant and retains its own canonical Newton-source checkpoints. The returned bank
includes its full owner equation. -/
@[expose] def cells {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (higher : 1 < curve.polynomial.natDegree) {degreeBound : Nat}
    (elimination : AxisSafeCuts.AxisEliminationCertificate curve.polynomial degreeBound)
    (output : Exact.Basic.Output curve.polynomial (Cuts.Ambient curve) curve.polynomial.natDegree)
    (same : output = LargeSquare.isolateLargeSquare higher curve.squarefree elimination)
    (directory : System.FilePath) (savedOnly : Bool) :
    IO {bank : Branches.BranchCellBank curve (BranchIsolationReplay.data curve higher output) higher //
      bank = BranchCellBank.ofData curve (BranchIsolationReplay.data curve higher output) higher} := do
  let action : PolynomialInverseCheckpoint.Execution ({bank : Branches.BranchCellBank curve (BranchIsolationReplay.data
    curve higher output) higher //
      bank = BranchCellBank.ofData curve (BranchIsolationReplay.data curve higher output) higher}) := do
    IO.FS.createDirAll directory
    let branches := BranchIsolationReplay.data curve higher output
    let budget := BranchCellBankReplay.budget curve branches higher
    let control ← PolynomialInverseCheckpoint.Control.create savedOnly
    let states ← collect (BranchCellBankReplay.refined curve branches higher) fun index => do
      let original := BranchCellBankReplay.original curve branches higher index
      profile directory s!"BEGIN original branch-cell refinement {index.val}"
      let state ← NewtonExtractionCheckpoint.refineState higher curve.squarefree elimination original
        budget.radius budget.radius_positive control ((Purelib.System.FilePath.join directory (System.FilePath.mk
          (s!"branch-{index.val}"))))
      have canonical := BranchCellBankReplay.restored_track curve higher elimination output same index
      have linked := state.property.trans (canonical original budget.radius budget.radius_positive).symm
      profile directory s!"END original branch-cell refinement {index.val}"
      return ⟨state.val, linked⟩
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("counts.json")))) (←
      PolynomialInverseCheckpoint.Execution.counts)
    let bank := BranchCellBankReplay.restore curve branches higher states.val states.property
    return ⟨bank, BranchCellBankReplay.restore_eq curve branches higher states.val states.property⟩
  let (result, _) ← PolynomialInverseCheckpoint.Execution.run action {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) result

/-- Restore the enclosing frame from the original second branch refinements, then classify its actual finite faces using
the retained branch locations. -/
@[expose] def framed {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (higher : 1 < curve.polynomial.natDegree) {degreeBound : Nat}
    (elimination : AxisSafeCuts.AxisEliminationCertificate curve.polynomial degreeBound)
    (output : Exact.Basic.Output curve.polynomial (Cuts.Ambient curve) curve.polynomial.natDegree)
    (same : output = LargeSquare.isolateLargeSquare higher curve.squarefree elimination)
    (bank : Branches.BranchCellBank curve (BranchIsolationReplay.data curve higher output) higher)
    (directory : System.FilePath) (savedOnly : Bool) :
    IO {grid : Meshes.FramedPuncturedGrid curve (BranchIsolationReplay.data curve higher output) higher //
      grid = FramedPuncturedGrid.ofBank bank.framed} := do
  let action : PolynomialInverseCheckpoint.Execution ({grid : Meshes.FramedPuncturedGrid curve
    (BranchIsolationReplay.data curve higher output) higher //
      grid = FramedPuncturedGrid.ofBank bank.framed}) := do
    IO.FS.createDirAll directory
    let budget := FramedBranchCellBankReplay.budget bank
    let control ← PolynomialInverseCheckpoint.Control.create savedOnly
    let states ← collect (FramedBranchCellBankReplay.refined bank) fun index => do
      let original := BranchCellWinding.state bank index
      profile directory s!"BEGIN original framed-branch refinement {index.val}"
      let state ← NewtonExtractionCheckpoint.refineState higher curve.squarefree elimination original
        budget.radius budget.radius_positive control ((Purelib.System.FilePath.join directory (System.FilePath.mk
          (s!"branch-{index.val}"))))
      have canonical := BranchCellBankReplay.restored_track curve higher elimination output same index
      have linked := state.property.trans (canonical original budget.radius budget.radius_positive).symm
      profile directory s!"END original framed-branch refinement {index.val}"
      return ⟨state.val, linked⟩
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("counts.json")))) (←
      PolynomialInverseCheckpoint.Execution.counts)
    return ⟨FramedBranchCellBankReplay.punctured bank states.val states.property,
      FramedBranchCellBankReplay.punctured_eq bank states.val states.property⟩
  let (result, _) ← PolynomialInverseCheckpoint.Execution.run action {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) result

/-- Restore the original ordered branch isolation and requested geometric caches.

Reuse checked polynomial and Newton stages, retain complete source equalities and compare exact saved readbacks of
cells, frames and endpoint roots. -/
@[expose] def inspect {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (higher : 1 < curve.polynomial.natDegree) (directory : System.FilePath) (savedOnly : Bool)
    (acquireCells : Bool := false) (acquireFrame : Bool := false) (acquireRoots : Bool := false) : IO Unit := do
  let action : RootRefinementCheckpoint.Execution Unit := do
    IO.FS.createDirAll directory
    let source := BranchIsolationReplay.input curve higher
    let control ← RootRefinementCheckpoint.Control.create savedOnly
    profile directory "BEGIN canonical branch enumeration; finite winding/clearance validation is not cached"
    profile directory "BEGIN checked axis-elimination stage replay; local arithmetic validation is not cached"
    let polynomialControl ← PolynomialInverseCheckpoint.Control.create savedOnly
    let axisAction : PolynomialInverseCheckpoint.Execution _ := do
      let first ← PolynomialInverseCheckpoint.run polynomialControl ((Purelib.System.FilePath.join directory
        (System.FilePath.mk ("axis-vertical")))) _
        (Sylvester.separatedSylvester curve.polynomial)
      let second ← PolynomialInverseCheckpoint.run polynomialControl ((Purelib.System.FilePath.join directory
        (System.FilePath.mk ("axis-horizontal")))) _
        (Sylvester.separatedSylvester (QuarterTurn.quarterTurn curve.polynomial))
      return (first, second)
    let (axisResult, axisCounts) ← PolynomialInverseCheckpoint.Execution.run axisAction {}
    let (first, second) ← (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) axisResult
    let elimination := Replay.certificate first second source.nonzero source.degreePositive
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("axis-counts.json")))) axisCounts
    profile directory "END checked axis-elimination stage replay; BEGIN ordered extraction checkpoints"
    let result ← InitialExtractionCheckpoint.isolateLargeSquare elimination
      (.direct elimination (.canonical elimination)) source.degreeAtLeastTwo source.squarefree
      control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("branches"))))
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("proposal-counts.json")))) (←
      RootRefinementCheckpoint.Execution.counts)
    let isolated := result
    have canonicalIsolation : isolated.val = source.isolation := by
      exact isolated.property.trans (Elimination.isolation_eq first second
        source.nonzero source.degreePositive source.degreeAtLeastTwo source.squarefree)
    let branches := BranchIsolationReplay.data curve higher isolated.val
    let canonical : { value : BranchIsolation.Data curve // value = BranchIsolation.data curve } :=
      ⟨branches, BranchIsolationReplay.data_eq curve higher isolated.val canonicalIsolation⟩
    let states := List.ofFn fun index : Fin canonical.val.siteCount =>
      InitialExtractionCheckpoint.stateData (canonical.val.track higher index).initial
    let geometry := Json.mkObj
      [("format", toJson "ccl-canonical-branch-geometry-v1"),
       ("scope", toJson "exact canonical branch-interface readback; no lifted intersection or period claim"),
       ("polynomial", toJson (curve.polynomial.coeffs.map gaussianData)),
       ("genus", toJson genus),
       ("ambient", toJson (RootStateCheckpoint.boxData (RootRadius.Box.largeSquareBox curve.polynomial))),
       ("orderedStates", Json.arr states.toArray)]
    let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("geometry.json")))
    if ← path.pathExists then
      let saved : Json ← loadJson path
      unless saved == geometry do
        saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid-geometry.json")))) (saved,
          geometry)
        throw (IO.userError "canonical geometry changed; both exact readbacks retained")
    else
      saveJson path geometry
    profile directory "END exact canonical branch enumeration; original source equality reconstructed"
    Purelib.System.IO.println geometry.compress
    Purelib.System.IO.println (toJson (← RootRefinementCheckpoint.Execution.counts)).compress
    if acquireCells then
      let bank ← cells curve higher elimination isolated.val isolated.property ((Purelib.System.FilePath.join directory
        (System.FilePath.mk ("cells")))) savedOnly
      let rows := List.ofFn fun index : Fin branches.siteCount =>
        (RootStateCheckpoint.boxData (bank.val.cell index).box,
         InitialExtractionCheckpoint.stateData (bank.val.rows index).location.state)
      let actual := toJson rows
      let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("cells/geometry.json")))
      if ← path.pathExists then
        let expected : Json ← loadJson path
        unless actual == expected do
          saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("cells/invalid-geometry.json"))))
            (actual, expected)
          throw (IO.userError "restored branch cells changed; both exact readbacks retained")
      else saveJson path actual
      Purelib.System.IO.println s!"Exact canonical branch-cell bank restored: {rows.length} branches."
      if acquireFrame then
        let restored ← framed curve higher elimination isolated.val isolated.property bank.val
          ((Purelib.System.FilePath.join directory (System.FilePath.mk ("frame")))) savedOnly
        let linked : {grid : Meshes.FramedPuncturedGrid curve branches higher //
            grid = FramedPuncturedGrid.ofData curve branches higher} :=
          ⟨restored.val, restored.property.trans
            (congrArg (fun value => FramedPuncturedGrid.ofBank value.framed) bank.property)⟩
        let grid := linked.val
        let rows := List.ofFn fun index : Fin branches.siteCount =>
          (RootStateCheckpoint.boxData (grid.bank.toBranchCellBank.cell index).box,
           InitialExtractionCheckpoint.stateData (grid.bank.rows index).location.state)
        let actual := Json.mkObj
          [("vertical", toJson (grid.bank.grid.vertical.map fun line => fractionData line.coordinate)),
           ("horizontal", toJson (grid.bank.grid.horizontal.map fun line => fractionData line.coordinate)),
           ("branches", toJson rows), ("holes", toJson grid.faces.holes.length),
           ("regularFaces", toJson grid.faces.regulars.length)]
        let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("frame/geometry.json")))
        if ← path.pathExists then
          let expected : Json ← loadJson path
          unless actual == expected do
            saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("frame/invalid-geometry.json"))))
              (actual, expected)
            throw (IO.userError "restored framed grid changed; both exact readbacks retained")
        else saveJson path actual
        Purelib.System.IO.println
          s!"Exact canonical framed grid restored: {grid.faces.holes.length} holes and {grid.faces.regulars.length} \
            regular faces."
        if acquireRoots then
          let rootControl ← RootRefinementCheckpoint.Control.create savedOnly
          let vertexAction : RootRefinementCheckpoint.Execution _ :=
            SquareRootFamilyCheckpoint.GridFrames.restore rootControl ((Purelib.System.FilePath.join directory
              (System.FilePath.mk ("vertex-roots")))) grid.bank.grid
          let (vertexResult, vertexCounts) ← RootRefinementCheckpoint.Execution.run vertexAction {}
          let frames ← (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) vertexResult
          let snapshot := toJson (frames.val.entries.map fun entry =>
            (gaussianData entry.point, List.ofFn fun sheet : Fin 2 =>
              InitialExtractionCheckpoint.stateData (entry.frame.owners sheet).track.initial))
          saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("vertex-root-counts.json"))))
            vertexCounts
          let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("vertex-frames.json")))
          if ← path.pathExists then
            let expected : Json ← loadJson path
            unless snapshot == expected do
              saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid-vertex-frames.json"))))
                (snapshot, expected)
              throw (IO.userError "restored vertex frames changed; both exact readbacks retained")
          else saveJson path snapshot
          Purelib.System.IO.println s!"Exact canonical endpoint frames restored: {frames.val.entries.length} vertices."
  let (result, _) ← RootRefinementCheckpoint.Execution.run action {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) result

end StandardBranchGeometryHarness

/-- Select the quadratic, quintic or sextic branch-geometry checkpoint and requested replay depth. -/
@[expose] def main (arguments : List String) : IO Unit := do
  match arguments with
  | [curve, directory, mode] =>
      unless mode == "resume" || mode == "replay" || mode == "cells-resume" || mode == "cells-replay" ||
          mode == "framed-resume" || mode == "framed-replay" || mode == "roots-resume" || mode == "roots-replay" do
        throw (IO.userError "mode must select resume or replay for branches, cells, framed grid or roots")
      let savedOnly := mode == "replay" || mode == "cells-replay" || mode == "framed-replay" || mode == "roots-replay"
      let acquireRoots := mode == "roots-resume" || mode == "roots-replay"
      let acquireFrame := acquireRoots || mode == "framed-resume" || mode == "framed-replay"
      let acquireCells := acquireFrame || mode == "cells-resume" || mode == "cells-replay"
      match curve with
      | "quadratic" =>
          StandardBranchGeometryHarness.inspect PeriodCurves.quadraticCurve
            (by decide) directory savedOnly acquireCells acquireFrame acquireRoots
      | "quintic" =>
          StandardBranchGeometryHarness.inspect PeriodCurves.quinticCurve
            (by decide) directory savedOnly acquireCells acquireFrame acquireRoots
      | "sextic" =>
          StandardBranchGeometryHarness.inspect PeriodCurves.sexticCurve
            (by decide) directory savedOnly acquireCells acquireFrame acquireRoots
      | _ => throw (IO.userError "curve must be quadratic, quintic or sextic")
  | _ => throw (IO.userError
    "usage: StandardBranchGeometryHarness.lean quadratic|quintic|sextic DIRECTORY resume|replay|cells-resume|\
      cells-replay|framed-resume|framed-replay|roots-resume|roots-replay")
