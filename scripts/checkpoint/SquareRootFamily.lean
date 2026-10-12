module

import Purelib.System.FilePath

import Purelib.Data.Json.Codec
import Purelib.Data.String.Basic
import scripts.checkpoint.RootRefinement
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.RootContinuation.SquareRootOwnerFamily

import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.RootContinuation.SquareRootOwnerReplay
public import Purelib.Riemann.RootContinuation.RootOwnerFrameReplay
public import scripts.checkpoint.InitialExtraction
import Batteries.Logic
import Init.Data.List.OfFn
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.Exact.LargeSquare
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.Track.Basic
import scripts.checkpoint.Integration

open Purelib

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.RootContinuation.RootOwnerFrameReplay

open Purelib.Riemann.RootContinuation.RootOwnerFrames

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.Data (Json)
open scoped Purelib.Data.String
open Purelib.Data.Json (toJson)

public section

/-!
Checked ordered endpoint-family restoration using the shared isolation
loader.  The continuation receives the original two owners and their erased
source equations.  This does not prepare dyadic banks or select a new sheet.
-/

namespace SquareRootFamilyCheckpoint

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]
  [MonadExceptOf IO.Error m] [MonadStateOf RootRefinementCheckpoint.Counts m]

/-- Restore the original ordered pair of independent square-root owners.

Checked isolation data supplies the original family and its source equations; the continuation receives those exact
owners without preparing new banks. -/
@[expose] def withFamily {parameter : Data.Gaussian.Basic.Canonical} (nonzero : parameter ≠ 0)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (use : SquareRootOwnerFamily.IndependentFamily parameter → m Unit) : m Unit := do
  let source := SquareRootOwnerReplay.input nonzero
  IO.FS.createDirAll directory
  IntegrationCheckpoint.profile directory "BEGIN exact independent square-root family restoration"
  let result ← InitialExtractionCheckpoint.isolateLargeSquare source.elimination
    (.separated ⟨control.savedOnly, pure ()⟩ _ source.nonzero source.degreePositive)
    source.degreeAtLeastTwo source.squarefree
    control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("isolation"))))
  let family := SquareRootOwnerReplay.family nonzero result.val result.property
  IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("owners.json")))) (toJson
    (List.ofFn fun sheet : Fin 2 => InitialExtractionCheckpoint.stateData (family.owner sheet).track.initial))
  IntegrationCheckpoint.profile directory "END exact two-sheet family restored; bank preparation still separate"
  use family

/-- Restore the complete canonical grid endpoint frame from checked isolation proposals. The equality includes the
frame's executable classifier. -/
@[expose] def withFrame {parameter : Data.Gaussian.Basic.Canonical} (nonzero : parameter ≠ 0)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    {α : Type} (use : {frame : RootOwnerFrames.OwnerFrame parameter //
      frame = OwnerFrame.build nonzero} → m α) : m α := do
  let source := SquareRootReconditioning.isolationInput nonzero
  IO.FS.createDirAll directory
  let result ← InitialExtractionCheckpoint.isolateLargeSquare source.elimination
    (.separated ⟨control.savedOnly, pure ()⟩ _ source.nonzero source.degreePositive)
    source.degreeAtLeastTwo source.squarefree
    control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("isolation"))))
  let saved : OwnerFrameReplay.Saved nonzero := result
  let frame := OwnerFrameReplay.restore nonzero saved
  IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("frame-owners.json"))))
    (toJson
    (List.ofFn fun sheet : Fin 2 => InitialExtractionCheckpoint.stateData (frame.owners sheet).track.initial))
  use ⟨frame, OwnerFrameReplay.restore_eq nonzero saved⟩

namespace GridFrames

open Purelib.RootIsolation.SquareRoot.Grid.RootFrames
open Purelib.Riemann
open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Polynomial.Geometry.Grid.ClearGrid

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box}

/-- One retained vertical line, in the grid's original horizontal order. -/
@[expose] def row (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (vertical : ClearGrid.VerticalLine polynomial ambient) (offset : Nat) :
    (horizontal : List (ClearGrid.HorizontalLine polynomial ambient)) → m {entries : List (RootFrames.RootFrameEntry
      polynomial) //
      entries = horizontal.map (RootFrameEntry.ofLines vertical)}
  | [] => pure ⟨[], rfl⟩
  | first :: remaining => do
      withFrame (RootFramesReplay.pointNonzero vertical first) control ((Purelib.System.FilePath.join directory
        (System.FilePath.mk (toString offset)))) fun frame => do
        let tail ← row control directory vertical (offset + 1) remaining
        return ⟨RootFramesReplay.entry vertical first frame.val :: tail.val,
          congrArg₂ List.cons (RootFramesReplay.entry_eq vertical first frame.val frame.property) tail.property⟩

/-- Traverse each endpoint once, retaining the exact canonical flat-map order. -/
@[expose] def rows (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (horizontal : List (ClearGrid.HorizontalLine polynomial ambient)) (offset : Nat) :
    (vertical : List (ClearGrid.VerticalLine polynomial ambient)) → m {entries : List (RootFrames.RootFrameEntry
      polynomial) //
      entries = vertical.flatMap (fun line => horizontal.map (RootFrameEntry.ofLines line))}
  | [] => pure ⟨[], rfl⟩
  | first :: remaining => do
      let head ← row control ((Purelib.System.FilePath.join directory (System.FilePath.mk (toString offset)))) first 0
        horizontal
      let tail ← rows control directory horizontal (offset + 1) remaining
      return ⟨head.val ++ tail.val, congrArg₂ List.append head.property tail.property⟩

/-- The caller receives the original complete root-frame cache with an exact ownership equation. Edge transport and
corrected periods remain separate. -/
@[expose] def restore (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) : m {frames :
      RootIsolation.SquareRoot.Grid.RootFrames grid // frames =
        RootIsolation.SquareRoot.Grid.RootFrames.build
      grid} := do
  let entries ← rows control directory grid.horizontal 0 grid.vertical
  return ⟨RootFramesReplay.restore grid entries.val entries.property,
    RootFramesReplay.restore_eq grid entries.val entries.property⟩

end GridFrames

end SquareRootFamilyCheckpoint
