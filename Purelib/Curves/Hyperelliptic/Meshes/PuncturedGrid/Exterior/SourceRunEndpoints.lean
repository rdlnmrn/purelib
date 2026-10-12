module
import Purelib.Data.List.Membership
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.Dyadic.SourceListResampling
import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Path.Resampling.OrientedBounds
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunTotals
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryFragmentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Topology.Polygon.Stokes

public section

/-! Maximal runs begin and end at the original parent's full parameters.
Use the actual side anchors and distinct-parent handoffs, without identifying
the primitive owners on opposite sides of a handoff. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns
open Purelib.Data.List
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Integration.Path.Resampling
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters (firstParameter lastParameter)
open Purelib.Integration.Path.Resampling.OrientedBounds (orientParameter orientParameter_start orientParameter_finish
  oriented_increments)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential other :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted
    differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}
  {requested : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
  {comparison : prepared.ClosedBoundaryComparison other requested minimum} {vertical : Bool}

namespace StoredSourceChord

/-- Every changed-parent junction uses the full oriented source endpoints, and the final retained chord reaches its
terminal endpoint. -/
private def parentEnds (forward : Bool) (before : SourceChordRuns.StoredSourceChord comparison vertical) :
    List (SourceChordRuns.StoredSourceChord comparison vertical) → Prop
  | [] => BoundaryTraceParameters.lastParameter before.2.forward before.2.range = (if forward then 1 else 0)
  | after :: rest =>
      (after.2.index ≠ before.2.index →
        BoundaryTraceParameters.lastParameter before.2.forward before.2.range = (if forward then 1 else 0) ∧
          BoundaryTraceParameters.firstParameter after.2.forward after.2.range = (if forward then 0 else 1)) ∧
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parentEnds forward
        after rest

/-- The retained chord word starts at its oriented initial endpoint and has full endpoints at every changed-parent
handoff. -/
private def parentWord (forward : Bool) : List (SourceChordRuns.StoredSourceChord comparison vertical) → Prop
  | [] => True
  | first :: rest => BoundaryTraceParameters.firstParameter first.2.forward first.2.range = (if forward then 0 else 1) ∧
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parentEnds forward first rest

/-- Removing a retained initial chord segment preserves the endpoint handoff certificate from its actual last chord. -/
private theorem parentEnds_tail (forward : Bool) (first : SourceChordRuns.StoredSourceChord comparison vertical)
    (before after : List (SourceChordRuns.StoredSourceChord comparison vertical))
    (ends : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parentEnds forward
      first (before ++ after)) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parentEnds forward
      (StoredSourceChord.lastChord first before) after := by
  induction before generalizing first with
  | nil => exact ends
  | cons next rest ih => exact ih next ends.2

/-- The original indexed chord bank's distinct-parent handoffs and final endpoint certify its complete parent-end word.
-/
private theorem parentEnds_ofFn {n : Nat} (forward : Bool) (source : Fin (n + 1) → SourceChordRuns.StoredSourceChord
  comparison vertical)
    (joins : ∀ i : Fin n, (source i.succ).2.index ≠ (source i.castSucc).2.index →
      BoundaryTraceParameters.lastParameter (source i.castSucc).2.forward (source i.castSucc).2.range = (if forward then
        1 else 0) ∧
        BoundaryTraceParameters.firstParameter (source i.succ).2.forward (source i.succ).2.range = (if forward then 0
          else 1))
    (finish : BoundaryTraceParameters.lastParameter (source (Fin.last n)).2.forward (source (Fin.last n)).2.range = (if
      forward then 1 else 0)) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parentEnds forward (source 0)
      (List.ofFn (fun i : Fin n => source i.succ)) := by
  induction n with
  | zero => exact finish
  | succ n ih =>
    rw [OfFn.Basic.ofFn_succ]
    exact ⟨joins 0, ih (fun i => source i.succ) (fun i => joins i.succ) finish⟩

end StoredSourceChord

/-- Read the original parent primitive's endpoint difference in the selected traversal direction. -/
@[expose] def sourceParentIncrement (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (forward : Bool) (parent : Fin comparison.original.plans.length) : PrimitivePoint :=
  (comparison.sourceValues parent (if forward then 1 else 0)).sub
    (comparison.sourceValues parent (if forward then 0 else 1))

namespace SourceChordRun

/-- The retained run starts and finishes at its original parent's full endpoints in the selected direction. -/
@[expose] def FullEndpoints (run : SourceChordRuns.SourceChordRun comparison vertical) (forward : Bool) : Prop :=
  BoundaryTraceParameters.firstParameter run.first.2.forward run.first.2.range = (if forward then 0 else 1) ∧
    BoundaryTraceParameters.lastParameter (StoredSourceChord.lastChord run.first run.rest).2.forward
      (StoredSourceChord.lastChord run.first run.rest).2.range = (if forward then 1 else 0)

/-- Orient the original complete run parameters into a chain from zero to one with unchanged sampled increments and paid
mesh widths. -/
theorem sampling_mesh (run : SourceChordRuns.SourceChordRun comparison vertical) (forward : Bool) {width :
  InverseRootPolynomial.Coordinate}
    (sampling : run.values = SourceListResampling.increments (comparison.sourceValues run.parent)
      (BoundaryTraceParameters.firstParameter run.first.2.forward run.first.2.range) run.parameters)
    (bounds : SourceResampling.Chain (OrientedBounds.orientParameter forward (BoundaryTraceParameters.firstParameter
      run.first.2.forward run.first.2.range))
      (run.parameters.map (OrientedBounds.orientParameter forward))
      (OrientedBounds.orientParameter forward (BoundaryTraceParameters.lastParameter (StoredSourceChord.lastChord
        run.first run.rest).2.forward
        (StoredSourceChord.lastChord run.first run.rest).2.range)) ∧
      SourceResampling.widths (OrientedBounds.orientParameter forward (BoundaryTraceParameters.firstParameter
        run.first.2.forward run.first.2.range))
        (run.parameters.map (OrientedBounds.orientParameter forward)) width)
    (ends : run.FullEndpoints forward) :
    run.values = SourceListResampling.increments
      (fun parameter => comparison.sourceValues run.parent (OrientedBounds.orientParameter forward parameter)) 0
      (run.parameters.map (OrientedBounds.orientParameter forward)) ∧
    SourceResampling.Chain 0 (run.parameters.map (OrientedBounds.orientParameter forward)) 1 ∧
      SourceResampling.widths 0 (run.parameters.map (OrientedBounds.orientParameter forward)) width := by
  have first := (congrArg (OrientedBounds.orientParameter forward) ends.1).trans (OrientedBounds.orientParameter_start
    forward)
  have last := (congrArg (OrientedBounds.orientParameter forward) ends.2).trans (OrientedBounds.orientParameter_finish
    forward)
  have chain := Eq.mp (congrArg₂ (fun first last =>
    SourceResampling.Chain first (run.parameters.map (OrientedBounds.orientParameter forward)) last) first last)
      bounds.1
  have steps := Eq.mp (congrArg (fun first =>
    SourceResampling.widths first (run.parameters.map (OrientedBounds.orientParameter forward)) width) first) bounds.2
  have oriented := sampling.trans (OrientedBounds.oriented_increments (comparison.sourceValues run.parent) forward
    (BoundaryTraceParameters.firstParameter run.first.2.forward run.first.2.range) run.parameters).symm
  exact ⟨oriented.trans (congrArg (fun start => SourceListResampling.increments
    (fun parameter => comparison.sourceValues run.parent (OrientedBounds.orientParameter forward parameter)) start
    (run.parameters.map (OrientedBounds.orientParameter forward))) first), chain, steps⟩

/-- A maximal retained run has full source endpoints, and the remaining runs retain their parent-word certificate. -/
private theorem run_end (run : SourceChordRuns.SourceChordRun comparison vertical) (rest : List
  (SourceChordRuns.SourceChordRun comparison vertical))
    (forward : Bool) (apart : SourceChordRun.startsApart run.parent rest)
    (word : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parentWord forward
      ((run :: rest).map SourceChordRun.chords).flatten) :
    run.FullEndpoints forward ∧
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parentWord forward (rest.map
      SourceChordRun.chords).flatten := by
  have ends := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parentEnds_tail
    forward run.first run.rest (rest.map SourceChordRun.chords).flatten word.2
  cases rest with
  | nil => exact ⟨⟨word.1, ends⟩, True.intro⟩
  | cons next tail =>
    have different : next.first.2.index ≠ (StoredSourceChord.lastChord run.first run.rest).2.index := by
      intro equal
      exact apart (run.last_parent.symm.trans (equal.symm.trans next.first_parent))
    have boundary := ends.1 different
    exact ⟨⟨word.1, boundary.1⟩, ⟨boundary.2, ends.2⟩⟩

/-- Every separated run in the original parent word has its full oriented source endpoints. -/
private theorem runs_endpoints (runs : List (SourceChordRuns.SourceChordRun comparison vertical)) (forward : Bool)
    (apart : SourceChordRun.separated runs) (word :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parentWord forward (runs.map
      SourceChordRun.chords).flatten) :
    ∀ run ∈ runs, run.FullEndpoints forward := by
  induction runs with
  | nil => intro _ member; cases member
  | cons run rest ih =>
    have ends := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.run_end run rest
      forward apart.1 word
    intro found member
    rcases Data.List.Membership.mem_cons.mp member with rfl | member
    · exact ends.1
    · exact ih apart.2 ends.2 found member

/-- Read the complete oriented endpoint increment of the run's retained original parent. -/
@[expose] def parentIncrement (run : SourceChordRuns.SourceChordRun comparison vertical) (forward : Bool) :
  PrimitivePoint :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.sourceParentIncrement comparison forward run.parent

/-- The run's actual endpoint increment equals its original parent increment when both full endpoints are retained. -/
theorem endpointIncrement_eq (run : SourceChordRuns.SourceChordRun comparison vertical) {forward : Bool}
    (ends : run.FullEndpoints forward) : run.endpointIncrement = run.parentIncrement forward := by
  have first := congrArg₂ (fun (index : Fin comparison.original.plans.length) (parameter :
    InverseRootPolynomial.Coordinate) =>
    comparison.sourceValues index parameter) run.first_parent ends.1
  have last := congrArg₂ (fun (index : Fin comparison.original.plans.length) (parameter :
    InverseRootPolynomial.Coordinate) =>
    comparison.sourceValues index parameter) run.last_parent ends.2
  exact congrArg₂ PrimitivePoint.sub last first

/-- Full endpoint certificates identify the original run-endpoint increment list with its retained parent-increment
list. -/
private theorem mapped_endpoints (runs : List (SourceChordRuns.SourceChordRun comparison vertical)) (forward : Bool)
    (ends : ∀ run ∈ runs, run.FullEndpoints forward) :
    runs.map SourceChordRun.endpointIncrement = runs.map (fun run => run.parentIncrement forward) :=
  Map.map_congr_left (fun run member => run.endpointIncrement_eq (ends run member))

end SourceChordRun

namespace SourceChordGrouping

/-- Maximal grouping of the original indexed chord bank preserves full endpoints of every retained run. -/
theorem endpoints_ofFn {n : Nat} {source : Fin (n + 1) → SourceChordRuns.StoredSourceChord comparison vertical}
    (grouped : SourceChordRuns.SourceChordGrouping comparison vertical (List.ofFn source)) (forward : Bool)
    (joins : ∀ i : Fin n, (source i.succ).2.index ≠ (source i.castSucc).2.index →
      BoundaryTraceParameters.lastParameter (source i.castSucc).2.forward (source i.castSucc).2.range = (if forward then
        1 else 0) ∧
        BoundaryTraceParameters.firstParameter (source i.succ).2.forward (source i.succ).2.range = (if forward then 0
          else 1))
    (start : BoundaryTraceParameters.firstParameter (source 0).2.forward (source 0).2.range = (if forward then 0 else
      1))
    (finish : BoundaryTraceParameters.lastParameter (source (Fin.last n)).2.forward (source (Fin.last n)).2.range = (if
      forward then 1 else 0)) :
    ∀ run ∈ grouped.runs, run.FullEndpoints forward := by
  have word : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parentWord forward
    (List.ofFn source) := by
    rw [OfFn.Basic.ofFn_succ]
    exact ⟨start, Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parentEnds_ofFn
      forward source joins finish⟩
  rw [← grouped.flattened] at word
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.runs_endpoints grouped.runs
    forward grouped.separated word

/-- The exact original sampled run totals equal their full retained parent increments in run order. -/
theorem full_totals (grouped : SourceChordRuns.SourceChordGrouping comparison vertical chords) (forward : Bool)
    (totals : (grouped.runs.map SourceChordRun.values).map PairedIncrementArea.total =
      grouped.runs.map SourceChordRun.endpointIncrement)
    (ends : ∀ run ∈ grouped.runs, run.FullEndpoints forward) :
    (grouped.runs.map SourceChordRun.values).map PairedIncrementArea.total =
      grouped.runs.map (fun run => run.parentIncrement forward) :=
  totals.trans (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.mapped_endpoints
    grouped.runs forward ends)

end SourceChordGrouping
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns
