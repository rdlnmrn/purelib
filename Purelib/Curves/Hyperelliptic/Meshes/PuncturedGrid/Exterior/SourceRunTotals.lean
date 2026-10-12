module
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns
import Purelib.Integration.Path.Dyadic.SourceListResampling
public import Purelib.Integration.Path.Resampling.OrientedBounds
import Purelib.Data.List.Flatten
import Init.Data.List.OfFn
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryFragmentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Topology.Polygon.Stokes

public section

/-! Telescope only the totals of the actual consecutive same-parent runs.
Internal run areas remain present in the consuming whole-side formula. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns
open Purelib.Data
open Purelib.Data.List
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Integration.Path.Dyadic.SourceListResampling
open Purelib.Integration.Path.Resampling
open Purelib.Riemann.Paths
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordData (sourceParameters sourceParameters_first
  sourceParameters_last)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns (StoredSourceChord SourceChordRun)
open Purelib.Integration.Path.Resampling.OrientedBounds (orientParameter sourceParameters_chain sourceParameters_widths)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters (firstParameter lastParameter)
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

/-- Read the original chord's ordered source parameters after each retained dyadic step. -/
@[expose] def parameters (chord : SourceChordRuns.StoredSourceChord comparison vertical) : List Coordinate :=
  List.ofFn (fun edge : Fin (RectangularDyadicPairedTrace.dyadicCount chord.2.depth) =>
    SourceChordData.sourceParameters chord.2.forward chord.2.range chord.2.depth edge.succ)

/-- The final retained parameter of the original chord is its certified terminal source parameter. -/
private theorem parameters_terminal (chord : SourceChordRuns.StoredSourceChord comparison vertical) :
    SourceListResampling.terminal (BoundaryTraceParameters.firstParameter chord.2.forward chord.2.range)
      chord.parameters =
      BoundaryTraceParameters.lastParameter chord.2.forward chord.2.range := by
  exact (congrArg (fun first => SourceListResampling.terminal first chord.parameters)
    (SourceChordData.sourceParameters_first chord.2.forward chord.2.range chord.2.depth).symm).trans
      ((SourceListResampling.terminal_ofFn _).trans (SourceChordData.sourceParameters_last ..))

/-- The original chord parameters form an oriented source chain with every step bounded by the paid dyadic width. -/
private theorem parameter_bounds (chord : SourceChordRuns.StoredSourceChord comparison vertical) (forward : Bool)
    (direction : chord.2.forward = forward) {width : InverseRootPolynomial.Coordinate}
    (bounded : (1 / 2 : InverseRootPolynomial.Coordinate) ^ chord.2.depth ≤ width) :
    SourceResampling.Chain (OrientedBounds.orientParameter forward (BoundaryTraceParameters.firstParameter
      chord.2.forward chord.2.range))
      (chord.parameters.map (OrientedBounds.orientParameter forward)) (OrientedBounds.orientParameter forward
        (BoundaryTraceParameters.lastParameter chord.2.forward chord.2.range)) ∧
    SourceResampling.widths (OrientedBounds.orientParameter forward (BoundaryTraceParameters.firstParameter
      chord.2.forward chord.2.range))
      (chord.parameters.map (OrientedBounds.orientParameter forward)) width := by
  cases direction
  dsimp only [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parameters, -eq_self,
    -iff_self]
  rw [OfFn.Basic.map_ofFn]
  exact ⟨sourceParameters_chain .., OrientedBounds.sourceParameters_widths _ _ _ chord.2.within bounded⟩

/-- The original cached chord increments equal sampling its exact retained source parameter list. -/
private theorem increments_parameters (chord : SourceChordRuns.StoredSourceChord comparison vertical) :
    chord.increments = SourceListResampling.increments (comparison.sourceValues chord.2.index)
      (BoundaryTraceParameters.firstParameter chord.2.forward chord.2.range) chord.parameters := by
  exact (CenteredPathIncrements.Sample.increments_raw chord.2.sample).trans
    ((SourceListResampling.increments_ofFn _ _).symm.trans
      (congrArg (fun first => SourceListResampling.increments (comparison.sourceValues chord.2.index)
        first chord.parameters) (SourceChordData.sourceParameters_first ..)))

/-- Read the original source primitive at the retained chord's initial parameter. -/
@[expose] def startValue (chord : SourceChordRuns.StoredSourceChord comparison vertical) : PrimitivePoint :=
  comparison.sourceValues chord.2.index (BoundaryTraceParameters.firstParameter chord.2.forward chord.2.range)

/-- Read the original source primitive at the retained chord's terminal parameter. -/
@[expose] def finishValue (chord : SourceChordRuns.StoredSourceChord comparison vertical) : PrimitivePoint :=
  comparison.sourceValues chord.2.index (BoundaryTraceParameters.lastParameter chord.2.forward chord.2.range)

/-- The retained physical chord intervals follow consecutively from the supplied lower endpoint. -/
private def physicalAfter (lower : InverseRootPolynomial.Coordinate) : List (SourceChordRuns.StoredSourceChord
  comparison vertical) → Prop
  | [] => True
  | chord :: rest => chord.1.lower = lower ∧
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.physicalAfter
    chord.1.upper rest

/-- Read the final physical endpoint after traversing the original chord list. -/
private def physicalFinish (lower : InverseRootPolynomial.Coordinate) : List (SourceChordRuns.StoredSourceChord
  comparison vertical) → InverseRootPolynomial.Coordinate
  | [] => lower
  | chord :: rest =>
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.physicalFinish
    chord.1.upper rest

/-- Splitting a consecutive physical chord list preserves adjacency on both retained sublists. -/
private theorem physical_split (before after : List (SourceChordRuns.StoredSourceChord comparison vertical)) {lower :
  InverseRootPolynomial.Coordinate}
    (connected : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.physicalAfter
      lower (before ++ after)) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.physicalAfter lower before ∧
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.physicalAfter
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.physicalFinish lower before)
      after := by
  induction before generalizing lower with
  | nil => exact ⟨True.intro, connected⟩
  | cons chord rest ih =>
    have split := ih connected.2
    exact ⟨⟨connected.1, split.1⟩, split.2⟩

/-- The original indexed chord bank forms a consecutive physical list when all adjoining endpoints agree. -/
private theorem physical_ofFn {n : Nat} (source : Fin (n + 1) → SourceChordRuns.StoredSourceChord comparison vertical)
    (joins : ∀ i : Fin n, (source i.succ).1.lower = (source i.castSucc).1.upper) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.physicalAfter (source
      0).1.lower (List.ofFn source) := by
  induction n with
  | zero =>
    rw [OfFn.Basic.ofFn_succ]
    exact ⟨rfl, True.intro⟩
  | succ n ih =>
    rw [OfFn.Basic.ofFn_succ]
    refine ⟨rfl, ?_⟩
    have tail := ih (fun i => source i.succ) (fun i => joins i.succ)
    exact (congrArg (fun lower =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.physicalAfter lower
      (List.ofFn (fun i => source i.succ))) (joins 0)).mp tail

/-- Read the last original chord in a nonempty retained chord list. -/
@[expose] def lastChord (first : SourceChordRuns.StoredSourceChord comparison vertical) : List
  (SourceChordRuns.StoredSourceChord comparison vertical) →
    SourceChordRuns.StoredSourceChord comparison vertical
  | [] => first
  | next :: rest =>
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.lastChord next rest

/-- Concatenating consecutive same-parent chord samples gives the increments of their exact assembled original parameter
path. -/
private theorem word_increments (first : SourceChordRuns.StoredSourceChord comparison vertical)
    (rest : List (SourceChordRuns.StoredSourceChord comparison vertical))
    (same : ∀ chord ∈ rest, chord.2.index = first.2.index)
    (connected : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.physicalAfter
      first.1.upper rest) :
    ((first :: rest).map StoredSourceChord.increments).flatten =
      SourceListResampling.increments (comparison.sourceValues first.2.index)
        (BoundaryTraceParameters.firstParameter first.2.forward first.2.range) (((first :: rest).map
          Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parameters).flatten) :=
          by
  induction rest generalizing first with
  | nil =>
    simpa only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, Data.List.Append.append_nil, -eq_self,
      -iff_self]
      using first.increments_parameters
  | cons next rest ih =>
    have tail := ih next (fun chord member =>
      (same chord (List.mem_cons_of_mem next member)).trans (same next List.mem_cons_self).symm) connected.2
    have joint := first.2.same_parent_parameters next.2 (same next List.mem_cons_self) connected.1
    have tailEq : SourceListResampling.increments (comparison.sourceValues next.2.index)
        (BoundaryTraceParameters.firstParameter next.2.forward next.2.range) (((next :: rest).map
          Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parameters).flatten) =
        SourceListResampling.increments (comparison.sourceValues first.2.index)
          (BoundaryTraceParameters.lastParameter first.2.forward first.2.range) (((next :: rest).map
            Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parameters).flatten) :=
      congrArg₂ (fun index start => SourceListResampling.increments (comparison.sourceValues index) start
        (((next :: rest).map
          Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parameters).flatten))
          (same next List.mem_cons_self) joint
    change first.increments ++ ((next :: rest).map StoredSourceChord.increments).flatten =
      SourceListResampling.increments _ _ (first.parameters ++ ((next :: rest).map
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parameters).flatten)
    rw [SourceListResampling.increments_append, first.parameters_terminal]
    exact congrArg₂ List.append first.increments_parameters (tail.trans tailEq)

/-- The assembled original parameter path ends at the final retained chord's terminal parameter. -/
private theorem word_terminal (first : SourceChordRuns.StoredSourceChord comparison vertical)
    (rest : List (SourceChordRuns.StoredSourceChord comparison vertical))
    (same : ∀ chord ∈ rest, chord.2.index = first.2.index)
    (connected : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.physicalAfter
      first.1.upper rest) :
    SourceListResampling.terminal (BoundaryTraceParameters.firstParameter first.2.forward first.2.range)
      (((first :: rest).map
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parameters).flatten) =
      BoundaryTraceParameters.lastParameter
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.lastChord first
        rest).2.forward (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.lastChord
        first rest).2.range := by
  induction rest generalizing first with
  | nil => simpa only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, Data.List.Append.append_nil,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.lastChord, -eq_self,
        -iff_self] using first.parameters_terminal
  | cons next rest ih =>
    have tail := ih next (fun chord member =>
      (same chord (List.mem_cons_of_mem next member)).trans (same next List.mem_cons_self).symm) connected.2
    have joint := first.2.same_parent_parameters next.2 (same next List.mem_cons_self) connected.1
    change SourceListResampling.terminal _ (first.parameters ++ ((next :: rest).map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parameters).flatten) = _
    rw [SourceListResampling.terminal_append, first.parameters_terminal, ← joint]
    exact tail

/-- A consecutive same-parent chord word retains its common oriented chain and parameter-width bounds. -/
private theorem word_bounds (first : SourceChordRuns.StoredSourceChord comparison vertical) (rest : List
  (SourceChordRuns.StoredSourceChord comparison vertical))
    (same : ∀ chord ∈ rest, chord.2.index = first.2.index) (connected :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.physicalAfter first.1.upper
      rest)
    (forward : Bool) {width : InverseRootPolynomial.Coordinate}
    (bounds : ∀ chord ∈ first :: rest, chord.2.forward = forward ∧ (1 / 2 :
      InverseRootPolynomial.Coordinate) ^ chord.2.depth ≤ width) :
    SourceResampling.Chain (OrientedBounds.orientParameter forward (BoundaryTraceParameters.firstParameter
      first.2.forward first.2.range))
      ((((first :: rest).map
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parameters).flatten).map
        (OrientedBounds.orientParameter forward))
      (OrientedBounds.orientParameter forward (BoundaryTraceParameters.lastParameter
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.lastChord first
        rest).2.forward (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.lastChord
        first rest).2.range)) ∧
    SourceResampling.widths (OrientedBounds.orientParameter forward (BoundaryTraceParameters.firstParameter
      first.2.forward first.2.range))
      ((((first :: rest).map
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parameters).flatten).map
        (OrientedBounds.orientParameter forward)) width := by
  have initial := first.parameter_bounds forward (bounds first List.mem_cons_self).1 (bounds first List.mem_cons_self).2
  induction rest generalizing first with
  | nil =>
    simpa only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, Data.List.Append.append_nil,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.lastChord, -eq_self,
      -iff_self] using initial
  | cons next rest ih =>
    have tail := ih next (fun chord member =>
      (same chord (List.mem_cons_of_mem next member)).trans (same next List.mem_cons_self).symm) connected.2
      (fun chord member => bounds chord (List.mem_cons_of_mem first member))
      (next.parameter_bounds forward (bounds next (List.mem_cons_of_mem first List.mem_cons_self)).1
        (bounds next (List.mem_cons_of_mem first List.mem_cons_self)).2)
    have joint := congrArg (OrientedBounds.orientParameter forward)
      (first.2.same_parent_parameters next.2 (same next List.mem_cons_self) connected.1)
    rw [joint] at tail
    change SourceResampling.Chain _ ((first.parameters ++ ((next :: rest).map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parameters).flatten).map _) _
      ∧
      SourceResampling.widths _ ((first.parameters ++ ((next :: rest).map
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parameters).flatten).map _)
        width
    rw [Data.List.Map.map_append]
    refine ⟨Chain.append initial.1 tail.1, SourceListResampling.widths_append initial.2 ?_⟩
    rw [Chain.terminal_eq initial.1]
    exact tail.2

/-- The last chord of a same-parent word retains the first chord's original parent position. -/
private theorem last_parent (first : SourceChordRuns.StoredSourceChord comparison vertical) (rest : List
  (SourceChordRuns.StoredSourceChord comparison vertical))
    (same : ∀ chord ∈ rest, chord.2.index = first.2.index) :
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.lastChord first
      rest).2.index = first.2.index := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
    exact (ih next (fun chord member => (same chord (List.mem_cons_of_mem next member)).trans
      (same next List.mem_cons_self).symm)).trans (same next List.mem_cons_self)

end StoredSourceChord

namespace SourceChordRun

/-- Concatenate every original chord's retained source parameters in run order. -/
@[expose] def parameters (run : SourceChordRuns.SourceChordRun comparison vertical) : List Coordinate :=
  (run.chords.map
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.parameters).flatten

/-- A physically consecutive run's cached increments equal sampling its original parent along the retained complete
parameter list. -/
private theorem increments_parameters (run : SourceChordRuns.SourceChordRun comparison vertical)
    (connected : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.physicalAfter
      run.first.1.upper run.rest) :
    run.values = SourceListResampling.increments (comparison.sourceValues run.parent)
      (BoundaryTraceParameters.firstParameter run.first.2.forward run.first.2.range) run.parameters :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.word_increments run.first
    run.rest
    (fun chord member => (run.rest_parent chord member).trans run.first_parent.symm) connected).trans
      (congrArg (fun index => SourceListResampling.increments (comparison.sourceValues index)
        (BoundaryTraceParameters.firstParameter run.first.2.forward run.first.2.range) run.parameters) run.first_parent)

/-- The difference of the exact source values at the retained run's final and initial endpoints. -/
@[expose] def endpointIncrement (run : SourceChordRuns.SourceChordRun comparison vertical) : PrimitivePoint :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.lastChord run.first
    run.rest).finishValue.sub run.first.startValue

/-- The last original chord in the run retains its certified run-parent position. -/
theorem last_parent (run : SourceChordRuns.SourceChordRun comparison vertical) :
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.lastChord run.first
      run.rest).2.index = run.parent :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.last_parent run.first run.rest
    (fun chord member => (run.rest_parent chord member).trans run.first_parent.symm)).trans run.first_parent

/-- The complete sampled displacement of a consecutive original-parent run equals its exact endpoint increment. -/
private theorem total_eq (run : SourceChordRuns.SourceChordRun comparison vertical)
    (connected : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.physicalAfter
      run.first.1.upper run.rest) :
    PairedIncrementArea.total run.values = run.endpointIncrement := by
  have finish := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.word_terminal
    run.first run.rest
    (fun chord member => (run.rest_parent chord member).trans run.first_parent.symm) connected
  exact (congrArg PairedIncrementArea.total (run.increments_parameters connected)).trans
    ((SourceListResampling.increments_total _ _ _).trans
      (congrArg₂ PrimitivePoint.sub
        (congrArg₂ (fun index parameter => comparison.sourceValues index parameter) run.last_parent.symm finish)
        (congrArg (fun index => comparison.sourceValues index
          (BoundaryTraceParameters.firstParameter run.first.2.forward run.first.2.range)) run.first_parent.symm)))

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun in
/-- Physical adjacency of the flattened original chord list holds inside each retained run. -/
private theorem runs_connected (runs : List (SourceChordRuns.SourceChordRun comparison vertical)) {lower :
  InverseRootPolynomial.Coordinate}
    (connected : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.physicalAfter
      lower (runs.map chords).flatten) :
    ∀ run ∈ runs, Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.physicalAfter
      run.first.1.upper run.rest := by
  induction runs generalizing lower with
  | nil => intro _ member; cases member
  | cons run rest ih =>
    have split := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.physical_split
      run.chords (rest.map chords).flatten connected
    intro found member
    rcases Data.List.Membership.mem_cons.mp member with rfl | member
    · exact split.1.2
    · exact ih split.2 found member

/-- The original consecutive run totals equal their retained endpoint increments in the same list order. -/
private theorem mapped_totals (runs : List (SourceChordRuns.SourceChordRun comparison vertical))
    (connected : ∀ run ∈ runs,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.physicalAfter
      run.first.1.upper run.rest) :
    (runs.map SourceChordRun.values).map PairedIncrementArea.total = runs.map endpointIncrement := by
  induction runs with
  | nil => rfl
  | cons run rest ih =>
    exact congrArg₂ List.cons (run.total_eq (connected run List.mem_cons_self))
      (ih (fun found member => connected found (List.mem_cons_of_mem run member)))

end SourceChordRun

namespace SourceChordGrouping

/-- Every grouped original-parent run retains the common oriented source-chain and dyadic-width bounds. -/
theorem parameter_bounds_ofFn {n : Nat} {source : Fin (n + 1) → SourceChordRuns.StoredSourceChord comparison vertical}
    (grouped : SourceChordRuns.SourceChordGrouping comparison vertical (List.ofFn source))
    (joins : ∀ i : Fin n, (source i.succ).1.lower = (source i.castSucc).1.upper)
    (forward : Bool) {width : InverseRootPolynomial.Coordinate}
    (bounds : ∀ i, (source i).2.forward = forward ∧ (1 / 2 : InverseRootPolynomial.Coordinate)^(source i).2.depth ≤
      width) :
    ∀ run ∈ grouped.runs,
      SourceResampling.Chain (OrientedBounds.orientParameter forward (BoundaryTraceParameters.firstParameter
        run.first.2.forward run.first.2.range))
        (run.parameters.map (OrientedBounds.orientParameter forward))
        (OrientedBounds.orientParameter forward (BoundaryTraceParameters.lastParameter
          (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.lastChord run.first
          run.rest).2.forward
          (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.lastChord run.first
            run.rest).2.range)) ∧
      SourceResampling.widths (OrientedBounds.orientParameter forward (BoundaryTraceParameters.firstParameter
        run.first.2.forward run.first.2.range))
        (run.parameters.map (OrientedBounds.orientParameter forward)) width := by
  have connected := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.physical_ofFn
    source joins
  rw [← grouped.flattened] at connected
  intro run member
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.word_bounds run.first
    run.rest
    (fun chord present => (run.rest_parent chord present).trans run.first_parent.symm)
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.runs_connected grouped.runs
      connected run member) forward
  intro chord present
  have original : chord ∈ List.ofFn source := Eq.mp (congrArg (fun chords => chord ∈ chords) grouped.flattened)
    (Data.List.mem_flatten_of_mem (Map.mem_map_of_mem member) present)
  obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp original
  exact bounds i

/-- Reconstruct the full parameter path of every original-parent run using the retained physical joins. No source
samples or matching witnesses are supplied. -/
theorem sampling_ofFn {n : Nat} {source : Fin (n + 1) → SourceChordRuns.StoredSourceChord comparison vertical}
    (grouped : SourceChordRuns.SourceChordGrouping comparison vertical (List.ofFn source))
    (joins : ∀ i : Fin n, (source i.succ).1.lower = (source i.castSucc).1.upper) :
    ∀ run ∈ grouped.runs, run.values = SourceListResampling.increments (comparison.sourceValues run.parent)
      (BoundaryTraceParameters.firstParameter run.first.2.forward run.first.2.range) run.parameters := by
  have connected := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.physical_ofFn
    source joins
  rw [← grouped.flattened] at connected
  intro run member
  exact run.increments_parameters
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.runs_connected grouped.runs
    connected run member)

/-- The totals of the original grouped sampled paths are exactly their retained endpoint increments in run order. -/
theorem totals_ofFn {n : Nat} {source : Fin (n + 1) → SourceChordRuns.StoredSourceChord comparison vertical}
    (grouped : SourceChordRuns.SourceChordGrouping comparison vertical (List.ofFn source))
    (joins : ∀ i : Fin n, (source i.succ).1.lower = (source i.castSucc).1.upper) :
    (grouped.runs.map SourceChordRun.values).map PairedIncrementArea.total =
      grouped.runs.map SourceChordRun.endpointIncrement := by
  have connected := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.physical_ofFn
    source joins
  rw [← grouped.flattened] at connected
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.mapped_totals grouped.runs
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.runs_connected grouped.runs
    connected)

end SourceChordGrouping
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns
