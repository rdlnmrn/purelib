module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordData
import Purelib.Integration.Path.PairedAreaBlocks
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Topology.Polygon.Stokes

section

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Data.List

open Purelib.Geometry.Rectangle.Partition

open Purelib.Integration.Path

public section

/-! Group the retained fine source fragments without changing physical order.
Every run retains its actual sample data and a single certified parent index.
The exact area formula keeps internal excursions and the block-total polygon. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Riemann.Normalization
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

/-- A retained physical interval with its original closed-bank source chord and complete cached fine sample. -/
@[expose] def StoredSourceChord (comparison : prepared.ClosedBoundaryComparison other requested minimum) (vertical :
  Bool) :=
  Σ physical : PreparedAxisPartitions.Interval, SourceChordData comparison vertical physical

/-- Read the complete original increment list of the retained source chord. -/
@[expose] def StoredSourceChord.increments {comparison : prepared.ClosedBoundaryComparison other requested minimum}
  {vertical : Bool}
    (chord : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord comparison vertical) :
      List PrimitivePoint := chord.2.increments

set_option genInjectivity false in
/-- A nonempty consecutive run of original stored source chords with one retained parent position. -/
structure SourceChordRun (comparison : prepared.ClosedBoundaryComparison other requested minimum) (vertical : Bool)
  where
  /-- The run's original retained closed-bank parent position. -/ parent : Fin comparison.original.plans.length
  /-- The first actual retained source chord of this nonempty run. -/ first :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord comparison vertical
  /-- The remaining original source chords in their physical order. -/ rest : List
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord comparison vertical)
  /-- The first retained chord belongs to the run's original parent position. -/ first_parent : first.2.index = parent
  /-- Every remaining retained chord belongs to that identical original parent position. -/ rest_parent : ∀ chord ∈
    rest, chord.2.index = parent

constructive_injectivity SourceChordRun

namespace SourceChordRun
variable {comparison : prepared.ClosedBoundaryComparison other requested minimum} {vertical : Bool}

/-- Read the complete original stored chord list of the nonempty run. -/
@[expose] def chords (run : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun comparison
  vertical) := run.first :: run.rest

/-- Concatenate the complete cached fine increments of the original chords in run order. -/
@[expose] def values (run : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun comparison
  vertical) := (run.chords.map
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.increments).flatten

/-- The supplied parent position differs from the first retained run position, when present. -/
@[expose] def startsApart (parent : Fin comparison.original.plans.length) : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun comparison vertical) → Prop
  | [] => True
  | run :: _ => parent ≠ run.parent

/-- Every adjacent pair of original source-chord runs has distinct retained parent positions. -/
@[expose] def separated : List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun
  comparison vertical) → Prop
  | [] => True
  | run :: rest => Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.startsApart
    run.parent rest ∧
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.separated rest

/-- Every original stored chord in the run retains its common parent position. -/
theorem parent_eq (run : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun comparison
  vertical) {chord : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord comparison
  vertical}
    (member : chord ∈ run.chords) : chord.2.index = run.parent := by
  rcases Membership.mem_cons.mp member with rfl | member
  · exact run.first_parent
  · exact run.rest_parent chord member

/-- Form the singleton run retaining the original source chord and parent position. -/
@[expose] def single (chord : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord
  comparison vertical) : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun comparison
  vertical :=
  ⟨chord.2.index, chord, [], rfl, by intro _ member; cases member⟩

/-- Prepend an original source chord to a run with the identical retained parent position. -/
@[expose] def prepend (chord : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord
  comparison vertical) (run : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun
  comparison vertical)
    (same : chord.2.index = run.parent) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun comparison vertical :=
  ⟨run.parent, chord, run.chords, same, fun _ member => run.parent_eq member⟩

/-- Prepend the original chord, extending the first run exactly when its retained parent position agrees. -/
@[expose] def insert (chord : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord
  comparison vertical) :
    List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun comparison vertical) → List
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun comparison vertical)
  | [] => [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.single chord]
  | run :: rest => if same : chord.2.index = run.parent then
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.prepend chord run same :: rest
      else Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.single chord :: run :: rest

/-- Group the original source chords into maximal consecutive runs by executable parent-position equality. -/
@[expose] def group : List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord
  comparison vertical) → List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun
  comparison vertical)
  | [] => []
  | chord :: rest => Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.insert chord
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.group rest)

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun
/-- Inserting a source chord preserves its exact position before the original flattened runs. -/
private theorem insert_flatten (chord :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord comparison vertical) (runs : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun comparison vertical)) :
    ((Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.insert chord runs).map
      chords).flatten = chord :: (runs.map chords).flatten := by
  cases runs with
  | nil => rfl
  | cons run rest =>
    if same : chord.2.index = run.parent then
      rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.insert, dif_pos same]
      rfl
    else
      rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.insert, dif_neg same]
      rfl

/-- Flattening the grouped runs returns every original stored chord in its exact order. -/
theorem group_flatten (chords : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord comparison vertical)) :
    ((Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.group chords).map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.chords).flatten = chords := by
  induction chords with
  | nil => rfl
  | cons chord rest ih =>
    exact (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.insert_flatten chord
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.group rest)).trans (congrArg
      (List.cons chord) ih)

end

/-- Inserting an original source chord preserves distinct parent positions between adjacent runs. -/
private theorem insert_separated (chord :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord comparison vertical)
    (runs : List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun comparison
      vertical)) (apart : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.separated
      runs) : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.separated
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.insert chord runs) := by
  cases runs with
  | nil => exact ⟨True.intro, True.intro⟩
  | cons run rest =>
    if same : chord.2.index = run.parent then
      rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.insert, dif_pos same]
      exact apart
    else
      rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.insert, dif_neg same]
      exact ⟨same, apart⟩

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun
/-- Adjacent grouped source-chord runs have distinct retained parent positions. -/
theorem group_separated (chords : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord comparison vertical)) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.separated
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.group chords) := by
  induction chords with
  | nil => exact True.intro
  | cons chord rest ih =>
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.insert_separated chord
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.group rest) ih

/-- Reading all cached fine increments commutes with flattening the original stored chord runs. -/
private theorem values_flatten (runs : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun comparison vertical)) :
    (runs.map Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.values).flatten =
      (((runs.map chords).flatten).map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.increments).flatten := by
  induction runs with
  | nil => rfl
  | cons run rest ih =>
    rw [List.map_cons, List.flatten_cons, List.map_cons, List.flatten_cons, Map.map_append, Flatten.flatten_append]
    exact congrArg (List.append run.values) ih

/-- Every original stored chord's parent position occurs as the retained parent of a run. -/
private theorem parent_present (runs : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun comparison vertical))
    {chord : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord comparison vertical}
      (member : chord ∈ (runs.map chords).flatten) :
    ∃ run ∈ runs, run.parent = chord.2.index := by
  induction runs with
  | nil => cases member
  | cons run rest ih =>
    rcases Membership.mem_append.mp member with here | there
    · exact ⟨run, List.mem_cons_self, (run.parent_eq here).symm⟩
    · obtain ⟨found, present, same⟩ := ih there
      exact ⟨found, List.mem_cons_of_mem run present, same⟩

end SourceChordRun

set_option genInjectivity false in
/-- Cached maximal consecutive source-chord runs with exact original-list readback and distinct adjacent parent
positions. -/
structure SourceChordGrouping (comparison : prepared.ClosedBoundaryComparison other requested minimum) (vertical : Bool)
    (chords : List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord comparison
      vertical)) where
  /-- The cached original source-chord runs in retained physical order. -/ runs : List
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun comparison vertical)
  /-- Flattening the cached runs gives the exact original stored chord list. -/ flattened : (runs.map
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.chords).flatten = chords
  /-- The cached maximal runs have distinct retained parent positions at every junction. -/ separated :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.separated runs

constructive_injectivity SourceChordGrouping

namespace SourceChordGrouping
variable {comparison : prepared.ClosedBoundaryComparison other requested minimum} {vertical : Bool}
  {chords : List (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord
    comparison vertical)}

/-- Compute and cache the original source-chord runs with exact flattening and adjacent-parent separation certificates.
-/
@[expose] def build (chords : List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord
  comparison vertical)) : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordGrouping
  comparison vertical chords :=
  ⟨SourceChordRun.group chords,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.group_flatten chords,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.group_separated chords⟩

/-- Reading all cached fine increments commutes with flattening the original stored chord runs. -/
theorem values_flatten (grouped : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordGrouping
  comparison vertical chords) :
    (grouped.runs.map Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.values).flatten
      = (chords.map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.increments).flatten :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.values_flatten grouped.runs).trans
    (congrArg (fun chords => (chords.map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.increments).flatten)
      grouped.flattened)

/-- The original full source path area equals its retained run excursion areas plus the polygon area of run totals. -/
theorem area_eq (grouped : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordGrouping
  comparison vertical chords) :
    PairedIncrementArea.area (chords.map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.increments).flatten =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((grouped.runs.map
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.values).map
        PairedIncrementArea.area) +
        PairedIncrementArea.area ((grouped.runs.map
          Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.values).map
          PairedIncrementArea.total) :=
  (congrArg PairedIncrementArea.area grouped.values_flatten.symm).trans (PairedAreaBlocks.area_flatten _)

/-- Every original stored chord's parent position occurs as the retained parent of a run. -/
theorem parent_present (grouped : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordGrouping
  comparison vertical chords)
    {chord : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord comparison vertical}
      (member : chord ∈ chords) :
    ∃ run ∈ grouped.runs, run.parent = chord.2.index := by
  rw [← grouped.flattened] at member
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.parent_present grouped.runs
    member

/-- The original finite source-sample path has the exact retained run-excursion and run-total polygon decomposition. -/
theorem area_ofFn {n : Nat} {source : Fin n →
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord comparison vertical}
    (grouped : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordGrouping comparison
      vertical (List.ofFn source)) :
    PairedIncrementArea.area (List.ofFn (fun i => (source i).increments)).flatten =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((grouped.runs.map
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.values).map
        PairedIncrementArea.area) +
        PairedIncrementArea.area ((grouped.runs.map
          Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.values).map
          PairedIncrementArea.total) := by
  have formula := grouped.area_eq
  rw [OfFn.Basic.map_ofFn] at formula
  exact formula

/-- Coverage of an original parent-position range by source chords is preserved by the retained run grouping. -/
theorem covers {n count offset : Nat} {source : Fin n →
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord comparison vertical}
    (grouped : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordGrouping comparison
      vertical (List.ofFn source))
    (coverage : ∀ parent : Fin count, ∃ i, (source i).2.index.val = offset + parent.val) :
    ∀ parent : Fin count, ∃ run ∈ grouped.runs, run.parent.val = offset + parent.val := by
  intro parent
  obtain ⟨i, position⟩ := coverage parent
  obtain ⟨run, present, same⟩ := grouped.parent_present (OfFn.Basic.mem_ofFn.mpr ⟨i, rfl⟩)
  exact ⟨run, present, (congrArg Fin.val same).trans position⟩

end SourceChordGrouping
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns

end
