module
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Word.Pairing
public import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Word.SignedWord
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Algebra

open Purelib.Data

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.BoundaryWord

open Purelib.Topology.Surface.Word

@[expose] public section

/-!
# Actual cut-primitive area and the computed boundary-word matrix

Every step retains its signed generator increment, local increment error,
and displacement from the modeled primitive. The exact area formula includes
their interaction. Thus neither primitive descent nor constant cut jumps are
silently assumed. Exact compatibility is a separate, explicit specialization.
-/

namespace Purelib.Topology.Surface.Cut.WordArea

open Purelib.Data.List

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint edgeArea edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Surface.Word.Pairing
open Purelib.Topology.Surface.Cut.BoundaryWord (CutWordEntry CutBoundaryWord)
open Purelib.Topology.Polygon.Stokes.PrimitivePoint (sub)

namespace CutWordArea

variable {source target count : Nat} {labels : Fin source → Fin target}
  {generators : Data.Vector (Stokes.OrientedEdge source) count}

/-- Read the ordered signed-generator coefficient rows from the original cut entries. -/
def word (entries : List (BoundaryWord.CutWordEntry labels generators)) : List (Pairing.Coefficients count) :=
  entries.map fun entry => entry.letter.coefficients

open Purelib.Topology.Surface.Cut.WordArea.CutWordArea in
set_option genInjectivity false in
/-- Executable quantities for one cut-word comparison step.

The original cut entry and signed-generator increment determine the modeled
endpoints. Cached drift, local increment error and their complete area correction
retain the discrepancy from the supplied original primitive. -/
structure Step (primitive : Fin source → Stokes.PrimitivePoint) (values : Fin count → Stokes.PrimitivePoint) where
  /-- Original cut entry represented by this step. -/ entry : BoundaryWord.CutWordEntry labels generators
  /-- Modeled primitive position before the retained step. -/ start : Stokes.PrimitivePoint
  /-- Cached signed-generator increment of the original entry. -/ increment : Stokes.PrimitivePoint
  /-- The increment is the linear evaluation of the entry's retained coefficient row. -/ increment_eq : increment =
    Pairing.linear entry.letter.coefficients values
  /-- Modeled primitive position after the retained step. -/ finish : Stokes.PrimitivePoint
  /-- The modeled finish is the retained start plus increment. -/ finish_eq : finish = start.add increment
  /-- Cached displacement of the actual start primitive from the modeled start. -/ drift : Stokes.PrimitivePoint
  /-- The drift uses the original cut edge's start and the retained modeled start. -/ drift_eq : drift =
    (PrimitivePoint.sub (primitive entry.edge.start)) start
  /-- Cached discrepancy between the actual edge increment and its signed-generator model. -/ error :
    Stokes.PrimitivePoint
  /-- The local error is the original primitive endpoint difference minus the modeled increment. -/ error_eq : error =
    (PrimitivePoint.sub ((PrimitivePoint.sub (primitive entry.edge.finish)) (primitive entry.edge.start))) increment
  /-- Cached full correction to the modeled edge area. -/ correction : Gaussian.Basic.Canonical
  /-- The correction includes drift-increment and actual-start-error interactions. -/ correction_eq : correction =
    Stokes.edgeArea drift increment + Stokes.edgeArea (primitive entry.edge.start) error

constructive_injectivity Step

namespace Step

open Purelib.Topology.Surface.Cut.WordArea
/-- Cache one modeled increment, its original primitive discrepancy and the full area correction. -/
def build (primitive : Fin source → Stokes.PrimitivePoint) (values : Fin count → Stokes.PrimitivePoint)
    (entry : BoundaryWord.CutWordEntry labels generators) (start : Stokes.PrimitivePoint) : CutWordArea.Step (labels :=
      labels) (generators := generators) primitive values :=
  let increment := Pairing.linear entry.letter.coefficients values
  let drift := (PrimitivePoint.sub (primitive entry.edge.start)) start
  let error := (PrimitivePoint.sub ((PrimitivePoint.sub (primitive entry.edge.finish)) (primitive entry.edge.start)))
    increment
  { entry := entry, start := start, increment := increment, increment_eq := rfl
    finish := start.add increment, finish_eq := rfl
    drift := drift, drift_eq := rfl, error := error, error_eq := rfl
    correction := Stokes.edgeArea drift increment + Stokes.edgeArea (primitive entry.edge.start) error
    correction_eq := rfl }

/-- The original primitive edge area equals the modeled step area plus its retained correction. -/
theorem area_eq {primitive : Fin source → Stokes.PrimitivePoint} {values : Fin count → Stokes.PrimitivePoint}
    (step : CutWordArea.Step (labels := labels) (generators := generators) primitive values) :
    Stokes.edgeArea (primitive step.entry.edge.start) (primitive step.entry.edge.finish) =
      Stokes.edgeArea step.start step.finish + step.correction := by
  rw [step.finish_eq, step.correction_eq, step.drift_eq, step.error_eq]
  simp only [Stokes.edgeArea, PrimitivePoint.add, PrimitivePoint.sub]
  ring1

end Step

open Purelib.Topology.Surface.Cut.WordArea.CutWordArea in
open Purelib.Topology.Surface.Cut.WordArea in
open Purelib.Topology.Surface.Cut.WordArea.CutWordArea in
/-- Build the ordered step bank while carrying each modeled endpoint into the next step. -/
def steps (primitive : Fin source → Stokes.PrimitivePoint) (values : Fin count → Stokes.PrimitivePoint) :
    Stokes.PrimitivePoint → List (BoundaryWord.CutWordEntry labels generators) → List (CutWordArea.Step (labels :=
      labels) (generators := generators) primitive values)
  | _, [] => []
  | start, entry :: rest =>
      let first := Step.build primitive values entry start
      first :: steps primitive values first.finish rest

section
open Purelib.Topology.Surface.Cut.WordArea.CutWordArea
open Purelib.Topology.Surface.Cut.WordArea
/-- Sum the complete retained area correction over the ordered step bank. -/
def correction {primitive : Fin source → Stokes.PrimitivePoint} {values : Fin count → Stokes.PrimitivePoint} :
    List (CutWordArea.Step (labels := labels) (generators := generators) primitive values) → Gaussian.Basic.Canonical
  | [] => 0
  | step :: rest => step.correction + correction rest

/-- Sum both coordinates of the retained local increment errors. -/
def errorTotal {primitive : Fin source → Stokes.PrimitivePoint} {values : Fin count → Stokes.PrimitivePoint} :
    List (CutWordArea.Step (labels := labels) (generators := generators) primitive values) → Stokes.PrimitivePoint
  | [] => PrimitivePoint.zero
  | step :: rest => step.error.add (errorTotal rest)

end

open Purelib.Topology.Surface.Cut.WordArea.CutWordArea in
/-- The step bank reads back the original ordered cut entries exactly. -/
theorem steps_entries (primitive : Fin source → Stokes.PrimitivePoint) (values : Fin count → Stokes.PrimitivePoint)
    (entries : List (BoundaryWord.CutWordEntry labels generators)) (start : Stokes.PrimitivePoint) :
    (steps primitive values start entries).map Purelib.Topology.Surface.Cut.WordArea.CutWordArea.Step.entry = entries :=
      by
  induction entries generalizing start with
  | nil => rfl
  | cons entry rest ih => exact congrArg (List.cons entry) (ih _)

section
open Purelib.Topology.Surface.Cut.WordArea.CutWordArea
open Purelib.Topology.Surface.Cut.WordArea
open Purelib.Topology.Surface.Cut.WordArea.CutWordArea
/-- On a genuine path, accumulated local error is exactly the discrepancy between its actual endpoint displacement and
the modeled total increment. -/
theorem errorTotal_eq (primitive : Fin source → Stokes.PrimitivePoint) (values : Fin count → Stokes.PrimitivePoint)
    (entries : List (BoundaryWord.CutWordEntry labels generators)) {first last : Fin source}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (entries.map CutWordEntry.edge) first
      last)
    (start : Stokes.PrimitivePoint) :
    errorTotal (steps primitive values start entries) =
      (PrimitivePoint.sub ((PrimitivePoint.sub (primitive last)) (primitive first))) (Pairing.linear (Pairing.totalAt
        (CutWordArea.word entries)) values) := by
  induction entries generalizing first start with
  | nil =>
      cases path
      change PrimitivePoint.zero = (PrimitivePoint.sub ((PrimitivePoint.sub (primitive last)) (primitive last)))
        (Pairing.linear (fun _ => 0) values)
      rw [Pairing.linear_zero]
      simp only [PrimitivePoint.zero, PrimitivePoint.sub]
      congr 1 <;> ring1
  | cons entry rest ih =>
      cases path with
      | cons tail =>
          change (Step.build primitive values entry start).error.add
            (errorTotal (steps primitive values (Step.build primitive values entry start).finish rest)) = _
          rw [ih tail]
          change ((PrimitivePoint.sub ((PrimitivePoint.sub (primitive entry.edge.finish)) (primitive entry.edge.start)))
            (Pairing.linear entry.letter.coefficients values)).add
            ((PrimitivePoint.sub ((PrimitivePoint.sub (primitive last)) (primitive entry.edge.finish))) (Pairing.linear
              (Pairing.totalAt (CutWordArea.word rest)) values)) =
            (PrimitivePoint.sub ((PrimitivePoint.sub (primitive last)) (primitive entry.edge.start)))
              (Pairing.linear (fun index => entry.letter.coefficients index + Pairing.totalAt (CutWordArea.word rest)
                index) values)
          rw [Pairing.linear_add]
          simp only [PrimitivePoint.add, PrimitivePoint.sub]
          congr 1 <;> ring1

/-- This holds even for discontinuous lists. All discontinuities are visible in the retained step drifts; a path
certificate specializes them to prefix sums of the local increment errors. -/
theorem steps_area (primitive : Fin source → Stokes.PrimitivePoint) (values : Fin count → Stokes.PrimitivePoint)
    (entries : List (BoundaryWord.CutWordEntry labels generators)) (start : Stokes.PrimitivePoint) :
    Stokes.edgeListArea primitive (entries.map CutWordEntry.edge) =
      Pairing.traceArea values start (CutWordArea.word entries) + correction (steps primitive values start entries) :=
        by
  induction entries generalizing start with
  | nil => change (0 : Gaussian.Basic.Canonical) = 0 + 0; ring1
  | cons entry rest ih =>
      have one : Stokes.edgeArea (primitive entry.edge.start) (primitive entry.edge.finish) =
          Stokes.edgeArea start (start.add (Pairing.linear entry.letter.coefficients values)) +
          (Step.build primitive values entry start).correction := (Step.build primitive values entry start).area_eq
      rw [List.map_cons, Stokes.edgeListArea, one, ih (start.add (Pairing.linear entry.letter.coefficients values))]
      change _ = (Stokes.edgeArea start (start.add (Pairing.linear entry.letter.coefficients values)) +
        Pairing.traceArea values (start.add (Pairing.linear entry.letter.coefficients values)) (CutWordArea.word rest))
          +
        ((Step.build primitive values entry start).correction +
          correction (steps primitive values (start.add (Pairing.linear entry.letter.coefficients values)) rest))
      ring1

end

open Purelib.Topology.Surface.Cut.WordArea in
/-- Exact local compatibility suffices for the modeled word to be the literal primitive path. No geometric intersection
claim is used. -/
theorem traceArea_eq_of_compatible (primitive : Fin source → Stokes.PrimitivePoint) (values : Fin count →
  Stokes.PrimitivePoint)
    (entries : List (BoundaryWord.CutWordEntry labels generators)) {first last : Fin source}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (entries.map CutWordEntry.edge) first
      last)
    (compatible : ∀ entry ∈ entries,
      Pairing.linear entry.letter.coefficients values =
        (PrimitivePoint.sub (primitive entry.edge.finish)) (primitive entry.edge.start)) :
    Pairing.traceArea values (primitive first) (CutWordArea.word entries) = Stokes.edgeListArea primitive (entries.map
      CutWordEntry.edge) := by
  induction entries generalizing first with
  | nil => rfl
  | cons entry rest ih =>
      cases path with
      | cons tail =>
          have next : (primitive entry.edge.start).add (Pairing.linear entry.letter.coefficients values) =
              primitive entry.edge.finish := by
            rw [compatible entry List.mem_cons_self]
            cases primitive entry.edge.start
            cases primitive entry.edge.finish
            simp only [PrimitivePoint.add, PrimitivePoint.sub]
            congr 1 <;> ring1
          change Stokes.edgeArea _ _ + Pairing.traceArea values _ (CutWordArea.word rest) =
            Stokes.edgeArea _ _ + Stokes.edgeListArea primitive (rest.map CutWordEntry.edge)
          rw [next, ih tail (fun next member => compatible next (List.mem_cons_of_mem _ member))]

end CutWordArea

namespace CutBoundaryWord

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}

open Purelib.Topology.Surface.Cut.WordArea in
/-- The boundary coefficient word is the coefficient reading of its original retained entries.

The original ordered letter projection and its coefficient projection compose
entry by entry. Their cached word therefore keeps the same signed-generator
rows and boundary occurrence order. -/
theorem coefficients_entries (boundary : BoundaryWord.CutBoundaryWord labels edges) :
    boundary.coefficients = CutWordArea.word boundary.alphabet.entries := by
  rw [boundary.coefficients_eq, boundary.letters_eq, Map.map_map]
  rfl

/-- Generator increments are cached from the actual retained representative edges. A reversed occurrence need not have
their exact negative: the sample below retains the difference instead of requiring its vanishing. -/
def generatorValues (boundary : BoundaryWord.CutBoundaryWord labels edges) (primitive : Fin source →
  Stokes.PrimitivePoint) :
    Data.Vector Stokes.PrimitivePoint boundary.alphabet.count :=
  Data.Vector.Basic.vectorOfFn fun index =>
    (PrimitivePoint.sub (primitive (boundary.alphabet.generators index).finish)) (primitive
      (boundary.alphabet.generators index).start)

open Purelib.Topology.Surface.Cut.WordArea in
set_option genInjectivity false in
/-- Cached comparison of the original cut primitive with its signed-generator word.

The sample retains generator increments, ordered steps, local area corrections and total endpoint error, together with
the correction for a closed boundary. -/
structure AreaSample (boundary : BoundaryWord.CutBoundaryWord labels edges) (primitive : Fin source →
  Stokes.PrimitivePoint)
    (start : Stokes.PrimitivePoint) where
  /-- Retained primitive increments of the original representative generator edges. -/ values : Data.Vector
    Stokes.PrimitivePoint boundary.alphabet.count
  /-- The generator values are the exact original endpoint increments. -/ values_eq : values =
    CutBoundaryWord.generatorValues boundary primitive
  /-- Cached ordered modeled steps for the original boundary entries. -/ steps : List (CutWordArea.Step (labels :=
    labels) (generators := boundary.alphabet.generators) primitive values)
  /-- The retained step bank is built from the original entries and supplied initial primitive. -/ steps_eq : steps =
    CutWordArea.steps primitive values start boundary.alphabet.entries
  /-- Cached total of all step area corrections. -/ correction : Gaussian.Basic.Canonical
  /-- The total correction sums exactly the retained step corrections. -/ correction_eq : correction =
    CutWordArea.correction steps
  /-- Cached sum of the original local increment discrepancies. -/ errorTotal : Stokes.PrimitivePoint
  /-- The total error sums exactly the retained step errors. -/ errorTotal_eq : errorTotal = CutWordArea.errorTotal
    steps
  /-- Cached area correction after accounting for the modeled endpoint discrepancy. -/ closedCorrection :
    Gaussian.Basic.Canonical
  /-- The closed correction subtracts the initial-position pairing with the retained total error. -/ closedCorrection_eq
    : closedCorrection = correction - Stokes.edgeArea start errorTotal

constructive_injectivity AreaSample

namespace AreaSample

open Purelib.Topology.Surface.Cut.WordArea
/-- Cache generator increments, the complete modeled step bank and all original area and endpoint corrections. -/
def build (boundary : BoundaryWord.CutBoundaryWord labels edges) (primitive : Fin source → Stokes.PrimitivePoint) (start
  : Stokes.PrimitivePoint) :
    CutBoundaryWord.AreaSample boundary primitive start :=
  let values := CutBoundaryWord.generatorValues boundary primitive
  let steps := CutWordArea.steps primitive values start boundary.alphabet.entries
  let correction := CutWordArea.correction steps
  let errorTotal := CutWordArea.errorTotal steps
  ⟨values, rfl, steps, rfl, correction, rfl, errorTotal, rfl, correction - Stokes.edgeArea start errorTotal, rfl⟩

/-- Exact comparison with the computed matrix, including the full endpoint and compatibility corrections. This does not
assume a symplectic basis. -/
theorem area_eq {boundary : BoundaryWord.CutBoundaryWord labels edges} {primitive : Fin source → Stokes.PrimitivePoint}
  {start : Stokes.PrimitivePoint}
    (sample : CutBoundaryWord.AreaSample boundary primitive start) :
    Stokes.edgeListArea primitive edges =
      Stokes.edgeArea start (Pairing.linear boundary.signature.total sample.values) +
      Pairing.contract (fun row column => boundary.signature.matrix row column) sample.values + sample.correction := by
  rw [sample.correction_eq, sample.steps_eq, ← boundary.signature.traceArea_eq,
    CutBoundaryWord.coefficients_entries boundary, ← CutWordArea.steps_area, boundary.alphabet.edges_eq]

/-- Closedness removes the modeled endpoint term only after transferring its full discrepancy into the accumulated error
correction. -/
theorem closed_area_eq {boundary : BoundaryWord.CutBoundaryWord labels edges} {primitive : Fin source →
  Stokes.PrimitivePoint} {anchor : Fin source}
    (sample : CutBoundaryWord.AreaSample boundary primitive (primitive anchor))
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor) :
    Stokes.edgeListArea primitive edges =
      Pairing.contract (fun row column => boundary.signature.matrix row column) sample.values + sample.closedCorrection
        := by
  have errors := CutWordArea.errorTotal_eq primitive sample.values boundary.alphabet.entries
    (by rw [boundary.alphabet.edges_eq]; exact closed) (primitive anchor)
  have total : Pairing.linear boundary.signature.total sample.values =
      Pairing.linear (Pairing.totalAt (CutWordArea.word boundary.alphabet.entries)) sample.values := by
    unfold Pairing.linear
    congr 1 <;> apply FiniteSum.Fin.sumFin_congr <;> intro index <;>
      rw [boundary.signature.total_eq, CutBoundaryWord.coefficients_entries boundary]
  rw [sample.area_eq, sample.closedCorrection_eq, sample.errorTotal_eq, sample.steps_eq, errors, total]
  simp only [Stokes.edgeArea, PrimitivePoint.sub]
  ring1

end AreaSample

end CutBoundaryWord

end Purelib.Topology.Surface.Cut.WordArea
