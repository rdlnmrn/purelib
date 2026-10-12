module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Data.Vector.Basic

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryPotential
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.PotentialReadings
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Topology.Surface.Cut.PotentialClosed
public import Purelib.Topology.Surface.Word.GeneratorValuations
public import Purelib.Riemann.Periods.CutPeriodCompleteness
import Purelib.Topology.Surface.Cut.GeneratorBounds
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Data

open Purelib.Data.List

open Purelib.Riemann.Periods.CutPeriodCompleteness

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Boundary.BoundaryPotential
open _root_.Purelib.Topology.Surface.Boundary renaming BoundaryPotential -> BoundaryPotential

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.BoundaryWord

open Purelib.Topology.Surface.Cut.GeneratorBounds

open Purelib.Topology.Surface.Cut.PotentialClosed

open Purelib.Topology.Surface.Cut.PotentialReadings
open _root_.Purelib.Topology.Surface.Cut renaming PotentialReadings -> PotentialReadings

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.GeneratorValuations

/-! Extend finite generator readings to closed antisymmetric readings of the actual surface. -/
public section

namespace Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePairing)
open _root_.Purelib.Topology.Surface.Boundary (BoundaryPotential)
open _root_.Purelib.Topology.Surface.Cut (PotentialReadings)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)
open Purelib.Data.Gaussian.Basic (Canonical)

local notation "vget" => Data.Vector.get

variable {vertices facesCount : Nat} {faces : Fin facesCount → Stokes.OrientedTriangle vertices}
  {indices : List (Fin facesCount)} {boundary : List (Stokes.OrientedEdge vertices)}
  (patch : Patch.CutPatch faces indices boundary)
  (pairing : ProjectedEdgePairs.ProjectedEdgePairing patch.vertexLabels patch.boundary)
  (values : Data.Vector Gaussian.Basic.Canonical (ProjectedEdgePairing.boundaryWord
    pairing).alphabet.count)

namespace GeneratorExtension

/-- Extend the retained generator-value vector to the original projected edge-reading function. -/
@[expose] def generatorSource : Stokes.OrientedEdge vertices → Gaussian.Basic.Canonical :=
  ProjectedEdgePairing.generatorValue pairing (vget values)

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.

end GeneratorExtension

open Purelib.Topology.Surface.Cut in
set_option genInjectivity false in
/-- Both the cut potential and the surface increments are retained executable data. -/
structure GeneratorExtension where
  /-- Cached boundary potential whose increments agree with the original generator extension. -/ potential :
    Boundary.BoundaryPotential patch.boundary (fun edge => GeneratorExtension.generatorSource patch pairing
    values (OrientedEdge.map patch.vertexLabels edge))
  /-- Retained surface increment reading constructed from that exact potential. -/ readings :
    PotentialReadings patch (GeneratorExtension.generatorSource patch pairing values) potential

-- Preserve the original constructor certificate names of this unchanged nominal datatype.

constructive_injectivity GeneratorExtension

namespace GeneratorExtension

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
open Purelib.Topology.Surface.Cut in
/-- Cache a cut potential and its induced surface increments from generator values.

Unique projected incidence and zero one-sided generator values make the original cut boundary total vanish and certify
the retained potential. -/
@[expose] def build
    (unique : ((patch.triangles.flatMap OrientedTriangle.boundary).map (OrientedEdge.map patch.vertexLabels)).Nodup)
    (physical : ∀ index, (ProjectedEdgePairing.boundaryWord pairing).alphabet.oneSided index = true → vget values index
      = 0) :
    GeneratorExtension patch pairing values :=
  let boundaryUnique := PotentialClosed.boundary_unique_of_occurrences unique
  let source := generatorSource patch pairing values
  let zero := ProjectedEdgePairing.boundary_value_zero pairing source (ProjectedEdgePairing.generatorValue_reverse
    pairing (vget values))
    (ProjectedEdgePairing.generatorValue_physical pairing boundaryUnique (vget values) physical)
  let potential := BoundaryPotential.build (fun edge => source (OrientedEdge.map patch.vertexLabels edge)) patch.closed
    patch.simple zero
  ⟨potential, PotentialReadings.build patch source potential⟩

variable {patch pairing values} (data : GeneratorExtension patch pairing
  values)
  (unique : ((patch.triangles.flatMap OrientedTriangle.boundary).map (OrientedEdge.map patch.vertexLabels)).Nodup)

include unique

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
/-- The retained surface reading is antisymmetric under edge reversal. -/
theorem value_reverse (edge : Stokes.OrientedEdge vertices) : data.readings.value edge.reverse = -data.readings.value
  edge :=
  PotentialReadings.value_reverse data.readings unique (ProjectedEdgePairing.generatorValue_reverse pairing (vget
    values)) edge

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
/-- Reading any projected original generator returns its retained input value. -/
theorem generator_readback (index : Fin (ProjectedEdgePairing.boundaryWord pairing).alphabet.count) :
    data.readings.value (OrientedEdge.map patch.vertexLabels ((ProjectedEdgePairing.boundaryWord
      pairing).alphabet.generators index)) = vget values index :=
  (PotentialReadings.value_boundary data.readings unique _ (ProjectedEdgePairing.generator_mem pairing index)).trans
    (ProjectedEdgePairing.generatorValue_generator pairing (PotentialClosed.boundary_unique_of_occurrences unique) (vget
      values) index)

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
/-- The retained reading sums to zero around each included original face. -/
theorem face_zero (index : Fin facesCount) (covered : index ∈ indices) :
    SewingRetraction.wordValue data.readings.value (faces index).boundary = 0 :=
  PotentialReadings.face_zero data.readings unique index covered

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
/-- The retained reading vanishes on each exposed physical edge when one-sided generator values vanish. -/
theorem physical_zero
    (physical : ∀ index, (ProjectedEdgePairing.boundaryWord pairing).alphabet.oneSided index = true → vget values index
      = 0)
    (edge : Stokes.OrientedEdge patch.count) (member : edge ∈ pairing.boundary) :
    data.readings.value (OrientedEdge.map patch.vertexLabels edge) = 0 :=
  (PotentialReadings.value_boundary data.readings unique edge (pairing.boundary_subset member)).trans
    (ProjectedEdgePairing.generatorValue_physical pairing (PotentialClosed.boundary_unique_of_occurrences unique) (vget
      values) physical edge member)

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
open Purelib.Topology.Surface.Cut.GeneratorExtension in
open _root_.Purelib.Topology.Surface.Cut renaming GeneratorExtension -> GeneratorExtension in
/-- Every retained physical loop has zero value, as a consequence of its individual boundary incidences. -/
theorem physical_word_zero
    (physical : ∀ index, (ProjectedEdgePairing.boundaryWord pairing).alphabet.oneSided index = true → vget values index
      = 0)
    (word : List (Stokes.OrientedEdge vertices))
    (supported : ∀ edge ∈ word, edge ∈ pairing.boundary.map (OrientedEdge.map patch.vertexLabels)) :
    SewingRetraction.wordValue data.readings.value word = 0 := by
  induction word with
  | nil => rfl
  | cons edge rest ih =>
      obtain ⟨source, member, equal⟩ := Map.mem_map.mp (supported edge List.mem_cons_self)
      have zero := physical_zero data unique physical source member
      rw [equal] at zero
      change data.readings.value edge + SewingRetraction.wordValue data.readings.value rest = 0
      rw [zero, ih (fun other member => supported other (List.mem_cons_of_mem _ member)), zero_add]

end GeneratorExtension
end Purelib.Topology.Surface.Cut
