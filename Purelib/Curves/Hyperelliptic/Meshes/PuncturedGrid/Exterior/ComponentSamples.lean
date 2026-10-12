module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Data.List.Flatten
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapJoins
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RegularWitnesses
import Batteries.Logic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

public section

/-!
# Group the existing shared-surface samples by their original components

The certified occurrence order splits the already computed sample list.
Component summaries combine cached segment summaries, without another root
reading, primitive evaluation, or preparation.
-/

section

open Purelib.Curves
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation SurfaceComponent SurfaceOccurrence)

open Purelib.Riemann.Normalization

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples

set_option genInjectivity false in
/-- An exact ordered split of the original values whose mapped readback is the supplied concatenation. -/
structure MappedSplit {Alpha : Type u} {Beta : Type v} (map : Alpha → Beta)
    (first last : List Beta) (values : List Alpha) where
  /-- The retained original prefix. -/ before : List Alpha
  /-- The retained original suffix. -/ after : List Alpha
  /-- The prefix maps to exactly the supplied first list. -/ before_eq : before.map map = first
  /-- The suffix maps to exactly the supplied last list. -/ after_eq : after.map map = last
  /-- The two retained lists concatenate to the original values. -/ append_eq : before ++ after = values

constructive_injectivity MappedSplit

/-- Split the original values at the certified mapped prefix while retaining both readbacks and the exact append
identity. -/
@[expose] def splitMapped {Alpha : Type u} {Beta : Type v} (map : Alpha → Beta) :
    (first last : List Beta) → (values : List Alpha) → values.map map = first ++ last →
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.MappedSplit map first last values
  | [], _, values, equal => ⟨[], values, rfl, equal, rfl⟩
  | _ :: _, _, [], equal => by cases equal
  | first :: remaining, last, value :: values, equal => by
      have parts := List.cons.inj equal
      let split := Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.splitMapped map remaining
        last values parts.2
      exact ⟨value :: split.before, split.after, congrArg₂ List.cons parts.1 split.before_eq,
        split.after_eq, congrArg (List.cons value) split.append_eq⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {index depth readingIndex : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {shared :
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
  {localTarget localArea : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples

set_option genInjectivity false in
/-- One original exterior component with its actual retained occurrence samples and cached cap and surface summaries. -/
structure SampledComponent (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains) (depth
      readingIndex : Nat)
    (localTarget localArea : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original exterior component and its retained surface preparation. -/ component :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
    regular domains differential
  /-- The actual samples of that component's original occurrences. -/ values : List
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry (regular := regular)
    sample shared depth readingIndex localTarget localArea floor)
  /-- The sample occurrences equal the original component order exactly. -/ occurrences_eq : values.map (fun value =>
    value.entry.occurrence) = component.prepared.occurrences
  /-- The cached summary of the actual complete cap paths. -/ cap : Path.IncrementArea.Summary (values.map (fun value =>
    value.evaluated.capPath)).flatten
  /-- The summary of the corresponding original surface increments. -/ surface : Path.IncrementArea.Summary (values.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry.increment)

constructive_injectivity SampledComponent

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent

/-- Group the supplied original occurrence samples and combine their cached cap summaries without new primitive
readings. -/
@[expose] def build (component :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
  regular domains differential)
    (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry
      (regular := regular) sample shared depth readingIndex localTarget localArea floor))
    (occurrences : values.map (fun value => value.entry.occurrence) = component.prepared.occurrences) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent (regular := regular) sample shared
      depth readingIndex localTarget localArea floor := by
  refine ⟨component, values, occurrences, ?_, Path.IncrementArea.Summary.build (values.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry.increment)⟩
  simpa only [Map.map_map, Function.comp_def,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry.pair, -eq_self,
    -iff_self] using
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry.rightSummary values

/-- In even degree, the actual cached cap area equals the complete retained regular primitive-path area. -/
theorem regular_area (group : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent (regular :=
  regular) sample shared depth readingIndex localTarget localArea floor)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    group.cap.area = Path.IncrementArea.pathArea
      (Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive.SideBank.regularPrimitivePaths sample.primitive.value
        depth
        (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.capSpine
        group.component.prepared.occurrences).bank).flatten := by
  rw [group.cap.area_eq]
  exact group.component.prepared.regular_cap_area group.values group.occurrences_eq degree

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

set_option genInjectivity false in
/-- Both projections certify an exact partition of the original sample
list in its original order, including empty components. -/
structure ComponentSamples (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains) (depth
      readingIndex : Nat)
    (localTarget localArea : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat)
    (components : List
      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
      regular domains differential))
    (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry
      (regular := regular) sample shared depth readingIndex localTarget localArea floor)) where
  /-- The grouped original component samples. -/ groups : List
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent (regular := regular) sample shared
    depth readingIndex localTarget localArea floor)
  /-- The groups retain exactly the supplied original components. -/ components_eq : groups.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent.component = components
  /-- Flattening the grouped samples recovers the exact original sample list. -/ values_eq : (groups.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent.values).flatten = values

constructive_injectivity ComponentSamples

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples

/-- Split the already computed samples along the original component occurrence lists, including empty components. -/
@[expose] def build : (components : List
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
  regular domains differential)) →
    (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry
      (regular := regular) sample shared depth readingIndex localTarget localArea floor)) →
    values.map (fun value => value.entry.occurrence) = components.flatMap (fun component =>
      component.prepared.occurrences) →
    ComponentSamples sample shared depth readingIndex
      localTarget localArea floor components values
  | [], values, equal => by
      have empty : values = [] := List.map_eq_nil_iff.mp equal
      subst values
      exact ⟨[], rfl, rfl⟩
  | component :: components, values, equal => by
      let split := Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.splitMapped (fun value :
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry (regular :=
        regular) sample shared depth readingIndex localTarget localArea floor => value.entry.occurrence)
        component.prepared.occurrences (components.flatMap (fun item :
          SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
          regular domains differential => item.prepared.occurrences)) values
        (by simpa only [Flatten.flatMap_cons, -eq_self, -iff_self] using equal)
      let head := Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent.build component
        split.before split.before_eq
      let tail := build
        components split.after split.after_eq
      refine ⟨head :: tail.groups, congrArg (List.cons component) tail.components_eq, ?_⟩
      change split.before ++ (tail.groups.map
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent.values).flatten = values
      rw [tail.values_eq]
      exact split.append_eq

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples

variable {prepared :
  ExteriorProgram.AllSurfacePreparation
  regular domains differential} {target areaTarget : Normalization.InverseRootPolynomial.Coordinate}
  {request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared target
    areaTarget floor}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request
namespace Evaluation

/-- Group the exact samples already used by the full surface estimate. -/
@[expose] def components
    (evaluated : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.Evaluation
      request sample shared depth readingIndex) :
    ComponentSamples sample shared depth readingIndex
      request.localTarget request.budget.areaTarget floor prepared.components evaluated.samples.values := by
  apply ComponentSamples.build
  calc
    evaluated.samples.values.map (fun value => value.entry.occurrence) =
        (evaluated.samples.values.map
          Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry.entry).map
          Entry.occurrence
          := by
      rw [Map.map_map]
      rfl
    _ = prepared.components.flatMap (fun component => component.prepared.occurrences) := by
      rw [evaluated.samples.entries_eq, request.occurrences_eq, prepared.occurrences_eq]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.Evaluation

end
