module
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBoundary
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

public section

/-!
# The full cap-area error against the retained reciprocal energy

The original occurrence order identifies the energy's opposite inverse arcs.
Exact component and endpoint accounting reduce the entire area discrepancy
to a finite sum of local arc errors, paying the actual occurrence count.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Riemann

open Purelib.Riemann.Normalization

open Purelib.Data.Gaussian.Basic.Canonical

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
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {target areaTarget : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}
  {request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared target
    areaTarget floor}

namespace Request.Evaluation

/-- The original occurrence order identifies the sampled reversed inverse-arc sum with the exact attached cap words. -/
theorem reverse_arc_sum (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.Evaluation request sample
  shared depth readingIndex)
    (attached : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared)
      (energyDepth : Nat) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.samples.values.map (fun value =>
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.arcArea sample.primitive.value.eval energyDepth
      value.entry.occurrence.finish value.entry.occurrence.start)) =
    Geometry.Grid.CellBoundary.sumValues (fun word => Geometry.Grid.CellBoundary.sumValues (fun edge =>
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.arcArea sample.primitive.value.eval energyDepth
      (lifted.vertices.coordinate edge.finish) (lifted.vertices.coordinate edge.start)) word) attached.words := open
        Purelib in by
  have indexed : evaluated.samples.values.map (fun value => value.entry.occurrence.placement.indexed) =
    attached.words.flatten := by
    calc
      _ = (evaluated.samples.values.map
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry.entry).map (fun
        entry => entry.occurrence.placement.indexed) := by
        rw [Data.List.Map.map_map]
        rfl
      _ = _ := by rw [evaluated.samples.entries_eq, request.indexed_eq, attached.words_flatten]
  rw [Geometry.Grid.CellBoundary.sumValues_flatten, ← indexed, Data.List.Map.map_map]
  apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
  apply Data.List.Map.map_congr_left
  intro value _
  dsimp only [Function.comp_def]
  rw [value.entry.occurrence.placement.start_eq, value.entry.occurrence.placement.finish_eq]

/-- The retained regular cap energy equals the actual reverse-arc sum on the same original sampled occurrences. -/
theorem energy_area_sum (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.Evaluation request sample
  shared depth readingIndex)
    {attached : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared} {geometry
      : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
      attached}
    {energyDepth : Nat} {parameters : Path.Dyadic.RadialTriangles.Parameters energyDepth} {radius :
      Normalization.InverseRootPolynomial.Coordinate}
    (energy : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularEnergy geometry parameters sample radius) :
    energy.area = Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.samples.values.map (fun value =>
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.arcArea sample.primitive.value.eval energyDepth
      value.entry.occurrence.finish value.entry.occurrence.start)) :=
  energy.area_eq_arcs.trans (evaluated.reverse_arc_sum attached energyDepth).symm

/-- Every term is charged, with the exact sample count inherited from the
original request. This is a finite area estimate, not a closure assumption. -/
theorem cap_arc_error (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.Evaluation request sample
  shared depth readingIndex)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) (energyDepth : Nat) {error :
      Normalization.InverseRootPolynomial.Coordinate}
    (localBounds : ∀ value ∈ evaluated.samples.values,
      Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.arcArea
        sample.primitive.value.eval energyDepth
        value.entry.occurrence.finish value.entry.occurrence.start + value.endpointArea + value.evaluated.right.area) ≤
          error) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.cap.area + Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (evaluated.samples.values.map (fun value =>
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.arcArea sample.primitive.value.eval energyDepth
        value.entry.occurrence.finish value.entry.occurrence.start))) ≤
        (request.count : Normalization.InverseRootPolynomial.Coordinate) ^ 2 * error := open Purelib in by
  have bound := Gaussian.Norm.Sum.Bounds.normSq_sum_le (evaluated.samples.values.map (fun value =>
    Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.arcArea sample.primitive.value.eval energyDepth
      value.entry.occurrence.finish value.entry.occurrence.start +
      value.endpointArea + value.evaluated.right.area)) error (by
        intro term member
        obtain ⟨value, member, equal⟩ := Data.List.Map.mem_map.mp member
        rw [← equal]
        exact localBounds value member)
  have count := congrArg List.length evaluated.samples.entries_eq
  rw [Data.List.Map.length_map, request.count_entries] at count
  have aligned := Data.List.Map.map_congr_left (values := evaluated.samples.values)
    (function := fun value => Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.arcArea
      sample.primitive.value.eval energyDepth value.entry.occurrence.finish value.entry.occurrence.start +
      value.endpointArea + value.evaluated.right.area)
    (other := fun value => Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.arcArea sample.primitive.value.eval
      energyDepth value.entry.occurrence.finish value.entry.occurrence.start + (value.evaluated.right.area +
      value.endpointArea))
    (by intro value _; ring1)
  rw [Data.List.Map.length_map, count, aligned, ← Data.Gaussian.Norm.Sum.Basic.gaussianSum_map_add, ←
    evaluated.cap_area_segments degree] at bound
  have commuted := bound
  rw [Gaussian.Basic.add_comm] at commuted
  exact commuted.trans_eq (by ring1)

/-- The complete cap-plus-energy discrepancy satisfies the actual occurrence-count-squared bound from the retained local
arc errors. -/
theorem cap_energy_error (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.Evaluation request sample
  shared depth readingIndex)
    (degree : curve.polynomial.natDegree = 2 * genus + 2)
    {attached : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared} {geometry
      : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
      attached}
    {energyDepth : Nat} {parameters : Path.Dyadic.RadialTriangles.Parameters energyDepth} {radius error :
      Normalization.InverseRootPolynomial.Coordinate}
    (energy : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularEnergy geometry parameters sample radius)
    (localBounds : ∀ value ∈ evaluated.samples.values,
      Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.arcArea
        sample.primitive.value.eval energyDepth
        value.entry.occurrence.finish value.entry.occurrence.start + value.endpointArea + value.evaluated.right.area) ≤
          error) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.cap.area + energy.area) ≤ (request.count :
      Normalization.InverseRootPolynomial.Coordinate) ^ 2 * error := by
  rw [evaluated.energy_area_sum energy]
  exact evaluated.cap_arc_error degree energyDepth localBounds

/-- The finite allocator pays the exact occurrence count in the full
cap-plus-energy discrepancy. Its local obligations are the existing arc
comparison certificates at the same common energy depth. -/
theorem cap_energy_error_requested (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.Evaluation request sample
  shared depth readingIndex)
    (degree : curve.polynomial.natDegree = 2 * genus + 2)
    {attached : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared} {geometry
      : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
      attached}
    {energyDepth : Nat} {parameters : Path.Dyadic.RadialTriangles.Parameters energyDepth} {radius :
      Normalization.InverseRootPolynomial.Coordinate}
    (energy : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularEnergy geometry parameters sample radius)
    (errorTarget : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < errorTarget)
    (localBounds : ∀ value ∈ evaluated.samples.values,
      Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.arcArea
        sample.primitive.value.eval energyDepth
        value.entry.occurrence.finish value.entry.occurrence.start + value.endpointArea + value.evaluated.right.area) <
          Rational.Budget.Aggregate.perTerm errorTarget request.count) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.cap.area + energy.area) < errorTarget := by
  have bound := evaluated.cap_energy_error degree energy (fun value member => (localBounds value member).le)
  have paid := Rational.Budget.Aggregate.count_mul_perTerm_lt positive request.count
  exact bound.trans_lt ((by ring1 : (request.count : Normalization.InverseRootPolynomial.Coordinate) ^ 2 *
    Rational.Budget.Aggregate.perTerm errorTarget request.count =
    (request.count : Normalization.InverseRootPolynomial.Coordinate) * ((request.count :
      Normalization.InverseRootPolynomial.Coordinate) * Rational.Budget.Aggregate.perTerm errorTarget
      request.count)).trans_lt paid)

end Request.Evaluation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation
