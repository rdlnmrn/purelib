module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedCapPolygons
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateCanonicalTotals
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

public section

/-! The retained automatic regular cap samples realize the attachment polygon. -/
section

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib

open Purelib.Data.List

open Purelib.Riemann.Normalization

open _root_.Purelib.Data.Gaussian.Basic (conj)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapJoining

/-- Gaussian conjugation preserves subtraction. -/
private theorem conj_sub (first last : Normalization.InverseRootPolynomial.Gaussian) : Data.Gaussian.Basic.conj
  (first - last) = Data.Gaussian.Basic.conj first - Data.Gaussian.Basic.conj last := by
  apply Gaussian.Basic.ext
  · rfl
  · simp only [Data.Gaussian.Basic.conj, Gaussian.Basic.sub_im, -eq_self, -iff_self]; ring1

/-- Pairing mapped Gaussian totals agrees with mapping their original zipped entries, with the first coordinate
conjugated. -/
private theorem zip_totals {A : Type u} {B : Type v} (first : A → Normalization.InverseRootPolynomial.Gaussian) (last :
  B → Normalization.InverseRootPolynomial.Gaussian)
    (xs : List A) (ys : List B) :
    (xs.zip ys).map (fun pair => (⟨conj (first pair.1), last pair.2⟩ : Topology.Polygon.Stokes.PrimitivePoint)) =
      List.zipWith (fun left right => (⟨conj left, right⟩ : Topology.Polygon.Stokes.PrimitivePoint)) (xs.map first)
        (ys.map last) := by
  induction xs generalizing ys with
  | nil => rfl
  | cons head tail ih => cases ys with
    | nil => rfl
    | cons other rest => exact congrArg (List.cons _) (ih rest)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapJoining

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapJoining

/-- For even polynomial degree, the automatic exterior preparation retains exactly the original sheet-zero and sheet-one
programs. -/
private theorem built_programs (source : Hyperelliptic.Differentials.Basic.Differential genus) (degree :
  curve.polynomial.natDegree = 2 * genus + 2) :

      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
      regular domains source).components.map
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent.program
      =
      [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted source 0,
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted source 1] := by
  cases shape : curve.degreeShape with
  | odd oddDegree =>
      have impossible : False := by omega
      exact impossible.elim
  | even _ =>
      simp only
        [SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build,
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.exteriorPrograms, shape, List.map_cons, List.map_nil,
        -eq_self, -iff_self]
      rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapJoining

variable {target : Normalization.InverseRootPolynomial.Coordinate} {floor stage depth otherDepth readingIndex : Nat}
  {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage box}
  {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    {otherShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other stage domains}
  {allocated : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest
    (ExteriorProgram.AllSurfacePreparation.build
    regular domains differential)

      (ExteriorProgram.AllSurfacePreparation.build
      regular domains other) target floor}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapJoining.PairedCapRequest.Evaluation

/-- The entire retained paired cap-total polygon, including both exterior
components, is exactly the joining area of the supplied automatic attachment. -/
theorem conjugate_built_joining
    (evaluated : PairedCapRequest.Evaluation allocated
      sample otherSample shared otherShared depth otherDepth readingIndex)
    (attached : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
      regular domains differential))
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    Path.PairedIncrementArea.area ((evaluated.left.samples.pairedValues evaluated.right.samples).map (fun pair =>
      Path.ConjugateIncrementComparison.conjugateFirst pair.2)) =
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons.CapAttachment.conjugateJoiningArea attached
        sample otherSample := by
  have leftPrograms := (congrArg (List.map
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent.program)
    evaluated.left.components.components_eq).trans
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapJoining.built_programs (regular := regular) (domains :=
      domains) differential degree)
  have rightPrograms := (congrArg (List.map
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent.program)
    evaluated.right.components.components_eq).trans
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapJoining.built_programs other degree)
  rw [Map.map_map] at leftPrograms rightPrograms
  have grouped := Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent.paired_groups_area [0,
    1] evaluated.left.components.groups evaluated.right.components.groups
    leftPrograms rightPrograms degree
  rw [evaluated.left.components.values_eq, evaluated.right.components.values_eq] at grouped
  have entries : (evaluated.left.samples.pairedValues evaluated.right.samples).map (fun pair =>
    Path.ConjugateIncrementComparison.conjugateFirst pair.2) =
      List.zipWith (fun left right => (⟨conj left, right⟩ : Topology.Polygon.Stokes.PrimitivePoint))
        (evaluated.left.samples.values.map (fun value => value.evaluated.right.total))
        (evaluated.right.samples.values.map (fun value => value.evaluated.right.total)) := by
    simp only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples.pairedValues,
      Map.map_map, -eq_self, -iff_self]
    exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapJoining.zip_totals (fun value =>
      value.evaluated.right.total) (fun value => value.evaluated.right.total)
      evaluated.left.samples.values evaluated.right.samples.values
  have result := (congrArg Path.PairedIncrementArea.area entries).trans grouped
  have wordOrder := attached.words_eq.trans (Data.List.Map.map_congr_left
    (fun component _ => component.prepared.occurrences_eq))
  have selected := congrArg (List.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.indexed)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapJoining.built_programs (regular := regular) (domains :=
    domains) differential degree)
  rw [Map.map_map] at selected
  have words : attached.words = ([0, 1] : List (Fin 2)).map
      (fun sheet => (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted
        differential sheet).indexed) := wordOrder.trans selected
  apply result.trans
  unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons.CapAttachment.conjugateJoiningArea
  dsimp only
  rw [words, Map.map_map]
  apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
  apply Data.List.Map.map_congr_left
  intro sheet _
  apply congrArg Path.PairedIncrementArea.area
  apply Data.List.Map.map_congr_left
  intro edge _
  exact congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapJoining.conj_sub _ _) rfl

/-- Pay the canonical exterior-to-attachment comparison using the original
request allowance and its retained component-total bound. -/
theorem conjugate_built_joining_accurate
    (evaluated : PairedCapRequest.Evaluation allocated
      sample otherSample shared otherShared depth otherDepth readingIndex)
    (attached : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
      regular domains differential))
    (degree : curve.polynomial.natDegree = 2 * genus + 2)
    (firstReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
      (lastReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings otherShared
      lifted.mesh)
    {bound : Normalization.InverseRootPolynomial.Coordinate}
    (bounded : ∀ word ∈ lifted.exteriorBoundaries,
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
        (Path.PairedIncrementArea.total (word.map (fun edge =>
          (⟨conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh firstReadings.values
            edge),
            Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh lastReadings.values edge⟩ :
              Topology.Polygon.Stokes.PrimitivePoint)))) bound) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (lifted.exteriorBoundaries.map (fun
      word => Path.PairedIncrementArea.area (word.map (fun edge =>
      (⟨conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh firstReadings.values
        edge),
        Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh lastReadings.values edge⟩ :
          Topology.Polygon.Stokes.PrimitivePoint))))) -
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons.CapAttachment.conjugateJoiningArea attached
        sample otherSample) < 2 * (target + 4 * bound^2) := by
  have comparison := evaluated.conjugate_components_accurate firstReadings lastReadings bounded
  dsimp only at comparison
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapJoining.PairedCapRequest.Evaluation.conjugate_built_joining
    evaluated attached degree, Map.map_map] at comparison
  exact comparison

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapJoining.PairedCapRequest.Evaluation

end
