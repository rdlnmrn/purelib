module
import Purelib.Data.List.Map
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedComponentBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapJoining
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
public import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

public section

/-! The retained cap request itself pays its canonical component-total premise. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapTotalBounds

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib

open Purelib.Riemann.Normalization

open _root_.Purelib.Data.Gaussian.Basic (conj)

/-- The paired total of an ordered list is the pair of component sums, with the first component conjugated. -/
private theorem paired_total {A : Type u} (values : List A) (first last : A →
  Normalization.InverseRootPolynomial.Gaussian) :
    Path.PairedIncrementArea.total (values.map (fun value => (⟨conj (first value), last value⟩ :
      Topology.Polygon.Stokes.PrimitivePoint))) =
      (⟨conj (Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map first)), Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (values.map last)⟩ : Topology.Polygon.Stokes.PrimitivePoint) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      change (⟨conj (first head), last head⟩ : Topology.Polygon.Stokes.PrimitivePoint).add
        (Path.PairedIncrementArea.total _) = _
      rw [ih]
      exact congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk (Gaussian.Basic.conj_add _ _).symm rfl

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

/-- The automatic surface preparation retains exactly the lifted grid's original exterior boundary words. -/
private theorem canonical_components (source : Hyperelliptic.Differentials.Basic.Differential genus) :

      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
      regular domains source).components.map (fun component => component.program.indexed) =
      lifted.exteriorBoundaries := by
  change ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.exteriorPrograms lifted source).map
    (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent.build
    regular domains)).map _ = _
  rw [Data.List.Map.map_map]
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.exteriorPrograms_indexed lifted source

namespace PairedCapRequest
variable {target : Normalization.InverseRootPolynomial.Coordinate} {floor stage depth otherDepth readingIndex : Nat}
  {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage box}
  {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    {otherShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other stage domains}
  {allocated : PairedCapRequest
    (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
    regular domains differential)

      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
      regular domains other) target floor}

/-- Component totals use the existing allowance, even though the two cap
samples have independent local subdivisions. All component ownership is internal. -/
theorem Evaluation.built_component_totals_bounded
    (evaluated : PairedCapRequest.Evaluation allocated
      sample otherSample shared otherShared depth otherDepth readingIndex)
    (degree : curve.polynomial.natDegree = 2 * genus + 2)
    (firstReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
      (lastReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings otherShared
      lifted.mesh) :
    ∀ word ∈ lifted.exteriorBoundaries,
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.PairedIncrementArea.total (word.map (fun edge =>
        (⟨conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh firstReadings.values
          edge),
          Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh lastReadings.values edge⟩ :
            Topology.Polygon.Stokes.PrimitivePoint)))) allocated.allowance := by
  intro word member
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapTotalBounds.paired_total]
  have first := evaluated.left.canonical_word_small
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapTotalBounds.canonical_components differential) degree
    firstReadings word member
  have last := evaluated.right.canonical_word_small
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapTotalBounds.canonical_components other) degree lastReadings
    word member
  constructor
  · have h := (Gaussian.Norm.Basic.normSq_conj _).trans_le first.le
    change Fraction.Order.Basic.LessEqual _ _ at h
    change Fraction.Order.Basic.LessEqual _ _
    simpa only [Gaussian.Basic.conj_eq_canonical,
      Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using h
  · have h := last.le
    change Fraction.Order.Basic.LessEqual _ _ at h
    change Fraction.Order.Basic.LessEqual _ _
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using h

/-- The same cap evaluations also pay the two one-lap periods needed by the
terminal-product comparison, on either supplied incoming sheet. -/
theorem Evaluation.built_one_lap_small
    (evaluated : PairedCapRequest.Evaluation allocated
      sample otherSample shared otherShared depth otherDepth readingIndex)
    (degree : curve.polynomial.natDegree = 2 * genus + 2)
    (firstReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
      (lastReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings otherShared
      lifted.mesh)
    (sheet : Fin 2) :
    Data.Gaussian.Norm.Basic.normSq (lifted.edges.chainValue lifted.vertices
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh firstReadings.values)
      base.bank.exterior sheet) < allocated.allowance ∧
    Data.Gaussian.Norm.Basic.normSq (lifted.edges.chainValue lifted.vertices
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh lastReadings.values)
      base.bank.exterior sheet) < allocated.allowance :=
  ⟨evaluated.left.canonical_one_lap_small
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapTotalBounds.canonical_components differential) degree
    firstReadings sheet,
    evaluated.right.canonical_one_lap_small
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapTotalBounds.canonical_components other) degree lastReadings
      sheet⟩

/-- The complete regular source-to-attachment estimate has no external
component-total hypothesis or additional period acquisition. -/
theorem Evaluation.conjugate_built_joining_paid
    (evaluated : PairedCapRequest.Evaluation allocated
      sample otherSample shared otherShared depth otherDepth readingIndex)
    (attached : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
      regular domains differential))
    (degree : curve.polynomial.natDegree = 2 * genus + 2)
    (firstReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
      (lastReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings otherShared
      lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (lifted.exteriorBoundaries.map (fun
      word => Path.PairedIncrementArea.area (word.map (fun edge =>
      (⟨conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh firstReadings.values
        edge),
        Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh lastReadings.values edge⟩ :
          Topology.Polygon.Stokes.PrimitivePoint))))) -
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons.CapAttachment.conjugateJoiningArea attached
        sample otherSample) < 2 * (target + 4 * allocated.allowance^2) :=

    BuiltCapJoining.PairedCapRequest.Evaluation.conjugate_built_joining_accurate
    evaluated attached degree firstReadings lastReadings

      (Evaluation.built_component_totals_bounded
      evaluated degree firstReadings lastReadings)

end PairedCapRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapTotalBounds
