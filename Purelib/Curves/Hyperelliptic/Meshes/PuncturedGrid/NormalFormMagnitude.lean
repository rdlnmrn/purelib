module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PrimitiveAreaBounds
public import Purelib.Topology.Surface.Boundary.DualCoordinateBounds
import Purelib.Topology.Surface.Boundary.NormalFormArea
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.WordArea
import Purelib.Topology.Surface.Sewing.CenteredSewnSamples
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests
import Purelib.Topology.Surface.Cut.GeneratorBounds
import Purelib.Topology.Surface.Word.NormalFormMagnitude
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Curves

open Purelib

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann

public section

/-!
# Fixed bounds for actual transformed word readings

The coarse boundary reference and cached dual amplification are prepared
before accuracy. They control the actual retained generator increments and
all computed handle coordinates on every later shared surface.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormMagnitude

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {source : Hyperelliptic.Differentials.Basic.Differential genus} {boundary :
    Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms.LiftedPuncturedGrid.BoundaryProgram lifted source}
  {segments : Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank boundary.program.period} {differential :
    Fin genus}
  {comparison : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank.ofSegments boundary.program segments) differential}
  {pairing : Topology.Surface.Word.ProjectedEdgePairs.ProjectedEdgePairing lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {count : Nat} {programs : Data.Vector
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram lifted source) count}

namespace WordAreaBudget

variable {family : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily programs comparison.domains
  differential}
  {prepared : Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch
    pairing (Periods.PeriodMatrix.standardDifferential differential) comparison.domains}
  {reference : Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences.BoundaryReference boundary comparison
    prepared.prepared}
  {lengthBound : Nat} {pathTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate}
  {targets : Data.Vector Normalization.InverseRootPolynomial.Coordinate count} {floor : Nat}

/-- The actual centered generator readings are bounded by four times the retained original boundary reference. -/
theorem word_values_bounded (budget : Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests.WordAreaBudget family
  prepared reference lengthBound pathTarget areaTarget targets floor)
    {minimumStages : Data.Vector Nat count} {requested :
      Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily.Requested budget.word.request.periods
      minimumStages}
    (sample : Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles.Requested.Sewn requested lifted.cutPolygon.patch)
      (centered : Topology.Surface.Sewing.CenteredSewnSamples.Centered sample.surface)
    {wordData : Topology.Surface.Cut.BoundaryWord.CutBoundaryWord lifted.cutPolygon.patch.cut.vertexLabels
      lifted.cutPolygon.patch.cut.boundary}
    (wordSample : Topology.Surface.Cut.WordArea.CutBoundaryWord.AreaSample wordData centered.energyValues
      (centered.energyValues lifted.cutPolygon.patch.cut.anchor))
    (word_eq : wordData = Topology.Surface.Cut.BoundaryWord.ProjectedEdgePairing.boundaryWord pairing) (index : Fin
      wordData.alphabet.count) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (wordSample.values index) (4 * reference.bound) := open
      Purelib.Data in by
  apply Topology.Surface.Cut.GeneratorBounds.CutBoundaryWord.AreaSample.values_bounded wordSample pairing word_eq ?_
    index
  intro edge member
  constructor
  · apply Readings.PrimitiveAreaBounds.PrimitivePoint.bounded_of_conjugate (centered.conjugate _)
    rw [centered.right_eq, centered.primitives_eq]
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
      reference.start_bounded budget.reference_later sample.triangles sample.surface edge member
  · apply Readings.PrimitiveAreaBounds.PrimitivePoint.bounded_of_conjugate (centered.conjugate _)
    rw [centered.right_eq, centered.primitives_eq]
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
      reference.finish_bounded budget.reference_later sample.triangles sample.surface edge member

/-- The actual transformed normal-form coordinates satisfy the original reference bound amplified by the cached dual
profile. -/
theorem normal_values_bounded (budget : Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests.WordAreaBudget family
  prepared reference lengthBound pathTarget areaTarget targets floor)
    {minimumStages : Data.Vector Nat count} {requested :
      Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily.Requested budget.word.request.periods
      minimumStages}
    (sample : Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles.Requested.Sewn requested lifted.cutPolygon.patch)
      (centered : Topology.Surface.Sewing.CenteredSewnSamples.Centered sample.surface)
    {wordData : Topology.Surface.Cut.BoundaryWord.CutBoundaryWord lifted.cutPolygon.patch.cut.vertexLabels
      lifted.cutPolygon.patch.cut.boundary}
    (wordSample : Topology.Surface.Cut.WordArea.CutBoundaryWord.AreaSample wordData centered.energyValues
      (centered.energyValues lifted.cutPolygon.patch.cut.anchor))
    (word_eq : wordData = Topology.Surface.Cut.BoundaryWord.ProjectedEdgePairing.boundaryWord pairing)
    {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord wordData} {raw : List
      (Handle.Basic.PivotIndices wordData.alphabet.count)}
    {normal : LinearAlgebra.Alternating.NormalForm integral.paired raw} (profile :
      Topology.Surface.Boundary.DualCoordinateBounds.DualMagnitude normal.reduction)
    (evaluated : Topology.Surface.Boundary.NormalFormArea normal wordSample.values) (index : Fin
      wordData.alphabet.count) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (evaluated.points index) (profile.factor * (4 *
      reference.bound)) :=
  open Purelib.Data.Rat in Topology.Surface.Word.NormalFormMagnitude.NormalFormArea.bounded evaluated profile
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) reference.bound_positive.le)
    (Hyperelliptic.Meshes.PuncturedGrid.NormalFormMagnitude.WordAreaBudget.word_values_bounded budget sample centered
      wordSample word_eq) index

end WordAreaBudget
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormMagnitude
