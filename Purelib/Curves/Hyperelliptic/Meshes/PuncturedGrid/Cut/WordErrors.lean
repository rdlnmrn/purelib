module
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Vector.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryContactErrors
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.WordArea
public import Purelib.Topology.Surface.Cut.WordErrors
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests
public import Purelib.Topology.Surface.Sewing.CenteredSewnSamples
import Purelib.Topology.Surface.Cut.ChordErrors
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.BoundaryWord

open Purelib.Topology.Surface.Cut.ChordErrors

open Purelib.Topology.Surface.Cut.IntegralPairing

open Purelib.Topology.Surface.Cut.WordArea

open Purelib.Topology.Surface.Cut.WordErrors.CutBoundaryWord

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Word

public section

/-!
# Requested word and chord errors on one actual period surface

The contact budget already controls each actual paired cut increment. Exact
word provenance transports that bound to every reversed letter; forward
letters are exact. All prefixes and retained chords share the resulting
finite error scale. No additional per-letter analytic premise is supplied.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordErrors

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds (Coordinate)
open _root_.Purelib.Topology.Surface.Boundary (BoundaryContactSources)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts (BoundaryContactPreparations)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutCycleProgram)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePairing)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies (PrimitiveFamily)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily (Requested)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests (ContactBudget)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles
open Purelib.Topology.Surface.Cut.BoundaryWord (CutWordEntry)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open _root_.Purelib.Topology.Surface.Sewing (ChordCycleBank)
open Purelib.Topology.Surface.Cut.WordErrors
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Topology.Surface.Sewing.CenteredSewnSamples (Centered)
open Purelib.Topology.Surface.Cut.BoundaryWord.ProjectedEdgePairing (boundaryWord boundaryWord_provenance)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {source :
    Differential genus} {count : Nat}
  {programs : Data.Vector
    (CutCycleProgram lifted source) count}
  {domains : FaceDomainBank lifted.frames
    base.faces.regulars} {differential : Fin genus}
  {family : PrimitiveFamily programs domains
    differential} {patch : SewnPatch lifted.mesh.triangulation.faces}
  {pairing : ProjectedEdgePairing patch.cut.vertexLabels
    patch.cut.boundary}
  {prepared : BoundaryContactPreparations patch
    pairing (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential differential) domains}
  {lengthBound : Nat} {pathTarget boundaryTarget : Coordinate}
  {targets : Data.Vector Coordinate count}
    {floor : Nat}
  {budget : ContactBudget family prepared
    lengthBound pathTarget boundaryTarget targets floor}
  {minimumStages : Data.Vector Nat count} {requested :
    Requested budget.periods
    minimumStages}

/-- The original boundary-contact budget bounds every actual cut-word letter error on the retained centered sample. -/
theorem word_errors_bounded (budget : ContactPeriodRequests.ContactBudget family prepared lengthBound pathTarget
  boundaryTarget targets floor)
    {minimumStages : Data.Vector Nat count} {requested : PrimitiveFamily.Requested budget.periods
      minimumStages}
    (sample : Requested.Sewn requested patch) (centered : CenteredSewnSamples.Centered sample.surface) {origin :
      Stokes.PrimitivePoint}
    (wordSample : CutBoundaryWord.AreaSample (ProjectedEdgePairing.boundaryWord pairing) centered.energyValues origin) :
    CutWordArea.ErrorsBounded centered.energyValues wordSample.values (ProjectedEdgePairing.boundaryWord
      pairing).alphabet.entries budget.perPair := by
  apply CutWordArea.errors_of_pairing budget.boundary.positive.le (ProjectedEdgePairing.boundaryWord_provenance pairing)
    (AreaSample.values_apply wordSample)
  intro pair member
  apply PrimitivePoint.bounded_of_conjugate
    (PrimitivePoint.add_conjugate
      (PrimitivePoint.sub_conjugate (centered.conjugate _) (centered.conjugate _))
      (PrimitivePoint.sub_conjugate (centered.conjugate _) (centered.conjugate _)))
  change Data.Gaussian.Basic.Canonical.normSq (((centered.energyValues pair.first.finish).right - (centered.energyValues
    pair.first.start).right) +
    ((centered.energyValues pair.second.finish).right - (centered.energyValues pair.second.start).right)) ≤ _
  simp only [centered.right_eq, centered.primitives_eq]
  have equal : ((sample.surface.sewn.values pair.first.finish - sample.surface.sewn.values patch.cut.anchor) -
      (sample.surface.sewn.values pair.first.start - sample.surface.sewn.values patch.cut.anchor)) +
      ((sample.surface.sewn.values pair.second.finish - sample.surface.sewn.values patch.cut.anchor) -
      (sample.surface.sewn.values pair.second.start - sample.surface.sewn.values patch.cut.anchor)) =
        (sample.surface.sewn.values pair.first.finish - sample.surface.sewn.values pair.first.start) +
          (sample.surface.sewn.values pair.second.finish - sample.surface.sewn.values pair.second.start) := by ring1
  rw [equal]
  rcases List.mem_iff_getElem.mp member with ⟨position, bound, same⟩
  have accurate := budget.boundary_accurate sample ⟨position, bound⟩
  unfold Topology.Surface.Boundary.BoundaryContactErrors.BoundaryContactSources.mismatch at accurate
  simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, same] using accurate.le

/-- The actual complete cut-word error satisfies the original boundary-length squared contact allowance. -/
theorem word_errorTotal_bounded (sample : Requested.Sewn requested patch) (centered : CenteredSewnSamples.Centered
  sample.surface)
    {origin : Stokes.PrimitivePoint} (wordSample : CutBoundaryWord.AreaSample (ProjectedEdgePairing.boundaryWord
      pairing) centered.energyValues origin) :
    PrimitivePoint.Bounded wordSample.errorTotal
      ((patch.cut.boundary.length : PreparedPrimitiveChargeBounds.Coordinate) * ((patch.cut.boundary.length :
        PreparedPrimitiveChargeBounds.Coordinate) * budget.perPair)) :=
  AreaSample.errorTotal_bounded wordSample (word_errors_bounded
    budget sample centered wordSample)

/-- Every actual cut-word path prefix has endpoint drift bounded by the original complete boundary error scale. -/
theorem word_prefix_drift_bounded (sample : Requested.Sewn requested patch) (centered : CenteredSewnSamples.Centered
  sample.surface)
    {origin : Stokes.PrimitivePoint} (wordSample : CutBoundaryWord.AreaSample (ProjectedEdgePairing.boundaryWord
      pairing) centered.energyValues origin)
    {first last : List (BoundaryWord.CutWordEntry patch.cut.vertexLabels (ProjectedEdgePairing.boundaryWord
      pairing).alphabet.generators)}
    (equal : first ++ last = (ProjectedEdgePairing.boundaryWord pairing).alphabet.entries) {start finish : Fin
      patch.cut.count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (first.map CutWordEntry.edge) start
      finish) :
    PrimitivePoint.Bounded ((centered.energyValues finish).sub ((centered.energyValues start).add
      (Pairing.linear (Pairing.totalAt (CutWordArea.word first)) wordSample.values)))
        ((patch.cut.boundary.length : PreparedPrimitiveChargeBounds.Coordinate) * ((patch.cut.boundary.length :
          PreparedPrimitiveChargeBounds.Coordinate) * budget.perPair)) := by
  have estimate := CutWordArea.prefix_drift_bounded
    (word_errors_bounded budget sample centered wordSample)
    budget.boundary.positive.le equal path
  have lengthEq := congrArg List.length (ProjectedEdgePairing.boundaryWord pairing).alphabet.edges_eq
  rw [Data.List.Map.length_map] at lengthEq
  simpa only [lengthEq] using estimate

/-- Each actual retained chord error satisfies that same original complete boundary-length squared contact allowance. -/
theorem chord_errors_bounded (sample : Requested.Sewn requested patch) (centered : CenteredSewnSamples.Centered
  sample.surface)
    {origin : Stokes.PrimitivePoint} (wordSample : CutBoundaryWord.AreaSample (ProjectedEdgePairing.boundaryWord
      pairing) centered.energyValues origin)
    {bank : Topology.Surface.Sewing.ChordCycleBank (ProjectedEdgePairing.boundaryWord pairing)}
    {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord (ProjectedEdgePairing.boundaryWord pairing)}
    (chords : bank.Sample integral centered.energyValues wordSample.values) (index : Fin
      (ProjectedEdgePairing.boundaryWord pairing).alphabet.count) :
    PrimitivePoint.Bounded (chords.errors index)
      ((patch.cut.boundary.length : PreparedPrimitiveChargeBounds.Coordinate) * ((patch.cut.boundary.length :
        PreparedPrimitiveChargeBounds.Coordinate) * budget.perPair)) :=
  ChordCycleBank.Sample.errors_bounded chords budget.boundary.positive.le
    (word_errors_bounded budget sample centered wordSample)
    index

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordErrors
