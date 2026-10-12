module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.WordArea
public import Purelib.Topology.Surface.Sewing.CenteredSewnSamples
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordErrors
public import Purelib.CCL.Calculus.WeightedAggregateBudget
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.CCL.Calculus

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies

open Purelib.Data.Rat

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.BoundaryWord

open Purelib.Topology.Surface.Cut.IntegralPairing

open Purelib.Topology.Surface.Cut.WordArea

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Word

public section

/-!
# One positive request for every word prefix and chord

The complete boundary count determines the per-letter error. Reallocating
the existing contact request cancels its pair-count denominator exactly,
so the final budget pays the word count once, not two independent squares.
All counts and scalar calculations are cached before numerical sampling.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds (Coordinate)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts (BoundaryContactPreparations)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutCycleProgram)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePairing)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies (PrimitiveFamily)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily (Requested)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests (ContactBudget)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutWordEntry)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open _root_.Purelib.Topology.Surface.Sewing (ChordCycleBank)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Topology.Surface.Cut.BoundaryWord.ProjectedEdgePairing (boundaryWord)
open Purelib.Topology.Surface.Sewing.CenteredSewnSamples (Centered)
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
  {patch : SewnPatch lifted.mesh.triangulation.faces}
  {pairing : ProjectedEdgePairing patch.cut.vertexLabels
    patch.cut.boundary}

set_option genInjectivity false in
/-- A cached positive budget for every original boundary-word letter, prefix and chord.

The complete retained word count determines one per-entry allowance; the contact allocation cancels its own pair-count
factor before the final word estimate. -/
structure WordBudget (family : PeriodFamilies.PrimitiveFamily programs domains differential)
    (prepared : BoundaryContacts.BoundaryContactPreparations patch pairing (PeriodMatrix.standardDifferential
      differential) domains)
    (lengthBound : Nat) (pathTarget wordTarget : PreparedPrimitiveChargeBounds.Coordinate) (targets :
      Data.Vector PreparedPrimitiveChargeBounds.Coordinate count) (floor : Nat) where
  /-- The requested complete word-error target is strictly positive. -/ positive : 0 < wordTarget
  /-- The cached complete original cut-boundary length. -/ wordCount : Nat
  /-- The cached word count equals the exact original cut-boundary length. -/ wordCount_eq : wordCount =
    patch.cut.boundary.length
  /-- The cached positive error allowance per original word entry. -/ perEntry :
    PreparedPrimitiveChargeBounds.Coordinate
  /-- The per-entry allowance is the aggregate allocation using the retained word target and count. -/ perEntry_eq :
    perEntry = Aggregate.perTerm wordTarget wordCount
  /-- The cached contact-boundary target before cancellation of the original pair-count scale. -/ boundaryTarget :
    PreparedPrimitiveChargeBounds.Coordinate
  /-- The contact target is the original pair-count scale multiplied by the cached word-entry allowance. -/
    boundaryTarget_eq : boundaryTarget =
    (2 * (Aggregate.countCoordinate prepared.pairCount + 1) ^ 2) * perEntry
  /-- The original joint period and contact request paying the cached boundary target. -/ request :
    ContactPeriodRequests.ContactBudget family prepared lengthBound pathTarget boundaryTarget targets floor

constructive_injectivity WordBudget

namespace WordBudget

variable {family : PrimitiveFamily programs domains
  differential}
  {prepared : BoundaryContactPreparations patch
    pairing (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential differential) domains}
  {lengthBound : Nat} {pathTarget wordTarget : Coordinate}
  {targets : Data.Vector Coordinate count}
    {floor : Nat}

/-- Consume a previously cached complete boundary count. In particular, an implicit canonical patch must not be
materialized just to count its edges. Generated and intrinsic boundary programs supply the same exact readback. -/
@[expose] def build (family : PeriodFamilies.PrimitiveFamily programs domains differential)
    (prepared : BoundaryContacts.BoundaryContactPreparations patch pairing (PeriodMatrix.standardDifferential
      differential) domains)
    (wordCount : Nat) (wordCount_eq : wordCount = patch.cut.boundary.length)
    (lengthBound : Nat) (pathTarget : PreparedPrimitiveChargeBounds.Coordinate) (pathPositive : 0 < pathTarget)
    (wordTarget : PreparedPrimitiveChargeBounds.Coordinate) (wordPositive : 0 < wordTarget)
    (targets : Data.Vector PreparedPrimitiveChargeBounds.Coordinate count) (positive : ∀ index, 0 < targets
      index) (floor : Nat) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordRequests.WordBudget family prepared lengthBound pathTarget
      wordTarget targets floor :=
  let perEntry := Aggregate.perTerm wordTarget wordCount
  let boundaryTarget := (2 * (Aggregate.countCoordinate prepared.pairCount + 1) ^ 2) * perEntry
  have boundaryPositive := Fraction.Order.Arithmetic.mul_pos_direct
    (WeightedAggregateBudget.countScale_positive prepared.pairCount)
    (Aggregate.perTerm_positive wordPositive wordCount)
  ⟨wordPositive, wordCount, wordCount_eq, perEntry, rfl, boundaryTarget, rfl,
    ContactBudget.build family prepared lengthBound pathTarget pathPositive boundaryTarget boundaryPositive targets
      positive floor⟩

/-- Cancellation of the contact pair-count scale leaves exactly the allocation for the complete original word count. -/
theorem perPair_eq (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordRequests.WordBudget family prepared
  lengthBound pathTarget wordTarget targets floor) :
    budget.request.perPair = Aggregate.perTerm wordTarget patch.cut.boundary.length := by
  have countEq : budget.request.pairCount = prepared.pairCount := budget.request.pairCount_eq.trans
    prepared.pairCount_eq.symm
  exact budget.request.perPair_eq.trans
    ((congrArg₂ Aggregate.perTerm budget.boundaryTarget_eq countEq).trans
      ((WeightedAggregateBudget.perTerm_rescale budget.perEntry prepared.pairCount).trans
        (budget.perEntry_eq.trans (congrArg (Aggregate.perTerm wordTarget) budget.wordCount_eq))))

/-- The squared original word-count error scale remains strictly below the requested complete target. -/
theorem total_error_lt (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordRequests.WordBudget family prepared
  lengthBound pathTarget wordTarget targets floor) :
    (patch.cut.boundary.length : PreparedPrimitiveChargeBounds.Coordinate) * ((patch.cut.boundary.length :
      PreparedPrimitiveChargeBounds.Coordinate) * budget.request.perPair) < wordTarget := by
  rw [budget.perPair_eq]
  exact Aggregate.count_mul_perTerm_lt budget.positive _

/-- The actual period request retains the supplied minimum stage floor. -/
theorem floor_le (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordRequests.WordBudget family prepared
  lengthBound pathTarget wordTarget targets floor) :
    floor ≤ budget.request.periods.index := budget.request.contacts.floor_le.trans budget.request.periods.surface_later

/-- Both components of the complete original word-error total satisfy the retained positive word target. -/
theorem word_accurate (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordRequests.WordBudget family prepared
  lengthBound pathTarget wordTarget targets floor)
    {minimumStages : Data.Vector Nat count} {requested : PrimitiveFamily.Requested budget.request.periods
      minimumStages}
    (sample : Requested.Sewn requested patch) (centered : CenteredSewnSamples.Centered sample.surface) {origin :
      Stokes.PrimitivePoint}
    (wordSample : CutBoundaryWord.AreaSample (ProjectedEdgePairing.boundaryWord pairing) centered.energyValues origin) :
    Data.Gaussian.Norm.Basic.normSq wordSample.errorTotal.left < wordTarget ∧
      Data.Gaussian.Norm.Basic.normSq wordSample.errorTotal.right < wordTarget :=
  let bounded := WordErrors.word_errorTotal_bounded (budget := budget.request) sample centered wordSample
  by
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
      (show _ ∧ _ from ⟨bounded.1.trans_lt budget.total_error_lt,
        bounded.2.trans_lt budget.total_error_lt⟩)

/-- Each original chord error satisfies the same retained word target in both primitive coordinates. -/
theorem chords_accurate (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordRequests.WordBudget family prepared
  lengthBound pathTarget wordTarget targets floor)
    {minimumStages : Data.Vector Nat count} {requested : PrimitiveFamily.Requested budget.request.periods
      minimumStages}
    (sample : Requested.Sewn requested patch) (centered : CenteredSewnSamples.Centered sample.surface) {origin :
      Stokes.PrimitivePoint}
    (wordSample : CutBoundaryWord.AreaSample (ProjectedEdgePairing.boundaryWord pairing) centered.energyValues origin)
    {bank : Topology.Surface.Sewing.ChordCycleBank (ProjectedEdgePairing.boundaryWord pairing)} {integral :
      Topology.Surface.Cut.IntegralPairing.CutBoundaryWord (ProjectedEdgePairing.boundaryWord pairing)}
    (chords : bank.Sample integral centered.energyValues wordSample.values) (index : Fin
      (ProjectedEdgePairing.boundaryWord pairing).alphabet.count) :
    Data.Gaussian.Norm.Basic.normSq (chords.errors index).left < wordTarget ∧
      Data.Gaussian.Norm.Basic.normSq (chords.errors index).right < wordTarget :=
  let bounded := WordErrors.chord_errors_bounded (budget := budget.request) sample centered wordSample chords index
  by
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
      (show _ ∧ _ from ⟨bounded.1.trans_lt budget.total_error_lt,
        bounded.2.trans_lt budget.total_error_lt⟩)

/-- Every actual original word-prefix drift satisfies the retained target in both primitive coordinates. -/
theorem prefix_accurate (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordRequests.WordBudget family prepared
  lengthBound pathTarget wordTarget targets floor)
    {minimumStages : Data.Vector Nat count} {requested : PrimitiveFamily.Requested budget.request.periods
      minimumStages}
    (sample : Requested.Sewn requested patch) (centered : CenteredSewnSamples.Centered sample.surface) {origin :
      Stokes.PrimitivePoint}
    (wordSample : CutBoundaryWord.AreaSample (ProjectedEdgePairing.boundaryWord pairing) centered.energyValues origin)
    {first last : List (BoundaryWord.CutWordEntry patch.cut.vertexLabels (ProjectedEdgePairing.boundaryWord
      pairing).alphabet.generators)}
    (equal : first ++ last = (ProjectedEdgePairing.boundaryWord pairing).alphabet.entries) {start finish : Fin
      patch.cut.count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (first.map CutWordEntry.edge) start
      finish) :
    let drift := (centered.energyValues finish).sub ((centered.energyValues start).add
      (Pairing.linear (Pairing.totalAt (CutWordArea.word first)) wordSample.values))
    Data.Gaussian.Norm.Basic.normSq drift.left < wordTarget ∧ Data.Gaussian.Norm.Basic.normSq
      drift.right < wordTarget :=
  let bounded := WordErrors.word_prefix_drift_bounded (budget := budget.request) sample centered wordSample equal path
  by
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
      (show _ ∧ _ from ⟨bounded.1.trans_lt budget.total_error_lt,
        bounded.2.trans_lt budget.total_error_lt⟩)

end WordBudget
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordRequests
