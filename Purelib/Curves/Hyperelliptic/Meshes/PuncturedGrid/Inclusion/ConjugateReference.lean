module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Riemann

open Purelib

public section

/-! Conjugate reference corrections use the retained prefix bounds and
two-sheet total requests, preserving the even exterior correction. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateReference

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base next : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {current :
    Meshes.LiftedPuncturedGrid next}
  (included : Geometry.Grid.Extension.CoordinateInclusion base.bank.grid next.bank.grid)
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames next.faces.regulars}
  {firstDifferential secondDifferential : Hyperelliptic.Differentials.Basic.Differential genus}

namespace PolarizedReferenceRequest

open Purelib.Topology.Surface.Sewing.SewingRetraction in
/-- Conjugating every original edge reading conjugates the retained word value. -/
private theorem word_conj {count : Nat} (value : Topology.Polygon.Stokes.OrientedEdge count → Gaussian.Basic.Canonical)
  (word : List (Topology.Polygon.Stokes.OrientedEdge count)) :
    wordValue (fun edge => Data.Gaussian.Basic.conj (value edge)) word =
      Data.Gaussian.Basic.conj (wordValue value word) := by
  induction word with
  | nil => rfl
  | cons edge rest ih =>
      change Data.Gaussian.Basic.conj (value edge) + wordValue _ rest =
        Data.Gaussian.Basic.conj (value edge + wordValue value rest)
      rw [ih, Gaussian.Basic.conj_add]

/-- The conjugated pair of original values satisfies the same sum magnitude bound. -/
private theorem conjugate_sum_bound {first last : Gaussian.Basic.Canonical} {bound : Fraction.Rational}
    (small : Data.Gaussian.Norm.Basic.normSq (first + last) ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Basic.conj first + Data.Gaussian.Basic.conj last) ≤ bound
      := by
  rw [← Gaussian.Basic.conj_add, Gaussian.Norm.Basic.normSq_conj]
  exact small

/-- The original squared-length paired-prefix bound is nonnegative. -/
private theorem prefixBound_nonnegative (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank
  domains firstDifferential) :
    0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.prefixBound (paired :=
      paired) included fixed :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.pow_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) fixed.nonnegative)

open Purelib.Topology.Surface.Sewing.SewingRetraction in
/-- The cached original paired-prefix word observation meets its retained magnitude bound. -/
private theorem prefix_bounded (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  firstDifferential)
    {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank firstDifferential
      stage domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
      (later : fixed.index ≤ stage) (newSheet : Fin 2) :
    Data.Gaussian.Norm.Basic.normSq (wordValue (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
      current.mesh readings.values)
      (current.edges.indexedEdges current.vertices
        (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.priorWalk (paired :=
        paired) included) newSheet)) ≤
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.prefixBound (paired :=
        paired) included fixed := by
  let retainedMagnitude := Readings.EdgeMagnitude.ofBank
    (owner := Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison.ownerFromMesh current.mesh) fixed later
      readings
  let observation := Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations.realize retainedMagnitude
    (current.edges.indexedEdges current.vertices
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.priorWalk (paired :=
    paired) included) newSheet)
  have cached := observation.bounded
  change Data.Gaussian.Norm.Basic.normSq observation.total ≤ observation.bound at cached
  rw [observation.total_readback, observation.bound_readback,
    Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations.BoundSpecification] at cached
  change Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values)
    (current.edges.indexedEdges current.vertices
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.priorWalk (paired :=
    paired) included) newSheet)) ≤
    ((current.edges.indexedEdges current.vertices
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.priorWalk (paired :=
      paired) included) newSheet).length : Fraction.Rational) ^ 2 * (4 * fixed.bound) at cached
  rw [current.edges.indexedEdges_length] at cached
  exact cached
/-- The common original polarized reference weight is nonnegative. -/
private theorem weight_nonnegative (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank
  domains firstDifferential)
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains secondDifferential) :
    0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.canonicalWeight
      (paired := paired) included first second :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    ((Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateReference.PolarizedReferenceRequest.prefixBound_nonnegative
      included first).trans (Fraction.Order.Basic.le_max_left _ _))

variable {included}
  {first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains firstDifferential} {second :
    Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains secondDifferential}
  {newSheet : Fin 2} {error : Fraction.Rational}
open Purelib.Topology.Surface.Sewing.SewingRetraction in
/-- The extracted reference correction is the exact paired area of the retained prefix and two-sheet reference word
values. -/
private theorem correction_readback
    (first second : Topology.Polygon.Stokes.OrientedEdge current.vertices.count → Gaussian.Basic.Canonical) :
    let priorWord := current.edges.indexedEdges current.vertices
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.priorWalk (paired :=
      paired) included) newSheet
    let outward := current.edges.indexedEdges current.vertices
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.referenceWalk (paired
      := paired) included) newSheet
    let returning := current.edges.indexedEdges current.vertices
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.referenceWalk (paired
      := paired) included)
      (Hyperelliptic.Branches.BranchCutLifts.otherSheet newSheet)
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitReferenceCorrection (paired := paired)
      included
      current.edges current.vertices newSheet
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient))
        =
      Topology.Polygon.Stokes.edgeArea
        (⟨wordValue first priorWord, wordValue second priorWord⟩ : Topology.Polygon.Stokes.PrimitivePoint)
        (⟨wordValue first outward + wordValue first returning,
          wordValue second outward + wordValue second returning⟩ : Topology.Polygon.Stokes.PrimitivePoint) := by
  intro priorWord outward returning
  refine (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_congr (fun coefficient
    => ?_)).trans
    (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_area (wordValue first
      priorWord)
      (wordValue first outward + wordValue first returning) (wordValue second priorWord)
      (wordValue second outward + wordValue second returning))
  unfold Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitReferenceCorrection
  rw [← bank.resplit_pairs_value included current.edges current.vertices]
  rw [Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.word_mix,
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.word_mix,
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.word_mix, Gaussian.Basic.conj_add]
  congr 1
  dsimp only [outward, returning,
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.referenceWalk]
  ring1

/-- Every later common sample satisfies the requested polarized reference
bound; no smallness assumption on the A-prefix or exterior term is supplied. -/
theorem conjugate_accurate (request :
  Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest (paired := paired) included
  first second newSheet error)
    {stage : Nat} {leftShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      firstDifferential stage domains}
    {rightShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank secondDifferential stage
      domains}
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftShared
      current.mesh) (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
      rightShared current.mesh)
    (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitReferenceCorrection (paired := paired)
      included
      current.edges current.vertices newSheet
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix (fun edge =>
        Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh
        leftReadings.values edge))
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
          coefficient))) ≤ error := open Purelib.Approximation in by
  rw [Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateReference.PolarizedReferenceRequest.correction_readback,
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateReference.PolarizedReferenceRequest.word_conj,
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateReference.PolarizedReferenceRequest.word_conj,
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateReference.PolarizedReferenceRequest.word_conj]
  have fixedLater := (Nat.Order.le_max_left _ _).trans later
  have requestsLater := (Nat.Order.le_max_right _ _).trans later
  have leftBound :=
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateReference.PolarizedReferenceRequest.prefix_bounded (paired :=
    paired) included first leftReadings ((Nat.Order.le_max_left _ _).trans fixedLater) newSheet
  have rightBound :=
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateReference.PolarizedReferenceRequest.prefix_bounded (paired :=
    paired) included second rightReadings ((Nat.Order.le_max_right _ _).trans fixedLater) newSheet
  have leftSmall := request.left.accurate leftReadings ((Nat.Order.le_max_left _ _).trans requestsLater)
  have rightSmall := request.right.accurate rightReadings ((Nat.Order.le_max_right _ _).trans requestsLater)
  have canonicalBound {point : Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : Data.Gaussian.Norm.Basic.normSq point ≤ limit) :
      Gaussian.Basic.Canonical.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    exact h
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  have estimate := Readings.PrimitiveAreaBounds.PrimitivePoint.area_bound
    (first := (⟨_, _⟩ : Topology.Polygon.Stokes.PrimitivePoint)) (last := (⟨_, _⟩ :
      Topology.Polygon.Stokes.PrimitivePoint))
    ⟨canonicalBound (((Gaussian.Norm.Basic.normSq_conj _).trans_le leftBound).trans (Fraction.Order.Basic.le_max_left
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.prefixBound (paired :=
      paired) included first)
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.prefixBound (paired :=
      paired) included second))),
      canonicalBound (rightBound.trans (Fraction.Order.Basic.le_max_right
        (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.prefixBound (paired
        := paired) included first)
        (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.prefixBound (paired
        := paired) included second)))⟩ ⟨canonicalBound (conjugate_sum_bound leftSmall), canonicalBound rightSmall⟩
  refine estimate.trans ?_
  change Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.canonicalWeight
    (paired := paired) included first second * Rational.Budget.Weighted.allowance error request.weight ≤ error
  rw [← request.weight_eq]
  exact Rational.Budget.Weighted.mul_allowance_le request.positive.le
    (request.weight_eq ▸
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateReference.PolarizedReferenceRequest.weight_nonnegative
      included first second)

/-- Remove the reference part after polarization, retaining the exterior
correction for both degree parities on these same face readings. -/
theorem conjugate_end_accurate (request :
  Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest (paired := paired) included
  first second newSheet error)
    {stage : Nat} {leftShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      firstDifferential stage domains}
    {rightShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank secondDifferential stage
      domains}
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftShared
      current.mesh) (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
      rightShared current.mesh)
    (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitEndCorrection (paired := paired) included
      current.edges current.vertices newSheet
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix (fun edge =>
        Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh
        leftReadings.values edge))
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
          coefficient)) -
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitExteriorCorrection (paired := paired)
        included
        current.edges current.vertices newSheet
          (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix (fun edge =>
          Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
          current.mesh leftReadings.values edge))
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
          coefficient))) ≤ error := by
  have split := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_congr (fun
    coefficient =>
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitEndCorrection_split (paired := paired)
      included current.edges current.vertices newSheet
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix (fun edge =>
        Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh
        leftReadings.values edge))
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
          coefficient))
  have read : Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient
    => Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitEndCorrection (paired := paired) included
      current.edges current.vertices newSheet
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix (fun edge =>
        Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh
        leftReadings.values edge))
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
          coefficient)) -
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitExteriorCorrection (paired := paired)
        included
        current.edges current.vertices newSheet
          (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix (fun edge =>
          Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
          current.mesh leftReadings.values edge))
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
          coefficient)) =
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitReferenceCorrection (paired := paired)
        included
        current.edges current.vertices newSheet
          (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix (fun edge =>
          Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
          current.mesh leftReadings.values edge))
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
          coefficient)) := by
    rw [split]
    unfold Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract
    ring1
  rw [read]
  exact Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateReference.PolarizedReferenceRequest.conjugate_accurate
    request leftReadings rightReadings later

end PolarizedReferenceRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateReference
