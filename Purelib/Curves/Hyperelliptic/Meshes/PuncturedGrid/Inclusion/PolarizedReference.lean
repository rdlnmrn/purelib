module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ReferenceAreaRequest
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Riemann

open Purelib

public section

/-! Requested decay of the polarized reference correction on one refined
bank. The even-degree exterior correction is not removed by this request. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference

open Purelib.Data.Rat.Fraction (Rational)

open Purelib.Data.Gaussian.Basic (Canonical)

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

/-- The original paired-prefix walk resplit through the retained coordinate inclusion. -/
@[expose] def priorWalk := included.resplit
  (bank.loopProduct (paired.split.pairs.flatMap (fun pair => [pair.1, pair.2])))
    (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)

/-- The original terminal reference walk resplit through the retained coordinate inclusion. -/
@[expose] def referenceWalk := included.resplit
  (bank.rows.get paired.split.ending.reference).reference.walk
    (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)

/-- The squared original paired-prefix length times its retained fourfold edge magnitude bound. -/
@[expose] def prefixBound (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  firstDifferential) : Fraction.Rational :=
  (((Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.priorWalk (paired :=
    paired) included).edgeCount : Fraction.Rational)^2 * (4 * fixed.bound))

/-- The original paired-prefix magnitude bound is nonnegative. -/
private theorem prefixBound_nonnegative (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank
  domains firstDifferential) :
    0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.prefixBound (paired :=
      paired) included fixed :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.pow_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) fixed.nonnegative)

open Purelib.Topology.Surface.Sewing.SewingRetraction in
/-- The cached value of the original paired-prefix walk satisfies its retained magnitude bound. -/
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

/-- Both component errors use the same positive allowance, which pays the
larger of the two retained prefix bounds. -/
@[expose] def canonicalWeight (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  firstDifferential)
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains secondDifferential) :
      Fraction.Rational :=
  4 * max (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.prefixBound (paired
    := paired) included first)
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.prefixBound (paired :=
    paired) included second)

/-- The common polarized reference weight is nonnegative. -/
theorem weight_nonnegative (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  firstDifferential)
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains secondDifferential) :
    0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.canonicalWeight
      (paired := paired) included first second :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    ((Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.prefixBound_nonnegative
      included first).trans (Fraction.Order.Basic.le_max_left _ _))

end PolarizedReferenceRequest

set_option genInjectivity false in
/-- A paid polarized correction for the actual terminal reference walk.

Both increment requests retain the same original paired occurrences and use a common allowance derived from the two
prefix bounds. -/
structure PolarizedReferenceRequest
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains firstDifferential) (second
      : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains secondDifferential)
    (newSheet : Fin 2) (error : Fraction.Rational) where
  /-- The requested reference correction target is positive. -/ positive : 0 < error
  /-- The cached common paired-prefix weight. -/ weight : Fraction.Rational
  /-- The cached weight is the canonical weight of the two retained magnitude banks. -/ weight_eq : weight =
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.canonicalWeight (paired :=
    paired) included first second
  /-- The actual paired occurrences of the original terminal reference walk. -/ reference :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk current.mesh
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.referenceWalk (paired :=
    paired) included)
  /-- The first differential increment request on the retained reference occurrences. -/ left :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk.IncrementRequest
    reference domains firstDifferential newSheet (Rational.Budget.Weighted.allowance error weight)
  /-- The second differential increment request on the retained reference occurrences. -/ right :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk.IncrementRequest
    reference domains secondDifferential newSheet (Rational.Budget.Weighted.allowance error weight)

constructive_injectivity PolarizedReferenceRequest

namespace PolarizedReferenceRequest

variable {included}
  {first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains firstDifferential} {second :
    Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains secondDifferential}
  {newSheet : Fin 2} {error : Fraction.Rational}

/-- Prepare both differential increment requests on the same original terminal reference occurrences. -/
@[expose] def build (included : Geometry.Grid.Extension.CoordinateInclusion base.bank.grid next.bank.grid)
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains firstDifferential) (second
      : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains secondDifferential)
    (newSheet : Fin 2) (error : Fraction.Rational) (positive : 0 < error) :
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest (paired := paired)
      included first second newSheet error :=
  let weight :=
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.canonicalWeight (paired :=
    paired) included first second
  let reference := Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk.build current.mesh
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.referenceWalk (paired :=
    paired) included)
  have allowancePositive := Rational.Budget.Weighted.allowance_positive positive
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.weight_nonnegative
      included first second)
  ⟨positive, weight, rfl, reference,

      Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk.IncrementRequest.build
      reference domains firstDifferential newSheet _ allowancePositive,

      Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk.IncrementRequest.build
      reference domains secondDifferential newSheet _ allowancePositive⟩

/-- The common threshold covering both magnitude banks and reference increment requests. -/
@[expose] def index (request : Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest
  (paired := paired) included first second newSheet error) : Nat :=
  max (max first.index second.index) (max request.left.index request.right.index)

open Purelib.Topology.Surface.Sewing.SewingRetraction in
/-- The extracted reference correction is exactly the paired area of the original prefix and two-sheet reference
readings. -/
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
theorem accurate (request : Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest
  (paired := paired) included first second newSheet error)
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
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
          coefficient))) ≤ error := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.correction_readback]
  have fixedLater := (Nat.Order.le_max_left _ _).trans later
  have requestsLater := (Nat.Order.le_max_right _ _).trans later
  have leftBound :=
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.prefix_bounded (paired :=
    paired) included first leftReadings ((Nat.Order.le_max_left _ _).trans fixedLater) newSheet
  have rightBound :=
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.prefix_bounded (paired :=
    paired) included second rightReadings ((Nat.Order.le_max_right _ _).trans fixedLater) newSheet
  have leftSmall := request.left.accurate leftReadings ((Nat.Order.le_max_left _ _).trans requestsLater)
  have rightSmall := request.right.accurate rightReadings ((Nat.Order.le_max_right _ _).trans requestsLater)
  have canonicalBound {point : Canonical} {limit : Rational}
      (h : Data.Gaussian.Norm.Basic.normSq point ≤ limit) :
      Canonical.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    exact h
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  have estimate := Readings.PrimitiveAreaBounds.PrimitivePoint.area_bound
    (first := (⟨_, _⟩ : Topology.Polygon.Stokes.PrimitivePoint)) (last := (⟨_, _⟩ :
      Topology.Polygon.Stokes.PrimitivePoint))
    ⟨canonicalBound (leftBound.trans (Fraction.Order.Basic.le_max_left
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.prefixBound (paired :=
      paired) included first)
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.prefixBound (paired :=
      paired) included second))),
      canonicalBound (rightBound.trans (Fraction.Order.Basic.le_max_right
        (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.prefixBound (paired
        := paired) included first)
        (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.prefixBound (paired
        := paired) included second)))⟩
    ⟨canonicalBound leftSmall, canonicalBound rightSmall⟩
  refine estimate.trans ?_
  change Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.canonicalWeight
    (paired := paired) included first second * Rational.Budget.Weighted.allowance error request.weight ≤ error
  rw [← request.weight_eq]
  exact Rational.Budget.Weighted.mul_allowance_le request.positive.le
    (request.weight_eq ▸
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest.weight_nonnegative
      included first second)

/-- Remove the reference part after polarization, retaining the exterior
correction for both degree parities on these same face readings. -/
theorem end_accurate (request :
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
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
          coefficient)) -
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitExteriorCorrection (paired := paired)
        included
        current.edges current.vertices newSheet
          (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
          (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
          coefficient))) ≤ error := by
  have split := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_congr (fun
    coefficient =>
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitEndCorrection_split (paired := paired)
      included current.edges current.vertices newSheet
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
          coefficient))
  have read : Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient
    => Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitEndCorrection (paired := paired) included
      current.edges current.vertices newSheet
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
          coefficient)) -
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitExteriorCorrection (paired := paired)
        included
        current.edges current.vertices newSheet
          (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
          (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
          coefficient)) =
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitReferenceCorrection (paired := paired)
        included
        current.edges current.vertices newSheet
          (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
          (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
          coefficient)) := by
    rw [split]
    unfold Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract
    ring1
  rw [read]
  exact request.accurate leftReadings rightReadings later

end PolarizedReferenceRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference
