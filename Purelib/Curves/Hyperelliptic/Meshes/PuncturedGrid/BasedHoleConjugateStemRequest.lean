module
import Purelib.Data.Nat.Order
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedHoleArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedHoleStemRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugatePolygonRequests
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugatePolygonRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

public section

/-! The existing fine-hole stem request also controls the conjugate pairing. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedHoleConjugateStemRequest

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences (PairedWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedHoleStemRequest (PairedStemRequest)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded area_bound)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue wordValue_append)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation edgeValuation_reverse
  orderedRoute orderedRoute_value)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_neg)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {current : LiftedPuncturedGrid base}
  {domains : FaceDomainBank current.frames
    base.faces.regulars} {leftDifferential rightDifferential :
    Differential genus}
  {hole : BranchHole base.bank.toBranchCellBank} {start :
    Canonical}
  {stem : Purelib.Polynomial.Geometry.Grid.Walks.Walk base.bank.grid start hole.cell.box.anchor}

namespace PairedStemRequest

/-- The actual indexed walk value obeys the paid face magnitude bound scaled by its squared edge count. -/
private theorem word_bound {differential : Differentials.Basic.Differential genus} (fixed :
  MagnitudeBank.FaceMagnitudeBank domains differential)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
    (later : fixed.index ≤ stage) {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk base.bank.grid start
      finish) (sheet : Fin 2) :
    Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation current.mesh
      readings.values) (current.edges.indexedEdges current.vertices walk sheet)) ≤
      (walk.edgeCount : Fraction.Rational)^2 * (4 * fixed.bound) := by
  let retainedMagnitude := Readings.EdgeMagnitude.ofBank
    (owner := SourceChartComparison.ownerFromMesh current.mesh) fixed later readings
  let observation := WordObservations.realize retainedMagnitude (current.edges.indexedEdges current.vertices walk sheet)
  have cached := observation.bounded
  change Data.Gaussian.Norm.Basic.normSq observation.total ≤ observation.bound at cached
  rw [observation.total_readback, observation.bound_readback, WordObservations.BoundSpecification] at cached
  change Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation
    current.mesh readings.values) (current.edges.indexedEdges current.vertices walk sheet)) ≤
    ((current.edges.indexedEdges current.vertices walk sheet).length : Fraction.Rational) ^ 2 * (4 * fixed.bound)
      at cached
  rw [current.edges.indexedEdges_length] at cached
  exact cached
/-- The common two-differential stem-and-hole magnitude ceiling is nonnegative. -/
private theorem magnitude_nonnegative (leftFixed : MagnitudeBank.FaceMagnitudeBank domains leftDifferential)
    (rightFixed : MagnitudeBank.FaceMagnitudeBank domains rightDifferential) :
    0 ≤ ((stem.append hole.boundary).edgeCount : Fraction.Rational)^2 *
      (4 * max leftFixed.bound rightFixed.bound) :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.pow_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (leftFixed.nonnegative.trans
      (Fraction.Order.Basic.le_max_left _ _)))

/-- Evaluating an ordered edge word after conjugation equals conjugating its actual word value. -/
private theorem word_conj {count : Nat} (value : Stokes.OrientedEdge count → Data.Gaussian.Basic.Canonical)
    (word : List (Stokes.OrientedEdge count)) :
    SewingRetraction.wordValue (fun edge => Data.Gaussian.Basic.conj (value edge)) word =
      Data.Gaussian.Basic.conj (SewingRetraction.wordValue value word) := by
  induction word with
  | nil => rfl
  | cons edge rest ih =>
    change Data.Gaussian.Basic.conj (value edge) + SewingRetraction.wordValue _ rest =
      Data.Gaussian.Basic.conj (value edge + SewingRetraction.wordValue value rest)
    rw [ih, Data.Gaussian.Basic.conj_add]

variable {leftFixed : FaceMagnitudeBank domains
  leftDifferential} {rightFixed : FaceMagnitudeBank
  domains rightDifferential}
  {sheet : Fin 2} {error : Rational}
variable (member : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid start)
include member

/-- The requested bound concerns the based-excursion/lap difference, with the lap starting at the actual sheet reached
by the outward stem. -/
theorem conjugate_accurate (request : BasedHoleStemRequest.PairedStemRequest hole stem leftFixed rightFixed sheet error)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh) (rightReadings :
      TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh)
    (later : request.index ≤ stage) :
    let value := fun edge => (⟨Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh
      leftReadings.values edge),
      CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩ : Stokes.PrimitivePoint)
    let arrival := RootEdgeBank.target current.edges stem sheet
    let loop := current.edges.indexedEdges current.vertices
      (stem.based hole.boundary) sheet
    let boundary := current.edges.indexedEdges current.vertices hole.boundary arrival
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (loop.map value) - PairedIncrementArea.area
      (boundary.map value)) ≤ error := by
  intro value arrival loop boundary
  have polygonLater := (Nat.Order.le_max_left _ _).trans later
  have totalLater := (Nat.Order.le_max_right _ _).trans later
  have fixedLater := request.polygons.fixed_later polygonLater
  have leftTotal := request.leftTotal.accurate leftReadings ((Nat.Order.le_max_left _ _).trans totalLater)
  have rightTotal := request.rightTotal.accurate rightReadings ((Nat.Order.le_max_right _ _).trans totalLater)
  let outward := current.edges.indexedEdges current.vertices stem sheet
  let other := current.edges.indexedEdges current.vertices stem (BranchCutLifts.otherSheet sheet)
  let first := fun edge => Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh
    leftReadings.values edge)
  let second := CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values
  let multiplier : PrimitivePoint := ⟨wordValue first outward + SewingRetraction.wordValue first boundary,
    SewingRetraction.wordValue second outward + SewingRetraction.wordValue second boundary⟩
  let defect : PrimitivePoint := ⟨-(SewingRetraction.wordValue first outward + SewingRetraction.wordValue first other),
    -(SewingRetraction.wordValue second outward + SewingRetraction.wordValue second other)⟩
  have magnitudeNonnegative : 0 ≤ request.magnitude := request.magnitude_eq ▸
    magnitude_nonnegative
    (stem := stem) leftFixed rightFixed
  have bounded : PrimitivePoint.Bounded multiplier request.magnitude := by
    have firstBound :=
      word_bound leftFixed
      leftReadings fixedLater.1
      (stem.append hole.boundary) sheet
    have secondBound :=
      word_bound rightFixed
      rightReadings fixedLater.2
      (stem.append hole.boundary) sheet
    rw [current.edges.indexedEdges_append, SewingRetraction.wordValue_append] at firstBound secondBound
    rw [request.magnitude_eq]
    constructor
    · change Data.Gaussian.Basic.Canonical.normSq (SewingRetraction.wordValue first outward + SewingRetraction.wordValue
        first boundary) ≤ _
      dsimp only [first]
      rw [word_conj,
        word_conj, ←
        Data.Gaussian.Basic.conj_add]
      have h := (Data.Gaussian.Norm.Basic.normSq_conj _).trans_le
        (firstBound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.le_max_left leftFixed.bound
            rightFixed.bound) (by decide))
          (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2)))
      change Fraction.Order.Basic.LessEqual _ _ at h ⊢
      simpa only [-eq_self, -iff_self, Data.Gaussian.Norm.Basic.normSq_eq_canonical] using h
    · have h := secondBound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.le_max_right leftFixed.bound
          rightFixed.bound) (by decide))
        (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2))
      change Fraction.Order.Basic.LessEqual _ _ at h ⊢
      simp only [-eq_self, -iff_self, Data.Gaussian.Norm.Basic.normSq_eq_canonical] at h
      convert h using 1
  have oldBound {point : Data.Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : Data.Gaussian.Basic.Canonical.normSq point ≤ limit) :
      Data.Gaussian.Norm.Basic.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    simpa only [-eq_self, -iff_self, Data.Gaussian.Norm.Basic.normSq_eq_canonical] using h
  have canonicalBound {point : Data.Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : Data.Gaussian.Norm.Basic.normSq point ≤ limit) :
      Data.Gaussian.Basic.Canonical.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    simpa only [-eq_self, -iff_self, Data.Gaussian.Norm.Basic.normSq_eq_canonical] using h
  have small : PrimitivePoint.Bounded defect request.totalTarget := by
    constructor
    · change Data.Gaussian.Basic.Canonical.normSq (-(SewingRetraction.wordValue first outward +
        SewingRetraction.wordValue first other)) ≤ _
      dsimp only [first]
      rw [word_conj,
        word_conj, ←
        Data.Gaussian.Basic.conj_add,
        Data.Gaussian.Basic.Canonical.normSq_neg]
      exact canonicalBound ((Data.Gaussian.Norm.Basic.normSq_conj _).trans_le leftTotal)
    · exact canonicalBound ((Data.Gaussian.Norm.Basic.normSq_neg _).trans_le rightTotal)
  have cross : Data.Gaussian.Norm.Basic.normSq (Stokes.edgeArea multiplier defect) ≤ error / 4 := by
    apply oldBound
    apply (PrimitivePoint.area_bound bounded small).trans
    rw [request.totalTarget_eq]
    exact Weighted.mul_allowance_le
      (Fraction.Order.Field.div_pos_direct request.positive (by decide : (0 : Fraction.Rational) < 4)).le
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) magnitudeNonnegative)
  have different : sheet ≠ BranchCutLifts.otherSheet sheet :=
    (by decide +kernel : ∀ sheet : Fin 2, sheet ≠ BranchCutLifts.otherSheet sheet) sheet
  have opposite := PolygonRequest.conjugate_accurate request.polygons leftReadings rightReadings polygonLater different
  have identity := BasedHoleArea.based_paired_area current.edges current.vertices hole member stem sheet first second
    (fun edge => by dsimp only [first]; rw [CanonicalEdgeValues.edgeValuation_reverse]; rfl)
      (CanonicalEdgeValues.edgeValuation_reverse current.mesh rightReadings.values)
  change PairedIncrementArea.area (loop.map value) = PairedIncrementArea.area (boundary.map value) +
    (PairedIncrementArea.area (outward.map value) - PairedIncrementArea.area (other.map value)) +
      Stokes.edgeArea multiplier defect at identity
  rw [identity]
  rw [show PairedIncrementArea.area (boundary.map value) +
      (PairedIncrementArea.area (outward.map value) - PairedIncrementArea.area (other.map value)) +
      Stokes.edgeArea multiplier defect - PairedIncrementArea.area (boundary.map value) =
    (PairedIncrementArea.area (outward.map value) - PairedIncrementArea.area (other.map value)) +
      Stokes.edgeArea multiplier defect by ring1]
  exact ((Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct opposite cross) (by decide))).trans_eq
      ((by ring1 : 2 * (error / 4 + error / 4) = error / 4 * 4).trans (Fraction.Field.div_mul_cancel_of_ne _ _ (by
        decide)))

end PairedStemRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedHoleConjugateStemRequest
