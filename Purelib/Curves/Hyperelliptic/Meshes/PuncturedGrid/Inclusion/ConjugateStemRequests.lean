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

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearStemArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearStemRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugatePolygonRequests
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemRequests

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugatePolygonRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearStemRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

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

/-! The conjugate based excursion retains its two stem defects and pays
them with the original polygon and total-increment requests. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateStemRequests

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearStemRequests (BilinearStemRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearStemRequests.BilinearStemRequest (stem)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests (BilinearHoleRequest)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded area_bound)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue wordValue_append)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation edgeValuation_reverse
  orderedRoute orderedRoute_value)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_neg)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base next : FramedPuncturedGrid curve branches
    higher}
  {lifted : LiftedPuncturedGrid base} {current : LiftedPuncturedGrid next}
    {bank : BasedBranchBank
    lifted}
  {included : Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion base.bank.grid next.bank.grid}
  {domains : FaceDomainBank current.frames
    next.faces.regulars} {leftDifferential rightDifferential :
    Differential genus}

namespace BilinearStemRequest

/-- Conjugating every Gaussian edge value conjugates the complete finite word value. -/
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

/-- A retained indexed walk value satisfies the squared edge-count magnitude bound at a paid face stage. -/
private theorem word_bound {differential : Differentials.Basic.Differential genus} (fixed :
  MagnitudeBank.FaceMagnitudeBank domains differential)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
    (later : fixed.index ≤ stage) {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk next.bank.grid start
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
/-- The shared stem-and-boundary magnitude allowance is nonnegative. -/
private theorem magnitude_nonnegative (leftFixed : MagnitudeBank.FaceMagnitudeBank domains leftDifferential)
    (rightFixed : MagnitudeBank.FaceMagnitudeBank domains rightDifferential) (branch : BranchIsolation.Data.Index
      branches) :
    0 ≤ (((BilinearStemRequest.stem bank included branch).append (BilinearHoleRequest.boundary bank included
      branch)).edgeCount : Fraction.Rational)^2 *
      (4 * max leftFixed.bound rightFixed.bound) :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.pow_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (leftFixed.nonnegative.trans
      (Fraction.Order.Basic.le_max_left _ _)))

variable {leftFixed : FaceMagnitudeBank domains
  leftDifferential} {rightFixed : FaceMagnitudeBank
  domains rightDifferential}
  {branch : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {sheet : Fin 2} {error :
    Rational}
/-- The requested bound concerns the based-excursion/lap difference, with the lap starting at the actual sheet reached
by the outward stem. -/
theorem conjugate_accurate (request : BilinearStemRequests.BilinearStemRequest bank included leftFixed rightFixed branch
  sheet error)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh) (rightReadings :
      TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh)
    (later : request.index ≤ stage) :
    let value := fun edge => (⟨Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh
      leftReadings.values edge),
      CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩ : Stokes.PrimitivePoint)
    let arrival := RootEdgeBank.target current.edges (BilinearStemRequest.stem bank included branch) sheet
    let loop := current.edges.indexedEdges current.vertices
      (included.resplit (bank.rows.get branch).reference.walk (FramedBranchCellBank.baseMember base.bank)) sheet
    let boundary := current.edges.indexedEdges current.vertices (BilinearHoleRequest.boundary bank included branch)
      arrival
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (loop.map value) - PairedIncrementArea.area
      (boundary.map value)) ≤ error := by
  intro value arrival loop boundary
  have polygonLater := (Nat.Order.le_max_left _ _).trans later
  have totalLater := (Nat.Order.le_max_right _ _).trans later
  have fixedLater := request.polygons.fixed_later polygonLater
  have leftTotal := request.leftTotal.accurate leftReadings ((Nat.Order.le_max_left _ _).trans totalLater)
  have rightTotal := request.rightTotal.accurate rightReadings ((Nat.Order.le_max_right _ _).trans totalLater)
  let outward := current.edges.indexedEdges current.vertices (BilinearStemRequest.stem bank included branch) sheet
  let other := current.edges.indexedEdges current.vertices (BilinearStemRequest.stem bank included branch)
    (BranchCutLifts.otherSheet sheet)
  let first := fun edge => Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh
    leftReadings.values edge)
  let second := CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values
  let multiplier : PrimitivePoint := ⟨wordValue first outward + SewingRetraction.wordValue first boundary,
    SewingRetraction.wordValue second outward + SewingRetraction.wordValue second boundary⟩
  let defect : PrimitivePoint := ⟨-(SewingRetraction.wordValue first outward + SewingRetraction.wordValue first other),
    -(SewingRetraction.wordValue second outward + SewingRetraction.wordValue second other)⟩
  have magnitudeNonnegative : 0 ≤ request.magnitude := request.magnitude_eq ▸
    magnitude_nonnegative
    leftFixed rightFixed branch
  have bounded : PrimitivePoint.Bounded multiplier request.magnitude := by
    have firstBound :=
      word_bound leftFixed
      leftReadings fixedLater.1
      ((BilinearStemRequest.stem bank included branch).append (BilinearHoleRequest.boundary bank included branch)) sheet
    have secondBound :=
      word_bound
      rightFixed rightReadings fixedLater.2
      ((BilinearStemRequest.stem bank included branch).append (BilinearHoleRequest.boundary bank included branch)) sheet
    rw [current.edges.indexedEdges_append, SewingRetraction.wordValue_append] at firstBound secondBound
    rw [request.magnitude_eq]
    constructor
    · rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      change Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue (fun edge =>
        Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values edge))
        outward +
        SewingRetraction.wordValue (fun edge => Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation
          current.mesh leftReadings.values edge)) boundary) ≤ _
      rw [word_conj,
        word_conj, ←
        Data.Gaussian.Basic.conj_add,
        Data.Gaussian.Norm.Basic.normSq_conj]
      exact firstBound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.le_max_left leftFixed.bound
          rightFixed.bound) (by decide))
        (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2))
    · rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact secondBound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.le_max_right leftFixed.bound
          rightFixed.bound) (by decide))
        (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2))
  have small : PrimitivePoint.Bounded defect request.totalTarget := by
    constructor
    · rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      change Data.Gaussian.Norm.Basic.normSq (-(SewingRetraction.wordValue (fun edge =>
        Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values edge))
        outward +
        SewingRetraction.wordValue (fun edge => Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation
          current.mesh leftReadings.values edge)) other)) ≤ _
      rw [Data.Gaussian.Norm.Basic.normSq_neg,
        word_conj,
        word_conj, ←
        Data.Gaussian.Basic.conj_add,
        Data.Gaussian.Norm.Basic.normSq_conj]
      exact leftTotal
    · rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact (Data.Gaussian.Norm.Basic.normSq_neg _).trans_le rightTotal
  have cross : Data.Gaussian.Norm.Basic.normSq (Stokes.edgeArea multiplier defect) ≤ error / 4 := by
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    apply (PrimitivePoint.area_bound bounded small).trans
    rw [request.totalTarget_eq]
    exact Weighted.mul_allowance_le
      (Fraction.Order.Field.div_pos_direct request.positive (by decide : (0 : Fraction.Rational) < 4)).le
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) magnitudeNonnegative)
  have different : sheet ≠ BranchCutLifts.otherSheet sheet :=
    (by decide +kernel : ∀ sheet : Fin 2, sheet ≠ BranchCutLifts.otherSheet sheet) sheet
  have opposite := PolygonRequest.conjugate_accurate request.polygons leftReadings rightReadings polygonLater different
  have identity := BilinearStemArea.resplit_paired_loop_area bank included current.edges current.vertices
    (fun point member => (BranchCellBank.referenceAt next.bank.toBranchCellBank point member).toLoop) branch sheet first
      second
    (by
      intro edge
      change Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values
        edge.reverse) =
        -Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values edge)
      rw [CanonicalEdgeValues.edgeValuation_reverse]
      rfl) (CanonicalEdgeValues.edgeValuation_reverse current.mesh rightReadings.values)
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

end BilinearStemRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateStemRequests
