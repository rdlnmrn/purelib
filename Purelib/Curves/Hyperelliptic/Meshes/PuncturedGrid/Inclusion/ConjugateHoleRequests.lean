module
import Purelib.Data.Nat.Order
import Purelib.Data.List.Map
import Purelib.Data.Fin
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests
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
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugatePolygonRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing

public section

/-! The doubled original branch contour is compared to twice either
conjugate lap, retaining and paying the cross of the two lap totals. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateHoleRequests

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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests (BilinearHoleRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests.BilinearHoleRequest (boundary)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded area_bound)
open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint edgeArea)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation orderedRoute
  orderedRoute_value)
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

namespace BilinearHoleRequest

/-- The paired edge-word total reads the conjugated first differential word value and the unchanged second word value.
-/
private theorem total_readback {count : Nat} (first second : Stokes.OrientedEdge count → Data.Gaussian.Basic.Canonical)
  (word : List (Stokes.OrientedEdge count)) :
    PairedIncrementArea.total (word.map (fun edge => (⟨Data.Gaussian.Basic.conj (first edge), second edge⟩ :
      Stokes.PrimitivePoint))) =
      ⟨Data.Gaussian.Basic.conj (SewingRetraction.wordValue first word), SewingRetraction.wordValue second
        word⟩ := by
  induction word with
  | nil => rfl
  | cons edge rest ih =>
      change (⟨Data.Gaussian.Basic.conj (first edge), second edge⟩ : Stokes.PrimitivePoint).add
        (PairedIncrementArea.total (rest.map _)) = _
      rw [ih]
      apply congrArg₂ PrimitivePoint.mk
      · exact (Data.Gaussian.Basic.conj_add _ _).symm
      · rfl

/-- The actual indexed walk value obeys the paid face magnitude bound scaled by its squared edge count. -/
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
/-- The retained two-differential resplit boundary magnitude ceiling is nonnegative. -/
private theorem magnitude_nonnegative (leftFixed : MagnitudeBank.FaceMagnitudeBank domains leftDifferential)
    (rightFixed : MagnitudeBank.FaceMagnitudeBank domains rightDifferential) (branch : BranchIsolation.Data.Index
      branches) :
    0 ≤ ((BilinearHoleRequest.boundary bank included branch).edgeCount : Fraction.Rational)^2 * (4 * max leftFixed.bound
      rightFixed.bound) :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.pow_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (leftFixed.nonnegative.trans
      (Fraction.Order.Basic.le_max_left _ _)))

variable {leftFixed : FaceMagnitudeBank domains
  leftDifferential} {rightFixed : FaceMagnitudeBank
  domains rightDifferential}
  {branch : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {error :
    Rational}
section

/-- Two sheets have a positive literal finite bound. -/
local instance : NeZero (2 : Nat) := ⟨by decide +kernel⟩

/-- Twice either lap approximates the actual doubled contour. The two-sheet total pays its cross term; no zero-area
assertion is used. -/
theorem conjugate_accurate (request : BilinearHoleRequests.BilinearHoleRequest bank included leftFixed rightFixed branch
  error)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh) (rightReadings :
      TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh)
    (later : request.index ≤ stage) (sheet : Fin 2) :
    let value := fun edge => (⟨Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh
      leftReadings.values edge),
      CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩ : Stokes.PrimitivePoint)
    let walk := BilinearHoleRequest.boundary bank included branch
    let lap := PairedIncrementArea.area ((current.edges.indexedEdges current.vertices walk sheet).map value)
    Data.Gaussian.Norm.Basic.normSq (lap + lap - PairedIncrementArea.area
      ((current.edges.indexedEdges current.vertices (walk.append walk) 0).map value)) ≤ error := by
  intro value walk lap
  have polygonLater := (Nat.Order.le_max_left _ _).trans later
  have totalLater := (Nat.Order.le_max_right _ _).trans later
  have fixedLater := request.polygons.fixed_later polygonLater
  have leftTotal := request.leftTotal.accurate leftReadings ((Nat.Order.le_max_left _ _).trans totalLater)
  have rightTotal := request.rightTotal.accurate rightReadings ((Nat.Order.le_max_right _ _).trans totalLater)
  let words := fun sheet => current.edges.indexedEdges current.vertices walk sheet
  let totals := fun sheet => PairedIncrementArea.total ((words sheet).map value)
  let areas := fun sheet => PairedIncrementArea.area ((words sheet).map value)
  have magnitudeNonnegative : 0 ≤ request.magnitude := request.magnitude_eq ▸
    magnitude_nonnegative
    leftFixed rightFixed branch
  have bounded : PrimitivePoint.Bounded (totals 0) request.magnitude := by
    dsimp only [totals, value]
    rw [total_readback,
      request.magnitude_eq]
    constructor
    · rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical,
        Data.Gaussian.Norm.Basic.normSq_conj]
      exact (word_bound
        leftFixed leftReadings fixedLater.1 walk 0).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.le_max_left leftFixed.bound
            rightFixed.bound) (by decide))
          (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2))
    · rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact (word_bound
        rightFixed rightReadings fixedLater.2 walk 0).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.le_max_right leftFixed.bound
            rightFixed.bound) (by decide))
          (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2))
  have small : PrimitivePoint.Bounded ((totals 0).add (totals 1)) request.totalTarget := by
    dsimp only [totals, value]
    rw [total_readback,
      total_readback]
    constructor
    · rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      change Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Basic.conj _ +
        Data.Gaussian.Basic.conj _) ≤ _
      rw [← Data.Gaussian.Basic.conj_add, Data.Gaussian.Norm.Basic.normSq_conj]
      exact leftTotal
    · rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact rightTotal
  have cross : Data.Gaussian.Norm.Basic.normSq (Stokes.edgeArea (totals 0) (totals 1)) ≤ error / 4 := by
    have same : Stokes.edgeArea (totals 0) (totals 1) = Stokes.edgeArea (totals 0) ((totals 0).add (totals 1)) := by
      simp only [-eq_self, -iff_self, Stokes.edgeArea, PrimitivePoint.add]
      ring1
    rw [same]
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    apply (PrimitivePoint.area_bound bounded small).trans
    rw [request.totalTarget_eq]
    exact Weighted.mul_allowance_le
      (Fraction.Order.Field.div_pos_direct request.positive (by decide : (0 : Fraction.Rational) < 4)).le
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) magnitudeNonnegative)
  have opposite := PolygonRequest.conjugate_accurate request.polygons leftReadings rightReadings polygonLater (by
    decide)
  have either : ∀ sheet : Fin 2, Data.Gaussian.Norm.Basic.normSq (areas sheet + areas sheet - (areas 0 + areas
    1)) ≤ error / 4 := by
    intro position
    refine Fin.cases_induction ?_ (fun next => ?_) position
    · change Data.Gaussian.Norm.Basic.normSq (areas 0 + areas 0 - (areas 0 + areas 1)) ≤ error / 4
      rw [show areas 0 + areas 0 - (areas 0 + areas 1) = areas 0 - areas 1 by ring1]
      exact opposite
    · refine Fin.cases_induction ?_ (fun empty => Fin.elim0 empty) next
      change Data.Gaussian.Norm.Basic.normSq (areas 1 + areas 1 - (areas 0 + areas 1)) ≤ error / 4
      rw [show areas 1 + areas 1 - (areas 0 + areas 1) = -(areas 0 - areas 1) by ring1,
        Data.Gaussian.Norm.Basic.normSq_neg]
      exact opposite
  have double : current.edges.indexedEdges current.vertices (walk.append walk) 0 = words 0 ++ words 1 :=
    HoleRequests.resplit_hole_double_indexed bank included branch
  rw [double, List.Map.map_append, PairedAreaBlocks.area_append]
  change Data.Gaussian.Norm.Basic.normSq (areas sheet + areas sheet - (areas 0 + areas 1 + Stokes.edgeArea
    (totals 0) (totals 1))) ≤ error
  rw [show areas sheet + areas sheet - (areas 0 + areas 1 + Stokes.edgeArea (totals 0) (totals 1)) =
    (areas sheet + areas sheet - (areas 0 + areas 1)) - Stokes.edgeArea (totals 0) (totals 1) by ring1]
  exact ((Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct (either sheet) cross) (by decide))).trans_eq
      ((by ring1 : 2 * (error / 4 + error / 4) = error / 4 * 4).trans (Fraction.Field.div_mul_cancel_of_ne _ _ (by
        decide)))

end

end BilinearHoleRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateHoleRequests
