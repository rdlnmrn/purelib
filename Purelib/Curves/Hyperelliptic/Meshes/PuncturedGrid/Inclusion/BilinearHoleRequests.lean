module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Map
import Purelib.Data.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PolygonRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleRequests
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

public section

/-! The paired area of the doubled original branch-cell contour. The cross
term of the two lap totals is paid using both differential increment requests. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests

open Purelib.Data
open Purelib.Data.Rat

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PolygonRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude

open Purelib.Integration.Path

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing

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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences (PairedWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PolygonRequests (PolygonRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk
  (IncrementRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleRequests (resplit_hole_double_indexed)
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

/-- The original branch-cell boundary resplit on the retained enlarged grid. -/
@[expose] def boundary (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (included : Extension.CoordinateInclusion
  base.bank.grid next.bank.grid)
    (branch : BranchIsolation.Data.Index branches) :=
  included.resplit (bank.rows.get branch).boundary ((base.bank.cell branch).anchor_mem (base.bank.cell_mem branch))

/-- The paired edge-word total reads the actual word value of each differential. -/
private theorem total_readback {count : Nat} (first second : Stokes.OrientedEdge count → Data.Gaussian.Basic.Canonical)
  (word : List (Stokes.OrientedEdge count)) :
    PairedIncrementArea.total (word.map (fun edge => (⟨first edge, second edge⟩ : Stokes.PrimitivePoint))) =
      ⟨wordValue first word, SewingRetraction.wordValue second word⟩ := by
  induction word with
  | nil => rfl
  | cons edge rest ih =>
      change (⟨first edge, second edge⟩ : Stokes.PrimitivePoint).add (PairedIncrementArea.total (rest.map _)) = _
      rw [ih]
      rfl

/-- The indexed walk value obeys the paid face magnitude bound scaled by its squared edge count. -/
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
/-- The two-differential resplit boundary magnitude ceiling is nonnegative. -/
theorem magnitude_nonnegative (leftFixed : MagnitudeBank.FaceMagnitudeBank domains leftDifferential)
    (rightFixed : MagnitudeBank.FaceMagnitudeBank domains rightDifferential) (branch : BranchIsolation.Data.Index
      branches) :
    0 ≤ ((boundary bank
      included branch).edgeCount : Fraction.Rational)^2 * (4 * max leftFixed.bound rightFixed.bound) :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.pow_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (leftFixed.nonnegative.trans
      (Fraction.Order.Basic.le_max_left _ _)))

end BilinearHoleRequest

set_option genInjectivity false in
/-- A paid paired-area comparison of twice either original-cell lap with its actual doubled contour.

The same retained boundary placement carries both differential increment requests and the polygon request, including
their cross-term budget. -/
structure BilinearHoleRequest (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (included :
  Extension.CoordinateInclusion base.bank.grid next.bank.grid)
    (leftFixed : MagnitudeBank.FaceMagnitudeBank domains leftDifferential) (rightFixed : MagnitudeBank.FaceMagnitudeBank
      domains rightDifferential)
    (branch : BranchIsolation.Data.Index branches) (error : Fraction.Rational) where
  /-- The requested squared-area error is strictly positive. -/ positive : 0 < error
  /-- The cached common magnitude bound for the actual resplit boundary. -/ magnitude : Fraction.Rational
  /-- The magnitude uses the squared boundary count and maximum of the retained differential magnitude bounds. -/
    magnitude_eq : magnitude =
    ((Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests.BilinearHoleRequest.boundary bank
    included branch).edgeCount : Fraction.Rational)^2 *
    (4 * max leftFixed.bound rightFixed.bound)
  /-- The retained common allowance for both differential increment requests. -/ totalTarget : Fraction.Rational
  /-- The increment allowance is the weighted share of one quarter of the error target. -/ totalTarget_eq : totalTarget
    = Weighted.allowance (error / 4) (4 * magnitude)
  /-- The actual paired source placement on the resplit original boundary. -/ paired : WalkOccurrences.PairedWalk
    current.mesh (Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests.BilinearHoleRequest.boundary
    bank included branch)
  /-- The retained opposite-sheet polygon comparison at one quarter of the target. -/ polygons :
    PolygonRequests.PolygonRequest leftFixed rightFixed paired 0 1 (error / 4)
  /-- The first differential increment request on the same paired placement. -/ leftTotal : PairedWalk.IncrementRequest
    paired domains leftDifferential 0 totalTarget
  /-- The second differential increment request on the same paired placement. -/ rightTotal :
    PairedWalk.IncrementRequest paired domains rightDifferential 0 totalTarget

constructive_injectivity BilinearHoleRequest

namespace BilinearHoleRequest

variable {leftFixed : FaceMagnitudeBank domains
  leftDifferential} {rightFixed : FaceMagnitudeBank
  domains rightDifferential}
  {branch : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {error :
    Rational}

/-- Prepare the retained boundary placement, opposite-sheet polygon comparison and both weighted increment requests. -/
@[expose] def build (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (included : Extension.CoordinateInclusion
  base.bank.grid next.bank.grid)
    (leftFixed : MagnitudeBank.FaceMagnitudeBank domains leftDifferential) (rightFixed : MagnitudeBank.FaceMagnitudeBank
      domains rightDifferential)
    (branch : BranchIsolation.Data.Index branches) (error : Fraction.Rational) (positive : 0 < error) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests.BilinearHoleRequest bank included leftFixed
      rightFixed branch error :=
  let magnitude :=
    ((boundary bank
    included branch).edgeCount : Fraction.Rational)^2 * (4 * max leftFixed.bound rightFixed.bound)
  let totalTarget := Weighted.allowance (error / 4) (4 * magnitude)
  have quarterPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
  have totalPositive := Weighted.allowance_positive quarterPositive
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (magnitude_nonnegative
      (bank := bank) (included := included) leftFixed rightFixed branch))
  let paired := PairedWalk.build current.mesh
    (boundary bank included
    branch)
  ⟨positive, magnitude, rfl, totalTarget, rfl, paired,
    PolygonRequest.build leftFixed rightFixed paired 0 1 (error / 4) quarterPositive,
    IncrementRequest.build paired domains leftDifferential 0 totalTarget totalPositive,
    IncrementRequest.build paired domains rightDifferential 0 totalTarget totalPositive⟩

/-- The common maximum stage paying the polygon and both differential increment requests. -/
@[expose] def index (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests.BilinearHoleRequest bank included leftFixed
  rightFixed branch error) : Nat :=
  max request.polygons.index (max request.leftTotal.index request.rightTotal.index)

/-- Twice either lap approximates the actual doubled contour. The two-sheet total pays its cross term; no zero-area
assertion is used. -/
theorem accurate (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests.BilinearHoleRequest
  bank included leftFixed rightFixed branch error)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh) (rightReadings :
      TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh)
    (later : request.index ≤ stage) (sheet : Fin 2) :
    let value := fun edge => (⟨edgeValuation current.mesh leftReadings.values edge,
      CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩ : Stokes.PrimitivePoint)
    let walk := boundary
      bank included branch
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
    · have h := (word_bound
        leftFixed leftReadings fixedLater.1 walk 0).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.le_max_left leftFixed.bound
            rightFixed.bound) (by decide))
          (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2))
      change Fraction.Order.Basic.LessEqual _ _ at h ⊢
      simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at h
      convert h using 1
    · have h := (word_bound
        rightFixed rightReadings fixedLater.2 walk 0).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.le_max_right leftFixed.bound
            rightFixed.bound) (by decide))
          (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2))
      change Fraction.Order.Basic.LessEqual _ _ at h ⊢
      simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at h
      convert h using 1
  have oldBound {point : Data.Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : Data.Gaussian.Basic.Canonical.normSq point ≤ limit) :
      Data.Gaussian.Norm.Basic.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using h
  have canonicalBound {point : Data.Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : Data.Gaussian.Norm.Basic.normSq point ≤ limit) :
      Data.Gaussian.Basic.Canonical.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using h
  have small : PrimitivePoint.Bounded ((totals 0).add (totals 1)) request.totalTarget := by
    dsimp only [totals, value]
    rw [total_readback,
      total_readback]
    exact ⟨canonicalBound leftTotal, canonicalBound rightTotal⟩
  have cross : Data.Gaussian.Norm.Basic.normSq (Stokes.edgeArea (totals 0) (totals 1)) ≤ error / 4 := by
    have same : Stokes.edgeArea (totals 0) (totals 1) = Stokes.edgeArea (totals 0) ((totals 0).add (totals 1)) := by
      simp only [Stokes.edgeArea, PrimitivePoint.add]
      ring1
    rw [same]
    apply oldBound
    apply (PrimitivePoint.area_bound bounded small).trans
    rw [request.totalTarget_eq]
    exact Weighted.mul_allowance_le
      (Fraction.Order.Field.div_pos_direct request.positive (by decide : (0 : Fraction.Rational) < 4)).le
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) magnitudeNonnegative)
  have opposite := request.polygons.accurate leftReadings rightReadings polygonLater (by decide)
  have either : ∀ sheet : Fin 2, Data.Gaussian.Norm.Basic.normSq (areas sheet + areas sheet - (areas 0 + areas
    1)) ≤ error / 4 := by
    refine Data.Fin.cases_induction ?_ (fun predecessor => Data.Fin.cases_induction ?_ (fun empty => Fin.elim0 empty)
      predecessor)
    · change Data.Gaussian.Norm.Basic.normSq (areas 0 + areas 0 - (areas 0 + areas 1)) ≤ error / 4
      rw [show areas 0 + areas 0 - (areas 0 + areas 1) = areas 0 - areas 1 by ring1]
      exact opposite
    · change Data.Gaussian.Norm.Basic.normSq (areas 1 + areas 1 - (areas 0 + areas 1)) ≤ error / 4
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

end BilinearHoleRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests
