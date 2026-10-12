module
meta import Purelib.Elab.ConstructiveInjectivity
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
import Purelib.Data.Gaussian.Norm.Sum.Basic
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PolygonRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
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
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PolygonRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Meshes

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing

public section

/-! Compare either exterior lap with the actual closed exterior components.
In odd degree the cross term of the two lap totals is paid explicitly. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences (PairedWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PolygonRequests (PolygonRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk
  (IncrementRequest)
open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation orderedRoute
  orderedRoute_value)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_neg)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {next : FramedPuncturedGrid curve branches higher}
  {current : LiftedPuncturedGrid next}
  {domains : FaceDomainBank current.frames
    next.faces.regulars} {leftDifferential rightDifferential :
    Differential genus}

namespace ExteriorLapRequest

/-- The paired total of the actual word readings consists of the two original scalar word values. -/
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

/-- The actual indexed walk value obeys the retained primitive magnitude bound scaled by its squared edge count. -/
private theorem word_bound {differential : Differentials.Basic.Differential genus} (fixed :
  MagnitudeBank.FaceMagnitudeBank domains differential)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
    (later : fixed.index ≤ stage) {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk next.bank.grid start
      finish) (sheet : Fin 2) :
    Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation current.mesh
      readings.values) (current.edges.indexedEdges current.vertices walk sheet)) ≤
      (walk.edgeCount : Fraction.Rational) ^ 2 * (4 * fixed.bound) := by
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
/-- The common two-differential exterior-lap magnitude bound is nonnegative. -/
theorem magnitude_nonnegative (leftFixed : MagnitudeBank.FaceMagnitudeBank domains leftDifferential)
    (rightFixed : MagnitudeBank.FaceMagnitudeBank domains rightDifferential) :
    0 ≤ (next.bank.exterior.edgeCount : Fraction.Rational) ^ 2 * (4 * max leftFixed.bound rightFixed.bound) :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.pow_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (leftFixed.nonnegative.trans
      (Fraction.Order.Basic.le_max_left _ _)))

end ExteriorLapRequest

set_option genInjectivity false in
/-- A paid comparison between either exterior lap and the actual closed exterior component list.

One retained paired placement carries both polygon and differential increment requests, including the explicit lap-total
cross-term budget in odd degree. -/
structure ExteriorLapRequest (leftFixed : MagnitudeBank.FaceMagnitudeBank domains leftDifferential) (rightFixed :
  MagnitudeBank.FaceMagnitudeBank domains rightDifferential)
     (error : Fraction.Rational) where
  /-- The requested exterior-lap error is strictly positive. -/ positive : 0 < error
  /-- The cached common magnitude bound for the two differential exterior-lap values. -/ magnitude : Fraction.Rational
  /-- The cached bound uses the actual squared exterior edge count and maximum retained differential magnitude. -/
    magnitude_eq : magnitude = (next.bank.exterior.edgeCount : Fraction.Rational) ^ 2 *
    (4 * max leftFixed.bound rightFixed.bound)
  /-- The common allowance for the two differential lap increment requests. -/ totalTarget : Fraction.Rational
  /-- The increment allowance is the weighted share of one quarter of the target. -/ totalTarget_eq : totalTarget =
    Weighted.allowance (error / 4) (4 * magnitude)
  /-- The actual paired placement of the original exterior walk. -/ paired : WalkOccurrences.PairedWalk current.mesh
    next.bank.exterior
  /-- The retained polygon comparison between its two initial sheets. -/ polygons : PolygonRequests.PolygonRequest
    leftFixed rightFixed paired 0 1 (error / 4)
  /-- The first differential increment-cancellation request on that exact paired exterior walk. -/ leftTotal :
    PairedWalk.IncrementRequest paired domains leftDifferential 0 totalTarget
  /-- The second differential increment-cancellation request on that same paired exterior walk. -/ rightTotal :
    PairedWalk.IncrementRequest paired domains rightDifferential 0 totalTarget

constructive_injectivity ExteriorLapRequest

namespace ExteriorLapRequest

variable {leftFixed : FaceMagnitudeBank domains
  leftDifferential} {rightFixed : FaceMagnitudeBank
  domains rightDifferential}
  {error : Rational}

/-- Prepare the paired exterior walk once and retain the polygon and both increment requests with the explicit
cross-term allowance. -/
@[expose] def build (leftFixed : MagnitudeBank.FaceMagnitudeBank domains leftDifferential) (rightFixed :
  MagnitudeBank.FaceMagnitudeBank domains rightDifferential)
     (error : Fraction.Rational) (positive : 0 < error) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest.ExteriorLapRequest leftFixed rightFixed error :=
  let magnitude := (next.bank.exterior.edgeCount : Fraction.Rational) ^ 2 * (4 * max leftFixed.bound rightFixed.bound)
  let totalTarget := Weighted.allowance (error / 4) (4 * magnitude)
  have quarterPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
  have totalPositive := Weighted.allowance_positive quarterPositive
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (magnitude_nonnegative leftFixed
      rightFixed))
  let paired := PairedWalk.build current.mesh next.bank.exterior
  ⟨positive, magnitude, rfl, totalTarget, rfl, paired,
    PolygonRequest.build leftFixed rightFixed paired 0 1 (error / 4) quarterPositive,
    IncrementRequest.build paired domains leftDifferential 0 totalTarget totalPositive,
    IncrementRequest.build paired domains rightDifferential 0 totalTarget totalPositive⟩

/-- The common maximum stage paying the exterior polygon and both increment request stages. -/
@[expose] def index (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest.ExteriorLapRequest
  leftFixed rightFixed error) : Nat :=
  max request.polygons.index (max request.leftTotal.index request.rightTotal.index)

section

/-- Two sheets have a positive literal finite bound. -/
local instance : NeZero (2 : Nat) := ⟨by decide +kernel⟩

/-- In odd degree the actual closed exterior is the double contour. Both differential increment requests pay its
lap-total cross term. -/
theorem odd_accurate (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest.ExteriorLapRequest
  leftFixed rightFixed error)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh) (rightReadings :
      TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh)
    (later : request.index ≤ stage) (degree : curve.polynomial.natDegree = 2 * genus + 1) (sheet : Fin 2) :
    let value := fun edge => (⟨edgeValuation current.mesh leftReadings.values edge,
      CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩ : Stokes.PrimitivePoint)
    let walk := next.bank.exterior
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
    magnitude_nonnegative leftFixed
    rightFixed
  have bounded : PrimitivePoint.Bounded (totals 0) request.magnitude := by
    dsimp only [totals, value]
    rw [total_readback,
      request.magnitude_eq]
    constructor
    · have h := (word_bound leftFixed
        leftReadings fixedLater.1 walk 0).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.le_max_left leftFixed.bound
            rightFixed.bound) (by decide))
          (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2))
      change Fraction.Order.Basic.LessEqual _ _ at h ⊢
      simp only [-eq_self, -iff_self, Data.Gaussian.Norm.Basic.normSq_eq_canonical] at h
      convert h using 1
    · have h := (word_bound rightFixed
        rightReadings fixedLater.2 walk 0).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
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
  have small : PrimitivePoint.Bounded ((totals 0).add (totals 1)) request.totalTarget := by
    dsimp only [totals, value]
    rw [total_readback,
      total_readback]
    exact ⟨canonicalBound leftTotal, canonicalBound rightTotal⟩
  have cross : Data.Gaussian.Norm.Basic.normSq (Stokes.edgeArea (totals 0) (totals 1)) ≤ error / 4 := by
    have same : Stokes.edgeArea (totals 0) (totals 1) = Stokes.edgeArea (totals 0) ((totals 0).add (totals 1)) := by
      simp only [-eq_self, -iff_self, Stokes.edgeArea, PrimitivePoint.add]
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
    (current.edges.indexedEdges_append current.vertices walk walk 0).trans
      (congrArg (fun rest => words 0 ++ rest)
        (congrArg (current.edges.indexedEdges current.vertices walk) (current.exterior_swap_odd degree 0)))
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

section

end

/-- Two sheets have a positive literal finite bound. -/
local instance : NeZero (2 : Nat) := ⟨by decide +kernel⟩

/-- Both degree shapes compare the same one-lap polygon with the literal closed exterior component list; no component
area is set to zero. -/
theorem accurate (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest.ExteriorLapRequest leftFixed
  rightFixed error)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh) (rightReadings :
      TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh)
    (later : request.index ≤ stage) (sheet : Fin 2) :
    let value := fun edge => (⟨edgeValuation current.mesh leftReadings.values edge,
      CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩ : Stokes.PrimitivePoint)
    let area := fun word => PairedIncrementArea.area (word.map value)
    let lap := area (current.edges.indexedEdges current.vertices next.bank.exterior sheet)
    Data.Gaussian.Norm.Basic.normSq (lap + lap - Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (current.exteriorBoundaries.map area)) ≤ error := by
  intro value area lap
  cases shape : curve.degreeShape with
  | odd degree =>
      have estimate := request.odd_accurate leftReadings rightReadings later degree sheet
      simpa only [-eq_self, -iff_self, LiftedPuncturedGrid.exteriorBoundaries, shape, List.map_cons, List.map_nil,
        Data.Gaussian.Norm.Sum.Basic.gaussianSum, add_zero] using estimate
  | even _ =>
      have opposite := request.polygons.accurate leftReadings rightReadings
        ((Nat.Order.le_max_left _ _).trans later) (by decide)
      let areas := fun initial => area (current.edges.indexedEdges current.vertices next.bank.exterior initial)
      have quarter : error / 4 ≤ error := by
        apply (Fraction.Order.Field.div_le_iff_pos (by decide)).mpr
        exact (show error = error * 1 by ring1).le.trans
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide : (1 : Fraction.Rational) ≤ 4)
            request.positive.le)
      have estimate : ∀ initial : Fin 2, Data.Gaussian.Norm.Basic.normSq (areas initial + areas initial -
        (areas 0 + areas 1)) ≤ error := by
        intro position
        refine Fin.cases_induction ?_ (fun next => ?_) position
        · change Data.Gaussian.Norm.Basic.normSq (areas 0 + areas 0 - (areas 0 + areas 1)) ≤ error
          rw [show areas 0 + areas 0 - (areas 0 + areas 1) = areas 0 - areas 1 by ring1]
          exact opposite.trans quarter
        · refine Fin.cases_induction ?_ (fun empty => Fin.elim0 empty) next
          change Data.Gaussian.Norm.Basic.normSq (areas 1 + areas 1 - (areas 0 + areas 1)) ≤ error
          rw [show areas 1 + areas 1 - (areas 0 + areas 1) = -(areas 0 - areas 1) by ring1,
            Data.Gaussian.Norm.Basic.normSq_neg]
          exact opposite.trans quarter
      simpa only [-eq_self, -iff_self, LiftedPuncturedGrid.exteriorBoundaries, shape, List.map_cons, List.map_nil,
        Data.Gaussian.Norm.Sum.Basic.gaussianSum, add_zero] using estimate sheet

end

end ExteriorLapRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest
