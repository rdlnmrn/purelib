module

public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Entries
public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Polynomial
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Data.List.DependentProduct
public import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Tactic.Ring

/-! # Ordered ordinary polynomial programmes on the original covered parents

The finite occurrence product retains each original coordinate, uniform box
bounds and first numerator request. Later stages retarget those same ceilings,
then store their actual inverse/power/primitive/pullback caches. The same
closed centered path supplies every stage's physical cycle and sheets.
-/

public section

attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

namespace Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents

open Purelib
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum gaussianNormSqSum)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedRefinementMovement
  (movementSum movementMass movementMass_eq movementMass_nonnegative)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (UniformBounds UniformRequest)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.UniformRequest (PolynomialModel)

variable {genus count floor : Nat} {curve : HyperellipticCurve genus} {basis : Differential genus}
    {differential : OddPowerDifferential curve.polynomial}

/-- Read the original physical start and retained sheet of one centered parent occurrence. -/
abbrev polynomialStart (parent : CenteredEdge curve basis) : LiftedPoint 2 :=
  ⟨parent.edge.segment.pointAt parent.edge.left.parameter, parent.edge.sheet⟩

/-- Read the original physical finish on that same centered parent's retained sheet. -/
abbrev polynomialFinish (parent : CenteredEdge curve basis) : LiftedPoint 2 :=
  ⟨parent.edge.segment.pointAt parent.edge.request.endpoint.parameter, parent.edge.sheet⟩

/-- The original covering seed contains the literal first endpoint of this occurrence. -/
theorem polynomialStart_inside {parent : CenteredEdge curve basis} (patch : PreparedPatch parent) (count : Nat) :
    (patch.neighborhood count).box.Contains (polynomialStart parent).coordinate := by
  have inside := patch.start_inside count
  rewrite [parent.edge.point_zero] at inside
  exact inside

/-- The original covered finish witness contains this same occurrence's literal last endpoint. -/
theorem polynomialFinish_inside {parent : CenteredEdge curve basis} (patch : PreparedPatch parent) (count : Nat)
    (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1)) :
    (patch.neighborhood count).box.Contains (polynomialFinish parent).coordinate := by
  rewrite [parent.edge.point_one] at inside
  exact inside

namespace PolynomialWork

/-- The three complete pre-stage caches at one original bounded covered occurrence.

The initial request is the actual stage-zero request, not an auxiliary search
that is discarded. Positive stages reuse its numerator ceiling and scale.
-/
@[expose] def Entry {parents : List (CenteredEdge curve basis)}
    (covered : CoveredParents count parents) (floor : Nat)
    (differential : OddPowerDifferential curve.polynomial) (index : Fin parents.length) : Type _ :=
    (_coordinate : { value : Spatial.Coordinate
      (polynomialStart (parents[index.val]'index.isLt)).coordinate
      (polynomialFinish (parents[index.val]'index.isLt)).coordinate //
      value = Spatial.Coordinate.build _ _ }) ×
    (bounds : { value : UniformBounds ((covered.entry index).val.neighborhood count) //
      value = UniformBounds.build ((covered.entry index).val.neighborhood count) }) ×
    { request : UniformRequest bounds.val 0 (differential.numerator.scale differential.scale) floor
        (quarterRadius 1 0 / 4) //
      request = bounds.val.request 0 (differential.numerator.scale differential.scale) floor
        (quarterRadius 1 0 / 4)
        (Order.Field.div_pos_direct (quarterRadius_pos (by decide +kernel) 0) (by decide +kernel)) }

end PolynomialWork

/-- Retain the complete coordinate, bounds and initial request at every original covered occurrence in order. -/
@[expose] def PolynomialWork {parents : List (CenteredEdge curve basis)}
    (covered : CoveredParents count parents) (floor : Nat)
    (differential : OddPowerDifferential curve.polynomial) : Type _ :=
  DependentProduct parents (PolynomialWork.Entry covered floor differential)

namespace PolynomialWork

variable {parents : List (CenteredEdge curve basis)} {covered : CoveredParents count parents}

/-- Read the exact retained coordinate/bounds/request triple at one bounded original occurrence. -/
@[expose] def entry (work : PolynomialWork covered floor differential) (index : Fin parents.length) :=
  DependentProduct.get parents work index

/-- Read the unchanged retained work product after one original covered parent. -/
@[expose] def tail {parent : CenteredEdge curve basis} {remaining : List (CenteredEdge curve basis)}
    {patch : PreparedPatch parent} {inside : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {covered : CoveredParents count remaining}
    (work : PolynomialWork (.cons patch inside covered) floor differential) :
    PolynomialWork covered floor differential := work.2

/-- Materialize the three original caches once per literal parent occurrence in list order. -/
def build (covered : CoveredParents count parents) (floor : Nat)
    (differential : OddPowerDifferential curve.polynomial) : PolynomialWork covered floor differential :=
  DependentProduct.ofFn parents (fun index =>
    let coordinate := Spatial.Coordinate.build
      (polynomialStart (parents[index.val]'index.isLt)).coordinate
      (polynomialFinish (parents[index.val]'index.isLt)).coordinate
    let bounds := UniformBounds.build ((covered.entry index).val.neighborhood count)
    let request := bounds.request 0 (differential.numerator.scale differential.scale) floor
      (quarterRadius 1 0 / 4)
      (Order.Field.div_pos_direct (quarterRadius_pos (by decide +kernel) 0) (by decide +kernel))
    ⟨⟨coordinate, rfl⟩, ⟨bounds, rfl⟩, ⟨request, rfl⟩⟩)

/-- The complete finite work product retains the original per-occurrence three-factory execution. -/
private theorem packaged_build_factory (covered : CoveredParents count parents) (floor : Nat)
    (differential : OddPowerDifferential curve.polynomial) :
    build covered floor differential = DependentProduct.ofFn parents (fun index =>
      let coordinate := Spatial.Coordinate.build
        (polynomialStart (parents[index.val]'index.isLt)).coordinate
        (polynomialFinish (parents[index.val]'index.isLt)).coordinate
      let bounds := UniformBounds.build ((covered.entry index).val.neighborhood count)
      let request := bounds.request 0 (differential.numerator.scale differential.scale) floor
        (quarterRadius 1 0 / 4)
        (Order.Field.div_pos_direct (quarterRadius_pos (by decide +kernel) 0) (by decide +kernel))
      ⟨⟨coordinate, rfl⟩, ⟨bounds, rfl⟩, ⟨request, rfl⟩⟩) := by rfl

/-- The complete finite work product retains the original per-occurrence three-factory execution. -/
theorem build_factory (covered : CoveredParents count parents) (floor : Nat)
    (differential : OddPowerDifferential curve.polynomial) :
    build covered floor differential = DependentProduct.ofFn parents (fun index =>
      let coordinate := Spatial.Coordinate.build
        (polynomialStart (parents[index.val]'index.isLt)).coordinate
        (polynomialFinish (parents[index.val]'index.isLt)).coordinate
      let bounds := UniformBounds.build ((covered.entry index).val.neighborhood count)
      let request := bounds.request 0 (differential.numerator.scale differential.scale) floor
        (quarterRadius 1 0 / 4)
        (Order.Field.div_pos_direct (quarterRadius_pos (by decide +kernel) 0) (by decide +kernel))
      ⟨⟨coordinate, rfl⟩, ⟨bounds, rfl⟩, ⟨request, rfl⟩⟩) :=
  packaged_build_factory covered floor differential

namespace Models

/-- The actual selected request and whole model at one original occurrence of the same retained work product. -/
@[expose] def Entry (work : PolynomialWork covered floor differential) (stage : Nat)
    (index : Fin parents.length) : Type _ :=
    (request : { value : UniformRequest (work.entry index).2.1.val 0
      (differential.numerator.scale differential.scale) floor (quarterRadius 1 stage / 4) //
      value = (work.entry index).2.2.val.atStage stage }) ×
    { model : PolynomialModel (differential := differential) request.val (work.entry index).1.val
        (quarterRadius_pos (by decide +kernel) stage) //
      model = PolynomialModel.build request.val (work.entry index).1.val
        (quarterRadius_pos (by decide +kernel) stage) }

end Models

/-- Actual finite stage requests and complete polynomial models indexed by the same retained work product. -/
@[expose] def Models (work : PolynomialWork covered floor differential) (stage : Nat) : Type _ :=
  DependentProduct parents (Models.Entry work stage)

/-- Materialize every actual stage request before the polynomial model that consumes it. -/
def models (work : PolynomialWork covered floor differential) (stage : Nat) : work.Models stage :=
  DependentProduct.ofFn parents (fun index =>
    let request := (work.entry index).2.2.val.atStage stage
    let model := PolynomialModel.build (differential := differential) request (work.entry index).1.val
      (quarterRadius_pos (by decide +kernel) stage)
    ⟨⟨request, rfl⟩, ⟨model, rfl⟩⟩)

/-- The entire stage bank retains the actual request/model factory pair at every original occurrence. -/
private theorem packaged_models_factory (work : PolynomialWork covered floor differential) (stage : Nat) :
    work.models stage = DependentProduct.ofFn parents (fun index =>
      let request := (work.entry index).2.2.val.atStage stage
      let model := PolynomialModel.build (differential := differential) request (work.entry index).1.val
        (quarterRadius_pos (by decide +kernel) stage)
      ⟨⟨request, rfl⟩, ⟨model, rfl⟩⟩) := by rfl

/-- The entire stage bank retains the actual request/model factory pair at every original occurrence. -/
theorem models_factory (work : PolynomialWork covered floor differential) (stage : Nat) :
    work.models stage = DependentProduct.ofFn parents (fun index =>
      let request := (work.entry index).2.2.val.atStage stage
      let model := PolynomialModel.build (differential := differential) request (work.entry index).1.val
        (quarterRadius_pos (by decide +kernel) stage)
      ⟨⟨request, rfl⟩, ⟨model, rfl⟩⟩) := packaged_models_factory work stage

namespace Models

variable {work : PolynomialWork covered floor differential} {stage : Nat}

/-- Read the actual stored request and whole polynomial cache at the original bounded occurrence. -/
@[expose] def entry (models : work.Models stage) (index : Fin parents.length) :=
  DependentProduct.get parents models index

/-- Read the first actual cell from its retained polynomial model without rebuilding it. -/
@[expose] def cell {parent : CenteredEdge curve basis} {remaining : List (CenteredEdge curve basis)}
    {patch : PreparedPatch parent} {inside : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {covered : CoveredParents count remaining}
    (work : PolynomialWork (.cons patch inside covered) floor differential)
    (models : work.Models stage) : CellModel := models.1.2.val.pullback.model

/-- Read the unchanged model tail on the same original retained work product. -/
@[expose] def tail {parent : CenteredEdge curve basis} {remaining : List (CenteredEdge curve basis)}
    {patch : PreparedPatch parent} {inside : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {covered : CoveredParents count remaining}
    {work : PolynomialWork (.cons patch inside covered) floor differential}
    (models : work.Models stage) : work.tail.Models stage := models.2

/-- Read the actual spatial cells from their stored polynomial caches in the original parent order. -/
@[expose] def cells : {parents : List (CenteredEdge curve basis)} →
    (covered : CoveredParents count parents) → (work : PolynomialWork covered floor differential) →
    work.Models stage → List CellModel
  | [], .nil, _, _ => []
  | _ :: _, .cons _ _ covered, work, models =>
      cell work models :: cells covered work.tail models.tail

/-- The stored cell list retains every original occurrence, including repeated and zero-width parents. -/
theorem cells_length : {parents : List (CenteredEdge curve basis)} →
    (covered : CoveredParents count parents) → (work : PolynomialWork covered floor differential) →
    (models : work.Models stage) → (cells covered work models).length = parents.length
  | [], .nil, _, _ => rfl
  | _ :: _, .cons _ _ covered, work, models => congrArg Nat.succ (cells_length covered work.2 models.2)

/-- The actual retained coordinate displacement is the original parent's movement, with its original endpoints. -/
theorem movement {parent : CenteredEdge curve basis} (patch : PreparedPatch parent)
    (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    {remaining : List (CenteredEdge curve basis)} {tail : CoveredParents count remaining}
    (work : PolynomialWork (.cons patch inside tail) floor differential) :
    Norm.Basic.normSq work.1.1.val.displacement = parent.edge.pointMovement := by
  rewrite [work.1.1.val.displacement_eq]
  change Norm.Basic.normSq ((polynomialFinish parent).coordinate - (polynomialStart parent).coordinate) =
    Norm.Basic.normSq (parent.edge.point 1 - parent.edge.point 0)
  rewrite [parent.edge.point_one, parent.edge.point_zero]
  rfl

/-- The exact ordered cell allowances sum to the original movement sum times the actual stage allocation. -/
theorem totalWeightedAllowance_eq : {parents : List (CenteredEdge curve basis)} →
    (covered : CoveredParents count parents) → (work : PolynomialWork covered floor differential) →
    (models : work.Models stage) →
    (PathModel.mk (cells covered work models)).totalWeightedAllowance = movementSum parents * quarterRadius 1 stage
  | [], .nil, _, _ => by change (0 : Rational) = 0 * _; ring1
  | parent :: remaining, .cons patch inside covered, work, models => by
      change models.1.2.val.pullback.model.weightedAllowance +
        (PathModel.mk (cells covered work.2 models.2)).totalWeightedAllowance = _
      rewrite [models.1.2.val.weightedAllowance_eq]
      change Norm.Basic.normSq work.1.1.val.displacement * quarterRadius 1 stage +
        (PathModel.mk (cells covered work.2 models.2)).totalWeightedAllowance = _
      rewrite [movement patch inside work,
        totalWeightedAllowance_eq covered work.2 models.2, movementSum]
      ring1

/-- The exact original count-weighted allowance is G times the stage allocation, where G is original movementMass. -/
theorem aggregateAllowance_eq (models : work.Models stage) :
    (PathModel.mk (cells covered work models)).aggregateAllowance = movementMass parents * quarterRadius 1 stage := by
  unfold PathModel.aggregateAllowance
  rewrite [cells_length covered work models, totalWeightedAllowance_eq covered work models, movementMass_eq]
  ring1

/-- The actual point-acquisition operation on a retained occurrence's same original covered neighborhood.

This is a query factory, not a materialized infinite point bank. A finite
certificate query acquires its own Point once and refines that actual Point.
-/
def points {parent : CenteredEdge curve basis} (patch : PreparedPatch parent)
    (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (coordinate : Spatial.Coordinate (polynomialStart parent).coordinate (polynomialFinish parent).coordinate)
    (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1) :
    ContinuedNeighborhood.Point (patch.neighborhood count) (coordinate.point input) :=
  ContinuedNeighborhood.Point.acquire (patch.neighborhood count) (coordinate.point input)
    (coordinate.point_inside (polynomialStart_inside patch count) (polynomialFinish_inside patch count inside)
      lower upper)

/-- The query factory returns the whole original acquired Point on its retained neighborhood and coordinate. -/
private theorem packaged_points_factory {parent : CenteredEdge curve basis} (patch : PreparedPatch parent)
    (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (coordinate : Spatial.Coordinate (polynomialStart parent).coordinate (polynomialFinish parent).coordinate)
    (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1) :
    points patch inside coordinate input lower upper =
      ContinuedNeighborhood.Point.acquire (patch.neighborhood count) (coordinate.point input)
        (coordinate.point_inside (polynomialStart_inside patch count) (polynomialFinish_inside patch count inside)
          lower upper) := by rfl

/-- The query factory returns the whole original acquired Point on its retained neighborhood and coordinate. -/
theorem points_factory {parent : CenteredEdge curve basis} (patch : PreparedPatch parent)
    (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (coordinate : Spatial.Coordinate (polynomialStart parent).coordinate (polynomialFinish parent).coordinate)
    (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1) :
    points patch inside coordinate input lower upper =
      ContinuedNeighborhood.Point.acquire (patch.neighborhood count) (coordinate.point input)
        (coordinate.point_inside (polynomialStart_inside patch count) (polynomialFinish_inside patch count inside)
          lower upper) := packaged_points_factory patch inside coordinate input lower upper

/-- Attach one retained polynomial cell to the certificates of its original centered tail.

The head uses the stored pullback and coordinate query factory. The tail is
supplied intact, keeping this dependent construction outside recursive equations.
-/
private def certifyCons {parent : CenteredEdge curve basis} (patch : PreparedPatch parent)
    (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    {remaining : List (CenteredEdge curve basis)} {covered : CoveredParents count remaining}
    (work : PolynomialWork (.cons patch inside covered) floor differential)
    (models : work.Models stage) (ordinary : differential.denominatorPairs = 0)
    {finish : LiftedPoint 2}
    (chain : CenteredPathChain remaining (start := polynomialFinish parent) (finish := finish))
    (tail : Algebraic.Path.Jets.UniformPathCertificates curve differential
      (cells covered work.2 models.2) chain.path) :
    Algebraic.Path.Jets.UniformPathCertificates curve differential
      (cells (.cons patch inside covered) work models) (CenteredPathChain.cons parent chain).path :=
  .cons models.1.2.val.pullback.start_eq models.1.2.val.pullback.finish_eq
    (.uniform (models.1.2.val.certificate ordinary
      (ClearSegment.liftOnSheet parent.edge.sheet parent.edge.localSegment)
      (polynomialStart_inside patch count) (polynomialFinish_inside patch count inside)
      (points patch inside work.1.1.val))) tail

/-- Certify every stored polynomial cell on the SAME original centered chain and its actual retained sheets. -/
def certify (ordinary : differential.denominatorPairs = 0) :
    {parents : List (CenteredEdge curve basis)} → (covered : CoveredParents count parents) →
    (work : PolynomialWork covered floor differential) → (models : work.Models stage) →
    {start finish : LiftedPoint 2} → (chain : CenteredPathChain parents (start := start) (finish := finish)) →
    Algebraic.Path.Jets.UniformPathCertificates curve differential (cells covered work models) chain.path
  | [], .nil => fun _ _ => by
      intro start finish chain
      cases chain with
      | nil => exact .nil _
  | parent :: _, .cons patch inside covered => fun work models => by
      intro start finish chain
      cases chain with
      | cons _ chain =>
          exact certifyCons patch inside work models ordinary chain
            (certify ordinary covered work.2 models.2 chain)

/-- Read the actual later-minus-earlier cell samples in their literal occurrence order. -/
private def errors {earlier later : Nat} : {parents : List (CenteredEdge curve basis)} →
    (covered : CoveredParents count parents) → (work : PolynomialWork covered floor differential) →
    work.Models earlier → work.Models later → List Canonical
  | [], .nil => fun _ _ _ => []
  | _ :: _, .cons _ _ covered => fun work first last =>
      ((cell work last).integralSample - (cell work first).integralSample) ::
        errors covered work.tail first.tail last.tail

/-- The actual error list contains precisely the original number of occurrences. -/
private theorem errors_length {earlier later : Nat} : {parents : List (CenteredEdge curve basis)} →
    (covered : CoveredParents count parents) → (work : PolynomialWork covered floor differential) →
    (first : work.Models earlier) → (last : work.Models later) →
    (errors covered work first last).length = parents.length
  | [], .nil => fun _ _ _ => rfl
  | _ :: _, .cons _ _ covered => fun work first last =>
      congrArg Nat.succ (errors_length covered work.2 first.2 last.2)

/-- The error sum is the difference of the two SAME complete ordered path samples. -/
private theorem errors_sum {earlier later : Nat} : {parents : List (CenteredEdge curve basis)} →
    (covered : CoveredParents count parents) → (work : PolynomialWork covered floor differential) →
    (first : work.Models earlier) → (last : work.Models later) →
    gaussianSum (errors covered work first last) =
      (PathModel.mk (cells covered work last)).integralSample -
        (PathModel.mk (cells covered work first)).integralSample
  | [], .nil => fun _ _ _ => by change (0 : Canonical) = 0 - 0; ring1
  | _ :: _, .cons _ _ covered => fun work first last => by
      let firstHead := first.1.2.val.pullback.model.integralSample
      let lastHead := last.1.2.val.pullback.model.integralSample
      have tail := errors_sum covered work.2 first.2 last.2
      change (lastHead - firstHead) + gaussianSum (errors covered work.2 first.2 last.2) =
        (lastHead + (PathModel.mk (cells covered work.2 last.2)).integralSample) -
          (firstHead + (PathModel.mk (cells covered work.2 first.2)).integralSample)
      exact (congrArg (fun value : Canonical => (lastHead - firstHead) + value) tail).trans (by ring1)

/-- Every actual local model payment is summed on the original movement spine. -/
private theorem errors_normSum_le (ordinary : differential.denominatorPairs = 0)
    {earlier later : Nat} (order : earlier ≤ later) : {parents : List (CenteredEdge curve basis)} →
    (covered : CoveredParents count parents) → (work : PolynomialWork covered floor differential) →
    (first : work.Models earlier) → (last : work.Models later) →
    gaussianNormSqSum (errors covered work first last) ≤
      32 * quarterRadius 1 earlier * movementSum parents
  | [], .nil => fun _ _ _ => by
      change (0 : Rational) ≤ _ * 0
      rewrite [Field.mul_zero_direct]
      exact Order.Basic.le_refl 0
  | parent :: remaining, .cons patch inside covered => fun work first last => by
      have localBound := first.1.2.val.later_integral_difference_le last.1.2.val ordinary
        (ClearSegment.liftOnSheet parent.edge.sheet parent.edge.localSegment)
        (polynomialStart_inside patch count) (polynomialFinish_inside patch count inside)
        (points patch inside work.1.1.val) order
      change Norm.Basic.normSq (last.1.2.val.pullback.model.integralSample -
        first.1.2.val.pullback.model.integralSample) ≤
          quarterRadius (32 * Norm.Basic.normSq work.1.1.val.displacement) earlier at localBound
      have head := localBound.trans_eq
        (congrArg (fun value => quarterRadius (32 * value) earlier) (movement patch inside work))
      simp only [quarterRadius_eq_mul_pow] at head
      have tail := errors_normSum_le ordinary order covered work.2 first.2 last.2
      change Canonical.normSq (_ - _) + gaussianNormSqSum (errors covered work.2 first.2 last.2) ≤ _
      rewrite [← Norm.Basic.normSq_eq_canonical]
      exact (Order.Arithmetic.add_le_add_direct head tail).trans_eq (by
        rewrite [movementSum, quarterRadius_eq_mul_pow]
        ring1)

/-- The actual later sample is paid by E=32G on the original finite ordered cover. -/
theorem later_close (ordinary : differential.denominatorPairs = 0) {earlier later : Nat}
    (first : work.Models earlier) (last : work.Models later) (order : earlier ≤ later) :
    Norm.Basic.normSq ((PathModel.mk (cells covered work last)).integralSample -
      (PathModel.mk (cells covered work first)).integralSample) ≤
        quarterRadius (32 * movementMass parents) earlier := by
  have original := Norm.Sum.Basic.normSq_gaussianSum_le (errors covered work first last)
  rewrite [← Norm.Basic.normSq_eq_canonical, errors_sum covered work first last,
    errors_length covered work first last] at original
  have bounded := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (errors_normSum_le ordinary order covered work first last)
    (Cast.Order.natCast_le_direct (m := 0) (n := parents.length) (Nat.zero_le _))
  exact (original.trans bounded).trans_eq (by
    rewrite [movementMass_eq]
    simp only [quarterRadius_eq_mul_pow]
    ring1)

end Models

variable {point : LiftedPoint 2} (chain : CenteredPathChain parents (start := point) (finish := point))
    (work : PolynomialWork covered floor differential) (models : (stage : Nat) → work.Models stage)
    (ordinary : differential.denominatorPairs = 0)

/-- The actual requested model is the literal list of retained polynomial pullbacks at that stage. -/
def model (stage : Nat) : PathModel := ⟨Models.cells covered work (models stage)⟩

/-- The original stage view retains precisely the cells of its actual supplied finite model bank. -/
private theorem packaged_model_cells (stage : Nat) :
    (model work models stage).cells = Models.cells covered work (models stage) := by rfl

/-- The original stage view retains precisely the cells of its actual supplied finite model bank. -/
theorem model_cells (stage : Nat) :
    (model work models stage).cells = Models.cells covered work (models stage) :=
  packaged_model_cells work models stage

/-- The original movement mass determines the nonnegative geometric scale 32G. -/
@[expose] def errorScale (parents : List (CenteredEdge curve basis)) : Rational := 32 * movementMass parents

/-- The computed geometric scale retains its original finite nonnegative movement mass. -/
theorem errorScale_nonnegative : 0 ≤ errorScale parents :=
  Order.Arithmetic.mul_nonneg_direct (Cast.Order.natCast_le_direct (m := 0) (n := 32) (Nat.zero_le 32))
    (movementMass_nonnegative parents)

/-- Retain every original polynomial path with internally derived allowance, progression and center bounds. -/
def program : RefinementProgram where
  model := model work models
  errorScale := errorScale parents
  errorScale_nonneg := errorScale_nonnegative
  modelAllowance_le := by
    intro stage
    have exactAllowance := Models.aggregateAllowance_eq (models stage)
    have massBound := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Cast.Order.natCast_le_direct (m := 1) (n := 32) (by decide +kernel)) (movementMass_nonnegative parents)
    have scaled := quarterRadius_scale_mono (by
      exact (show movementMass parents = 1 * movementMass parents by ring1).trans_le massBound) stage
    exact exactAllowance.trans_le ((show movementMass parents * quarterRadius 1 stage =
      quarterRadius (movementMass parents) stage by
        rewrite [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]; ring1).trans_le scaled)
  later_close := by
    intro earlier later order
    rewrite [← Norm.Basic.normSq_eq_canonical]
    exact Models.later_close ordinary (models earlier) (models later) order
  centerBound := 2 * (Norm.Basic.normSq (model work models 0).integralSample + errorScale parents)
  centerBound_nonneg := Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    (by
      have terms := Order.Arithmetic.add_le_add_direct
        (Norm.Basic.normSq_nonneg (model work models 0).integralSample)
        (errorScale_nonnegative (parents := parents))
      rewrite [Field.zero_add] at terms
      exact terms)
  sample_bounded := by
    intro stage
    rewrite [← Norm.Basic.normSq_eq_canonical]
    have offset := (Models.later_close ordinary (models 0) (models stage) (Nat.zero_le _)).trans
      (quarterRadius_le_scale (errorScale_nonnegative (parents := parents)) 0)
    exact Norm.Bounds.value_normSq_le_of_offset offset

/-- The programme's cells are the exact stored pullback cells, without another model request. -/
private theorem packaged_program_model (stage : Nat) :
    (program work models ordinary).model stage = model work models stage := by rfl

/-- The programme's cells are the exact stored pullback cells, without another model request. -/
theorem program_model (stage : Nat) :
    (program work models ordinary).model stage = model work models stage :=
  packaged_program_model work models ordinary stage

/-- The numerical programme retains exactly E=32G from the original ordered parent geometry. -/
private theorem packaged_program_errorScale :
    (program work models ordinary).errorScale = 32 * movementMass parents := by rfl

/-- The numerical programme retains exactly E=32G from the original ordered parent geometry. -/
theorem program_errorScale :
    (program work models ordinary).errorScale = 32 * movementMass parents :=
  packaged_program_errorScale work models ordinary

/-- Uniformly realize the full ordinary numerator on the SAME original closed centered cycle at every stage. -/
def certified : Algebraic.Period.Jets.CertifiedPeriodProgram curve differential
    ⟨fun _ => ⟨point, chain.path⟩⟩ where
  integral := program work models ordinary
  certificates := by
    intro stage
    rewrite [program_model]
    exact Models.certify ordinary covered work (models stage) chain

/-- Construct a genuine closed-cycle programme from one retained pre-stage work bank and its actual stage factory.

Every finite stage materializes its own request/model bank once. Readings of
that bank use stored values; no memoization across separate stage calls is asserted.
-/
def fromWork : Algebraic.Period.Jets.CertifiedPeriodProgram curve differential ⟨fun _ => ⟨point, chain.path⟩⟩ :=
  certified chain work work.models ordinary

/-- The actual closed-cycle producer retains the same complete original numerical programme. -/
private theorem packaged_fromWork_integral :
    (fromWork chain work ordinary).integral = program work work.models ordinary := by rfl

/-- The actual closed-cycle producer retains the same complete original numerical programme. -/
theorem fromWork_integral :
    (fromWork chain work ordinary).integral = program work work.models ordinary :=
  packaged_fromWork_integral chain work ordinary

end PolynomialWork

end Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents

end
