module
-- The exposed cell preparation retains the public overlap-ready model owner.
public import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Riemann.Normalization.ContinuedInverseRootOverlap
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Normalization.InverseRootComparison
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

public import Purelib.Riemann.Paths.ClearBoxPaths
public import Purelib.Riemann.Normalization.RegularFaceInverseModels
public import Purelib.Riemann.Normalization.AlignedInverseRootSeed
public import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Geometry.Rational.Box.Sample
import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.State.WindingOne.Basic
import Mathlib.Order.Basic

public section

/-!
# Automatically acquired, owner-backed models on regular face children

A local query transports the retained face-anchor owner along an actual
clear path and aligns a seed inside its terminal owner. The face's uniform
mesh bound makes that seed valid on the entire child rectangle. Polynomial
refinement reads this cache; it neither chooses a new sheet nor reruns the
transport. Generated traces and aligned samples enter through the same
semantic constructor, without equality to a canonical search result.

The sign-sensitive estimate below is at the child anchor. Agreement along
shared child edges and comparison with the global period boundary are
separate obligations, not consequences of residual smallness alone.
-/

namespace Purelib.Riemann.Normalization.TransportedFaceInverseModels

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial (OverlapReady)
open Purelib.Riemann.Normalization.RegularFaceInverseModels
  (Clearance Bounds CellGeometry SeededCell)
open Purelib.Riemann.Normalization.OwnerSeededInverseRoot (Owner)
open Purelib.Riemann.Normalization.AlignedInverseRootSeed (AlignedSeed)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {polynomial : Polynomial} {box : Box} {clearance : Clearance polynomial box}
  {bounds : Bounds clearance}

open Purelib.Polynomial in
open Purelib.Riemann.Paths in
set_option genInjectivity false in
/-- A small-cell inverse model retaining its original continuation route, traced owner and aligned seed.

The route joins the original outer anchor to the cell anchor. The stored model is exactly the constant polynomial of the
aligned terminal seed, with the original cell geometry retained. -/
structure TransportedCell (bounds : Bounds clearance) (source : Owner (polynomial.eval box.anchor)) (inner : Box) where
  /-- The retained original cell refinement and smallness certificate. -/ geometry : CellGeometry bounds inner
  /-- The retained cleared route from the original outer anchor to the cell anchor. -/ route : ClearBoxPaths.Route
    polynomial box box.anchor inner.anchor
  /-- The original traced route starting at the supplied source owner. -/ traced : TracedPath route.path source
  /-- The retained aligned seed of the exact traced terminal owner. -/ aligned : AlignedSeed traced.finishOwner
  /-- The original cell inverse-root model, or its exact retained request refinement. -/ model : Model polynomial inner
  /-- The model value is exactly the constant polynomial of the retained aligned seed. -/ value_eq : model.value =
    Dense.Basic.DensePolynomial.constant aligned.seed.value

constructive_injectivity TransportedCell

namespace TransportedCell

variable {source : Owner (polynomial.eval box.anchor)} {inner : Box}

open Purelib.Approximation in
open Purelib.Data in
/-- Take two fixed Newton refinements to enter the automatic overlap budget.

The retained model's smallness proves the refined bound is at most one divided by 256 throughout the same cell. -/
@[expose] def overlapReady (cell : TransportedCell bounds source inner) : OverlapReady polynomial inner :=
  ⟨cell.model.refine 2, by
    rw [Model.refine_bound, Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
    exact (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct cell.model.bound_small
      (by decide +kernel : (0 : Coordinate) ≤ (1 / 4) ^ 2)).trans
      (by decide +kernel : (1 / 16 : Coordinate) * (1 / 4) ^ 2 ≤ 1 / 256)⟩

section
open Purelib.Riemann.Paths
/-- Build the original small-cell inverse model from a retained route, trace and aligned terminal seed.

The constructor preserves those exact inputs and uses the cell anchor and its containment certificate to form the seeded
model. -/
@[expose] def ofTraced (geometry : CellGeometry bounds inner)
    (route : ClearBoxPaths.Route polynomial box box.anchor inner.anchor)
    (traced : TracedPath route.path source) (aligned : AlignedSeed traced.finishOwner) :
    TransportedCell bounds source inner :=
  let cell := SeededCell.ofSeed geometry inner.anchor inner.contains_anchor aligned.seed
  ⟨geometry, route, traced, aligned, cell.model, cell.value_eq⟩

/-- Continue the original anchor owner to a small cell and retain its aligned inverse-root model.

The cleared box route and traced path determine the exact terminal owner; its aligned seed is passed to the original
cell-model constructor. -/
@[expose] def acquire (geometry : CellGeometry bounds inner) (source : Owner (polynomial.eval box.anchor)) :
    TransportedCell bounds source inner :=
  let route := ClearBoxPaths.Route.build clearance box.anchor inner.anchor box.contains_anchor
    (geometry.refines.contains inner.contains_anchor)
  let traced := TracedPath.build route.path route.within source
  ofTraced geometry route traced (AlignedSeed.ofOwner traced.finishOwner)

end

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Normalization in
/-- A refined cell model and an approximate root in the aligned owner's box satisfy the retained anchor mismatch bound.

The original residual bound is nonnegative and at most one over 4096; the estimate keeps the geometric model refinement
term and sixteen times that residual separately. -/
theorem refine_anchor_mismatch (cell : TransportedCell bounds source inner)
    (root : Gaussian) (inside : cell.aligned.seed.owner.track.initial.box.Contains root)
    {rootError : Coordinate} (nonnegative : 0 ≤ rootError) (small : rootError ≤ 1 / 4096)
    (residual : Data.Gaussian.Norm.Basic.normSq (root ^ 2 - polynomial.eval inner.anchor) ≤ rootError *
      Data.Gaussian.Norm.Basic.normSq (polynomial.eval inner.anchor))
    (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (1 - root * (cell.model.refine index).value.eval inner.anchor) ≤
      Geometric.Basic.quarterRadius (1 / 256) index + 16 * rootError := by
  apply InverseRootComparison.Model.refine_mismatch_bound
    (initialBound := (1 / 256 : Fraction.Rational)) cell.model inner.anchor inner.contains_anchor root nonnegative
      residual
  · rw [cell.value_eq, Dense.Basic.DensePolynomial.eval_constant]
    have scalar := cell.aligned.aligned root inside
    simpa only [Norm.Basic.normSq_eq_canonical] using scalar
  · exact (add_le_add le_rfl
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small (by decide))).trans
        (by decide +kernel : (1 / 256 : Coordinate) + 16 * (1 / 4096) ≤ 1 / 64)

set_option genInjectivity false in
/-- A refined model request retaining its exact refinement index and strict target accuracy.

The stored model is the original transported cell model at the retained index, so the request preserves its seed and
geometric ownership. -/
structure Request (cell : TransportedCell bounds source inner) (target : Coordinate) where
  /-- The retained original model refinement index. -/ index : Nat
  /-- The original cell inverse-root model, or its exact retained request refinement. -/ model : Model polynomial inner
  /-- The request model equals the original cell model refined at its stored index. -/ model_eq : model =
    cell.model.refine index
  /-- The stored request model bound is strictly below the original target. -/ accurate : model.bound < target

constructive_injectivity Request

namespace Request

open Purelib.Approximation.Rational in
/-- Choose the first geometric refinement of the original cell model below the positive target.

The request caches that exact model refinement and its defining equation, with the search certificate transferred to the
stored bound. -/
@[expose] def build (cell : TransportedCell bounds source inner) (target : Coordinate) (positive : 0 < target) :
    Request cell target :=
  let index := Geometric.Search.firstQuarterBelow cell.model.bound 0 target
  let model := cell.model.refine index
  ⟨index, model, rfl, by
    rw [Model.refine_bound]
    exact Geometric.Search.firstQuarterBelow_accurate _ cell.model.bound_nonnegative 0 _ positive⟩

open Purelib.Data.Gaussian in
/-- The requested model's inverse-root residual is strictly below its target at every point of the original cell. -/
theorem residual_lt {cell : TransportedCell bounds source inner} {target : Coordinate}
    (request : Request cell target) (point : Gaussian) (inside : inner.Contains point) :
    Data.Gaussian.Norm.Basic.normSq (1 - polynomial.eval point * (request.model.value.eval point) ^ 2) < target := by
  rw [← request.model.residual_eq]
  have scalar := (request.model.residualBound point inside).trans_lt request.accurate
  simpa only [Norm.Basic.normSq_eq_canonical] using scalar

end Request

section
open Purelib
open Purelib.Approximation
open Purelib.Geometry
open Purelib.Data.Rat
open Purelib.Riemann.Normalization
open Purelib.Riemann.Paths
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Readings.PreparedObservationNeighborhoods (ObservationNeighborhood)
open Purelib.Riemann.Normalization.OwnerSeededInverseRoot (SeededNeighborhood)

/-- Equivalent retained roots give nearest inverse-model values at the cell anchor.

The auxiliary neighborhood uses the acquired cell seed. The two models may
have different boxes and independent refinement indices; their root and
polynomial sign remain those of the supplied owners. -/
theorem anchor_nearest {polynomial : InverseRootPolynomial.Polynomial} {box inner : InverseRootPolynomial.Box}
    {clearance : RegularFaceInverseModels.Clearance polynomial box} {bounds : RegularFaceInverseModels.Bounds clearance}
    {source : OwnerSeededInverseRoot.Owner (polynomial.eval box.anchor)} (cell :
      TransportedFaceInverseModels.TransportedCell bounds source inner)
    {count : Nat} {patch : ContinuedInverseRoot.ContinuedNeighborhood polynomial count}
    (sample : ContinuedNeighborhood.Point patch inner.anchor) (inside : patch.box.Contains inner.anchor)
    (roots : Gaussian.Equivalence.NamedEquivalent
      (OwnerTraceReadings.ownerName cell.aligned.seed.owner) sample.certificate.value.name)
    (leftIndex rightIndex : Nat) :
    Data.Gaussian.Norm.Basic.normSq ((cell.model.refine leftIndex).value.eval inner.anchor - (patch.base.refine
      rightIndex).value.eval inner.anchor) ≤
      Data.Gaussian.Norm.Basic.normSq ((cell.model.refine leftIndex).value.eval inner.anchor +
        (patch.base.refine rightIndex).value.eval inner.anchor) := by
  let site := ObservationNeighborhood.ofPoint polynomial 0 inner.anchor
    cell.traced.finishOwner.parameterNonzero
  let auxiliary := ContinuedNeighborhood.ofAligned site cell.aligned
  let first : ContinuedNeighborhood.Point auxiliary inner.anchor :=
    ContinuedNeighborhood.Point.ofOwner cell.aligned.seed.owner (Rational.Box.refines_refl _)
  have equal : cell.model.value.eval inner.anchor = auxiliary.base.model.value.eval inner.anchor := by
    rw [cell.value_eq, auxiliary.base.model_value_eq]
    rfl
  rw [InverseRootPolynomial.Model.refine_eval_eq cell.model auxiliary.base.model inner.anchor equal leftIndex]
  have scalar := first.equivalent_nearest sample auxiliary.center_inside inside roots leftIndex rightIndex
  simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, SeededNeighborhood.refine] using scalar

end

end TransportedCell

end Purelib.Riemann.Normalization.TransportedFaceInverseModels
