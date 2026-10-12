module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Polynomial.Clearance.Box.Region

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
public import Purelib.Riemann.Paths.ClearBoxPathWinding
public import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Tactic.Ring

public section

/-!
# Actual clear routes across the reciprocal collar

The box between an inverse point and its scaled-conjugate point lies in the
same clear collar. Thus the existing axis-path integrator and owner trace can
cross it, starting with the supplied reciprocal owner and retaining the
actual terminal owner. Neither a fresh root label nor an assumed path
clearance is input. This does not yet identify the supplied reciprocal owner
with the scaled original-chart owner, or compare the two chart integrals.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rational

open Purelib.Geometry.Rational.Box

open Purelib.Polynomial.Clearance.Box

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial.Winding

open Purelib.Riemann.Integration

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.ClearBoxPathWinding

open Purelib.Riemann.Paths.ClearBoxPaths

open Purelib.Riemann.Paths.PreparedPathTrace

open Purelib.Riemann.Paths.PreparedPathWinding

open Purelib.Riemann.Paths.PreparedPathWinding.PreparedClearPathModels

open Purelib.Riemann.Paths.TracedPrimitiveNeighborhood

open Purelib.Riemann.Topology

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Gaussian.Scale (scale)
open Purelib.Geometry.Rational.Box.Boundary (OnBoxBoundary)
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar (Data)
open Purelib.Riemann.Paths.PreparedBoundarySegments (ParentOnBoundary)

/-- The smallest axis rectangle containing two displayed rational points.

Each coordinate retains the minimum and maximum of the same two inputs.
The endpoint comparisons certify the original ordered rectangle bounds. -/
@[expose] def betweenBox (first last : Data.Gaussian.Basic.Canonical) : Box :=
  ⟨min first.re last.re, max first.re last.re, min first.im last.im, max first.im last.im,
    (Fraction.Order.Basic.min_le_left _ _).trans (Fraction.Order.Basic.le_max_left _ _),
      (Fraction.Order.Basic.min_le_left _ _).trans (Fraction.Order.Basic.le_max_left _ _)⟩

/-- The first displayed endpoint belongs to its coordinatewise spanning rectangle.

The four retained coordinate bounds compare that endpoint with the
minimum and maximum used in the same spanning rectangle. -/
theorem betweenBox_first (first last : Data.Gaussian.Basic.Canonical) :
  (betweenBox first last).Contains first :=
  ⟨Fraction.Order.Basic.min_le_left _ _, Fraction.Order.Basic.le_max_left _ _, Fraction.Order.Basic.min_le_left _ _,
    Fraction.Order.Basic.le_max_left _ _⟩

/-- The last displayed endpoint belongs to its coordinatewise spanning rectangle.

The four retained coordinate bounds compare that endpoint with the
minimum and maximum used in the same spanning rectangle. -/
theorem betweenBox_last (first last : Data.Gaussian.Basic.Canonical) :
  (betweenBox first last).Contains last :=
  ⟨Fraction.Order.Basic.min_le_right _ _, Fraction.Order.Basic.le_max_right _ _, Fraction.Order.Basic.min_le_right _ _,
    Fraction.Order.Basic.le_max_right _ _⟩

/-- A coordinate between a value and its nonnegative contraction has its square between the endpoint squares.

The scale lies between zero and one. Its sign and the supplied endpoint
bounds give both square comparisons for either sign of the outer value. -/
private theorem squared_coordinate_bounds {factor outer value : Fraction.Rational}
    (factorNonnegative : 0 ≤ factor) (factorUpper : factor ≤ 1)
    (inside : min outer (factor * outer) ≤ value ∧ value ≤ max outer (factor * outer)) :
    (factor * outer) ^ 2 ≤ value ^ 2 ∧ value ^ 2 ≤ outer ^ 2 := by
  have factorSquare := Fraction.Order.Arithmetic.pow_le_pow_direct factorNonnegative factorUpper 2
  rw [one_pow] at factorSquare
  have innerSquare : (factor * outer) ^ 2 ≤ outer ^ 2 := by
    rw [show (factor * outer) ^ 2 = factor ^ 2 * outer ^ 2 by ring1]
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct factorSquare
      (Fraction.Order.Arithmetic.sq_nonneg_direct outer)).trans_eq (by ring1)
  have upper : value ^ 2 ≤ outer ^ 2 := by
    have bound := Rational.Box.sq_le_endpoint_max inside.1 inside.2
    by_cases ordered : outer ≤ factor * outer
    · rw [Fraction.Order.Basic.min_eq_left ordered, Fraction.Order.Basic.max_eq_right ordered] at bound
      exact bound.trans (Fraction.Order.Basic.max_le le_rfl innerSquare)
    · have ordered := (le_total outer (factor * outer)).resolve_left ordered
      rw [Fraction.Order.Basic.min_eq_right ordered, Fraction.Order.Basic.max_eq_left ordered] at bound
      exact bound.trans (Fraction.Order.Basic.max_le innerSquare le_rfl)
  refine ⟨?_, upper⟩
  by_cases nonnegative : 0 ≤ outer
  · have ordered : factor * outer ≤ outer :=
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct factorUpper nonnegative).trans_eq (by ring1)
    rw [Fraction.Order.Basic.min_eq_right ordered, Fraction.Order.Basic.max_eq_left ordered] at inside
    exact Fraction.Order.Arithmetic.pow_le_pow_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct factorNonnegative nonnegative) inside.1 2
  · have nonpositive : outer ≤ 0 := (le_total (0 : Fraction.Rational) outer).resolve_left nonnegative
    have negativeNonnegative : 0 ≤ -outer := by
      simpa only [show -(0 : Fraction.Rational) = 0 by decide] using Fraction.Order.Arithmetic.neg_le_neg_direct
        nonpositive
    have orderedNeg : factor * -outer ≤ -outer :=
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct factorUpper negativeNonnegative).trans_eq (by ring1)
    have ordered : outer ≤ factor * outer := by
      have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct orderedNeg
      simpa only [show -(factor * -outer) = factor * outer by ring1, neg_neg] using reversed
    rw [Fraction.Order.Basic.min_eq_left ordered, Fraction.Order.Basic.max_eq_right ordered] at inside
    have innerNonpositive : factor * outer ≤ 0 := by
      exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct nonpositive factorNonnegative).trans_eq (by
        ring1)
    have innerNegative : 0 ≤ -(factor * outer) := by
      simpa only [show -(0 : Fraction.Rational) = 0 by decide] using Fraction.Order.Arithmetic.neg_le_neg_direct
        innerNonpositive
    have lower := Fraction.Order.Arithmetic.pow_le_pow_direct innerNegative
      (Fraction.Order.Arithmetic.neg_le_neg_direct inside.2) 2
    simpa only [show (-(factor * outer)) ^ 2 = (factor * outer) ^ 2 by ring1,
      show (-value) ^ 2 = value ^ 2 by ring1] using lower

/-- Every point of the full rectangle, not just its diagonal, has norm between those of the two positively collinear
endpoints. -/
theorem betweenBox_norm_bounds {first last point : Data.Gaussian.Basic.Canonical} {factor : Fraction.Rational}
    (factorNonnegative : 0 ≤ factor) (factorUpper : factor ≤ 1) (aligned : last = Scale.scale factor first)
    (inside : (betweenBox first last).Contains point) :
      Data.Gaussian.Norm.Basic.normSq last ≤ Data.Gaussian.Norm.Basic.normSq point ∧
      Data.Gaussian.Norm.Basic.normSq point ≤ Data.Gaussian.Norm.Basic.normSq first := by
  rw [aligned] at inside ⊢
  have real := squared_coordinate_bounds
    factorNonnegative factorUpper ⟨inside.1, inside.2.1⟩
  have imaginary := squared_coordinate_bounds
    factorNonnegative factorUpper inside.2.2
  exact ⟨add_le_add real.1 imaginary.1, add_le_add real.2 imaginary.2⟩

variable {genus : Nat} {curve : HyperellipticCurve genus}

namespace Data

/-- The coordinatewise rectangle joining the original inverse point to its retained collar side point. -/
@[expose] def fiberBox (data : ReciprocalExteriorCollar.Data curve) (source : Data.Gaussian.Basic.Canonical) : Box :=
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport.betweenBox source⁻¹ (data.sidePoint source)

/-- Every point of the original collar fiber rectangle has squared norm between the retained endpoint norms. -/
theorem fiber_norm_bounds (data : ReciprocalExteriorCollar.Data curve) {source point : Data.Gaussian.Basic.Canonical}
    (boundary : Boundary.OnBoxBoundary (Cuts.Ambient curve) source) (inside :
      (fiberBox data source).Contains point) :
    Data.Gaussian.Norm.Basic.normSq (data.sidePoint source) ≤ Data.Gaussian.Norm.Basic.normSq point ∧
      Data.Gaussian.Norm.Basic.normSq point ≤ Data.Gaussian.Norm.Basic.normSq source⁻¹ := by
  have ratioBounds := ReciprocalExteriorCollar.ratio_bounds curve boundary
  exact Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport.betweenBox_norm_bounds ((by
      decide : (0 : Fraction.Rational) ≤ 1 / 2).trans ratioBounds.1) ratioBounds.2
    ((data.sidePoint_eq source).trans (ReciprocalExteriorCollar.chord_eq_scaled_inverse curve
      (PreparedExteriorReciprocal.boundary_nonzero boundary))) inside

/-- The original coordinate and radicand lower bounds hold throughout the collar fiber rectangle. -/
theorem fiber_clearance (data : ReciprocalExteriorCollar.Data curve) {source point : Data.Gaussian.Basic.Canonical}
    (boundary : Boundary.OnBoxBoundary (Cuts.Ambient curve) source) (inside :
      (fiberBox data source).Contains point) :
    data.coordinateBound ≤ Data.Gaussian.Norm.Basic.normSq point ∧
      data.radicandBound ≤ Data.Gaussian.Norm.Basic.normSq ((HyperellipticReciprocal.polynomial curve).eval
        point) := by
  have bounds := fiber_norm_bounds data boundary
    inside
  have endpoint := (data.point_clearance boundary (stage := 1) (by constructor <;> decide)).1
  rw [data.point_eq, ReciprocalExteriorCollar.deform_one curve (PreparedExteriorReciprocal.boundary_nonzero boundary),
    ← data.sidePoint_eq] at endpoint
  have coordinate := endpoint.trans bounds.1
  refine ⟨coordinate, ?_⟩
  rw [data.radicandBound_eq]
  apply ReciprocalExteriorCollar.radicand_lower curve
  · exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounds.2
      (ReciprocalExteriorCollar.radius_square_positive curve).le).trans
        (ReciprocalExteriorCollar.inverse_inDisk curve boundary)
  · rwa [data.coordinateBound_eq] at coordinate

/-- Use the regular reversed-polynomial bound when the reciprocal origin is regular, and the retained collar bound
otherwise. -/
@[expose] def fiberBound (data : ReciprocalExteriorCollar.Data curve) : Fraction.Rational :=
  if HyperellipticReciprocal.originOrder curve = 0 then Data.Gaussian.Norm.Basic.normSq
    curve.polynomial.leadingCoeff / 4 else data.radicandBound

/-- The retained fiber radicand lower bound is strictly positive. -/
theorem fiberBound_positive (data : ReciprocalExteriorCollar.Data curve) : 0 <
  fiberBound data := by
  unfold fiberBound
  split
  · exact Fraction.Order.Field.div_pos_direct
      (Data.Gaussian.Norm.Basic.normSq_pos (DensePolynomial.leadingCoeff_ne_zero curve.nonzero)) (by decide)
  · exact data.radicandBound_positive

/-- A regular reciprocal chart has no coordinate factor to pay. In the branch case the original homogeneous collar lower
bound is retained. -/
theorem fiberBound_lower (data : ReciprocalExteriorCollar.Data curve) {source point : Data.Gaussian.Basic.Canonical}
    (boundary : Boundary.OnBoxBoundary (Cuts.Ambient curve) source) (inside :
      (fiberBox data source).Contains point) :
    fiberBound data ≤
      Data.Gaussian.Norm.Basic.normSq ((HyperellipticReciprocal.polynomial curve).eval point) := by
  unfold fiberBound
  split
  next regular =>
    rw [HyperellipticReciprocal.polynomial_eval, regular, pow_zero, Data.Gaussian.Basic.mul_one]
    apply Reciprocal.Bounds.disk_lower curve.polynomial (BranchIsolation.degreePositive curve)
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (fiber_norm_bounds data boundary inside).2
      (ReciprocalExteriorCollar.radius_square_positive curve).le).trans
        (ReciprocalExteriorCollar.inverse_inDisk curve boundary)
  next => exact (fiber_clearance data boundary
    inside).2

/-- Certify the original reciprocal radicand lower bound throughout the entire fiber rectangle. -/
@[expose] def fiberClearance (data : ReciprocalExteriorCollar.Data curve) {source : Data.Gaussian.Basic.Canonical}
  (boundary : Boundary.OnBoxBoundary (Cuts.Ambient curve) source) :
    Region.RegionClearance (HyperellipticReciprocal.polynomial curve)
      (fiberBox data source) where
  bound := fiberBound data
  positive := fiberBound_positive data
  lower := fun _ inside => fiberBound_lower data
    boundary inside

end Data

set_option genInjectivity false in
/-- Cache the two-axis route and full-rectangle clearance between the retained endpoints.

The rectangle, endpoint witnesses and lower bound belong to the supplied
collar. The original route and those same bounds remain retained together. -/
structure Fiber (data : ReciprocalExteriorCollar.Data curve) (source : Data.Gaussian.Basic.Canonical) where
  /-- The original source point lies on the original ambient boundary. -/ boundary : Boundary.OnBoxBoundary
    (Cuts.Ambient curve) source
  /-- The cached rectangle joining the original reciprocal source and collar side point. -/ box :
    Rational.Box
  /-- The cached rectangle is exactly the original source fiber rectangle. -/ box_eq : box =
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport.Data.fiberBox data source
  /-- The original inverse source point belongs to the cached rectangle. -/ firstInside : box.Contains source⁻¹
  /-- The retained collar side point belongs to the cached rectangle. -/ lastInside : box.Contains (data.sidePoint
    source)
  /-- The reciprocal radicand is uniformly bounded away from zero throughout the cached rectangle. -/ clearance :
    Region.RegionClearance (HyperellipticReciprocal.polynomial curve) box
  /-- The retained clearance uses exactly the original fiber lower bound. -/ clearance_eq : clearance.bound =
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport.Data.fiberBound data
  /-- The cached two-axis clear route from the original inverse point to the retained side point. -/ route :
    ClearBoxPaths.Route (HyperellipticReciprocal.polynomial curve) box source⁻¹ (data.sidePoint source)

constructive_injectivity Fiber

namespace Fiber

variable {data : Data curve} {source :
  Purelib.Data.Gaussian.Basic.Canonical}

/-- Cache the fiber rectangle, its exact clearance and the two-axis route between the original retained endpoints. -/
@[expose] def build (data : ReciprocalExteriorCollar.Data curve) {source : Data.Gaussian.Basic.Canonical} (boundary :
  Boundary.OnBoxBoundary (Cuts.Ambient curve) source) :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport.Fiber data source :=
  let box := Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport.Data.fiberBox data source
  let firstInside := Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport.betweenBox_first source⁻¹
    (data.sidePoint source)
  let lastInside := Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport.betweenBox_last source⁻¹
    (data.sidePoint source)
  let clearance := Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport.Data.fiberClearance data boundary
  ⟨boundary, box, rfl, firstInside, lastInside, clearance, rfl,
    Route.build clearance source⁻¹ (data.sidePoint source) firstInside lastInside⟩

/-- Construct the collar fiber at a bounded parameter of an original boundary edge. -/
@[expose] def ofParent (data : ReciprocalExteriorCollar.Data curve) {differential : Differentials.Basic.Differential
  genus}
    (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential)
    (boundary : PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve))
    {parameter : Fraction.Rational} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
      Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport.Fiber data (parent.edge.point parameter) :=
  build data (boundary.point inside)

/-- The original affine-in-stage collar lies inside this same cleared rectangle. The rectangular route is a covered
replacement, not an unrelated path chosen solely because it has equal endpoints. -/
theorem deform_contains (fiber : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport.Fiber data source)
  {stage : Fraction.Rational} (inside : 0 ≤ stage ∧ stage ≤ 1) :
    fiber.box.Contains (data.point source stage) := by
  rw [data.point_eq, ReciprocalExteriorCollar.deform_affine curve (PreparedExteriorReciprocal.boundary_nonzero
    fiber.boundary),
    ← data.sidePoint_eq]
  have segment := Rational.Box.contains_line fiber.firstInside fiber.lastInside inside
  have same : Affine.line source⁻¹ (data.sidePoint source - source⁻¹) stage =
      source⁻¹ + Scale.scale stage (data.sidePoint source - source⁻¹) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Affine.line, Cast.ofCoordinate_re, Cast.ofCoordinate_im,
        Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im, Scale.scale_re, Scale.scale_im] <;> ring1
  rwa [same] at segment

/-- The supplied owner is the starting occurrence. The integrator's retained trace ends at the owner subsequently passed
to the reciprocal patch. -/
@[expose] def transport (fiber : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport.Fiber data source)
    (owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval source⁻¹)) :
    PreparedPathTrace.TracedPath fiber.route.path owner :=
  TracedPath.build fiber.route.path fiber.route.within owner

/-- The retained fiber route winding is the difference of its endpoint winding potentials in the same cleared box. -/
theorem winding (fiber : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport.Fiber data source) :
    ClearPath.rawWinding fiber.route.path =
    ClearBoxPaths.windingPotential
        (HyperellipticReciprocal.polynomial curve) fiber.box (data.sidePoint source) -
      ClearBoxPaths.windingPotential
        (HyperellipticReciprocal.polynomial curve) fiber.box source⁻¹ :=
  Route.winding fiber.clearance
    (BranchIsolation.degreePositive
      (HyperellipticReciprocalCurve.reciprocalCurve curve)) fiber.route fiber.firstInside

/-- The retained owner trace winding equals the winding of the original fiber route. -/
theorem transport_winding (fiber : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport.Fiber data source)
    (owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval source⁻¹)) :
    Polygon.Basic.chainRaw (HyperellipticReciprocal.polynomial curve) source⁻¹ (fiber.transport
      owner).trace.get.vertices =
      ClearPath.rawWinding fiber.route.path :=
  TracedPath.winding_original
    (fiber.transport owner)

/-- The endpoint primitive is prepared from this transport's retained owner, with an operational same-root certificate
already in `Neighborhood`. -/
@[expose] def terminalNeighborhood (fiber : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport.Fiber data
  source)
    {owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval source⁻¹)}
    (traced : PreparedPathTrace.TracedPath fiber.route.path owner) (count : Nat) :
    TracedPrimitiveNeighborhood.Neighborhood traced count :=
  Neighborhood.build traced count

end Fiber
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport
