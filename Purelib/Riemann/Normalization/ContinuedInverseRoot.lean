module
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Geometry.Rational.Box.Sum
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Riemann.Normalization.InverseRootComparison
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.RootContinuation.SquareRootContinuation

public import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance.Transport
public import Purelib.Riemann.Normalization.AlignedInverseRootSeed
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Geometry.Rational.Box.Square.Centered

open Purelib.Data.Rat.Fraction.Order

public section

/-!
# Polynomial models on a continued operational sheet

Shrink the coordinate box to the retained root owner's continuation clearance.
Every point in this box admits a finite Rouché continuation from that same
owner, and every operational candidate remains aligned with the polynomial
seed.  Point owners are cached separately, so generated owners can be checked
by containment instead of equality with the canonical continuation algorithm.
-/

namespace Purelib.Riemann.Normalization.ContinuedInverseRoot

open Purelib.Riemann.Normalization.OwnerSeededInverseRoot (SeededNeighborhood Owner)
open Purelib.Riemann.Normalization.AlignedInverseRootSeed (AlignedSeed)
open Purelib.Riemann.Readings.PreparedObservationNeighborhoods (ObservationNeighborhood)
open Purelib.Riemann.Readings.PreparedObservationNeighborhoods (variationRadius variationRadius_positive
  variation_error_le_quarter centeredBox_refines centeredBox_center centeredBox_proper)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Readings.PreparedObservationPoints

open Purelib.Data.Rat in
/-- The exact rational field used for continuation and inverse-error bounds. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
private abbrev Gaussian := Basic.Canonical
/-- The original rational box carrier with retained coordinate bounds. -/
private abbrev Box := Geometry.Rational.Box

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
set_option genInjectivity false in
/-- An aligned seeded neighborhood with a certified continuation radius and uniform root-norm lower bound.

The retained seed owner refines the original origin owner. The continuation allowance is the minimum of its initial
contour and four ambient-side clearances, and all parameter movements on the exact centered box lie strictly below it.
-/
structure ContinuedNeighborhood (polynomial : Polynomial) (count : Nat) where
  /-- The original aligned seeded observation neighborhood and its inverse-root model. -/ base : SeededNeighborhood
    polynomial count
  /-- The original root owner at the seeded site's exact center evaluation. -/ origin : Owner (polynomial.eval
    base.site.center)
  /-- The retained seed-owner box refines the original origin-owner box. -/ owner_refines :
    base.seed.owner.track.initial.box.Refines origin.track.initial.box
  /-- Every root in the retained seed-owner box has squared seed mismatch at most one two-hundred-fifty-sixth. -/
    aligned : forall root, base.seed.owner.track.initial.box.Contains root ->
    normSq (1 - root * base.seed.value) <= 1 / 256
  /-- The retained common contour and ambient-side clearance allowance. -/ continuationAllowance : Fraction.Rational
  /-- The allowance equals the exact minimum of the original contour and four ambient-side clearances. -/
    continuationAllowance_eq : continuationAllowance = min base.seed.owner.track.initial.clearance.bound
    (min base.seed.owner.track.initial.ambientLeftClearance.bound
      (min base.seed.owner.track.initial.ambientRightClearance.bound
        (min base.seed.owner.track.initial.ambientBottomClearance.bound
          base.seed.owner.track.initial.ambientTopClearance.bound)))
  /-- The retained common continuation allowance is strictly positive. -/ continuationAllowance_positive : 0 <
    continuationAllowance
  /-- The retained positive centered continuation radius. -/ radius : Fraction.Rational
  /-- The retained radius is no larger than the original seeded-neighborhood radius. -/ radius_bound : radius ≤
    base.radius
  /-- The retained continuation radius is strictly positive. -/ radius_positive : 0 < radius
  /-- The exact centered box carrying the continuation movement certificate. -/ box : Geometry.Rational.Box
  /-- The box is centered at the original observation point with the retained radius. -/ box_eq : box =
    BoxTransport.centeredBox base.site.center radius radius_positive.le
  /-- Every point of the retained box has parameter movement strictly below the exact continuation allowance. -/
    movement_small : ∀ point, box.Contains point →
    normSq (polynomial.eval base.site.center - polynomial.eval point) < continuationAllowance
  /-- The cached positive lower bound on squared norms of roots in the original seed-owner box. -/ rootLower :
    Fraction.Rational
  /-- The root lower bound equals one quarter divided by the original seed norm squared plus one. -/ rootLower_eq :
    rootLower = (1 / 4) / (normSq base.seed.value + 1)
  /-- The cached root squared-norm lower bound is strictly positive. -/ rootLower_positive : 0 < rootLower

constructive_injectivity ContinuedNeighborhood

namespace ContinuedNeighborhood

variable {polynomial : Polynomial} {count : Nat}

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
/-- A radius bounded by the seed and variation radii makes polynomial movement smaller than the continuation allowance.

The exact centered box refines the retained observation ambient box.
Its original Lipschitz slope and squared diagonal pay at most one quarter
of the positive allowance, giving the strict movement inequality. -/
theorem movement_of_radius (base : SeededNeighborhood polynomial count)
    {allowance radius : Fraction.Rational} (allowancePositive : 0 < allowance)
    (radiusNonnegative : 0 ≤ radius) (baseBound : radius ≤ base.radius)
    (variationBound : radius ≤ variationRadius allowance base.site.denominatorSlope)
    {point : Basic.Canonical}
    (inside : (BoxTransport.centeredBox base.site.center radius radiusNonnegative).Contains point) :
    normSq (polynomial.eval base.site.center - polynomial.eval point) < allowance := by
  have movement := base.site.denominator_movement_le radiusNonnegative
    (baseBound.trans base.radius_le_site) inside
  have paid := variation_error_le_quarter base.site.denominatorSlope_positive.le radiusNonnegative variationBound
  apply (movement.trans paid).trans_lt
  have strict := Arithmetic.mul_lt_mul_of_pos_left_direct
    allowancePositive (by decide : (1 / 4 : Fraction.Rational) < 1)
  simpa only [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.one_mul,
    Fraction.Field.mul_one_direct] using strict

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
/-- Construct a continued neighborhood from an original seeded site, origin owner and uniform seed alignment.

The radius uses the exact minimum of the retained contour and ambient-side clearances; the root lower bound is one
quarter divided by the seed norm squared plus one. -/
@[expose] def ofSeeded (base : SeededNeighborhood polynomial count)
    (origin : Owner (polynomial.eval base.site.center))
    (refines : base.seed.owner.track.initial.box.Refines origin.track.initial.box)
    (aligned : forall root, base.seed.owner.track.initial.box.Contains root ->
      normSq (1 - root * base.seed.value) <= 1 / 256) : ContinuedNeighborhood polynomial count :=
  let allowance := min base.seed.owner.track.initial.clearance.bound
    (min base.seed.owner.track.initial.ambientLeftClearance.bound
      (min base.seed.owner.track.initial.ambientRightClearance.bound
        (min base.seed.owner.track.initial.ambientBottomClearance.bound
          base.seed.owner.track.initial.ambientTopClearance.bound)))
  have allowancePositive : 0 < allowance := Basic.lt_min base.seed.owner.track.initial.clearance.positive
    (Basic.lt_min base.seed.owner.track.initial.ambientLeftClearance.positive
      (Basic.lt_min base.seed.owner.track.initial.ambientRightClearance.positive
        (Basic.lt_min base.seed.owner.track.initial.ambientBottomClearance.positive
          base.seed.owner.track.initial.ambientTopClearance.positive)))
  let radius := min base.radius (variationRadius allowance base.site.denominatorSlope)
  have positive : 0 < radius := Basic.lt_min base.radius_positive
    (variationRadius_positive allowancePositive base.site.denominatorSlope_positive.le)
  { base := base
    origin := origin
    owner_refines := refines
    aligned := aligned
    continuationAllowance := allowance
    continuationAllowance_eq := rfl
    continuationAllowance_positive := allowancePositive
    radius := radius
    radius_bound := Basic.min_le_left _ _
    radius_positive := positive
    box := BoxTransport.centeredBox base.site.center radius positive.le
    box_eq := rfl
    movement_small := fun _ inside => movement_of_radius base allowancePositive positive.le
      (Basic.min_le_left _ _) (Basic.min_le_right _ _) inside
    rootLower := (1 / 4) / (normSq base.seed.value + 1)
    rootLower_eq := rfl
    rootLower_positive := Field.div_pos_direct (by decide)
      (Arithmetic.add_pos_of_nonneg_of_pos_direct (normSq_nonneg _) (by decide)) }

open Purelib.Data.Rat in
/-- The original seeded continuation radius retains its exact variation-radius payment.

The original constructor takes the minimum of the seeded radius and this
same allowance-dependent radius. Reading that scalar minimum keeps the
complete seed, origin and alignment owners unchanged.
-/
theorem ofSeeded_radius_le_variation (base : SeededNeighborhood polynomial count)
    (origin : Owner (polynomial.eval base.site.center))
    (refines : base.seed.owner.track.initial.box.Refines origin.track.initial.box)
    (aligned : ∀ root, base.seed.owner.track.initial.box.Contains root →
      normSq (1 - root * base.seed.value) ≤ 1 / 256) :
    (ofSeeded base origin refines aligned).radius ≤
      variationRadius (ofSeeded base origin refines aligned).continuationAllowance base.site.denominatorSlope :=
  Basic.min_le_right _ _

open Purelib.Data.Gaussian in
/-- The retained continued box has a weak movement ceiling from its identical original slope and radius.

The box equality and retained radius inclusion specialize the original
observation-site estimate without replacing the neighborhood or querying
its point owners.
-/
theorem movement_le (patch : ContinuedNeighborhood polynomial count) {point : Basic.Canonical}
    (inside : patch.box.Contains point) :
    normSq (polynomial.eval patch.base.site.center - polynomial.eval point) ≤
      patch.base.site.denominatorSlope * (8 * patch.radius ^ 2) := by
  have retained := inside
  rewrite [patch.box_eq] at retained
  exact patch.base.site.denominator_movement_le patch.radius_positive.le
    (patch.radius_bound.trans patch.base.radius_le_site) retained

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
/-- Replace the continued box by a supplied positive radius with retained base containment and pointwise movement
evidence.

The original seeded site, root owner, alignment, continuation allowance and root lower bound remain those of the
supplied neighborhood. -/
@[expose] def withRadius (patch : ContinuedNeighborhood polynomial count) (radius : Fraction.Rational)
    (positive : 0 < radius) (baseBound : radius ≤ patch.base.radius)
    (movement : ∀ point, (BoxTransport.centeredBox patch.base.site.center radius
      positive.le).Contains point →
      normSq (polynomial.eval patch.base.site.center - polynomial.eval point) < patch.continuationAllowance) :
    ContinuedNeighborhood polynomial count :=
  { patch with
    radius := radius
    radius_bound := baseBound
    radius_positive := positive
    box := BoxTransport.centeredBox patch.base.site.center radius positive.le
    box_eq := rfl
    movement_small := movement }

section
open Purelib.Riemann.Normalization
/-- Build the continued neighborhood from a retained aligned seed for the original observation site's root owner. -/
@[expose] def ofAligned (site : ObservationNeighborhood polynomial count)
    {origin : Owner (polynomial.eval site.center)} (aligned : AlignedSeed origin) :
    ContinuedNeighborhood polynomial count :=
  ofSeeded (SeededNeighborhood.ofSeed site aligned.seed) origin aligned.refines aligned.aligned

/-- Align a seed to the original observation owner and construct its continued neighborhood. -/
@[expose] def ofOwner (site : ObservationNeighborhood polynomial count)
    (origin : Owner (polynomial.eval site.center)) : ContinuedNeighborhood polynomial count :=
  ofAligned site (AlignedSeed.ofOwner origin)

end

/-- The continuation radius is bounded by the original seeded-neighborhood radius. -/
theorem radius_le_base (patch : ContinuedNeighborhood polynomial count) : patch.radius <= patch.base.radius :=
  patch.radius_bound

/-- The continuation radius is bounded by the original observation-site radius. -/
theorem radius_le_site (patch : ContinuedNeighborhood polynomial count) : patch.radius <= patch.base.site.radius := by
  exact patch.radius_le_base.trans patch.base.radius_le_site

/-- The continued neighborhood's positive centered box has strictly increasing coordinate intervals. -/
theorem box_proper (patch : ContinuedNeighborhood polynomial count) : patch.box.Proper := by
  rw [patch.box_eq]; exact centeredBox_proper _ patch.radius_positive

/-- The continued neighborhood's retained box refines the original seeded box. -/
theorem box_refines (patch : ContinuedNeighborhood polynomial count) : patch.box.Refines patch.base.box := by
  rw [patch.box_eq, patch.base.box_eq]
  exact centeredBox_refines _ patch.radius_positive.le patch.base.radius_positive.le patch.radius_le_base

/-- The original observation center belongs to the continued neighborhood's exact box. -/
theorem center_inside (patch : ContinuedNeighborhood polynomial count) : patch.box.Contains patch.base.site.center := by
  rw [patch.box_eq]; exact centeredBox_center _ _

open Purelib.Data.Gaussian in
/-- Every point in the continued box retains the original denominator squared-norm lower bound. -/
theorem parameter_lower (patch : ContinuedNeighborhood polynomial count) {point : Basic.Canonical}
    (inside : patch.box.Contains point) : patch.base.site.denominatorValue / 4 <= normSq (polynomial.eval point) := by
  rw [patch.box_eq] at inside
  exact patch.base.site.denominator_lower patch.radius_positive.le patch.radius_le_site inside

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The original polynomial is nonzero at every supplied point of the continued box. -/
theorem parameter_nonzero (patch : ContinuedNeighborhood polynomial count) {point : Basic.Canonical}
    (inside : patch.box.Contains point) : polynomial.eval point ≠ 0 := by
  have positive : 0 < normSq (polynomial.eval point) :=
    (Field.div_pos_direct patch.base.site.denominatorValue_positive (by decide)).trans_le
      (patch.parameter_lower inside)
  intro zero
  rw [zero, normSq_zero] at positive
  exact (lt_irrefl _ positive)

open Purelib.Data.Gaussian in
/-- Polynomial movement from the original center is strictly below the retained continuation allowance. -/
theorem parameter_movement_allowance (patch : ContinuedNeighborhood polynomial count) {point : Basic.Canonical}
    (inside : patch.box.Contains point) :
    normSq (polynomial.eval patch.base.site.center - polynomial.eval point) <
      patch.continuationAllowance := patch.movement_small point inside

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Polynomial movement from the original center is below the seed owner's initial contour clearance.

The retained movement certificate bounds the same centered-box evaluation
difference by the unchanged minimum of contour and ambient clearances. -/
theorem parameter_movement (patch : ContinuedNeighborhood polynomial count) {point : Basic.Canonical}
    (inside : patch.box.Contains point) :
    normSq (polynomial.eval patch.base.site.center - polynomial.eval point) <
      patch.base.seed.owner.track.initial.clearance.bound :=
  (patch.parameter_movement_allowance inside).trans_le (by
    rw [patch.continuationAllowance_eq]; exact Basic.min_le_left _ _)

open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Direct root-owner transport preserves the original initial box when movement satisfies contour and all four
ambient-side clearances. -/
private theorem directTransport_box {source target : Basic.Canonical} (owner : Owner source)
    (targetNonzero : target ≠ 0)
    (small : normSq (source - target) < owner.track.initial.clearance.bound)
    (leftSmall : normSq (source - target) < owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : normSq (source - target) < owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : normSq (source - target) < owner.track.initial.ambientBottomClearance.bound)
    (topSmall : normSq (source - target) < owner.track.initial.ambientTopClearance.bound) :
    (ExactQuadraticOwnerClearance.directTransport owner targetNonzero (by
        simpa only [Norm.Basic.normSq_eq_canonical]
          using small)).track.initial.box =
      owner.track.initial.box := by
  unfold ExactQuadraticOwnerClearance.directTransport
  by_cases same : source = target
  · subst target
    unfold ExactQuadraticOwnerClearance.reservedTransport
    rw [dif_pos rfl]
  · exact (ExactQuadraticOwnerClearance.reservedTransportAmbientCache owner targetNonzero (by
      simpa only [Norm.Basic.normSq_eq_canonical]
        using small) 0
      same (by simpa only [Norm.Basic.normSq_eq_canonical] using leftSmall) (by
          simpa only [Norm.Basic.normSq_eq_canonical]
            using rightSmall) (by
            simpa only [Norm.Basic.normSq_eq_canonical]
              using bottomSmall) (by simpa only [Norm.Basic.normSq_eq_canonical] using topSmall)
      (SquareRootContinuation.transportedOwner owner.track.initial (by
          simpa only [Norm.Basic.normSq_eq_canonical]
            using small)).clearance.positive).initialBox

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Every root sample in the retained seed-owner box has squared norm at least the cached positive floor.

The original alignment bound supplies a positive product of root and seed
quadrances. Division by the seed quadrance plus one gives the unchanged floor. -/
theorem root_lower (patch : ContinuedNeighborhood polynomial count) {root : Basic.Canonical}
    (inside : patch.base.seed.owner.track.initial.box.Contains root) : patch.rootLower <= normSq root := by
  have alignment := patch.aligned root inside
  have lower := Norm.Bounds.half_normSq_sub_le_normSq_sub (1 : Basic.Canonical) (1 - root * patch.base.seed.value)
  have identity : (1 : Basic.Canonical) - (1 - root * patch.base.seed.value) = root * patch.base.seed.value := by ring1
  simp only [Norm.Basic.normSq_eq_canonical] at lower
  rw [identity,
      normSq_mul, show normSq (1 : Basic.Canonical) = (1 : Fraction.Rational) by decide] at lower
  have productLower : (1 / 4 : Fraction.Rational) <= normSq root * normSq patch.base.seed.value := by
    calc
      _ <= (1 / 2 : Fraction.Rational) - 1 / 256 := by decide +kernel
      _ <= (1 / 2 : Fraction.Rational) - normSq (1 - root * patch.base.seed.value) :=
        Arithmetic.sub_le_sub_left_direct alignment _
      _ <= _ := lower
  rw [patch.rootLower_eq]
  apply (Field.div_le_iff_pos
    (Arithmetic.add_pos_of_nonneg_of_pos_direct (normSq_nonneg patch.base.seed.value) (by
      decide))).2
  exact productLower.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (le_add_of_nonneg_right (by decide)) (normSq_nonneg root))

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Two readings inside the same original aligned seed box have a uniformly separated sum.

The retained root floor holds on the entire convex box, so it also bounds
the midpoint of these two actual readings. Neither a new signed window nor
an equality between independently supplied root owners is assumed.
-/
theorem root_sum_lower (patch : ContinuedNeighborhood polynomial count) {first last : Basic.Canonical}
    (firstInside : patch.base.seed.owner.track.initial.box.Contains first)
    (lastInside : patch.base.seed.owner.track.initial.box.Contains last) :
    4 * patch.rootLower ≤ normSq (first + last) := by
  have lower := Geometry.Rational.Box.sum_normSq_lower patch.base.seed.owner.track.initial.box patch.rootLower
    (fun inside => by
      rewrite [Norm.Basic.normSq_eq_canonical]
      exact patch.root_lower inside) firstInside lastInside
  rewrite [Norm.Basic.normSq_eq_canonical] at lower
  exact lower

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- A root owner at the original polynomial's specified point, refining the retained seed-owner box.

The record also caches the exact positive parameter squared norm used to convert relative residual requests into
absolute targets. -/
structure Point (patch : ContinuedNeighborhood polynomial count) (point : Basic.Canonical) where
  /-- The original root owner of the polynomial evaluated at this exact point. -/ owner : Owner (polynomial.eval point)
  /-- This point owner's initial box refines the original neighborhood's seed-owner box. -/ refines :
    owner.track.initial.box.Refines patch.base.seed.owner.track.initial.box
  /-- The cached squared norm of the exact point's polynomial value. -/ parameterNorm : Fraction.Rational
  /-- The cached parameter norm equals the original polynomial evaluation's squared norm. -/ parameterNorm_eq :
    parameterNorm = normSq (polynomial.eval point)
  /-- The exact point's parameter squared norm is strictly positive. -/ parameterNorm_positive : 0 < parameterNorm

constructive_injectivity Point

namespace Point

variable {patch : ContinuedNeighborhood polynomial count} {point : Data.Gaussian.Basic.Canonical}

open Purelib.Data.Gaussian in
/-- Retain a supplied point owner with its original seed-box refinement and exact positive parameter squared norm. -/
@[expose] def ofOwner (owner : Owner (polynomial.eval point))
    (refines : owner.track.initial.box.Refines patch.base.seed.owner.track.initial.box) : Point patch point where
  owner := owner
  refines := refines
  parameterNorm := normSq (polynomial.eval point)
  parameterNorm_eq := rfl
  parameterNorm_positive := by
    have scalar := Norm.Basic.normSq_pos owner.parameterNonzero
    rw [Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar

open Purelib.Data.Gaussian in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Transport the original seed owner directly to a point inside the continued box.

The retained movement bound and parameter nonvanishing supply the exact transport request and refinement to the original
seed box. -/
@[expose] def acquire (patch : ContinuedNeighborhood polynomial count) (point : Basic.Canonical)
    (inside : patch.box.Contains point) : Point patch point :=
  ofOwner (ExactQuadraticOwnerClearance.directTransport patch.base.seed.owner
    (patch.parameter_nonzero inside) (by
      simpa only [Norm.Basic.normSq_eq_canonical] using patch.parameter_movement inside))
    (ExactQuadraticOwnerClearance.directTransport_initial_box_refines patch.base.seed.owner
      (patch.parameter_nonzero inside) (by
        simpa only [Norm.Basic.normSq_eq_canonical] using patch.parameter_movement inside))

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The directly acquired point owner retains the original seed-owner initial box.

The retained continuation allowance bounds each of the contour and four
ambient clearances, so the same direct owner transport preserves this box. -/
theorem acquire_initial_box (patch : ContinuedNeighborhood polynomial count) (point : Basic.Canonical)
    (inside : patch.box.Contains point) :
    (acquire patch point inside).owner.track.initial.box = patch.base.seed.owner.track.initial.box := by
  apply directTransport_box
  all_goals
    apply (patch.parameter_movement_allowance inside).trans_le
    rw [patch.continuationAllowance_eq]
  · exact Basic.min_le_left _ _
  · exact (Basic.min_le_right _ _).trans (Basic.min_le_left _ _)
  · exact (Basic.min_le_right _ _).trans ((Basic.min_le_right _ _).trans
      (Basic.min_le_left _ _))
  · exact (Basic.min_le_right _ _).trans ((Basic.min_le_right _ _).trans
      ((Basic.min_le_right _ _).trans (Basic.min_le_left _ _)))
  · exact (Basic.min_le_right _ _).trans ((Basic.min_le_right _ _).trans
      ((Basic.min_le_right _ _).trans (Basic.min_le_right _ _)))

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- The actual acquired point owner's contour retains the uniform original-seed transport floor.

A finite movement ceiling below the original continuation allowance pays
all four retained ambient-line margins. The exact original acquisition
factory and its selected owner remain unchanged.
-/
theorem acquire_clearance_lower (patch : ContinuedNeighborhood polynomial count) (ceiling : Fraction.Rational)
    (small : ceiling < patch.continuationAllowance) {point : Basic.Canonical} (inside : patch.box.Contains point)
    (paid : normSq (polynomial.eval patch.base.site.center - polynomial.eval point) ≤ ceiling) :
    ExactQuadraticOwnerClearance.transportFloor patch.base.seed.owner ceiling ≤
      (acquire patch point inside).owner.track.initial.clearance.bound := by
  have left : ceiling < patch.base.seed.owner.track.initial.ambientLeftClearance.bound :=
    small.trans_le (by
      rewrite [patch.continuationAllowance_eq]
      exact (Basic.min_le_right _ _).trans (Basic.min_le_left _ _))
  have right : ceiling < patch.base.seed.owner.track.initial.ambientRightClearance.bound :=
    small.trans_le (by
      rewrite [patch.continuationAllowance_eq]
      exact (Basic.min_le_right _ _).trans ((Basic.min_le_right _ _).trans (Basic.min_le_left _ _)))
  have bottom : ceiling < patch.base.seed.owner.track.initial.ambientBottomClearance.bound :=
    small.trans_le (by
      rewrite [patch.continuationAllowance_eq]
      exact (Basic.min_le_right _ _).trans ((Basic.min_le_right _ _).trans
        ((Basic.min_le_right _ _).trans (Basic.min_le_left _ _))))
  have top : ceiling < patch.base.seed.owner.track.initial.ambientTopClearance.bound :=
    small.trans_le (by
      rewrite [patch.continuationAllowance_eq]
      exact (Basic.min_le_right _ _).trans ((Basic.min_le_right _ _).trans
        ((Basic.min_le_right _ _).trans (Basic.min_le_right _ _))))
  have scalarPaid : Norm.Basic.normSq (polynomial.eval patch.base.site.center - polynomial.eval point) ≤ ceiling := by
    rewrite [Norm.Basic.normSq_eq_canonical]
    exact paid
  change ExactQuadraticOwnerClearance.transportFloor patch.base.seed.owner ceiling ≤
    (ExactQuadraticOwnerClearance.directTransport patch.base.seed.owner (patch.parameter_nonzero inside)
      (by simpa only [Norm.Basic.normSq_eq_canonical] using
        patch.parameter_movement inside)).track.initial.clearance.bound
  exact ExactQuadraticOwnerClearance.directTransport_clearance_lower _ _ _ ceiling left right bottom top scalarPaid

/-- Read the certified square-root name of the retained point owner using its original nonzero parameter proof. -/
@[expose] def certificate (sample : Point patch point) := sample.owner.certificate sample.owner.parameterNonzero

/-- Equal inputs to the identical acquisition factory retain the same original certified root name. -/
theorem acquire_name_eq {first last : Data.Gaussian.Basic.Canonical}
    (firstInside : patch.box.Contains first) (lastInside : patch.box.Contains last) (equal : first = last) :
    (acquire patch first firstInside).certificate.value.name =
      (acquire patch last lastInside).certificate.value.name := by
  cases equal
  rfl

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Riemann.RootContinuation
/-- Every possible root of the retained point certificate lies in the original seed-owner box. -/
theorem candidate_inside (sample : Point patch point)
    (state : sample.certificate.value.name.process.State) {root : Basic.Canonical}
    (possible : sample.certificate.value.name.process.Possible state root) :
    patch.base.seed.owner.track.initial.box.Contains root :=
  sample.refines.contains
    (sample.owner.certificate_candidate_in_initial_box sample.owner.parameterNonzero state possible)

/-- Every original raw sample of this actual point owner stays in the same retained seed box. -/
theorem approximation_inside (sample : Point patch point) (index : Nat) :
    patch.base.seed.owner.track.initial.box.Contains
      ((CertifiedSquareRoot.approximation sample.owner.track).sample index) :=
  sample.refines.contains (CertifiedSquareRoot.approximation_sample_initial_inside sample.owner.track index)

/-- A retained seed-box anchor fixes every actual point sample near the same original nonzero reference.

The seed-box diameter is measured against its actual cached root floor.
One retained anchor near the reference controls all other samples in that
same box, even when the uniform seed was reboxed outside a source owner.
-/
theorem approximation_near_reference (sample : Point patch point) (anchor reference : Basic.Canonical)
    (referenceNorm : Fraction.Rational) (normEq : referenceNorm = normSq reference)
    (nonnegative : 0 ≤ referenceNorm)
    (anchorInside : patch.base.seed.owner.track.initial.box.Contains anchor)
    (near : normSq (anchor - reference) ≤ referenceNorm / 64)
    (diameter : patch.base.seed.owner.track.initial.box.diagonalSq ≤ patch.rootLower / 256)
    (index : Nat) :
    normSq ((CertifiedSquareRoot.approximation sample.owner.track).sample index - reference) ≤ referenceNorm / 16 := by
  have anchorBound : normSq anchor ≤ 3 * referenceNorm := by
    have triangle := Norm.Bounds.normSq_add_le_two (anchor - reference) reference
    simp only [Norm.Basic.normSq_eq_canonical] at triangle
    rewrite [show anchor - reference + reference = anchor by ring1] at triangle
    calc
      _ ≤ 2 * (normSq (anchor - reference) + normSq reference) := triangle
      _ ≤ 2 * (referenceNorm / 64 + referenceNorm) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.add_le_add_direct near normEq.ge) (by decide +kernel)
      _ = (2 * ((64 : Fraction.Rational)⁻¹ + 1)) * referenceNorm := by
        simp only [Fraction.Field.div_eq_mul_inv_direct]
        ring1
      _ ≤ 3 * referenceNorm :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel) nonnegative
  have boxBound : patch.base.seed.owner.track.initial.box.diagonalSq ≤ (3 * referenceNorm) / 256 :=
    diameter.trans (Field.divide_mono ((patch.root_lower anchorInside).trans anchorBound) (by decide +kernel))
  have sampleBound :=
    (Geometry.Rational.Box.normSq_sub_le_diagonalSq (sample.approximation_inside index) anchorInside).trans boxBound
  rewrite [Norm.Basic.normSq_eq_canonical] at sampleBound
  have triangle := Norm.Bounds.normSq_sub_le_via
    ((CertifiedSquareRoot.approximation sample.owner.track).sample index) anchor reference
  simp only [Norm.Basic.normSq_eq_canonical] at triangle
  calc
    _ ≤ 2 * (normSq ((CertifiedSquareRoot.approximation sample.owner.track).sample index - anchor) +
        normSq (anchor - reference)) := triangle
    _ ≤ 2 * ((3 * referenceNorm) / 256 + referenceNorm / 64) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct sampleBound near) (by decide +kernel)
    _ = (2 * (3 * (256 : Fraction.Rational)⁻¹ + (64 : Fraction.Rational)⁻¹)) * referenceNorm := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ ≤ (16 : Fraction.Rational)⁻¹ * referenceNorm :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel) nonnegative
    _ = referenceNorm / 16 := by
      rewrite [Fraction.Field.div_eq_mul_inv_direct]
      ring1

/-- Every possible root of the retained point certificate satisfies the cached root squared-norm lower bound. -/
theorem candidate_lower (sample : Point patch point)
    (state : sample.certificate.value.name.process.State) {root : Basic.Canonical}
    (possible : sample.certificate.value.name.process.Possible state root) : patch.rootLower <= normSq root :=
  patch.root_lower (sample.candidate_inside state possible)

end

open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Request a root-certificate state at the positive relative error times the exact cached parameter norm. -/
@[expose] def residualState (sample : Point patch point) (error : Fraction.Rational) (positive : 0 < error) :
    sample.certificate.value.name.process.State :=
  CertifiedSquareRoot.residualState sample.owner.parameterNonzero sample.owner.track
    (error * sample.parameterNorm) (Arithmetic.mul_pos_direct positive sample.parameterNorm_positive)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Every possible root at the requested residual state satisfies the original relative squared-residual bound. -/
theorem candidate_residual (sample : Point patch point) (error : Fraction.Rational) (positive : 0 < error)
    {root : Basic.Canonical}
    (possible : sample.certificate.value.name.process.Possible (sample.residualState error positive) root) :
    normSq (root ^ 2 - polynomial.eval point) <= error * normSq (polynomial.eval point) := by
  have residual := CertifiedSquareRoot.residualState_candidate_residual_lt
    sample.owner.parameterNonzero sample.owner.track (error * sample.parameterNorm)
      (Arithmetic.mul_pos_direct positive sample.parameterNorm_positive) possible
  rw [sample.parameterNorm_eq] at residual
  simpa only [pow_two] using residual.le

open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Riemann.Normalization
/-- The refined original inverse-root model has a geometric mismatch bound against every root possible at the retained
residual state.

The bound retains the quarter-scale alignment term and sixteen times the relative root error, with the error at most one
four-thousand-ninety-sixth. -/
theorem polynomial_mismatch (sample : Point patch point) (inside : patch.box.Contains point)
    (error : Fraction.Rational) (positive : 0 < error) (small : error <= 1 / 4096)
    {root : Basic.Canonical}
    (possible : sample.certificate.value.name.process.Possible (sample.residualState error positive) root)
    (index : Nat) :
    normSq (1 - root * (patch.base.refine index).value.eval point) <=
      Geometric.Basic.quarterRadius (1 / 256) index + 16 * error := by
  rw [← Norm.Basic.normSq_eq_canonical]
  apply (InverseRootComparison.Model.refine_mismatch_bound patch.base.model) point (patch.box_refines.contains inside)
    root positive.le
    (by simpa only [Norm.Basic.normSq_eq_canonical] using sample.candidate_residual error positive possible)
  · rw [Norm.Basic.normSq_eq_canonical, patch.base.model_value_eq, Dense.Basic.DensePolynomial.eval_constant]
    exact patch.aligned root (sample.candidate_inside _ possible)
  · calc
      _ <= (1 / 256 : Fraction.Rational) + 16 * (1 / 4096) := add_le_add le_rfl
        (Arithmetic.mul_le_mul_of_nonneg_left_direct small (by decide))
      _ <= 1 / 64 := by decide +kernel

/-- Bound the refined polynomial's squared error against the reciprocal of a possible retained root.

Divide the alignment-plus-relative-residual bound by the original neighborhood's positive root lower bound, keeping the
exact point and root-certificate state. -/
theorem polynomial_inverse_error (sample : Point patch point) (inside : patch.box.Contains point)
    (error : Fraction.Rational) (positive : 0 < error) (small : error <= 1 / 4096)
    {root : Basic.Canonical}
    (possible : sample.certificate.value.name.process.Possible (sample.residualState error positive) root)
    (index : Nat) :
    normSq ((patch.base.refine index).value.eval point - inv root) <=
      (Geometric.Basic.quarterRadius (1 / 256) index + 16 * error) / patch.rootLower := by
  have rootPositive := patch.rootLower_positive.trans_le (sample.candidate_lower _ possible)
  have rootNonzero : root ≠ 0 := by
    intro zero
    rw [zero, normSq_zero] at rootPositive
    exact (lt_irrefl _ rootPositive)
  have initial : normSq (1 - root * patch.base.model.value.eval point) <= 1 / 256 := by
    rw [patch.base.model_value_eq, Dense.Basic.DensePolynomial.eval_constant]
    exact patch.aligned root (sample.candidate_inside _ possible)
  have budgetSmall : (1 / 256 : Fraction.Rational) + 16 * error <= 1 / 64 := by
    calc
      _ <= (1 / 256 : Fraction.Rational) + 16 * (1 / 4096) := add_le_add le_rfl
        (Arithmetic.mul_le_mul_of_nonneg_left_direct small (by decide))
      _ <= 1 / 64 := by decide +kernel
  have comparison := (InverseRootComparison.Model.refine_inverse_error patch.base.model) point
    (patch.box_refines.contains inside)
    root rootNonzero positive.le (by
      simpa only [Norm.Basic.normSq_eq_canonical] using sample.candidate_residual error positive possible)
    (by simpa only [Norm.Basic.normSq_eq_canonical] using initial) budgetSmall index
  simp only [Norm.Basic.normSq_eq_canonical] at comparison
  have inverse_eq : Field.inv root = inv root := by
    with_unfolding_all exact (Field.inv_eq root).symm
  rw [inverse_eq] at comparison
  exact comparison.trans (Field.div_le_div_of_nonneg_left_direct
    (add_nonneg (Geometric.Basic.quarterRadius_nonneg (by decide +kernel) index)
      (Arithmetic.mul_nonneg_direct (by decide) positive.le))
    patch.rootLower_positive (sample.candidate_lower _ possible))

end Point

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- The indexed quarter-radius relative root error starting at one four-thousand-ninety-sixth. -/
@[expose] def relativeRootError (index : Nat) : Fraction.Rational := Geometric.Basic.quarterRadius (1 / 4096) index

section
open Purelib.Approximation.Rational
/-- Every scheduled relative root error is strictly positive. -/
theorem relativeRootError_positive (index : Nat) : 0 < relativeRootError index :=
  Geometric.Basic.quarterRadius_pos (by decide +kernel) index

/-- Every scheduled relative root error is at most one four-thousand-ninety-sixth. -/
theorem relativeRootError_small (index : Nat) : relativeRootError index <= 1 / 4096 :=
  Geometric.Basic.quarterRadius_le_scale (by decide +kernel) index

end

section
open Purelib.Data.Rat
/-- The inverse-error geometric scale: one one-hundred-twenty-eighth divided by the retained root lower bound. -/
@[expose] def inverseErrorScale (patch : ContinuedNeighborhood polynomial count) : Fraction.Rational :=
  (1 / 128) / patch.rootLower

/-- The retained inverse-error geometric scale is strictly positive. -/
theorem inverseErrorScale_positive (patch : ContinuedNeighborhood polynomial count) : 0 < patch.inverseErrorScale :=
  Field.div_pos_direct (by decide +kernel) patch.rootLower_positive

/-- A scalar sum identity transports two geometric contributions through a common retained divisor.

The variables keep the exact rational constants opaque during ring normalization.
-/
private theorem combine_geometric_scalars (a b c divisor geometric : Fraction.Rational)
    (scalar : a + 16 * b = c) :
    (a * geometric + 16 * (b * geometric)) / divisor = (c / divisor) * geometric := by
  rw [← scalar]
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  ring1

end

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- The scheduled alignment and relative root-error terms combine into the retained inverse-error quarter-radius scale.
-/
private theorem combined_error_eq (patch : ContinuedNeighborhood polynomial count) (index : Nat) :
    (Geometric.Basic.quarterRadius (1 / 256) index + 16 * relativeRootError index) / patch.rootLower =
      Geometric.Basic.quarterRadius patch.inverseErrorScale index := by
  have scalar : (1 / 256 : Fraction.Rational) + 16 * (1 / 4096) = 1 / 128 := by
    change (1 / (256 : Nat) : Fraction.Rational) + (16 : Nat) * (1 / (4096 : Nat)) = 1 / (128 : Nat)
    rw [Fraction.Cast.natCast_eq_fromInt 256, Fraction.Cast.natCast_eq_fromInt 16,
      Fraction.Cast.natCast_eq_fromInt 4096, Fraction.Cast.natCast_eq_fromInt 128]
    decide +kernel
  simp only [relativeRootError, inverseErrorScale, Geometric.Basic.quarterRadius_eq_mul_pow]
  exact combine_geometric_scalars (1 / 256) (1 / 4096) (1 / 128) patch.rootLower
    ((1 / 4 : Fraction.Rational) ^ index) scalar

namespace Point

variable {patch : ContinuedNeighborhood polynomial count} {point : Data.Gaussian.Basic.Canonical}

/-- Reindex the same original Point along equality of its retained neighborhood.

Only the dependent neighborhood index changes. The actual owner, refinement
certificate and cached parameter norm are transported as one complete value;
no acquisition, observation or root preparation occurs.
-/
@[expose] def castPatch {first last : ContinuedNeighborhood polynomial count}
    (equal : first = last) (sample : Point last point) : Point first point :=
  equal.symm ▸ sample

/-- Neighborhood reindexing retains the entire original Point heterogeneously. -/
theorem castPatch_heq {first last : ContinuedNeighborhood polynomial count}
    (equal : first = last) (sample : Point last point) : HEq (castPatch equal sample) sample := by
  cases equal
  rfl

/-- Neighborhood reindexing preserves the exact original named certificate value. -/
theorem castPatch_name {first last : ContinuedNeighborhood polynomial count}
    (equal : first = last) (sample : Point last point) :
    (castPatch equal sample).certificate.value.name = sample.certificate.value.name := by
  cases equal
  rfl

/-- Transport a neighborhood point certificate along equality of its point.

The supplied equality changes only the dependent point index. The retained
owner, seed-box refinement and cached parameter norm are transported together
without rebuilding any observation or owner.
-/
@[expose] def castPoint {patch : ContinuedNeighborhood polynomial count} {first last : InverseRootPolynomial.Gaussian}
    (equal : first = last) (sample : Point patch last) : Point patch first :=
  equal.symm ▸ sample

/-- Point transport retains the certificate's exact named value.

Equality elimination keeps the original certificate and its selected name.
No new point owner, reading or observation is constructed by this transport.
-/
theorem castPoint_name {patch : ContinuedNeighborhood polynomial count} {first last : InverseRootPolynomial.Gaussian}
    (equal : first = last) (sample : Point patch last) :
    (castPoint equal sample).certificate.value.name = sample.certificate.value.name := by
  cases equal
  rfl

/-- Read the original point certificate at the scheduled relative root-error state. -/
@[expose] def readingState (sample : Point patch point) (index : Nat) : sample.certificate.value.name.process.State :=
  sample.residualState (relativeRootError index) (relativeRootError_positive index)

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
/-- Every root possible at the scheduled reading state satisfies the corresponding geometric inverse-error bound. -/
theorem reading_inverse_error (sample : Point patch point) (inside : patch.box.Contains point)
    (index : Nat) {root : Basic.Canonical}
    (possible : sample.certificate.value.name.process.Possible (sample.readingState index) root) :
    normSq ((patch.base.refine index).value.eval point - inv root) <=
      Geometric.Basic.quarterRadius patch.inverseErrorScale index := by
  rw [<- combined_error_eq]
  exact sample.polynomial_inverse_error inside _ (relativeRootError_positive index)
    (relativeRootError_small index) possible index

end Point

section
open Purelib.Approximation.Rational
open Purelib.Data.Rat
/-- Search the retained inverse-error scale for the first quarter-radius index below the requested target. -/
@[expose] def requestIndex (patch : ContinuedNeighborhood polynomial count) (target : Fraction.Rational) : Nat :=
  Geometric.Search.firstQuarterBelow patch.inverseErrorScale 0 target

/-- The selected index makes the retained inverse-error quarter-radius strictly smaller than the positive target. -/
theorem requestIndex_accurate (patch : ContinuedNeighborhood polynomial count) (target : Fraction.Rational)
    (positive : 0 < target) :
    Geometric.Basic.quarterRadius patch.inverseErrorScale (patch.requestIndex target) < target :=
  Geometric.Search.firstQuarterBelow_accurate _ patch.inverseErrorScale_positive.le 0 target positive

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- At the selected reading state, the refined original inverse-root polynomial has squared reciprocal error strictly
below the requested positive target. -/
theorem Point.request_inverse_error {patch : ContinuedNeighborhood polynomial count} {point : Basic.Canonical}
    (sample : Point patch point) (inside : patch.box.Contains point)
    (target : Fraction.Rational) (positive : 0 < target) {root : Basic.Canonical}
    (possible : sample.certificate.value.name.process.Possible
      (sample.readingState (patch.requestIndex target)) root) :
    normSq ((patch.base.refine (patch.requestIndex target)).value.eval point - inv root) < target :=
  (sample.reading_inverse_error inside _ possible).trans_lt (patch.requestIndex_accurate target positive)

end ContinuedNeighborhood

end Purelib.Riemann.Normalization.ContinuedInverseRoot
