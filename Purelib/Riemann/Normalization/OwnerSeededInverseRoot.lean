module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Geometry.Rational.Box.Square.Centered
public import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Basic

public import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.Track.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Owner-backed seeds for finite inverse-root polynomials

A displayed root owner supplies a sufficiently accurate rational root sample.
Dividing that sample by the radicand gives the inverse-root seed.  A computed
positive coordinate radius then makes the first Newton residual small
throughout a box.  The existing observation neighborhood's Horner work is
reused, and no successful-search or residual-smallness input is required.

The owner and the sample's checked membership in its initial box are retained.  Proving that later
polynomial values agree with the continued operational sheet, and turning
their antiderivatives into global primitive samples, are separate steps.
-/

namespace Purelib.Riemann.Normalization.OwnerSeededInverseRoot

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Readings.PreparedObservationPoints
open Purelib.Riemann.Readings.PreparedObservationNeighborhoods (ObservationNeighborhood centeredBox_refines
  centeredBox_proper variationRadius variationRadius_positive variation_error_le_quarter)

open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
private abbrev Gaussian := Basic.Canonical
open Purelib.Data.Rat in
/-- The exact rational coordinate field used for residual bounds. -/
private abbrev Coordinate := Fraction.Rational
/-- The original rational box carrier with retained coordinate bounds. -/
private abbrev Box := Purelib.Geometry.Rational.Box

/-- The original nominal square-root continuation owner of the retained nonzero parameter. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Convert a relative square-root sample residual into the same inverse-square-root seed residual bound.

The seed is the original sample divided by the nonzero parameter; cancellation preserves the exact sample and parameter
identities. -/
theorem seed_residual_le_relative {parameter root : Basic.Canonical} {bound : Fraction.Rational}
    (nonzero : parameter ≠ 0)
    (residualBound : normSq (root * root - parameter) <= bound * normSq parameter) :
    normSq (1 - parameter * (root * inv parameter) ^ 2) <= bound := by
  have identity : (1 - parameter * (root * inv parameter) ^ 2) * parameter =
      -(root * root - parameter) := by
    calc
      _ = parameter - root * root * (parameter * inv parameter) ^ 2 := by ring1
      _ = _ := by
        have cancel : parameter * inv parameter = 1 := by
          with_unfolding_all exact Basic.Canonical.mul_inv_cancel parameter nonzero
        rw [cancel]
        ring1
  have positive := Norm.Basic.normSq_pos nonzero
  rw [Norm.Basic.normSq_eq_canonical] at positive
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := normSq parameter) ?_ positive
  calc
    _ = normSq ((1 - parameter * (root * inv parameter) ^ 2) * parameter) := (Basic.Canonical.normSq_mul _ _).symm
    _ = normSq (root * root - parameter) := by rw [identity, Basic.Canonical.normSq_neg]
    _ <= bound * normSq parameter := residualBound

/-- A square-root residual below parameter norm squared divided by sixty-four gives inverse-root seed residual at most
one sixty-fourth. -/
theorem seed_residual_le {parameter root : Basic.Canonical} (nonzero : parameter ≠ 0)
    (residualBound : normSq (root * root - parameter) <= normSq parameter / 64) :
    normSq (1 - parameter * (root * inv parameter) ^ 2) <= 1 / 64 := by
  apply seed_residual_le_relative nonzero
  simpa only [Fraction.Field.div_eq_mul_inv_direct,
    Fraction.Field.one_mul, Fraction.Field.mul_comm] using residualBound

end

open Purelib.Data.Gaussian in
set_option genInjectivity false in
/-- An inverse-root seed tied to an original root owner and a retained sample inside its initial box.

The value is exactly the sample divided by the original parameter, and both its square-root residual and inverse-root
residual are certified. -/
structure Seed (parameter : Basic.Canonical) where
  /-- The original nominal root owner for this parameter. -/ owner : Owner parameter
  /-- The retained square-root approximation belonging to the original owner's box. -/ rootSample : Basic.Canonical
  /-- The retained sample lies in the original owner's initial box. -/ rootSample_inside :
    owner.track.initial.box.Contains rootSample
  /-- The retained sample's squared residual is at most the parameter norm squared divided by sixty-four. -/
    rootSample_residual : normSq (rootSample * rootSample - parameter) <= normSq parameter / 64
  /-- The retained Gaussian sample or inverse-root seed value specified by this record. -/ value : Basic.Canonical
  /-- The inverse-root seed value is exactly the retained root sample divided by the original parameter. -/ value_eq :
    value = rootSample * inv parameter
  /-- The retained inverse-root seed residual is at most one sixty-fourth. -/ residual_small : normSq (1 - parameter *
    value ^ 2) <= 1 / 64

constructive_injectivity Seed

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- A root sample inside the original owner's initial box with the requested squared-residual bound.

The exact parameter, owner and rational residual request index the retained
sample and its two certificates; no alternative box or root owner is selected. -/
structure OwnerSample {parameter : Basic.Canonical} (owner : Owner parameter) (target : Fraction.Rational) where
  /-- The retained Gaussian sample or inverse-root seed value specified by this record. -/ value : Basic.Canonical
  /-- The retained sample lies in the exact original owner's initial box. -/ inside : owner.track.initial.box.Contains
    value
  /-- The retained sample's squared root residual fits the original requested target. -/ residualBound : normSq (value *
    value - parameter) <= target

constructive_injectivity OwnerSample

namespace OwnerSample

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Riemann.Branches in
/-- The Gaussian point whose coordinates are the midpoints of the original box intervals. -/
def boxCenter (box : Purelib.Geometry.Rational.Box) : Basic.Canonical :=
  ⟨ClearSheetContinuation.midpoint box.xLower box.xUpper,
    ClearSheetContinuation.midpoint box.yLower box.yUpper⟩

open Purelib.Geometry.Rational in
open Purelib.Riemann.Branches in
/-- The coordinate-midpoint point lies in the original box.

The original valid coordinate intervals bound each of their retained rational
midpoints, so all four box inequalities hold for the same center point. -/
theorem boxCenter_inside (box : Purelib.Geometry.Rational.Box) : box.Contains (boxCenter box) :=
  ⟨ClearSheetContinuation.left_le_midpoint box.x_valid,
    ClearSheetContinuation.midpoint_le_right box.x_valid,
    ClearSheetContinuation.left_le_midpoint box.y_valid,
    ClearSheetContinuation.midpoint_le_right box.y_valid⟩

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Acquire a residual-bounded sample from the original owner's box and track.

Use the original box center if it already satisfies the positive target; otherwise retain the certified sample at the
track's selected residual index. -/
def acquire {parameter : Basic.Canonical} (owner : Owner parameter) (target : Fraction.Rational)
    (positive : 0 < target) : OwnerSample owner target :=
  let center := boxCenter owner.track.initial.box
  if accurate : normSq (center * center - parameter) <= target then
    ⟨center, boxCenter_inside _, accurate⟩
  else
    let index := CertifiedSquareRoot.residualIndex owner.track target positive
    let root := (CertifiedSquareRoot.approximation owner.track).sample index
    have inside : owner.track.initial.box.Contains root := by
      change owner.track.initial.box.Contains
        ((CertifiedSquareRoot.approximation owner.track).sample index)
      rw [CertifiedSquareRoot.approximation_sample]
      exact (CoherentRoot.state_refines_of_le owner.track (Nat.zero_le _)).contains
        (CoherentRoot.state owner.track
          (max (CertifiedSquareRoot.baseIndex owner.track) index)).box.contains_anchor
    ⟨root, inside,
      ((CertifiedSquareRoot.sample_residual_le owner.track index).trans
        (CertifiedSquareRoot.residualIndex_accurate owner.track target positive).le)⟩

end OwnerSample

namespace Seed

open Purelib.Data.Gaussian in
/-- Build an inverse-root seed from the original owner and an inside-box sample satisfying its relative residual bound.
-/
def ofSample {parameter : Basic.Canonical} (owner : Owner parameter) (sample : Basic.Canonical)
    (inside : owner.track.initial.box.Contains sample)
    (residualBound : normSq (sample * sample - parameter) <= normSq parameter / 64) : Seed parameter where
  owner := owner
  rootSample := sample
  rootSample_inside := inside
  rootSample_residual := residualBound
  value := sample * inv parameter
  value_eq := rfl
  residual_small := seed_residual_le owner.parameterNonzero residualBound

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Acquire a sample from the original root owner and retain its inverse-root seed.

The positive residual target is the original parameter squared norm divided by sixty-four, preserving the owner and its
initial-box sample evidence. -/
def ofOwner {parameter : Basic.Canonical} (owner : Owner parameter) : Seed parameter :=
  let sample := OwnerSample.acquire owner (normSq parameter / 64)
    (by
      have positive := Norm.Basic.normSq_pos owner.parameterNonzero
      rw [Norm.Basic.normSq_eq_canonical] at positive
      exact Fraction.Order.Field.div_pos_direct positive (by decide +kernel))
  ofSample owner sample.value sample.inside sample.residualBound

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
/-- Bound inverse-root mismatch for another point inside the original owner's initial box.

The bound retains the seed's actual inverse-root residual and the original box diagonal squared times the seed squared
norm. -/
theorem mismatch_le {parameter : Basic.Canonical} (seed : Seed parameter) {root : Basic.Canonical}
    (inside : seed.owner.track.initial.box.Contains root) :
    normSq (1 - root * seed.value) <=
      2 * (normSq (1 - parameter * seed.value ^ 2) +
        seed.owner.track.initial.box.diagonalSq * normSq seed.value) := by
  have centerEq : seed.rootSample * seed.value = parameter * seed.value ^ 2 := by
    rw [seed.value_eq]
    calc
      _ = seed.rootSample ^ 2 * inv parameter := by ring1
      _ = seed.rootSample ^ 2 * inv parameter * (parameter * inv parameter) := by
        have cancel : parameter * inv parameter = 1 := by
          with_unfolding_all exact Basic.Canonical.mul_inv_cancel parameter seed.owner.parameterNonzero
        rw [cancel, Basic.mul_one]
      _ = _ := by ring1
  have identity : 1 - root * seed.value =
      (1 - parameter * seed.value ^ 2) + (seed.rootSample - root) * seed.value := by
    rw [<- centerEq]; ring1
  rw [identity]
  have triangle := Norm.Bounds.normSq_add_le_two
    (1 - parameter * seed.value ^ 2) ((seed.rootSample - root) * seed.value)
  simp only [Norm.Basic.normSq_eq_canonical] at triangle
  apply triangle.trans
  apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _ (by decide)
  apply add_le_add le_rfl
  rw [Basic.Canonical.normSq_mul]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (by
      simpa only [Norm.Basic.normSq_eq_canonical] using
        Box.normSq_sub_le_diagonalSq seed.rootSample_inside inside) (Basic.Canonical.normSq_nonneg _)

end Seed

open Purelib.Data.Rat in
/-- The original denominator slope times the square of the seed norm is nonnegative.

The observation site's positive slope and the retained seed's rational square
supply the two nonnegative factors of this unchanged variation scale. -/
theorem seedScale_nonnegative {polynomial : Polynomial} {count : Nat}
    (site : ObservationNeighborhood polynomial count) (seed : Seed (polynomial.eval site.center)) :
    0 <= site.denominatorSlope * normSq seed.value ^ 2 :=
  Fraction.Order.Arithmetic.mul_nonneg_direct site.denominatorSlope_positive.le
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Readings in
/-- The original seed has inverse-root residual at most one sixteenth throughout a sufficiently small centered box.

The radius lies inside the unit ambient box, and its retained denominator variation error must be at most one
sixty-fourth; the original center seed pays the remaining residual term. -/
theorem seed_small_on_box {polynomial : Polynomial} {count : Nat}
    (site : ObservationNeighborhood polynomial count) (seed : Seed (polynomial.eval site.center))
    {radius : Fraction.Rational} (nonnegative : 0 <= radius)
    (radiusBound : radius <= 1)
    (radiusError : (site.denominatorSlope * normSq seed.value ^ 2) * (8 * radius ^ 2) <= 1 / 64)
    {point : Basic.Canonical} (inside : (Box.Square.Centered.BoxTransport.centeredBox site.center radius
      nonnegative).Contains point) :
    normSq (1 - polynomial.eval point * seed.value ^ 2) <= 1 / 16 := by
  have centerInside := PreparedObservationNeighborhoods.centeredBox_center site.center nonnegative
  have refines : (Box.Square.Centered.BoxTransport.centeredBox site.center radius nonnegative).Refines site.ambient :=
    by
    rw [site.ambient_eq]
    exact centeredBox_refines _ nonnegative (by decide) radiusBound
  have variation := Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound polynomial
    (refines.contains centerInside) (refines.contains inside)
  rw [<- site.denominatorSlope_eq] at variation
  have distance := Box.normSq_sub_le_diagonalSq centerInside inside
  rw [Box.Square.Centered.BoxTransport.centeredBox_diagonalSq] at distance
  simp only [Norm.Basic.normSq_eq_canonical] at variation distance
  have movement : normSq (polynomial.eval site.center - polynomial.eval point) <=
      site.denominatorSlope * (8 * radius ^ 2) := variation.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct distance site.denominatorSlope_positive.le)
  have perturbation : normSq ((polynomial.eval site.center - polynomial.eval point) * seed.value ^ 2) <= 1 / 64 := by
    have squareNorm := Power.normSq_pow seed.value 2
    simp only [Norm.Basic.normSq_eq_canonical] at squareNorm
    rw [Basic.Canonical.normSq_mul, squareNorm]
    calc
      _ <= (site.denominatorSlope * (8 * radius ^ 2)) * normSq seed.value ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct movement
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      _ = (site.denominatorSlope * normSq seed.value ^ 2) * (8 * radius ^ 2) := by ring1
      _ <= 1 / 64 := radiusError
  have identity : 1 - polynomial.eval point * seed.value ^ 2 =
      (1 - polynomial.eval site.center * seed.value ^ 2) +
        (polynomial.eval site.center - polynomial.eval point) * seed.value ^ 2 := by ring1
  rw [identity]
  calc
    _ <= 2 * (normSq (1 - polynomial.eval site.center * seed.value ^ 2) +
        normSq ((polynomial.eval site.center - polynomial.eval point) * seed.value ^ 2)) :=
      by
        have scalar := Norm.Bounds.normSq_add_le_two
          (1 - polynomial.eval site.center * seed.value ^ 2)
          ((polynomial.eval site.center - polynomial.eval point) * seed.value ^ 2)
        simpa only [Norm.Basic.normSq_eq_canonical] using scalar
    _ <= 2 * ((1 / 64 : Fraction.Rational) + 1 / 64) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add seed.residual_small perturbation) (by decide)
    _ = 1 / 16 := by decide +kernel

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- An original observation site and root-owned seed with a positive centered box and certified inverse-root model.

The radius remains below the site radius, and the model's polynomial is exactly the constant polynomial of the retained
seed value. -/
structure SeededNeighborhood (polynomial : Polynomial) (count : Nat) where
  /-- The original nonzero polynomial observation neighborhood and its retained bounds. -/ site :
    ObservationNeighborhood polynomial count
  /-- The original root-owned inverse-root seed for the site's exact center evaluation. -/ seed : Seed (polynomial.eval
    site.center)
  /-- The retained positive centered-neighborhood radius. -/ radius : Fraction.Rational
  /-- The retained radius is no larger than the original observation site's radius. -/ radius_le_site : radius ≤
    site.radius
  /-- The retained centered-neighborhood radius is strictly positive. -/ radius_positive : 0 < radius
  /-- The exact centered box retained for the inverse-root model. -/ box : Purelib.Geometry.Rational.Box
  /-- The box equals the centered square at the original site center and retained radius. -/ box_eq : box =
    Box.Square.Centered.BoxTransport.centeredBox site.center radius radius_positive.le
  /-- The certified inverse-root polynomial model on this exact retained box. -/ model : Model polynomial box
  /-- The model polynomial is exactly the constant polynomial of the retained seed value. -/ model_value_eq :
    model.value = Dense.Basic.DensePolynomial.constant seed.value

constructive_injectivity SeededNeighborhood

namespace SeededNeighborhood

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
/-- Package a retained site and seed with a supplied positive radius and pointwise inverse-root residual bound.

The exact centered box and original constant seed polynomial define the certified model, while the site-radius
inequality is retained. -/
def ofRadius {polynomial : Polynomial} {count : Nat} (site : ObservationNeighborhood polynomial count)
    (seed : Seed (polynomial.eval site.center)) (radius : Fraction.Rational) (positive : 0 < radius)
    (siteBound : radius ≤ site.radius)
    (small : ∀ point, (Box.Square.Centered.BoxTransport.centeredBox site.center radius positive.le).Contains point →
      normSq (1 - polynomial.eval point * seed.value ^ 2) ≤ 1 / 16) :
    SeededNeighborhood polynomial count where
  site := site
  seed := seed
  radius := radius
  radius_le_site := siteBound
  radius_positive := positive
  box := Box.Square.Centered.BoxTransport.centeredBox site.center radius positive.le
  box_eq := rfl
  model := Model.ofSeed polynomial _ seed.value small
  model_value_eq := rfl

open Purelib.Data.Rat in
/-- Choose a positive radius for the original observation site and retained seed using its denominator variation scale.

The minimum of the site radius and computed residual radius pays the uniform one-sixteenth seed residual without
replacing the root owner. -/
def ofSeed {polynomial : Polynomial} {count : Nat} (site : ObservationNeighborhood polynomial count)
    (seed : Seed (polynomial.eval site.center)) : SeededNeighborhood polynomial count :=
  let radius := min site.radius (variationRadius (1 / 16) (site.denominatorSlope * normSq seed.value ^ 2))
  have positive : 0 < radius := Fraction.Order.Basic.lt_min site.radius_positive
    (variationRadius_positive (by decide) (seedScale_nonnegative site seed))
  ofRadius site seed radius positive (Fraction.Order.Basic.min_le_left _ _)
    (fun _ inside => seed_small_on_box site seed positive.le
      ((Fraction.Order.Basic.min_le_left _ _).trans site.radius_le_one)
      (by
        have bound := variation_error_le_quarter (seedScale_nonnegative site seed) positive.le
          (Fraction.Order.Basic.min_le_right _ _)
        exact bound.trans_eq (by decide +kernel)) inside)

/-- Build a seeded observation neighborhood from the original site's supplied root owner. -/
def ofOwner {polynomial : Polynomial} {count : Nat} (site : ObservationNeighborhood polynomial count)
    (owner : Owner (polynomial.eval site.center)) : SeededNeighborhood polynomial count :=
  ofSeed site (Seed.ofOwner owner)

open Purelib.Data.Gaussian in
open Purelib.Riemann.Topology in
/-- Build an observation site and independently selected sheet owner at the original nonzero polynomial value.

The resulting neighborhood retains the supplied point, coefficient count and selected sheet through its seed and
inverse-root model. -/
def ofPoint (polynomial : Polynomial) (point : Basic.Canonical) (clear : polynomial.eval point ≠ 0)
    (count : Nat) (sheet : Fin 2) : SeededNeighborhood polynomial count :=
  ofOwner (ObservationNeighborhood.ofPoint polynomial count point clear)
    (SquareRootContinuationChain.Owner.independent clear sheet)

/-- The seeded neighborhood's positive centered box has strictly increasing coordinate intervals. -/
theorem box_proper {polynomial : Polynomial} {count : Nat} (patch : SeededNeighborhood polynomial count) :
    patch.box.Proper := by
  rw [patch.box_eq]
  exact centeredBox_proper _ patch.radius_positive

/-- The seeded neighborhood's retained box refines the original site's ambient unit box. -/
theorem box_refines {polynomial : Polynomial} {count : Nat} (patch : SeededNeighborhood polynomial count) :
    patch.box.Refines patch.site.ambient := by
  rw [patch.box_eq]
  exact patch.site.box_refines patch.radius_positive.le patch.radius_le_site

/-- Refine the retained inverse-root polynomial model at the requested index on the same original box. -/
def refine {polynomial : Polynomial} {count : Nat} (patch : SeededNeighborhood polynomial count)
    (index : Nat) : Model polynomial patch.box := patch.model.refine index

end SeededNeighborhood

end Purelib.Riemann.Normalization.OwnerSeededInverseRoot
