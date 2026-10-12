module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Power.Isolation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.Exact.Ownership.Radius
import Purelib.RootIsolation.FTA.Squarefree.Input
public import Purelib.RootIsolation.Residual.Global.Assignment
import Purelib.RootIsolation.Residual.Global.Bounds
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

public import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Exact.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.RootIsolation.Exact.Ownership.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Interior
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite square-root owner reconditioning

A Rouché move preserves the root occurrence, but its freshly extracted box
refines the preceding box.  Iterating only that operation would eventually
trap a long continuation in its first box.  This module supplies the missing
finite reconditioning step.  It takes a sufficiently accurate rational sample
from the continued track, globally assigns a tiny winding-one box around that
sample to one of the two independently isolated target owners, and proves that
the tiny box is still strictly inside the continued owner.

Thus the result contains a displayed common descendant of the old owner and a
fresh global owner.  No root is selected in a completed field, and the entire
assignment is computed from finite residual and box certificates.
-/

namespace Purelib.Riemann.RootContinuation.SquareRootReconditioning

open Purelib.Data.Rat

open Purelib.Riemann.Topology.SquareRootContinuationChain

/-- The exact rational coordinate carrier. -/
public abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
public abbrev Gaussian := Basic.Canonical
open Purelib.Polynomial.Dense.Gaussian in
/-- Dense Gaussian polynomials over exact rational coordinates. -/
public abbrev GaussianPolynomial :=
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The original rational box type with retained coordinate bounds. -/
public abbrev Box := Purelib.Geometry.Rational.Box
/-- The original square-root owner indexed by its nonzero radicand. -/
public abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
/-- The original winding-one track indexed by its polynomial and ambient box. -/
public abbrev WindingOneTrack := Purelib.RootIsolation.Track.Basic.WindingOneTrack

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
/-- The quadratic polynomial whose roots square to the original radicand.

The retained degree-two power polynomial uses the same Gaussian radicand and
coefficient ordering as the original finite squarefree isolation. -/
@[expose] public def rootPolynomial (parameter : Gaussian) : GaussianPolynomial :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
    SquareRootDegree.degreeTwo

open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation in
/-- Construct the explicit squarefree isolation input for the nonzero radicand's quadratic polynomial.

Nonzero radicand and the retained degree-two bound provide the original
polynomial, elimination certificates and complete finite isolation input. -/
@[expose] public def isolationInput {parameter : Gaussian} (parameterNonzero : parameter ≠ 0) :
    RootIsolation.FTA.Squarefree.Input (rootPolynomial parameter) := by
  exact Power.Isolation.isolationInput parameterNonzero
    SquareRootDegree.degreeTwo
    SquareRootDegree.degreeTwo_atLeastTwo

/-- One eighth of the original owner's residual interior radius.

The request uses the same initial clearance radius as the original owner;
the fixed factor leaves room for the assigned band inside its interior. -/
@[expose] public def requestedRadius {parameter : Gaussian} (owner : Owner parameter) :
    Coordinate :=
  owner.track.initial.clearance.residualInteriorRadius / 8

/-- The retained assignment radius request is strictly positive.

The original clearance supplies a positive interior radius, and division
by the displayed positive constant preserves that strict bound. -/
public theorem requestedRadius_positive {parameter : Gaussian}
    (owner : Owner parameter) : 0 < requestedRadius owner := by
  exact Fraction.Order.Field.div_pos_direct
    owner.track.initial.clearance.residualInteriorRadius_pos (by decide)

open Purelib.RootIsolation.Residual in
/-- The minimum residual threshold controlling global location, assignment accuracy and original clearance.

The three bounds use the same quadratic polynomial, its explicit isolation input and the original owner's requested
interior radius. -/
@[expose] public def residualTarget {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (owner : Owner parameter) : Coordinate :=
  min (Global.Bounds.outsideResidualThreshold
      (rootPolynomial parameter))
    (min (Global.Assignment.insideResidualTarget
        (isolationInput parameterNonzero) (requestedRadius owner))
      (owner.track.initial.clearance.bound / 4))

open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation.Residual in
/-- The combined residual threshold is strictly positive for the original nonzero radicand.

Each retained minimum entry is positive: global exclusion, inside assignment
and one quarter of the original boundary-clearance allowance. -/
public theorem residualTarget_positive {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (owner : Owner parameter) :
    0 < residualTarget parameterNonzero owner := by
  apply Fraction.Order.Basic.lt_min
  · apply Global.Bounds.outsideResidualThreshold_pos
    unfold rootPolynomial
    rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]
    exact SquareRootDegree.degreeTwo.positive
  · apply Fraction.Order.Basic.lt_min
    · exact Global.Assignment.insideResidualTarget_pos
        (isolationInput parameterNonzero) (requestedRadius_positive owner)
    · exact Fraction.Order.Field.div_pos_direct
        owner.track.initial.clearance.positive (by decide)

open Purelib.Approximation.Rational in
open Purelib.Riemann.RootContinuation in
/-- Search the original track's geometric residual scale for the combined reconditioning threshold.

The finite search starts at zero and keeps the original track scale and
combined positive threshold as its exact inputs. -/
@[expose] public def sampleIndex {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (owner : Owner parameter) : Nat :=
  Geometric.Search.firstQuarterBelow
    (CoherentRoot.residualScale
      (rootPolynomial parameter) owner.ambient owner.track)
    0 (residualTarget parameterNonzero owner)

open Purelib.Riemann.RootContinuation in
/-- Read the original root-track sample at the retained residual search index.

The approximation and search index come from the same original track; no
second sample or independently selected owner is substituted. -/
@[expose] public def sample {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (owner : Owner parameter) : Gaussian :=
  (CoherentRoot.approximation owner.track).sample
    (sampleIndex parameterNonzero owner)

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
/-- The selected sample's squared polynomial residual is below the combined threshold.

The retained geometric search accuracy composes with the original track
residual bound for the same polynomial and displayed sample. -/
public theorem sample_residual_lt {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (owner : Owner parameter) :
    normSq ((rootPolynomial parameter).eval
      (sample parameterNonzero owner)) <
        residualTarget parameterNonzero owner := by
  rw [← Norm.Basic.normSq_eq_canonical]
  exact (CoherentRoot.sample_residual_le owner.track (by
    rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]
    exact SquareRootDegree.degreeTwo.positive)
      (sampleIndex parameterNonzero owner)).trans_lt
    (Geometric.Search.firstQuarterBelow_accurate
      (CoherentRoot.residualScale
        (rootPolynomial parameter) owner.ambient owner.track)
      (CoherentRoot.residualScale_nonneg
        (rootPolynomial parameter) owner.ambient owner.track)
      0 (residualTarget parameterNonzero owner)
      (residualTarget_positive parameterNonzero owner))

open Purelib.Riemann.RootContinuation in
/-- The selected sample remains in the original owner's initial box. -/
public theorem sample_inside_owner {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (owner : Owner parameter) :
    owner.track.initial.box.Contains (sample parameterNonzero owner) := by
  rw [sample, CoherentRoot.approximation_sample]
  exact (CoherentRoot.state_refines_of_le owner.track
    (Nat.zero_le (sampleIndex parameterNonzero owner))).contains
      (CoherentRoot.state owner.track
        (sampleIndex parameterNonzero owner)).box.contains_anchor

open Purelib.Data.Gaussian in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation.Residual in
/-- The selected sample lies in the quadratic polynomial's certified global root box.

An outside sample would have residual above the retained exclusion threshold,
contradicting the strict residual estimate for that exact sample. -/
public theorem sample_inside_largeSquare {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (owner : Owner parameter) :
    (Bounds.RootRadius.Box.largeSquareBox (rootPolynomial parameter)).Contains
      (sample parameterNonzero owner) := by
  by_cases inside :
      (Bounds.RootRadius.Box.largeSquareBox (rootPolynomial parameter)).Contains
        (sample parameterNonzero owner)
  · exact inside
  · have outsideLower := Global.Bounds.outsideResidualThreshold_le
      (p := rootPolynomial parameter) (by
        unfold rootPolynomial
        rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]
        exact SquareRootDegree.degreeTwo_atLeastTwo)
      (sample parameterNonzero owner) inside
    rw [Norm.Basic.normSq_eq_canonical] at outsideLower
    have residualBelowOutside :
        normSq ((rootPolynomial parameter).eval
          (sample parameterNonzero owner)) <
          Global.Bounds.outsideResidualThreshold
            (rootPolynomial parameter) :=
      (sample_residual_lt parameterNonzero owner).trans_le
        (Fraction.Order.Basic.min_le_left _ _)
    exact ((not_lt_of_ge outsideLower) residualBelowOutside).elim

open Purelib.RootIsolation.Residual in
/-- The selected sample satisfies the global assignment procedure's inside-residual threshold.

The retained nested minimum lies below the inside target for the original
isolation input and the same requested radius. -/
public theorem sample_residual_lt_insideTarget {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (owner : Owner parameter) :
    normSq ((rootPolynomial parameter).eval
      (sample parameterNonzero owner)) <
      Global.Assignment.insideResidualTarget
        (isolationInput parameterNonzero) (requestedRadius owner) :=
  (sample_residual_lt parameterNonzero owner).trans_le
    ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))

/-- The selected sample's residual is below one quarter of the original boundary-clearance bound.

The second retained minimum carries this clearance allowance for the same
original track and displayed sample. -/
public theorem sample_residual_lt_ownerQuarter {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (owner : Owner parameter) :
    normSq ((rootPolynomial parameter).eval
      (sample parameterNonzero owner)) <
      owner.track.initial.clearance.bound / 4 :=
  (sample_residual_lt parameterNonzero owner).trans_le
    ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _))

open Purelib.Data.Gaussian in
open Purelib.RootIsolation.Residual in
/-- Assign the retained original sample to an explicit isolated root within the requested radius.

The exact global-box containment and residual certificates feed the finite assignment procedure; the resulting owner
remains tied to this same sample and request. -/
@[irreducible, expose] public def assignment {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    (owner : Owner parameter) :
    Global.Assignment.AssignedResult (isolationInput parameterNonzero)
      (sample parameterNonzero owner) (requestedRadius owner) :=
  Global.Assignment.assignInside (isolationInput parameterNonzero)
    (sample parameterNonzero owner)
    (sample_inside_largeSquare parameterNonzero owner)
    (requestedRadius_positive owner)
    (by simpa only [Norm.Basic.normSq_eq_canonical] using sample_residual_lt_insideTarget parameterNonzero owner)

open Purelib.Data.Gaussian in
/-- A positive squared-norm radius bound gives strict signed bounds on both Gaussian coordinates.

Each coordinate square lies below the supplied positive radius square;
applying the same comparison to the coordinate and its negation gives both signs. -/
private theorem signed_coordinate_bounds_of_normSq_lt_sq
    {delta : Gaussian} {radius : Coordinate} (radiusPositive : 0 < radius)
    (distance : normSq delta < radius ^ 2) :
    -radius < delta.re ∧ delta.re < radius ∧
      -radius < delta.im ∧ delta.im < radius := by
  simp only [Basic.Canonical.normSq, ← pow_two] at distance
  have realSquare : delta.re ^ 2 < radius ^ 2 :=
    (show delta.re ^ 2 ≤ delta.re ^ 2 + delta.im ^ 2 from
      le_add_of_nonneg_right (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans_lt
      distance
  have imaginarySquare : delta.im ^ 2 < radius ^ 2 :=
    (show delta.im ^ 2 ≤ delta.re ^ 2 + delta.im ^ 2 from
      le_add_of_nonneg_left (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans_lt
      distance
  have realUpper := Bounds.Square.lt_of_sq_lt_sq_of_nonneg
    radiusPositive.le realSquare
  have realNegativeUpper := Bounds.Square.lt_of_sq_lt_sq_of_nonneg
    radiusPositive.le (a := -delta.re) (by
      calc
        (-delta.re) ^ 2 = delta.re ^ 2 := by ring1
        _ < radius ^ 2 := realSquare)
  have imaginaryUpper := Bounds.Square.lt_of_sq_lt_sq_of_nonneg
    radiusPositive.le imaginarySquare
  have imaginaryNegativeUpper :=
    Bounds.Square.lt_of_sq_lt_sq_of_nonneg
      radiusPositive.le (a := -delta.im) (by
        calc
          (-delta.im) ^ 2 = delta.im ^ 2 := by ring1
          _ < radius ^ 2 := imaginarySquare)
  exact
    ⟨by
      have negated := Fraction.Order.Arithmetic.neg_lt_neg_direct
        realNegativeUpper
      simpa only [neg_neg] using negated,
      realUpper,
      by
        have negated := Fraction.Order.Arithmetic.neg_lt_neg_direct
          imaginaryNegativeUpper
        simpa only [neg_neg] using negated,
      imaginaryUpper⟩

open Purelib.Algebra in
open Purelib.Data.Gaussian in
/-- Every point of the assigned state lies within the original residual interior radius of the sample.

The assignment's squared distance bound is at most eighteen times its radius squared, and the retained radius is at most
one eighth of the original interior radius. -/
private theorem assigned_band_distance_lt {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (owner : Owner parameter)
    {z : Gaussian}
    (inside : (assignment parameterNonzero owner).state.box.Contains z) :
    normSq (z - sample parameterNonzero owner) <
      owner.track.initial.clearance.residualInteriorRadius ^ 2 := by
  let radius := owner.track.initial.clearance.residualInteriorRadius
  let epsilon := requestedRadius owner
  have radiusPositive : 0 < radius := by
    simpa only [radius] using
      owner.track.initial.clearance.residualInteriorRadius_pos
  have radiusSquarePositive : 0 < radius ^ 2 :=
    Fraction.Order.Arithmetic.pow_pos_direct radiusPositive 2
  have assignedRadiusSquareLe :
      (assignment parameterNonzero owner).radius ^ 2 ≤ epsilon ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (assignment parameterNonzero owner).radiusPositive.le
      (assignment parameterNonzero owner).radiusLeRequested 2
  have bandLe :
      18 * (assignment parameterNonzero owner).radius ^ 2 ≤
        18 * epsilon ^ 2 :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      assignedRadiusSquareLe (by decide)
  have epsilon_eq : epsilon = (1 / 8 : Coordinate) * radius := by
    dsimp only [epsilon, requestedRadius, radius]
    simp only [Field.ExplicitField.div_eq_mul_inv,
      Fraction.Field.one_mul]
    rw [Fraction.Field.mul_comm]
  have scaledStrict : 18 * epsilon ^ 2 < radius ^ 2 := by
    rw [epsilon_eq]
    calc
      18 * ((1 / 8 : Coordinate) * radius) ^ 2 =
          (18 * (1 / 8 : Coordinate) ^ 2) * radius ^ 2 := by
        ring1
      _ < 1 * radius ^ 2 :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
          (show (18 : Coordinate) * (1 / 8) ^ 2 < 1 by decide)
          radiusSquarePositive
      _ = radius ^ 2 := by ring1
  calc
    normSq (z - sample parameterNonzero owner) ≤
        18 * (assignment parameterNonzero owner).radius ^ 2 :=
      by simpa only [Norm.Basic.normSq_eq_canonical] using (assignment parameterNonzero owner).bandNearSample z inside
    _ ≤ 18 * epsilon ^ 2 := bandLe
    _ < radius ^ 2 := scaledStrict

open Purelib.Data.Gaussian in
/-- The assigned state's box lies strictly inside the original owner's initial box.

The original residual-interior margins and the assigned band's coordinate bounds certify all four strict box
inequalities. -/
public theorem assignment_state_strict_owner {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (owner : Owner parameter) :
    (assignment parameterNonzero owner).state.box.StrictInterior
      owner.track.initial.box := by
  let source := owner.track.initial.box
  let localBox := (assignment parameterNonzero owner).state.box
  let anchor := sample parameterNonzero owner
  let radius := owner.track.initial.clearance.residualInteriorRadius
  have margins := owner.track.initial.clearance.residualInteriorMargins
    (sample_inside_owner parameterNonzero owner)
    (by
      simpa only [rootPolynomial, Norm.Basic.normSq_eq_canonical] using
        sample_residual_lt_ownerQuarter parameterNonzero owner)
  have radiusPositive : 0 < radius := by
    simpa only [radius] using
      owner.track.initial.clearance.residualInteriorRadius_pos
  let lower : Gaussian := ⟨localBox.xLower, localBox.yLower⟩
  let upper : Gaussian := ⟨localBox.xUpper, localBox.yUpper⟩
  have lowerInside : localBox.Contains lower :=
    ⟨le_rfl, localBox.x_valid, le_rfl, localBox.y_valid⟩
  have upperInside : localBox.Contains upper :=
    ⟨localBox.x_valid, le_rfl, localBox.y_valid, le_rfl⟩
  have lowerBounds := signed_coordinate_bounds_of_normSq_lt_sq radiusPositive
    (assigned_band_distance_lt parameterNonzero owner lowerInside)
  have upperBounds := signed_coordinate_bounds_of_normSq_lt_sq radiusPositive
    (assigned_band_distance_lt parameterNonzero owner upperInside)
  exact
    { left := by
        calc
          source.xLower < anchor.re - radius := by
            have := margins.1
            dsimp only [source, anchor, radius] at this ⊢
            have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct this (-radius)
            dsimp only [source, anchor, radius] at shifted ⊢
            convert shifted using 1 <;> ring1
          _ < localBox.xLower := by
            have := lowerBounds.1
            dsimp only [lower, anchor] at this
            have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct this anchor.re
            simp only [Basic.sub_re] at shifted
            dsimp only [anchor] at shifted ⊢
            convert shifted using 1 <;> ring1
      right := by
        calc
          localBox.xUpper < anchor.re + radius := by
            have := upperBounds.2.1
            dsimp only [upper, anchor] at this
            have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct this anchor.re
            simp only [Basic.sub_re] at shifted
            dsimp only [anchor] at shifted ⊢
            convert shifted using 1 <;> ring1
          _ < source.xUpper := by
            simpa only [source, anchor, radius] using margins.2.1
      bottom := by
        calc
          source.yLower < anchor.im - radius := by
            have := margins.2.2.1
            dsimp only [source, anchor, radius] at this ⊢
            have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct this (-radius)
            dsimp only [source, anchor, radius] at shifted ⊢
            convert shifted using 1 <;> ring1
          _ < localBox.yLower := by
            have := lowerBounds.2.2.1
            dsimp only [lower, anchor] at this
            have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct this anchor.im
            simp only [Basic.sub_im] at shifted
            dsimp only [anchor] at shifted ⊢
            convert shifted using 1 <;> ring1
      top := by
        calc
          localBox.yUpper < anchor.im + radius := by
            have := upperBounds.2.2.2
            dsimp only [upper, anchor] at this
            have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct this anchor.im
            simp only [Basic.sub_im] at shifted
            dsimp only [anchor] at shifted ⊢
            convert shifted using 1 <;> ring1
          _ < source.yUpper := by
            simpa only [source, anchor, radius] using margins.2.2.2 }

section
open Purelib.Polynomial.Dense.Gaussian
/-- Read the independently isolated track selected by the retained sample-assignment result.

The selected two-sheet index comes from the original assignment result,
and the returned track keeps the same polynomial and global ambient box. -/
@[expose] public def freshOwner {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (owner : Owner parameter) : Owner parameter where
  parameterNonzero := parameterNonzero
  ambient := Bounds.RootRadius.Box.largeSquareBox (rootPolynomial parameter)
  track := (isolationInput parameterNonzero).isolation.tracks.get
    (assignment parameterNonzero owner).owner.owner

/-- Read the independently isolated quadratic root track at the supplied two-sheet index.

The retained finite isolation supplies the track at the explicit index,
with the same nonzero radicand and coefficient-computed global box. -/
@[expose] public def canonicalOwner {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (index : Fin 2) : Owner parameter where
  parameterNonzero := parameterNonzero
  ambient := Bounds.RootRadius.Box.largeSquareBox (rootPolynomial parameter)
  track := (isolationInput parameterNonzero).isolation.tracks.get index

end

/-- The assigned fresh owner is exactly the canonical owner at the retained assignment index. -/
@[simp] public theorem freshOwner_eq_canonicalOwner {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (owner : Owner parameter) :
    freshOwner parameterNonzero owner =
      canonicalOwner parameterNonzero
        (assignment parameterNonzero owner).owner.owner :=
  rfl

open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation in
set_option genInjectivity false in
/-- A common root track and certified refinement connecting the original and assigned fresh owners.

The common initial box lies strictly inside the original owner, while its retained radius refinement lies strictly
inside the exact assigned fresh owner. -/
public structure Bridge {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (owner : Owner parameter) where
  /-- The retained common winding-one track for the original quadratic. -/ common : WindingOneTrack (rootPolynomial
    parameter)
    (Bounds.RootRadius.Box.largeSquareBox (rootPolynomial parameter))
  /-- The common initial box lies strictly inside the original owner's initial box. -/ commonInitialStrictOwner :
    common.initial.box.StrictInterior
    owner.track.initial.box
  /-- The retained radius used to refine the common initial state. -/ refinementRadius : Coordinate
  /-- The retained refinement radius is strictly positive. -/ refinementRadiusPositive : 0 < refinementRadius
  /-- The retained refined winding-one state in the same global ambient box. -/ refined :
    State.WindingOne.Basic.WindingOneState (rootPolynomial parameter)
    (Bounds.RootRadius.Box.largeSquareBox (rootPolynomial parameter))
  /-- The state is exactly the common track's refinement at the retained radius and positivity witness. -/ refined_eq :
    refined = common.refine common.initial refinementRadius
    refinementRadiusPositive
  /-- The exact refined box lies strictly inside the assigned fresh owner's initial box. -/ refinedStrictFresh :
    refined.box.StrictInterior
    (freshOwner parameterNonzero owner).track.initial.box

constructive_injectivity Bridge

open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation.Exact in
open Purelib.RootIsolation.Residual in
/-- Construct the common-track bridge from the original sample's retained assignment result.

The assignment radius is retained with its positivity witness and exact refinement equation; both strict containment
certificates refer to the original and selected fresh owners. -/
@[irreducible, expose] public def bridge {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    (owner : Owner parameter) : Bridge parameterNonzero owner := by
  let assigned := assignment parameterNonzero owner
  let radius := Ownership.Radius.assignmentRadius
    (rootPolynomial parameter)
    (Bounds.RootRadius.Box.largeSquareBox (rootPolynomial parameter))
    (isolationInput parameterNonzero).isolation
  let radiusPositive := Ownership.Radius.assignmentRadius_pos
    (rootPolynomial parameter)
    (Bounds.RootRadius.Box.largeSquareBox (rootPolynomial parameter))
    (isolationInput parameterNonzero).isolation
  let refined := assigned.track.refine assigned.track.initial radius
    radiusPositive
  exact
    { common := assigned.track
      commonInitialStrictOwner := by
        simpa only [assigned, Global.Assignment.AssignedResult.trackInitial]
          using assignment_state_strict_owner parameterNonzero owner
      refinementRadius := radius
      refinementRadiusPositive := radiusPositive
      refined := refined
      refined_eq := rfl
      refinedStrictFresh := by
        simpa only [assigned, radius, radiusPositive, refined, freshOwner]
          using assigned.owner.strict }

end Purelib.Riemann.RootContinuation.SquareRootReconditioning
