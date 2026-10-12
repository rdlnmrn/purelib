module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Apart
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.Track.Basic

import Purelib.Riemann.RootContinuation.SquareRootContinuation
public import Purelib.Riemann.Branches.SquareRootSheets
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

/-!
# An operational square root from any certified winding track

`SquareRootSheets` starts from the two independently isolated owners of
`Z^2 - w`.  Rouché continuation produces different tracks, in different
finite ambient boxes.  This file proves the same operational square-root
contract for every such track.  Thus a transported owner can be used as an
actual division-safe CCL value without re-isolating, and hence without losing
its sheet identity.
-/

namespace Purelib.Riemann.RootContinuation.CertifiedSquareRoot

open Purelib.Data.Nat

open Purelib.Data.Rat in
/-- The exact rational coordinate carrier used by the square-root construction. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
abbrev Gaussian := Basic.Canonical
/-- The original rational box type retaining its coordinate bounds. -/
abbrev Box := Purelib.Geometry.Rational.Box
open Purelib.Approximation.Gaussian in
/-- An executable Gaussian approximation with quantitative refinement and sample bounds. -/
abbrev Approximation := Sequence.ApproximationData
/-- A coherent Gaussian name retaining its executable approximation. -/
abbrev CoherentNamed := Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
/-- Operational equivalence between the two original Gaussian names. -/
abbrev NamedEquivalent := Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
/-- The original certified winding-one polynomial root track. -/
abbrev WindingOneTrack := Purelib.RootIsolation.Track.Basic.WindingOneTrack

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Approximation.Rational in
open Purelib.Polynomial.Power in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- Find the first geometric residual index below the fixed nonzero-radicand threshold.

The search uses the original winding track's residual scale and starts at index zero; the track and its ambient box
remain unchanged. -/
@[expose] def baseIndex {parameter : Gaussian} {ambient : Box}
    (track : WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) ambient) : Nat :=
  Geometric.Search.firstQuarterBelow
    (CoherentRoot.residualScale
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo)
      ambient track)
    0 (SquareRootSheets.residualTarget parameter)

section
open Purelib.Polynomial.Power
open Purelib.Riemann.Branches
open Purelib.Riemann.RootContinuation
/-- Tail the original root-track approximation at the retained base index.

Samples use the maximum of the requested index and the base index, retaining the same certified track rather than
selecting a new root owner. -/
@[expose] def approximation {parameter : Gaussian} {ambient : Box}
    (track : WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) ambient) : Approximation :=
  SquareRootSheets.tail
    (CoherentRoot.approximation track) (baseIndex track)

/-- The tailed approximation sample is the anchor of the original track state at the maximum index. -/
@[simp] theorem approximation_sample {parameter : Gaussian} {ambient : Box}
    (track : WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) ambient) (index : Nat) :
    (approximation track).sample index =
      (CoherentRoot.state track (max (baseIndex track) index)).box.anchor := by
  rw [approximation, SquareRootSheets.tail_sample,
    CoherentRoot.approximation_sample]

end

section
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Polynomial.Power
open Purelib.Riemann.Branches
open Purelib.Riemann.RootContinuation
/-- Every tailed root sample has squared residual bounded by the original geometric residual scale.

The estimate holds at the requested index even when the retained base index is larger, by monotonicity of the
quarter-radius. -/
theorem sample_residual_le {parameter : Gaussian} {ambient : Box}
    (track : WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) ambient)
    (index : Nat) :
    normSq
        ((approximation track).sample index *
            (approximation track).sample index - parameter) <=
      Geometric.Basic.quarterRadius
        (CoherentRoot.residualScale
          (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
            SquareRootDegree.degreeTwo)
          ambient track) index := by
  let selected := max (baseIndex track) index
  have raw := CoherentRoot.sample_residual_le track (by
    rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]
    exact SquareRootDegree.degreeTwo.positive) selected
  rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval] at raw
  have selectedBound := quarterRadius_antitone
    (CoherentRoot.residualScale_nonneg
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo)
      ambient track)
    (show index ≤ max (baseIndex track) index from by
      rw [Order.max_eq_natMax]
      exact Order.le_max_right (baseIndex track) index)
  simpa only [approximation, SquareRootSheets.tail_sample,
    selected, SquareRootDegree.degreeTwo_value, Basic.Canonical.normSq, Data.Gaussian.Norm.Basic.normSq, pow_two] using
      raw.trans selectedBound

/-- For a nonzero radicand, every tailed sample has residual below its fixed nonzero threshold.

The finite base-index search retains its original target and scale; each same tailed sample lies beyond that base, so
its residual obeys the fixed nonzero-radicand threshold. -/
theorem sample_residual_lt_target {parameter : Gaussian} {ambient : Box}
    (parameterNonzero : parameter ≠ 0)
    (track : WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) ambient)
    (index : Nat) :
    normSq
        ((approximation track).sample index *
            (approximation track).sample index - parameter) <
      SquareRootSheets.residualTarget parameter := by
  let scale := CoherentRoot.residualScale
    (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
      SquareRootDegree.degreeTwo)
    ambient track
  have baseSmall : Geometric.Basic.quarterRadius scale
      (baseIndex track) <
      SquareRootSheets.residualTarget parameter := by
    exact Geometric.Search.firstQuarterBelow_accurate scale
      (CoherentRoot.residualScale_nonneg
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          SquareRootDegree.degreeTwo)
        ambient track)
      0 (SquareRootSheets.residualTarget parameter)
      (SquareRootSheets.residualTarget_positive parameterNonzero)
  let selected := max (baseIndex track) index
  have raw := CoherentRoot.sample_residual_le track (by
    rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]
    exact SquareRootDegree.degreeTwo.positive) selected
  rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval] at raw
  have selectedSmall : Geometric.Basic.quarterRadius scale selected <
      SquareRootSheets.residualTarget parameter :=
    (quarterRadius_antitone
      (CoherentRoot.residualScale_nonneg
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          SquareRootDegree.degreeTwo)
        ambient track)
      (show baseIndex track ≤ max (baseIndex track) index from by
        rw [Order.max_eq_natMax]
        exact Order.le_max_left (baseIndex track) index)).trans_lt baseSmall
  simpa only [approximation, SquareRootSheets.tail_sample,
    selected, SquareRootDegree.degreeTwo_value, Basic.Canonical.normSq, Data.Gaussian.Norm.Basic.normSq, pow_two] using
      raw.trans_lt selectedSmall

end

section
open Purelib.Approximation.Rational
open Purelib.Polynomial.Power
open Purelib.Riemann.RootContinuation
/-- Search the track's residual scale for an index below the requested positive tolerance.

The finite search starts at zero and retains the track's residual scale and
supplied target. Its selected index belongs to the same quadratic root track. -/
@[expose] def residualIndex {parameter : Gaussian} {ambient : Box}
    (track : WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) ambient)
    (target : Coordinate) (_positive : 0 < target) : Nat :=
  Geometric.Search.firstQuarterBelow
    (CoherentRoot.residualScale
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo)
      ambient track) 0 target

/-- The selected residual index makes the original geometric residual bound strictly smaller than the target. -/
theorem residualIndex_accurate {parameter : Gaussian} {ambient : Box}
    (track : WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) ambient)
    (target : Coordinate) (positive : 0 < target) :
    Geometric.Basic.quarterRadius
        (CoherentRoot.residualScale
          (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
            SquareRootDegree.degreeTwo)
          ambient track)
        (residualIndex track target positive) < target := by
  exact Geometric.Search.firstQuarterBelow_accurate _
    (CoherentRoot.residualScale_nonneg
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo)
      ambient track) 0 target positive

end

open Purelib.Polynomial.Power in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- Every tailed sample for a nonzero radicand satisfies the fixed positive squared-norm lower bound. -/
theorem sample_norm_lower {parameter : Gaussian} {ambient : Box}
    (parameterNonzero : parameter ≠ 0)
    (track : WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) ambient)
    (index : Nat) :
    SquareRootSheets.sampleNormLower parameter <=
      normSq ((approximation track).sample index) :=
  SquareRootSheets.normSq_lower_of_square_residual
    (sample_residual_lt_target parameterNonzero track index).le

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Polynomial.Power in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- Certify that all possible values of the tailed process stay uniformly away from zero.

The retained lower squared norm depends on the original nonzero radicand; each possible value is a later sample of the
same root track. -/
@[expose] def possibleApart {parameter : Gaussian} {ambient : Box}
    (parameterNonzero : parameter ≠ 0)
    (track : WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) ambient) :
    Process.Apart.Possible.PossibleApart (approximation track).toProcess where
  lowerSq := SquareRootSheets.sampleNormLower parameter
  positive := SquareRootSheets.sampleLower_positive
    parameterNonzero
  lower := by
    intro state value possible
    change (approximation track).Possible state value at possible
    rcases possible with ⟨later, _order, rfl⟩
    simpa only [Basic.Canonical.normSq, Data.Gaussian.Norm.Basic.normSq, pow_two] using
      sample_norm_lower parameterNonzero track later

section
open Purelib.Approximation.Gaussian
open Purelib.Polynomial.Power
open Purelib.Riemann.RootContinuation
/-- Turn the tailed root-track approximation into its coherent Gaussian name.

The coherent name retains this exact approximation, including its sample
function, refinement indices and quantitative bounds. -/
@[expose] def rawRoot {parameter : Gaussian} {ambient : Box}
    (track : WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) ambient) : CoherentNamed :=
  Name.Coherent.CoherentNamed.ofApproximation
    (approximation track)

/-- Equip the original coherent root name with a retained apartness preparation.

The nonzero radicand supplies a positive lower squared norm for every possible sample, preserving the track's sheet
identity. -/
@[expose] def root {parameter : Gaussian} {ambient : Box}
    (parameterNonzero : parameter ≠ 0)
    (track : WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) ambient) : CoherentNamed :=
  Name.Coherent.CoherentNamed.apartify
    (rawRoot track) (possibleApart parameterNonzero track)

/-- Read the retained apartness certificate of the prepared root name.

The nonzero radicand supplies the same preparation used to build the root.
Its certificate bounds the possible values of that retained prepared name. -/
@[expose] def rootApart {parameter : Gaussian} {ambient : Box}
    (parameterNonzero : parameter ≠ 0)
    (track : WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) ambient) :
    Name.Basic.Named.Apart
      (root parameterNonzero track).name where
  certificate := Process.Apart.Preparation.apartifyApart
    (possibleApart parameterNonzero track)

/-- Prepare a root-name state meeting the requested residual tolerance and apartness condition.

The state starts from the original residual search index and refines the same tailed approximation using its retained
lower bound. -/
@[expose] def residualState {parameter : Gaussian} {ambient : Box}
    (parameterNonzero : parameter ≠ 0)
    (track : WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) ambient)
    (target : Coordinate) (positive : 0 < target) :
    (root parameterNonzero track).name.process.State := by
  change Process.Apart.Preparation.ApartState
    (approximation track).toProcess (possibleApart parameterNonzero track)
  exact Process.Apart.Preparation.prepareApartState
    (possibleApart parameterNonzero track)
    (residualIndex track target positive)

end

open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
open Purelib.Approximation.Rational in
/-- Every possible candidate at the prepared residual state squares to within the requested tolerance.

Later candidates inherit the geometric residual estimate from the same track and the order bound retained by apartness
preparation. -/
theorem residualState_candidate_residual_lt
    {parameter : Gaussian} {ambient : Box}
    (parameterNonzero : parameter ≠ 0)
    (track : WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) ambient)
    (target : Coordinate) (positive : 0 < target) {candidate : Gaussian}
    (possible : (root parameterNonzero track).name.process.Possible
      (residualState parameterNonzero track target positive) candidate) :
    normSq (candidate * candidate - parameter) < target := by
  change (approximation track).Possible
    (residualState parameterNonzero track target positive).source candidate
      at possible
  rcases possible with ⟨later, stateLeLater, rfl⟩
  have indexLeState : residualIndex track target positive <=
      (residualState parameterNonzero track target positive).source := by
    change residualIndex track target positive <=
      (approximation track).refineIndex
        (residualIndex track target positive)
        ((possibleApart parameterNonzero track).lowerSq / 12)
        (possibleApart parameterNonzero track).twelfth_pos
    exact (approximation track).refineIndex_ge _ _ _
  have indexLeLater : residualIndex track target positive <= later :=
    indexLeState.trans stateLeLater
  have residual := sample_residual_le track later
  have radiusLe := quarterRadius_antitone
    (CoherentRoot.residualScale_nonneg
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo)
      ambient track) indexLeLater
  exact residual.trans_lt
    (radiusLe.trans_lt (residualIndex_accurate track target positive))

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
/-- Square every original tailed sample with explicit geometric radius and center bounds.

The radius scale is four times the original center bound times the track scale. Refinement searches this exact scale
while retaining pointwise square samples. -/
@[expose] def squareApproximation {parameter : Gaussian} {ambient : Box}
    (track : WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) ambient) : Approximation :=
  let source := approximation track
  let scale := 4 * source.centerBound *
    CoherentRoot.scale track
  { sample := fun index => source.sample index * source.sample index
    radiusSq := Geometric.Basic.quarterRadius scale
    radiusSq_nonneg := Geometric.Basic.quarterRadius_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          source.centerBound_nonneg)
        (CoherentRoot.scale_positive track).le)
    later_close := by
      intro earlier later order
      have movement := source.later_close order
      have sourceRadiusLe : source.radiusSq earlier <=
          Geometric.Basic.quarterRadius
            (CoherentRoot.scale track) earlier :=
        quarterRadius_antitone
          (CoherentRoot.scale_positive track).le
          (show earlier ≤ max (baseIndex track) earlier from by
            rw [Order.max_eq_natMax]
            exact Order.le_max_right (baseIndex track) earlier)
      have firstTerm :
          Data.Gaussian.Norm.Basic.normSq ((source.sample later - source.sample earlier) *
              source.sample later) <=
            Geometric.Basic.quarterRadius
                (CoherentRoot.scale track) earlier *
              source.centerBound := by
        rw [Norm.Basic.normSq_mul]
        exact Fraction.Order.Arithmetic.mul_le_mul_direct
          (movement.trans sourceRadiusLe) (source.sample_bounded later)
          (Norm.Basic.normSq_nonneg _) (Geometric.Basic.quarterRadius_nonneg
            (CoherentRoot.scale_positive track).le earlier)
      have secondTerm :
          Data.Gaussian.Norm.Basic.normSq (source.sample earlier *
              (source.sample later - source.sample earlier)) <=
            source.centerBound *
              Geometric.Basic.quarterRadius
                (CoherentRoot.scale track) earlier := by
        rw [Norm.Basic.normSq_mul]
        exact Fraction.Order.Arithmetic.mul_le_mul_direct
          (source.sample_bounded earlier) (movement.trans sourceRadiusLe)
          (Norm.Basic.normSq_nonneg _) source.centerBound_nonneg
      have identity :
          source.sample later * source.sample later -
              source.sample earlier * source.sample earlier =
            (source.sample later - source.sample earlier) *
                source.sample later +
              source.sample earlier *
                (source.sample later - source.sample earlier) := by
        apply Basic.ext <;>
          simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im] <;> ring1
      rw [identity]
      calc
        Data.Gaussian.Norm.Basic.normSq
            ((source.sample later - source.sample earlier) *
                source.sample later +
              source.sample earlier *
                (source.sample later - source.sample earlier)) <=
          2 *
            (Data.Gaussian.Norm.Basic.normSq ((source.sample later - source.sample earlier) *
                source.sample later) +
              Data.Gaussian.Norm.Basic.normSq (source.sample earlier *
                (source.sample later - source.sample earlier))) :=
          Norm.Bounds.normSq_add_le_two _ _
        _ <= 2 *
            (Geometric.Basic.quarterRadius
                (CoherentRoot.scale track) earlier *
                source.centerBound +
              source.centerBound *
                Geometric.Basic.quarterRadius
                  (CoherentRoot.scale track) earlier) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (add_le_add firstTerm secondTerm) (by decide)
        _ = Geometric.Basic.quarterRadius scale earlier := by
          rw [Geometric.Basic.quarterRadius_eq_mul_pow,
            Geometric.Basic.quarterRadius_eq_mul_pow]
          dsimp only [scale]
          ring1
    refineIndex current target _ :=
      Geometric.Search.firstQuarterBelow scale current target
    refineIndex_ge current target _ :=
      Geometric.Search.firstQuarterBelow_ge scale current target
    refineIndex_accurate :=
      Geometric.Search.firstQuarterBelow_accurate scale
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            source.centerBound_nonneg)
          (CoherentRoot.scale_positive track).le)
    centerBound := source.centerBound * source.centerBound
    centerBound_nonneg := Fraction.Order.Arithmetic.mul_nonneg_direct
      source.centerBound_nonneg source.centerBound_nonneg
    sample_bounded := by
      intro index
      rw [Norm.Basic.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_direct
        (source.sample_bounded index) (source.sample_bounded index)
        (Norm.Basic.normSq_nonneg _) source.centerBound_nonneg }

open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
/-- Each square-approximation sample is the square of the same indexed original sample. -/
@[simp] theorem squareApproximation_sample {parameter : Gaussian}
    {ambient : Box}
    (track : WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) ambient)
    (index : Nat) :
    (squareApproximation track).sample index =
      (approximation track).sample index *
        (approximation track).sample index := rfl

open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
/-- Compare the squared samples with the constant original radicand at a shared requested index.

Both starting indices are respected, and every later squared sample satisfies the original track's residual estimate
below the requested tolerance. -/
@[expose] def squareApproximation_equivalent_parameter {parameter : Gaussian}
    {ambient : Box}
    (track : WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) ambient) :
    Equivalence.Equivalent
      (squareApproximation track)
      (Sequence.Constant.constantApproximation parameter) where
  compare := by
    intro leftStart rightStart target positive
    let start := max leftStart rightStart
    let scale := CoherentRoot.residualScale
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo)
      ambient track
    let index := Geometric.Search.firstQuarterBelow scale start target
    have radiusSmall : Geometric.Basic.quarterRadius scale index < target :=
      Geometric.Search.firstQuarterBelow_accurate scale
        (CoherentRoot.residualScale_nonneg
          (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
            SquareRootDegree.degreeTwo)
          ambient track) start target positive
    exact
      { leftIndex := index
        rightIndex := index
        left_ge := (show leftStart ≤ max leftStart rightStart from by
          rw [Order.max_eq_natMax]
          exact Order.le_max_left _ _).trans
          (Geometric.Search.firstQuarterBelow_ge scale start target)
        right_ge := (show rightStart ≤ max leftStart rightStart from by
          rw [Order.max_eq_natMax]
          exact Order.le_max_right _ _).trans
          (Geometric.Search.firstQuarterBelow_ge scale start target)
        close := by
          intro leftLater rightLater leftOrder _rightOrder
          have residualBound := sample_residual_le track leftLater
          have radiusLater := quarterRadius_antitone
            (CoherentRoot.residualScale_nonneg
              (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
                SquareRootDegree.degreeTwo)
              ambient track) leftOrder
          simpa only [squareApproximation_sample,
            Sequence.Constant.constantApproximation,
            Basic.Canonical.normSq, Data.Gaussian.Norm.Basic.normSq, pow_two] using
              residualBound.trans_lt (radiusLater.trans_lt radiusSmall) }

section
open Purelib.Approximation.Gaussian
open Purelib.Polynomial.Power
open Purelib.Riemann.RootContinuation
/-- The product of the original raw root name with itself is equivalent to the exact radicand name.

The comparison passes through the retained pointwise square approximation and its certified constant-parameter
comparison. -/
@[expose] def rawRoot_square {parameter : Gaussian} {ambient : Box}
    (track : WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) ambient) :
    NamedEquivalent
      (Name.Coherent.CoherentNamed.mul
        (rawRoot track) (rawRoot track)).name
      (Name.Basic.Named.exact parameter) := by
  let source := approximation track
  let product := squareApproximation track
  have actualToProduct : NamedEquivalent
      (Name.Basic.Named.mul source.toNamed source.toNamed)
      product.toNamed :=
    Sequence.Arithmetic.Multiplication.Bridge.mulToNamed_equivalent_pointwise
      source source product (by intro index; rfl)
  have productToConstant : NamedEquivalent product.toNamed
      (Sequence.Constant.constantApproximation parameter).toNamed :=
    Sequence.Name.Equivalence.approximationEquivalent_toNamed
      (squareApproximation_equivalent_parameter track)
  exact Equivalence.NamedEquivalent.trans
    (by simpa only [rawRoot,
      Name.Coherent.CoherentNamed.mul,
      Name.Coherent.CoherentNamed.ofApproximation, source, product]
      using actualToProduct)
    (Equivalence.NamedEquivalent.trans productToConstant
      (Equivalence.NamedEquivalent.symm
        (Sequence.Name.Exact.exact_toConstantNamed parameter)))

/-- The apartness-prepared root squares operationally to the exact original radicand.

Multiplication respects the retained equivalence between the prepared name and its original raw root name. -/
@[expose] def root_square {parameter : Gaussian} {ambient : Box}
    (parameterNonzero : parameter ≠ 0)
    (track : WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) ambient) :
    NamedEquivalent
      (Name.Coherent.CoherentNamed.mul
        (root parameterNonzero track)
        (root parameterNonzero track)).name
      (Name.Basic.Named.exact parameter) := by
  let raw := rawRoot track
  let prepared := root parameterNonzero track
  have preparedToRaw : NamedEquivalent prepared.name raw.name :=
    Equivalence.NamedEquivalent.symm
      (Name.Coherent.CoherentNamed.apartifyEquivalent raw
        (possibleApart parameterNonzero track))
  have products : NamedEquivalent
      (Name.Coherent.CoherentNamed.mul prepared prepared).name
      (Name.Coherent.CoherentNamed.mul raw raw).name :=
    Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
      prepared raw prepared raw preparedToRaw preparedToRaw
  exact Equivalence.NamedEquivalent.trans products
    (rawRoot_square track)

end

open Purelib.Approximation.Gaussian in
set_option genInjectivity false in
/-- A coherent root name retaining both apartness and operational equality of its square with the radicand.

The square comparison refers to the exact retained name, so the value and its division-safe certificate share the same
owner. -/
structure Certificate (parameter : Gaussian) where
  /-- The retained coherent Gaussian root name. -/ value : CoherentNamed
  /-- The retained root name stays quantitatively away from zero. -/ apart : Name.Basic.Named.Apart value.name
  /-- The square of the retained root name is equivalent to the exact original radicand. -/ square : NamedEquivalent
    (Name.Coherent.CoherentNamed.mul value value).name
    (Name.Basic.Named.exact parameter)

constructive_injectivity Certificate

open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
/-- Package the root, its apartness preparation and its square comparison from the original winding track.

All three fields refer to the same nonzero radicand and the same certified root track. -/
@[expose] def certificate {parameter : Gaussian} {ambient : Box}
    (parameterNonzero : parameter ≠ 0)
    (track : WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) ambient) :
    Certificate parameter where
  value := root parameterNonzero track
  apart := rootApart parameterNonzero track
  square := root_square parameterNonzero track

end Purelib.Riemann.RootContinuation.CertifiedSquareRoot

end
