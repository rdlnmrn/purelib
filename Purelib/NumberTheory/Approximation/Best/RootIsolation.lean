module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Fraction.NaturalDenominator
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.GaussianInt.Fraction.NaturalDenominator
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.NumberTheory.Approximation.Best.Basic
import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Best.Error
import Purelib.NumberTheory.Approximation.Best.Search
public import Purelib.NumberTheory.Approximation.Best.Successor.Select
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Winding.Box.Residual
public import Purelib.RootIsolation.Approximation.Denominator
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.NumberTheory.Approximation

open Purelib.Polynomial

section
@[expose] public section

/-!
# Best approximations of finite RAT responses

A root-approximation track is a finite request-and-response object, not an
unnamed completed root.  One response contains a displayed rational sample
strictly inside its new winding-one box, together with a polynomial residual
bound.  This module converts that sample to the Gaussian-denominator format
used by the best-approximation calculation.

The resulting program emits only pairs satisfying the full two-tier best
predicate for the displayed RAT response.  From a supplied best pair it
selects one pair at the next occupied denominator level.  The selector is
empty exactly when the supplied pair already has zero error, so every call
constructively returns either a genuine next best pair or an exact terminal
certificate.

No assertion is made about an unrepresented limiting point of the track.
-/

namespace Purelib.NumberTheory.Approximation.Best.RootIsolation

/-! ## RAT-response interface -/

/-- Convert the common-denominator sample returned by a finite RAT request to
the Gaussian-denominator source consumed by the best-approximation program. -/
def responseSource (sample :
  Gaussian.Basic.Canonical.Fraction.NaturalDenominator) : GaussianInt.Fraction :=
  GaussianInt.Fraction.NaturalDenominator.ofCommon sample

/-- Converting a common-denominator sample to a Gaussian-denominator source preserves its value. -/
theorem responseSource_value (sample :
  Gaussian.Basic.Canonical.Fraction.NaturalDenominator) :
    (responseSource sample).value = sample.value :=
  GaussianInt.Fraction.NaturalDenominator.ofCommon_value sample

/-- Complete finite list of all and only the best approximants to one
displayed rational RAT response. -/
def bestApproximations (sample :
  Gaussian.Basic.Canonical.Fraction.NaturalDenominator) : List GaussianInt.Pair.Basic.ConvergentPair :=
  Best.Search.allBest (responseSource sample)

/-- The computed response list contains exactly the best approximants to the sample value. -/
theorem mem_bestApproximations_iff
    (sample : Gaussian.Basic.Canonical.Fraction.NaturalDenominator) (pair : GaussianInt.Pair.Basic.ConvergentPair) :
    pair ∈ bestApproximations sample ↔ Best.Basic.IsBest sample.value pair := by
  rewrite [bestApproximations]
  have result := Best.Search.mem_allBest_iff_isBest
    (responseSource sample) pair
  rw [responseSource_value] at result
  exact result

/-- Every displayed RAT response has at least one computed best approximant. -/
theorem bestApproximations_nonempty (sample :
  Gaussian.Basic.Canonical.Fraction.NaturalDenominator) :
    bestApproximations sample ≠ [] := by
  obtain ⟨pair, best, _⟩ := Best.Successor.Select.exists_zeroErrorBest (responseSource sample)
  have sampleBest : Best.Basic.IsBest sample.value pair := by
    rwa [responseSource_value] at best
  have member := (mem_bestApproximations_iff sample pair).mpr sampleBest
  intro empty
  rw [empty] at member
  exact List.not_mem_nil member

/-- Select the next best approximant to one displayed RAT response. -/
def nextBestApproximation?
    (sample : Gaussian.Basic.Canonical.Fraction.NaturalDenominator) (lower : GaussianInt.Pair.Basic.ConvergentPair) :
      Option GaussianInt.Pair.Basic.ConvergentPair :=
  Best.Successor.Select.nextBest? (responseSource sample) lower

/-- The RAT-facing selector emits only genuine consecutive best
approximants. -/
theorem nextBestApproximation?_sound
    {sample : Gaussian.Basic.Canonical.Fraction.NaturalDenominator} {lower next : GaussianInt.Pair.Basic.ConvergentPair}
    (selected : nextBestApproximation? sample lower = some next) :
    Best.Consecutive.Basic.AreConsecutiveBest sample.value lower next := by
  have sound := Best.Successor.Select.nextBest?_sound selected
  rwa [responseSource_value] at sound

/-- For a certified best approximant to a RAT response, the executable
selector produces the next occupied best level or certifies exact
termination. -/
theorem nextBestApproximation_or_exactTerminal
    {sample : Gaussian.Basic.Canonical.Fraction.NaturalDenominator} {lower : GaussianInt.Pair.Basic.ConvergentPair}
    (lowerBest : Best.Basic.IsBest sample.value lower) :
    (∃ next : GaussianInt.Pair.Basic.ConvergentPair,
      nextBestApproximation? sample lower = some next ∧
        Best.Consecutive.Basic.AreConsecutiveBest sample.value lower next) ∨
      Best.Error.errorQuadrance sample.value lower = 0 := by
  have sourceBest : Best.Basic.IsBest (responseSource sample).value lower := by
    rwa [responseSource_value]
  have result := Best.Successor.Select.nextBest_or_exactTerminal sourceBest
  change (∃ next : GaussianInt.Pair.Basic.ConvergentPair,
    nextBestApproximation? sample lower = some next ∧
      Best.Consecutive.Basic.AreConsecutiveBest (responseSource sample).value lower next) ∨
    Best.Error.errorQuadrance (responseSource sample).value lower = 0 at result
  rw [responseSource_value] at result
  exact result

/-- The next-best selector for a RAT response is empty exactly at a displayed
zero-error terminal. -/
theorem nextBestApproximation?_eq_none_iff
    {sample : Gaussian.Basic.Canonical.Fraction.NaturalDenominator} {lower : GaussianInt.Pair.Basic.ConvergentPair}
    (lowerBest : Best.Basic.IsBest sample.value lower) :
    nextBestApproximation? sample lower = none ↔
      Best.Error.errorQuadrance sample.value lower = 0 := by
  have sourceBest : Best.Basic.IsBest (responseSource sample).value lower := by
    rwa [responseSource_value]
  have result := Best.Successor.Select.nextBest?_eq_none_iff sourceBest
  change nextBestApproximation? sample lower = none ↔
    Best.Error.errorQuadrance (responseSource sample).value lower = 0 at result
  rw [responseSource_value] at result
  exact result

/-! ## Exact finite observations -/

set_option genInjectivity false in
/-- Best-approximation arithmetic attached to one exact rational observation,
such as the degree-one branch of the finite FTA or a linear RFAP site. -/
structure PointBestResponse (point :
  Gaussian.Basic.Canonical) where
  /-- The exact point expressed with one positive natural common denominator. -/ sample :
    Gaussian.Basic.Canonical.Fraction.NaturalDenominator
  /-- The retained sample represents the specified point exactly. -/ sampleValue : sample.value = point
  /-- The retained finite list of best approximants to the point. -/ approximants : List
    GaussianInt.Pair.Basic.ConvergentPair
  /-- At least one best approximant is retained. -/ approximantsNonempty : approximants ≠ []
  /-- List membership is equivalent to bestness for the original point. -/ memApproximantsIff : ∀ pair :
    GaussianInt.Pair.Basic.ConvergentPair,
    pair ∈ approximants ↔ Best.Basic.IsBest point pair
  /-- The retained deterministic next-level selector on displayed pairs. -/ next? :
    GaussianInt.Pair.Basic.ConvergentPair → Option GaussianInt.Pair.Basic.ConvergentPair
  /-- Every selected successor is consecutive best for the original point. -/ nextSound : ∀ {lower next :
    GaussianInt.Pair.Basic.ConvergentPair}, next? lower = some next →
    Best.Consecutive.Basic.AreConsecutiveBest point lower next
  /-- A best pair has a selected consecutive successor or exactly represents the original point. -/ nextOrTerminal : ∀
    {lower : GaussianInt.Pair.Basic.ConvergentPair}, Best.Basic.IsBest point lower →
    (∃ next : GaussianInt.Pair.Basic.ConvergentPair, next? lower = some next ∧
      Best.Consecutive.Basic.AreConsecutiveBest point lower next) ∨
      Best.Error.errorQuadrance point lower = 0

constructive_injectivity PointBestResponse

/-- Construct the complete all-best and next-best package for an exact
displayed Gaussian-rational point. -/
def respondToPoint (point : Gaussian.Basic.Canonical) :
  PointBestResponse point := by
  let sample := Gaussian.Basic.Canonical.Fraction.NaturalDenominator.ofGaussian point
  have sampleValue : sample.value = point :=
    Gaussian.Basic.Canonical.Fraction.NaturalDenominator.ofGaussian_value point
  exact
    { sample := sample
      sampleValue := sampleValue
      approximants := bestApproximations sample
      approximantsNonempty := bestApproximations_nonempty sample
      memApproximantsIff := fun pair => by
        have result := mem_bestApproximations_iff sample pair
        rw [sampleValue] at result
        exact result
      next? := nextBestApproximation? sample
      nextSound := fun selected => by
        have sound := nextBestApproximation?_sound selected
        rwa [sampleValue] at sound
      nextOrTerminal := fun {lower} best => by
        have sampleBest : Best.Basic.IsBest sample.value lower := by
          rwa [sampleValue]
        have result := nextBestApproximation_or_exactTerminal sampleBest
        rw [sampleValue] at result
        exact result }

/-! ## Direct RFAP-I track responses -/

/-- The refined winding-one state returned by one finite call to an RFAP-I
root-approximation track. -/
def trackResponseState
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Geometry.Rational.Box}
    (track : RootIsolation.Track.Basic.WindingOneTrack p ambient) (current :
      RootIsolation.State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon) :
    RootIsolation.State.WindingOne.Basic.WindingOneState p ambient :=
  track.refine current epsilon epsilonPositive

/-- Canonical common-denominator presentation of the rational anchor carried
by one finite RFAP-I track response. -/
def trackResponseSample
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Geometry.Rational.Box}
    (track : RootIsolation.Track.Basic.WindingOneTrack p ambient) (current :
      RootIsolation.State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon) : Gaussian.Basic.Canonical.Fraction.NaturalDenominator
      :=
  Gaussian.Basic.Canonical.Fraction.NaturalDenominator.ofGaussian
    (trackResponseState track current epsilon epsilonPositive).box.anchor

/-- The canonical response sample represents the returned winding-one box anchor exactly. -/
theorem trackResponseSample_value
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Geometry.Rational.Box}
    (track : RootIsolation.Track.Basic.WindingOneTrack p ambient) (current :
      RootIsolation.State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon) :
    (trackResponseSample track current epsilon epsilonPositive).value =
      (trackResponseState track current epsilon epsilonPositive).box.anchor :=
  Gaussian.Basic.Canonical.Fraction.NaturalDenominator.ofGaussian_value _

/-- The displayed RAT response sample lies in its returned winding-one box. -/
theorem trackResponseSample_inside
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Geometry.Rational.Box}
    (track : RootIsolation.Track.Basic.WindingOneTrack p ambient) (current :
      RootIsolation.State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon) :
    (trackResponseState track current epsilon epsilonPositive).box.Contains
      (trackResponseSample track current epsilon epsilonPositive).value := by
  rw [trackResponseSample_value]
  exact Geometry.Rational.Box.contains_anchor _

/-- The state returned by the track refines the current box. -/
theorem trackResponseState_refines
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Geometry.Rational.Box}
    (track : RootIsolation.Track.Basic.WindingOneTrack p ambient) (current :
      RootIsolation.State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon) :
    (trackResponseState track current epsilon epsilonPositive).box.Refines
      current.box :=
  track.nested current epsilon epsilonPositive

/-- The returned box has squared diagonal at most the square of the positive requested accuracy. -/
theorem trackResponseState_accurate
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Geometry.Rational.Box}
    (track : RootIsolation.Track.Basic.WindingOneTrack p ambient) (current :
      RootIsolation.State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon) :
    (trackResponseState track current epsilon epsilonPositive).box.diagonalSq ≤
      epsilon ^ 2 :=
  track.accurate current epsilon epsilonPositive

/-- The canonical RAT response sample inherits the RFAP-I anchor residual
bound from the returned nonzero-winding box. -/
theorem trackResponseSample_residual_le
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Geometry.Rational.Box}
    (degreePositive : 0 < p.natDegree)
    (track : RootIsolation.Track.Basic.WindingOneTrack p ambient) (current :
      RootIsolation.State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon) :
    Data.Gaussian.Norm.Basic.normSq
        (p.eval (trackResponseSample track current epsilon epsilonPositive).value) ≤
      Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient
        (trackResponseState track current epsilon epsilonPositive).box := by
  rw [trackResponseSample_value]
  let state := trackResponseState track current epsilon epsilonPositive
  exact Winding.Box.Residual.anchor_residual_le_of_quadrupledBoxWinding_ne_zero
    p degreePositive state.refinesAmbient state.proper state.raw.rawWinding_ne

/-- Execute the complete all-best table at one direct response of an RFAP-I
root-approximation track. -/
def trackBestApproximations
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Geometry.Rational.Box}
    (track : RootIsolation.Track.Basic.WindingOneTrack p ambient) (current :
      RootIsolation.State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon) : List GaussianInt.Pair.Basic.ConvergentPair :=
  bestApproximations (trackResponseSample track current epsilon epsilonPositive)

-- Realize the retained equation in the opaque theorem context before exposed builders.
set_option Elab.async false in
/-- The computed track-response list contains exactly the best approximants to its box anchor. -/
theorem mem_trackBestApproximations_iff
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Geometry.Rational.Box}
    (track : RootIsolation.Track.Basic.WindingOneTrack p ambient) (current :
      RootIsolation.State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon) (pair : GaussianInt.Pair.Basic.ConvergentPair) :
    pair ∈ trackBestApproximations track current epsilon epsilonPositive ↔
      Best.Basic.IsBest
        (trackResponseState track current epsilon epsilonPositive).box.anchor
        pair := by
  rewrite [trackBestApproximations]
  have result := mem_bestApproximations_iff
    (trackResponseSample track current epsilon epsilonPositive) pair
  rw [trackResponseSample_value] at result
  exact result

/-- Every finite track response has a nonempty computed best-approximation list. -/
theorem trackBestApproximations_nonempty
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Geometry.Rational.Box}
    (track : RootIsolation.Track.Basic.WindingOneTrack p ambient) (current :
      RootIsolation.State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon) :
    trackBestApproximations track current epsilon epsilonPositive ≠ [] :=
  bestApproximations_nonempty
    (trackResponseSample track current epsilon epsilonPositive)

/-- Select one representative of the next occupied best level at a direct
RFAP-I track response. -/
def trackNextBestApproximation?
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Geometry.Rational.Box}
    (track : RootIsolation.Track.Basic.WindingOneTrack p ambient) (current :
      RootIsolation.State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (lower : GaussianInt.Pair.Basic.ConvergentPair) : Option GaussianInt.Pair.Basic.ConvergentPair :=
  nextBestApproximation?
    (trackResponseSample track current epsilon epsilonPositive) lower

/-- A successful track-response selection gives a consecutive best pair at the returned box anchor. -/
theorem trackNextBestApproximation?_sound
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Geometry.Rational.Box}
    {track : RootIsolation.Track.Basic.WindingOneTrack p ambient} {current :
      RootIsolation.State.WindingOne.Basic.WindingOneState p ambient}
    {epsilon : Fraction.Rational} {epsilonPositive : 0 < epsilon}
    {lower next : GaussianInt.Pair.Basic.ConvergentPair}
    (selected : trackNextBestApproximation? track current epsilon
      epsilonPositive lower = some next) :
    Best.Consecutive.Basic.AreConsecutiveBest
      (trackResponseState track current epsilon epsilonPositive).box.anchor
      lower next := by
  have sound := nextBestApproximation?_sound selected
  rwa [trackResponseSample_value] at sound

/-- Every best approximant to a direct RFAP-I track response has a computed
consecutive successor or is an exact terminal for that displayed response. -/
theorem trackNextBestApproximation_or_exactTerminal
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Geometry.Rational.Box}
    {track : RootIsolation.Track.Basic.WindingOneTrack p ambient} {current :
      RootIsolation.State.WindingOne.Basic.WindingOneState p ambient}
    {epsilon : Fraction.Rational} {epsilonPositive : 0 < epsilon}
    {lower : GaussianInt.Pair.Basic.ConvergentPair}
    (lowerBest : Best.Basic.IsBest
      (trackResponseState track current epsilon epsilonPositive).box.anchor
      lower) :
    (∃ next : GaussianInt.Pair.Basic.ConvergentPair,
      trackNextBestApproximation? track current epsilon epsilonPositive lower =
          some next ∧
        Best.Consecutive.Basic.AreConsecutiveBest
          (trackResponseState track current epsilon epsilonPositive).box.anchor
          lower next) ∨
      Best.Error.errorQuadrance
        (trackResponseState track current epsilon epsilonPositive).box.anchor
        lower = 0 := by
  have sampleBest : Best.Basic.IsBest
      (trackResponseSample track current epsilon epsilonPositive).value lower := by
    rwa [trackResponseSample_value]
  have result := nextBestApproximation_or_exactTerminal sampleBest
  change (∃ next : GaussianInt.Pair.Basic.ConvergentPair,
    trackNextBestApproximation? track current epsilon epsilonPositive lower =
        some next ∧
      Best.Consecutive.Basic.AreConsecutiveBest
        (trackResponseSample track current epsilon epsilonPositive).value
        lower next) ∨
    Best.Error.errorQuadrance
      (trackResponseSample track current epsilon epsilonPositive).value lower = 0
      at result
  rw [trackResponseSample_value] at result
  exact result

set_option genInjectivity false in
/-- One finite response of any RFAP-I root-approximation track, packaged with
its refinement, residual, complete all-best table, and total next-best step. -/
structure TrackBestResponse
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Geometry.Rational.Box}
    (degreePositive : 0 < p.natDegree)
    (track : RootIsolation.Track.Basic.WindingOneTrack p ambient) (current :
      RootIsolation.State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon) where
  /-- The retained winding-one state in the original polynomial and ambient box. -/ refined :
    RootIsolation.State.WindingOne.Basic.WindingOneState p ambient
  /-- The retained state refines the supplied current box. -/ refinesCurrent : refined.box.Refines current.box
  /-- The retained box meets the requested squared-diagonal bound. -/ accurate : refined.box.diagonalSq ≤ epsilon ^ 2
  /-- The retained rational sample with one positive natural common denominator. -/ sample :
    Gaussian.Basic.Canonical.Fraction.NaturalDenominator
  /-- The sample represents the retained refined box anchor exactly. -/ sampleValue : sample.value = refined.box.anchor
  /-- The retained refined box contains the sample value. -/ sampleInside : refined.box.Contains sample.value
  /-- The polynomial residual at the sample meets the bound determined by the original ambient and refined boxes. -/
    residualLe : Data.Gaussian.Norm.Basic.normSq (p.eval sample.value) ≤
    Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient refined.box
  /-- The retained finite best-approximation list for the sample value. -/ approximants : List
    GaussianInt.Pair.Basic.ConvergentPair
  /-- The retained sample has at least one listed best approximant. -/ approximantsNonempty : approximants ≠ []
  /-- The retained list contains all and only best approximants to this sample value. -/ memApproximantsIff : ∀ pair :
    GaussianInt.Pair.Basic.ConvergentPair,
    pair ∈ approximants ↔ Best.Basic.IsBest sample.value pair
  /-- The retained deterministic successor selector for this sample. -/ next? : GaussianInt.Pair.Basic.ConvergentPair →
    Option GaussianInt.Pair.Basic.ConvergentPair
  /-- Every selected pair is consecutive best above its supplied predecessor for this sample. -/ nextSound : ∀ {lower
    next : GaussianInt.Pair.Basic.ConvergentPair}, next? lower = some next →
    Best.Consecutive.Basic.AreConsecutiveBest sample.value lower next
  /-- Every best pair has a selected consecutive successor or zero error for this sample. -/ nextOrTerminal : ∀ {lower :
    GaussianInt.Pair.Basic.ConvergentPair}, Best.Basic.IsBest sample.value lower →
    (∃ next : GaussianInt.Pair.Basic.ConvergentPair, next? lower = some next ∧
      Best.Consecutive.Basic.AreConsecutiveBest sample.value lower next) ∨
      Best.Error.errorQuadrance sample.value lower = 0

constructive_injectivity TrackBestResponse

/-- Construct the complete proof-bearing response package by finite
calculation from an RFAP-I track call. -/
def respondToTrack
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Geometry.Rational.Box}
    (degreePositive : 0 < p.natDegree)
    (track : RootIsolation.Track.Basic.WindingOneTrack p ambient) (current :
      RootIsolation.State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon) :
    TrackBestResponse degreePositive track current epsilon epsilonPositive where
  refined := trackResponseState track current epsilon epsilonPositive
  refinesCurrent := trackResponseState_refines track current epsilon
    epsilonPositive
  accurate := trackResponseState_accurate track current epsilon epsilonPositive
  sample := trackResponseSample track current epsilon epsilonPositive
  sampleValue := trackResponseSample_value track current epsilon epsilonPositive
  sampleInside := trackResponseSample_inside track current epsilon epsilonPositive
  residualLe := trackResponseSample_residual_le degreePositive track current
    epsilon epsilonPositive
  approximants := trackBestApproximations track current epsilon epsilonPositive
  approximantsNonempty := trackBestApproximations_nonempty track current epsilon
    epsilonPositive
  memApproximantsIff := fun pair => by
    exact mem_bestApproximations_iff
      (trackResponseSample track current epsilon epsilonPositive) pair
  next? := trackNextBestApproximation? track current epsilon epsilonPositive
  nextSound := fun selected => by
    exact nextBestApproximation?_sound selected
  nextOrTerminal := fun best => by
    exact nextBestApproximation_or_exactTerminal best

/-! ## Polynomial RAT request -/

/-- Execute one polynomial RAT-compatible refinement request and retain its
interior rational response point and residual certificate. -/
def respond
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Geometry.Rational.Box}
      {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : RootIsolation.State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational}
    (epsilonPositive : 0 < epsilon) :
    RootIsolation.Approximation.Denominator.Output degreeAtLeastTwo squarefree elimination
      current epsilon :=
  RootIsolation.Approximation.Denominator.approximate degreeAtLeastTwo squarefree elimination
    current epsilonPositive

/-- The finite list computed from a polynomial RAT request contains all and
only the best approximants to that request's certified rational response. -/
theorem mem_bestApproximations_respond_iff
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Geometry.Rational.Box}
      {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : RootIsolation.State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational}
    (epsilonPositive : 0 < epsilon) (pair : GaussianInt.Pair.Basic.ConvergentPair) :
    pair ∈ bestApproximations
        (respond degreeAtLeastTwo squarefree elimination current
          epsilonPositive).fraction ↔
      Best.Basic.IsBest
        (respond degreeAtLeastTwo squarefree elimination current
          epsilonPositive).fraction.value pair :=
  mem_bestApproximations_iff _ _

/-- One polynomial RAT request therefore supports a total next-best step:
from any certified best response approximant, compute its genuine next best
level or certify that the response is represented exactly. -/
theorem respond_nextBest_or_exactTerminal
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Geometry.Rational.Box}
      {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : RootIsolation.State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational}
    (epsilonPositive : 0 < epsilon) (lower : GaussianInt.Pair.Basic.ConvergentPair)
    (lowerBest : Best.Basic.IsBest
      (respond degreeAtLeastTwo squarefree elimination current
        epsilonPositive).fraction.value lower) :
    (∃ next : GaussianInt.Pair.Basic.ConvergentPair,
      nextBestApproximation?
          (respond degreeAtLeastTwo squarefree elimination current
            epsilonPositive).fraction lower = some next ∧
        Best.Consecutive.Basic.AreConsecutiveBest
          (respond degreeAtLeastTwo squarefree elimination current
            epsilonPositive).fraction.value lower next) ∨
      Best.Error.errorQuadrance
        (respond degreeAtLeastTwo squarefree elimination current
          epsilonPositive).fraction.value lower = 0 :=
  nextBestApproximation_or_exactTerminal lowerBest

end Purelib.NumberTheory.Approximation.Best.RootIsolation

end
