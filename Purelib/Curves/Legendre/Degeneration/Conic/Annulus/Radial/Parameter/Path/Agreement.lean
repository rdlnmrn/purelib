module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Path
public import Purelib.Riemann.RootContinuation.FixedRootBoxPath.Preparation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.RootContinuation.SquareRootProvenance.Comparison
import Purelib.Geometry.Rational.Box.Square.Centered.Separation.Distance
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling

/-!
# Operational agreement of original nonlinear fixed-box branches

Both actual path owners retain their original endpoint Seed windows. A
quantified geometric bound on the two source centers pays the sum of their
actual root samples. Their same-radicand square identities then produce the
existing operational comparison, retaining both independently selected sample
indices. No near-root assumption or new square-root equivalence record is used.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Path.Cache

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

variable {site : Fin 2} {parameter increment : Canonical} {quarter : UnitCircuitQuarter}
variable {span : Interval.Bounds} {reference lastReference : Fraction.Rational}
variable {unit : Owner
  ((unitPolynomial site).eval (sourcePoint site parameter (Waist.direction quarter reference)).base)}
variable {source : Lift (sourcePoint site parameter (Waist.direction quarter reference)) unit}
variable {lastUnit : Owner
  ((unitPolynomial site).eval (sourcePoint site parameter (Waist.direction quarter lastReference)).base)}
variable {lastSource : Lift (sourcePoint site parameter (Waist.direction quarter lastReference)) lastUnit}
variable {first : Anchor source} {last : Anchor lastSource}
variable {admitted : IncrementBound site parameter increment}
variable {firstInside : span.Contains reference} {lastInside : span.Contains lastReference}
variable {width : span.width ^ 2 ≤ 1 / Fraction.Cast.fromInt 65536}

/-- Derive operational agreement of the two actual fixed-box path owners from the retained source-window geometry.

The original owners and both complete root certificates are constructed once
for the queried parameter. Every actual sampled reading stays in its respective
original Seed window. Their positive sum floor and same exact square identities
pay the generic comparison with both consumer start indices retained.
-/
def agreement (cache : Cache first last increment admitted firstInside lastInside width)
    (near : Norm.Basic.normSq
      ((sourcePoint site parameter (Waist.direction quarter lastReference)).ordinate -
        (sourcePoint site parameter (Waist.direction quarter reference)).ordinate) ≤
      first.seed.separation.radius ^ 2 / Fraction.Cast.fromInt 256)
    (index : Fraction.Rational) (inside : FixedRootBoxPath.Inside index) : cache.path.Agreement index inside := by
  unfold FixedRootBoxPath.PathData.Agreement
  let firstOwner := cache.path.First index inside
  let lastOwner := cache.path.Second index inside
  let firstRoot := firstOwner.certificate (cache.path.nonzero index inside)
  let lastRoot := lastOwner.certificate (cache.path.nonzero index inside)
  apply SquareRootProvenance.equivalent_of_sum_lower firstRoot.square lastRoot.square
    (first.seed.separation.radius ^ 2)
    (Fraction.Order.Arithmetic.pow_pos_direct first.seed.separation.positive 2)
  intro leftIndex rightIndex
  have firstPossible := Process.Sampling.witnessAt_possible
    firstRoot.value.name.process firstRoot.value.name.state leftIndex
  have lastPossible := Process.Sampling.witnessAt_possible
    lastRoot.value.name.process lastRoot.value.name.state rightIndex
  have firstContained := firstOwner.certificate_candidate_in_initial_box
    (cache.path.nonzero index inside) _ firstPossible
  have lastContained := lastOwner.certificate_candidate_in_initial_box
    (cache.path.nonzero index inside) _ lastPossible
  change (cache.path.First index inside).track.initial.box.Contains
    ((Name.Sampling.approximation firstRoot.value.name).sample leftIndex) at firstContained
  change (cache.path.Second index inside).track.initial.box.Contains
    ((Name.Sampling.approximation lastRoot.value.name).sample rightIndex) at lastContained
  rewrite [cache.first_box, first.seed.box_eq] at firstContained
  rewrite [cache.last_box, last.seed.box_eq] at lastContained
  have paid := first.seed.separation.near_sum_normSq_lower last.seed.separation near firstContained lastContained
  rewrite [Norm.Basic.normSq_eq_canonical] at paid
  exact paid

/-- The first original fixed-box branch at the finish agrees with the retained independent last Step root cache.

The two branches are compared at the same actual finish radicand. The existing
last-branch endpoint comparison then preserves the original last Step owner,
root certificate and its independently cached operational process.
-/
def firstFinishEquivalent (cache : Cache first last increment admitted firstInside lastInside width)
    (near : Norm.Basic.normSq
      ((sourcePoint site parameter (Waist.direction quarter lastReference)).ordinate -
        (sourcePoint site parameter (Waist.direction quarter reference)).ordinate) ≤
      first.seed.separation.radius ^ 2 / Fraction.Cast.fromInt 256)
    (step : Step last increment) (finish : span.upper = lastReference) :
    NamedEquivalent
      (ownerRootName (cache.path.nonzero 1 (by decide +kernel)) (cache.path.First 1 (by decide +kernel)))
      step.root.value.name :=
  (cache.path.expose (cache.agreement near 1 (by decide +kernel))).trans (cache.finishEquivalent step finish)

/-- Construct actual accepted normalized-root advances on the retained nonlinear path at its internally computed depth.

The two original Seed budgets and the complete nonlinear path are inputs
already retained by the cache. The original preparation computes sufficient
finite depth, shares each midpoint owner, and retains every actual advance
and endpoint handoff; no successful search or supplied cutoff is required.
-/
def prepare (cache : Cache first last increment admitted firstInside lastInside width) :
    FixedRootBoxPath.Preparation.Result cache.path :=
  FixedRootBoxPath.Preparation.Result.build cache.path

/-- The cached actual preparation starts on the same original independent first parameter Step root.

The complete supplied preparation remains an input. Its source cache equation
and the original path-start comparison preserve both actual starting owners.
-/
def prepared_startEquivalent (cache : Cache first last increment admitted firstInside lastInside width)
    (prepared : FixedRootBoxPath.Preparation.Result cache.path)
    (step : Step first increment) (start : span.lower = reference) :
    NamedEquivalent (ownerRootName prepared.source.parameterNonzero prepared.source) step.root.value.name := by
  have comparison := cache.startEquivalent step start
  rewrite [← prepared.source_eq] at comparison
  exact comparison

/-- The actual final advanced owner agrees with the retained independent last parameter Step root.

The original preparation retains its genuine final advance and comparison to
its own cached target. Cross-window path agreement and the original last-Step
comparison complete the handoff without reconstructing the preparation,
changing its depth, or identifying its distinct owners by fiat.
-/
def prepared_finishEquivalent (cache : Cache first last increment admitted firstInside lastInside width)
    (prepared : FixedRootBoxPath.Preparation.Result cache.path)
    (near : Norm.Basic.normSq
      ((sourcePoint site parameter (Waist.direction quarter lastReference)).ordinate -
        (sourcePoint site parameter (Waist.direction quarter reference)).ordinate) ≤
      first.seed.separation.radius ^ 2 / Fraction.Cast.fromInt 256)
    (step : Step last increment) (finish : span.upper = lastReference) :
    NamedEquivalent (ownerRootName prepared.finishOwner.parameterNonzero prepared.finishOwner)
      step.root.value.name := by
  have comparison := cache.firstFinishEquivalent near step finish
  rewrite [← prepared.target_eq] at comparison
  exact prepared.finish_agrees.trans comparison

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Path.Cache

end
