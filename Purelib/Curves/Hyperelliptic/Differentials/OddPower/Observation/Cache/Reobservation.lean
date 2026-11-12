module

public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Interpretation
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Independent evaluator payments on one retained scalar root observation

A new arithmetic request consumes the old complete evaluator cache and the
identical root observation. Both old and new numerical readings are retained,
with their existing generic operational observation comparison. The old
reading's visible radius remains explicit in their discrepancy bound.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Riemann.RootContinuation

variable {radicand : Coefficients} {differential : OddPowerDifferential radicand}
    {point : Canonical} {sheet : CoherentNamed} {apart : Name.Basic.Named.Apart sheet.name}
    {state : sheet.name.process.State} {rootObservation : RootObservation} {primary : AccuracyRequest}
    {coefficient : CoherentNamed} {floor : Fraction.Rational}

/-- A smaller free arithmetic request preserves the original root sample's fourth-order allowance.

Only the independently selected evaluator's free tolerance decreases. The
unchanged root observation keeps its actual primary residual and spread
payment, which pays the original allowance through the existing theorem.
-/
theorem errorBound_le_factor_of_tolerance_le {parameter : Canonical}
    (differential : OddPowerDifferential radicand) (point : Canonical)
    (root : CertifiedSquareRoot.Certificate parameter)
    {primary accuracy : AccuracyRequest} (sample : CertifiedSquareRoot.Sampling.ResidualObservation root primary)
    (paid : accuracy.tolerance ≤ primary.tolerance) {floor : Fraction.Rational} (positive : 0 < floor) :
    errorBound differential point floor sample.observation accuracy ≤
      allowanceFactor differential point root floor * primary.tolerance := by
  have comparison : errorBound differential point floor sample.observation accuracy ≤
      errorBound differential point floor sample.observation primary :=
    Fraction.Order.Arithmetic.add_le_add_direct paid
      (Fraction.Order.Basic.le_refl (4 * sensitivity differential point floor * sample.observation.spread))
  exact comparison.trans (errorBound_le_factor differential point root sample positive)

namespace Reading

/-- The old complete reading, a genuinely new request on its evaluator, and their actual observation comparison.

The new accuracy applies to both independently selected arithmetic states.
The original scalar root observation and its positive candidate floor remain
unchanged. The existing comparison stores both actual old/new observations,
not merely later samples that replace their displayed witnesses.
-/
@[expose] def Reobservation
    (retained : Reading differential point sheet apart state rootObservation primary coefficient floor)
    (accuracy : AccuracyRequest) :=
  (original : { cache : Reading differential point sheet apart state rootObservation primary coefficient floor //
    cache = retained }) ×
  (requested : Reading differential point sheet apart state rootObservation accuracy
    original.val.original.coefficient floor) ×
  Equivalence.Observation.Comparison original.val.original.asObservation requested.original.asObservation
    accuracy.tolerance

/-- Request independent arithmetic states on the actual old evaluator and compare both unchanged displayed readings. -/
def reobserve (retained : Reading differential point sheet apart state rootObservation primary coefficient floor)
    (accuracy : AccuracyRequest) : Reobservation retained accuracy := by
  let requested := Cache.request differential point sheet apart state rootObservation retained.original.rootCache_eq
    accuracy retained.original.coefficient retained.original.coefficient_eq floor retained.positive retained.lower
  have equivalent : NamedEquivalent retained.original.coefficient.name requested.original.coefficient.name :=
    NamedEquivalent.transport rfl (congrArg CoherentNamed.name requested.coefficient_eq.symm)
      (NamedEquivalent.refl retained.original.coefficient.name)
  let comparison := Equivalence.Observation.Comparison.build retained.original.asObservation
    requested.original.asObservation equivalent accuracy.tolerance accuracy.positive
  exact ⟨⟨retained, rfl⟩, requested, comparison⟩

namespace Reobservation

variable {retained : Reading differential point sheet apart state rootObservation primary coefficient floor}
    {accuracy : AccuracyRequest}

/-- Read the complete retained original arithmetic observation, including its old states and comparison. -/
@[expose] def original (paid : Reobservation retained accuracy) :
    Reading differential point sheet apart state rootObservation primary coefficient floor := paid.1.val

/-- The complete old observation is exactly the original input cache. -/
theorem original_eq (paid : Reobservation retained accuracy) : paid.original = retained := paid.1.property

/-- Read the genuinely new arithmetic observation on the identical retained original evaluator cache. -/
@[expose] def requested (paid : Reobservation retained accuracy) :
    Reading differential point sheet apart state rootObservation accuracy paid.original.original.coefficient floor :=
  paid.2.1

/-- Read the existing comparison on both actual old/new observation owners and displayed readings. -/
@[expose] def comparison (paid : Reobservation retained accuracy) :
    Equivalence.Observation.Comparison paid.original.original.asObservation paid.requested.original.asObservation
      accuracy.tolerance := paid.2.2

/-- The genuinely new arithmetic witness pays its own free request and the same retained root-observation spread. -/
theorem reading_close (paid : Reobservation retained accuracy) :
    Norm.Basic.normSq (paid.requested.reading - scalarReading differential point rootObservation) <
      errorBound differential point floor rootObservation accuracy := paid.requested.reading_close

/-- An independent actual root-spread payment bounds the new evaluator reading without any old arithmetic radius. -/
theorem reading_error_le (paid : Reobservation retained accuracy) {spread : Fraction.Rational}
    (rootPaid : rootObservation.spread ≤ spread) :
    Norm.Basic.normSq (paid.requested.reading - scalarReading differential point rootObservation) ≤
      accuracy.tolerance + 4 * sensitivity differential point floor * spread :=
  paid.reading_close.le.trans
    (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl accuracy.tolerance)
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rootPaid
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 4)
          (sensitivity_nonnegative differential point paid.original.positive))))

/-- The old displayed witness retains its honest original-radius cost in the actual old/new comparison. -/
theorem old_new_error_le (paid : Reobservation retained accuracy) :
    Norm.Basic.normSq (paid.original.reading - paid.requested.reading) ≤
      16 * (paid.original.original.asObservation.radius + paid.requested.original.asObservation.radius) +
        4 * accuracy.tolerance := paid.comparison.reading_error_le

end Reobservation

end Reading

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache

end
