module

public import Purelib.Riemann.Branches.PreparedSheetContinuationCore
public import Purelib.Approximation.Gaussian.Equivalence.Observation
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Actual source comparisons after retained root preparation

An original CachedSource keeps its exact prepared Owner. Its existing
reconditioning comparison transports a separately established source-channel
agreement to that retained Owner's supplied Certificate. Both original
possible-reading requests and the actual based-tail comparison are cached;
no target advance or final endpoint agreement is assumed.
-/

public section

namespace Purelib.Riemann.Branches.PreparedSheetContinuation.CachedSource

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Canonical}
variable {segment : ClearSegment polynomial ambient start finish} {current : Endpoint}
variable {owner : Owner (polynomial.eval (segment.pointAt current.parameter))} {request : StepRequest}

/-- The existing preparation comparison preserves the exact supplied cached Owner and both original root names. -/
def sourceEquivalent (cached : CachedSource segment current owner request) :
    NamedEquivalent (owner.certificate owner.parameterNonzero).value.name
      (cached.preparedOwner.certificate cached.preparedOwner.parameterNonzero).value.name := by
  have retained := congrArg
    (fun actual : Owner (polynomial.eval (segment.pointAt current.parameter)) =>
      (actual.certificate actual.parameterNonzero).value.name) cached.preparedOwner_eq
  exact NamedEquivalent.transport rfl retained.symm (sourceRootEquivalent segment current owner request)

/-- Compose original source agreement with the exact cached preparation and supplied full certificate identity. -/
def channelEquivalent (cached : CachedSource segment current owner request)
    (root : CertifiedSquareRoot.Certificate (polynomial.eval (segment.pointAt current.parameter)))
    (root_eq : root = cached.preparedOwner.certificate cached.preparedOwner.parameterNonzero)
    (channel : CoherentNamed)
    (agreement : NamedEquivalent channel.name (owner.certificate owner.parameterNonzero).value.name) :
    NamedEquivalent channel.name root.value.name := by
  have retainedName := congrArg (fun certificate : CertifiedSquareRoot.Certificate
    (polynomial.eval (segment.pointAt current.parameter)) => certificate.value.name) root_eq
  exact NamedEquivalent.transport rfl retainedName.symm (agreement.trans cached.sourceEquivalent)

/-- Actual original channel requests and their retained paid comparison after one exact cached preparation.

The existing request objects preserve their original states, finite witnesses,
radii and request equations. The existing Comparison retains both inputs,
actual based views, tail indices, sampled readings and residual bound.
-/
@[expose] def PaidComparison (cached : CachedSource segment current owner request)
    (root : CertifiedSquareRoot.Certificate (polynomial.eval (segment.pointAt current.parameter)))
    (_root_eq : root = cached.preparedOwner.certificate cached.preparedOwner.parameterNonzero)
    (channel : CoherentNamed) (accuracy : Fraction.Rational) : Type 1 :=
  Σ first : Equivalence.Observation.Request channel (accuracy / 64),
    Σ last : Equivalence.Observation.Request root.value (accuracy / 64),
      { compared : Equivalence.Observation.Comparison first.reading last.reading (accuracy / 16) //
          compared.bound ≤ accuracy }

/-- Reuse the exact supplied prepared root certificate and derive one paid actual two-reading comparison.

The input agreement concerns the original source Owner at the same point.
Preparation's original reconditioning comparison supplies the new source
agreement internally. Requests run once on the supplied channel and the
retained prepared Certificate. That supplied cache remains unchanged; the
original source-comparison procedure may reconstruct its own canonical
preparation or common track, so internal preparation reuse is not asserted.
-/
def compare (cached : CachedSource segment current owner request)
    (root : CertifiedSquareRoot.Certificate (polynomial.eval (segment.pointAt current.parameter)))
    (root_eq : root = cached.preparedOwner.certificate cached.preparedOwner.parameterNonzero)
    (channel : CoherentNamed)
    (agreement : NamedEquivalent channel.name (owner.certificate owner.parameterNonzero).value.name)
    (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    PaidComparison cached root root_eq channel accuracy := by
  let radius := accuracy / 64
  have radiusPositive : 0 < radius := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  let first := Equivalence.Observation.Request.build channel radius radiusPositive
  let last := Equivalence.Observation.Request.build root.value radius radiusPositive
  let equivalent := cached.channelEquivalent root root_eq channel agreement
  let tolerance := accuracy / 16
  have tolerancePositive : 0 < tolerance := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  let compared := Equivalence.Observation.Comparison.build first.reading last.reading equivalent
    tolerance tolerancePositive
  have paid : compared.bound ≤ accuracy := by
    rewrite [compared.bound_eq]
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct first.radius_lt.le last.radius_lt.le)
      (by decide +kernel : (0 : Fraction.Rational) ≤ 16)
    calc
      _ ≤ 16 * (accuracy / 64 + accuracy / 64) + 4 * (accuracy / 16) :=
        Fraction.Order.Arithmetic.add_le_add_direct scaled (Fraction.Order.Basic.le_refl _)
      _ = (3 / 4) * accuracy := by
        simp only [Fraction.Field.div_eq_mul_inv_direct accuracy 64,
          Fraction.Field.div_eq_mul_inv_direct accuracy 16, -eq_self, -iff_self]
        have scalar : (16 * (2 * (64 : Fraction.Rational)⁻¹) +
            4 * (16 : Fraction.Rational)⁻¹) = 3 / 4 := by decide +kernel
        calc
          _ = (16 * (2 * (64 : Fraction.Rational)⁻¹) + 4 * (16 : Fraction.Rational)⁻¹) * accuracy := by ring1
          _ = _ := by rewrite [scalar]; rfl
      _ ≤ 1 * accuracy := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (by decide +kernel : (3 / 4 : Fraction.Rational) ≤ 1) positive.le
      _ = _ := Fraction.Field.one_mul _
  exact ⟨first, last, compared, paid⟩

namespace PaidComparison

variable {cached : CachedSource segment current owner request}
variable {root : CertifiedSquareRoot.Certificate (polynomial.eval (segment.pointAt current.parameter))}
variable {root_eq : root = cached.preparedOwner.certificate cached.preparedOwner.parameterNonzero}
variable {channel : CoherentNamed} {accuracy : Fraction.Rational}

/-- Read the complete original channel request retained by the preparation comparison. -/
@[expose] def first (paid : PaidComparison cached root root_eq channel accuracy) :
    Equivalence.Observation.Request channel (accuracy / 64) := paid.1

/-- Read the entire original prepared Certificate request, preserving its actual state and finite witness. -/
@[expose] def last (paid : PaidComparison cached root root_eq channel accuracy) :
    Equivalence.Observation.Request root.value (accuracy / 64) := paid.2.1

/-- Read the complete original operational comparison on those same two retained possible readings. -/
@[expose] def comparison (paid : PaidComparison cached root root_eq channel accuracy) :
    Equivalence.Observation.Comparison paid.first.reading paid.last.reading (accuracy / 16) := paid.2.2.val

/-- The exact actual difference of the retained original readings pays the supplied accuracy. -/
theorem residual_le (paid : PaidComparison cached root root_eq channel accuracy) :
    Norm.Basic.normSq (paid.first.reading.value - paid.last.reading.value) ≤ accuracy := by
  have bound := paid.comparison.residual_le
  rewrite [paid.comparison.residual_eq] at bound
  exact bound.trans paid.2.2.property

end PaidComparison

end Purelib.Riemann.Branches.PreparedSheetContinuation.CachedSource
