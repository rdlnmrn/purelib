module
import Purelib.Approximation.Gaussian.Division.Prepared.Equivalence
public import Purelib.Approximation.Gaussian.Division.Prepared.Decision.Laws
public import Purelib.Approximation.Gaussian.Division.Prepared.Rational
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic

open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division.Prepared

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Provenance

section
@[expose] public section

/-!
# Semantic completeness and invariance of exact division decisions

Exact zero means an executable operational comparison with zero exists;
preparability means an equivalent whole-ball-apart presentation exists.
Neither predicate demands pointwise equality of approximate candidates.
The converse completeness laws require a computed exact decision, supplied
below by rational provenance and by the separate algebraic client. They are
not equality decisions for arbitrary opaque channels.
-/

namespace Purelib.Approximation.Gaussian.Provenance.Rational.Basic.RationalSidecar

/-- For a channel with retained rational provenance, operational zero is equivalent to absence of a prepared
denominator. -/
theorem zero_iff_unpreparable {channel :
  Coherent.CoherentNamed}
    (sidecar : RationalSidecar channel) : Zero.IsZero channel ↔ ¬ Equivalence.IsPrepared channel :=
  sidecar.decide.zero_iff_unpreparable

/-- For a channel with retained rational provenance, preparation is equivalent to absence of an operational zero
identity. -/
theorem prepared_iff_nonzero {channel :
  Coherent.CoherentNamed}
    (sidecar : RationalSidecar channel) : Equivalence.IsPrepared channel ↔ ¬ Zero.IsZero channel :=
  sidecar.decide.prepared_iff_nonzero

/-- Rational provenance decisions for operationally equivalent original channels give the same preparation flag. -/
theorem decide_respects {first second :
  Coherent.CoherentNamed}
    (left : RationalSidecar first) (right : RationalSidecar second)
    (equivalent : Gaussian.Equivalence.NamedEquivalent first.name second.name) :
    left.decide.isPrepared = right.decide.isPrepared := left.decide.respects right.decide equivalent

end Purelib.Approximation.Gaussian.Provenance.Rational.Basic.RationalSidecar

end
