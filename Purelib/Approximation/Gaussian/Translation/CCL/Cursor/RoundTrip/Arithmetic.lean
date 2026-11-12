module

public import Purelib.Approximation.Gaussian.Translation.CCL.Cursor.RoundTrip
public import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Name.Coherent.Law.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Equivalence

/-! # Unary arithmetic and composition through original retained cursor round trips -/

public section
namespace Purelib.Approximation.Gaussian.Translation.CCL.Cursor.RoundTrip.CertifiedApproximationCursorRoundTrip

open Purelib.Approximation.Gaussian.Equivalence (Equivalent NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Sequence (ApproximationData)
open Purelib.Approximation.Gaussian.Translation.CCL.Cursor.Basic (CursorObservation)

/-- Negation preserves the two original channels of a retained approximation/cursor round trip. -/
def neg_equivalent {approximation : ApproximationData}
    (certificate : CertifiedApproximationCursorRoundTrip approximation) :
    NamedEquivalent (CoherentNamed.neg (CoherentNamed.ofApproximation approximation)).name
      (CoherentNamed.neg
        (CoherentNamed.ofApproximation (CursorObservation.approximation approximation.toNamed))).name :=
  (Law.Arithmetic.negation_respects _ _ certificate.named).equivalent

/-- Every finite natural power preserves both original channels and the retained round-trip certificate. -/
def power_equivalent {approximation : ApproximationData}
    (certificate : CertifiedApproximationCursorRoundTrip approximation) (exponent : Nat) :
    NamedEquivalent (Power.namedPower (CoherentNamed.ofApproximation approximation) exponent).name
      (Power.namedPower
        (CoherentNamed.ofApproximation (CursorObservation.approximation approximation.toNamed)) exponent).name :=
  Power.namedPower_respects _ _ certificate.named exponent

/-- A finite power of the actual negated input preserves the same original round-trip owners. -/
def negPower_equivalent {approximation : ApproximationData}
    (certificate : CertifiedApproximationCursorRoundTrip approximation) (exponent : Nat) :
    NamedEquivalent
      (Power.namedPower (CoherentNamed.neg (CoherentNamed.ofApproximation approximation)) exponent).name
      (Power.namedPower (CoherentNamed.neg
        (CoherentNamed.ofApproximation (CursorObservation.approximation approximation.toNamed))) exponent).name :=
  Power.namedPower_respects _ _ certificate.neg_equivalent exponent

/-- Compose two original input comparisons through three actual retained cursor round trips.

The existing transitivity algorithm synchronizes the actual middle sampler and
allocates its quarter targets. All original round-trip witnesses are reused.
-/
def compareThrough {first middle last : ApproximationData}
    (left : CertifiedApproximationCursorRoundTrip first)
    (center : CertifiedApproximationCursorRoundTrip middle)
    (right : CertifiedApproximationCursorRoundTrip last)
    (firstMiddle : Equivalent first middle) (middleLast : Equivalent middle last) :
    Equivalent (CursorObservation.approximation first.toNamed) (CursorObservation.approximation last.toNamed) :=
  (left.compare center firstMiddle).trans (center.compare right middleLast)

end Purelib.Approximation.Gaussian.Translation.CCL.Cursor.RoundTrip.CertifiedApproximationCursorRoundTrip
end
