module
public import Purelib.Approximation.Gaussian.Coherent.Additive
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
public import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
public import Purelib.Approximation.Gaussian.Provenance.Rational.Basic

import Purelib.Approximation.Gaussian.Arithmetic.Neg
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Data.Gaussian.Basic

open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Coherent

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian.Provenance

section
section
@[expose] public section

/-!
# Numerical channels with automatically propagated finite provenance

Arithmetic constructors keep the actual numerical program. Their sidecars
are derived by operational laws, never by treating approximate samples as
exact values. Unsupported combinations lose only the sidecar. This is a
small supported rule set, not general algebraic-number normalization.
-/

namespace Purelib.Approximation.Gaussian.Provenance.Rational.Arithmetic

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

/-- Transport exact Gaussian provenance through stateful negation of the original channel. -/
def negateRational {channel :
  Coherent.CoherentNamed} (rational : RationalSidecar channel) :
    RationalSidecar (CoherentNamed.neg channel) :=
  ⟨-rational.value, NamedEquivalent.trans
    (Additive.coherentNeg_respects channel
      (Coherence.exact rational.value) rational.equivalent)
    (Neg.exactNeg rational.value)⟩

/-- A retained exact rational value equal to zero gives the original channel an operational zero identity. -/
def rationalZero {channel : Coherent.CoherentNamed}
  (rational : RationalSidecar channel) (zero : rational.value = 0) :
    Purelib.Approximation.Gaussian.Equivalence.Zero.ZeroIdentity channel := by
  unfold Purelib.Approximation.Gaussian.Equivalence.Zero.ZeroIdentity
  simpa only [zero] using rational.equivalent
end Purelib.Approximation.Gaussian.Provenance.Rational.Arithmetic

end

end

section
@[expose] public section

/-! # Transporting exact rational provenance through finite arithmetic -/

namespace Purelib.Approximation.Gaussian.Provenance.Rational.Basic.RationalSidecar

/-- Transport the two original rational provenance certificates through coherent addition. -/
def add {first second :
  Coherent.CoherentNamed}
    (left : RationalSidecar first) (right : RationalSidecar second) :
    RationalSidecar (CoherentNamed.add first second) :=
  { value := left.value + right.value
    equivalent := NamedEquivalent.trans
      (Congruence.coherentAdd_respects first
        (Coherence.exact left.value) second
        (Coherence.exact right.value)
        left.equivalent right.equivalent)
      (Exact.Arithmetic.exact_add left.value right.value) }

/-- Transport the two original rational provenance certificates through coherent multiplication. -/
def mul {first second :
  Coherent.CoherentNamed}
    (left : RationalSidecar first) (right : RationalSidecar second) :
    RationalSidecar (CoherentNamed.mul first second) :=
  { value := left.value * right.value
    equivalent := NamedEquivalent.trans
      (Congruence.coherentMul_respects first
        (Coherence.exact left.value) second
        (Coherence.exact right.value)
        left.equivalent right.equivalent)
      (Exact.Arithmetic.exact_mul left.value right.value) }

/-- Symbolic cancellation supplies exact-zero provenance for any coherent input, without requiring exact rational
provenance for that input. -/
def addNeg (input :
  Coherent.CoherentNamed) :
    RationalSidecar (CoherentNamed.add input
      (CoherentNamed.neg input)) :=
  ⟨0, Neg.coherentAdd_neg_right input⟩
end Purelib.Approximation.Gaussian.Provenance.Rational.Basic.RationalSidecar

end
