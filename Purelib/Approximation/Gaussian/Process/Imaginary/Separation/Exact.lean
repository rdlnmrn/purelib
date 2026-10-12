module
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Gaussian.Basic

import Purelib.Approximation.Gaussian.Acquisition.Provenance
public import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Absolute
import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Bounds.Abs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian.Process.Imaginary

section
@[expose] public section

/-!
# Evidence-directed finite Legendre words

Reuse a cached provider or separation first. Nonreal rational provenance
automatically constructs and transports an all-row provider. Otherwise one
signed numerical inspection prepares either half-plane, or returns retained
near-boundary evidence. Nonzeroness of the input alone is not used as a
certificate for every intermediate word denominator. Real inputs and
unsupported symbolic provenance may remain inconclusive by this sufficient
test; this is not a decision procedure for each particular real word.
-/

namespace Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Exact

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Acquisition (Provenance)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

open Purelib.Data.Rat in
/-- A nonreal exact Gaussian rational has an unsigned imaginary separation certificate.

The gap is the absolute imaginary coordinate; all possible readings of the exact coherent name equal the supplied
rational value. -/
def exactSeparation (value :
  Data.Gaussian.Basic.Canonical) (nonreal : value.im ≠ 0) :
    Approximation.Gaussian.Process.Imaginary.Separation (Coherence.exact value) := by
  have lower : ∀ {candidate : Purelib.Riemann.Integration.LegendreModularMonodromy.Gaussian},
      (Coherence.exact value).name.process.Possible (Coherence.exact value).name.state candidate →
      Fraction.abs value.im ≤ Fraction.abs candidate.im := by
    intro candidate possible
    change candidate = value at possible
    subst candidate
    exact Fraction.Order.Basic.le_refl _
  have positive : 0 < Fraction.abs value.im :=
    ⟨Fraction.Order.Arithmetic.abs_nonneg_direct _, fun reverse =>
      (Bounds.Abs.abs_ne_zero_direct nonreal)
        (Data.Rat.Fraction.Order.Basic.le_antisymm _ _ reverse
          (Fraction.Order.Arithmetic.abs_nonneg_direct _))⟩
  exact Separation.ofAbsolute (Coherence.exact value).name.state
    (Fraction.abs value.im) positive lower
end Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Exact

end
