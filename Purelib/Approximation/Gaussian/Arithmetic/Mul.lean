module
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Bridge
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Name

namespace Purelib.Approximation.Gaussian.Arithmetic.Mul

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Gaussian.Sequence.Name

section
public section

/-!
# Numerical channels with automatically propagated finite provenance

Arithmetic constructors keep the actual numerical program. Their sidecars
are derived by operational laws, never by treating approximate samples as
exact values. Unsupported combinations lose only the sidecar. This is a
small supported rule set, not general algebraic-number normalization.
-/

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

/-- Replace the right factor by its retained exact rational provenance while preserving the operational product. -/
@[expose] def mulRightConstant (left right : Coherent.CoherentNamed) (rational : Rational.Basic.RationalSidecar right) :
    Gaussian.Equivalence.NamedEquivalent (CoherentNamed.mul left right).name
      (CoherentNamed.mul left
        (Coherence.exact rational.value)).name :=
  Congruence.coherentMul_respects left left right
    (Coherence.exact rational.value)
    (NamedEquivalent.refl _) rational.equivalent

/-- Replace the left factor by its retained exact rational provenance while preserving the operational product. -/
@[expose] def mulLeftConstant (left right : Coherent.CoherentNamed) (rational : Rational.Basic.RationalSidecar left) :
    Gaussian.Equivalence.NamedEquivalent (CoherentNamed.mul left right).name
      (CoherentNamed.mul
        (Coherence.exact rational.value) right).name :=
  Congruence.coherentMul_respects left
    (Coherence.exact rational.value) right right rational.equivalent
    (NamedEquivalent.refl _)

end

section
public section

/-!
# Operational field laws for coherent CCL names

The declarations in this module compare productive finite processes.  They do
not assign a completed value to a nonterminating CCL.  Exact constants below
are introduced only through the terminating Gaussian-rational constructor.
-/

/-- Multiplication by the terminating exact unit on the right changes no finite operational observation. -/
@[expose] def coherentMul_one_right (input : CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul input.name
        (Named.exact 1))
      input.name := by
  let one := Coherence.exact 1
  let inputApproximation :=
    Sampling.approximation input.name
  have pointwise : Gaussian.Equivalence.NamedEquivalent
      (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation input.name one.name).toNamed
      inputApproximation.toNamed :=
    Equivalence.approximationEquivalent_toNamed
      (Equivalence.approximationEquivalentOfSamplesEq
        (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation input.name one.name)
        inputApproximation
        (by
          intro index
          rw [Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation_sample]
          change inputApproximation.sample index * 1 =
            inputApproximation.sample index
          exact Data.Gaussian.Basic.mul_one _))
  exact NamedEquivalent.trans
    (by
      simpa only [one, Coherence.exact,
        Coherence.exact] using
        Bridge.coherentMul_toNamed input one)
    (NamedEquivalent.trans pointwise
      (NamedEquivalent.symm
        (Equivalence.named_toSamplingNamed input.name)))

/-- Multiplication by the terminating exact unit on the left changes no finite operational observation. -/
@[expose] def coherentMul_one_left (input : CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        (Named.exact 1) input.name)
      input.name :=
  NamedEquivalent.trans
    (Laws.coherentMul_comm (Coherence.exact 1) input)
    (Approximation.Gaussian.Arithmetic.Mul.coherentMul_one_right input)

/-- Multiplication by the terminating exact zero on the right is operationally the terminating exact zero. -/
@[expose] def coherentMul_zero_right (input : CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul input.name
        (Named.exact 0))
      (Named.exact 0) := by
  let zero := Coherence.exact 0
  let zeroApproximation :=
    Sampling.approximation
      (Named.exact 0)
  have pointwise : Gaussian.Equivalence.NamedEquivalent
      (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation input.name zero.name).toNamed
      zeroApproximation.toNamed :=
    Equivalence.approximationEquivalent_toNamed
      (Equivalence.approximationEquivalentOfSamplesEq
        (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation input.name zero.name)
        zeroApproximation
        (by
          intro index
          rw [Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation_sample]
          change
            (Sampling.approximation input.name).sample
                index * 0 = 0
          exact Data.Gaussian.Basic.mul_zero _))
  exact NamedEquivalent.trans
    (by
      simpa only [zero, Coherence.exact,
        Coherence.exact] using
        Bridge.coherentMul_toNamed input zero)
    (NamedEquivalent.trans pointwise
      (NamedEquivalent.symm
        (Equivalence.named_toSamplingNamed
          (Named.exact 0))))

/-- Multiplication by exact zero on the left has the symmetric law. -/
@[expose] def coherentMul_zero_left (input : CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        (Named.exact 0) input.name)
      (Named.exact 0) :=
  NamedEquivalent.trans
    (Laws.coherentMul_comm (Coherence.exact 0) input)
    (Approximation.Gaussian.Arithmetic.Mul.coherentMul_zero_right input)

end

public section

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
-/

/-- Multiply the original coherent name by the exact Gaussian factor on the left. -/
@[expose] def scaleName (factor : Data.Gaussian.Basic.Canonical) (value : Coherent.CoherentNamed) :
  Coherent.CoherentNamed :=
  CoherentNamed.mul (Coherent.CoherentNamed.Coherence.exact factor) value

end

end
end

end Purelib.Approximation.Gaussian.Arithmetic.Mul
