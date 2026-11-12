module

public import Purelib.Algebra.Quadratic.Pair.Gaussian
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Process.Addition
import Purelib.Approximation.Gaussian.Process.Multiplication
import Purelib.Approximation.Gaussian.Enclosure.Ball.Add
import Purelib.Approximation.Gaussian.Enclosure.Ball.Mul
import Purelib.Data.Rat.Fraction.Field

/-!
# Quadratic readings at one retained generator state

The original linear denotation consumes its generator's supplied state and
witness. Both exact coefficient states are retained directly; the resulting
reading and visible radius are derived from the actual arithmetic process.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Gaussian

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian
open Purelib.Data.Rat

variable {K : Type} {parameter : K}

/-- Use one original generator state in the exact two-coefficient denotation. -/
@[expose] def readingState (coefficient : K → Canonical) (original : CoherentNamed)
    (value : Pair K parameter) (state : original.name.process.State) :
    (denote coefficient original value).name.process.State :=
  ((), ((), state))

/-- The retained generator witness gives a possible reading of the same original denotation. -/
theorem reading_possible (coefficient : K → Canonical) (original : CoherentNamed)
    (value : Pair K parameter) (state : original.name.process.State) (root : Canonical)
    (possible : original.name.process.Possible state root) :
    (denote coefficient original value).name.process.Possible (readingState coefficient original value state)
      (coefficient value.re + coefficient value.im * root) :=
  ⟨coefficient value.re, coefficient value.im * root, rfl,
    ⟨coefficient value.im, root, rfl, possible, rfl⟩, rfl⟩

/-- The actual visible squared radius is eight times the retained generator radius and coefficient quadrance. -/
theorem reading_radius (coefficient : K → Canonical) (original : CoherentNamed)
    (value : Pair K parameter) (state : original.name.process.State) :
    ((denote coefficient original value).name.process.ball
      (readingState coefficient original value state)).radiusSq =
      8 * Norm.Basic.normSq (coefficient value.im) * (original.name.process.ball state).radiusSq := by
  change 2 * (0 + (4 * (0 * _ + Norm.Basic.normSq (coefficient value.im) *
    (original.name.process.ball state).radiusSq) + 2 * (0 * (original.name.process.ball state).radiusSq))) = _
  rewrite [Fraction.Field.zero_mul_direct, Fraction.Field.zero_add, Fraction.Field.zero_mul_direct,
    Fraction.Field.mul_zero_direct, Fraction.Field.add_comm _ 0, Fraction.Field.zero_add,
    Fraction.Field.zero_add, ← Fraction.Field.mul_assoc,
    show (2 : Fraction.Rational) * 4 = 8 by decide +kernel, ← Fraction.Field.mul_assoc]
  rfl

end Purelib.Algebra.Quadratic.Pair.Gaussian

end
