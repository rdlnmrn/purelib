module
import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Data.GaussianInt.Pair.Basic

import Purelib.Data.GaussianInt.Basic
import Mathlib.Order.Basic

@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Hurwitz.Continuant

open Purelib.Data in
/-- Prepend an integer digit to a retained convergent pair by the original numerator-denominator recurrence. -/
def prepend (head :
  Data.GaussianInt.Fraction.Basic.Integer) (tail : GaussianInt.Pair.Basic.ConvergentPair) :
  GaussianInt.Pair.Basic.ConvergentPair :=
  ⟨head * tail.numerator + tail.denominator, tail.numerator⟩
end Purelib.Data.ComplexContinuedFraction.Hurwitz.Continuant
end

@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Hurwitz.Continuant

open Purelib.Data in
/-- Compute the integral continuant pair of a finite Hurwitz digit list.

The empty list gives the pair one over zero. Each retained head replaces the tail pair by head times its numerator plus
denominator over its numerator, without fraction normalization. -/
def continuant : List
  Data.GaussianInt.Fraction.Basic.Integer → GaussianInt.Pair.Basic.ConvergentPair
  | [] => ⟨1, 0⟩
  | head :: tail => prepend head
    (continuant tail)
end Purelib.Data.ComplexContinuedFraction.Hurwitz.Continuant
end

@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Hurwitz.Continuant

open Purelib.Data in
/-- The continuant of a nonempty list is the current digit prepended to the retained tail continuant. -/
@[simp] theorem continuant_cons (head :
  Data.GaussianInt.Fraction.Basic.Integer)
    (tail : List Data.GaussianInt.Fraction.Basic.Integer) :
    continuant (head :: tail) =
      prepend head (continuant
      tail) := rfl
end Purelib.Data.ComplexContinuedFraction.Hurwitz.Continuant
end

@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Hurwitz.Continuant

open Purelib.Data in
/-- The empty continuant is the integral pair one over zero. -/
@[simp] theorem continuant_nil :
  continuant [] = ⟨1, 0⟩ := rfl
end Purelib.Data.ComplexContinuedFraction.Hurwitz.Continuant
end
