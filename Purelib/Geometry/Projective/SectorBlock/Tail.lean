module

public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Contraction
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Projective.Line.Basic
import Purelib.Tactic.QuotientFreeOmega

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Basic

section
section
@[expose] public section
namespace Purelib.Geometry.Projective.SectorBlock.Tail

/-- A displayed tail equation for one compatible completed sector. It is the cross-multiplied form of `value = s + 1/(γ
tail)`. -/
structure CompatibleTail (sector :
  Sector) (tail value
  : Data.Gaussian.Basic.Canonical) : Prop where
  /-- The cleared homographic equation relating tail, value, and sector representative. -/ equation :
    Canonical.gamma * tail * value = Canonical.gamma * tail * sector.rep + 1
  /-- The value lies in the canonical annular band. -/ band : Sector.Band value
  /-- The value satisfies the selected sector predicate. -/ holds : sector.Holds value

end Purelib.Geometry.Projective.SectorBlock.Tail
end
end

end

section
@[expose] public section
namespace Purelib.Geometry.Projective.SectorBlock.Tail
/-- The exact completed-sector compatibility predicate. -/
abbrev SourceEncodingEncoderCompatibleTailAlias :=
  CompatibleTail
end Purelib.Geometry.Projective.SectorBlock.Tail

end

section
section
@[expose] public section
namespace Purelib.Geometry.Projective.SectorBlock.Tail.CompatibleTail
section CompatibleTail

/-- Compatibility gives the cleared residual identity `gamma*tail*(value-sector.rep)=1`. -/
theorem residual_equation {sector :
  Sector} {tail value : Data.Gaussian.Basic.Canonical}
    (compatible : CompatibleTail sector tail value) :
    Canonical.gamma * tail * (value - sector.rep) = 1 := by
  calc
    Canonical.gamma * tail * (value - sector.rep) =
        Canonical.gamma * tail * value - Canonical.gamma * tail * sector.rep :=
          by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1
    _ = 1 := by
      rw [compatible.equation]
      apply Data.Gaussian.Basic.ext <;>
        simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.one_re, Basic.one_im] <;>
          ring1
end CompatibleTail
end Purelib.Geometry.Projective.SectorBlock.Tail.CompatibleTail
end
end

end

section
section
@[expose] public section
namespace Purelib.Geometry.Projective.SectorBlock.Tail.CompatibleTail
section CompatibleTail

/-- The tail squared norm times twice the residual squared norm equals one. -/
theorem norm_equation {sector :
  Sector}
  {tail value : Data.Gaussian.Basic.Canonical}
    (compatible : CompatibleTail sector tail value) :
    (2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep)) * Data.Gaussian.Norm.Basic.normSq tail
      = 1 := by
  have normEquation := congrArg Data.Gaussian.Norm.Basic.normSq
    (residual_equation compatible)
  rw [Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_mul, Constants.normSq_gamma,
    Data.Gaussian.Norm.Basic.normSq_one] at normEquation
  calc
    (2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep)) * Data.Gaussian.Norm.Basic.normSq tail
      =
        2 * Data.Gaussian.Norm.Basic.normSq tail * Data.Gaussian.Norm.Basic.normSq (value -
          sector.rep) := by ring1
    _ = 1 := normEquation
end CompatibleTail
end Purelib.Geometry.Projective.SectorBlock.Tail.CompatibleTail
end
end

end

section
section
@[expose] public section
namespace Purelib.Geometry.Projective.SectorBlock.Tail.CompatibleTail
section CompatibleTail

/-- A compatible affine tail is nonzero. -/
theorem tail_nonzero {sector :
  Sector}
  {tail value : Data.Gaussian.Basic.Canonical}
    (compatible : CompatibleTail sector tail value) : tail ≠ 0 := by
  intro tailZero
  have equation := compatible.equation
  simp only [tailZero,
    Data.Gaussian.Basic.mul_zero,
    Data.Gaussian.Basic.zero_mul,
    Data.Gaussian.Basic.zero_add] at equation
  exact one_ne_zero equation.symm
end CompatibleTail
end Purelib.Geometry.Projective.SectorBlock.Tail.CompatibleTail
end
end

end

section
section
@[expose] public section
namespace Purelib.Geometry.Projective.SectorBlock.Tail.CompatibleTail
section CompatibleTail

/-- A canonical compatible tail has squared norm strictly greater than one.

The sector contraction bound and the retained norm identity give the strict inequality. -/
theorem tail_norm_gt_one {sector :
  Sector} {tail value : Data.Gaussian.Basic.Canonical}
    (compatible : CompatibleTail sector tail value) :
    1 < Data.Gaussian.Norm.Basic.normSq tail := by
  have contraction := Sector.contraction compatible.band sector compatible.holds
  have factorLess : 2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep) < (1 : Fraction.Rational) := by
    calc
      2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep) < 2 * (1 / 2 : Fraction.Rational) :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          (by decide) contraction
      _ = 1 := by decide
  by_cases greater : 1 < Data.Gaussian.Norm.Basic.normSq tail
  · exact greater
  · have tailLe : Data.Gaussian.Norm.Basic.normSq tail ≤ 1 := le_of_not_gt greater
    have factorNonnegative :
        0 ≤ 2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep) :=
      Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    have productLe :
        (2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep)) * Data.Gaussian.Norm.Basic.normSq
          tail ≤
          (2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep)) * 1 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct tailLe
        factorNonnegative
    have oneLtOne : (1 : Fraction.Rational) < 1 := by
      calc
        1 = (2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep)) *
          Data.Gaussian.Norm.Basic.normSq tail :=
          compatible.norm_equation.symm
        _ ≤ (2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep)) * 1 := productLe
        _ = 2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep) := by ring1
        _ < 1 := factorLess
    exact (lt_irrefl 1 oneLtOne).elim
end CompatibleTail
end Purelib.Geometry.Projective.SectorBlock.Tail.CompatibleTail
end
end

end

section
section
@[expose] public section
namespace Purelib.Geometry.Projective.SectorBlock

set_option genInjectivity false in
/-- A finite compatible tail is either an affine continuation with its exact branch certificate or the formal terminal
coordinate.

An affine tail retains its original Gaussian tail, source value and completed-sector equation. The terminal constructor
retains the distinct formal endpoint in the same sector, without identifying it with an affine value. -/
inductive Tail (sector : Sector) where
  /-- The terminal tail representing the selected sector representative. -/ | omega
  /-- An affine tail and source value with their exact compatibility certificate. -/ | affine (tail value :
    Data.Gaussian.Basic.Canonical) (compatible : Geometry.Projective.SectorBlock.Tail.CompatibleTail sector tail value)

constructive_injectivity Tail

namespace Tail.affine

end Tail.affine

end Purelib.Geometry.Projective.SectorBlock
end
end

end

section
@[expose] public section
namespace Purelib.Geometry.Projective.SectorBlock.Tail
/-- The finite affine-or-terminal compatible-tail type. -/
abbrev SourceEncodingEncoderTailAlias :=
  Tail
end Purelib.Geometry.Projective.SectorBlock.Tail

end

section
section
@[expose] public section
namespace Purelib.Geometry.Projective.SectorBlock.Tail
section Tail

/-- The canonical tail is the terminal tail exactly at the selected representative, or an affine compatible tail for the
displayed value. -/
def ModelsValue {sector : Sector} (tail :
  Tail sector) (value : Data.Gaussian.Basic.Canonical) : Prop :=
  match tail with
  | .omega => value = sector.rep
  | .affine _ storedValue _ => storedValue = value
end Tail
end Purelib.Geometry.Projective.SectorBlock.Tail
end
end

end

section
section
@[expose] public section
namespace Purelib.Geometry.Projective.SectorBlock.Tail
section Tail

/-- Read a compatible tail as its affine or terminal homogeneous coordinate pair. -/
def point {sector : Sector} :
  Tail sector → GaussianLine
  | .omega => Proj.omega
  | .affine tail _ _ => Proj.affine tail
end Tail
end Purelib.Geometry.Projective.SectorBlock.Tail
end
end

end
