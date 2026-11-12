module

public import Purelib.Algebra.Quadratic.Pair.Gaussian
public import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Real
import Purelib.Data.Gaussian.Basic

/-!
# Rational quadratic coordinates at a retained Gaussian channel

The real-axis coefficient map interprets the original rational pair owner.
Its parameter retains the pair convention: a generator satisfying `r² = q`
interprets `Pair Rational (-q)`, on either original supplied root sheet.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Gaussian

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)

variable {parameter : Rational}

/-- Interpret the original rational pair at the same retained generator and exact real-axis coefficients. -/
@[expose] def denoteRational (generator : CoherentNamed) (value : Pair Rational parameter) : CoherentNamed :=
  denote Cast.CoordinateTaylor.ofCoordinate generator value

/-- Rational scalar coordinates compare to their original exact real-axis channel. -/
def denoteRational_scalar (generator : CoherentNamed) (value : Rational) :
    NamedEquivalent (denoteRational generator (Pair.scalar value : Pair Rational parameter)).name
      (Coherence.exact (Cast.CoordinateTaylor.ofCoordinate value)).name :=
  denote_scalar Cast.CoordinateTaylor.ofCoordinate Cast.ofCoordinate_zero generator value

/-- Addition of original rational pair coordinates retains its operational numerical sum. -/
def denoteRational_add (generator : CoherentNamed) (left right : Pair Rational parameter) :
    NamedEquivalent (CoherentNamed.add (denoteRational generator left) (denoteRational generator right)).name
      (denoteRational generator (left + right)).name :=
  denote_add Cast.CoordinateTaylor.ofCoordinate Cast.ofCoordinate_add generator left right

/-- Negation of original rational pair coordinates retains its operational numerical negation. -/
def denoteRational_neg (generator : CoherentNamed) (value : Pair Rational parameter) :
    NamedEquivalent (CoherentNamed.neg (denoteRational generator value)).name
      (denoteRational generator (-value)).name :=
  denote_neg Cast.CoordinateTaylor.ofCoordinate Cast.ofCoordinate_zero Cast.ofCoordinate_add generator value

/-- Rational pair multiplication agrees with the retained generator's negative-parameter square equation. -/
def denoteRational_mul (generator : CoherentNamed)
    (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate (-parameter)))
    (left right : Pair Rational parameter) :
    NamedEquivalent (CoherentNamed.mul (denoteRational generator left) (denoteRational generator right)).name
      (denoteRational generator (left * right)).name := by
  have retained : PowerIdentity generator 2 (-Cast.CoordinateTaylor.ofCoordinate parameter) := by
    rewrite [← Cast.ofCoordinate_neg parameter]
    exact identity
  exact denote_mul Cast.CoordinateTaylor.ofCoordinate Cast.ofCoordinate_add Cast.ofCoordinate_mul
    Cast.ofCoordinate_sub generator retained left right

end Purelib.Algebra.Quadratic.Pair.Gaussian

end
