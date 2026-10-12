module
public import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.Observation.Basic
public import Purelib.Approximation.Observation.Interval
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Block.Basic
public import Purelib.Data.CCL.Encoding.Cylinder
import Purelib.Data.CCL.Encoding.Cylinder.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.CCL.Encoding (Block)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.CCL

open Purelib.Approximation.Rational

open Purelib.Data

open Purelib.Data.CCL.Encoding

open Purelib.Data.CCL.Encoding.Cylinder.Basic

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line.Basic

section
@[expose] public section

/-!
# Joint finite profile of a completed CCL prefix

A completed-block prefix carries two deliberately separate rational data:

* its fair-bit symbolic cylinder weight, calculated from the raw word; and
* its geometric squared-chordal spread, calculated from block contraction.

Both improve under finite extension, but no theorem identifies them.  A
finite realization certificate also turns the prefix into an inhabited
finite observation, without choosing a point from an eventual intersection.
-/

section

namespace Purelib.Approximation.CCL.Prefix

/-- An inhabited finite completed-prefix cylinder as a neutral observation. The witness and its realization are explicit
finite inputs. -/
def completedPrefixObservation
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Cylinder.Basic.Realizes blocks witness) :
    Approximation.Observation Line.GaussianLine Chordal.Basic.chordalSq where
  Possible point := Nonempty (Cylinder.Basic.Realizes blocks point)
  witness := witness
  witness_possible := ⟨witnessRealizes⟩
  spread := Cylinder.cylinderSpread blocks
  spread_nonnegative := Cylinder.cylinderSpread_nonneg blocks
  pairwise := by
    intro left right leftPossible rightPossible
    rcases leftPossible with ⟨leftRealizes⟩
    rcases rightPossible with ⟨rightRealizes⟩
    exact Realizes.chordalSq_le_half_pow
      leftRealizes rightRealizes

/-- A displayed suffix gives genuine predicate refinement between the two finite observations. -/
theorem completedPrefixObservation_append_refines
    (stem suffix : List Block) (witness : Line.GaussianLine)
    (witnessRealizes :
      Cylinder.Basic.Realizes (stem ++ suffix) witness) :
    Observation.Refines
      (completedPrefixObservation (stem ++ suffix) witness witnessRealizes)
      (completedPrefixObservation stem witness
        (Cylinder.realizesPrefix witnessRealizes)) := by
  constructor
  rintro point ⟨pointRealizes⟩
  exact ⟨Cylinder.realizesPrefix pointRealizes⟩

/-- Transport a finite completed-prefix observation through a supplied rational probe. The sensitivity certificate
explicitly relates probe separation to squared chordal separation on displayed projective points. -/
def completedPrefixProbeObservation
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Cylinder.Basic.Realizes blocks witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Approximation.Observation Fraction.Rational
      Distance.rationalSeparation :=
  (completedPrefixObservation blocks witness witnessRealizes).map
    probe factor factorNonnegative sensitive

/-- A finite CCL prefix therefore gives an explicit rational enclosure for any supplied rational probe satisfying the
displayed sensitivity estimate. No eventual projective point is selected. -/
def completedPrefixProbeBound
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Cylinder.Basic.Realizes blocks witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Rat.Interval :=
  (completedPrefixProbeObservation blocks witness witnessRealizes
    probe factor factorNonnegative sensitive).rationalBound

/-- Every explicitly supplied realization of the finite prefix evaluates inside its rational probe enclosure. -/
theorem completedPrefixProbeBound_contains
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Cylinder.Basic.Realizes blocks witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    {point : Line.GaussianLine} (pointRealizes : Cylinder.Basic.Realizes blocks point) :
    (completedPrefixProbeBound blocks witness witnessRealizes
      probe factor factorNonnegative sensitive).Contains (probe point) := by
  apply Observation.rationalBound_contains
  exact ⟨point, ⟨pointRealizes⟩, rfl⟩

/-- The enclosure width is the explicit twice-sensitivity-times-prefix spread budget. -/
theorem completedPrefixProbeBound_width
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Cylinder.Basic.Realizes blocks witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    (completedPrefixProbeBound blocks witness witnessRealizes
      probe factor factorNonnegative sensitive).width =
        2 * (factor * Cylinder.cylinderSpread blocks) := by
  rw [completedPrefixProbeBound,
    Observation.rationalBound_width]
  rfl

/-- Extending a completed prefix gives a genuinely nested rational probe enclosure when the same displayed realization
is used as centre. -/
theorem completedPrefixProbeBound_append_refines
    (stem suffix : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Cylinder.Basic.Realizes (stem ++ suffix) witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Interval.Refines
      (completedPrefixProbeBound (stem ++ suffix) witness witnessRealizes
        probe factor factorNonnegative sensitive)
      (completedPrefixProbeBound stem witness
        (Cylinder.realizesPrefix witnessRealizes)
        probe factor factorNonnegative sensitive) := by
  have spreadLe :
      factor * Cylinder.cylinderSpread (stem ++ suffix) ≤
        factor * Cylinder.cylinderSpread stem :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Cylinder.cylinderSpread_le_of_append stem suffix) factorNonnegative
  constructor
  · exact Fraction.Order.Arithmetic.sub_le_sub_left_direct spreadLe (probe witness)
  · exact Fraction.Order.Arithmetic.add_le_add_direct le_rfl spreadLe

end Purelib.Approximation.CCL.Prefix

section

namespace Purelib.Data.CCL.Encoding.Cylinder.CompletedPrefixCertificate

/-- The rational probe enclosure supplied by this one finite certificate. -/
def probeBound (certificate :
  Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Rat.Interval :=
  Purelib.Approximation.CCL.Prefix.completedPrefixProbeBound certificate.blocks certificate.witness
    certificate.witnessRealizes probe factor factorNonnegative sensitive

end Purelib.Data.CCL.Encoding.Cylinder.CompletedPrefixCertificate

end

namespace Purelib.Approximation.CCL.Prefix

/-- Meeting the computed finite block count makes the complete rational probe enclosure narrower than the requested
positive rational width. -/
theorem completedPrefixProbeBound_width_lt_requested
    {blocks : List Block} (witness : Line.GaussianLine)
    (witnessRealizes : Cylinder.Basic.Realizes blocks witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (enough : Budget.requiredProbeBlockCount target factor ≤ blocks.length) :
    (completedPrefixProbeBound blocks witness witnessRealizes
      probe factor factorPositive.le sensitive).width < target := by
  have scalePositive : (0 : Fraction.Rational) < 2 * factor :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) factorPositive
  have spreadTargetPositive :
      (0 : Fraction.Rational) < target / (2 * factor) :=
    Fraction.Order.Field.div_pos_direct targetPositive scalePositive
  have spreadSmall :
      Cylinder.cylinderSpread blocks < target / (2 * factor) :=
    Cylinder.cylinderSpread_lt_of_requiredBlockCount_le spreadTargetPositive enough
  have scaled :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      scalePositive spreadSmall
  rw [completedPrefixProbeBound_width]
  calc
    2 * (factor * Cylinder.cylinderSpread blocks) =
        (2 * factor) * Cylinder.cylinderSpread blocks := by ring1
    _ < (2 * factor) * (target / (2 * factor)) := scaled
    _ = target := by
      calc
        (2 * factor) * (target / (2 * factor)) =
            (target / (2 * factor)) * (2 * factor) := by ring1
        _ = target :=
          Fraction.Field.div_mul_cancel_of_ne
            target (2 * factor) scalePositive.ne'

end Purelib.Approximation.CCL.Prefix

end

end
