module
public import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.Observation.Basic
public import Purelib.Approximation.Observation.Interval
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Block.Basic
public import Purelib.Data.CCL.Encoding.Cylinder
public import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.CCL.Encoding.Cylinder.Projective
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
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

open Purelib.Data.CCL.Encoding.Cylinder

open Purelib.Data.CCL.Encoding.Cylinder.Projective

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line.Basic

section
@[expose] public section

/-!
# Finite measure bounds for projectively rescaled CCL prefixes

The integral CCL encoder retains arbitrary nonzero homogeneous rescalings at
intermediate decoding stages.  Its certificates therefore use
`ProjectiveRealizes`, rather than the canonical-tail `Realizes` relation used
by the original prefix profile.  This module gives those exact encoder-facing
certificates the same finite observation and rational-enclosure interface.

No projective normalization, representative choice, completed point, or
infinite continuation is introduced.
-/

section

namespace Purelib.Approximation.CCL.Prefix

/-- An inhabited completed-prefix cylinder whose realization traces retain the encoder's exact homogeneous rescalings.
-/
def completedProjectivePrefixObservation
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Projective.ProjectiveRealizes blocks witness) :
    Approximation.Observation Line.GaussianLine Chordal.Basic.chordalSq where
  Possible point :=
    Nonempty (Projective.ProjectiveRealizes blocks point)
  witness := witness
  witness_possible := ⟨witnessRealizes⟩
  spread := Cylinder.cylinderSpread blocks
  spread_nonnegative := Cylinder.cylinderSpread_nonneg blocks
  pairwise := by
    intro left right leftPossible rightPossible
    rcases leftPossible with ⟨leftRealizes⟩
    rcases rightPossible with ⟨rightRealizes⟩
    exact ProjectiveRealizes.chordalSq_le_half_pow
      leftRealizes rightRealizes

/-- Appending explicitly supplied projective blocks refines the admitted finite predicate. -/
theorem completedProjectivePrefixObservation_append_refines
    (stem suffix : List Block) (witness : Line.GaussianLine)
    (witnessRealizes :
      Projective.ProjectiveRealizes (stem ++ suffix) witness) :
    Observation.Refines
      (completedProjectivePrefixObservation
        (stem ++ suffix) witness witnessRealizes)
      (completedProjectivePrefixObservation stem witness
        (Cylinder.projectiveRealizesPrefix witnessRealizes)) := by
  constructor
  rintro point ⟨pointRealizes⟩
  exact ⟨Cylinder.projectiveRealizesPrefix pointRealizes⟩

/-- Transport an encoder-facing projective prefix observation through a supplied rational sensitivity estimate. -/
def completedProjectivePrefixProbeObservation
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Projective.ProjectiveRealizes blocks witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Approximation.Observation Fraction.Rational
      Distance.rationalSeparation :=
  (completedProjectivePrefixObservation blocks witness witnessRealizes).map
    probe factor factorNonnegative sensitive

/-- Rational probe enclosure obtained directly from a projectively rescaled finite encoder certificate. -/
def completedProjectivePrefixProbeBound
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Projective.ProjectiveRealizes blocks witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Rat.Interval :=
  (completedProjectivePrefixProbeObservation blocks witness witnessRealizes
    probe factor factorNonnegative sensitive).rationalBound

/-- Every explicitly supplied projective realization evaluates inside the encoder-facing rational probe enclosure. -/
theorem completedProjectivePrefixProbeBound_contains
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Projective.ProjectiveRealizes blocks witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    {point : Line.GaussianLine}
    (pointRealizes : Projective.ProjectiveRealizes blocks point) :
    (completedProjectivePrefixProbeBound blocks witness witnessRealizes
      probe factor factorNonnegative sensitive).Contains (probe point) := by
  apply Observation.rationalBound_contains
  exact ⟨point, ⟨pointRealizes⟩, rfl⟩

/-- The projective-prefix probe enclosure has the same explicit rational width as its canonical-tail counterpart. -/
theorem completedProjectivePrefixProbeBound_width
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Projective.ProjectiveRealizes blocks witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    (completedProjectivePrefixProbeBound blocks witness witnessRealizes
      probe factor factorNonnegative sensitive).width =
        2 * (factor * Cylinder.cylinderSpread blocks) := by
  rw [completedProjectivePrefixProbeBound,
    Observation.rationalBound_width]
  rfl

/-- Extending an encoder-facing completed prefix gives a nested probe enclosure when the same projective witness is
retained. -/
theorem completedProjectivePrefixProbeBound_append_refines
    (stem suffix : List Block) (witness : Line.GaussianLine)
    (witnessRealizes :
      Projective.ProjectiveRealizes (stem ++ suffix) witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Interval.Refines
      (completedProjectivePrefixProbeBound (stem ++ suffix) witness
        witnessRealizes probe factor factorNonnegative sensitive)
      (completedProjectivePrefixProbeBound stem witness
        (Cylinder.projectiveRealizesPrefix witnessRealizes)
        probe factor factorNonnegative sensitive) := by
  have spreadLe :
      factor * Cylinder.cylinderSpread (stem ++ suffix) ≤
        factor * Cylinder.cylinderSpread stem :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Cylinder.cylinderSpread_le_of_append stem suffix) factorNonnegative
  constructor
  · exact Fraction.Order.Arithmetic.sub_le_sub_left_direct spreadLe (probe witness)
  · exact Fraction.Order.Arithmetic.add_le_add_direct le_rfl spreadLe

/-- A finite positive rational request can be discharged directly against the number of completed projective blocks
emitted by the encoder. -/
theorem completedProjectivePrefixProbeBound_width_lt_requested
    {blocks : List Block} (witness : Line.GaussianLine)
    (witnessRealizes : Projective.ProjectiveRealizes blocks witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (enough : Budget.requiredProbeBlockCount target factor ≤ blocks.length) :
    (completedProjectivePrefixProbeBound blocks witness witnessRealizes
      probe factor factorPositive.le sensitive).width < target := by
  have scalePositive : (0 : Fraction.Rational) < 2 * factor :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) factorPositive
  have spreadTargetPositive :
      (0 : Fraction.Rational) < target / (2 * factor) :=
    Fraction.Order.Field.div_pos_direct targetPositive scalePositive
  have spreadSmall : Cylinder.cylinderSpread blocks < target / (2 * factor) :=
    Cylinder.cylinderSpread_lt_of_requiredBlockCount_le spreadTargetPositive enough
  have scaled :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      scalePositive spreadSmall
  rw [completedProjectivePrefixProbeBound_width]
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

section

namespace Purelib.Data.CCL.Encoding.Cylinder.CompletedProjectivePrefixCertificate

/-- The rational probe enclosure supplied by one projective certificate. -/
def probeBound (certificate :
  Cylinder.CompletedProjectivePrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Rat.Interval :=
  Purelib.Approximation.CCL.Prefix.completedProjectivePrefixProbeBound certificate.blocks certificate.witness
    certificate.witnessRealizes probe factor factorNonnegative sensitive

end Purelib.Data.CCL.Encoding.Cylinder.CompletedProjectivePrefixCertificate

end
end

end
