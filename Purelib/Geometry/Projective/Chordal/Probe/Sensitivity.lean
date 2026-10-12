module
public import Purelib.Data.Function.Rat.Algebra
import Purelib.Data.Rat.Distance.Power
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian

import Purelib.CCL.Measure.Basic
import Purelib.Data.Rat.Distance.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Function

open Purelib.Data.Rat

open Purelib.Data.Rat.Distance

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line.Basic

open Purelib.Geometry.Projective.Line.Gaussian

section
/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

@[expose] public section

namespace Purelib.Geometry.Projective.Chordal.Probe

/-- A sensitivity certificate is preserved exactly by negating the probe. -/
theorem negProbe_sensitive
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    ∀ left right,
      Distance.rationalSeparation
          (Rat.negProbe probe left) (Rat.negProbe probe right) ≤
        factor * Chordal.Basic.chordalSq left right := by
  intro left right
  rw [Rat.rationalSeparation_negProbe]
  exact sensitive left right
end Purelib.Geometry.Projective.Chordal.Probe

end

section
@[expose] public section

/-!
# Root-free L2 stability of finite CCL prefix probes

Direct Lipschitz control by `chordalSq` is stronger than is natural for many
nonconstant projective observables.  This module instead accepts the
square-root-free estimate

`rationalSeparation (probe x) (probe y) ^ 2 ≤ factor * chordalSq x y`.

CCL cylinder contraction then controls exact finite powered-L2 distances.
Finite Cauchy--Schwarz transfers that control to squared expectation error,
and a request at the square of a supplied rational tolerance recovers an
ordinary strict expectation-separation theorem.  No square root is selected.
-/

namespace Purelib.Geometry.Projective.Chordal.Probe

/-- A rational probe whose squared output separation is controlled by squared chordal separation. -/
def SquaredProbeSensitive (probe : Line.GaussianLine
  → Fraction.Rational)
    (factor : Fraction.Rational) : Prop :=
  ∀ left right,
    Proj.HasNonzeroCoordinate left →
    Proj.HasNonzeroCoordinate right →
    Distance.rationalSeparation (probe left) (probe right) ^ 2 ≤
      factor * Chordal.Basic.chordalSq left right

/-- Squared-sensitive probes are invariant under an explicitly supplied projective equivalence between valid homogeneous
representatives. -/
theorem squaredSensitive_probe_eq_of_projectiveEquivalent
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (sensitive : SquaredProbeSensitive probe factor)
    {left right : Line.GaussianLine}
    (leftValid : Proj.HasNonzeroCoordinate left)
    (rightValid : Proj.HasNonzeroCoordinate right)
    (equivalent : left.Equivalent right) :
    probe left = probe right := by
  have squareNonpositive :
      Distance.rationalSeparation
          (probe left) (probe right) ^ 2 ≤ 0 := by
    calc
      Distance.rationalSeparation
          (probe left) (probe right) ^ 2 ≤
          factor * Chordal.Basic.chordalSq left right :=
        sensitive left right leftValid rightValid
      _ = 0 := by
        rw [Chordal.Basic.chordalSq_eq_zero_of_equivalent equivalent]
        ring1
  have squareZero :
      Distance.rationalSeparation
          (probe left) (probe right) ^ 2 = 0 :=
    le_antisymm squareNonpositive
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have differenceSquareZero : (probe left - probe right) ^ 2 = 0 := by
    rw [← NaturalLp.rationalSeparation_sq]
    exact squareZero
  have differenceZero : probe left - probe right = 0 :=
    (Fraction.Order.Arithmetic.sq_eq_zero_direct _).mp differenceSquareZero
  calc
    probe left = (probe left - probe right) + probe right := by ring1
    _ = 0 + probe right := by rw [differenceZero]
    _ = probe right := by ring1

end Purelib.Geometry.Projective.Chordal.Probe

end

section
section
@[expose] public section

/-!
# Finite measure certificates emitted by the executable CCL encoder

This module is the concrete bridge from `Purelib.CCL.Encoding.Encoder.encodeBlocks` to the
projectively rescaled prefix-measure facade.  It packages each finite encoder
result as an inhabited rational enclosure and lifts a finite input table to a
finite expectation enclosure.

The reconstructed affine input is used only through the encoder's explicit
finite projective-equivalence proof.  No quotient representative is chosen.
-/

namespace Purelib.Geometry.Projective.Chordal.Probe

/-- Any chordal-sensitive rational probe takes the same value on two explicitly equivalent homogeneous representatives.
-/
theorem probe_eq_of_projectiveEquivalent
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    {left right : Line.GaussianLine} (equivalent : left.Equivalent right) :
    probe left = probe right := by
  have separationNonpositive :
      Distance.rationalSeparation
          (probe left) (probe right) ≤ 0 := by
    calc
      Distance.rationalSeparation
          (probe left) (probe right) ≤
          factor * Chordal.Basic.chordalSq left right :=
        sensitive left right
      _ = 0 := by
        rw [Chordal.Basic.chordalSq_eq_zero_of_equivalent equivalent]
        ring1
  apply (Distance.rationalSeparation_eq_zero_iff (probe left) (probe right)).mp
  exact Fraction.Order.Basic.Compatibility.le_antisymm _ _
    separationNonpositive (Distance.rationalSeparation_nonneg _ _)
end Purelib.Geometry.Projective.Chordal.Probe

end

end
