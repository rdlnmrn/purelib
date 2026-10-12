module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.List.Membership

open Purelib.Data.Gaussian.Basic
open Purelib.Data.Gaussian.Norm.Basic
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction

/-!
# Finite Gaussian-list quadrance bounds

The original ordered list determines its finite maximum, retained with the
unit base. Direct scalar and membership certificates bound every original
entry and the entire list without changing its fold or coefficient order.
-/

namespace Purelib.Data.Gaussian.List.NormBounds

/-- Every entry in the displayed Gaussian list has squared norm bounded by the same
rational.

The recursive proposition retains one scalar inequality for the head and the
corresponding bound on the original tail; the empty list satisfies it trivially. -/
@[expose] public def CoefficientsNormLe : List Canonical → Rational → Prop
  | [], _ => True
  | coefficient :: remaining, bound =>
      Norm.Basic.normSq coefficient ≤ bound ∧ Purelib.Data.Gaussian.List.NormBounds.CoefficientsNormLe remaining bound

/-- A uniform squared-norm bound on a Gaussian list remains valid after increasing the
rational bound.

Each retained head inequality increases by scalar transitivity.
The original tail satisfies the same larger bound by structural recursion. -/
public theorem CoefficientsNormLe.mono : ∀ {values : List Canonical}
    {small large : Rational}, NormBounds.CoefficientsNormLe values small →
      small ≤ large → NormBounds.CoefficientsNormLe values large
  | [], _small, _large, _bounded, _order => trivial
  | _ :: _remaining, _small, _large, bounded, order =>
      ⟨bounded.1.trans order, Purelib.Data.Gaussian.List.NormBounds.CoefficientsNormLe.mono bounded.2 order⟩

/-- Compute a positive uniform bound by folding the maximum of Gaussian squared norms
with one.

The finite fold retains the input list order and returns at least one, including for
the empty list. -/
@[expose] public def coefficientNormMaximum (coefficients : List Canonical) : Rational :=
  coefficients.foldr (fun coefficient bound => max (Norm.Basic.normSq coefficient) bound) 1

/-- The computed uniform coefficient squared-norm maximum is strictly positive.

The original fold starts at positive one. Each maximum retains a value
at least as large as the same positive tail maximum. -/
public theorem coefficientNormMaximum_pos (coefficients : List Canonical) :
    0 < NormBounds.coefficientNormMaximum coefficients := by
  induction coefficients with
  | nil => exact (by decide)
  | cons coefficient remaining inductionHypothesis =>
      exact inductionHypothesis.trans_le (Fraction.Order.Basic.le_max_right _ _)

/-- Every retained member of the Gaussian list has squared norm at most its computed
maximum.

The retained head has quadrance at most the original two-argument
maximum. Membership in the tail keeps its original recursive bound,
which increases to the same whole-list maximum. -/
public theorem coefficient_norm_le_maximum : ∀ {coefficients : List Canonical}
    {coefficient : Canonical}, coefficient ∈ coefficients →
    Norm.Basic.normSq coefficient ≤ NormBounds.coefficientNormMaximum coefficients
  | [], coefficient, member => by cases member
  | head :: remaining, coefficient, member => by
      rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | tailMember
      · exact Fraction.Order.Basic.le_max_left _ _
      · exact (Purelib.Data.Gaussian.List.NormBounds.coefficient_norm_le_maximum tailMember).trans
          (Fraction.Order.Basic.le_max_right _ _)

/-- The complete Gaussian list satisfies its computed uniform squared-norm bound.

The finite maximum bounds the head and the original tail maximum.
The existing monotonicity certificate raises that tail's uniform bound
to the same retained whole-list maximum. -/
public theorem coefficientsNormLe_maximum (coefficients : List Canonical) :
    NormBounds.CoefficientsNormLe coefficients (NormBounds.coefficientNormMaximum coefficients) := by
  induction coefficients with
  | nil => trivial
  | cons head remaining inductionHypothesis =>
      constructor
      · exact Fraction.Order.Basic.le_max_left _ _
      · exact CoefficientsNormLe.mono inductionHypothesis
          (Fraction.Order.Basic.le_max_right _ _)

end Purelib.Data.Gaussian.List.NormBounds
