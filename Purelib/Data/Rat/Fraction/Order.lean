module
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Nat.Order

open scoped Purelib.Data.Nat

namespace Purelib.Data.Rat.Fraction.Order

open Purelib.Data.Rat

/-- The sum of two quarters of a rational is half of that rational. -/
public theorem quarter_add_quarter_eq_half (target : Fraction.Rational) :
    target / 4 + target / 4 = target / 2 := by
  apply Fraction.Field.mul_right_cancel_of_ne
    (show (4 : Fraction.Rational) ≠ 0 by decide)
  calc
    (target / 4 + target / 4) * 4 =
        (target / 4) * 4 + (target / 4) * 4 := by rw [add_mul]
    _ = target + target := by
      rw [show target / 4 * 4 = target from
        Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)]
    _ = target * 2 := by ring1
    _ = ((target / 2) * 2) * 2 := by
      rw [show target / 2 * 2 = target from
        Fraction.Field.div_mul_cancel_of_ne target 2 (by decide)]
    _ = (target / 2) * (2 * 2) :=
      Fraction.Field.mul_assoc (target / 2) 2 2
    _ = (target / 2) * 4 := by
      rw [show (2 : Fraction.Rational) * 2 = 4 by decide]

/-- Twice one quarter of a rational is half of that rational. -/
public theorem two_mul_quarter_eq_half (target : Fraction.Rational) :
    2 * (target / 4) = target / 2 := by
  calc
    2 * (target / 4) = target / 4 + target / 4 := by ring1
    _ = target / 2 := quarter_add_quarter_eq_half target

/-- A nonnegative rational is at most twice its sum with any nonnegative rational. -/
public theorem le_twice_sum_of_nonneg
    (left right : Fraction.Rational) (leftNonnegative : 0 ≤ left)
    (rightNonnegative : 0 ≤ right) :
    left ≤ 2 * (left + right) := by
  have sumNonnegative : 0 ≤ left + right :=
    add_nonneg leftNonnegative rightNonnegative
  calc
    left ≤ left + right := le_add_of_nonneg_right rightNonnegative
    _ = 1 * (left + right) :=
      (_root_.one_mul _).symm
    _ ≤ 2 * (left + right) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (by decide) sumNonnegative

/-- Successive division by two fixed positive rational denominators preserves weak comparison. -/
public theorem div_div_le_div_div_of_le
    {left right firstDenominator secondDenominator : Fraction.Rational}
    (order : left ≤ right)
    (firstPositive : 0 < firstDenominator)
    (secondPositive : 0 < secondDenominator) :
    (left / firstDenominator) / secondDenominator ≤
      (right / firstDenominator) / secondDenominator := by
  change (left * firstDenominator⁻¹) * secondDenominator⁻¹ ≤
    (right * firstDenominator⁻¹) * secondDenominator⁻¹
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct order
      (Fraction.Order.Field.inv_pos_direct firstPositive).le)
    (Fraction.Order.Field.inv_pos_direct secondPositive).le

end Purelib.Data.Rat.Fraction.Order

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Data.Rat.Fraction.Order

open Purelib.Data.Rat in
/-- One over 128 is at most one over 32 in the canonical rational order. -/
private theorem one_over_one_twenty_eight_le_one_over_thirty_two :
    (1 / 128 : Fraction.Rational) ≤ 1 / 32 := by
  have denominatorPositive : (0 : Fraction.Rational) < 128 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 128) (by decide)
  apply (Fraction.Order.Field.div_le_iff_pos denominatorPositive).2
  have thirtyTwoNonzero : (32 : Fraction.Rational) ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 32) (by decide)).ne'
  have inverseThirtyTwo : (1 / 32 : Fraction.Rational) * 32 = 1 :=
    Fraction.Field.div_mul_cancel_of_ne 1 32 thirtyTwoNonzero
  calc
    (1 : Fraction.Rational) ≤ 4 := by decide
    _ = 1 * 4 := by ring1
    _ = ((1 / 32 : Fraction.Rational) * 32) * 4 := by rw [inverseThirtyTwo]
    _ = (1 / 32 : Fraction.Rational) * 128 := by ring1
end Purelib.Data.Rat.Fraction.Order

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Data.Rat.Fraction.Order

open Purelib.Data.Rat in
/-- One over 32 is at most one quarter in the canonical rational order. -/
private theorem one_over_thirty_two_le_one_over_four :
    (1 / 32 : Fraction.Rational) ≤ 1 / 4 := by
  have denominatorPositive : (0 : Fraction.Rational) < 32 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 32) (by decide)
  apply (Fraction.Order.Field.div_le_iff_pos denominatorPositive).2
  have fourNonzero : (4 : Fraction.Rational) ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 4) (by decide)).ne'
  have inverseFour : (1 / 4 : Fraction.Rational) * 4 = 1 :=
    Fraction.Field.div_mul_cancel_of_ne 1 4 fourNonzero
  calc
    (1 : Fraction.Rational) ≤ 8 := by decide
    _ = 1 * 8 := by ring1
    _ = ((1 / 4 : Fraction.Rational) * 4) * 8 := by rw [inverseFour]
    _ = (1 / 4 : Fraction.Rational) * 32 := by ring1
end Purelib.Data.Rat.Fraction.Order

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Data.Rat.Fraction.Order

open Purelib.Data.Rat in
/-- Twice the sum of two one-over-32 terms is one eighth. -/
private theorem twice_two_thirty_seconds_eq_eighth :
    2 * ((1 / 32 : Fraction.Rational) + 1 / 32) = 1 / 8 := by
  have eightNonzero : (8 : Fraction.Rational) ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 8) (by decide)).ne'
  have inverseEighth : (8 : Fraction.Rational) * (1 / 8) = 1 := by
    calc
      (8 : Fraction.Rational) * (1 / 8) = (1 / 8) * 8 := by ring1
      _ = 1 := Fraction.Field.div_mul_cancel_of_ne
        1 8 eightNonzero
  have thirtyTwoNonzero : (32 : Fraction.Rational) ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 32) (by decide)).ne'
  have inverseThirtyTwo : (1 / 32 : Fraction.Rational) * 32 = 1 :=
    Fraction.Field.div_mul_cancel_of_ne 1 32 thirtyTwoNonzero
  have thirtySecond : (1 / 32 : Fraction.Rational) =
      2 * (1 / 8 : Fraction.Rational) ^ 2 := by
    apply Fraction.Field.mul_right_cancel_of_ne thirtyTwoNonzero
    calc
      (1 / 32 : Fraction.Rational) * 32 = 1 := inverseThirtyTwo
      _ = (8 * (1 / 8 : Fraction.Rational)) *
          (8 * (1 / 8 : Fraction.Rational)) := by rw [inverseEighth]; ring1
      _ = (2 * (1 / 8 : Fraction.Rational) ^ 2) * 32 := by ring1
  rw [thirtySecond]
  calc
    2 * (2 * (1 / 8 : Fraction.Rational) ^ 2 +
        2 * (1 / 8 : Fraction.Rational) ^ 2) =
      (8 * (1 / 8 : Fraction.Rational)) * (1 / 8 : Fraction.Rational) := by ring1
    _ = 1 * (1 / 8 : Fraction.Rational) := by rw [inverseEighth]
    _ = 1 / 8 := by ring1
end Purelib.Data.Rat.Fraction.Order

end

section
section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

section

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

section

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

section
/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

section

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

section
@[expose] public section

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

namespace Purelib.Approximation.Gaussian.Sequence.Geometric.Channel
section Channel

open Purelib.Data.Rat in
/-- Adding a nonnegative rational gives an upper bound for the left summand. -/
private theorem left_le_sum (left right :
  Fraction.Rational)
    (rightNonnegative : 0 ≤ right) : left ≤ left + right :=
  le_add_of_nonneg_right rightNonnegative
end Channel

end Purelib.Approximation.Gaussian.Sequence.Geometric.Channel

end

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

end

section
section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

section

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

section

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

section
/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

section

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

section
@[expose] public section

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

namespace Purelib.Approximation.Gaussian.Sequence.Geometric.Channel
section Channel

open Purelib.Data.Rat in
/-- Adding a nonnegative left rational gives an upper bound for the right summand. -/
private theorem right_le_sum (left right :
  Fraction.Rational)
    (leftNonnegative : 0 ≤ left) : right ≤ left + right :=
  le_add_of_nonneg_left leftNonnegative
end Channel

end Purelib.Approximation.Gaussian.Sequence.Geometric.Channel

end

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

end

section
section
@[expose] public section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section Purelib.CCL.Measure

end Purelib.CCL.Measure

end

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

end

section
section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

section
@[expose] public section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

section Purelib.CCL.Measure

section PrefixFamilyProcess

end PrefixFamilyProcess

end Purelib.CCL.Measure

end

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

end

section
section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

section
@[expose] public section

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

section Purelib.CCL.Measure

end Purelib.CCL.Measure

end

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

end

section
section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

section

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

section
@[expose] public section

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

section Purelib.CCL.Measure

section PrefixFamilyProcess

end PrefixFamilyProcess

end Purelib.CCL.Measure

end

/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

end

section
section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

section

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

section
@[expose] public section

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

section Purelib.CCL.Measure

section PrefixFamilyProcess

end PrefixFamilyProcess

end Purelib.CCL.Measure

end

/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

end

section
section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

section

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

section
@[expose] public section

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

section Purelib.CCL.Measure

section PrefixFamilyProcess

end PrefixFamilyProcess

end Purelib.CCL.Measure

end

/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

end

section
section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

section

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

section

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

section
/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

section
@[expose] public section

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

section Purelib.CCL.Measure

end Purelib.CCL.Measure

end

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

end

section
section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

section
@[expose] public section

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

section Purelib.CCL.Measure

end Purelib.CCL.Measure

end

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

end

section
section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

section
@[expose] public section

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

section Purelib.CCL.Measure

end Purelib.CCL.Measure

end

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

end

section
section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

section

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

section

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

section
/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

section

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

section

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

section
@[expose] public section

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

section Purelib.CCL.Progressive.QuadraticTrace
section Trace

end Trace

end Purelib.CCL.Progressive.QuadraticTrace

end

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

end

section
section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

section

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

section

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

section
/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

section

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

section

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

section

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

section

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

section

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

section

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

section
@[expose] public section

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

namespace Purelib.Data.Rat.Fraction.Order

open Purelib.Data.Rat in
/-- The sum of two nonnegative rationals is nonnegative. -/
public theorem add_nonnegative
    {left right : Fraction.Rational} (leftNonnegative : 0 ≤ left)
    (rightNonnegative : 0 ≤ right) : 0 ≤ left + right := by
  calc
    0 = 0 + 0 := by ring1
    _ ≤ left + right :=
      Fraction.Order.Arithmetic.add_le_add_direct leftNonnegative
        rightNonnegative

end Purelib.Data.Rat.Fraction.Order

end

end

section
section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

section

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

section

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

section
/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

section

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

section

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

section

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

section

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

section

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

section

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

section
@[expose] public section

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

namespace Purelib.Data.Rat.Fraction.Order

section TriangleSpreadRules

open Purelib.Data.Rat in
/-- A strictly positive rational is nonzero. -/
theorem rational_ne_zero_of_positive {value : Fraction.Rational}
    (positive : 0 < value) : value ≠ 0 := by
  intro valueZero
  apply positive.2
  rw [valueZero]
end TriangleSpreadRules
end Purelib.Data.Rat.Fraction.Order

end

end

section
section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section
@[expose] public section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

namespace Purelib.Data.Rat.Fraction

open Purelib.Data.Rat in
/-- The sum of two halves of a rational is the original rational. -/
public theorem half_add_half (epsilon : Fraction.Rational) :
    epsilon / 2 + epsilon / 2 = epsilon := by
  calc
    epsilon / 2 + epsilon / 2 = (epsilon / 2) * 2 := by ring1
    _ = epsilon :=
      Fraction.Field.div_mul_cancel_of_ne epsilon 2 (by decide)

end Purelib.Data.Rat.Fraction

end

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

end

section
section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section
@[expose] public section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

namespace Purelib.Data.Rat.Fraction

open Purelib.Data.Rat in
/-- Half of a positive rational is positive. -/
public theorem half_positive {epsilon : Fraction.Rational} (positive : 0 < epsilon) :
    0 < epsilon / 2 :=
  Fraction.Order.Field.div_pos_direct positive (by decide)

end Purelib.Data.Rat.Fraction

end

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

end

section
section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

section

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

section

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

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

namespace Purelib.Data.Rat.Fraction

open Purelib.Data.Rat in
/-- For two rationals summing to one, a lower bound on the right complement gives the strict upper bound on the left. -/
theorem left_lt_of_add_eq_one_of_one_sub_lt_right
    (left right level : Fraction.Rational) (sum : left + right = 1)
    (rightLarge : 1 - level < right) : left < level := by
  calc
    left = 1 - right := by
      rw [← sum]
      ring1
    _ < 1 - (1 - level) :=
      Fraction.Order.Arithmetic.sub_lt_sub_left_direct rightLarge 1
    _ = level := by ring1
end Purelib.Data.Rat.Fraction

end

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

end

section
section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

section
@[expose] public section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

namespace Purelib.Data.Rat.Fraction

open Purelib in
open Purelib.Data.Rat in
/-- One quarter of a positive rational is strictly smaller than half of it. -/
public theorem quarter_lt_half {target : Fraction.Rational} (positive : 0 < target) :
    target / 4 < target / 2 := by
  have quarterPositive : (0 : Fraction.Rational) < target / 4 :=
    Fraction.Order.Field.div_pos_direct positive (by decide)
  calc
    target / 4 = target / 4 + 0 := by ring1
    _ < target / 4 + target / 4 :=
      Fraction.Order.Arithmetic.add_lt_add_left_direct quarterPositive _
    _ = target / 2 := Order.quarter_add_quarter_eq_half target

end Purelib.Data.Rat.Fraction

end

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

end

section
section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

section

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

section

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

section
/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

section

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

section

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

section

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

section

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

section
@[expose] public section

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

section Purelib.Measure

section Distribution

end Distribution

end Purelib.Measure

end

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

end

section
section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

section

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

section

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

section
/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

section

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

section

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

section

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

section
@[expose] public section

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

section Purelib.Measure

section PointwiseEnclosureProcess

end PointwiseEnclosureProcess

end Purelib.Measure

end

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

end

section
section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

section

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

section

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

section
/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

section

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

section

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

section

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

section

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

section

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

section
@[expose] public section

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

section Purelib.Riemann.Integration.Positivity

end Purelib.Riemann.Integration.Positivity

end

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

end
