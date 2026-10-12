module
import Purelib.Data.Rat.Fraction.Basic

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Multiplication
public import Purelib.Data.Rat.Fraction.Order.Basic

section
section

/-!
# Exact local certificates for the prepared cyclic quartic

The first outer cell of the canonical connector from `-1` to `1` runs along
the horizontal line `im z = -1/2`, from `-5/4` to `-1`.  This file records
the nine endpoints of its depth-three dyadic subdivision and caches the exact
values of `z^4 - 1` there as reduced constructive rationals.

Storing the reduced representatives, including their explicit Bezout
certificates, is important for the later prepared-sheet checks: direct box
clearance can inspect these small values instead of repeatedly normalizing the
large rational expression obtained by polynomial evaluation.
-/

section

/-!
# The second prepared cell of the explicit quartic connector

This module restricts the canonical horizontal connector to its second outer
cell and caches its affine quartic coefficients.  Small unit-scaled rational
calculations certify the exact dense-Horner variation, the dyadic preparation
radius, a segment-specific linearization lower bound, and the first retained
eighth-unit transport floor without increasing Lean's elaboration limits.
-/

section

section

/-!
# The dyadic grid of the second prepared quartic connector cell

This module caches the nine Purelib.Data.Gaussian-rational radicands of the second outer
connector cell on its depth-three dyadic mesh.  A common fine unit keeps the
endpoint evaluations and all eight squared displacements constructive and
small enough to elaborate at the ordinary limits.
-/

section

section
@[expose] public section

/-!
# Analytic and grid data for the third prepared quartic connector cell

The third outer horizontal cell retains the terminal box of the second cell.
Its preparation estimate uses one certified leaf of the finite radicand scan,
and its depth-three grid uses reduced rational representatives for the exact
quadratic boundary checks.
-/

namespace Purelib.Data.Rat.Fraction.Order.NatCast

open Purelib.Data.Rat in
/-- A positive natural number has a positive canonical rational cast. -/
theorem natCast_pos_direct (n : Nat) (positive : 0 < n) :
    (0 : Fraction.Rational) < n :=
  Fraction.Cast.Order.natCast_pos_direct positive
end Purelib.Data.Rat.Fraction.Order.NatCast

end

end

section
section
@[expose] public section

/-!
# Exact local certificates for the prepared cyclic quartic

The first outer cell of the canonical connector from `-1` to `1` runs along
the horizontal line `im z = -1/2`, from `-5/4` to `-1`.  This file records
the nine endpoints of its depth-three dyadic subdivision and caches the exact
values of `z^4 - 1` there as reduced constructive rationals.

Storing the reduced representatives, including their explicit Bezout
certificates, is important for the later prepared-sheet checks: direct box
clearance can inspect these small values instead of repeatedly normalizing the
large rational expression obtained by polynomial evaluation.
-/

namespace Purelib.Data.Rat.Fraction.Order.NatCast

open Purelib.Data.Rat in
/-- Every natural-number cast to the canonical rational carrier is nonnegative. -/
public theorem qNatNonnegative (n : Nat) : (0 : Fraction.Rational) ≤ n
  :=
  Fraction.Cast.Order.natCast_le_direct (Nat.zero_le n)

end Purelib.Data.Rat.Fraction.Order.NatCast

end

/-!
# The second prepared cell of the explicit quartic connector

This module restricts the canonical horizontal connector to its second outer
cell and caches its affine quartic coefficients.  Small unit-scaled rational
calculations certify the exact dense-Horner variation, the dyadic preparation
radius, a segment-specific linearization lower bound, and the first retained
eighth-unit transport floor without increasing Lean's elaboration limits.
-/

/-!
# The dyadic grid of the second prepared quartic connector cell

This module caches the nine Purelib.Data.Gaussian-rational radicands of the second outer
connector cell on its depth-three dyadic mesh.  A common fine unit keeps the
endpoint evaluations and all eight squared displacements constructive and
small enough to elaborate at the ordinary limits.
-/

/-!
# Analytic and grid data for the third prepared quartic connector cell

The third outer horizontal cell retains the terminal box of the second cell.
Its preparation estimate uses one certified leaf of the finite radicand scan,
and its depth-three grid uses reduced rational representatives for the exact
quadratic boundary checks.
-/

end

section
section

/-!
# Exact local certificates for the prepared cyclic quartic

The first outer cell of the canonical connector from `-1` to `1` runs along
the horizontal line `im z = -1/2`, from `-5/4` to `-1`.  This file records
the nine endpoints of its depth-three dyadic subdivision and caches the exact
values of `z^4 - 1` there as reduced constructive rationals.

Storing the reduced representatives, including their explicit Bezout
certificates, is important for the later prepared-sheet checks: direct box
clearance can inspect these small values instead of repeatedly normalizing the
large rational expression obtained by polynomial evaluation.
-/

section

/-!
# The second prepared cell of the explicit quartic connector

This module restricts the canonical horizontal connector to its second outer
cell and caches its affine quartic coefficients.  Small unit-scaled rational
calculations certify the exact dense-Horner variation, the dyadic preparation
radius, a segment-specific linearization lower bound, and the first retained
eighth-unit transport floor without increasing Lean's elaboration limits.
-/

section
@[expose] public section

namespace Purelib.Data.Rat.Fraction.Order.NatCast

open Purelib.Data.Rat in
/-- A positive natural number has positive canonical rational cast. -/
private theorem qNatPositiveLate (n : Nat) (positive : 0 < n) :
    (0 : Fraction.Rational) < n :=
  Fraction.Cast.Order.natCast_pos_direct positive
end Purelib.Data.Rat.Fraction.Order.NatCast

end

/-!
# The dyadic grid of the second prepared quartic connector cell

This module caches the nine Purelib.Data.Gaussian-rational radicands of the second outer
connector cell on its depth-three dyadic mesh.  A common fine unit keeps the
endpoint evaluations and all eight squared displacements constructive and
small enough to elaborate at the ordinary limits.
-/

/-!
# Analytic and grid data for the third prepared quartic connector cell

The third outer horizontal cell retains the terminal box of the second cell.
Its preparation estimate uses one certified leaf of the finite radicand scan,
and its depth-three grid uses reduced rational representatives for the exact
quadratic boundary checks.
-/

end

section
section

/-!
# Exact local certificates for the prepared cyclic quartic

The first outer cell of the canonical connector from `-1` to `1` runs along
the horizontal line `im z = -1/2`, from `-5/4` to `-1`.  This file records
the nine endpoints of its depth-three dyadic subdivision and caches the exact
values of `z^4 - 1` there as reduced constructive rationals.

Storing the reduced representatives, including their explicit Bezout
certificates, is important for the later prepared-sheet checks: direct box
clearance can inspect these small values instead of repeatedly normalizing the
large rational expression obtained by polynomial evaluation.
-/

section

/-!
# The second prepared cell of the explicit quartic connector

This module restricts the canonical horizontal connector to its second outer
cell and caches its affine quartic coefficients.  Small unit-scaled rational
calculations certify the exact dense-Horner variation, the dyadic preparation
radius, a segment-specific linearization lower bound, and the first retained
eighth-unit transport floor without increasing Lean's elaboration limits.
-/

section
@[expose] public section

namespace Purelib.Data.Rat.Fraction.Order.NatCast

open Purelib.Data.Rat in
/-- Weak comparison of natural numerators is preserved by rational division by a common positive natural denominator. -/
public theorem lateNatDivLeNatDiv (m n d : Nat) (lessEqual : m ≤ n)
    (positive : 0 < d) : (m : Fraction.Rational) / d ≤ (n : Fraction.Rational) / d := by
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Cast.Order.natCast_le_direct lessEqual)
      (Fraction.Order.Field.inv_pos_direct
        (qNatPositiveLate d positive)).le

end Purelib.Data.Rat.Fraction.Order.NatCast

end

/-!
# The dyadic grid of the second prepared quartic connector cell

This module caches the nine Purelib.Data.Gaussian-rational radicands of the second outer
connector cell on its depth-three dyadic mesh.  A common fine unit keeps the
endpoint evaluations and all eight squared displacements constructive and
small enough to elaborate at the ordinary limits.
-/

/-!
# Analytic and grid data for the third prepared quartic connector cell

The third outer horizontal cell retains the terminal box of the second cell.
Its preparation estimate uses one certified leaf of the finite radicand scan,
and its depth-three grid uses reduced rational representatives for the exact
quadratic boundary checks.
-/

end

section
section

/-!
# Exact local certificates for the prepared cyclic quartic

The first outer cell of the canonical connector from `-1` to `1` runs along
the horizontal line `im z = -1/2`, from `-5/4` to `-1`.  This file records
the nine endpoints of its depth-three dyadic subdivision and caches the exact
values of `z^4 - 1` there as reduced constructive rationals.

Storing the reduced representatives, including their explicit Bezout
certificates, is important for the later prepared-sheet checks: direct box
clearance can inspect these small values instead of repeatedly normalizing the
large rational expression obtained by polynomial evaluation.
-/

section

/-!
# The second prepared cell of the explicit quartic connector

This module restricts the canonical horizontal connector to its second outer
cell and caches its affine quartic coefficients.  Small unit-scaled rational
calculations certify the exact dense-Horner variation, the dyadic preparation
radius, a segment-specific linearization lower bound, and the first retained
eighth-unit transport floor without increasing Lean's elaboration limits.
-/

section

section

/-!
# The dyadic grid of the second prepared quartic connector cell

This module caches the nine Purelib.Data.Gaussian-rational radicands of the second outer
connector cell on its depth-three dyadic mesh.  A common fine unit keeps the
endpoint evaluations and all eight squared displacements constructive and
small enough to elaborate at the ordinary limits.
-/

section
@[expose] public section

namespace Purelib.Data.Rat.Fraction.Order.NatCast

open Purelib.Data.Rat in
/-- A positive natural number has positive canonical rational cast. -/
private theorem qNatPositiveRecenter (n : Nat) (positive : 0 < n) :
    (0 : Fraction.Rational) < n :=
  Fraction.Cast.Order.natCast_pos_direct positive
end Purelib.Data.Rat.Fraction.Order.NatCast

end

/-!
# Analytic and grid data for the third prepared quartic connector cell

The third outer horizontal cell retains the terminal box of the second cell.
Its preparation estimate uses one certified leaf of the finite radicand scan,
and its depth-three grid uses reduced rational representatives for the exact
quadratic boundary checks.
-/

end

section
section

/-!
# Exact local certificates for the prepared cyclic quartic

The first outer cell of the canonical connector from `-1` to `1` runs along
the horizontal line `im z = -1/2`, from `-5/4` to `-1`.  This file records
the nine endpoints of its depth-three dyadic subdivision and caches the exact
values of `z^4 - 1` there as reduced constructive rationals.

Storing the reduced representatives, including their explicit Bezout
certificates, is important for the later prepared-sheet checks: direct box
clearance can inspect these small values instead of repeatedly normalizing the
large rational expression obtained by polynomial evaluation.
-/

section

/-!
# The second prepared cell of the explicit quartic connector

This module restricts the canonical horizontal connector to its second outer
cell and caches its affine quartic coefficients.  Small unit-scaled rational
calculations certify the exact dense-Horner variation, the dyadic preparation
radius, a segment-specific linearization lower bound, and the first retained
eighth-unit transport floor without increasing Lean's elaboration limits.
-/

section

section
@[expose] public section

/-!
# The dyadic grid of the second prepared quartic connector cell

This module caches the nine Purelib.Data.Gaussian-rational radicands of the second outer
connector cell on its depth-three dyadic mesh.  A common fine unit keeps the
endpoint evaluations and all eight squared displacements constructive and
small enough to elaborate at the ordinary limits.
-/

namespace Purelib.Data.Rat.Fraction.Order.NatCast

open Purelib.Data.Rat in
/-- A positive natural number has positive canonical rational cast. -/
private theorem qNatPositiveSecond (n : Nat) (positive : 0 < n) :
    (0 : Fraction.Rational) < n :=
  Fraction.Cast.Order.natCast_pos_direct positive
end Purelib.Data.Rat.Fraction.Order.NatCast

end

/-!
# Analytic and grid data for the third prepared quartic connector cell

The third outer horizontal cell retains the terminal box of the second cell.
Its preparation estimate uses one certified leaf of the finite radicand scan,
and its depth-three grid uses reduced rational representatives for the exact
quadratic boundary checks.
-/

end

section
section
@[expose] public section

/-!
# Exact local certificates for the prepared cyclic quartic

The first outer cell of the canonical connector from `-1` to `1` runs along
the horizontal line `im z = -1/2`, from `-5/4` to `-1`.  This file records
the nine endpoints of its depth-three dyadic subdivision and caches the exact
values of `z^4 - 1` there as reduced constructive rationals.

Storing the reduced representatives, including their explicit Bezout
certificates, is important for the later prepared-sheet checks: direct box
clearance can inspect these small values instead of repeatedly normalizing the
large rational expression obtained by polynomial evaluation.
-/

namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedCertificates

open Purelib.Data.Rat in
/-- A positive natural number has positive canonical rational cast. -/
private theorem qNatPositive (n : Nat) (positive : 0 < n) :
    (0 : Fraction.Rational) < n :=
  Fraction.Cast.Order.natCast_pos_direct positive
end Purelib.Examples.Riemann.ExplicitQuarticPreparedCertificates

end

/-!
# The second prepared cell of the explicit quartic connector

This module restricts the canonical horizontal connector to its second outer
cell and caches its affine quartic coefficients.  Small unit-scaled rational
calculations certify the exact dense-Horner variation, the dyadic preparation
radius, a segment-specific linearization lower bound, and the first retained
eighth-unit transport floor without increasing Lean's elaboration limits.
-/

/-!
# The dyadic grid of the second prepared quartic connector cell

This module caches the nine Purelib.Data.Gaussian-rational radicands of the second outer
connector cell on its depth-three dyadic mesh.  A common fine unit keeps the
endpoint evaluations and all eight squared displacements constructive and
small enough to elaborate at the ordinary limits.
-/

/-!
# Analytic and grid data for the third prepared quartic connector cell

The third outer horizontal cell retains the terminal box of the second cell.
Its preparation estimate uses one certified leaf of the finite radicand scan,
and its depth-three grid uses reduced rational representatives for the exact
quadratic boundary checks.
-/

end

section
section

/-!
# Exact local certificates for the prepared cyclic quartic

The first outer cell of the canonical connector from `-1` to `1` runs along
the horizontal line `im z = -1/2`, from `-5/4` to `-1`.  This file records
the nine endpoints of its depth-three dyadic subdivision and caches the exact
values of `z^4 - 1` there as reduced constructive rationals.

Storing the reduced representatives, including their explicit Bezout
certificates, is important for the later prepared-sheet checks: direct box
clearance can inspect these small values instead of repeatedly normalizing the
large rational expression obtained by polynomial evaluation.
-/

section
@[expose] public section

/-!
# The second prepared cell of the explicit quartic connector

This module restricts the canonical horizontal connector to its second outer
cell and caches its affine quartic coefficients.  Small unit-scaled rational
calculations certify the exact dense-Horner variation, the dyadic preparation
radius, a segment-specific linearization lower bound, and the first retained
eighth-unit transport floor without increasing Lean's elaboration limits.
-/

namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedSecondCell

open Purelib.Data.Rat in
/-- A positive natural number has positive canonical rational cast. -/
private theorem qNatPositive (n : Nat) (positive : 0 < n) :
    (0 : Fraction.Rational) < n :=
  Fraction.Cast.Order.natCast_pos_direct positive
end Purelib.Examples.Riemann.ExplicitQuarticPreparedSecondCell

end

/-!
# The dyadic grid of the second prepared quartic connector cell

This module caches the nine Purelib.Data.Gaussian-rational radicands of the second outer
connector cell on its depth-three dyadic mesh.  A common fine unit keeps the
endpoint evaluations and all eight squared displacements constructive and
small enough to elaborate at the ordinary limits.
-/

/-!
# Analytic and grid data for the third prepared quartic connector cell

The third outer horizontal cell retains the terminal box of the second cell.
Its preparation estimate uses one certified leaf of the finite radicand scan,
and its depth-three grid uses reduced rational representatives for the exact
quadratic boundary checks.
-/

end

section
@[expose] public section

/-!
# Explicit finite branch data for the cyclic quartic

This file supplies four audited rational winding boxes for
`y² = x⁴ - 1`.  Their centres are the exact Gaussian-rational roots
`-1`, `1`, `-i`, and `i`.  Every box has horizontal radius `1/4` and vertical
radius `1/2`; the narrow horizontal direction keeps the four interiors
separated while the lower boundary places the canonical connectors in the
balanced corridor between the horizontal and vertical branch points.
Factorwise boundary clearance and an exact quadrupled winding calculation
turn the boxes into a
degree-complete shrinking branch family.  Thus the period programs below use
the explicit-data theorem path and do not execute the generic global root
isolator while elaborating the example.
-/

namespace Purelib.Data.Rat.Fraction.Order.NatCast

open Purelib.Data.Rat in
/-- A positive natural number has positive canonical rational cast. -/
private theorem firstConnectorCastPositive (n : Nat) (positive : 0 < n) :
    (0 : Fraction.Rational) < n :=
  Fraction.Cast.Order.natCast_pos_direct positive
end Purelib.Data.Rat.Fraction.Order.NatCast

end
