module

import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.State
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian.Name.Coherent.State

section
section
@[expose] public section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.State.Exact.ExplicitLegendreFrame

/-- A terminating coefficient channel read at its unique exact state. -/
def exactCoefficientState (value :
  Canonical) : ExplicitLegendreFrame.CoefficientState where
  channel := Coherence.exact value
  state := ()
end Purelib.Approximation.Gaussian.Name.Coherent.State.Exact.ExplicitLegendreFrame

end

end

section
section
@[expose] public section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.State.Exact.ExplicitLegendreFrame

/-- The retained exact coefficient state has zero coherence allowance. -/
@[simp] theorem
  exactCoefficientState_allowance
  (value : Canonical) :
    (exactCoefficientState value).allowance = 0
      := rfl
end Purelib.Approximation.Gaussian.Name.Coherent.State.Exact.ExplicitLegendreFrame

end

end

section
section
@[expose] public section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.State.Exact.ExplicitLegendreFrame

/-- The witness read from an exact coefficient state is the displayed Gaussian rational. -/
@[simp] theorem
  exactCoefficientState_value
  (value : Canonical) :
    (exactCoefficientState value).value = value
      := rfl
end Purelib.Approximation.Gaussian.Name.Coherent.State.Exact.ExplicitLegendreFrame

end

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

namespace Purelib.Approximation.Gaussian.Name.Coherent.State.Exact
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-! ## Exact finite coefficient frames -/

/-- A terminating coefficient channel read at its unique exact state. -/
def exactCoefficientState (value :
  Canonical) : CoefficientState where
  channel := Coherence.exact value
  state := ()
end Purelib.Approximation.Gaussian.Name.Coherent.State.Exact

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

namespace Purelib.Approximation.Gaussian.Name.Coherent.State.Exact
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The retained exact coefficient state has zero coherence allowance. -/
@[simp] theorem exactCoefficientState_allowance (value :
  Canonical) :
    (exactCoefficientState value).allowance = 0 := rfl
end Purelib.Approximation.Gaussian.Name.Coherent.State.Exact

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

namespace Purelib.Approximation.Gaussian.Name.Coherent.State.Exact
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The witness read from an exact coefficient state is the displayed Gaussian rational. -/
@[simp] theorem exactCoefficientState_value (value :
  Canonical) :
    (exactCoefficientState value).value = value := rfl
end Purelib.Approximation.Gaussian.Name.Coherent.State.Exact

end
