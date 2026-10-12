module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Power.Gaussian
public import Purelib.Polynomial.Power.Gaussian.Squarefree
import Purelib.RootIsolation.FTA.Squarefree.Basic
public import Purelib.RootIsolation.FTA.Squarefree.Build
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.Data.Gaussian.Field

open Purelib.Data

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

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

namespace Purelib.RootIsolation.Power.Isolation

open Purelib.Data.Gaussian

/-! ## Exact higher-degree chamber frames -/

/-- The complete Paper-I finite isolation input at one nonzero parameter. -/
def isolationInput
    {parameter : Gaussian.Basic.Canonical} (parameterNonzero : parameter ≠ 0)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    RootIsolation.FTA.Squarefree.Input (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree) where
  squarefree := Power.Gaussian.Squarefree.squarefree parameterNonzero degree
  degreeAtLeastTwo := by
    rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]
    exact degreeAtLeastTwo
end Purelib.RootIsolation.Power.Isolation

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

namespace Purelib.RootIsolation.Power.Isolation

open Purelib.Data.Gaussian

/-- The independently computed degree-many box result at one exact rational
parameter. -/
def isolationResult
    {parameter : Gaussian.Basic.Canonical} (parameterNonzero : parameter ≠ 0)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    FTA.Squarefree.AdapterResult (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree) :=
  FTA.Squarefree.Build.Box.prove
    (isolationInput parameterNonzero degree degreeAtLeastTwo)
end Purelib.RootIsolation.Power.Isolation

end
