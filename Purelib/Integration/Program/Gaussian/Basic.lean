module

import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Progressive finite integration with Gaussian coefficients

This is the period-facing integration kernel.  Every model is still a finite
list of rationally parameterized cells, but its local polynomial coefficients
are Gaussian rationals.  Hence a cell can approximate a genuinely complex
coefficient before multiplication by the complex path displacement.
-/

namespace Purelib.Integration.Program.Gaussian.Basic

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
set_option genInjectivity false in
/-- An original Gaussian polynomial path at each stage with certified geometric allowances and sample comparisons.

The retained error scale bounds each path allowance and every later-versus-earlier sample difference; a separate
nonnegative center bound controls all samples. -/
structure RefinementProgram where
  /-- The original Gaussian polynomial path model at each stage. -/ model : Nat -> Basic.PathModel
  /-- The retained geometric error scale. -/ errorScale : Fraction.Rational
  /-- The retained error scale is nonnegative. -/ errorScale_nonneg : 0 <= errorScale
  /-- Each original path's aggregate allowance lies below the corresponding quarter-radius bound. -/ modelAllowance_le :
    forall index,
    (model index).aggregateAllowance <=
      Geometric.Basic.quarterRadius errorScale index
  /-- Each later sample differs from the original earlier sample by at most its quarter-radius squared allowance. -/
    later_close : forall {earlier later : Nat}, earlier <= later ->
    Basic.Canonical.normSq ((model later).integralSample - (model earlier).integralSample) <=
      Geometric.Basic.quarterRadius errorScale earlier
  /-- The retained common squared-norm bound for path samples. -/ centerBound : Fraction.Rational
  /-- The common sample bound is nonnegative. -/ centerBound_nonneg : 0 <= centerBound
  /-- Every original path sample obeys the retained common bound. -/ sample_bounded : forall index,
    Basic.Canonical.normSq (model index).integralSample <= centerBound

constructive_injectivity RefinementProgram

end Purelib.Integration.Program.Gaussian.Basic

end
