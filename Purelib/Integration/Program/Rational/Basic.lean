module

import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Integration.Polynomial.Rational.Path.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Integration.Polynomial.Rational.Path.Allowance
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# General certified integration by finite path refinements

An integrand is supplied operationally: at each natural refinement it returns
one finite path of rational polynomial cell models and finite rational sample
certificates.  The integration program sums the exact polynomial cell
integrals.  A rational geometric modulus and a finite later-refinement
certificate turn those displayed sums into an ordinary productive CCL name.

There is no measure, completed partition, function-as-an-infinite-set, or
infinitesimal.  The only universal refinements are natural-number calls to the
supplied finite program.
-/

namespace Purelib.Integration.Program.Rational.Basic

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Rational.Path in
set_option genInjectivity false in
/-- A retained rational-polynomial path sequence with geometric allowance and sample-closeness bounds.

Each original stage model keeps its exact Gaussian integral sample; nonnegative error and center scales certify
refinement and uniform sample magnitude. -/
structure RefinementProgram where
  /-- The retained original rational-polynomial path model at each stage. -/ model : Nat → Basic.PathModel
  /-- The retained geometric error scale. -/ errorScale : Fraction.Rational
  /-- The retained error scale is nonnegative. -/ errorScale_nonneg : 0 ≤ errorScale
  /-- Each original model allowance obeys the retained stagewise geometric bound. -/ modelAllowance_le : ∀ index,
    (model index).aggregateAllowance ≤
      Geometric.Basic.quarterRadius errorScale index
  /-- Original later and earlier model samples are close at the earlier stage's geometric scale. -/ later_close : ∀
    {earlier later : Nat}, earlier ≤ later →
    Basic.Canonical.normSq ((model later).integralSample - (model earlier).integralSample) ≤
      Geometric.Basic.quarterRadius errorScale earlier
  /-- The retained uniform sample squared-norm bound. -/ centerBound : Fraction.Rational
  /-- The retained center bound is nonnegative. -/ centerBound_nonneg : 0 ≤ centerBound
  /-- Every original model sample satisfies the retained center bound. -/ sample_bounded : ∀ index,
    Basic.Canonical.normSq (model index).integralSample ≤ centerBound

constructive_injectivity RefinementProgram

end Purelib.Integration.Program.Rational.Basic

end
