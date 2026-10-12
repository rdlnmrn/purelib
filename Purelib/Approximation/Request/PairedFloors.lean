module

import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Approximation

open Purelib.Data.Rat

@[expose] public section

/-!
# Shared finite budgets for cap endpoint comparisons

Retain both root requests and their independent model and reading floors,
together with the coordinate comparison. The types of the two root
preparations stay abstract so both terminal and disk consumers can reuse it.
-/

universe u v

namespace Purelib.Approximation.Request.PairedFloors

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Gaussian.Equivalence (Comparison)

set_option genInjectivity false in
/-- Abstract the retained request types while storing their model and root floors explicitly in the comparison contract.
This keeps elaboration independent of the concrete continuation process's state representation. -/
structure RequestData (coefficientUpper productScale : Fraction.Rational)
    (reciprocalType : Fraction.Rational → Type u) (regularType : Fraction.Rational → Type v)
    (reciprocalIndex reciprocalRootIndex : (target : Fraction.Rational) → reciprocalType target → Nat)
    (regularIndex regularRootIndex : (target : Fraction.Rational) → regularType target → Nat)
    (stream coordinateSamples : Gaussian.Sequence.ApproximationData)
    (target : Fraction.Rational) (floor : Nat) where
  /-- The original comparison target is strictly positive. -/ positive : 0 < target
  /-- The cached coordinate-comparison budget. -/ budget : Fraction.Rational
  /-- The coordinate budget is the target divided by four times the incremented coefficient bound. -/ budget_eq : budget
    = target / (4 * (coefficientUpper + 1))
  /-- The cached common target for both root requests. -/ rootTarget : Fraction.Rational
  /-- The root target divides the coordinate budget by the incremented product scale. -/ rootTarget_eq : rootTarget =
    budget / (productScale + 1)
  /-- The retained reciprocal preparation at the exact common root target. -/ reciprocal : reciprocalType rootTarget
  /-- The retained regular preparation at the exact common root target. -/ regular : regularType rootTarget
  /-- The coordinate comparison retains both root reading floors and the supplied coordinate floor at the cached budget.
  -/ coordinate : Gaussian.Equivalence.Comparison stream coordinateSamples
    (max (reciprocalRootIndex rootTarget reciprocal) (regularRootIndex rootTarget regular)) floor budget
  /-- The cached common model stage for the two preparations. -/ index : Nat
  /-- The common model stage is exactly the maximum of the retained reciprocal and regular model stages. -/ index_eq :
    index = max (reciprocalIndex rootTarget reciprocal) (regularIndex rootTarget regular)

constructive_injectivity RequestData

end Purelib.Approximation.Request.PairedFloors
