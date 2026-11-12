module

import Purelib.Polynomial.Quadratic.Split
import Purelib.Data.Gaussian.Field

/-! # Original-root readbacks for centered split quadratic coordinates -/

namespace TestPurelib.Polynomial.QuadraticSplit

open Purelib.Algebra.Field
open Purelib.Polynomial.Quadratic
open Purelib.Data.Gaussian.Basic (Canonical)

/-- Both original roots and their product are recovered when the retained two is nonzero. -/
example {K : Type*} [ExplicitField K] (first last point : K) (twoNonzero : (2 : K) ≠ 0) :
    Split.center first last - Split.halfGap first last = first ∧
      Split.center first last + Split.halfGap first last = last ∧
      (point - first) * (point - last) = (point - Split.center first last) ^ 2 - Split.halfGap first last ^ 2 :=
  ⟨Split.center_sub_halfGap first last twoNonzero, Split.center_add_halfGap first last twoNonzero,
    Split.product_eq first last point twoNonzero⟩

/-- Coincident roots retain the exact centered-square identity without a distinctness assumption. -/
example (root point : Canonical) :
    (point - root) * (point - root) = (point - Split.center root root) ^ 2 - Split.halfGap root root ^ 2 :=
  Split.product_eq root root point (by decide +kernel)

/-- A separated ordered Gaussian pair has a retained nonzero half-gap. -/
example {first last : Canonical} (different : first ≠ last) : Split.halfGap first last ≠ 0 :=
  Split.halfGap_ne_zero (by decide +kernel) different

end TestPurelib.Polynomial.QuadraticSplit
