module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Gaussian.Evaluation.Norm.Weighted
import Purelib.Tactic.Ring

/-! Zero coefficient lists have zero weighted quadrance majorant. -/

namespace Purelib.Polynomial.Dense.Gaussian.Majorant

open Purelib.Data.Gaussian

open Purelib.Polynomial.Dense.Gaussian.Evaluation.Norm in
/-- Any finite replicated list of zero coefficients has zero weighted quadrance sum.

The original finite count and exponent retain the same weighted scan. Each
zero coefficient contributes zero before the unchanged replicated tail. -/
public theorem weightedNormSum_replicate_zero
    (count exponent : Nat) :
    Purelib.Polynomial.Dense.Gaussian.Evaluation.Norm.Weighted.weightedNormSum
      (List.replicate count (0 : Purelib.Data.Gaussian.Basic.Canonical)) exponent = 0 := open Purelib.Data in by
  induction count generalizing exponent with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, Weighted.weightedNormSum,
        Gaussian.Norm.Basic.normSq_zero, inductionHypothesis]
      ring1

end Purelib.Polynomial.Dense.Gaussian.Majorant
