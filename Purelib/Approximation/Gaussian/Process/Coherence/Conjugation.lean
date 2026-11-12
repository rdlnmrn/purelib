module

public import Purelib.Approximation.Gaussian.Process.Conjugation
public import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic

/-! # Coherence of conjugated original processes -/

public section

namespace Purelib.Approximation.Gaussian.Process.Coherence.Basic.Coherent

open Purelib.Data.Gaussian

/-- Preserve the original coherence allowances and requests under Gaussian conjugation. -/
@[expose] def conj {process : Process} (coherent : Coherent process) : Coherent process.conj where
  allowance := coherent.allowance
  allowance_nonneg := coherent.allowance_nonneg
  ball_radius_le := coherent.ball_radius_le
  possible_close := by
    rintro leftState rightState leftValue rightValue
      ⟨leftSource, leftPossible, rfl⟩ ⟨rightSource, rightPossible, rfl⟩
    rw [Basic.conj_eq_canonical leftSource, Basic.conj_eq_canonical rightSource,
      ← Basic.Canonical.conj_sub, ← Basic.conj_eq_canonical, Norm.Basic.normSq_conj]
    exact coherent.possible_close leftPossible rightPossible
  accuracyRequest := coherent.accuracyRequest
  accuracyRequest_pos := coherent.accuracyRequest_pos
  refine_accurate := coherent.refine_accurate

end Purelib.Approximation.Gaussian.Process.Coherence.Basic.Coherent

end
