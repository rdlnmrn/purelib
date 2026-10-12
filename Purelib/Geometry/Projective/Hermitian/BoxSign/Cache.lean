module
import Purelib.Geometry.Projective.Hermitian.Basic
public import Purelib.Geometry.Projective.Hermitian.Formula.Box.Override
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Projective.Hermitian.Formula.Box.Stability
import Purelib.Geometry.Rational.Box.Refinement

public section

open Purelib.Geometry

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.Geometry.Projective.Hermitian.Formula.Box

/-!
# Preservation of cached Hermitian form signs

Refining the retained rational box transports each cached form-sign certificate.
Adding a cache entry preserves every form already found in the retained tail.
The certificates follow the original ordered search and cache entries.
-/

namespace Purelib.Geometry.Projective.Hermitian.BoxSign.Cache

/-- Refining a box preserves every cached form sign. -/
theorem findFormOverride_refine_ne_none
    {outer inner : Rational.Box} (overrides : List (Formula.Box.FormOverride outer))
    (refines : inner.Refines outer) (target : Hermitian.HermitianForm)
    (found : Formula.Box.findFormOverride
      overrides target ≠ none) :
    Formula.Box.findFormOverride
      (overrides.map fun override => override.refine refines) target ≠ none := by
  induction overrides with
  | nil => exact (found rfl).elim
  | cons entry remaining inductionHypothesis =>
      rcases entry with ⟨form, stability⟩
      cases stability
      all_goals
        by_cases equal : form = target
        · simp only [Formula.Box.findFormOverride, FormOverride.refine, List.map_cons, dif_pos equal, -eq_self,
            -iff_self]
          intro impossible
          cases impossible
        · have tailFound : Formula.Box.findFormOverride remaining target ≠ none := by
            simpa only [Formula.Box.findFormOverride, dif_neg equal, -eq_self, -iff_self] using found
          simpa only [Formula.Box.findFormOverride, FormOverride.refine, List.map_cons, dif_neg equal, -eq_self,
            -iff_self] using inductionHypothesis tailFound

/-- Adding one cache entry preserves every form already found in the tail. -/
theorem findFormOverride_cons_ne_none
    {current : Rational.Box} (entry : Formula.Box.FormOverride current)
    (overrides : List (Formula.Box.FormOverride current)) (target : Hermitian.HermitianForm)
    (found : Formula.Box.findFormOverride
      overrides target ≠ none) :
    Formula.Box.findFormOverride
      (entry :: overrides) target ≠ none := by
  by_cases equal : entry.form = target
  · rewrite [Formula.Box.findFormOverride, dif_pos equal]
    intro impossible
    cases impossible
  · simpa only [Formula.Box.findFormOverride, dif_neg equal, -eq_self, -iff_self] using found

end Purelib.Geometry.Projective.Hermitian.BoxSign.Cache

end
