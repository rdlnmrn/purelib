module

import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Representation.Basic
import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation

section
@[expose] public section

/-!
# Certified finite translations between refinement protocols

This module separates two operations which cannot constructively be conflated.
A direct observation map converts only the information already present in one
finite observation.  A finite realizer may first refine its source in response
to a positive rational request and records the finite work performed.

Candidate readings are Gaussian rationals.  Relations between readings remain
explicit because an affine enclosure, a projective CCL tail, and a redundant
digit cell need not use identical internal coordinates.
-/

namespace Purelib.Approximation.Gaussian.Translation

set_option genInjectivity false in
/-- A finite family of target observations used when a boundary prevents one target observation from covering every
source reading. -/
structure Cover
    (source target : Representation)
    (observation : source.Observation) where
  /-- The retained finite family of target observations. -/ observations : List target.Observation
  /-- The target-observation family is nonempty. -/ nonempty : observations ≠ []
  /-- Every reading admitted by the original source observation is admitted by one retained target observation. -/
    covers : ∀ {value : Data.Gaussian.Basic.Canonical}, source.Possible observation value →
    ∃ targetObservation,
      targetObservation ∈ observations ∧
        target.Possible targetObservation value

constructive_injectivity Cover

namespace Cover.mk

end Cover.mk

end Purelib.Approximation.Gaussian.Translation

end
