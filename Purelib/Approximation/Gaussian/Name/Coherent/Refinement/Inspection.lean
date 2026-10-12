module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
public import Purelib.Approximation.Gaussian.Process.Apart.Based
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Gaussian.Process.Apart

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Requested-precision denominator acquisition

One prescribed source refinement followed by the audited small-or-apart
decision returns either candidate apartness or a persistent squared-norm
upper bound. Smallness is relative to a supplied threshold, not a zero test.
The ordinary canonical retry index is preserved: this is a requested-target
refinement, not a falsely labelled canonical `Progress` transition.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.Refinement

set_option genInjectivity false in
/-- Cached data from exactly one prescribed source refinement. Keeping the source equality separate from the ball
equality avoids recomputing either executable object in downstream tests. -/
structure Inspection (denominator :
  Coherent.CoherentNamed) (start : State denominator)
    (target : Fraction.Rational) (positive : 0 < target) where
  /-- The exact refinement state produced by the prescribed positive request. -/ retained : State denominator
  /-- The retained source equals the original process refinement by the displayed request. -/ source_eq :
    retained.source = denominator.name.process.refine start.source target positive
  /-- The prescribed refinement preserves the ordinary canonical retry index. -/ index_eq : retained.nextIndex =
    start.nextIndex
  /-- The cached enclosure of the retained refined state. -/ ball : Enclosure.Ball
  /-- The cached enclosure equals the original process enclosure at the retained source. -/ ball_eq : ball =
    denominator.name.process.ball retained.source

constructive_injectivity Inspection

namespace Inspection

/-- Perform one prescribed positive refinement and cache its exact source and enclosure.

The ordinary retry index is preserved and candidate provenance composes through the original process refinement. -/
def request {denominator :
  Coherent.CoherentNamed} (start : State denominator)
    (target : Fraction.Rational) (positive : 0 < target) :
      Inspection denominator start target positive :=
  let source := denominator.name.process.refine start.source target positive
  let retained : State denominator :=
    { source := source
      nextIndex := start.nextIndex
      persists := fun possible => start.persists
        (denominator.name.process.refine_persists start.source target positive possible) }
  { retained := retained
    source_eq := rfl
    index_eq := rfl
    ball := denominator.name.process.ball source
    ball_eq := rfl }

end Inspection

namespace Inspection

/-- Every candidate at the inspected refined source was possible at the original search state. -/
theorem possible_at_start
  {denominator : Coherent.CoherentNamed} {start : State denominator}
    {target : Fraction.Rational} {positive : 0 < target}
    (inspection : Inspection denominator start target
      positive)
    {value : Data.Gaussian.Basic.Canonical} (possible : denominator.name.process.Possible
      inspection.retained.source value) :
    denominator.name.process.Possible start.source value := by
  rw [inspection.source_eq] at possible
  exact denominator.name.process.refine_persists start.source target positive possible

/-- The cached inspected enclosure has squared radius strictly below the prescribed target. -/
theorem accurate {denominator :
  Coherent.CoherentNamed} {start : State denominator}
    {target : Fraction.Rational} {positive : 0 < target}
    (inspection : Inspection denominator start target
      positive) :
    inspection.ball.radiusSq < target := by
  rw [inspection.ball_eq, inspection.source_eq]
  exact denominator.name.process.accurate start.source target positive

/-- Transport apartness of the exact cached enclosure to candidate apartness of the process based at its retained
source. -/
def evidence {denominator :
  Coherent.CoherentNamed} {start : State denominator}
    {target : Fraction.Rational} {positive : 0 < target}
    (inspection : Inspection denominator start target
      positive)
    (apart : Ball.Apart inspection.ball) :
    Possible.PossibleApart (Gaussian.Process.Based.based denominator.name.process
      inspection.retained.source) := by
  apply Based.possibleApartOfBall
  rw [← inspection.ball_eq]
  exact apart

end Inspection
end Purelib.Approximation.Gaussian.Name.Coherent.Refinement

end
