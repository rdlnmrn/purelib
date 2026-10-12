module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Division.Partial.Equivalence
import Purelib.Approximation.Gaussian.Division.Partial.Ready
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Small
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.SmallOrApart
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Init.Core
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
import Purelib.Approximation.Rational.Request.Sixth
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

section

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division.Partial

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

namespace Purelib.Approximation.Gaussian

set_option genInjectivity false in
/-- Ordinary cached productive quotient, constructed only from positive evidence at the exact retained state. -/
structure Division.Partial.Bounded.Quotient (numerator denominator : Coherent.CoherentNamed) (state :
    Name.Coherent.Refinement.State
  denominator) where
  /-- The cached ordinary coherent quotient. -/ output : Coherent.CoherentNamed
  /-- The readiness certificate linking the cached output to these inputs and the exact retained denominator state. -/
    valid : Division.Partial.Ready numerator denominator state output

constructive_injectivity Division.Partial.Bounded.Quotient

/-- Construct and retain the ordinary coherent quotient from apartness evidence at the exact denominator state. -/
def Division.Partial.Bounded.quotient {denominator : Coherent.CoherentNamed} (numerator : Coherent.CoherentNamed)
    (state : Name.Coherent.Refinement.State denominator)
    (evidence : Possible.PossibleApart (Gaussian.Process.Based.based denominator.name.process state.source)) :
    Approximation.Gaussian.Division.Partial.Bounded.Quotient numerator denominator state :=
  { output := Ready.readyName numerator denominator state evidence
    valid := { evidence := evidence, output_eq := rfl } }

/-- The cached bounded-division quotient is operationally equivalent to any other ready quotient of the same original
inputs. -/
def Division.Partial.Bounded.Quotient.respects {numerator denominator : Coherent.CoherentNamed} {state other :
  Name.Coherent.Refinement.State denominator}
    (result : Approximation.Gaussian.Division.Partial.Bounded.Quotient numerator denominator state) {output :
      Coherent.CoherentNamed}
    (ready : Division.Partial.Ready numerator denominator other output) :
    Gaussian.Equivalence.NamedEquivalent result.output.name output.name :=
  Equivalence.ready_respects result.valid ready

/-- Successful reports construct the ordinary quotient; small reports retain their mathematical upper bound instead of
manufacturing a division. -/
def Name.Coherent.Refinement.SmallOrApart.Report.divide {denominator : Coherent.CoherentNamed} {start :
    Name.Coherent.Refinement.State
  denominator}
    {threshold : Fraction.Rational} {positive : 0 < threshold}
    (report : SmallOrApart.Report denominator start threshold positive) (numerator : Coherent.CoherentNamed) :
    Sum (Approximation.Gaussian.Division.Partial.Bounded.Quotient numerator denominator report.inspection.retained)
      (Name.Coherent.Refinement.Small denominator report.inspection.retained threshold) :=
  match report.outcome with
  | .inl evidence => .inl (Approximation.Gaussian.Division.Partial.Bounded.quotient numerator report.inspection.retained
    evidence)
  | .inr small => .inr small

end Purelib.Approximation.Gaussian

end

end
