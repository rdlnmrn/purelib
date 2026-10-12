module

import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Integral
public import Purelib.Measure.EventAlgebra.Content
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Measure.EventAlgebra.Simple.Basic

section
@[expose] public section

/-!
# Atomic representation of finite event-algebra contents

Finite content is already arithmetic data: a displayed list of nonnegative
rational weights.  Relative to a finitely presented event algebra, pushing
that table to complete truth signatures and consolidating equal signatures
produces the unique displayed algebra atoms relevant to every coded event and
simple observable.

No abstract measure is postulated and no carrier powerset is enumerated.
-/

namespace Purelib.Measure

namespace EventAlgebra

/-- The exact simple observable integrates identically through the consolidated algebra atom content and its retained
signature evaluator. -/
theorem simpleObservable_integral_eq_atomContent_integral {α : Type}
    (algebra : EventAlgebra α) (content : Content α)
    (observable : SimpleObservable algebra) :
    content.integral observable.evaluate =
      (algebra.atomContent content).integral observable.signatureValue := by
  calc
    content.integral observable.evaluate =
        content.integral (fun item =>
          observable.signatureValue (algebra.signature item)) := by
      exact content.integral_congr _ _ (fun item =>
        (observable.signatureValue_signature item).symm)
    _ = (algebra.atomContent content).integral observable.signatureValue :=
      algebra.integral_eq_atomContent_integral content
        observable.signatureValue

end EventAlgebra

end Purelib.Measure

end
