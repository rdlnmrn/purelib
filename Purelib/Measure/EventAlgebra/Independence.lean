module
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Independence.Basic
public import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Product.Independence
public import Purelib.Measure.EventAlgebra.Basic

section
@[expose] public section

/-!
# Independence of finite rational events

Independence is an exact rational multiplication identity between three
finite event evaluations.  Event families remain displayed lists.
-/

namespace Purelib.Measure

/-- Require independence for every pair of coded events from the two exact retained event algebras. -/
def Distribution.IndependentEventAlgebras {α : Type}
    (distribution : Distribution α)
    (left right : EventAlgebra α) : Prop :=
  ∀ leftCode rightCode,
    distribution.IndependentEvents
      (left.evaluate leftCode) (right.evaluate rightCode)

/-- The two coordinate pullbacks of event algebras are independent under the exact product law. -/
theorem Distribution.product_independentEventAlgebras
    {α β : Type} (left : Distribution α) (right : Distribution β)
    (leftAlgebra : EventAlgebra α)
    (rightAlgebra : EventAlgebra β) :
    (left.product right).IndependentEventAlgebras
      (leftAlgebra.comap fun pair : α × β => pair.1)
      (rightAlgebra.comap fun pair : α × β => pair.2) := by
  intro leftCode rightCode
  exact left.product_independentEvents_coordinates right
    (leftAlgebra.evaluate leftCode) (rightAlgebra.evaluate rightCode)

end Purelib.Measure

end
