module

meta import Purelib.Elab.Deriving.Repr

import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-! Separate arithmetic and normalization charges, with componentwise work operations. -/

namespace Purelib.Computation.Arithmetic.Cost.Basic

/-! ## The finite schoolbook work model -/

set_option genInjectivity false in
/-- Separate counts of arithmetic work and canonical normalization work.

The two natural-number charges are retained independently; addition and finite summation combine each component without
changing the accounting convention. -/
structure Work where
  /-- The charge for arithmetic on the displayed operands. -/ core : Nat
  /-- The separate charge for canonical normalization. -/ normalization : Nat
deriving DecidableEq

constructive_injectivity Purelib.Computation.Arithmetic.Cost.Basic.Work

derive_exposed_repr Purelib.Computation.Arithmetic.Cost.Basic.Work

namespace Work
/-- Zero arithmetic work and zero normalization work. -/
def zero : Work := ⟨0, 0⟩

/-- Add the two work components independently. -/
def add (left right : Work) : Work :=
  ⟨left.core + right.core,
    left.normalization + right.normalization⟩

/-- Zero work has both components zero. -/
instance : Zero Work := ⟨Work.zero⟩
/-- Work addition combines the two components independently. -/
instance : Add Work := ⟨Work.add⟩

/-- The arithmetic component of zero work is zero. -/
@[simp] theorem zero_core : (0 : Work).core = 0 := rfl
/-- The normalization component of zero work is zero. -/
@[simp] theorem zero_normalization : (0 : Work).normalization = 0
  := rfl
/-- Adding work adds its arithmetic components. -/
@[simp] theorem add_core (left right : Work) :
    (left + right).core = left.core + right.core := rfl
/-- Adding work adds its normalization components. -/
@[simp] theorem add_normalization (left right : Work) :
    (left + right).normalization =
      left.normalization + right.normalization := rfl

/-- Sum a finite list of work records componentwise. -/
def sum : List Work → Work
  | [] => 0
  | work :: remaining => work + Purelib.Computation.Arithmetic.Cost.Basic.Work.sum remaining

/-- The work sum of an empty list is zero. -/
@[simp] theorem sum_nil : Work.sum [] = 0 := rfl
/-- A work sum splits into its head charge and remaining sum. -/
@[simp] theorem sum_cons (work : Work) (remaining : List Work) :
    Work.sum (work :: remaining) = work + Work.sum remaining := rfl

/-- Add the arithmetic and normalization charges. -/
def total (work : Work) : Nat := work.core + work.normalization

end Work
end Purelib.Computation.Arithmetic.Cost.Basic

end
