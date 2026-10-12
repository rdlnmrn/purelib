module

public import Purelib.Data.Fin.Bijection.Basic
import Mathlib.Tactic.Linter.Lint

open Purelib.Data.Fin.Bijection

open Purelib.Data.Fin.Bijection.Basic

section
@[expose] public section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

namespace Purelib.Data.Fin.Bijection
section Bijection

/-! ## Finite cycle arithmetic -/

/-- Execute a finite bijection's forward map a supplied number of times.

The zero-step iteration is identity. Each successor applies one forward step after
the preceding iteration; recursion is on the displayed natural count. -/
def iterateForward {count : Nat} (bijection : Bijection count count) :
    Nat → Fin count → Fin count
  | 0, index => index
  | steps + 1, index => bijection.forward
      (iterateForward bijection steps index)

/-- Zero forward steps leave the retained index unchanged. -/
@[simp] theorem iterateForward_zero {count : Nat}
    (bijection : Bijection count count) (index : Fin count) :
    Bijection.iterateForward bijection 0 index = index := rfl

/-- A successor iteration applies the forward map once after the preceding iteration. -/
@[simp] theorem iterateForward_succ {count : Nat}
    (bijection : Bijection count count) (steps : Nat)
    (index : Fin count) :
    Bijection.iterateForward bijection (steps + 1) index =
      bijection.forward (Bijection.iterateForward bijection steps index) := rfl

/-- Every finite iterate of a bijection's forward map is injective.

Induction on the supplied step count composes the stored forward-map injectivity with
injectivity of the preceding iterate. -/
theorem iterateForward_injective {count : Nat}
    (bijection : Bijection count count) :
    ∀ steps : Nat, Function.Injective (Bijection.iterateForward bijection steps)
  | 0 => fun _ _ equal => equal
  | steps + 1 => by
      intro left right equal
      apply iterateForward_injective bijection steps
      exact bijection.forward_injective equal

/-- Iteration over a sum of step counts splits into two consecutive iterations.

Induction on the second count retains the same forward map and starting
index. Each successor applies one further retained forward step. -/
theorem iterateForward_add {count : Nat}
    (bijection : Bijection count count) (first second : Nat)
    (index : Fin count) :
    Bijection.iterateForward bijection (first + second) index =
      Bijection.iterateForward bijection second
        (Bijection.iterateForward bijection first index) := by
  induction second with
  | zero => rfl
  | succ second inductionHypothesis =>
      rw [Nat.add_succ, Bijection.iterateForward_succ, Bijection.iterateForward_succ,
        inductionHypothesis]
end Bijection

end Purelib.Data.Fin.Bijection

end

section
@[expose] public section

/-!
# Finite braid words and combinatorial closures

This file supplies the finite combinatorial target for certified polynomial
root motion.  A braid word is a displayed list of signed adjacent
transpositions.  Its strand action is evaluated into the explicit finite
bijections used by `Purelib.CCL.Progressive.Monodromy`; no quotient group, infinite
configuration space, or choice of representatives is introduced.

The closure predicate deliberately records the exact finite condition needed
to distinguish a knot from a multi-component link: the evaluated strand
permutation is one cycle.  A `CertifiedLoopBraid` then joins a word to the
monodromy of one finite chamber loop by pointwise equality of their displayed
permutations.
-/

namespace Purelib.Data.Fin.Bijection.Iteration

/-- Pointwise equal forward maps have equal iterates at each retained index and step
count. -/
theorem iterateForward_same {count : Nat}
    {left right : Bijection count count}
    (same : Bijection.Same left right)
    (steps : Nat) (index : Fin count) :
    Bijection.iterateForward left steps index =
      Bijection.iterateForward right steps index := by
  induction steps with
  | zero => rfl
  | succ prior inductionHypothesis =>
      rw [Bijection.iterateForward_succ,
        Bijection.iterateForward_succ,
        inductionHypothesis, same]

end Purelib.Data.Fin.Bijection.Iteration

end

section
@[expose] public section

/-!
# Constructive orbit labelling of cyclic monodromy

A finite one-cycle permutation can be labelled without any choice principle:
select one displayed base index and enumerate the orbit of the explicit
inverse map.  Bounded preimage search turns that injective enumeration into a
`Bijection`.  With this labelling, the original permutation is exactly
the cyclic predecessor, hence exactly the endpoint action of the positive
Artin band `sigma_1 ... sigma_(d-1)`.
-/

namespace Purelib.Data.Fin.Bijection.Iteration

section Bijection

/-- Every finite forward iterate commutes with one additional forward step. -/
theorem iterateForward_commutes_forward {count : Nat}
    (bijection : Bijection count count) (steps : Nat)
    (index : Fin count) :
    Bijection.iterateForward bijection steps
        (bijection.forward index) =
      bijection.forward
        (Bijection.iterateForward
          bijection steps index) := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      rw [Bijection.iterateForward_succ,
        Bijection.iterateForward_succ,
        inductionHypothesis]

/-- Every finite forward iterate commutes with the retained backward map. -/
theorem iterateForward_commutes_backward {count : Nat}
    (bijection : Bijection count count) (steps : Nat)
    (index : Fin count) :
    Bijection.iterateForward bijection steps
        (bijection.backward index) =
      bijection.backward
        (Bijection.iterateForward
          bijection steps index) := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      rw [Bijection.iterateForward_succ,
        Bijection.iterateForward_succ,
        inductionHypothesis, bijection.forward_backward,
        bijection.backward_forward]

/-- Equal numbers of backward and forward steps cancel at every retained finite index.

Iterating the reversed bijection executes the backward map; commutation and the
stored inverse laws cancel the two finite iterations. -/
theorem iterate_reverse_cancel {count : Nat}
    (bijection : Bijection count count) (steps : Nat)
    (index : Fin count) :
    Bijection.iterateForward bijection steps
        (Bijection.iterateForward
          bijection.reverse steps index) = index := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      rw [Bijection.iterateForward_succ,
        Bijection.iterateForward_succ]
      change bijection.forward
          (Bijection.iterateForward bijection steps
            (bijection.backward
              (Bijection.iterateForward
                bijection.reverse steps index))) = index
      rw [Iteration.iterateForward_commutes_backward,
        bijection.forward_backward, inductionHypothesis]
end Bijection

end Purelib.Data.Fin.Bijection.Iteration

end

section
@[expose] public section

/-!
# The quadratic power loop realizes the positive two-strand generator

`Purelib.CCL.Progressive.PowerMonodromy.unitCircuitLoop` is the existing fully explicit rational
coefficient loop for `Z^d-w`: four stereographic rational quarter-arcs,
finitely subdivided until every root-owner Rouché bound is satisfied.  Its
finite winding calculation proves that the owner monodromy is one full
`d`-cycle.

Here `d=2`.  On two displayed indices, a fixed-point-free bijection is the
unique transposition.  Consequently the positive one-circuit power loop has
the same strand action as the one-letter word `[sigma_1]`.  The positive sign
is backed by the already calculated positive parameter winding `4`, not by an
arbitrary sign choice.
-/

namespace Purelib.Data.Fin.Bijection.Iteration

/-- One iteration of a finite bijection executes its forward map once. -/
theorem iterateForward_one {count : Nat}
    (bijection : Bijection count count) (index : Fin count) :
    Bijection.iterateForward bijection 1 index =
      bijection.forward index := rfl
end Purelib.Data.Fin.Bijection.Iteration

end
