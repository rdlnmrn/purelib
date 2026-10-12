module
public import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.CCL.Persistent.State.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data.List.BinaryPrefix.Basic (SourcePersistentCCLWordAlias)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Persistent constructive CCL prefixes on shrinking root boxes

A fresh rational sample from each refined box need not retain any prefix of
the preceding sample's CCL word.  The persistent invariant below records the
stronger fact actually needed by the paper: every later winding-one subbox
has an explicit nonzero rational sample represented by the same raw prefix.

The second half of the file is deliberately structural.  It proves that a
finite one-bit controller with this invariant can be iterated for any
requested natural number of bits while the numerical box is independently
contracted to a requested rational accuracy.  Constructing that one-bit
controller from the finite curve-count and equality-owner geometry is a
separate obligation; it is not postulated as a theorem here.
-/

namespace Purelib.RootIsolation.CCL.Persistent

namespace Controller.Basic

set_option genInjectivity false in
/-- Output contract of the remaining geometric controller.  A nonterminal
step appends exactly one bit while preserving the persistent provider;
otherwise it returns an exact displayed rational root in the current box. -/
inductive StepResult
    {p : CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) where
  /-- A retained exact polynomial root inside the original current box. -/ | exact (root :
    CCL.Persistent.State.Basic.ExactRootIn p current.numerical.box)
  /-- One appended raw bit and its persistent state, retaining box refinement and the exact word extension. -/ | next
    (bit : Bool) (state : State p ambient)
      (boxRefines : state.numerical.box.Refines current.numerical.box)
      (word_eq : state.word = current.word ++ [bit])

constructive_injectivity StepResult

end Controller.Basic

set_option genInjectivity false in
/-- Finite data needed to turn one persistent raw prefix into its next bit.
The concrete implementation must be supplied by the constructive
curve-count/equality-owner development. -/
structure Controller (p :
  CoefficientPolynomial) (ambient : Box) where
  /-- Execute one finite persistent-prefix step for the supplied original state. -/ step : (current :
    State p ambient) → Controller.Basic.StepResult current

constructive_injectivity Controller

namespace Controller.Basic

set_option genInjectivity false in
/-- Result of structurally requesting a finite number of further bits. -/
inductive AdvanceResult
    {p : CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) : Nat → Type where
  /-- An exact displayed root retained in the original requested state's box. -/ | exact {count : Nat} (root :
    CCL.Persistent.State.Basic.ExactRootIn p current.numerical.box) :
      AdvanceResult current count
  /-- A state retaining the exact requested prefix extension, its length and refinement of the original state. -/ |
    advanced {count : Nat} (state : State p ambient)
      (refines : CCL.Persistent.State.Basic.StateRefines state current)
      (extension : SourcePersistentCCLWordAlias)
      (extension_length : extension.length = count)
      (word_eq : state.word = current.word ++ extension)
      (length_eq : state.word.length = current.word.length + count) :
      AdvanceResult current count

constructive_injectivity AdvanceResult

/-- Structural recursion on the requested number of raw bits. -/
def advanceBits
    {p : CoefficientPolynomial} {ambient : Box}
    (controller : Controller p ambient) (current : State p
      ambient) :
    (count : Nat) → CCL.Persistent.Controller.Basic.AdvanceResult current count
  | 0 => .advanced current (CCL.Persistent.State.Basic.stateRefines_refl current) [] rfl
      (@Eq.symm SourcePersistentCCLWordAlias
        (@HAppend.hAppend
          SourcePersistentCCLWordAlias
          SourcePersistentCCLWordAlias
          SourcePersistentCCLWordAlias
          (@instHAppendOfAppend SourcePersistentCCLWordAlias
            (@List.instAppend Bool)) current.word [])
        current.word (Data.List.Append.append_nil current.word))
      (Nat.add_zero current.word.length).symm
  | count + 1 =>
      match controller.step current with
      | .exact root => .exact root
      | .next bit next boxRefines nextWord =>
          match advanceBits controller next count with
          | .exact root => .exact
              { point := root.point
                root := root.root
                inside := boxRefines.contains root.inside }
          | .advanced final finalRefines extension extensionLength
              finalWord finalLength =>
              have nextRefines : CCL.Persistent.State.Basic.StateRefines next current := by
                refine ⟨boxRefines, ?_⟩
                rw [nextWord]
                exact ⟨[bit], rfl⟩
              .advanced final (finalRefines.trans nextRefines)
                (bit :: extension) (by
                  exact @Eq.mp (Nat.succ extension.length = Nat.succ count)
                    ((bit :: extension).length = count + 1) rfl
                    (congrArg Nat.succ extensionLength)) (by
                  rewrite [finalWord, nextWord]
                  exact Data.List.Append.append_assoc _ _ _) (by
                    rewrite [finalLength, nextWord, Data.List.Append.length_append]
                    change current.word.length + 1 + count = current.word.length + (count + 1)
                    rewrite [Nat.add_assoc, Nat.add_comm 1 count]
                    rfl)

end Controller.Basic

end Purelib.RootIsolation.CCL.Persistent

end

section
-- Equation generation for the finite dispatcher uses ParserStep's private splitter.

@[expose] public section

/-!
# Finite dispatch through initial CCL boundary ownership

One persistent controller step first separates the current box from the
single affine pole of its decoder matrix, then removes the bounded set of
rational terminals, and finally inspects the current nonterminal child
formula.  It either executes a box-stable strict-sign/equality-owned step or
retains the first genuinely parameterized Hermitian boundary with its
analysis and a uniform positive decoder-denominator margin.  Universal zero
boundaries are discharged structurally, and finite zero sets are exhausted
by a bounded form-cache loop.  Coupling the remaining curve events to the
persistent sample provider remains.
-/

namespace Purelib.RootIsolation.CCL.Persistent.Controller.Basic
/-- The original one-bit persistent-controller result for the same input state. -/
abbrev SourcePersistentDispatchStepResultAlias
    {p : CoefficientPolynomial} {ambient : Box} (current :
      State p ambient) :=
  CCL.Persistent.Controller.Basic.StepResult current
end Purelib.RootIsolation.CCL.Persistent.Controller.Basic

end
