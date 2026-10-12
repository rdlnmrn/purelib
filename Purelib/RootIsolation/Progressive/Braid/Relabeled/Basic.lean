module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Topology.Knot.Closure.Basic
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Fin.Bijection.Cycle
import Purelib.Data.Fin.Bijection.Iteration
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
public import Purelib.RootIsolation.Progressive.Chamber.Path.Transport
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Topology.Knot.Braid.Basic

open Purelib

open Purelib.RootIsolation

section
public section

/-!
# Constructive orbit labelling of cyclic monodromy

A finite one-cycle permutation can be labelled without any choice principle:
select one displayed base index and enumerate the orbit of the explicit
inverse map.  Bounded preimage search turns that injective enumeration into a
`Bijection`.  With this labelling, the original permutation is exactly
the cyclic predecessor, hence exactly the endpoint action of the positive
Artin band `sigma_1 ... sigma_(d-1)`.
-/

namespace Purelib.RootIsolation.Progressive.Braid.Relabeled.Basic

/-! ## Closed braids with an explicit owner relabelling -/

set_option genInjectivity false in
/-- A certified loop braid whose word positions are related to the chamber's
internal owner indices by an explicit finite bijection. -/
structure RelabeledLoopBraid
    (frame : Progressive.Chamber.Frame.ChamberFrame)
    (loop : Progressive.Chamber.Path.Basic.ChamberPath frame frame) where
  /-- The actual finite braid word of the original closed root path. -/ word : Topology.Knot.Braid.Word frame.degree
  /-- The retained finite bijection from word positions to original chamber-owner indices. -/ labeling :
    Data.Fin.Bijection frame.degree frame.degree
  /-- The saved labeling intertwines the original owner monodromy and retained word permutation. -/ agrees : ∀ position
    : Fin frame.degree,
    loop.monodromy.forward (labeling.forward position) =
      labeling.forward (word.permutation.forward position)

constructive_injectivity RelabeledLoopBraid

section RelabeledLoopBraid

/-- Certify the empty braid word and identity labeling for the empty original chamber path. -/
@[expose] def RelabeledLoopBraid.identity (frame :
  Progressive.Chamber.Frame.ChamberFrame) :
    Progressive.Braid.Relabeled.Basic.RelabeledLoopBraid frame (.nil frame) where
  word := []
  labeling := Data.Fin.Bijection.identity frame.degree
  agrees := fun _ => rfl

/-- Join two retained loop braids whose original labelings agree pointwise.

The output keeps the first labeling and concatenates the actual words, with transport agreement through the shared
chamber frame. -/
@[expose] def RelabeledLoopBraid.append {frame :
  Progressive.Chamber.Frame.ChamberFrame}
    {first second : Progressive.Chamber.Path.Basic.ChamberPath frame frame}
    (firstBraid : Progressive.Braid.Relabeled.Basic.RelabeledLoopBraid frame first)
    (secondBraid : Progressive.Braid.Relabeled.Basic.RelabeledLoopBraid frame second)
    (sameLabeling : Data.Fin.Bijection.Same
      firstBraid.labeling secondBraid.labeling) :
    Progressive.Braid.Relabeled.Basic.RelabeledLoopBraid frame (first.append second) where
  word := firstBraid.word ++ secondBraid.word
  labeling := firstBraid.labeling
  agrees := by
    intro position
    calc
      (first.append second).monodromy.forward
          (firstBraid.labeling.forward position) =
        second.monodromy.forward
          (first.monodromy.forward
            (firstBraid.labeling.forward position)) :=
        Progressive.Chamber.Path.Basic.ChamberPath.monodromy_append first second _
      _ = second.monodromy.forward
          (firstBraid.labeling.forward
            (firstBraid.word.permutation.forward position)) := by
        rw [firstBraid.agrees]
      _ = second.monodromy.forward
          (secondBraid.labeling.forward
            (firstBraid.word.permutation.forward position)) := by
        rw [sameLabeling]
      _ = secondBraid.labeling.forward
          (secondBraid.word.permutation.forward
            (firstBraid.word.permutation.forward position)) :=
        secondBraid.agrees (firstBraid.word.permutation.forward position)
      _ = firstBraid.labeling.forward
          (secondBraid.word.permutation.forward
            (firstBraid.word.permutation.forward position)) := by
        rw [sameLabeling]
      _ = firstBraid.labeling.forward
          ((firstBraid.word ++ secondBraid.word).permutation.forward
            position) := by
        rw [Topology.Knot.Braid.Word.permutation_append]
        rfl

/-- Invert a retained loop braid while preserving its original owner labeling. -/
@[expose] def RelabeledLoopBraid.reverse {frame :
  Progressive.Chamber.Frame.ChamberFrame}
    {loop : Progressive.Chamber.Path.Basic.ChamberPath frame frame}
    (braid : Progressive.Braid.Relabeled.Basic.RelabeledLoopBraid frame loop) :
    Progressive.Braid.Relabeled.Basic.RelabeledLoopBraid frame loop.reverse where
  word := braid.word.inverse
  labeling := braid.labeling
  agrees := by
    intro position
    calc
      loop.reverse.monodromy.forward (braid.labeling.forward position) =
          loop.monodromy.backward (braid.labeling.forward position) :=
        Progressive.Chamber.Path.Basic.ChamberPath.transport_reverse_forward loop _
      _ = braid.labeling.forward
          (braid.word.inverse.permutation.forward position) := by
        have forwardAt := braid.agrees
          (braid.word.permutation.backward position)
        rw [braid.word.permutation.forward_backward] at forwardAt
        have pulledBack := congrArg loop.monodromy.backward forwardAt
        rw [loop.monodromy.backward_forward] at pulledBack
        rw [braid.word.permutation_inverse position]
        exact pulledBack.symm

/-- Finite iterations of the retained word permutation and original monodromy agree through the saved labeling. -/
theorem RelabeledLoopBraid.iterate_agrees {frame :
  Progressive.Chamber.Frame.ChamberFrame}
    {loop : Progressive.Chamber.Path.Basic.ChamberPath frame frame}
    (braid : Progressive.Braid.Relabeled.Basic.RelabeledLoopBraid frame loop) (steps : Nat)
    (position : Fin frame.degree) :
    Data.Fin.Bijection.iterateForward loop.monodromy steps
        (braid.labeling.forward position) =
      braid.labeling.forward
        (Data.Fin.Bijection.iterateForward
          braid.word.permutation steps position) := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      rw [Data.Fin.Bijection.iterateForward_succ,
        Data.Fin.Bijection.iterateForward_succ,
        inductionHypothesis]
      exact braid.agrees _

/-- Form the finite closure of the retained braid word at the original chamber degree. -/
@[expose] def RelabeledLoopBraid.closure {frame :
  Progressive.Chamber.Frame.ChamberFrame}
    {loop : Progressive.Chamber.Path.Basic.ChamberPath frame frame}
    (braid : Progressive.Braid.Relabeled.Basic.RelabeledLoopBraid frame loop) : Topology.Knot.Braid.Closure where
  strands := frame.degree
  word := braid.word

/-- A relabeled retained braid closure is a knot when the original owner monodromy is a single cycle. -/
theorem
  RelabeledLoopBraid.closure_isKnot_of_monodromy_isSingleCycle
    {frame : Progressive.Chamber.Frame.ChamberFrame}
    {loop : Progressive.Chamber.Path.Basic.ChamberPath frame frame}
    (braid : Progressive.Braid.Relabeled.Basic.RelabeledLoopBraid frame loop)
    (single : Data.Fin.Bijection.IsSingleCycle
      loop.monodromy) : braid.closure.IsKnot := by
  refine
    { return_at_count := ?_
      no_early_return := ?_ }
  · intro position
    apply braid.labeling.forward_injective
    have returns := single.return_at_count (braid.labeling.forward position)
    rw [braid.iterate_agrees frame.degree position] at returns
    exact returns
  · intro position steps positive small returned
    apply single.no_early_return
      (braid.labeling.forward position) steps positive small
    rw [braid.iterate_agrees steps position]
    exact congrArg braid.labeling.forward returned

end RelabeledLoopBraid

end Purelib.RootIsolation.Progressive.Braid.Relabeled.Basic

end
