module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Topology.Knot.Closure.Basic
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Fin.Bijection.Cycle
import Purelib.Data.Fin.Bijection.Iteration
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
public import Purelib.RootIsolation.Progressive.Chamber.Path.Transport
import Purelib.Topology.Knot.Braid.Basic

open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)

open Purelib

open Purelib.RootIsolation

section
public section

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

namespace Purelib.RootIsolation.Progressive.Braid.Certified

open Purelib.Topology.Knot.Braid (Word)

set_option genInjectivity false in
/-- A certified braid extraction for one closed finite root path.  The word
is useful combinatorial output; `agrees` is the finite certificate that its
strand action is exactly the root-owner monodromy. -/
structure CertifiedLoopBraid (frame :
  ChamberFrame)
    (loop : ChamberPath frame frame) where
  /-- The actual finite braid word retained for the original closed root path. -/ word : Topology.Knot.Braid.Word
    frame.degree
  /-- The retained word's strand permutation agrees pointwise with the original owner monodromy. -/ agrees :
    Data.Fin.Bijection.Same
    word.permutation loop.monodromy

constructive_injectivity CertifiedLoopBraid

namespace CertifiedLoopBraid

/-- Certify the empty braid word for the empty path at the original chamber frame. -/
@[expose] def identity (frame :
  ChamberFrame) :
    Progressive.Braid.Certified.CertifiedLoopBraid frame (.nil frame) where
  word := []
  agrees := fun _ => rfl

/-- Concatenate two certified extractions without recomputing any root
matching. -/
@[expose] def append {frame :
  ChamberFrame} {first second : ChamberPath frame frame}
    (firstBraid : Progressive.Braid.Certified.CertifiedLoopBraid frame first)
    (secondBraid : Progressive.Braid.Certified.CertifiedLoopBraid frame second) :
    Progressive.Braid.Certified.CertifiedLoopBraid frame (first.append second) where
  word := firstBraid.word ++ secondBraid.word
  agrees := by
    intro index
    calc
      (firstBraid.word ++ secondBraid.word).permutation.forward index =
          secondBraid.word.permutation.forward
            (firstBraid.word.permutation.forward index) :=
        Word.permutation_append firstBraid.word secondBraid.word index
      _ = second.monodromy.forward (first.monodromy.forward index) := by
        rw [firstBraid.agrees, secondBraid.agrees]
      _ = (first.append second).monodromy.forward index :=
        (ChamberPath.monodromy_append
          first second index).symm

/-- Invert the retained braid word and its exact agreement with the original reversed root path. -/
@[expose] def reverse {frame :
  ChamberFrame} {loop : ChamberPath frame frame}
    (braid : Progressive.Braid.Certified.CertifiedLoopBraid frame loop) :
    Progressive.Braid.Certified.CertifiedLoopBraid frame loop.reverse where
  word := braid.word.inverse
  agrees := Data.Fin.Bijection.same_trans
    braid.word.permutation_inverse
    (Data.Fin.Bijection.same_trans
      (Data.Fin.Bijection.Basic.reverse_same braid.agrees)
      (Data.Fin.Bijection.same_symm
        loop.monodromy_reverse))

/-- Form the finite braid closure from the retained word and original chamber degree. -/
@[expose] def closure {frame :
  ChamberFrame} {loop : ChamberPath frame frame}
    (braid : Progressive.Braid.Certified.CertifiedLoopBraid frame loop) : Topology.Knot.Braid.Closure :=
  { strands := frame.degree
    word := braid.word }

/-- A retained braid closure is a knot when the original owner monodromy is one full cycle. -/
theorem
  closure_isKnot_of_monodromy_isSingleCycle
    {frame : ChamberFrame} {loop : ChamberPath frame frame}
    (braid : Progressive.Braid.Certified.CertifiedLoopBraid frame loop)
    (single : Data.Fin.Bijection.IsSingleCycle
      loop.monodromy) :
    braid.closure.IsKnot := by
  refine
    { return_at_count := ?_
      no_early_return := ?_ }
  · intro index
    change Data.Fin.Bijection.iterateForward
      braid.word.permutation frame.degree index = index
    rw [Data.Fin.Bijection.Iteration.iterateForward_same braid.agrees]
    exact single.return_at_count index
  · intro index steps positive small returned
    apply single.no_early_return index steps positive small
    change Data.Fin.Bijection.iterateForward
      braid.word.permutation steps index = index at returned
    rw [← Data.Fin.Bijection.Iteration.iterateForward_same braid.agrees]
    exact returned

end CertifiedLoopBraid

end Purelib.RootIsolation.Progressive.Braid.Certified

end
