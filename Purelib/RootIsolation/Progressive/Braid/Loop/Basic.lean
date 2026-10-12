module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Fin.Bijection.Cycle
import Purelib.RootIsolation.Progressive.Braid.Projected.Frame
import Purelib.RootIsolation.Progressive.Braid.Projected.Path
public import Purelib.RootIsolation.Progressive.Braid.Projected.Vertices
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Topology.Knot.Closure.Basic
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Path.Transport
import Purelib.Topology.Knot.Braid.Basic

open Purelib.RootIsolation.Progressive.Braid.Projected.Frame (ProjectedFrame)
open Purelib.RootIsolation.Progressive.Braid.Projected.Path (ProjectedPath)

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

namespace Purelib.RootIsolation.Progressive.Braid.Loop.Basic

set_option genInjectivity false in
/-- A closed, finitely subdivided, projection-certified rational polynomial
loop based at one displayed projected chamber frame. -/
structure AdmissibleLoop {strands : Nat} (base :
  ProjectedFrame strands) where
  /-- The actual projected chamber path returning to its original base frame. -/ path :
    ProjectedPath base base

constructive_injectivity AdmissibleLoop

namespace AdmissibleLoop

/-- Read the braid word extracted from the retained projected loop. -/
def word {strands : Nat} {base :
  ProjectedFrame strands}
    (loop : Progressive.Braid.Loop.Basic.AdmissibleLoop base) : Topology.Knot.Braid.Word strands :=
  loop.path.word

/-- Close the retained loop's braid word with its original strand count. -/
def closure {strands : Nat} {base :
  ProjectedFrame strands}
    (loop : Progressive.Braid.Loop.Basic.AdmissibleLoop base) : Topology.Knot.Braid.Closure where
  strands := strands
  word := loop.word

/-- The constant projected loop at the displayed base frame. -/
def identity {strands : Nat} (base :
  ProjectedFrame strands) :
    Progressive.Braid.Loop.Basic.AdmissibleLoop base where
  path := .nil base

/-- Reverse the retained projected loop while keeping its original base frame. -/
def reverse {strands : Nat} {base :
  ProjectedFrame strands}
    (loop : Progressive.Braid.Loop.Basic.AdmissibleLoop base) : Progressive.Braid.Loop.Basic.AdmissibleLoop base where
  path := loop.path.reverse

/-- The constant projected loop extracts the empty braid word. -/
@[simp] theorem identity_word {strands : Nat}
    (base : ProjectedFrame strands) :
      (Progressive.Braid.Loop.Basic.AdmissibleLoop.identity base).word = [] := rfl

/-- Reversing the retained projected loop extracts the inverse original braid word. -/
@[simp] theorem reverse_word {strands : Nat}
    {base : ProjectedFrame strands} (loop :
      Progressive.Braid.Loop.Basic.AdmissibleLoop base) :
    loop.reverse.word = loop.word.inverse :=
  ProjectedPath.word_reverse loop.path

/-- Read every retained coefficient polynomial along the projected loop, including its endpoints. -/
def coefficientVertices {strands : Nat} {base :
  ProjectedFrame strands}
    (loop : Progressive.Braid.Loop.Basic.AdmissibleLoop base) : List
      Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  Progressive.Braid.Projected.Vertices.coefficientVertices loop.path

/-- The coefficient-vertex list has one more entry than the original loop step count. -/
@[simp] theorem coefficientVertices_length
  {strands : Nat}
    {base : ProjectedFrame strands} (loop :
      Progressive.Braid.Loop.Basic.AdmissibleLoop base) :
    loop.coefficientVertices.length = loop.path.stepCount + 1 :=
  Progressive.Braid.Projected.Vertices.coefficientVertices_length loop.path

/-- Headline finite polynomial-loop braid theorem.  The existential witness
is the directly evaluated word, and its equation is the previously proved
finite extraction calculation. -/
theorem yieldsCertifiedBraid {strands : Nat}
    {base : ProjectedFrame strands} (loop :
      Progressive.Braid.Loop.Basic.AdmissibleLoop base) :
    ∃ word : Topology.Knot.Braid.Word strands,
      ∀ position : Fin strands,
        loop.path.chamberPath.monodromy.forward
            (base.ownerIndex position) =
          base.ownerIndex (word.permutation.forward position) :=
  ⟨loop.word, loop.path.transport_agrees⟩

/-- Single-cycle monodromy of the retained loop makes its extracted braid closure a knot. -/
theorem
  closure_isKnot_of_monodromy_isSingleCycle
  {strands : Nat}
    {base : ProjectedFrame strands} (loop :
      Progressive.Braid.Loop.Basic.AdmissibleLoop base)
    (single : Data.Fin.Bijection.IsSingleCycle
      loop.path.chamberPath.monodromy) : loop.closure.IsKnot :=
  loop.path.closure_isKnot_of_monodromy_isSingleCycle base single

/-- Concatenation of closed coefficient loops. -/
def append {strands : Nat} {base :
  ProjectedFrame strands}
    (first second : Progressive.Braid.Loop.Basic.AdmissibleLoop base) : Progressive.Braid.Loop.Basic.AdmissibleLoop base
      where
  path := first.path.append second.path

/-- Concatenating retained loops concatenates their extracted braid words in the same order. -/
@[simp] theorem append_word {strands : Nat}
    {base : ProjectedFrame strands} (first second :
      Progressive.Braid.Loop.Basic.AdmissibleLoop base) :
    (first.append second).word = first.word ++ second.word := by
  exact ProjectedPath.word_append first.path second.path

end AdmissibleLoop

end Purelib.RootIsolation.Progressive.Braid.Loop.Basic

end
