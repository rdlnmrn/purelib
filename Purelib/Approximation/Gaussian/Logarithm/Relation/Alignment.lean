module
public import Purelib.Approximation.Gaussian.Logarithm.Relation.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Difference
public import Purelib.Approximation.Relation.Selection
import Init.Prelude
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Approximation.Relation.Fibre

open Purelib.Approximation.Gaussian.Logarithm.Relation.Basic (Candidate)

open Purelib

open Purelib.Approximation.Gaussian.Logarithm

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Relation

section
@[expose] public section

/-!
# Local logarithm branches as a finite multivalued relation

A candidate is one anchored chart on one explicit coherent input cell, tagged
by a caller-supplied persistent owner.  A displayed finite family is local; it
does not enumerate all logarithm values.  Until separation has genuinely been
certified, distinct candidates remain in one explicit unresolved cluster.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Relation.Alignment
universe u

/-- Explicit zero discrepancy aligns one displayed branch to an independently owned reference branch. -/
def Aligned {Owner : Type u}
    (candidate reference : Candidate Owner) : Type :=
  Difference.LocalAlignment
    reference.branch.output candidate.branch.output

/-- A finite branch label selected by explicit zero alignment to an independently retained reference. -/
abbrev AlignedSelection {Owner : Type u} {count :
  Nat}
    (candidate : Fin count → Candidate Owner) :=
  Selection.AlignedSelection Aligned
    (Relation.Basic.localFibre candidate)

/-- Selection exposes exactly the candidate named by explicit alignment; list order and numerical nearest-neighbour
rules play no role. -/
def selectAligned {Owner : Type u} {count : Nat}
    {candidate : Fin count → Candidate Owner}
    (selection : AlignedSelection candidate) :
      Candidate Owner :=
  (Relation.Basic.localFibre candidate).candidate selection.label
end Purelib.Approximation.Gaussian.Logarithm.Relation.Alignment

end
