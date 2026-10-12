module
import Purelib.Topology.Knot.Braid.ThreeStrand.Word
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Curves.Legendre.Acquisition.Automatic.Basic
import Purelib.Topology.Knot.Braid.Artin
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual
import Init.Prelude
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Output
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Riemann.Integration.LegendreModularMonodromy

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.FractionalAction.Integral

open Purelib.Approximation.Gaussian.Name

open Purelib.Curves.Legendre.Acquisition

open Purelib.Topology.Knot.Braid

open Purelib.Topology.Knot.Braid.ThreeStrand.Integral

section
@[expose] public section

/-!
# Automatic finite-word dual period outputs

The public result caches the exact word matrix, its denominator preparation,
and the productive output. A positive enclosure constructs it directly;
bounded acquisition returns either this same result or an exact resumable
state. The transport proof is shared by both construction routes.
-/

namespace Purelib.Curves.Legendre.Acquisition.Automatic.Comparison

namespace Ready

/-- Independently acquired outputs agree whenever their finite words have the same period matrix, even when the words
and preparations differ. -/
def respects_matrix {tau : Coherent.CoherentNamed}
  {firstWord secondWord : ThreeStrand.Word}
    (first : Automatic.Basic.Ready tau firstWord) (second : Automatic.Basic.Ready tau secondWord)
    (equal : Dual.periodMatrix firstWord =
      Dual.periodMatrix secondWord) :
    Gaussian.Equivalence.NamedEquivalent first.output.name second.output.name := by
  rw [first.output_eq, second.output_eq]
  exact Comparison.fractionalLinear_of_matrix_eq
    (first.matrix_eq.trans (equal.trans second.matrix_eq.symm)) tau
    first.preparation second.preparation

/-- Certified Artin rewrites preserve automatically acquired outputs. -/
def respects_braid {tau : Coherent.CoherentNamed}
  {firstWord secondWord : ThreeStrand.Word}
    (first : Automatic.Basic.Ready tau firstWord) (second : Automatic.Basic.Ready tau secondWord)
    (relation : Artin.Equivalent firstWord secondWord) :
    Gaussian.Equivalence.NamedEquivalent first.output.name second.output.name :=
  respects_matrix first second
    (Dual.equivalent_periodMatrix_eq relation)

/-- Successful results do not depend on budgets, resumptions, or the choice between quantitative preparation and bounded
acquisition. -/
def respects {tau : Coherent.CoherentNamed} {word
  : ThreeStrand.Word}
    (first second : Automatic.Basic.Ready tau word) :
    Gaussian.Equivalence.NamedEquivalent first.output.name second.output.name :=
  respects_matrix first second rfl
end Ready

/-- Evidence-driven resumption agrees with any automatically acquired output for the same word, regardless of its budget
or retained search state. -/
def resume_respects {tau : Coherent.CoherentNamed} {word
  : ThreeStrand.Word}
    (state : Automatic.Basic.State tau word) (requirement : Automatic.Basic.Requirement state)
    (evidence : Automatic.Basic.Evidence requirement) (other : Automatic.Basic.Ready tau word) :
    Gaussian.Equivalence.NamedEquivalent (Automatic.Basic.resume state requirement evidence).output.name
      other.output.name :=
  Curves.Legendre.Acquisition.Automatic.Comparison.Ready.respects
    (Automatic.Basic.resume state requirement evidence) other
end Purelib.Curves.Legendre.Acquisition.Automatic.Comparison

end
