module
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Positive
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic
import Purelib.LinearAlgebra.Matrix.Inverse.Right
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Data.Vector.Basic

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Process.Imaginary

open Purelib.LinearAlgebra.Matrix.Inverse

open Purelib.Topology.Knot

open Purelib.Topology.Knot.Braid.ThreeStrand.Integral

section
@[expose] public section

/-!
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
-/

namespace Purelib.Curves.Legendre.Preparation.Positive
open Purelib.Riemann.Integration.LegendreModularMonodromy (fractionalDenominator)
open Purelib.Approximation.Gaussian.Division.Prepared (DenominatorPreparation)

/-- Every finite dual braid word has its denominator prepared automatically from the same positive enclosure. No
per-word separation witness is an input. -/
def prepareWord {tau : Coherent.CoherentNamed} (certificate :
  Positive.Basic.PositiveEnclosure tau)
    (word : Braid.Word 3) :
    DenominatorPreparation
      (fractionalDenominator
        (Dual.periodMatrix word) tau) :=
  Positive.prepare certificate _ (Right.row_nonzero_of_inverse _ _
    (Dual.periodMatrix_inverse_identities word).1)
end Purelib.Curves.Legendre.Preparation.Positive

end
