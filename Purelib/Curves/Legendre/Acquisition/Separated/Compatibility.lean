module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic
import Purelib.Curves.Legendre.Acquisition.Automatic.Positive

import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Positive
public import Purelib.Curves.Legendre.SeparatedWords
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Output
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Process.Imaginary

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.Acquisition.Automatic

section
@[expose] public section

/-! # Unsigned word preparation, including the negative acquisition path -/

namespace Purelib.Curves.Legendre.Acquisition.Separated.Compatibility

open Purelib.Curves.Legendre.SeparatedWords (Word)
open Purelib.Approximation.Gaussian.Acquisition.State (initial)

/-- Unsigned preparation from the original positive enclosure agrees operationally with its guaranteed positive word
output. -/
def original_positive_compatible {tau :
  Coherent.CoherentNamed}
    (positive : Positive.Basic.PositiveEnclosure tau) (word : SeparatedWords.Word) :
    Gaussian.Equivalence.NamedEquivalent
      (SeparatedWords.acquire (Approximation.Gaussian.Process.Imaginary.Separation.ofPositive positive)
          word).output.name
      (Positive.guaranteed positive word).output.name :=
  (SeparatedWords.acquire (Approximation.Gaussian.Process.Imaginary.Separation.ofPositive positive) word).respects_ready
    (Positive.guaranteed positive word)
end Purelib.Curves.Legendre.Acquisition.Separated.Compatibility

end
