module
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Topology.Knot.Braid.ThreeStrand.Word
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Positive
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic
public import Purelib.Curves.Legendre.Acquisition.Automatic.Basic
import Purelib.LinearAlgebra.Matrix.Inverse.Right
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual
import Init.Prelude
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Output
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Process.Imaginary

open Purelib.Curves.Legendre.Acquisition

open Purelib.LinearAlgebra.Matrix.Inverse

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

namespace Purelib.Curves.Legendre.Acquisition.Automatic.Positive
open Purelib.Riemann.Integration.LegendreModularMonodromy (fractionalLinear)

/-- Total construction from the single reusable positive enclosure. -/
def guaranteed {tau : Coherent.CoherentNamed} (certificate
  : Positive.Basic.PositiveEnclosure tau)
    (word : ThreeStrand.Word) : Automatic.Basic.Ready tau word :=
  let matrix := Dual.periodMatrix word
  let preparation := Positive.prepare certificate matrix
    (Right.row_nonzero_of_inverse _ _
      (Dual.periodMatrix_inverse_identities word).1)
  { matrix := matrix
    matrix_eq := rfl
    preparation := preparation
    output := fractionalLinear matrix tau preparation
    output_eq := rfl }
end Purelib.Curves.Legendre.Acquisition.Automatic.Positive

end
