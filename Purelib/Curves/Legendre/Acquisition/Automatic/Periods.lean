module
import Purelib.Topology.Knot.Braid.ThreeStrand.Word
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic
import Purelib.Curves.Legendre.Acquisition.Automatic.Basic
public import Purelib.Curves.Legendre.Acquisition.Automatic.Positive
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.PeriodMonodromy
public import Purelib.Curves.Legendre.Periods.Positive.Enclosure
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Output
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Matrix.Operational.Integral.Action
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Process.Imaginary

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.Acquisition

open Purelib.Curves.Legendre.Acquisition.Automatic

open Purelib.Curves.Legendre.Periods.Positive

open Purelib.Riemann.Periods

open Purelib.Topology.Knot.Braid

section
@[expose] public section

/-!
# Automatic finite-word dual period outputs

The public result caches the exact word matrix, its denominator preparation,
and the productive output. A positive enclosure constructs it directly;
bounded acquisition returns either this same result or an exact resumable
state. The transport proof is shared by both construction routes.
-/

namespace Purelib.Curves.Legendre.Acquisition.Automatic.Periods

/-- The finite period positivity theorem supplies the one reusable enclosure; callers of this adapter need neither an
enclosure nor denominator witnesses. -/
def guaranteedOfPeriodPositivity {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (data : PeriodMonodromy.NormalizedData frame)
    (positivity : PeriodMatrix.PointwisePositivity data.normalized)
    (word : ThreeStrand.Word) : Automatic.Basic.Ready data.ratio word :=
  Positive.guaranteed (Enclosure.enclosureOfPeriodPositivity data positivity) word
namespace Ready

/-- The automatic result is the transported period ratio, expressed by its fraction-free equation on the actual
closed-path period coordinates. -/
def transport {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (data : PeriodMonodromy.NormalizedData frame)
    (path : Paths.Path frame frame)
    (result : Automatic.Basic.Ready data.ratio path.word) :
    Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul
        (data.periods path 0) result.output).name
      (data.periods path 1).name :=
  PeriodMonodromy.productiveRatio_ofHomogeneous
    (data.periods path) data.aPeriod _ _ result.output
    (data.periods_normalized path 0) (data.periods_normalized path 1)
    result.output_equation

end Ready

/-- No caller-supplied denominator preparations: the single positive enclosure constructs the output and its
arbitrary-loop transport witness. -/
def guaranteed_transport {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (data : PeriodMonodromy.NormalizedData frame)
    (positivity : Positive.Basic.PositiveEnclosure data.ratio)
    (path : Paths.Path frame frame) :
    Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul (data.periods path 0)
        (Positive.guaranteed positivity path.word).output).name
      (data.periods path 1).name :=
  Curves.Legendre.Acquisition.Automatic.Periods.Ready.transport
    data path (Positive.guaranteed positivity path.word)

end Purelib.Curves.Legendre.Acquisition.Automatic.Periods

end
