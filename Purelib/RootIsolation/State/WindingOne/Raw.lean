module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.State.Raw
public import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Winding.Box.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free shrinking winding-one tracks

The local Newton-square extractor is stable under iteration because every
returned square carries a new finite boundary-clearance certificate.  This
module packages those repeated finite calls as the numerical track interface
used by box isolation and any independently shrinking finite envelope.
-/

namespace Purelib.RootIsolation.State.WindingOne.Basic.WindingOneState

/-- Forget exact winding four while retaining its constructive nonzeroness. -/
def raw
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (state : State.WindingOne.Basic.WindingOneState p ambient) : State.Raw.RawWindingState p ambient :=
  { box := state.box
    refinesAmbient := state.refinesAmbient
    proper := state.proper
    clearance := state.clearance
    rawWinding_ne := by
      intro windingZero
      have fourZero : (4 : Int) = 0 := by
        rw [← state.rawWindingFour]
        exact windingZero
      exact ((show (4 : Int) ≠ 0 by decide) fourZero).elim }
end Purelib.RootIsolation.State.WindingOne.Basic.WindingOneState

end
