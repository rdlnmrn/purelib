module
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.CCL.Semantics
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Multiplicity.Observation.CCL.Name
import Purelib.RootIsolation.Multiplicity.Side.Basic
import Purelib.RootIsolation.Multiplicity.Side.CCL.Basic
public import Purelib.RootIsolation.Multiplicity.Side.CCL.Persistent
import Purelib.RootIsolation.Multiplicity.Side.Index
import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
import Purelib.RootIsolation.Multiplicity.Family.Basic
import Purelib.RootIsolation.Multiplicity.Observation.Index

open Purelib.Data.CCL.Transducer (Machine)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Multiplicity.Side.Basic (SideResult)
open Purelib.RootIsolation.Multiplicity.Side.CCL.Basic (SideCCL)
open Purelib.RootIsolation.Multiplicity.Side.Index (SideIndex)

open Purelib.Approximation.Gaussian

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

namespace Purelib.RootIsolation.Multiplicity.Side.CCL.Name

/-- Arithmetic name at any zero-side or pole-side site. -/
def sideArithmeticName
    {source opposite : CoefficientPolynomial}
    (side : SideResult source opposite)
    (data : SideCCL side) : SideIndex side →
      Name.Basic.Named := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero =>
      intro index
      exact nomatch index
  | positive input family =>
      intro index
      exact Multiplicity.Observation.CCL.Name.observationArithmeticName (family.observationAt index.1)
        (data index.1) index.2

/-- Exact raw-parser semantics retained by any persistent site state. -/
theorem sidePersistentExact
    {source opposite : CoefficientPolynomial}
    (side : SideResult source opposite)
    (data : SideCCL side) (index : SideIndex side)
    (state : Multiplicity.Side.CCL.Persistent.SidePersistentState side data index) :
    Data.CCL.Transducer.Machine.Semantics.Basic.ExactCursor
      (sideArithmeticName side data index).process
      (sideArithmeticName side data index).state
      (Multiplicity.Side.CCL.Persistent.sidePersistentMachine side data index state) := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family => exact state.cursor.exact

/-- Each indexed side-site name emits exactly the requested finite number of bits extending its initial word. -/
theorem sideArithmeticName_productive
    {source opposite : CoefficientPolynomial}
    (side : SideResult source opposite)
    (data : SideCCL side) (index : SideIndex side) (count : Nat) :
    (sideArithmeticName side data index).machine.emitted.IsPrefix
        (Machine.Advance.advance
          (sideArithmeticName side data index).machine count).emitted ∧
      (Machine.Advance.advance
        (sideArithmeticName side data index).machine count).emitted.length =
          count :=
  (sideArithmeticName side data index).productive count

/-- Every finite prefix of the original indexed side-site name has exact raw-parser semantics. -/
theorem sideArithmeticName_exact
    {source opposite : CoefficientPolynomial}
    (side : SideResult source opposite)
    (data : SideCCL side) (index : SideIndex side) (count : Nat) :
    let name := sideArithmeticName side data index
    Data.CCL.Transducer.Machine.Semantics.Basic.ExactCursor
      name.process name.state
      (Machine.Advance.advance name.machine count) :=
  Name.CCL.Semantics.Named.advance_exact
    (sideArithmeticName side data index) count
end Purelib.RootIsolation.Multiplicity.Side.CCL.Name

end
