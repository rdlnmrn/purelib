module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
public import Purelib.Curves.Hyperelliptic.Differentials.Value
public import Purelib.Curves.Hyperelliptic.Sheets.Basic
public import Purelib.Geometry.Path.Gaussian.Lifted.Basic
public import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Basic

open Purelib.Integration.Polynomial.Gaussian

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Differentials

open Purelib.Geometry.Path.Gaussian

section
@[expose] public section

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Observation.Basis

set_option genInjectivity false in
/-- Finite algebraic evidence behind one sampled differential value. The generally irrational sheet coordinate remains a
coherent CCL name satisfying the curve equation operationally. The displayed rational integrand reading must be admitted
by one explicit finite state of the named quotient. -/
structure AlgebraicObservation {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential genus)
    {start finish : Lifted.Basic.LiftedPoint 2} (liftedCell : Lifted.Basic.LiftedCell start finish)
    (cell : Cell.Basic.CellModel)
    (observation : Cell.Basic.LocalObservation cell.polynomial cell.localAllowance) where
  /-- The exact Gaussian point retained for this local differential observation. -/ point :
    Data.Gaussian.Basic.Canonical
  /-- The retained point is the exact point computed by the original cell observation. -/ point_eq : point =
    Cell.Basic.CellModel.observationPoint cell observation
  /-- The coherent nonzero algebraic sheet value above this exact point. -/ sheetValue :
    Sheets.Basic.AlgebraicSheetValue curve point
  /-- The algebraic sheet label is the original lifted cell starting-sheet label. -/ chosenSheet_eq : sheetValue.sheet =
    start.sheet
  /-- The retained process state of the differential value built from this exact sheet certificate. -/ readingState :
    (Value.differentialValue differential point
      sheetValue.value sheetValue.apart).name.process.State
  /-- The observed integrand reading is possible at the retained differential process state. -/ readingPossible :
    (Value.differentialValue differential point
      sheetValue.value sheetValue.apart).name.process.Possible readingState
        observation.integrandReading

constructive_injectivity Purelib.Curves.Hyperelliptic.Integration.Algebraic.Observation.Basis.AlgebraicObservation

set_option genInjectivity false in
/-- Algebraic certificates for every displayed observation of one integration cell. This is useful finite diagnostic
data, but a finite list of samples is not by itself a uniform integration certificate. -/
inductive ObservationCertificates {genus :
  Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential genus)
    {start finish : Lifted.Basic.LiftedPoint 2} (liftedCell : Lifted.Basic.LiftedCell start finish)
    (cell : Cell.Basic.CellModel) :
    List (Cell.Basic.LocalObservation cell.polynomial cell.localAllowance) -> Type 2
  /-- The empty observation list has an empty algebraic certificate family. -/ | nil :
    ObservationCertificates curve differential
    liftedCell cell []
  /-- Prepend the algebraic certificate for the exact head observation to the retained tail certificates. -/ | cons
    {observation : Cell.Basic.LocalObservation cell.polynomial cell.localAllowance}
      {remaining : List
        (Cell.Basic.LocalObservation cell.polynomial cell.localAllowance)}
      (head : AlgebraicObservation curve differential
        liftedCell cell observation)
      (tail : ObservationCertificates curve
        differential liftedCell cell remaining) :
      ObservationCertificates curve differential
        liftedCell cell
        (observation :: remaining)

constructive_injectivity Purelib.Curves.Hyperelliptic.Integration.Algebraic.Observation.Basis.ObservationCertificates

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Observation.Basis

end

section
@[expose] public section

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Observation.Jets

set_option genInjectivity false in
/-- Finite algebraic evidence behind one sampled odd-power differential value. -/
structure AlgebraicObservation {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : OddPower.Basic.OddPowerDifferential)
    {start finish : Lifted.Basic.LiftedPoint 2} (liftedCell : Lifted.Basic.LiftedCell start finish)
    (cell : Cell.Basic.CellModel)
    (observation : Cell.Basic.LocalObservation cell.polynomial cell.localAllowance) where
  /-- The exact Gaussian point retained for this local differential observation. -/ point :
    Data.Gaussian.Basic.Canonical
  /-- The retained point is the exact point computed by the original cell observation. -/ point_eq : point =
    Cell.Basic.CellModel.observationPoint cell observation
  /-- The coherent nonzero algebraic sheet value above this exact point. -/ sheetValue :
    Sheets.Basic.AlgebraicSheetValue curve point
  /-- The algebraic sheet label is the original lifted cell starting-sheet label. -/ chosenSheet_eq : sheetValue.sheet =
    start.sheet
  /-- The retained process state of the differential value built from this exact sheet certificate. -/ readingState :
    (differential.value point sheetValue.value
      sheetValue.apart).name.process.State
  /-- The observed integrand reading is possible at the retained differential process state. -/ readingPossible :
    (differential.value point sheetValue.value
      sheetValue.apart).name.process.Possible readingState
        observation.integrandReading

constructive_injectivity Purelib.Curves.Hyperelliptic.Integration.Algebraic.Observation.Jets.AlgebraicObservation

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Observation.Jets

end
