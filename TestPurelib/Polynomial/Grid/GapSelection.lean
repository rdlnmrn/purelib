module
import all Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Elimination.Axis.Gap
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider

open Purelib
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (VerticalLine HorizontalLine)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Polynomial.Elimination.Axis
open Purelib.Data

/- This optional verifier reduces Extension.gapPoint's private producer body
   to compare the complete former two-line constructor. Production clients
   consume its opaque readbacks and actual retained paired payloads. -/
namespace TestPurelib.Polynomial.Grid.GapSelection

variable {polynomial : GaussianPolynomial} {ambient : Box}

/-- The complete former two-line constructor, retained only for quantified kernel comparison. -/
private def formerGapLines {degreeBound : Nat}
    (elimination : AxisEliminationCertificate polynomial degreeBound)
    (clearances : AxisClearances elimination) (inner : Box) (proper : inner.Proper)
    (refines : inner.Refines ambient) : VerticalLine polynomial ambient × HorizontalLine polynomial ambient :=
  let vertical := Gap.verticalGapCoordinate elimination proper.1
  have verticalSpec := Gap.verticalGapCoordinate_spec elimination proper.1
  let horizontal := Gap.horizontalGapCoordinate elimination proper.2
  have horizontalSpec := Gap.horizontalGapCoordinate_spec elimination proper.2
  (⟨vertical, ⟨refines.1.trans verticalSpec.2.1.le, verticalSpec.2.2.le.trans refines.2.1⟩,
      clearances.vertical ambient vertical verticalSpec.1⟩,
    ⟨horizontal, ⟨refines.2.2.1.trans horizontalSpec.2.1.le, horizontalSpec.2.2.le.trans refines.2.2.2⟩,
      clearances.horizontal ambient horizontal horizontalSpec.1⟩)

/-- Factoring the original point scans preserves the complete paired line payloads. -/
private theorem gapLines_eq_former {degreeBound : Nat}
    (elimination : AxisEliminationCertificate polynomial degreeBound)
    (clearances : AxisClearances elimination) (inner : Box) (proper : inner.Proper)
    (refines : inner.Refines ambient) :
    Purelib.Polynomial.Geometry.Grid.Extension.gapLines elimination clearances inner proper refines =
      formerGapLines elimination clearances inner proper refines := (rfl)

end TestPurelib.Polynomial.Grid.GapSelection
