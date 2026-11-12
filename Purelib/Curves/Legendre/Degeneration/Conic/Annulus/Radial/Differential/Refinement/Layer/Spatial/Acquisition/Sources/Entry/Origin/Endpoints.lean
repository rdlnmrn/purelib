module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial.Acquisition.Sources.Entry.Origin
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Block.Sources.Endpoints
import Purelib.Data.Fin
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Curves.Legendre.Periods.Fibre

/-! # Physical endpoint occurrence of the SAME retained fine Origin

The actual Origin keeps its full original Piece, Block, physical Sources
and SourceOccurrence. Exact parent transport changes only the public
centered-parent index; every original runtime cache remains unchanged.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

namespace Spatial.Acquisition.Sources.Entry

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Transport.Spatial
open Transport.Spatial.Parallel
open Transport.Spatial.Factors.Segment.Reading.Payment (widthRequest)

variable {radicand : CoefficientPolynomial}
variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}
variable {regular : parameter ≠ criticalValue site}
variable {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage}

namespace Origin

variable {pieces : List (Piece data actual accuracy)} {parent : CenteredEdge (Fibre.frameCurve frame) basis}

variable (retained : Origin (regular := regular) (frame := frame) (basis := basis) (count := count)
  (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) pieces parent)

/-- Read the actual physical endpoint occurrence from the SAME fine Origin and its already cached source position.

No Entry.origin, sourceOccurrence, locator or producer is called. The
complete original occurrence and its earlier-corner Reading/Samples stay
retained; its whole-parent incidence supplies the only index transport.
-/
@[expose] def physicalOccurrence : Spine.Sources.ParentOccurrence
    (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
    (targets := sourceTargets) parent :=
  retained.occurrence.physicalOccurrence.castParent retained.parent_eq

/-- The occurrence view is precisely the original cached source view under its exact whole-parent transport. -/
theorem physicalOccurrence_heq :
    HEq retained.physicalOccurrence retained.occurrence.physicalOccurrence :=
  retained.occurrence.physicalOccurrence.castParent_heq retained.parent_eq

end Origin

end Spatial.Acquisition.Sources.Entry

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

end
