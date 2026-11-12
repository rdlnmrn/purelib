module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient.Allocation.Rows
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fine
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy

/-! # Actual source-stage acquisition at the six-row work request

The supplied original complete closed centered chain owns this acquisition.
Its original sufficient-stage factory computes a new Target cache and source
preparations after the common work request. Their actual allowances pay
each individual row, before any physical point observation is requested.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient.Allocation

namespace Rows

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.RootContinuation
open Jets.Source.Cell.PreparedParents (StageAttempt)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable {data : (index : Fin 6) →
  Waist.Differential.Bounds.Data site parameter (Jets.Specification.Table.forms parameter index)}
variable (rows : Rows (anchor := anchor) data) (target : AccuracyRequest)
variable {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
variable {parent : CenteredEdge (Fibre.frameCurve frame) basis}
variable {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
variable (covered : CoveredParents count (parent :: parents))
variable (chain : CenteredPathChain (parent :: parents)
  (start := Jets.Source.Cell.PreparedParent.startPoint parent)
  (finish := Jets.Source.Cell.PreparedParent.startPoint parent))

/-- Compute the common row request first, then execute ONE original sufficient-stage closed-source acquisition. -/
def sourceStage (current floor rootStage : Nat) :
    StageAttempt.Requested covered chain current floor rootStage (rows.commonRequest target) :=
  StageAttempt.Requested.build covered chain current floor rootStage (rows.commonRequest target)

variable {rows target covered chain} {current floor rootStage : Nat}
variable (requested : StageAttempt.Requested covered chain current floor rootStage (rows.commonRequest target))

/-- Every SAME actually acquired six-channel source cell pays every individual retained row's common-work request. -/
theorem source_allowance_le (parentIndex : Fin (parent :: parents).length) (index : Fin 6) :
    ((requested.prepared.entry parentIndex).preparation.cell.models.cell index).localAllowance ≤
      (request (rows.get index) target).tolerance :=
  (requested.cell_allowance_lt parentIndex index).le.trans (rows.common_le target index)

variable {budgets : Budgets anchor} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
variable {within : segment.WithinAmbient} {completed : Segment budgets segment within}
variable {time : Fraction.Rational} {inside : FixedRootBoxPath.Inside time}
variable {reading : Segment.Reading completed time inside}

/-- The actual new source model allowance fits the SAME individual Fine cache without reindexing its accuracy. -/
theorem source_allowance_le_fine (parentIndex : Fin (parent :: parents).length) (index : Fin 6)
    (fine : Segment.Reading.Payment.Fine reading (rows.get index) target) :
    ((requested.prepared.entry parentIndex).preparation.cell.models.cell index).localAllowance ≤ fine.work.tolerance :=
  (source_allowance_le requested parentIndex index).trans_eq
    (congrArg AccuracyRequest.tolerance fine.work_eq).symm

end Rows

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient.Allocation

end
