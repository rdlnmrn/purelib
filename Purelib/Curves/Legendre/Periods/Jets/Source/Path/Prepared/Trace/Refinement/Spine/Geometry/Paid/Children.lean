module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Paid.Rows
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Chain

/-! # Paid rows allocated on their actual retained global child chain

The child chain is assembled from the given geometry before the original
request prefix chooses Targets. The existing shared-bank paid producer
then uses that very path as its allocation source. Its genuine old
root-return evidence and three independent old Spines are unchanged.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry.Paid

namespace Rows

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner)
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count floor : Nat} {sheet : Fin 2} {ambient : Purelib.Geometry.Rational.Box}
variable {grid : ClearGrid (Paths.polynomial parameter) ambient} {base : Canonical}
variable {owner : Owner ((Paths.polynomial parameter).eval base)} (closed : RootClosedWalk grid base owner)
variable {diameter : Rational} {positive : 0 < diameter}
variable {inputCenters : Centers (frame := frame) (basis := basis) (sheet := sheet) closed.traced.lineage}
variable {materialized : OwnerPath (Paths.polynomial parameter) base owner base
  (PreparedPathGluing.finishOwner closed.traced.prepared)}
variable {factory : materialized = closed.traced.lineage.ownerPath}

/-- Allocate Targets on the SAME actual child path before preparing its ONE bank and observing all three old rows.

The supplied continuation retains that exact chain and its whole factory.
Its path indexes the existing paid-row construction directly, so neither
a guessed cell count nor a wanted path equality transports the Targets.
The geometric closed endpoint pair does not replace the original retained
RootClosedWalk return comparison used by the actual paid producer.
-/
def withChildren
    (retained : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (target : AccuracyRequest) (stageFloor : Nat) {Result : Type u}
    (consume :
      (childChain : {value : CenteredPathChain retained.parents
          (start := (⟨base, sheet⟩ : LiftedPoint 2)) (finish := (⟨base, sheet⟩ : LiftedPoint 2)) //
        value = retained.chain}) →
      Rows (floor := floor) closed retained childChain.val.path target stageFloor → Result) : Result :=
  let childChain : {value : CenteredPathChain retained.parents
      (start := (⟨base, sheet⟩ : LiftedPoint 2)) (finish := (⟨base, sheet⟩ : LiftedPoint 2)) //
    value = retained.chain} := ⟨retained.chain, rfl⟩
  let paid := build (floor := floor) closed retained childChain.val.path target stageFloor
  consume childChain paid

end Rows

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry.Paid

end
