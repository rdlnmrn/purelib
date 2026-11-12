module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Chain
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table

/-! # Adaptive progressive programmes from one original whole source-bank rule

The fixed retained geometry and actual closed child chain are given before
programme precision. Each supplied bank belongs to its exact actual Targets.
The existing preparation projection and uniform certifier consume that same
bank, and literal model readbacks identify the resulting progressive samples.
Independent callback invocations are not claimed to share execution.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathTrace.PreparedPath (TraceLineage)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count floor : Nat} {sheet : Fin 2} {ambient : Purelib.Geometry.Rational.Box}
variable {point : Canonical} {clearPath : ClearPath (Paths.polynomial parameter) ambient point point}
variable {owner : Owner ((Paths.polynomial parameter).eval point)} {prepared : PreparedPath clearPath owner}
variable {lineage : TraceLineage prepared}
variable {inputCenters : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage}
variable {materialized : OwnerPath (Paths.polynomial parameter) point owner point
  (PreparedPathGluing.finishOwner prepared)} {factory : materialized = lineage.ownerPath}
variable {diameter : Rational} {positive : 0 < diameter}
variable (retained : Materialized.Geometry (count := count)
  diameter positive lineage inputCenters materialized factory)

namespace Geometry.Sources

variable (childChain : CenteredPathChain retained.parents
    (start := (⟨point, sheet⟩ : LiftedPoint 2)) (finish := (⟨point, sheet⟩ : LiftedPoint 2)))
variable (precision : Nat → Nat)
variable (requested : (index : Nat) → { value : CellEndpoints.Targets childChain.path (precision index) //
  value = CellEndpoints.Targets.build childChain.path (precision index) })
variable (sourceBanks : (index : Nat) → Sources (count := count) (floor := floor)
  (original := childChain.path) (stage := precision index) (targets := (requested index).val) retained)

/-- Certify the SAME actual whole-bank rule on the supplied fixed cycle using its selected precision at each index.

The source producer is an input. This operation reads its original prepared
product and uses the shared intrinsic progressive worker; it constructs no
second six-channel source bank and accepts no desired model equality.
-/
def certifiedAtPrecision (precisionFloor : ∀ index, index ≤ precision index) (channel : Fin 6) :
    CertifiedPeriodProgram (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
      (PreparedParents.constantCycle childChain) :=
  PreparedParents.certifiedAtPrecision (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) retained.covered childChain precision requested
    (fun index => preparations (count := count) (floor := floor) (original := childChain.path)
      (stage := precision index) (targets := (requested index).val) retained (sourceBanks index))
    precisionFloor channel

/-- The actual progressive model equals the literal model read from the SAME supplied whole bank at that index. -/
theorem certifiedAtPrecision_model (precisionFloor : ∀ index, index ≤ precision index)
    (channel : Fin 6) (index : Nat) :
    ((certifiedAtPrecision retained childChain precision requested sourceBanks precisionFloor channel).integral.model
      index) = model (count := count) (floor := floor) (original := childChain.path)
        (stage := precision index) (targets := (requested index).val) retained (sourceBanks index) channel := by
  unfold certifiedAtPrecision
  have original := PreparedParents.certifiedAtPrecision_model (parameter := parameter) (frame := frame)
    (basis := basis) (count := count) (floor := floor) retained.covered childChain precision requested
    (fun index => preparations (count := count) (floor := floor) (original := childChain.path)
      (stage := precision index) (targets := (requested index).val) retained (sourceBanks index))
    precisionFloor channel index
  exact original.trans (model_eq_sources (count := count) (floor := floor) (original := childChain.path)
    (stage := precision index) (targets := (requested index).val) retained (sourceBanks index) childChain channel).symm

/-- The six progressive cell lists retain every original whole-bank occurrence and its literal order. -/
theorem certifiedAtPrecision_cells (precisionFloor : ∀ index, index ≤ precision index)
    (channel : Fin 6) (index : Nat) :
    ((certifiedAtPrecision retained childChain precision requested sourceBanks precisionFloor channel).integral.model
      index).cells = cells (count := count) (floor := floor) (original := childChain.path)
        (stage := precision index) (targets := (requested index).val) retained (sourceBanks index) channel :=
  congrArg (fun value : PathModel => value.cells)
    (certifiedAtPrecision_model retained childChain precision requested sourceBanks precisionFloor channel index)

end Geometry.Sources

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

end
