module

public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Jet
public import Purelib.Curves.Legendre.Periods.Jets.Programs
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs.Comparison
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

/-! # Six actual child-bank model streams compared on their retained cycle

The GIVEN whole synchronized-jet factory identifies each actual programme.
Independent reference preparation caches remain on the SAME covered chain,
at their own actual precisions and construction floor. The original model
comparison consumes both banks; no occurrence factory is identified with a
different jet constructor and no output name is resampled.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (Equivalent)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner ownerName)
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count floor : Nat} {sheet : Fin 2} {ambient : Purelib.Geometry.Rational.Box}
variable {grid : ClearGrid (Paths.polynomial parameter) ambient} {base : Canonical}
variable (owner : Owner ((Paths.polynomial parameter).eval base)) (closed : RootClosedWalk grid base owner)
variable {inputCenters : Centers (frame := frame) (basis := basis) (sheet := sheet) closed.traced.lineage}
variable {materialized : OwnerPath (Paths.polynomial parameter) base owner base
  (PreparedPathGluing.finishOwner closed.traced.prepared)}
variable {factory : materialized = closed.traced.lineage.ownerPath} {diameter : Rational} {positive : 0 < diameter}
variable (retained : Materialized.Geometry (count := count)
  diameter positive closed.traced.lineage inputCenters materialized factory)
variable (childChain : CenteredPathChain retained.parents (start := (⟨base, sheet⟩ : LiftedPoint 2))
  (finish := (⟨base, sheet⟩ : LiftedPoint 2)))

namespace Geometry.Sources

variable (precision : Nat → Nat)
variable (requested : (index : Nat) → { value : CellEndpoints.Targets childChain.path (precision index) //
  value = CellEndpoints.Targets.build childChain.path (precision index) })
variable (sourceBanks : (index : Nat) → Sources (count := count) (floor := floor)
  (original := childChain.path) (stage := precision index) (targets := (requested index).val) retained)
variable {rootStage : Nat} {walkPositive : 0 < closed.walk.edgeCount}
variable (completed : (index : Nat) → Occurrences (count := count) (floor := floor)
  owner closed retained childChain (precision index) rootStage
    (requested index).val (requested index).property (sourceBanks index) walkPositive)

/-- Every channel of the GIVEN child-bank jet is its identical original adaptive certified programme. -/
theorem jet_programme_integral (precisionPaid : ∀ index, index ≤ precision index)
    (actual : SynchronizedPeriodJet frame)
    (actualFactory : actual =
      jet owner closed retained childChain precision requested sourceBanks completed precisionPaid)
    (channel : Fin 6) :
    actual.programme channel =
      (certifiedAtPrecision retained childChain precision requested sourceBanks precisionPaid channel).integral := by
  have original :
      (jet owner closed retained childChain precision requested sourceBanks completed precisionPaid).programme channel =
        (certifiedAtPrecision retained childChain precision requested sourceBanks precisionPaid channel).integral := by
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_
      (fun c => Fin.cases ?_ (fun d => Fin.cases ?_ (fun e => Fin.cases ?_
        (fun empty => Fin.elim0 empty) e) d) c) b) a) channel
    · exact jet_value_integral owner closed retained childChain precision requested sourceBanks completed
        precisionPaid 0
    · exact jet_value_integral owner closed retained childChain precision requested sourceBanks completed
        precisionPaid 1
    · exact jet_first_integral owner closed retained childChain precision requested sourceBanks completed
        precisionPaid 0
    · exact jet_first_integral owner closed retained childChain precision requested sourceBanks completed
        precisionPaid 1
    · exact jet_second_integral owner closed retained childChain precision requested sourceBanks completed
        precisionPaid 0
    · exact jet_second_integral owner closed retained childChain precision requested sourceBanks completed
        precisionPaid 1
  exact (congrArg (fun value : SynchronizedPeriodJet frame => value.programme channel) actualFactory).trans original

/-- Read the SAME literal preparation-list model through the GIVEN actual child-bank jet factory. -/
theorem jet_programme_model (precisionPaid : ∀ index, index ≤ precision index)
    (actual : SynchronizedPeriodJet frame)
    (actualFactory : actual =
      jet owner closed retained childChain precision requested sourceBanks completed precisionPaid)
    (channel : Fin 6) (index : Nat) :
    (actual.programme channel).model index =
      PreparedParents.modelAtPrecision retained.covered childChain precision requested
        (fun selected => preparations (count := count) (floor := floor) (original := childChain.path)
          (stage := precision selected) (targets := (requested selected).val) retained (sourceBanks selected))
        channel index := by
  have stored := congrArg (fun programme : RefinementProgram => programme.model index)
    (jet_programme_integral owner closed retained childChain precision requested sourceBanks completed
      precisionPaid actual actualFactory channel)
  exact stored.trans ((certifiedAtPrecision_model retained childChain precision requested sourceBanks
    precisionPaid channel index).trans (model_eq_sources retained (sourceBanks index) childChain channel))

/-- Compare all six GIVEN actual child-bank model streams with independent original preparations on that SAME chain.

Both complete preparation rules precede the numerical comparison target.
The operation returns the original executable Equivalent selector for each
channel. Its retained indices are MODEL stages; no output-name schedule is
used as a substitute, and no source or occurrence producer is executed here.
-/
def jet_programmes_equivalent (precisionPaid : ∀ index, index ≤ precision index)
    (actual : SynchronizedPeriodJet frame)
    (actualFactory : actual =
      jet owner closed retained childChain precision requested sourceBanks completed precisionPaid)
    {referenceFloor : Nat} (referencePrecision : Nat → Nat)
    (referenceRequests : (index : Nat) → {value : CellEndpoints.Targets childChain.path (referencePrecision index) //
      value = CellEndpoints.Targets.build childChain.path (referencePrecision index)})
    (referencePrepared : (index : Nat) → PreparedParents retained.covered referenceFloor (referenceRequests index).val)
    (referencePaid : ∀ index, index ≤ referencePrecision index) (channel : Fin 6) :
    Equivalent (actual.programme channel).approximation
      (PreparedParents.programAtPrecision retained.covered childChain referencePrecision referenceRequests
        referencePrepared referencePaid channel).approximation :=
  let original := PreparedParents.programsAtPrecision_equivalent
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    retained.covered childChain precision referencePrecision requested referenceRequests
    (fun selected => preparations (count := count) (floor := floor) (original := childChain.path)
      (stage := precision selected) (targets := (requested selected).val) retained (sourceBanks selected))
    referencePrepared precisionPaid referencePaid channel
  original.withSamples (actual.programme channel).approximation
    (PreparedParents.programAtPrecision retained.covered childChain referencePrecision referenceRequests
      referencePrepared referencePaid channel).approximation
    (fun index =>
      ((actual.programme channel).certifiedView_sample index).trans
        ((congrArg PathModel.integralSample
          (jet_programme_model owner closed retained childChain precision requested sourceBanks completed
            precisionPaid actual actualFactory channel index)).trans
          ((congrArg PathModel.integralSample
            (PreparedParents.programAtPrecision_model retained.covered childChain precision requested
              (fun selected => preparations (count := count) (floor := floor) (original := childChain.path)
                (stage := precision selected) (targets := (requested selected).val) retained (sourceBanks selected))
              precisionPaid channel index)).symm.trans
            ((PreparedParents.programAtPrecision retained.covered childChain precision requested
              (fun selected => preparations (count := count) (floor := floor) (original := childChain.path)
                (stage := precision selected) (targets := (requested selected).val) retained (sourceBanks selected))
              precisionPaid channel).certifiedView_sample index).symm)))
    (fun _index => rfl)

end Geometry.Sources

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

end
