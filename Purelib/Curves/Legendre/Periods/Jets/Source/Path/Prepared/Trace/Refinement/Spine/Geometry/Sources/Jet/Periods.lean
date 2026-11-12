module

public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Jet.Comparison
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Subedges
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Primitive.Subedges
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Subedges
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

/-! # The same actual child-bank value model and its original ordered period

The retained canonical-center factory supplies rooted refinement from the
original period walk to the actual child geometry. The given whole jet
factory supplies its identical value-zero model list. Their operational
comparison reuses the actual source-bank rule and original ordered period;
no source, occurrence, geometry, period bank or programme is reconstructed.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk (PolynomialValues)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Approximation.Gaussian.Equivalence (Equivalent)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count floor : Nat} {ambient : Purelib.Geometry.Rational.Box}
    {grid : ClearGrid (Paths.polynomial parameter) ambient} {base : Canonical}
    (owner : Owner ((Paths.polynomial parameter).eval base))
    (period : PeriodWalk (curve := Fibre.frameCurve frame) grid base owner basis)
    {inputCenters : Centers (frame := frame) (basis := basis) (sheet := 0) period.closed.traced.lineage}
    {materialized : OwnerPath (Paths.polynomial parameter) base owner base
      (PreparedPathGluing.finishOwner period.closed.traced.prepared)}
    {factory : materialized = period.closed.traced.lineage.ownerPath} {diameter : Rational} {positive : 0 < diameter}
    (retained : Materialized.Geometry (count := count)
      diameter positive period.closed.traced.lineage inputCenters materialized factory)
    (childChain : CenteredPathChain retained.parents
      (start := (⟨base, 0⟩ : LiftedPoint 2)) (finish := (⟨base, 0⟩ : LiftedPoint 2)))

namespace Geometry.Sources

variable (precision : Nat → Nat)
    (requested : (index : Nat) → { value : CellEndpoints.Targets childChain.path (precision index) //
      value = CellEndpoints.Targets.build childChain.path (precision index) })
    (sourceBanks : (index : Nat) → Sources (count := count) (floor := floor)
      (original := childChain.path) (stage := precision index) (targets := (requested index).val) retained)
    {rootStage : Nat} {walkPositive : 0 < period.closed.walk.edgeCount}
    (completed : (index : Nat) → Occurrences (count := count) (floor := floor)
      owner period.closed retained childChain (precision index) rootStage (requested index).val
        (requested index).property (sourceBanks index) walkPositive)

/-- Compare the actual adaptive jet's value-zero MODEL samples with its SAME original ordered period samples.

The center equality is the original acquisition's whole canonical-center
factory. The whole jet factory retains the actual source, occurrence and
six-channel caches. The resulting executable selector keeps independent
source and period indices and pays every later pair before readings. This
ordinary dx/y comparison applies to either the original A walk or its full
corrected-B walk; the x dx/y channel is a different differential.
-/
def valueZero_periodEquivalent (canonical : inputCenters = Centers.build period.closed.traced.lineage)
    (precisionPaid : ∀ index, index ≤ precision index)
    (actual : SynchronizedPeriodJet frame)
    (actualFactory : actual =
      jet owner period.closed retained childChain precision requested sourceBanks completed precisionPaid) :
    Equivalent (actual.programme 0).approximation (period.program 0).integral.approximation :=
  let original := period.subedgeSourcePeriodEquivalent
    (parameter := parameter) (frame := frame)
    (retained.periodSubedges owner period canonical) retained.covered childChain precision precisionPaid requested
    (fun index => preparations (count := count) (floor := floor) (original := childChain.path)
      (stage := precision index) (targets := (requested index).val) retained (sourceBanks index))
  original.withSamples (actual.programme 0).approximation (period.program 0).integral.approximation
    (fun index =>
      ((actual.programme 0).certifiedView_sample index).trans
        ((congrArg PathModel.integralSample
          (jet_programme_model owner period.closed retained childChain precision requested sourceBanks completed
            precisionPaid actual actualFactory 0 index)).trans
          (congrArg PathModel.integralSample
            (PreparedParents.certifiedAtPrecision_model retained.covered childChain precision requested
              (fun selected => preparations (count := count) (floor := floor) (original := childChain.path)
                (stage := precision selected) (targets := (requested selected).val) retained (sourceBanks selected))
              precisionPaid 0 index)).symm))
    (fun index => (period.program 0).integral.certifiedView_sample index)

/-- Compare the GIVEN adaptive jet's value-one MODEL stream with the SAME retained x dx/y polynomial programme.

The supplied PolynomialValues retains its original initial closed path,
coordinate numerator, full request/model/primitive caches and programme.
The actual center factory derives rooted refinement; the whole jet factory
identifies its literal child models. No source, jet, polynomial programme,
geometry, root chain or period bank is constructed again.
-/
def valueOne_periodEquivalent {polynomialFloor : Nat} (values : PolynomialValues period polynomialFloor)
    (canonical : inputCenters = Centers.build period.closed.traced.lineage)
    (precisionPaid : ∀ index, index ≤ precision index)
    (actual : SynchronizedPeriodJet frame)
    (actualFactory : actual =
      jet owner period.closed retained childChain precision requested sourceBanks completed precisionPaid) :
    Equivalent (actual.programme 1).approximation values.2.2.1.2.val.integral.approximation :=
  let original := values.1.subedgeSourceEquivalent (parameter := parameter) (frame := frame)
    values.2.2.1 (retained.periodSubedges owner period canonical) retained.covered childChain
    precision precisionPaid requested
    (fun index => preparations (count := count) (floor := floor) (original := childChain.path)
      (stage := precision index) (targets := (requested index).val) retained (sourceBanks index))
  original.withSamples (actual.programme 1).approximation values.2.2.1.2.val.integral.approximation
    (fun index =>
      ((actual.programme 1).certifiedView_sample index).trans
        ((congrArg PathModel.integralSample
          (jet_programme_model owner period.closed retained childChain precision requested sourceBanks completed
            precisionPaid actual actualFactory 1 index)).trans
          (congrArg PathModel.integralSample
            (PreparedParents.certifiedAtPrecision_model retained.covered childChain precision requested
              (fun selected => preparations (count := count) (floor := floor) (original := childChain.path)
                (stage := precision selected) (targets := (requested selected).val) retained (sourceBanks selected))
              precisionPaid 1 index)).symm))
    (fun index => values.2.2.1.2.val.integral.certifiedView_sample index)

end Geometry.Sources

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

end
