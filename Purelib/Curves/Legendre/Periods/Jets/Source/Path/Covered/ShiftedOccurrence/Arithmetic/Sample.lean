module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Sample.Query
import Purelib.Approximation.Gaussian.Provenance.Power
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Joint.Reobservation
import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Reobservation.Rows
import Purelib.Data.Vector.Basic
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Transport
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table

/-! # Factory and scalar readbacks for retained occurrence samples

The query construction retains both original observations, their spatial bank
and comparisons. These laws identify the same factories and scalar certificates.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrence

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets
open Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step.Joint (Spatial)
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation (ArithmeticComparison)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint liftedCell)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Acquisition.Segment
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.RootContinuation

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (firstParent :: remaining)}
    {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
    {requestIndex globalFloor rootStage : Nat}
    {request : Request whole requestIndex globalFloor rootStage}
    {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}

variable (located : Occurrence blocks request sourceIndex)
    (aligned : RootComparisons.Alignment
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference)
    (nonzero : increment ≠ 0) (spatial : AccuracyRequest)

namespace Sample

variable {located aligned nonzero spatial} {time : { input : Rational // Primitive.unitInterval.Contains input }}
    (answer : Sample located aligned nonzero spatial time)

/-- The original old query remains the complete actual source factory answer at that mapped physical time. -/
private theorem old_factory_proof : answer.old = located.sourceStep time.val time.property := answer.1.1.property

/-- Every retained old query equals its original mapped-time source factory. -/
@[expose] def OldFactoryLaw : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
        {target : Paths.Frame (parameter + increment)} {count : Nat}
        {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
        {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
        {covered : CoveredParents count (firstParent :: remaining)}
        {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
        {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
        {targets : CellEndpoints.Targets original stage}
        {prepared : PreparedParents covered floor targets}
        {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
        {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
        {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
        {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
        {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
          ShiftedGeometry (target := target) (basis := basis) (count := count)
            (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
        {requestIndex globalFloor rootStage : Nat}
        {request : Request whole requestIndex globalFloor rootStage}
        {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    {located : Occurrence blocks request sourceIndex}
    {aligned : RootComparisons.Alignment
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference}
    {nonzero : increment ≠ 0}
    {spatial : AccuracyRequest}
    {time : { input : Rational // Primitive.unitInterval.Contains input }}
    (answer : Sample located aligned nonzero spatial time),
    answer.old = located.sourceStep time.val time.property

/-- The original old query remains the complete actual source factory answer at that mapped physical time. -/
theorem old_eq : OldFactoryLaw := @old_factory_proof

/-- The independent target bundle remains its complete original actual source-query factory answer. -/
private theorem fresh_factory_proof :
    answer.fresh = (request.attempt.2.1.entry sourceIndex).preparation.query.observe target
    time.val time.property.1 time.property.2 := answer.2.1.1.property

/-- Every retained target bundle equals its original globally allocated query factory. -/
@[expose] def FreshFactoryLaw : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
        {target : Paths.Frame (parameter + increment)} {count : Nat}
        {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
        {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
        {covered : CoveredParents count (firstParent :: remaining)}
        {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
        {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
        {targets : CellEndpoints.Targets original stage}
        {prepared : PreparedParents covered floor targets}
        {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
        {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
        {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
        {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
        {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
          ShiftedGeometry (target := target) (basis := basis) (count := count)
            (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
        {requestIndex globalFloor rootStage : Nat}
        {request : Request whole requestIndex globalFloor rootStage}
        {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    {located : Occurrence blocks request sourceIndex}
    {aligned : RootComparisons.Alignment
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference}
    {nonzero : increment ≠ 0}
    {spatial : AccuracyRequest}
    {time : { input : Rational // Primitive.unitInterval.Contains input }}
    (answer : Sample located aligned nonzero spatial time),
    answer.fresh = (request.attempt.2.1.entry sourceIndex).preparation.query.observe target
        time.val time.property.1 time.property.2

/-- The independent target bundle remains its complete original actual source-query factory answer. -/
theorem fresh_eq : FreshFactoryLaw := @fresh_factory_proof

/-- The complete stored spatial bank is the original factory on the actual old Step and request. -/
private theorem spatialBank_factory_proof : answer.spatialBank.val =
    Point.Step.Joint.buildSpatial answer.old.2 nonzero spatial := answer.spatialBank.cache_eq

/-- Every stored spatial bank equals its factory at the retained old Step and request. -/
@[expose] def SpatialBankFactoryLaw : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
        {target : Paths.Frame (parameter + increment)} {count : Nat}
        {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
        {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
        {covered : CoveredParents count (firstParent :: remaining)}
        {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
        {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
        {targets : CellEndpoints.Targets original stage}
        {prepared : PreparedParents covered floor targets}
        {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
        {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
        {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
        {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
        {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
          ShiftedGeometry (target := target) (basis := basis) (count := count)
            (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
        {requestIndex globalFloor rootStage : Nat}
        {request : Request whole requestIndex globalFloor rootStage}
        {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    {located : Occurrence blocks request sourceIndex}
    {aligned : RootComparisons.Alignment
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference}
    {nonzero : increment ≠ 0}
    {spatial : AccuracyRequest}
    {time : { input : Rational // Primitive.unitInterval.Contains input }}
    (answer : Sample located aligned nonzero spatial time),
    answer.spatialBank.val =
        Point.Step.Joint.buildSpatial answer.old.2 nonzero spatial

/-- The complete stored spatial bank is the original factory on the actual old Step and request. -/
theorem spatialBank_eq : SpatialBankFactoryLaw := @spatialBank_factory_proof

/-- The same original Joint cache retains its entire old-Step and two-request factory identity. -/
private theorem joint_factory_proof :
    answer.joint = Point.Step.Joint.build answer.old.2 nonzero spatial spatial :=
  answer.spatialBank.joint_eq

/-- Every retained Joint equals its factory at the original Step and spatial requests. -/
@[expose] def JointFactoryLaw : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
        {target : Paths.Frame (parameter + increment)} {count : Nat}
        {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
        {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
        {covered : CoveredParents count (firstParent :: remaining)}
        {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
        {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
        {targets : CellEndpoints.Targets original stage}
        {prepared : PreparedParents covered floor targets}
        {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
        {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
        {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
        {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
        {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
          ShiftedGeometry (target := target) (basis := basis) (count := count)
            (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
        {requestIndex globalFloor rootStage : Nat}
        {request : Request whole requestIndex globalFloor rootStage}
        {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    {located : Occurrence blocks request sourceIndex}
    {aligned : RootComparisons.Alignment
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference}
    {nonzero : increment ≠ 0}
    {spatial : AccuracyRequest}
    {time : { input : Rational // Primitive.unitInterval.Contains input }}
    (answer : Sample located aligned nonzero spatial time),
    answer.joint = Point.Step.Joint.build answer.old.2 nonzero spatial spatial

/-- The same original Joint cache retains its entire old-Step and two-request factory identity. -/
theorem joint_eq : JointFactoryLaw := @joint_factory_proof

/-- The independent evaluator cache retains its entire original same-Joint reobservation factory. -/
private theorem paid_factory_proof : answer.paid = answer.joint.reobserve spatial := answer.spatialBank.paid_eq

/-- Every retained evaluator bank equals the reobservation of the same stored Joint. -/
@[expose] def PaidFactoryLaw : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
        {target : Paths.Frame (parameter + increment)} {count : Nat}
        {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
        {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
        {covered : CoveredParents count (firstParent :: remaining)}
        {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
        {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
        {targets : CellEndpoints.Targets original stage}
        {prepared : PreparedParents covered floor targets}
        {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
        {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
        {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
        {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
        {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
          ShiftedGeometry (target := target) (basis := basis) (count := count)
            (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
        {requestIndex globalFloor rootStage : Nat}
        {request : Request whole requestIndex globalFloor rootStage}
        {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    {located : Occurrence blocks request sourceIndex}
    {aligned : RootComparisons.Alignment
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference}
    {nonzero : increment ≠ 0}
    {spatial : AccuracyRequest}
    {time : { input : Rational // Primitive.unitInterval.Contains input }}
    (answer : Sample located aligned nonzero spatial time),
    answer.paid = answer.joint.reobserve spatial

/-- The independent evaluator cache retains its entire original same-Joint reobservation factory. -/
theorem paid_eq : PaidFactoryLaw := @paid_factory_proof

/-- The same direct child query retains its original whole factory on the actual edge and time. -/
private theorem direct_factory_proof :
    answer.direct = PreparedEdge.Query.build _ time.val time.property := answer.2.1.2.property

/-- Every retained direct child query equals its original factory at the bounded time. -/
@[expose] def DirectFactoryLaw : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
        {target : Paths.Frame (parameter + increment)} {count : Nat}
        {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
        {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
        {covered : CoveredParents count (firstParent :: remaining)}
        {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
        {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
        {targets : CellEndpoints.Targets original stage}
        {prepared : PreparedParents covered floor targets}
        {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
        {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
        {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
        {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
        {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
          ShiftedGeometry (target := target) (basis := basis) (count := count)
            (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
        {requestIndex globalFloor rootStage : Nat}
        {request : Request whole requestIndex globalFloor rootStage}
        {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    {located : Occurrence blocks request sourceIndex}
    {aligned : RootComparisons.Alignment
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference}
    {nonzero : increment ≠ 0}
    {spatial : AccuracyRequest}
    {time : { input : Rational // Primitive.unitInterval.Contains input }}
    (answer : Sample located aligned nonzero spatial time),
    answer.direct = PreparedEdge.Query.build _ time.val time.property

/-- The same direct child query retains its original whole factory on the actual edge and time. -/
theorem direct_eq : DirectFactoryLaw := @direct_factory_proof

/-- The ten retained comparisons preserve their whole original factory and all supplied old/new caches. -/
private theorem comparisons_factory_proof : answer.comparisons = comparisonBank
    (located := located) (input := time.val) (inside := time.property)
    (oldObserved := answer.old.1)
    (old_eq := (congrArg (fun retained => retained.1) answer.old_eq).trans
      (located.sourceStep_observation time.val time.property))
    (step := answer.old.2) (nonzero := nonzero) (joint := answer.joint) (paid := answer.paid)
    (newObserved := answer.fresh) (new_eq := answer.fresh_eq) (aligned := aligned) (direct := answer.direct) :=
  answer.2.2.property

/-- Every ten-comparison bank equals its factory on the same queries and spatial cache. -/
@[expose] def ComparisonsFactoryLaw : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
        {target : Paths.Frame (parameter + increment)} {count : Nat}
        {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
        {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
        {covered : CoveredParents count (firstParent :: remaining)}
        {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
        {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
        {targets : CellEndpoints.Targets original stage}
        {prepared : PreparedParents covered floor targets}
        {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
        {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
        {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
        {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
        {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
          ShiftedGeometry (target := target) (basis := basis) (count := count)
            (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
        {requestIndex globalFloor rootStage : Nat}
        {request : Request whole requestIndex globalFloor rootStage}
        {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    {located : Occurrence blocks request sourceIndex}
    {aligned : RootComparisons.Alignment
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference}
    {nonzero : increment ≠ 0}
    {spatial : AccuracyRequest}
    {time : { input : Rational // Primitive.unitInterval.Contains input }}
    (answer : Sample located aligned nonzero spatial time),
    answer.comparisons = comparisonBank
        (located := located) (input := time.val) (inside := time.property)
        (oldObserved := answer.old.1)
        (old_eq := (congrArg (fun retained => retained.1) answer.old_eq).trans
          (located.sourceStep_observation time.val time.property))
        (step := answer.old.2) (nonzero := nonzero) (joint := answer.joint) (paid := answer.paid)
        (newObserved := answer.fresh) (new_eq := answer.fresh_eq) (aligned := aligned) (direct := answer.direct)

/-- The ten retained comparisons preserve their whole original factory and all supplied old/new caches. -/
theorem comparisons_eq : ComparisonsFactoryLaw := @comparisons_factory_proof

/-- Read all four original numeric certificates from the SAME stored independently paid evaluator bank. -/
@[expose] def certificates : Data.Vector (Data.Vector (Quadratic.Basic.Certificate increment) 2) 2 :=
  answer.1.2.2.val

/-- The complete stored four-certificate bank retains its actual original factory without reconstruction. -/
private theorem certificates_factory_proof : answer.certificates = answer.paid.rowCertificates := answer.1.2.2.property

/-- Every retained certificate table equals the same paid evaluator's row-certificate table. -/
@[expose] def CertificatesFactoryLaw : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
        {target : Paths.Frame (parameter + increment)} {count : Nat}
        {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
        {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
        {covered : CoveredParents count (firstParent :: remaining)}
        {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
        {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
        {targets : CellEndpoints.Targets original stage}
        {prepared : PreparedParents covered floor targets}
        {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
        {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
        {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
        {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
        {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
          ShiftedGeometry (target := target) (basis := basis) (count := count)
            (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
        {requestIndex globalFloor rootStage : Nat}
        {request : Request whole requestIndex globalFloor rootStage}
        {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    {located : Occurrence blocks request sourceIndex}
    {aligned : RootComparisons.Alignment
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference}
    {nonzero : increment ≠ 0}
    {spatial : AccuracyRequest}
    {time : { input : Rational // Primitive.unitInterval.Contains input }}
    (answer : Sample located aligned nonzero spatial time),
    answer.certificates = answer.paid.rowCertificates

/-- The complete stored four-certificate bank retains its actual original factory without reconstruction. -/
theorem certificates_eq : CertificatesFactoryLaw := @certificates_factory_proof

/-- Select the SAME stored original numeric certificate for one adjacent row and differential coordinate. -/
@[expose] def certificate (order coordinate : Fin 2) : Quadratic.Basic.Certificate increment :=
  answer.certificates order coordinate

/-- The selected stored certificate retains its original actual new-bank factory at that SAME row. -/
private theorem certificate_factory_proof (order coordinate : Fin 2) :
    answer.certificate order coordinate = answer.paid.rowCertificate order coordinate :=
  (congrArg (fun values : Data.Vector (Data.Vector (Quadratic.Basic.Certificate increment) 2) 2 =>
      values order coordinate)
    answer.certificates_eq).trans (answer.paid.rowCertificates_apply order coordinate)

/-- Every selected certificate equals the same paid evaluator's row-certificate factory. -/
@[expose] def CertificateFactoryLaw : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
        {target : Paths.Frame (parameter + increment)} {count : Nat}
        {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
        {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
        {covered : CoveredParents count (firstParent :: remaining)}
        {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
        {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
        {targets : CellEndpoints.Targets original stage}
        {prepared : PreparedParents covered floor targets}
        {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
        {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
        {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
        {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
        {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
          ShiftedGeometry (target := target) (basis := basis) (count := count)
            (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
        {requestIndex globalFloor rootStage : Nat}
        {request : Request whole requestIndex globalFloor rootStage}
        {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    {located : Occurrence blocks request sourceIndex}
    {aligned : RootComparisons.Alignment
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference}
    {nonzero : increment ≠ 0}
    {spatial : AccuracyRequest}
    {time : { input : Rational // Primitive.unitInterval.Contains input }}
    (answer : Sample located aligned nonzero spatial time)
    (order coordinate : Fin 2),
    answer.certificate order coordinate = answer.paid.rowCertificate order coordinate

/-- The selected stored certificate retains its original actual new-bank factory at that SAME row. -/
theorem certificate_eq : CertificateFactoryLaw := @certificate_factory_proof

/-- Select three SAME stored comparison records for one adjacent row without comparison replay. -/
@[expose] def rowComparisons (order coordinate : Fin 2) :=
  ComparisonBank.row answer.comparisons order coordinate

/-- Read the SAME original source certificate through its exact scalar radicand index. -/
@[expose] def sourceRoot : CertifiedSquareRoot.Certificate
    (PicardFuchs.Polynomials.curveValue parameter
      ((prepared.entry located.block).preparation.cell.models.coordinate.point (located.sourceInput time.val))) :=
  answer.old.1.retained.sample.certificate.castParameter
  (Variation.Point.radicand_eq parameter
    ((prepared.entry located.block).preparation.cell.models.coordinate.point (located.sourceInput time.val)))

/-- Read the SAME independently transported target certificate at the identical physical point. -/
@[expose] def targetRoot : CertifiedSquareRoot.Certificate
    (PicardFuchs.Polynomials.curveValue (parameter + increment)
      ((prepared.entry located.block).preparation.cell.models.coordinate.point (located.sourceInput time.val))) :=
  answer.old.2.root.castParameter
  (Variation.Point.radicand_eq (parameter + increment)
    ((prepared.entry located.block).preparation.cell.models.coordinate.point (located.sourceInput time.val)))

/-- The original source square supplies the actual coefficient interpretation identity without a new root. -/
@[expose] def sourceIdentity : PowerIdentity answer.sourceRoot.value 2
    ((Paths.polynomial parameter).eval
      ((prepared.entry located.block).preparation.cell.models.coordinate.point
        (located.sourceInput time.val))) :=
  Eq.mpr (congrArg (fun value => PowerIdentity answer.sourceRoot.value 2 value)
    (Variation.Point.radicand_eq parameter _)) (PowerIdentity.ofSquare answer.sourceRoot.square)

/-- The original target square retains its changed polynomial owner in the same interpretation identity. -/
@[expose] def targetIdentity : PowerIdentity answer.targetRoot.value 2
    ((Paths.polynomial (parameter + increment)).eval
      ((prepared.entry located.block).preparation.cell.models.coordinate.point
        (located.sourceInput time.val))) :=
  Eq.mpr (congrArg (fun value => PowerIdentity answer.targetRoot.value 2 value)
    (Variation.Point.radicand_eq (parameter + increment) _)) (PowerIdentity.ofSquare answer.targetRoot.square)

/-- Read the SAME three selected numeric Readings at their exactly equal whole common request. -/
@[expose] def numerics (order coordinate : Fin 2) :=
  answer.joint.rowNumericsAtCommon answer.paid order coordinate

/-- Transport three SAME selected retained comparisons to that whole common request without replay. -/
@[expose] def commonComparisons (order coordinate : Fin 2) :=
  rowComparisonsAtCommon
  (located := located) (input := time.val) (oldObserved := answer.old.1) (step := answer.old.2)
  (nonzero := nonzero) (joint := answer.joint) (paid := answer.paid) (newObserved := answer.fresh)
    order coordinate (answer.rowComparisons order coordinate)

/-- Read the SAME selected actual target comparison with its complete original uniform and numeric owners explicit. -/
@[expose] def targetComparison (order coordinate : Fin 2) :
    ArithmeticComparison (answer.fresh.channel (Specification.Table.baseIndex order coordinate))
      (answer.numerics order coordinate).2.1 answer.targetIdentity :=
  (answer.commonComparisons order coordinate).2.1

/-- The selected actual certificate base is the unchanged source witness at the SAME common request. -/
private theorem certificate_base_proof (order coordinate : Fin 2) :
    (answer.certificate order coordinate).base = (answer.numerics order coordinate).1.reading :=
  (congrArg Quadratic.Basic.Certificate.base (answer.certificate_eq order coordinate)).trans
    (answer.joint.rowCommon_base answer.paid order coordinate)

/-- Every selected certificate base is the source reading at the same common request. -/
@[expose] def CertificateBaseLaw : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
        {target : Paths.Frame (parameter + increment)} {count : Nat}
        {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
        {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
        {covered : CoveredParents count (firstParent :: remaining)}
        {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
        {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
        {targets : CellEndpoints.Targets original stage}
        {prepared : PreparedParents covered floor targets}
        {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
        {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
        {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
        {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
        {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
          ShiftedGeometry (target := target) (basis := basis) (count := count)
            (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
        {requestIndex globalFloor rootStage : Nat}
        {request : Request whole requestIndex globalFloor rootStage}
        {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    {located : Occurrence blocks request sourceIndex}
    {aligned : RootComparisons.Alignment
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference}
    {nonzero : increment ≠ 0}
    {spatial : AccuracyRequest}
    {time : { input : Rational // Primitive.unitInterval.Contains input }}
    (answer : Sample located aligned nonzero spatial time)
    (order coordinate : Fin 2),
    (answer.certificate order coordinate).base = (answer.numerics order coordinate).1.reading

/-- The selected actual certificate base is the unchanged source witness at the SAME common request. -/
theorem certificate_base : CertificateBaseLaw := @certificate_base_proof

/-- The selected output is the independently paid actual target witness at that SAME original cache and row. -/
private theorem certificate_output_proof (order coordinate : Fin 2) :
    (answer.certificate order coordinate).output = (answer.numerics order coordinate).2.1.reading :=
  (congrArg Quadratic.Basic.Certificate.output (answer.certificate_eq order coordinate)).trans
    (answer.joint.rowCommon_output answer.paid order coordinate)

/-- Every selected certificate output is the independently paid target reading at the common request. -/
@[expose] def CertificateOutputLaw : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
        {target : Paths.Frame (parameter + increment)} {count : Nat}
        {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
        {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
        {covered : CoveredParents count (firstParent :: remaining)}
        {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
        {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
        {targets : CellEndpoints.Targets original stage}
        {prepared : PreparedParents covered floor targets}
        {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
        {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
        {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
        {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
        {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
          ShiftedGeometry (target := target) (basis := basis) (count := count)
            (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
        {requestIndex globalFloor rootStage : Nat}
        {request : Request whole requestIndex globalFloor rootStage}
        {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    {located : Occurrence blocks request sourceIndex}
    {aligned : RootComparisons.Alignment
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference}
    {nonzero : increment ≠ 0}
    {spatial : AccuracyRequest}
    {time : { input : Rational // Primitive.unitInterval.Contains input }}
    (answer : Sample located aligned nonzero spatial time)
    (order coordinate : Fin 2),
    (answer.certificate order coordinate).output = (answer.numerics order coordinate).2.1.reading

/-- The selected output is the independently paid actual target witness at that SAME original cache and row. -/
theorem certificate_output : CertificateOutputLaw := @certificate_output_proof

/-- The selected slope is the independent first or second source witness from the SAME actual paid bank. -/
private theorem certificate_slope_proof (order coordinate : Fin 2) :
    (answer.certificate order coordinate).slope = (answer.numerics order coordinate).2.2.reading :=
  (congrArg Quadratic.Basic.Certificate.slope (answer.certificate_eq order coordinate)).trans
    (answer.joint.rowCommon_slope answer.paid order coordinate)

/-- Every selected certificate slope is the independent source reading at the common request. -/
@[expose] def CertificateSlopeLaw : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
        {target : Paths.Frame (parameter + increment)} {count : Nat}
        {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
        {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
        {covered : CoveredParents count (firstParent :: remaining)}
        {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
        {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
        {targets : CellEndpoints.Targets original stage}
        {prepared : PreparedParents covered floor targets}
        {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
        {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
        {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
        {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
        {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
          ShiftedGeometry (target := target) (basis := basis) (count := count)
            (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
        {requestIndex globalFloor rootStage : Nat}
        {request : Request whole requestIndex globalFloor rootStage}
        {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    {located : Occurrence blocks request sourceIndex}
    {aligned : RootComparisons.Alignment
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference}
    {nonzero : increment ≠ 0}
    {spatial : AccuracyRequest}
    {time : { input : Rational // Primitive.unitInterval.Contains input }}
    (answer : Sample located aligned nonzero spatial time)
    (order coordinate : Fin 2),
    (answer.certificate order coordinate).slope = (answer.numerics order coordinate).2.2.reading

/-- The selected slope is the independent first or second source witness from the SAME actual paid bank. -/
theorem certificate_slope : CertificateSlopeLaw := @certificate_slope_proof

/-- Every selected actual certificate has its computed SAME original physical-box ceiling at the retained time. -/
private theorem certificate_factor_bound_proof (order coordinate : Fin 2) :
    (answer.certificate order coordinate).factor ≤
      Point.Step.Joint.rowCeiling
        (prepared.entry located.block).preparation.cell.patch increment order coordinate := by
  rewrite [answer.certificate_eq order coordinate]
  exact row_factor_le (located := located) (input := time.val) (inside := time.property)
    (oldObserved := answer.old.1) (step := answer.old.2) (nonzero := nonzero)
    (joint := answer.joint) (paid := answer.paid) order coordinate

/-- Every selected certificate factor meets the physical-box ceiling at the retained time. -/
@[expose] def CertificateFactorBound : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
        {target : Paths.Frame (parameter + increment)} {count : Nat}
        {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
        {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
        {covered : CoveredParents count (firstParent :: remaining)}
        {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
        {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
        {targets : CellEndpoints.Targets original stage}
        {prepared : PreparedParents covered floor targets}
        {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
        {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
        {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
        {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
        {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
          ShiftedGeometry (target := target) (basis := basis) (count := count)
            (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
        {requestIndex globalFloor rootStage : Nat}
        {request : Request whole requestIndex globalFloor rootStage}
        {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    {located : Occurrence blocks request sourceIndex}
    {aligned : RootComparisons.Alignment
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
          (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference}
    {nonzero : increment ≠ 0}
    {spatial : AccuracyRequest}
    {time : { input : Rational // Primitive.unitInterval.Contains input }}
    (answer : Sample located aligned nonzero spatial time)
    (order coordinate : Fin 2),
    (answer.certificate order coordinate).factor ≤
          Point.Step.Joint.rowCeiling
            (prepared.entry located.block).preparation.cell.patch increment order coordinate

/-- Every selected actual certificate has its computed SAME original physical-box ceiling at the retained time. -/
theorem certificate_factor_le : CertificateFactorBound := @certificate_factor_bound_proof

end Sample

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrence

end
