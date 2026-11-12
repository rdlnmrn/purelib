module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Accuracy
import Purelib.Approximation.Gaussian.Provenance.Power
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Joint.Reobservation
import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Reobservation.Rows
import Purelib.Data.Vector.Basic
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Transport
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table

/-! # Original query samples at retained global occurrences

The original raw prepared sources, Blocks and global Request remain abstract
indices. The seven existing dependent cache fields retain both query bundles,
their Step, whole original spatial bank, direct Query, ten unique comparisons
and the four scalar certificates. No closed-stage producer or polynomial restriction enters this
construction, and the original seven factory operations execute only once.
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

/-- The complete old query and its original Point.Step at the same mapped physical time. -/
@[expose] def Old (time : { input : Rational // Primitive.unitInterval.Contains input }) :=
  SourceStep located time.val

/-- The complete independent target query at its original globally allocated child and time. -/
@[expose] def Fresh (time : { input : Rational // Primitive.unitInterval.Contains input }) :=
  request.Observation sourceIndex time.val

/-- The original Joint bank indexed by that same retained old Point.Step and the two actual spatial requests. -/
@[expose] def Joint (time : { input : Rational // Primitive.unitInterval.Contains input })
    (old : Old located time) :=
  Point.Step.Joint old.2 nonzero spatial spatial

/-- The independent evaluator bank indexed by the same original Joint arithmetic cache. -/
@[expose] def Paid (time : { input : Rational // Primitive.unitInterval.Contains input })
    (old : Old located time) (joint : Joint located nonzero spatial time old) :=
  Variation.Arithmetic.Reobservations joint.arithmetic spatial

/-- The direct query on the original globally located prepared child edge at its original bounded time. -/
@[expose] def Direct (time : { input : Rational // Primitive.unitInterval.Contains input }) :=
  PreparedEdge.Query ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge
    time.val time.property

/-- The ten actual comparison types retain every original source, target, scalar and numeric owner. -/
@[expose] def Comparisons (time : { input : Rational // Primitive.unitInterval.Contains input })
    (old : Old located time) (fresh : Fresh (request := request) (sourceIndex := sourceIndex) time)
    (joint : Joint located nonzero spatial time old) (paid : Paid located nonzero spatial time old joint) :=
  ComparisonBank (parameter := parameter) (increment := increment)
    (frame := frame) (basis := basis) (target := target) (count := count)
    (firstParent := firstParent) (remaining := remaining) (covered := covered) (floor := floor)
    (baseStart := baseStart) (baseFinish := baseFinish) (original := original)
    (stage := stage) (targets := targets) (prepared := prepared)
    (ranges := ranges) (allocation := allocation) (admitted := admitted) (widths := widths)
    (whole := whole) (requestIndex := requestIndex) (globalFloor := globalFloor) (rootStage := rootStage)
    (blocks := blocks) (request := request) (sourceIndex := sourceIndex)
    located time.val old.1 old.2 nonzero joint paid fresh

/-- The original old query/Step cache retains its entire actual source factory equality. -/
@[expose] def RetainedOld (time : { input : Rational // Primitive.unitInterval.Contains input }) :=
  { value : Old located time // value = located.sourceStep time.val time.property }

/-- The independent target query cache retains its complete original globally allocated query factory. -/
@[expose] def RetainedFresh (time : { input : Rational // Primitive.unitInterval.Contains input }) :=
  { value : Fresh (request := request) (sourceIndex := sourceIndex) time //
    value = (request.attempt.2.1.entry sourceIndex).preparation.query.observe target
      time.val time.property.1 time.property.2 }

/-- The retained original direct child query includes its complete original factory equation. -/
@[expose] def RetainedDirect (time : { input : Rational // Primitive.unitInterval.Contains input }) :=
  { value : Direct (request := request) (sourceIndex := sourceIndex) time //
    value = PreparedEdge.Query.build _ time.val time.property }

/-- The ten retained comparisons include their whole factory on the SAME actual source and spatial bank. -/
@[expose] def RetainedComparisons (time : { input : Rational // Primitive.unitInterval.Contains input })
    (old : RetainedOld located time)
    (fresh : RetainedFresh (request := request) (sourceIndex := sourceIndex) time)
    (bank : Spatial old.val.2 nonzero spatial)
    (direct : RetainedDirect (request := request) (sourceIndex := sourceIndex) time) :=
  { value : Comparisons located nonzero spatial time old.val fresh.val bank.joint bank.paid //
    value = comparisonBank
      (located := located) (input := time.val) (inside := time.property)
      (oldObserved := old.val.1)
      (old_eq := (congrArg (fun answer => answer.1) old.property).trans
        (located.sourceStep_observation time.val time.property))
      (step := old.val.2) (nonzero := nonzero) (joint := bank.joint) (paid := bank.paid)
      (newObserved := fresh.val) (new_eq := fresh.property) (aligned := aligned) (direct := direct.val) }

/-- The four actual scalar certificates retain their complete original factory on the SAME spatial evaluator bank. -/
@[expose] def RetainedCertificates (time : { input : Rational // Primitive.unitInterval.Contains input })
    (old : RetainedOld located time) (bank : Spatial old.val.2 nonzero spatial) :=
  { certificates : Data.Vector (Data.Vector (Quadratic.Basic.Certificate increment) 2) 2 //
    certificates = bank.paid.rowCertificates }

/-- The original source query and whole spatial bank retain the four certificates on that SAME paid bank. -/
@[expose] def SourceCaches (time : { input : Rational // Primitive.unitInterval.Contains input }) :=
  (old : RetainedOld located time) ×
    (bank : Spatial old.val.2 nonzero spatial) × RetainedCertificates located nonzero spatial time old bank

/-- The independent target bundle and direct child query retain their own original whole factories. -/
@[expose] def QueryCaches (time : { input : Rational // Primitive.unitInterval.Contains input }) :=
  RetainedFresh (request := request) (sourceIndex := sourceIndex) time ×
    RetainedDirect (request := request) (sourceIndex := sourceIndex) time

end Sample

/-- One original bounded-time answer retains the seven original cache values and their whole factory equations.

The original occurrence and signed Alignment are inputs. This is the
existing Sigma and product containers at its query owner, without any closed-stage
builder, global root-chain proof, ValueCell or polynomial restriction index.
-/
@[expose] def Sample (time : { input : Rational // Primitive.unitInterval.Contains input }) :=
  (source : Sample.SourceCaches located nonzero spatial time) ×
  (queries : Sample.QueryCaches (request := request) (sourceIndex := sourceIndex) time) ×
  Sample.RetainedComparisons located aligned nonzero spatial time source.1 queries.1 source.2.1 queries.2

namespace Sample

/-- Retain both original queries, the spatial bank, four certificates and ten shared actual comparisons.

The source and target queries run before the original buildSpatial
operation, which constructs its Joint and paid evaluator bank once.
The four scalar certificates are retained before the direct child Query and
comparison factories. All original owner and request indices are kept.
-/
def build (time : { input : Rational // Primitive.unitInterval.Contains input }) :
    Sample located aligned nonzero spatial time :=
  let oldValue : Old located time := located.sourceStep time.val time.property
  let freshValue : Fresh (request := request) (sourceIndex := sourceIndex) time :=
    (request.attempt.2.1.entry sourceIndex).preparation.query.observe target
      time.val time.property.1 time.property.2
  let old : RetainedOld located time := ⟨oldValue, rfl⟩
  let fresh : RetainedFresh (request := request) (sourceIndex := sourceIndex) time := ⟨freshValue, rfl⟩
  let bank : Spatial old.val.2 nonzero spatial := Spatial.build old.val.2 nonzero spatial
  let certificates : Data.Vector (Data.Vector (Quadratic.Basic.Certificate increment) 2) 2 :=
    bank.paid.rowCertificates
  let directValue : Direct (request := request) (sourceIndex := sourceIndex) time := PreparedEdge.Query.build
    ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge
    time.val time.property
  let direct : RetainedDirect (request := request) (sourceIndex := sourceIndex) time := ⟨directValue, rfl⟩
  let comparisons : Comparisons located nonzero spatial time old.val fresh.val bank.joint bank.paid :=
    comparisonBank
      (located := located) (input := time.val) (inside := time.property)
      (oldObserved := old.val.1)
      (old_eq := (congrArg (fun answer => answer.1) old.property).trans
        (located.sourceStep_observation time.val time.property))
      (step := old.val.2) (nonzero := nonzero) (joint := bank.joint) (paid := bank.paid)
      (newObserved := fresh.val) (new_eq := fresh.property) (aligned := aligned) (direct := direct.val)
  ⟨⟨old, bank, ⟨certificates, rfl⟩⟩, ⟨fresh, direct⟩, ⟨comparisons, rfl⟩⟩

variable {located aligned nonzero spatial} {time : { input : Rational // Primitive.unitInterval.Contains input }}
    (answer : Sample located aligned nonzero spatial time)

/-- Read the complete original old query/Step pair at its retained mapped parent time. -/
@[expose] def old : Old located time := answer.1.1.val

/-- Read the independent whole original globally allocated target bundle at the same child time. -/
@[expose] def fresh : Fresh (request := request) (sourceIndex := sourceIndex) time := answer.2.1.1.val

/-- Read the complete original spatial bank on the same stored source Step. -/
@[expose] def spatialBank : Spatial answer.old.2 nonzero spatial := answer.1.2.1

/-- Read the original Joint root/scalar bank on exactly the stored old query's Point.Step. -/
@[expose] def joint : Joint located nonzero spatial time answer.old := answer.spatialBank.joint

/-- Read the actual independently paid evaluator bank on the same original Joint core. -/
@[expose] def paid : Paid located nonzero spatial time answer.old answer.joint := answer.spatialBank.paid

/-- Read the retained direct query used to derive the actual signed global/Step agreement. -/
@[expose] def direct : Direct (request := request) (sourceIndex := sourceIndex) time := answer.2.1.2.val

/-- Read the ten already materialized independent arithmetic/uniform comparisons without replay. -/
@[expose] def comparisons : Comparisons located nonzero spatial time answer.old answer.fresh answer.joint answer.paid :=
  answer.2.2.val

end Sample

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrence

end
