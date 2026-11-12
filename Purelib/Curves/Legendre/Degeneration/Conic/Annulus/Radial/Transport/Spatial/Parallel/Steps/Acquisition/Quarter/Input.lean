module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Circuit
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial.Acquisition.Entry
import Purelib.Approximation.AccuracyRequest
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Actual original geometry inputs for a paid whole quarter

The two inputs retain the complete original Steps quarter or an actual
original numerical Layer with its exact factory and decomposition caches.
Existing Sum and Sigma containers keep those two mathematical parents;
there is no callback record or replacement geometry/root owner. Source
and terminal unit-time certificates concern those exact cached parents.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement (Piece)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Riemann.Meshes

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable (leg : Transport.Leg site parameter unitQuarter)

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Input

/-- The complete original depth-seven quarter together with its same original source indices and unit-start proof. -/
@[expose] def Original :=
  Σ current : Endpoint,
    Σ reading : ReadingAt leg.actual current,
      Σ originalOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) current,
        { _original : Steps.Quarter leg.actual leg.regular current reading originalOwner //
          current = UniformPrimitiveMesh.firstEndpoint }

namespace Original

variable {leg} (input : Original leg)

/-- Read the unchanged source endpoint of the complete retained original Steps quarter. -/
@[expose] def current : Endpoint := input.1

/-- Read the unchanged complete original source Reading without performing its query. -/
@[expose] def reading : ReadingAt leg.actual input.current := input.2.1

/-- Read the identical original Steps Owner index, distinct from any later paid source Owner. -/
@[expose] def owner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.current := input.2.2.1

/-- Read the same entire original Steps quarter, including all old query, Geometry and covered caches. -/
@[expose] def quarter : Steps.Quarter leg.actual leg.regular input.current input.reading input.owner :=
  input.2.2.2.val

/-- The actual retained old Steps quarter begins at its certified original unit endpoint. -/
theorem initial : input.current = UniformPrimitiveMesh.firstEndpoint := input.2.2.2.property

end Original

section NumericallyIndexed

variable {radicand : CoefficientPolynomial} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}

/-- Exact factory and unit-span certificates for the SAME retained original numerical Layer.

The factory identity transports erased query and chain certificates only.
The actual Layer, scalar models, source Readings and decomposition remain
cached inputs; none is reconstructed from this proposition.
-/
@[irreducible, expose] def LayerAdmission {initialAccuracy : AccuracyRequest}
    (initial : Piece data leg.actual initialAccuracy) (depth : Nat) (layer : Refinement.Layer initial depth) : Prop :=
  layer = initial.layerAt depth ∧ 7 ≤ depth ∧ initial.Queried ∧
    initial.span.lower = 0 ∧ initial.span.upper = 1

/-- One complete actual numerical Layer and its original decomposition and final query caches.

The original initial piece retains its differential, accuracy, scalar Model
and full source Reading. The exact layerAt receipt supplies the existing
paid fold's intrinsic width and chain evidence. Its final QueryCache is an
actual separately retained original query, with no observation replay.
-/
@[expose] def Numerical :=
  Σ initialAccuracy : AccuracyRequest,
    Σ initial : Piece data leg.actual initialAccuracy,
      Σ depth : Nat,
        Σ layer : { retained : Refinement.Layer initial depth // LayerAdmission leg initial depth retained },
          Σ _parts : { retained : Refinement.Layer.Decomposition layer.val //
              retained = Refinement.Layer.Decomposition.build layer.val },
            { finish : ReadingAt leg.actual initial.upperEndpoint //
              QueryCache leg.actual initial.upperEndpoint finish }

namespace Numerical

variable {leg} (input : Numerical (data := data) leg)

/-- Read the SAME original initial residual request. -/
@[expose] def accuracy : AccuracyRequest := input.1

/-- Read the actual original initial piece with its complete source and scalar Model. -/
@[expose] def initial : Piece data leg.actual input.accuracy := input.2.1

/-- Read the actual retained original layer depth. -/
@[expose] def depth : Nat := input.2.2.1

/-- Read the same complete original numerical Layer without repeating its midpoint refinement. -/
@[expose] def layer : Refinement.Layer input.initial input.depth := input.2.2.2.1.val

/-- Read the exact cached head/tail view of that SAME original Layer. -/
@[expose] def parts : Refinement.Layer.Decomposition input.layer := input.2.2.2.2.1.val

/-- Read the same complete final requested-time Reading and its exact original query-factory receipt. -/
@[expose] def finish : { reading : ReadingAt leg.actual input.initial.upperEndpoint //
    QueryCache leg.actual input.initial.upperEndpoint reading } := input.2.2.2.2.2

/-- The retained actual layer has its exact original complete layerAt factory identity. -/
theorem layer_eq : input.layer = input.initial.layerAt input.depth := by
  have retained := input.2.2.2.1.property
  unfold LayerAdmission at retained
  exact retained.1

/-- The actual retained depth pays the original sharp paid-block width requirement. -/
theorem enough : 7 ≤ input.depth := by
  have retained := input.2.2.2.1.property
  unfold LayerAdmission at retained
  exact retained.2.1

/-- The exact original initial source keeps its own completed query-factory certificate. -/
theorem queried : input.initial.Queried := by
  have retained := input.2.2.2.1.property
  unfold LayerAdmission at retained
  exact retained.2.2.1

/-- The SAME old initial piece starts at chart time zero. -/
theorem atSource : input.initial.span.lower = 0 := by
  have retained := input.2.2.2.1.property
  unfold LayerAdmission at retained
  exact retained.2.2.2.1

/-- The SAME old initial piece ends at chart time one. -/
theorem atFinish : input.initial.span.upper = 1 := by
  have retained := input.2.2.2.1.property
  unfold LayerAdmission at retained
  exact retained.2.2.2.2

/-- The retained decomposition is exactly the original finite head/tail operation on this SAME cached Layer. -/
theorem parts_eq : input.parts = Refinement.Layer.Decomposition.build input.layer := input.2.2.2.2.1.property

variable {input} {initialAccuracy : AccuracyRequest}
variable (initialPiece : Piece data leg.actual initialAccuracy) (chosenDepth : Nat)
variable (retainedLayer : Refinement.Layer initialPiece chosenDepth)

/-- Retain an already completed original Layer and cache its finite decomposition once.

All query/width/unit-span certificates concern the supplied original
parents. Only the finite nonempty-list decomposition is computed here;
the Layer, its scalar Models and the supplied final query are not rebuilt.
-/
def ofLayer (factory : retainedLayer = initialPiece.layerAt chosenDepth) (enoughDepth : 7 ≤ chosenDepth)
    (sourceQueried : initialPiece.Queried) (atSource : initialPiece.span.lower = 0)
    (atFinish : initialPiece.span.upper = 1)
    (finishQuery : { reading : ReadingAt leg.actual initialPiece.upperEndpoint //
      QueryCache leg.actual initialPiece.upperEndpoint reading }) : Numerical (data := data) leg :=
  let parts := Refinement.Layer.Decomposition.build retainedLayer
  ⟨initialAccuracy, initialPiece, chosenDepth,
    ⟨retainedLayer, by unfold LayerAdmission; exact ⟨factory, enoughDepth, sourceQueried, atSource, atFinish⟩⟩,
    ⟨parts, rfl⟩, finishQuery⟩

section OfLayerReadbacks

variable (factory : retainedLayer = initialPiece.layerAt chosenDepth) (enoughDepth : 7 ≤ chosenDepth)
variable (sourceQueried : initialPiece.Queried) (atSource : initialPiece.span.lower = 0)
variable (atFinish : initialPiece.span.upper = 1)
variable (finishQuery : { reading : ReadingAt leg.actual initialPiece.upperEndpoint //
  QueryCache leg.actual initialPiece.upperEndpoint reading })

/-- The retained numerical input keeps the identical original initial request. -/
theorem ofLayer_accuracy :
    (ofLayer initialPiece chosenDepth retainedLayer factory enoughDepth sourceQueried atSource atFinish
      finishQuery).accuracy = initialAccuracy := by
  unfold ofLayer
  rfl

/-- The retained numerical input keeps the SAME chosen actual depth rather than a depth-seven execution. -/
theorem ofLayer_depth :
    (ofLayer initialPiece chosenDepth retainedLayer factory enoughDepth sourceQueried atSource atFinish
      finishQuery).depth = chosenDepth := by
  unfold ofLayer
  rfl

/-- The numerical input retains the complete identical original initial Piece across its exact request index. -/
theorem ofLayer_initial_heq :
    HEq (ofLayer initialPiece chosenDepth retainedLayer factory enoughDepth sourceQueried atSource atFinish
      finishQuery).initial initialPiece := by
  unfold ofLayer
  rfl

/-- The numerical input retains the whole SAME actual Layer across its exact depth and initial-Piece indices. -/
theorem ofLayer_layer_heq :
    HEq (ofLayer initialPiece chosenDepth retainedLayer factory enoughDepth sourceQueried atSource atFinish
      finishQuery).layer retainedLayer := by
  unfold ofLayer
  rfl

end OfLayerReadbacks

end Numerical

end NumericallyIndexed

/-- A numerical quarter input keeps its original indexed differential/data Owner with the SAME retained Layer caches. -/
@[expose] def Fine :=
  Σ radicand : CoefficientPolynomial,
    Σ differential : OddPowerDifferential radicand,
      Σ data : Waist.Differential.Bounds.Data site parameter differential, Numerical (data := data) leg

namespace Fine

variable {leg} (input : Fine leg)

/-- Read the original retained differential's polynomial index. -/
@[expose] def radicand : CoefficientPolynomial := input.1

/-- Read the SAME original indexed ordinary differential. -/
@[expose] def differential : OddPowerDifferential input.radicand := input.2.1

/-- Read its SAME original retained numerical/geometric bounds owner. -/
@[expose] def data : Waist.Differential.Bounds.Data site parameter input.differential := input.2.2.1

/-- Read the whole numerical input without changing its differential, source, request or Layer caches. -/
@[expose] def numerical : Numerical (data := input.data) leg := input.2.2.2

end Fine

end Input

/-- A whole-quarter geometry input retains exactly one of its two existing mathematical parents.

The original Steps quarter carries its original query/Geometry/unpaid-cover
caches. A numerical input carries the actual original finer Layer instead;
it requires no dummy old Steps or unpaid cover. The paid realization uses
the original corresponding producer in each branch.
-/
@[expose] def Input := Sum (Input.Original leg) (Input.Fine leg)

namespace Input

variable {leg} (input : Input leg)

/-- Read the actual original source endpoint of the retained parent. -/
@[expose] def sourceEndpoint : Endpoint :=
  match input with
  | .inl original => original.current
  | .inr fine => fine.numerical.initial.lowerEndpoint

/-- Read the SAME actual old source Reading of the retained parent, without a time query. -/
@[expose] def sourceReading : ReadingAt leg.actual input.sourceEndpoint :=
  match input with
  | .inl original => original.reading
  | .inr fine => fine.numerical.initial.source

/-- The exact actual parent source is at its original unit-quarter initial chart time. -/
theorem source_time : input.sourceEndpoint.parameter = 0 := by
  cases input with
  | inl original => exact congrArg Endpoint.parameter original.initial
  | inr fine => exact fine.numerical.atSource

variable {current : Endpoint} {reading : ReadingAt leg.actual current}
variable {originalOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) current}

/-- Retain the whole existing original Steps quarter and its exact source indices without reconstructing any cache. -/
@[expose] def ofSteps
    (original : Steps.Quarter leg.actual leg.regular current reading originalOwner)
    (initial : current = UniformPrimitiveMesh.firstEndpoint) : Input leg :=
  .inl ⟨current, reading, originalOwner, original, initial⟩

variable {radicand : CoefficientPolynomial} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}

/-- Retain a complete actual numerical input under its SAME original indexed differential and bounds Owner. -/
@[expose] def ofNumerical (numerical : Input.Numerical (data := data) leg) : Input leg :=
  .inr ⟨radicand, differential, data, numerical⟩

/-- The old constructor reads exactly the original source endpoint. -/
theorem ofSteps_sourceEndpoint
    (original : Steps.Quarter leg.actual leg.regular current reading originalOwner)
    (initial : current = UniformPrimitiveMesh.firstEndpoint) :
    (ofSteps original initial).sourceEndpoint = current := rfl

/-- The old constructor preserves the complete SAME original source Reading. -/
theorem ofSteps_sourceReading
    (original : Steps.Quarter leg.actual leg.regular current reading originalOwner)
    (initial : current = UniformPrimitiveMesh.firstEndpoint) :
    (ofSteps original initial).sourceReading = reading := rfl

/-- The numerical constructor preserves its SAME original source endpoint. -/
theorem ofNumerical_sourceEndpoint (numerical : Input.Numerical (data := data) leg) :
    (ofNumerical numerical).sourceEndpoint = numerical.initial.lowerEndpoint := rfl

/-- The numerical constructor preserves the entire SAME original source Reading. -/
theorem ofNumerical_sourceReading (numerical : Input.Numerical (data := data) leg) :
    (ofNumerical numerical).sourceReading = numerical.initial.source := rfl

end Input

end Steps.Acquisition.Quarter

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
