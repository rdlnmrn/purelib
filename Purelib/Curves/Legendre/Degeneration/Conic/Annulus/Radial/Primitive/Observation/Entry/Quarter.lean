module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Entry.Vertex
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
public import
  Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Comparison
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Original curved endpoint observations at the actual paid quarter vertices

The quarter's original initial agreement and stored paid finish comparison
supply the actual signed full-cubic relation. The retained original query
at each end is compared with the old bank endpoint query using its same
quarter budget. Both old primitive observations, their independent original
requests and visible radii remain unchanged. Only operational tail
comparisons are acquired. No source attachment or vertex is reconstructed.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Entry

namespace Quarter

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Legendre.Periods.Jets.Source (Row)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.Branches.ClearSheetContinuation (Subdivision)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (finalTarget)
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {positive : (0 : Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 unitQuarter positive}
variable {regular : parameter ≠ criticalValue site}
variable {current : Subdivision.Endpoint} {reading : ReadingAt actual current}
variable {originalOwner sourceOwner : OwnerAt site parameter unitQuarter positive current}
variable {original : Steps.Quarter actual regular current reading originalOwner}
variable {agreement : Steps.Acquisition.InitialAgreement current reading sourceOwner}
variable {row : Row} {vertexAccuracy : AccuracyRequest}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The original first-endpoint identity gives the source's exact physical coordinate without changing its Owner. -/
theorem source_base_eq (initial : current = UniformPrimitiveMesh.firstEndpoint) :
    Spatial.coordinate site parameter 2 unitQuarter positive current.parameter =
      (point site parameter 2 (Waist.direction unitQuarter 0) positive).base := by
  have bases := congrArg (fun endpoint : Subdivision.Endpoint =>
    (point site parameter 2 (Waist.direction unitQuarter endpoint.parameter) positive).base) initial
  exact bases

/-- The initial paid source Owner agrees with an arbitrary old bank query at this same actual quarter source.

The original Type-valued initial agreement is used in its signed direction.
The two retained original query Owners are compared by their actual common
quarter budget and exact base identity, without acquiring a common Owner.
-/
def sourceEquivalent {inside : FixedRootBoxPath.Inside 0}
    (old : Transport.Reading actual 0 inside) (initial : current = UniformPrimitiveMesh.firstEndpoint) :
    NamedEquivalent (ownerRootName sourceOwner.parameterNonzero sourceOwner) old.lift.value.name :=
  agreement.symm.trans
    (reading.agrees_of_base_eq old regular (source_base_eq (site := site) (parameter := parameter)
      (unitQuarter := unitQuarter) (positive := positive) initial))

/-- Compare both OLD primitive observations at the literal paid source Owner using derived full-sheet agreement. -/
def compareSource {inside : FixedRootBoxPath.Inside 0}
    {old : Transport.Reading actual 0 inside} {rootAccuracy bankAccuracy : AccuracyRequest}
    {sample : CertifiedSquareRoot.Sampling.ResidualObservation old.lift.unitRoot rootAccuracy}
    (entry : Entry (row.form parameter) old regular sample bankAccuracy)
    (vertex : OwnerPath.Primitive.Vertex (row.expression parameter)
      (Spatial.coordinate site parameter 2 unitQuarter positive current.parameter) sourceOwner vertexAccuracy)
    (initial : current = UniformPrimitiveMesh.firstEndpoint) (request : AccuracyRequest) :
    Equivalence.Observation.Comparison entry.selected.asObservation vertex.observation request.tolerance :=
  entry.compareVertex vertex (source_base_eq initial)
    (sourceEquivalent (agreement := agreement) (regular := regular) old initial) request

variable (paid : Steps.Acquisition.Quarter original sourceOwner agreement)

/-- The retained depth-seven target factory gives the final vertex's exact physical coordinate. -/
theorem finish_base_eq (initial : current = UniformPrimitiveMesh.firstEndpoint) :
    Spatial.coordinate site parameter 2 unitQuarter positive
        (finalTarget current paid.originalQuarter.cache.val).parameter =
      (point site parameter 2 (Waist.direction unitQuarter 1) positive).base := by
  have bases := congrArg (fun endpoint : Subdivision.Endpoint =>
    (point site parameter 2 (Waist.direction unitQuarter endpoint.parameter) positive).base)
    (paid.finalEndpoint_eq initial)
  exact bases

/-- The identical stored paid finishOwner agrees with an arbitrary OLD bank query at the certified final chart time.

The paid quarter's actual finishEquivalent is composed with the original
same-quarter comparison from its retained final Reading. The last Reading
need not be the bank query or the original Leg target, and neither input is
replaced by an endpoint-indexed Owner or an independently acquired root.
-/
def finishEquivalent {inside : FixedRootBoxPath.Inside 1}
    (old : Transport.Reading actual 1 inside) (initial : current = UniformPrimitiveMesh.firstEndpoint) :
    NamedEquivalent (ownerRootName paid.finishOwner.parameterNonzero paid.finishOwner) old.lift.value.name :=
  (Steps.Acquisition.Quarter.finishEquivalent paid).trans
    (paid.finishReading.agrees_of_base_eq old regular (finish_base_eq paid initial))

/-- Compare both OLD primitive observations at the literal stored paid finishOwner and derived original full sheet. -/
def compareFinish {inside : FixedRootBoxPath.Inside 1}
    {old : Transport.Reading actual 1 inside} {rootAccuracy bankAccuracy : AccuracyRequest}
    {sample : CertifiedSquareRoot.Sampling.ResidualObservation old.lift.unitRoot rootAccuracy}
    (entry : Entry (row.form parameter) old regular sample bankAccuracy)
    (vertex : OwnerPath.Primitive.Vertex (row.expression parameter)
      (Spatial.coordinate site parameter 2 unitQuarter positive
        (finalTarget current paid.originalQuarter.cache.val).parameter) paid.finishOwner vertexAccuracy)
    (initial : current = UniformPrimitiveMesh.firstEndpoint) (request : AccuracyRequest) :
    Equivalence.Observation.Comparison entry.selected.asObservation vertex.observation request.tolerance :=
  entry.compareVertex vertex (finish_base_eq paid initial) (finishEquivalent paid old initial) request

section Boundary

variable {firstInside : FixedRootBoxPath.Inside 0} {lastInside : FixedRootBoxPath.Inside 1}
variable {firstReading : Transport.Reading actual 0 firstInside} {lastReading : Transport.Reading actual 1 lastInside}
variable {firstRootAccuracy lastRootAccuracy firstAccuracy lastAccuracy : AccuracyRequest}
variable {firstSample : CertifiedSquareRoot.Sampling.ResidualObservation firstReading.lift.unitRoot firstRootAccuracy}
variable {lastSample : CertifiedSquareRoot.Sampling.ResidualObservation lastReading.lift.unitRoot lastRootAccuracy}
variable (firstEntry : Entry (row.form parameter) firstReading regular firstSample firstAccuracy)
variable (lastEntry : Entry (row.form parameter) lastReading regular lastSample lastAccuracy)
variable (firstVertex : OwnerPath.Primitive.Vertex (row.expression parameter)
  (Spatial.coordinate site parameter 2 unitQuarter positive current.parameter) sourceOwner vertexAccuracy)
variable (lastVertex : OwnerPath.Primitive.Vertex (row.expression parameter)
  (Spatial.coordinate site parameter 2 unitQuarter positive
    (finalTarget current paid.originalQuarter.cache.val).parameter) paid.finishOwner vertexAccuracy)

/-- Two actual endpoint Comparison caches bound the difference of the SAME old curved and paid primitive increments.

The two primitive constants cancel by the literal ordered difference. The
bound charges each old bank radius, each old paid vertex radius and both
actual new tail targets. No equality of selected primitive values or
identification of moving integrals is assumed.
-/
theorem boundary_error_lt {firstRequest lastRequest : AccuracyRequest}
    (firstCompared : Equivalence.Observation.Comparison
      firstEntry.selected.asObservation firstVertex.observation firstRequest.tolerance)
    (lastCompared : Equivalence.Observation.Comparison
      lastEntry.selected.asObservation lastVertex.observation lastRequest.tolerance) :
    Norm.Basic.normSq ((lastEntry.value - firstEntry.value) - (lastVertex.value - firstVertex.value)) <
      2 * ((16 * ((OddPower.Observation.radiusRequest lastAccuracy).tolerance +
          (OwnerPath.Primitive.vertexRequest vertexAccuracy).tolerance) + 4 * lastRequest.tolerance) +
        (16 * ((OddPower.Observation.radiusRequest firstAccuracy).tolerance +
          (OwnerPath.Primitive.vertexRequest vertexAccuracy).tolerance) + 4 * firstRequest.tolerance)) := by
  have firstBound := firstEntry.compareVertex_error_lt firstVertex firstCompared
  have lastBound := lastEntry.compareVertex_error_lt lastVertex lastCompared
  have difference (a b c d : Canonical) : (a - b) - (c - d) = (a - c) - (b - d) := by ring1
  rewrite [difference lastEntry.value firstEntry.value lastVertex.value firstVertex.value]
  exact (Norm.Bounds.normSq_sub_le_two _ _).trans_lt
    (Order.Arithmetic.mul_lt_mul_of_pos_left_direct (of_decide_eq_true rfl : (0 : Rational) < 2)
      (Order.Arithmetic.add_lt_add_direct lastBound firstBound))

section Spine

variable (observed : OwnerPath.Primitive.Spine (row.expression parameter) vertexAccuracy paid.receipt.trace)
variable (firstRequest lastRequest : AccuracyRequest)

/-- Two actual operational Comparison caches retain the literal old paid-spine endpoint observations and factories.

Both whole old curved Entries and the complete old paid quarter spine are
indices. No primitive observation or path is rebuilt. The two selected tail
comparisons are the only new observations, and each complete factory
identity is stored with its actual retained result.
-/
@[expose] def Compared (initial : current = UniformPrimitiveMesh.firstEndpoint) :=
  { retained : Equivalence.Observation.Comparison
      firstEntry.selected.asObservation observed.first.observation firstRequest.tolerance //
    retained = compareSource (agreement := agreement) firstEntry observed.first initial firstRequest } ×
    { retained : Equivalence.Observation.Comparison
        lastEntry.selected.asObservation observed.last.observation lastRequest.tolerance //
      retained = compareFinish paid lastEntry observed.last initial lastRequest }

namespace Compared

/-- Compare the two actual old quarter endpoint pairs once, preserving both complete original observation executions. -/
def build (initial : current = UniformPrimitiveMesh.firstEndpoint) :
    Compared paid firstEntry lastEntry observed firstRequest lastRequest initial :=
  let first := compareSource (agreement := agreement) firstEntry observed.first initial firstRequest
  let last := compareFinish paid lastEntry observed.last initial lastRequest
  ⟨⟨first, rfl⟩, ⟨last, rfl⟩⟩

variable {firstRequest lastRequest} {initial : current = UniformPrimitiveMesh.firstEndpoint}
variable (compared : Compared paid firstEntry lastEntry observed firstRequest lastRequest initial)

/-- Read the SAME original source Comparison on the old bank and literal old paid-spine source observation. -/
@[expose] def first : Equivalence.Observation.Comparison
    firstEntry.selected.asObservation observed.first.observation firstRequest.tolerance := compared.1.val

/-- Read the SAME original final Comparison on the old bank and literal stored paid-spine finish observation. -/
@[expose] def last : Equivalence.Observation.Comparison
    lastEntry.selected.asObservation observed.last.observation lastRequest.tolerance := compared.2.val

/-- The retained source Comparison is the complete actual factory using the derived signed source relation. -/
theorem first_eq : compared.first =
    compareSource (agreement := agreement) firstEntry observed.first initial firstRequest := compared.1.property

/-- The retained final Comparison is the complete actual factory using this stored paid finishOwner's relation. -/
theorem last_eq : compared.last = compareFinish paid lastEntry observed.last initial lastRequest := compared.2.property

include compared in
/-- The two actual cached endpoint comparisons pay the original curved and literal paid-spine boundary increments. -/
theorem boundary_error_lt :
    Norm.Basic.normSq ((lastEntry.value - firstEntry.value) - (observed.last.value - observed.first.value)) <
      2 * ((16 * ((OddPower.Observation.radiusRequest lastAccuracy).tolerance +
          (OwnerPath.Primitive.vertexRequest vertexAccuracy).tolerance) + 4 * lastRequest.tolerance) +
        (16 * ((OddPower.Observation.radiusRequest firstAccuracy).tolerance +
          (OwnerPath.Primitive.vertexRequest vertexAccuracy).tolerance) + 4 * firstRequest.tolerance)) :=
  Quarter.boundary_error_lt paid firstEntry lastEntry observed.first observed.last compared.first compared.last

end Compared

end Spine

end Boundary

end Quarter

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Entry

end
