module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Entry.Comparison
public import Purelib.Curves.Legendre.Periods.Jets.Source.Row.Forms
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive
import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian.Comparison
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Old curved primitive endpoint observations at a literal paid vertex Owner

The old bank Entry and old owner-path Vertex keep their separate requests,
selected values, states and visible radii. Original full-sheet agreement
transports the cached coefficient interpretation, and exact row normalization
retains its original channel. The existing operational Comparison then pays
both actual old observations and its newly requested tail separately.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Entry

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Legendre.Periods.Jets.Source (Row)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Rational) < 2} {actual : Transport.Quarter site parameter 2 quarter positive}
variable {time : Rational} {inside : FixedRootBoxPath.Inside time}
variable {reading : Transport.Reading actual time inside} {regular : parameter ≠ criticalValue site}
variable {row : Row} {rootAccuracy bankAccuracy vertexAccuracy : AccuracyRequest}
variable {sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot rootAccuracy}
variable {base : Canonical} {owner : Owner ((Paths.polynomial parameter).eval base)}
variable (entry : Entry (row.form parameter) reading regular sample bankAccuracy)
variable (vertex : OwnerPath.Primitive.Vertex (row.expression parameter) base owner vertexAccuracy)

/-- Derive evaluator agreement from both original full sheets and the actual original row's cleared normalization.

Base equality only transports the physical polynomial coordinate. Signed
root agreement is an independent original operational input. Reinterpretation
keeps the bank denotation's exact cached pair and original channel, and the
paid vertex retains its own complete denotation and old request.
-/
def equivalentVertex
    (point_eq : base = (point site parameter 2 (Waist.direction quarter time) positive).base)
    (fullSheet : NamedEquivalent (ownerRootName owner.parameterNonzero owner) reading.lift.value.name) :
    NamedEquivalent entry.endpoint.values.value.name vertex.original.channel.name := by
  cases point_eq
  unfold ownerRootName at fullSheet
  let sheets := entry.endpoint.prepared.equivalent.symm.trans fullSheet.symm
  let original := entry.endpoint.values.interpretation
  have normalized : (row.expression parameter).Equal original.source := by
    rewrite [original.source_eq]
    exact row.form_equal parameter
  let selected := original.reinterpret (row.expression parameter) normalized vertex.original.defined
  have sameChannel : selected.channel = original.channel := rfl
  have interpreted := selected.equivalent vertex.original sheets
  exact entry.endpoint.values.agrees_interpretation.trans
    (NamedEquivalent.transport (congrArg CoherentNamed.name sameChannel) rfl interpreted)

/-- Compare both actual OLD endpoint observations without selecting or replacing either one.

The returned original Comparison retains both complete observation owners,
actual based states/radii and the selected new tail comparison. The full-sheet
and polynomial certificates derive its evaluator agreement internally.
-/
def compareVertex
    (point_eq : base = (point site parameter 2 (Waist.direction quarter time) positive).base)
    (fullSheet : NamedEquivalent (ownerRootName owner.parameterNonzero owner) reading.lift.value.name)
    (request : AccuracyRequest) : Equivalence.Observation.Comparison
      entry.selected.asObservation vertex.observation request.tolerance :=
  Equivalence.Observation.Comparison.build entry.selected.asObservation vertex.observation
    (entry.equivalentVertex vertex point_eq fullSheet) request.tolerance request.positive

/-- Both old request radii and the independent tail target pay the unchanged primitive values at this endpoint. -/
theorem compareVertex_error_lt {request : AccuracyRequest}
    (comparison : Equivalence.Observation.Comparison
      entry.selected.asObservation vertex.observation request.tolerance) :
    Norm.Basic.normSq (entry.value - vertex.value) <
      16 * ((OddPower.Observation.radiusRequest bankAccuracy).tolerance +
        (OwnerPath.Primitive.vertexRequest vertexAccuracy).tolerance) + 4 * request.tolerance :=
  comparison.reading_error_le.trans_lt
    (Order.Arithmetic.add_lt_add_right_direct
      (Order.Arithmetic.mul_lt_mul_of_pos_left_direct (of_decide_eq_true rfl : (0 : Rational) < 16)
        (Order.Arithmetic.add_lt_add_direct entry.selected.asObservation_radius_lt vertex.requested.radius_lt)) _)

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Entry

end
