module
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.Requests
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Riemann.Readings.PreparedPrimitiveSamples.Numerator

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningValues.Accuracy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedFaceChartRequests
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Vector.Basic
import Purelib.Data.Nat.Order
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # Internally paid face residuals on the original canonical cochain

The literal source-minus-basis face list feeds the original signed-face
chart request. Its sufficient stage precedes the numerical bank and
triangle readings. The physical-loop and annular terms remain separate.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows.BasisCoordinates

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Riemann.Readings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (CutBank ClosedCoordinates)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedFaceChartRequests (SignedFaceChartRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector (get)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {lifted : LiftedPuncturedGrid base} {bank : BasedBranchBank lifted} {sheet : Fin 2}
    {ordered : Ordered bank sheet} {paired : Paired ordered} {prepared : Prepared paired}
    {cut : CutBank prepared} {word : List (OrientedEdge lifted.vertices.count)}
    {row : ClosedCoordinates word cut.integral} (coordinates : BasisCoordinates cut row)

/-- The literal signed source-route correction minus every original coefficient-weighted A/B route correction.

The source list comes first. Each retained genus row contributes its A list
then its B list; negation changes the signed multiplicities without deleting
zero weights, repeated faces or opposite occurrences.
-/
@[expose] def faceResidualTerms : List (SewingRetraction.FaceTerm lifted.mesh.triangles.length) :=
  row.route.correction ++ SewingRetraction.negative (List.ofFn (fun index : Fin genus =>
    SewingRetraction.scale (get coordinates.a index) (cut.rows.get index).a.route.correction ++
      SewingRetraction.scale (get coordinates.b index) (cut.rows.get index).b.route.correction)).flatten

/-- The literal signed correction list reads exactly the complete original face residual for every cochain. -/
theorem faceResidualTerms_value (value : OrientedEdge lifted.vertices.count → Canonical) :
    SewingRetraction.faceValue lifted.mesh.triangulation.faces value coordinates.faceResidualTerms =
      coordinates.faceResidual value := by
  let groups := fun index : Fin genus =>
    SewingRetraction.scale (get coordinates.a index) (cut.rows.get index).a.route.correction ++
      SewingRetraction.scale (get coordinates.b index) (cut.rows.get index).b.route.correction
  have original := SewingRetraction.faceValue_flatten_ofFn lifted.mesh.triangulation.faces value groups
  have rows := sumFin_congr (fun index : Fin genus =>
    (SewingRetraction.faceValue_append lifted.mesh.triangulation.faces value _ _).trans
      (congrArg₂ (fun first last : Canonical => first + last)
        (SewingRetraction.faceValue_scale lifted.mesh.triangulation.faces value
          (get coordinates.a index) (cut.rows.get index).a.route.correction)
        (SewingRetraction.faceValue_scale lifted.mesh.triangulation.faces value
          (get coordinates.b index) (cut.rows.get index).b.route.correction)))
  have combined := original.trans rows
  change SewingRetraction.faceValue lifted.mesh.triangulation.faces value
      (row.route.correction ++ SewingRetraction.negative (List.ofFn groups).flatten) = _
  rewrite [SewingRetraction.faceValue_append, SewingRetraction.faceValue_negative, combined]
  rfl

variable (differential : Differential genus)
variable (domains : FaceDomainBank lifted.frames base.faces.regulars)
variable (target : Rational) (positive : 0 < target)

/-- The original coordinate owner, literal signed correction and chart request before any numerical sampling.

The complete factories retain the actual source-minus-basis face list and
its original signed-face request. This cache may share a later numerical
bank with physical-loop, annular or other cycle requests.
-/
abbrev FaceResidualRequest (polynomial : Option (Ordinary curve.polynomial) := none) :=
  {_value : BasisCoordinates cut row // _value = coordinates} ×
  (terms : {value : List (SewingRetraction.FaceTerm lifted.mesh.triangles.length) //
    value = coordinates.faceResidualTerms}) ×
  {value : SignedFaceChartRequest lifted.mesh terms.val differential domains target polynomial //
    value = SignedFaceChartRequest.build lifted.mesh terms.val differential domains target positive polynomial}

/-- Prepare the actual signed face correction and its original chart request without constructing numerical readings. -/
def requestFaceResidual (polynomial : Option (Ordinary curve.polynomial) := none) :
    FaceResidualRequest coordinates differential domains target positive polynomial :=
  let original : {value : BasisCoordinates cut row // value = coordinates} := ⟨coordinates, rfl⟩
  let terms : {value : List (SewingRetraction.FaceTerm lifted.mesh.triangles.length) //
      value = coordinates.faceResidualTerms} := ⟨coordinates.faceResidualTerms, rfl⟩
  let requested : {value : SignedFaceChartRequest lifted.mesh terms.val differential domains target polynomial //
      value = SignedFaceChartRequest.build lifted.mesh terms.val differential domains target positive polynomial} :=
    ⟨SignedFaceChartRequest.build lifted.mesh terms.val differential domains target positive polynomial, rfl⟩
  ⟨original, terms, requested⟩

namespace FaceResidualRequest

variable {coordinates differential domains target positive}
variable {polynomial : Option (Ordinary curve.polynomial)}
variable (kept : FaceResidualRequest coordinates differential domains target positive polynomial)

/-- Read the same complete original coefficient owner. -/
@[expose] def original : BasisCoordinates cut row := kept.1.val

/-- Read the same literal source-minus-basis signed correction. -/
@[expose] def terms : List (SewingRetraction.FaceTerm lifted.mesh.triangles.length) := kept.2.1.val

/-- Read the same original chart request and its sufficient stage. -/
@[expose] def request : SignedFaceChartRequest lifted.mesh kept.terms differential domains target polynomial :=
  kept.2.2.val

/-- The complete coordinate owner retains its identity. -/
theorem original_eq : kept.original = coordinates := kept.1.property

/-- The signed list is the literal correction of that same coordinate owner. -/
theorem terms_eq : kept.terms = coordinates.faceResidualTerms := kept.2.1.property

/-- The chart request retains its complete original preparation factory. -/
theorem request_eq : kept.request =
    SignedFaceChartRequest.build lifted.mesh kept.terms differential domains target positive polynomial :=
  kept.2.2.property

/-- Every sufficiently late shared bank pays the complete face residual on its actual triangle readings. -/
theorem accurate
    (kept : FaceResidualRequest coordinates differential domains target positive)
    {stage : Nat} (later : kept.request.index ≤ stage)
    {shared : FacePrimitiveBank differential stage domains} (readings : TriangleReadings shared lifted.mesh) :
    normSq (coordinates.faceResidual (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)) < target := by
  have bounded := kept.request.accurate later readings
  have same := (congrArg (SewingRetraction.faceValue lifted.mesh.triangulation.faces
    (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)) kept.terms_eq).trans
      (coordinates.faceResidualTerms_value (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values))
  exact Eq.mp (congrArg (fun value : Canonical => normSq value < target) same) bounded

/-- The exact retained signed-face comparison data on the SAME supplied polynomial primitive bank. -/
@[expose] def Comparison {stage : Nat}
    (shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) : Type _ :=
  kept.request.Comparison shared

/-- Execute the original signed-face comparison once, retaining its actual per-occurrence common-model caches. -/
def compare {stage : Nat}
    (shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) :
    kept.Comparison shared := kept.request.compare shared

/-- The SAME retained polynomial comparisons internally pay the complete original correction value. -/
theorem comparison_accurate {stage : Nat} (later : kept.request.index ≤ stage)
    {shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    (compared : kept.Comparison shared) (readings : TriangleReadings shared lifted.mesh) :
    normSq (coordinates.faceResidual (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)) < target := by
  have bounded := kept.request.comparison_accurate later compared readings
  have same := (congrArg (SewingRetraction.faceValue lifted.mesh.triangulation.faces
    (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)) kept.terms_eq).trans
      (coordinates.faceResidualTerms_value (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values))
  exact Eq.mp (congrArg (fun value : Canonical => normSq value < target) same) bounded

end FaceResidualRequest

variable (minimum : Nat)

/-- The original coordinates, literal correction, signed-face request and its one actual numerical realization.

All preparatory factories are retained. The original request chooses its
sufficient stage before the given minimum is applied, and the resulting
face bank and triangle readings share that exact stage and mesh.
-/
abbrev FaceResidualPreparation (polynomial : Option (Ordinary curve.polynomial) := none) :=
  (requested : FaceResidualRequest coordinates differential domains target positive polynomial) ×
  (index : {value : Nat // value = max minimum requested.request.index}) ×
  (numerics : {value : FacePrimitiveBank differential index.val domains
    (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial) //
    value = FacePrimitiveBank.buildRequested differential index.val domains polynomial}) ×
  {value : TriangleReadings numerics.val lifted.mesh // value = TriangleReadings.build numerics.val lifted.mesh}

/-- Realize a given whole face request without unfolding its geometric producer during scalar stage inference. -/
private def withFaceResidualRequest {polynomial : Option (Ordinary curve.polynomial)}
    (requested : FaceResidualRequest coordinates differential domains target positive polynomial) :
    FaceResidualPreparation coordinates differential domains target positive minimum polynomial :=
  let index : {value : Nat // value = max minimum requested.request.index} :=
    ⟨max minimum requested.request.index, rfl⟩
  let numerics : {value : FacePrimitiveBank differential index.val domains
    (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial) //
      value = FacePrimitiveBank.buildRequested differential index.val domains polynomial} :=
    ⟨FacePrimitiveBank.buildRequested differential index.val domains polynomial, rfl⟩
  let readings : {value : TriangleReadings numerics.val lifted.mesh //
      value = TriangleReadings.build numerics.val lifted.mesh} :=
    ⟨TriangleReadings.build numerics.val lifted.mesh, rfl⟩
  ⟨requested, index, numerics, readings⟩

/-- Prepare the actual signed face correction and pay it with one original numerical bank and triangle reading cache.

The complete original coefficient owner and signed list remain data. The
original signed-face request derives every chart comparison and the finite
stage; no triangle-smallness or final residual bound is supplied by the caller.
-/
def prepareFaceResidual (polynomial : Option (Ordinary curve.polynomial) := none) :
    FaceResidualPreparation coordinates differential domains target positive minimum polynomial :=
  let requested := coordinates.requestFaceResidual differential domains target positive polynomial
  withFaceResidualRequest coordinates differential domains target positive minimum (polynomial := polynomial) requested

namespace FaceResidualPreparation

variable {coordinates differential domains target positive minimum}
variable {polynomial : Option (Ordinary curve.polynomial)}
variable (kept : FaceResidualPreparation coordinates differential domains target positive minimum polynomial)

/-- Read the same geometry-only request cache used before selecting and sampling the numerical bank. -/
@[expose] def requests : FaceResidualRequest coordinates differential domains target positive polynomial := kept.1

/-- Read the same complete original computed coefficient owner. -/
@[expose] def original : BasisCoordinates cut row := kept.requests.original

/-- Read the same literal signed face list supplied to the original chart request. -/
@[expose] def terms : List (SewingRetraction.FaceTerm lifted.mesh.triangles.length) := kept.requests.terms

/-- Read the same complete original signed-face request and its actual sufficient stage. -/
@[expose] def request : SignedFaceChartRequest lifted.mesh kept.terms differential domains target polynomial :=
  kept.requests.request

/-- Read the actual selected numerical stage, including the given lower floor. -/
@[expose] def index : Nat := kept.2.1.val

/-- Read the actual original face bank used by this preparation, with its exact stage and domain owners. -/
@[expose] def numerics : FacePrimitiveBank differential kept.index domains
    (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial) := kept.2.2.1.val

/-- Read the same triangle observations constructed from that one retained numerical bank. -/
@[expose] def readings : TriangleReadings kept.numerics lifted.mesh := kept.2.2.2.val

/-- The original basis coordinate cache retains its complete identity. -/
theorem original_eq : kept.original = coordinates := kept.requests.original_eq

/-- The retained list is exactly the original source-minus-basis correction, in its literal order. -/
theorem terms_eq : kept.terms = coordinates.faceResidualTerms := kept.requests.terms_eq

/-- The retained request is exactly its original signed-face preparation on these same terms and domains. -/
theorem request_eq : kept.request =
    SignedFaceChartRequest.build lifted.mesh kept.terms differential domains target positive polynomial :=
  kept.requests.request_eq

/-- The retained stage is exactly the given floor combined with the original request's own sufficient stage. -/
theorem index_eq : kept.index = max minimum kept.request.index := kept.2.1.property

/-- The retained numerical bank is its one original constructor at the actual selected stage. -/
theorem numerics_eq (kept : FaceResidualPreparation coordinates differential domains target positive minimum) :
    kept.numerics = FacePrimitiveBank.build differential kept.index domains :=
  kept.2.2.1.property.trans (FacePrimitiveBank.buildRequested_none differential kept.index domains)

/-- The actual selected numerator branch retains its whole original bank construction factory. -/
theorem numerics_requested_eq : kept.numerics =
    FacePrimitiveBank.buildRequested differential kept.index domains polynomial := kept.2.2.1.property

/-- The triangle observations retain their entire original bank and mesh factory. -/
theorem readings_eq : kept.readings = TriangleReadings.build kept.numerics lifted.mesh := kept.2.2.2.property

/-- The actual selected stage pays the original signed-face request. -/
theorem request_later : kept.request.index ≤ kept.index :=
  (Nat.Order.le_max_right minimum kept.request.index).trans_eq kept.index_eq.symm

/-- The actual selected stage meets the supplied numerical floor. -/
theorem minimum_le : minimum ≤ kept.index :=
  (Nat.Order.le_max_left minimum kept.request.index).trans_eq kept.index_eq.symm

/-- The actual retained canonical cochain pays the full source-minus-basis face residual internally.

The original signed-face request supplies its numerical triangle estimates.
The literal correction readback transports its strict bound to the complete
face residual; physical loops and annular corrections keep their own values.
-/
theorem accurate
    (kept : FaceResidualPreparation coordinates differential domains target positive minimum) :
    normSq (coordinates.faceResidual
    (CanonicalEdgeValues.edgeValuation lifted.mesh kept.readings.values)) < target :=
  kept.requests.accurate kept.request_later kept.readings

/-- The actual signed-face comparison cache on this SAME retained numerical bank. -/
@[expose] def Comparison : Type _ := kept.requests.Comparison kept.numerics

/-- Execute the retained signed-face comparison once on this preparation's exact primitive bank. -/
def compare : kept.Comparison := kept.requests.compare kept.numerics

/-- The SAME retained polynomial comparisons pay the original face residual on these actual observations. -/
theorem comparison_accurate (compared : kept.Comparison) :
    normSq (coordinates.faceResidual
      (CanonicalEdgeValues.edgeValuation lifted.mesh kept.readings.values)) < target :=
  kept.requests.comparison_accurate kept.request_later compared kept.readings

end FaceResidualPreparation

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows.BasisCoordinates
