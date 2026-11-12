module
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Riemann.Readings.PreparedPrimitiveSamples.Numerator

public import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words
public import Purelib.Topology.Mesh.QuadrilateralDual.Values
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedFaceChartRequests
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Topology.Polygon.Stokes
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.Data.Vector.Dependent

/-! # Requested analytic payment of actual compiled annular corrections

The retained mesh lookups already locate both triangles of every signed
regular occurrence. Their literal face list feeds the original signed-face
request; later numerical readings may be shared with other residual requests.
-/

public section

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement.Compilation

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellBank (ClearancePreparation)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Riemann.Readings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedFaceChartRequests (SignedFaceChartRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Indexed (sumFin_map)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector (DependentVector)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {original : LiftedPuncturedGrid base}
    {patches : List (ContinuedNeighborhood curve.polynomial count)}
    {prepared : ClearancePreparation base.bank.toBranchCellBank patches}
    {retained : ClearanceRefinement original prepared}
    {oldBank : BasedBranchBank original} {newBank : BasedBranchBank retained.fine}
    {annulusSheet stripSheet sheet : Fin 2}
    {annuli : DependentVector (fun index : Data.Index branches =>
      {value : retained.Annulus index annulusSheet // value = retained.annulus index annulusSheet})}
    {strips : DependentVector (fun index : Data.Index branches =>
      {value : retained.StemStrip oldBank newBank (annuli.get index).val stripSheet //
        value = retained.stemStrip oldBank newBank (annuli.get index).val stripSheet})}
    {labels : List (Data.Index branches)} (source : retained.Compilation oldBank newBank annuli strips labels sheet)

/-- The original globally compiled regular occurrences supply their exact cached two-triangle terms in order.

Every occurrence keeps its original arriving sheet and retained LocatedFace.
No face lookup, circuit compilation, root selection or triangulation runs
again to construct this list.
-/
@[expose] def correctionTerms : List (SewingRetraction.FaceTerm retained.fine.mesh.triangles.length) :=
  (List.ofFn (fun position : Fin source.compiled.regulars.length =>
    (source.corrections.correction (retained := retained) (compiled := source.compiled)
      position).occurrence.faceTerms)).flatten

/-- The complete literal triangle list reads exactly the original globally compiled regular correction sum. -/
theorem correctionTerms_value (reading : OrientedEdge retained.fine.vertices.count → Canonical)
    (anti : ∀ edge, reading edge.reverse = -reading edge) :
    SewingRetraction.faceValue retained.fine.mesh.triangulation.faces reading source.correctionTerms =
      CellBoundary.sumValues (fun occurrence => SewingRetraction.wordValue reading occurrence.word)
        source.compiled.regulars := by
  have original := SewingRetraction.faceValue_flatten_ofFn retained.fine.mesh.triangulation.faces reading
    (fun position : Fin source.compiled.regulars.length =>
      (source.corrections.correction (retained := retained) (compiled := source.compiled)
        position).occurrence.faceTerms)
  have actual := sumFin_congr (fun position : Fin source.compiled.regulars.length =>
    ((source.corrections.correction (retained := retained) (compiled := source.compiled)
      position).occurrence.faceTerms_value reading anti).trans
        (congrArg (SewingRetraction.wordValue reading) (source.correction_boundary position)))
  have indexed := (sumFin_map source.compiled.regulars
    (fun occurrence => SewingRetraction.wordValue reading occurrence.word)).trans
      (CellBoundary.sumValues_eq_gaussianSum_map
        (fun occurrence => SewingRetraction.wordValue reading occurrence.word) source.compiled.regulars).symm
  exact original.trans (actual.trans indexed)

variable (differential : Differential genus)
variable (domains : FaceDomainBank retained.fine.frames retained.fineBase.faces.regulars)
variable (target : Rational) (positive : 0 < target)

/-- The original compilation, actual triangle list and one original signed-face request with complete factories. -/
abbrev CorrectionRequest (polynomial : Option (Ordinary curve.polynomial) := none) :=
  {_value : retained.Compilation oldBank newBank annuli strips labels sheet // _value = source} ×
  (terms : {value : List (SewingRetraction.FaceTerm retained.fine.mesh.triangles.length) //
    value = source.correctionTerms}) ×
  {value : SignedFaceChartRequest retained.fine.mesh terms.val differential domains target polynomial //
    value = SignedFaceChartRequest.build retained.fine.mesh terms.val differential domains target positive polynomial}

/-- Select the actual annular correction requests and sufficient stage before numerical sampling.

The existing signed-face operation derives its own triangle comparisons.
The resulting request can consume the same later bank and readings as
physical-loop and source/basis face requests.
-/
def requestCorrections (polynomial : Option (Ordinary curve.polynomial) := none) :
    CorrectionRequest source differential domains target positive polynomial :=
  let original : {value : retained.Compilation oldBank newBank annuli strips labels sheet // value = source} :=
    ⟨source, rfl⟩
  let terms : {value : List (SewingRetraction.FaceTerm retained.fine.mesh.triangles.length) //
      value = source.correctionTerms} := ⟨source.correctionTerms, rfl⟩
  let requested : {value : SignedFaceChartRequest retained.fine.mesh terms.val differential domains target polynomial //
      value = SignedFaceChartRequest.build retained.fine.mesh terms.val differential domains target positive
        polynomial} :=
    ⟨SignedFaceChartRequest.build retained.fine.mesh terms.val differential domains target positive polynomial, rfl⟩
  ⟨original, terms, requested⟩

namespace CorrectionRequest

variable {source differential domains target positive}
variable {polynomial : Option (Ordinary curve.polynomial)}
variable (kept : CorrectionRequest source differential domains target positive polynomial)

/-- Read the same complete original word/compilation/location cache. -/
@[expose] def compilation : retained.Compilation oldBank newBank annuli strips labels sheet := kept.1.val

/-- Read the same actual signed triangle terms used by this request. -/
@[expose] def terms : List (SewingRetraction.FaceTerm retained.fine.mesh.triangles.length) := kept.2.1.val

/-- Read the same original signed-face chart request, including its actual sufficient stage. -/
@[expose] def request : SignedFaceChartRequest retained.fine.mesh kept.terms differential domains target polynomial :=
  kept.2.2.val

/-- The original complete compilation/location owner remains unchanged. -/
theorem compilation_eq : kept.compilation = source := kept.1.property

/-- The retained triangle list comes from the original cached quadrilateral occurrences. -/
theorem terms_eq : kept.terms = source.correctionTerms := kept.2.1.property

/-- The whole request is the original constructor on that actual triangle list and the same domains. -/
theorem request_eq : kept.request =
    SignedFaceChartRequest.build retained.fine.mesh kept.terms differential domains target positive polynomial :=
  kept.2.2.property

/-- The actual regular correction sum is below its requested target on every sufficiently late shared bank.

The chart request supplies the triangle bounds internally. The original
quadrilateral incidence and signed correction readback transport that bound
to the actual compiled regular occurrences, without changing their sheets.
-/
theorem accurate
    (kept : CorrectionRequest source differential domains target positive)
    {stage : Nat} (later : kept.request.index ≤ stage)
    {numerics : FacePrimitiveBank differential stage domains}
    (readings : TriangleReadings numerics retained.fine.mesh) :
    normSq (CellBoundary.sumValues (fun occurrence => SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation retained.fine.mesh readings.values) occurrence.word)
        source.compiled.regulars) < target := by
  have bounded := kept.request.accurate later readings
  have same := (congrArg (SewingRetraction.faceValue retained.fine.mesh.triangulation.faces
    (CanonicalEdgeValues.edgeValuation retained.fine.mesh readings.values)) kept.terms_eq).trans
      (source.correctionTerms_value (CanonicalEdgeValues.edgeValuation retained.fine.mesh readings.values)
        (CanonicalEdgeValues.edgeValuation_reverse retained.fine.mesh readings.values))
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
    {numerics : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    (compared : kept.Comparison numerics) (readings : TriangleReadings numerics retained.fine.mesh) :
    normSq (CellBoundary.sumValues (fun occurrence => SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation retained.fine.mesh readings.values) occurrence.word)
        source.compiled.regulars) < target := by
  have bounded := kept.request.comparison_accurate later compared readings
  have same := (congrArg (SewingRetraction.faceValue retained.fine.mesh.triangulation.faces
    (CanonicalEdgeValues.edgeValuation retained.fine.mesh readings.values)) kept.terms_eq).trans
      (source.correctionTerms_value (CanonicalEdgeValues.edgeValuation retained.fine.mesh readings.values)
        (CanonicalEdgeValues.edgeValuation_reverse retained.fine.mesh readings.values))
  exact Eq.mp (congrArg (fun value : Canonical => normSq value < target) same) bounded

end CorrectionRequest

end Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement.Compilation
