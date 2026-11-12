module

public import scripts.checkpoint.RawSubdivision
import Purelib.System.FilePath

/-! # Checked dyadic refinement from an original raw owner -/

public section

namespace RawRefinementCheckpoint

open Purelib
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Data (Json)
open Purelib.Data.Json (toJson)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.System.FilePath (join)
open IntegrationCheckpoint (fractionData gaussianData loadJson saveJson profile)

variable {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}

/-- Bind the original raw source and accuracy independently of canonical extraction checkpoints.

The exact coefficients, ambient, source box, clearance and eliminants identify
this request. A saved replay requires its existing header; a missing or
mismatched header retains the attempted data before returning an IO error.
-/
private def bindRequest (savedOnly : Bool) (directory : System.FilePath)
    (elimination : AxisEliminationCertificate polynomial degreeBound)
    (current : State.Raw.RawWindingState polynomial ambient) (epsilon : Rational) : IO Unit := do
  IO.FS.createDirAll directory
  let header := Json.mkObj
    [("protocol", toJson "raw-dyadic-candidate-newton-refinement-v1"),
      ("polynomial", toJson (polynomial.coeffs.map gaussianData)),
      ("ambient", toJson (RootStateCheckpoint.boxData ambient)),
      ("current", toJson (RootStateCheckpoint.boxData current.box)),
      ("boundary", toJson (fractionData current.clearance.bound)),
      ("epsilon", toJson (fractionData epsilon)), ("proposals", toJson (6 : Nat)),
      ("eliminationDegreeBound", toJson degreeBound),
      ("verticalEliminant", toJson (WindingCheckpoint.polynomialData elimination.vertical)),
      ("horizontalEliminant", toJson (WindingCheckpoint.polynomialData elimination.horizontal))]
  let path := join directory "request.json"
  if ← path.pathExists then
    let stored : Json ← loadJson path
    unless stored == header do
      saveJson (join directory "invalid-request.json") (stored, header)
      throw (IO.userError "saved raw dyadic request differs; exact records retained")
  else if savedOnly then
    saveJson (join directory "missing-request.json") header
    throw (IO.userError "missing raw dyadic request; header generation forbidden")
  else saveJson path header

/-- Restore the complete raw-owner refinement without a preliminary canonical extraction.

Six checked dyadic proposals use the actual supplied raw source and request.
Finite rejection alone selects the existing total extraction on those same
inputs. Both branches retain whole-result equality to the pure policy; column,
winding and header controls separately govern saved execution.
-/
def refine (input : FTA.Squarefree.Input polynomial)
    (elimination : AxisEliminationCertificate polynomial input.eliminationDegree)
    (same : elimination = input.elimination)
    (loader : RootRefinementCheckpoint.ClearanceLoader elimination (.canonical elimination) IO)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (savedOnly : Bool) (directory : System.FilePath)
    (current : State.Raw.RawWindingState polynomial ambient) (epsilon : Rational) (positive : 0 < epsilon) :
    IO { value : Refinement current epsilon // value =
      Newton.Search.Dyadic.refineRaw input elimination current epsilon positive } := do
  bindRequest savedOnly directory elimination current epsilon
  let candidate ← RawSubdivisionCheckpoint.attemptDyadic elimination loader winding
    (join directory "candidates") current epsilon
  match found : candidate.val with
  | some accepted =>
      return ⟨accepted, (Newton.Search.Dyadic.refineRaw_accept input elimination current epsilon positive
        accepted (candidate.property.symm.trans found)).symm⟩
  | none =>
      profile directory "FALLBACK after finite raw dyadic candidate attempt"
      let band ← RawSubdivisionCheckpoint.band input elimination same loader columns winding
        (join directory "fallback") current epsilon positive
      let result := Newton.Band.State.refinementOfOutput band.val
      return ⟨result, (congrArg (fun value : Newton.Band.Basic.Output input.squarefree current epsilon =>
        Newton.Band.State.refinementOfOutput value) band.property).trans
          (Newton.Search.Dyadic.refineRaw_fallback input elimination current epsilon positive
            (candidate.property.symm.trans found)).symm⟩

end RawRefinementCheckpoint
