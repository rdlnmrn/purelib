module

public import Purelib.RootIsolation.CCL.Persistent.Terminal.Observation

/-! # Quantified preparation replay and wrong-point evaluator replies -/

namespace TestPurelib.RootIsolation.CCL.Persistent.Terminal.Observation

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Evaluation (Reading)
open Purelib.RootIsolation
open Purelib.RootIsolation.CCL.Persistent.Terminal

/-- All original winding owners and persistent prefixes retain the complete original certified preparation on replay. -/
public theorem original_preparation_replayed {p : CoefficientPolynomial} {ambient : Box}
    (positive : 0 < p.natDegree) (track : Track.Basic.WindingOneTrack p ambient)
    (current : CCL.Persistent.State p ambient) :
    (Observation.prepare positive track current).replayExact
      (Observation.recordPreparation positive track current).trace =
      .ok (.ok (Prepare.prepare positive track current)) :=
  Observation.preparation_replay positive track current

/-- Check that the actual evaluator returns its cache and a reply for another point retains its invalidity reason. -/
public def run : IO Unit := do
  let polynomial : CoefficientPolynomial := ⟨[1, 0, -2]⟩
  let correct := (Reading.request polynomial 0).run (Reading.ofPoint polynomial)
  match correct.value with
  | .ok retained =>
      unless decide (retained.val.value = (-2 : Canonical)) && correct.trace.length == 1 do
        throw (IO.userError "polynomial query lost its original cached value or actual request")
  | .error _ => throw (IO.userError "polynomial query rejected its original evaluator")
  let wrong := (Reading.request polynomial 1).run (fun _ => Reading.ofPoint polynomial 0)
  match wrong.value with
  | .ok _ => throw (IO.userError "polynomial query accepted a value for a different point")
  | .error mismatch =>
      unless decide (mismatch.expected = 1) && decide (mismatch.reported = 0) do
        throw (IO.userError "polynomial query lost its exact requested and mismatched points")
  IO.print "terminal preparation coverage: original owner replay and certified wrong-point rejection passed\n"

end TestPurelib.RootIsolation.CCL.Persistent.Terminal.Observation
