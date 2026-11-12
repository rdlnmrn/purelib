module

import Purelib.RootIsolation.FTA.Squarefree.Build

/-!
# Complete original squarefree preparation regressions

Restored elimination and isolation values feed the original numerical FTA
record without recomputation. The complete result and every original track's
Newton refinement remain linked to their canonical constructors.
-/

namespace TestPurelib.RootIsolation.FTA.Squarefree

open Purelib
open Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Polynomial.Dense.Gaussian.Bounds.RootRadius
open RootIsolation.FTA.Squarefree
open RootIsolation.Track.Newton

/-- The complete cached numerical result retains the supplied original isolation verbatim. -/
private theorem retained_isolation {source : CoefficientPolynomial} {input : Input source}
    (prepared : Input.Prepared input) : (Build.BoxFTA.ofPrepared prepared).isolation = prepared.isolation := rfl

/-- Checked original isolation restoration agrees with the complete original numerical result and owner procedure. -/
private theorem restored_complete {source : CoefficientPolynomial} (input : Input source)
    (elimination : AxisEliminationCertificate source input.eliminationDegree)
    (eliminationEq : elimination = input.elimination)
    (isolation : RootIsolation.Exact.Basic.Output source (Box.largeSquareBox source) source.natDegree)
    (isolationEq : isolation = RootIsolation.Exact.LargeSquare.isolateLargeSquare
      input.degreeAtLeastTwo input.squarefree elimination) :
    Build.BoxFTA.ofPrepared (Input.Prepared.ofIsolation input elimination eliminationEq isolation isolationEq) =
      Build.BoxFTA.prove input :=
  Build.BoxFTA.ofPrepared_eq_prove _

/-- Every retained original track evaluates the same Newton refinement at an arbitrary finite request. -/
private theorem retained_track_refiner {source : CoefficientPolynomial} {input : Input source}
    (prepared : Input.Prepared input) (index : Fin prepared.isolation.tracks.length)
    (current : RootIsolation.State.WindingOne.Basic.WindingOneState source (Box.largeSquareBox source))
    (epsilon : Data.Rat.Fraction.Rational) (positive : 0 < epsilon) :
    (prepared.isolation.tracks.get index).refine current epsilon positive =
      Refinement.refineState input.degreeAtLeastTwo input.squarefree prepared.elimination current epsilon positive :=
  congrArg (fun refine => refine current epsilon positive)
    (prepared.refine _ (List.get_mem _ index))

end TestPurelib.RootIsolation.FTA.Squarefree
