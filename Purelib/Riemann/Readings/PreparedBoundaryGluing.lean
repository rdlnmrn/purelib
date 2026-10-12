module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive
import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Cache
public import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation

public section

/-!
# Sequential operational preparation around a finite branch boundary tour

One initial root owner determines all four prepared pieces: connector,
right owner boundary, reversed connector, and left owner boundary.  Their
three internal root-owner handoffs are exact, with each prepared spine
cached before it is reused.  This removes independent intermediate owner
choices; it does not yet prove final-to-initial root monodromy or the global
symplectic cut-surface identification.
-/

namespace Purelib.Riemann.Readings.PreparedBoundaryGluing

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.Paths
open Purelib.Curves.Hyperelliptic

set_option backward.match.sparseCases false

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
open Purelib.Riemann.Topology.PreparedCycleModels (Owner PreparedBoundaryDoublePath)

set_option genInjectivity false in
/-- A certified dyadic path bank with its retained terminal root owner.

The finishing owner is tied by an exact equality to the bank's own prepared path; the selected depth and positive
diameter remain those of the checked bank. -/
structure FinishedDyadic {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Purelib.Geometry.Rational.Box}
    {start finish : Basic.Canonical} (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (owner : Owner (polynomial.eval start)) (diameter : Fraction.Rational) (positive : 0 < diameter) where
  /-- The retained dyadic depth of the certified path bank. -/ depth : Nat
  /-- The exact certified bank for the original path, starting owner and diameter. -/ certificate :
    PreparedClearPathModels.PreparedPath.CertifiedDyadic
    depth diameter positive path owner
  /-- The retained root owner at the exact final parameter. -/ finishOwner : Owner (polynomial.eval finish)
  /-- The retained final owner is exactly the terminal owner of the prepared bank. -/ finishOwner_eq : finishOwner =
    PreparedPathGluing.finishOwner certificate.prepared

constructive_injectivity FinishedDyadic

namespace FinishedDyadic

open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.Paths
open Purelib.RootIsolation

/-- Prepare and cache one path bank at an adaptively selected depth.

The supplied positive diameter and starting owner determine the task; the result retains the cached certificate and its
exact terminal owner. -/
@[expose] def total {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient
  : Purelib.Geometry.Rational.Box} {start
  finish : Basic.Canonical}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) (within : path.WithinAmbient)
    (owner : Owner (polynomial.eval start)) (diameter : Fraction.Rational) (positive : 0 < diameter) :
    FinishedDyadic path owner diameter positive :=
  let selected := SquareRoot.Preparation.Bank.Adaptive.select [SquareRoot.Preparation.Bank.Adaptive.Task.ofPath path
    within owner]
    diameter positive
  let certificate := SquareRoot.Preparation.Bank.Cache.DyadicBank.cache selected.banks.head
  ⟨selected.depth, certificate, PreparedPathGluing.finishOwner certificate.prepared, rfl⟩

end FinishedDyadic

set_option genInjectivity false in
/-- Four retained boundary-cycle banks joined by their exact terminal owners.

Three owner equalities link successive banks, and the final owner is identified with the terminal owner of the left
boundary bank. -/
structure JoinedBoundaryDoublePath {genus : Nat} (curve : Basic.HyperellipticCurve genus) where
  /-- The original four-bank prepared boundary-cycle data. -/ data : PreparedBoundaryDoublePath curve
  /-- The right boundary starts at the exact terminal owner of the forward connector. -/ rightOwner_eq :
    data.rightBoundaryOwner = PreparedPathGluing.finishOwner data.forward
  /-- The reverse connector starts at the exact terminal owner of the right boundary. -/ backwardOwner_eq :
    data.backwardOwner = PreparedPathGluing.finishOwner data.rightBoundary
  /-- The left boundary starts at the exact terminal owner of the reverse connector. -/ leftOwner_eq :
    data.leftBoundaryOwner = PreparedPathGluing.finishOwner data.backward
  /-- The retained root owner at the exact final parameter. -/ finishOwner : Owner (curve.polynomial.eval
    data.leftState.box.anchor)
  /-- The retained final owner is exactly the terminal owner of the prepared bank. -/ finishOwner_eq : finishOwner =
    PreparedPathGluing.finishOwner data.leftBoundary

constructive_injectivity JoinedBoundaryDoublePath

namespace JoinedBoundaryDoublePath

open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Riemann.Topology

/-- Assemble the supplied four finished banks with their exact sequential owner links.

The resulting boundary data keeps all original certificates, selected depths and shared positive diameter; no bank or
terminal owner is recomputed. -/
@[expose] def ofFinished {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {leftAmbient rightAmbient connectorAmbient : Purelib.Geometry.Rational.Box}
    (leftState : State.WindingOne.Basic.WindingOneState curve.polynomial leftAmbient)
    (rightState : State.WindingOne.Basic.WindingOneState curve.polynomial rightAmbient)
    (connector : Polynomial.Geometry.ClearPath curve.polynomial connectorAmbient leftState.box.anchor
      rightState.box.anchor)
    (owner : Owner (curve.polynomial.eval leftState.box.anchor))
    (diameter : Fraction.Rational) (positive : 0 < diameter)
    (forward : FinishedDyadic connector owner diameter positive)
    (right : FinishedDyadic (BranchCutLifts.ownerBoundaryPath rightState) forward.finishOwner diameter positive)
    (backward : FinishedDyadic (BranchCutLifts.ClearPath.reverse connector) right.finishOwner diameter positive)
    (left : FinishedDyadic (BranchCutLifts.ownerBoundaryPath leftState) backward.finishOwner diameter positive) :
      JoinedBoundaryDoublePath curve :=
  let rightPath := BranchCutLifts.ownerBoundaryPath rightState
  let leftPath := BranchCutLifts.ownerBoundaryPath leftState
  let rightOwner := forward.finishOwner
  let backwardOwner := right.finishOwner
  let leftOwner := backward.finishOwner
  let data : PreparedBoundaryDoublePath curve :=
    { leftAmbient := leftAmbient
      rightAmbient := rightAmbient
      connectorAmbient := connectorAmbient
      leftState := leftState
      rightState := rightState
      connector := connector
      rightBoundaryPath := rightPath
      leftBoundaryPath := leftPath
      forwardDepth := forward.depth
      rightBoundaryDepth := right.depth
      backwardDepth := backward.depth
      leftBoundaryDepth := left.depth
      rootDiameter := diameter
      rootDiameterPositive := positive
      forwardOwner := owner
      forwardChecked := .certified forward.certificate
      rightBoundaryOwner := rightOwner
      rightBoundaryChecked := .certified right.certificate
      backwardOwner := backwardOwner
      backwardChecked := .certified backward.certificate
      leftBoundaryOwner := leftOwner
      leftBoundaryChecked := .certified left.certificate }
  { data := data
    rightOwner_eq := forward.finishOwner_eq
    backwardOwner_eq := right.finishOwner_eq
    leftOwner_eq := backward.finishOwner_eq
    finishOwner := left.finishOwner
    finishOwner_eq := left.finishOwner_eq }

/-- Prepare the ordered boundary-cycle banks by passing each bank's actual terminal owner to the next.

The forward connector, right boundary, reverse connector and left boundary are prepared sequentially, retaining each
selected depth and exact endpoint-owner link. -/
@[expose] def total {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {leftAmbient rightAmbient connectorAmbient : Purelib.Geometry.Rational.Box}
    (leftState : State.WindingOne.Basic.WindingOneState curve.polynomial leftAmbient)
    (rightState : State.WindingOne.Basic.WindingOneState curve.polynomial rightAmbient)
    (connector : Polynomial.Geometry.ClearPath curve.polynomial connectorAmbient leftState.box.anchor
      rightState.box.anchor)
    (within : connector.WithinAmbient) (owner : Owner (curve.polynomial.eval leftState.box.anchor))
    (diameter : Fraction.Rational) (positive : 0 < diameter) : JoinedBoundaryDoublePath curve :=
  let forward := FinishedDyadic.total connector within owner diameter positive
  let right := FinishedDyadic.total (BranchCutLifts.ownerBoundaryPath rightState)
    (BranchCutLifts.ownerBoundaryPath_withinAmbient rightState)
    forward.finishOwner diameter positive
  let backward := FinishedDyadic.total (BranchCutLifts.ClearPath.reverse connector)
    (BranchCutLifts.ClearPath.reverse_withinAmbient connector within) right.finishOwner diameter positive
  let left := FinishedDyadic.total (BranchCutLifts.ownerBoundaryPath leftState)
    (BranchCutLifts.ownerBoundaryPath_withinAmbient leftState)
    backward.finishOwner diameter positive
  ofFinished leftState rightState connector owner diameter positive forward right backward left

/-- Prepare the branch connector's joined boundary cycle at the retained refinement index.

The original left and right branch states determine both boundary paths, and the independent initial root owner is
selected at the connector's exact start. -/
@[expose] def ofConnectorAt {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : BranchIsolation.Data.Index branches) (refinement : Nat) : JoinedBoundaryDoublePath curve :=
  let startNonzero := Cuts.connectorAt_start_eval_ne_zero branches degreeGtOne left right refinement
  total (Cuts.refinedState branches degreeGtOne left refinement) (Cuts.refinedState branches degreeGtOne right
    refinement)
    (Cuts.connectorAt branches degreeGtOne left right refinement)
    (Cuts.connectorAt_withinAmbient branches degreeGtOne left right refinement)
    (SquareRootContinuationChain.Owner.independent startNonzero 0) 1 (by decide)

end JoinedBoundaryDoublePath

end Purelib.Riemann.Readings.PreparedBoundaryGluing
