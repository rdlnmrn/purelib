module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.LiftedCells.Certificates
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootClosedState
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain.Parents
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # The original cap refinement state on the same retained cached path

The existing root-safe refinement interface reads exactly the path already
assembled from the retained lifted cells. This comparison retains both
original inputs and their full factory identities.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive.LiftedCells

open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1}
    {error : Coordinate} {errorPositive : 0 < error} {floor : Nat}

/-- The original-parent refinement state follows the same supplied cached lifted path.

The state and path share the literal original cap parent list. Actual root
return remains the separate rootClosedState construction's roots field;
this equality only identifies the ordered lifted geometry.
-/
theorem state_path_eq
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval collar.box.anchor)}
    (closed : Boundary.Data cap owner sourceDifferential)
    (planned : Plan error errorPositive floor closed.covered.bank)
    (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := 1)
      (error := error) (errorPositive := errorPositive) (floor := floor) closed.covered.bank planned)
    (factory : paths = build closed.covered.bank planned)
    (keptPath : LiftedPath 2 (⟨collar.box.anchor, 0⟩ : LiftedPoint 2) ⟨collar.box.anchor, 0⟩)
    (pathFactory : keptPath = path closed.covered.bank planned paths factory closed.covered.cache.chain) :
    (Boundary.state closed).path = keptPath :=
  (Boundary.state_path closed).trans
    ((path_eq closed.covered.bank planned paths factory
      (CenteredPathChain.ofParents closed.covered.cache.parents closed.covered.cache.chain)).symm.trans
        pathFactory.symm)

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive.LiftedCells

end
