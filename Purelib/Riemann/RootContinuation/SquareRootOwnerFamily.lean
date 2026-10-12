module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Power.Isolation
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.FTA.Squarefree.Basic

import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
public import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.RootContinuation.SquareRootDegree

@[expose] public section

/-!
Retain one complete canonical quadratic isolation result for both sheets.
This caches executable data, not just a proposition about recomputation.
Projection preserves each original canonical owner exactly; there is no
relabeling, independently chosen box or new root-selection convention.
-/

namespace Purelib.Riemann.RootContinuation.SquareRootOwnerFamily

open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

open Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.Riemann.RootContinuation.SquareRootDegree (degreeTwo degreeTwo_atLeastTwo)
open Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance.Owner (accelerateTrack)

open Purelib.Polynomial.Power in
open Purelib.RootIsolation in
set_option genInjectivity false in
/-- One cached original quadratic isolation result supplying both independent square-root owners.

The record keeps the nonzero parameter certificate and an exact equation to the original degree-two isolation
construction, so both sheets reuse that same retained result. -/
structure IndependentFamily (parameter : Gaussian) where
  /-- The original parameter is certified nonzero. -/ parameterNonzero : parameter ≠ 0
  /-- The retained degree-two isolation result shared by the original two sheet owners. -/ result :
    FTA.Squarefree.AdapterResult (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degreeTwo)
  /-- The retained result is exactly the original quadratic isolation construction for this certificate. -/ result_eq :
    result = Power.Isolation.isolationResult parameterNonzero degreeTwo degreeTwo_atLeastTwo

constructive_injectivity IndependentFamily

open Purelib.RootIsolation in
/-- Cache the original degree-two isolation result once for a certified nonzero parameter. -/
def independentFamily {parameter : Gaussian} (nonzero : parameter ≠ 0) : IndependentFamily parameter where
  parameterNonzero := nonzero
  result := Power.Isolation.isolationResult nonzero degreeTwo degreeTwo_atLeastTwo
  result_eq := rfl

open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Polynomial.Power in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Read the original independent square-root owner for the retained sheet from the shared isolation result.

The exact degree cast selects its original track, whose acceleration and root-radius ambient box agree with the
established owner construction. -/
def IndependentFamily.owner {parameter : Gaussian} (family : IndependentFamily parameter)
    (sheet : Fin 2) : Owner parameter where
  parameterNonzero := family.parameterNonzero
  ambient := Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degreeTwo)
  track := QuadraticLineClearance.Owner.accelerateTrack parameter
    (family.result.trackAt (Fin.cast (Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree parameter degreeTwo).symm
      sheet))

open Purelib.Riemann.Topology
/-- The family sheet owner equals the original independent owner for the same nonzero parameter certificate. -/
theorem IndependentFamily.owner_eq_independent {parameter : Gaussian}
    (family : IndependentFamily parameter) (sheet : Fin 2) :
    family.owner sheet = SquareRootContinuationChain.Owner.independent family.parameterNonzero sheet := by
  cases family with
  | mk nonzero result same => cases same; rfl

/-- Building and selecting a family sheet recovers the exact original independent square-root owner. -/
theorem independentFamily_owner {parameter : Gaussian} (nonzero : parameter ≠ 0) (sheet : Fin 2) :
    (independentFamily nonzero).owner sheet = SquareRootContinuationChain.Owner.independent nonzero sheet := rfl

end Purelib.Riemann.RootContinuation.SquareRootOwnerFamily
