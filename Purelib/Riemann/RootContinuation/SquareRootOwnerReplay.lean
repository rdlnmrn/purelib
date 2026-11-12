module
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Power.Isolation
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.FTA.Squarefree.Build
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.Exact.Ownership.Prepare

public import Purelib.Riemann.RootContinuation.SquareRootOwnerFamily

@[expose] public section

/-!
Restore the original two-sheet family from its exact ordered isolation.
The eliminant, owner numbering and accelerated refinement functions are the
canonical ones.  The isolation equation is supplied by the finite replay
checker, not inferred from a valid box or a numerical root approximation.
Only the existing finite owner and isolation dependencies are used.
-/

namespace Purelib.Riemann.RootContinuation.SquareRootOwnerReplay

open Purelib.Riemann.RootContinuation.SquareRootOwnerFamily

open Purelib.Riemann.RootContinuation.SquareRootDegree (degreeTwo degreeTwo_atLeastTwo)
open Purelib.Riemann.RootContinuation.SquareRootOwnerFamily (IndependentFamily)

variable {parameter : Data.Gaussian.Basic.Canonical} (nonzero : parameter ≠ 0)

open Purelib.RootIsolation in
/-- The canonical executable two-root isolation input for the original nonzero parameter. -/
def input := Power.Isolation.isolationInput nonzero degreeTwo degreeTwo_atLeastTwo

section
open Purelib.Polynomial
open Purelib.RootIsolation
/-- Rebuild the finite square-root family result using the supplied ordered isolation.

The original input retains the eliminant, ownership selection and maximality witness while the supplied isolation
provides the executable root entries. -/
def result (isolation : Exact.Basic.Output (Power.Gaussian.rootPolynomial parameter degreeTwo)
    (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Power.Gaussian.rootPolynomial parameter
      degreeTwo))
    (Power.Gaussian.rootPolynomial parameter degreeTwo).natDegree) :
    FTA.Squarefree.AdapterResult (Power.Gaussian.rootPolynomial parameter degreeTwo) :=
  let source := input nonzero
  ⟨FTA.Squarefree.Build.BoxFTA.fromIsolation source isolation⟩

/-- An exact original isolation readback identifies the reconstructed finite family result. -/
theorem result_eq (isolation : Exact.Basic.Output (Power.Gaussian.rootPolynomial parameter degreeTwo)
    (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Power.Gaussian.rootPolynomial parameter
      degreeTwo))
    (Power.Gaussian.rootPolynomial parameter degreeTwo).natDegree)
    (same : isolation = (input nonzero).isolation) :
    result nonzero isolation = Power.Isolation.isolationResult nonzero degreeTwo degreeTwo_atLeastTwo := by
  exact congrArg FTA.Squarefree.AdapterResult.mk
    (FTA.Squarefree.Build.BoxFTA.fromIsolation_eq_prove (input nonzero) isolation same)

/-- Restore the original independent two-sheet owner family from its exact ordered isolation.

The nonzero parameter, owner numbering and canonical refinement operations retain their original identities. -/
def family (isolation : Exact.Basic.Output (Power.Gaussian.rootPolynomial parameter degreeTwo)
    (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Power.Gaussian.rootPolynomial parameter
      degreeTwo))
    (Power.Gaussian.rootPolynomial parameter degreeTwo).natDegree)
    (same : isolation = (input nonzero).isolation) : IndependentFamily parameter where
  parameterNonzero := nonzero
  result := result nonzero isolation
  result_eq := result_eq nonzero isolation same

end

open Purelib.Riemann in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- The restored family equals the complete original independent square-root family. -/
theorem family_eq (isolation : Exact.Basic.Output (Power.Gaussian.rootPolynomial parameter degreeTwo)
    (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Power.Gaussian.rootPolynomial parameter
      degreeTwo))
    (Power.Gaussian.rootPolynomial parameter degreeTwo).natDegree)
    (same : isolation = (input nonzero).isolation) :
    family nonzero isolation same = independentFamily nonzero := by
  have restored := result_eq nonzero isolation same
  exact (IndependentFamily.mk.injEq nonzero (result nonzero isolation)
    (result_eq nonzero isolation same) nonzero
    (Power.Isolation.isolationResult nonzero degreeTwo degreeTwo_atLeastTwo) rfl).mpr restored

end Purelib.Riemann.RootContinuation.SquareRootOwnerReplay
