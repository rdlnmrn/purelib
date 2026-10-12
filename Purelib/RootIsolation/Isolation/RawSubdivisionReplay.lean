module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Grid.Four.Elimination
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.Subdivision.Raw.Grid
import Purelib.RootIsolation.Subdivision.Raw.Grid.Elimination
public import Purelib.RootIsolation.Subdivision.Raw.Iteration.Forward
import Purelib.RootIsolation.Subdivision.Raw.Selection
import Purelib.RootIsolation.Subdivision.Raw.Step
public import Purelib.Polynomial.Clearance.Box.Grid.Four.Replay
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Grid.Four.Basic
import Purelib.Polynomial.Clearance.Box.Grid.Four.Clearance
import Purelib.Polynomial.Clearance.Box.Refinement.Contracting
import Purelib.Polynomial.Winding.Box.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-! Reassemble the original raw subdivision from checked saved cut grids.
The local winding tests still validate the original first-nonzero ordering.
Neither a different child nor a merely contracting replacement is accepted. -/
@[expose] public section

namespace Purelib.RootIsolation.Isolation.RawSubdivisionReplay

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)

/-- Only proof fields refer to the canonical grid producer. The four boxes
and their original scalar clearances come from the restored cut grid. -/
def grid (state : State.Raw.RawWindingState p ambient)
    (saved : Clearance.Box.Grid.Four.Replay.Checked elimination state.box state.proper) :
      Subdivision.Raw.Grid.RawFourGrid state := by
  let cuts := saved.val
  let clearances := cuts.childClearances state.clearance
  have same : cuts = Clearance.Box.Grid.Four.Elimination.buildClearFourGrid elimination state.box state.proper :=
    saved.property
  refine
    { lowerLeft := ⟨cuts.lowerLeft, cuts.lowerLeft_refines,
        cuts.lowerLeft_refines.trans state.refinesAmbient, ?_, clearances.1, ?_⟩
      upperLeft := ⟨cuts.upperLeft, cuts.upperLeft_refines,
        cuts.upperLeft_refines.trans state.refinesAmbient, ?_, clearances.2.1, ?_⟩
      lowerRight := ⟨cuts.lowerRight, cuts.lowerRight_refines,
        cuts.lowerRight_refines.trans state.refinesAmbient, ?_, clearances.2.2.1, ?_⟩
      upperRight := ⟨cuts.upperRight, cuts.upperRight_refines,
        cuts.upperRight_refines.trans state.refinesAmbient, ?_, clearances.2.2.2, ?_⟩
      additive := cuts.winding_additive }
  all_goals rw [same]
  · exact (Subdivision.Raw.Grid.Elimination.safeRawFourGrid elimination state).lowerLeft.proper
  · exact (Subdivision.Raw.Grid.Elimination.safeRawFourGrid elimination state).lowerLeft.contracts
  · exact (Subdivision.Raw.Grid.Elimination.safeRawFourGrid elimination state).upperLeft.proper
  · exact (Subdivision.Raw.Grid.Elimination.safeRawFourGrid elimination state).upperLeft.contracts
  · exact (Subdivision.Raw.Grid.Elimination.safeRawFourGrid elimination state).lowerRight.proper
  · exact (Subdivision.Raw.Grid.Elimination.safeRawFourGrid elimination state).lowerRight.contracts
  · exact (Subdivision.Raw.Grid.Elimination.safeRawFourGrid elimination state).upperRight.proper
  · exact (Subdivision.Raw.Grid.Elimination.safeRawFourGrid elimination state).upperRight.contracts

/-- Restoring the checked cut-grid cache gives the exact original safe four-grid state. -/
theorem grid_eq (state : State.Raw.RawWindingState p ambient)
    (saved : Clearance.Box.Grid.Four.Replay.Checked elimination state.box state.proper) :
    grid elimination state saved = Subdivision.Raw.Grid.Elimination.safeRawFourGrid elimination state := by
  rcases saved with ⟨cuts, same⟩
  cases same
  rfl

/-- Validate the original finite winding branch, reusing the saved grid. -/
def step (state : State.Raw.RawWindingState p ambient)
    (saved : Clearance.Box.Grid.Four.Replay.Checked elimination state.box state.proper) : State.Raw.RawWindingState p
      ambient :=
  let restored := grid elimination state saved
  let child := Subdivision.Raw.Selection.firstNonzeroChild restored
  ⟨child.box, child.refinesAmbient, child.proper, child.clearance,
    Subdivision.Raw.Selection.firstNonzeroChild_rawWinding_ne restored⟩

/-- Selecting the first nonzero child of the checked restored grid gives the original refinement step exactly. -/
theorem step_eq (state : State.Raw.RawWindingState p ambient)
    (saved : Clearance.Box.Grid.Four.Replay.Checked elimination state.box state.proper) :
    step elimination state saved = Subdivision.Raw.Step.refineOnce elimination state := by
  rcases saved with ⟨cuts, same⟩
  cases same
  rfl

/-- The full remaining-depth ownership equation is carried across one checked
checkpoint step. It does not evaluate the canonical recursive producer. -/
theorem advance_eq (state : State.Raw.RawWindingState p ambient)
    (saved : Clearance.Box.Grid.Four.Replay.Checked elimination state.box state.proper)
    (remaining : Nat) (result : State.Raw.RawWindingState p ambient)
    (tail : result = Subdivision.Raw.Iteration.Forward.refineForwardN elimination remaining (step elimination state
      saved)) :
    result = Subdivision.Raw.Iteration.Forward.refineForwardN elimination (remaining + 1) state := by
  exact tail.trans (congrArg (Subdivision.Raw.Iteration.Forward.refineForwardN elimination remaining) (step_eq
    elimination state saved))

end Purelib.RootIsolation.Isolation.RawSubdivisionReplay
