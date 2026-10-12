module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Region.Complement
import Purelib.Polynomial.Winding.Box.Region.Selection
import Purelib.Polynomial.Winding.Box.Region.Sum
import Purelib.RootIsolation.Exact.Extraction
import Purelib.RootIsolation.Exact.State
public import Purelib.RootIsolation.Exact.Step

public import Purelib.RootIsolation.Exact.State.Replay
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Exact isolation steps from checked extraction checkpoints

Rebuild the numerical fields of an isolation state and retain the original
track constructors.  Equality is to the canonical step, not to an arbitrary
equivalent root family.  Proof-only references to that step disappear from
the executable replay.  This imports only existing finite isolation modules.
-/

namespace Purelib.RootIsolation.Exact.Step.Replay

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
variable (degreeAtLeastTwo : 2 ≤ p.natDegree) (squarefree :
  Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
section Steps

variable (state : Exact.State.IsolationState p ambient)
  (nonnegative : ∀ region ∈ state.regions, 0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box)
  (positive : 0 < Winding.Box.Region.Sum.totalRaw state.regions)

set_option genInjectivity false in
/-- Source association is supplied by checking the exact ordered extraction
trace of the canonically selected positive region. -/
structure StepInput where
  /-- The actual positive-region selection in the original ordered region list. -/ selection :
    Winding.Box.Region.Selection.PositiveSelection state.regions
  /-- The retained selection equals the original finite positive-region scan. -/ selection_eq : selection =
    Winding.Box.Region.Selection.selectPositive state.regions nonnegative positive
  /-- The retained track and complement grid extracted from that exact selected region. -/ extracted :
    Exact.Extraction.RegionExtraction p ambient selection.selected
  /-- The retained extraction equals the original canonical extraction on the selected region. -/ extracted_eq :
    extracted = Exact.Extraction.extractRegion degreeAtLeastTwo squarefree elimination
    selection.selected selection.positive

constructive_injectivity StepInput

/-- Cache the exact next support, ordered complement regions and prepended track from the retained selection and
extraction. -/
@[expose] def StepInput.cache (input : StepInput
  degreeAtLeastTwo squarefree elimination state nonnegative positive) :
    Exact.State.Replay.StateCache (Exact.Step.step degreeAtLeastTwo squarefree elimination state nonnegative
      positive).next where
  support := state.support
  support_eq := rfl
  regions := Winding.Box.Region.Complement.complementRegions input.extracted.grid
    input.selection.selected.refinesAmbient ++
    (input.selection.before ++ input.selection.after)
  regions_eq := by
    rcases input with ⟨selection, selectionEq, extracted, extractedEq⟩
    cases selectionEq
    cases extractedEq
    rfl
  tracks := input.extracted.track :: state.tracks
  tracks_eq := by
    rcases input with ⟨selection, selectionEq, extracted, extractedEq⟩
    cases selectionEq
    cases extractedEq
    rfl

/-- Restore the original extraction-step result from its checked state cache.

The restored state retains the original support, four-unit winding decrease and one-track increase through the cache's
exact equality. -/
@[expose] def StepInput.restore (input : StepInput
  degreeAtLeastTwo squarefree elimination state nonnegative positive) :
    Exact.Step.StepResult state :=
  let cache := input.cache
  { next := cache.restore
    support_next := by
      rw [cache.restore_eq]
      exact (Exact.Step.step degreeAtLeastTwo squarefree elimination state nonnegative positive).support_next
    totalRaw_next := by
      rw [cache.restore_eq]
      exact (Exact.Step.step degreeAtLeastTwo squarefree elimination state nonnegative positive).totalRaw_next
    tracks_length_next := by
      rw [cache.restore_eq]
      exact (Exact.Step.step degreeAtLeastTwo squarefree elimination state nonnegative positive).tracks_length_next }

/-- The restored result equals the original positive-region extraction step exactly. -/
theorem StepInput.restore_eq
    (input : StepInput degreeAtLeastTwo squarefree elimination state nonnegative positive) :
    input.restore = Exact.Step.step degreeAtLeastTwo squarefree elimination state nonnegative positive := by
  have same := input.cache.restore_eq
  change input.restore.next = _ at same
  cases original : Exact.Step.step degreeAtLeastTwo squarefree elimination state nonnegative positive
  cases restored : input.restore
  rw [original, restored] at same
  dsimp only at same
  cases same
  rfl

end Steps

section Runs

variable {state : Exact.State.IsolationState p ambient}
end Runs
end Purelib.RootIsolation.Exact.Step.Replay

end
