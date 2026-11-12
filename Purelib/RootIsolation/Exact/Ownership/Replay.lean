module
import Purelib.RootIsolation.Refinement.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Exact.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.Exact.Ownership.Basic
public import Purelib.RootIsolation.Exact.Ownership.Prepare
import Purelib.RootIsolation.Exact.Ownership.Radius
import Purelib.RootIsolation.Exact.Partition.Location
import Purelib.RootIsolation.Exact.Partition.Margin
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Count
import Purelib.RootIsolation.State.Raw.Interior
public import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.RootIsolation.Track.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-! Restore the original partition classification from its exact refined state. -/
namespace Purelib.RootIsolation.Exact.Ownership.Replay

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count
  degreeBound : Nat}
  (degreeAtLeastTwo : 2 ≤ p.natDegree) (squarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound) (output :
    Exact.Basic.Output p ambient count)
  (track : Track.Basic.WindingOneTrack p ambient) (supported : track.initial.box.Refines
    output.support)

/-- A cached state equal to the original track's refinement at the partition ownership radius. -/
abbrev Refined := {state :
  State.WindingOne.Basic.WindingOneState p ambient // state =
  track.refine track.initial (Exact.Ownership.Radius.assignmentRadius p ambient output)
    (Exact.Ownership.Radius.assignmentRadius_pos p ambient output)}

/-- Restore the original owner selection using the checked cached ownership-radius refinement.

Locate the saved state's anchor in the original partition and retain strict owner containment; the source track, radius
and refined state remain linked by the saved equality. -/
def restore (saved : Refined output track) :
    Exact.Ownership.Basic.OwnerSelection output track :=
  let radius := Exact.Ownership.Radius.assignmentRadius p ambient output
  let positive := Exact.Ownership.Radius.assignmentRadius_pos p ambient output
  let refined : Refinement track.initial.raw radius :=
    { state := saved.val
      strict := by
        rewrite [saved.property]
        exact track.strict track.initial radius positive
      accurate := by
        rewrite [saved.property]
        exact track.accurate track.initial radius positive }
  let assigned := Exact.Ownership.Prepare.fromRefinement degreeAtLeastTwo squarefree elimination
    output track supported refined
  { owner := assigned.owner
    refined := saved.val
    refined_eq := saved.property
    strict :=
      (congrArg (fun current : State.WindingOne.Basic.WindingOneState p ambient =>
        current.box.StrictInterior (output.tracks.get assigned.owner).initial.box) saved.property).mp
        assigned.strict }

/-- Restoring the checked refinement cache returns exactly the original deterministic owner selection. -/
theorem restore_eq (saved : Refined output
  track) :
    restore degreeAtLeastTwo squarefree elimination output track supported saved =
      Exact.Ownership.Prepare.selectOutputOwner degreeAtLeastTwo squarefree elimination output track supported := by
  rcases saved with ⟨state, same⟩
  cases same
  rfl

/-- Restore the original owner selection using exact retained partition and track readbacks.

The cached output retains the complete original track and remainder partition.
The cached source track and its actual assignment-radius state are consumed
by the original restoration operation; the original nominal owners remain
indices of the returned complete selection certificate.
-/
def fromReadbacks (cachedOutput : Exact.Basic.Output p ambient count) (sameOutput : cachedOutput = output)
    (cachedTrack : Track.Basic.WindingOneTrack p ambient) (sameTrack : cachedTrack = track)
    (saved : Refined cachedOutput cachedTrack) : Exact.Ownership.Basic.OwnerSelection output track := by
  subst output
  subst track
  exact restore degreeAtLeastTwo squarefree elimination cachedOutput cachedTrack supported saved

/-- Complete partition, track and refinement readbacks retain the original deterministic owner selection. -/
theorem fromReadbacks_eq (cachedOutput : Exact.Basic.Output p ambient count) (sameOutput : cachedOutput = output)
    (cachedTrack : Track.Basic.WindingOneTrack p ambient) (sameTrack : cachedTrack = track)
    (saved : Refined cachedOutput cachedTrack) :
    fromReadbacks degreeAtLeastTwo squarefree elimination output track supported cachedOutput sameOutput
      cachedTrack sameTrack saved =
      Exact.Ownership.Prepare.selectOutputOwner degreeAtLeastTwo squarefree elimination output track supported := by
  cases sameOutput
  cases sameTrack
  exact restore_eq degreeAtLeastTwo squarefree elimination output track supported saved

end Purelib.RootIsolation.Exact.Ownership.Replay

end
