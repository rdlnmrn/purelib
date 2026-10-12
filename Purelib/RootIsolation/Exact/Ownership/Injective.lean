module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.Exact.Ownership.Basic
public import Purelib.RootIsolation.Exact.Ownership.Prepare
import Purelib.RootIsolation.Exact.Ownership.Radius
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Count
import Purelib.RootIsolation.Track.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free degree-sharp maximality

The finite exact-isolation partition assigns every sufficiently refined
winding-one track to one displayed output cell.  Zero-winding remainder cells
cannot own such a track, and a raw-winding-four output cell cannot own two
separated tracks.  All searches below scan finite lists directly.
-/

namespace Purelib.RootIsolation.Exact.Ownership.Injective

/-- Deterministic ownership is injective on every displayed separated
family.  If two refined states selected the same output track, that
winding-one output box would contain two separated winding-one boxes and
would therefore have raw winding at least eight, contradicting its displayed
raw winding four. -/
theorem selectedOwner_injective
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    {count familyCount : Nat} (output : Exact.Basic.Output p ambient count)
    (family : Fin familyCount → Track.Basic.WindingOneTrack p ambient)
    (supported : ∀ index, (family index).initial.box.Refines output.support)
    (pairwise : ∀ left right, left ≠ right →
      (family left).initial.box.Separated (family right).initial.box) :
    Function.Injective (fun index =>
      (Exact.Ownership.Prepare.selectOutputOwner degreeAtLeastTwo squarefree elimination output
        (family index) (supported index)).owner) := by
  let radius := Exact.Ownership.Radius.assignmentRadius p ambient output
  let radiusPositive := Exact.Ownership.Radius.assignmentRadius_pos p ambient output
  let refined : Fin familyCount → State.WindingOne.Basic.WindingOneState p ambient := fun index =>
    (family index).refine (family index).initial radius radiusPositive
  let selection : (index : Fin familyCount) →
      Exact.Ownership.Basic.OwnerSelection output (family index) := fun index =>
    Exact.Ownership.Prepare.selectOutputOwner degreeAtLeastTwo squarefree elimination output
      (family index) (supported index)
  let owner : Fin familyCount → Fin output.tracks.length :=
    fun index => (selection index).owner
  have ownerStrict (index : Fin familyCount) :
      (refined index).box.StrictInterior
        (output.tracks.get (owner index)).initial.box := by
    exact (selection index).strict
  intro left right ownerEqual
  change owner left = owner right at ownerEqual
  by_cases indicesEqual : left = right
  · exact indicesEqual
  · have initialSeparated := pairwise left right indicesEqual
    have refinedSeparated := initialSeparated.of_refines
      ((family left).nested (family left).initial radius radiusPositive)
      ((family right).nested (family right).initial radius radiusPositive)
    have leftInside := ownerStrict left
    have rightInside := ownerStrict right
    rw [← ownerEqual] at rightInside
    let region : Clearance.Box.Region.ClearRegion p ambient :=
      { box := (output.tracks.get (owner left)).initial.box
        refinesAmbient :=
          (output.tracks.get (owner left)).initial.refinesAmbient
        proper := (output.tracks.get (owner left)).initial.proper
        clearance := (output.tracks.get (owner left)).initial.clearance }
    have atLeastEight := State.WindingOne.Count.region_rawWinding_ge_eight_of_separated
      degreeAtLeastTwo squarefree elimination region (refined left)
        (refined right) leftInside rightInside refinedSeparated
    have exactlyFour :=
      (output.tracks.get (owner left)).initial.rawWindingFour
    dsimp only [region] at atLeastEight
    exact (by omega : False).elim
end Purelib.RootIsolation.Exact.Ownership.Injective

end
