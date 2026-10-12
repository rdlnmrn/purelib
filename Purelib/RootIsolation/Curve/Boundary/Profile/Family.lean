module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Attach
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Curve.Boundary.Analysis
import Purelib.RootIsolation.Curve.Boundary.Event.Basic
import Purelib.RootIsolation.Curve.Boundary.Event.Family
public import Purelib.RootIsolation.Curve.Boundary.Profile.Boundary
import Purelib.RootIsolation.Curve.Event.Profile.Family
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Event.Basic

open Purelib.Geometry.Projective.Hermitian (Atom)
open Purelib.LinearAlgebra.Coordinates2.Matrix (GaussianMatrix)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Curve.Boundary.Analysis (CurveBoundary)
open Purelib.RootIsolation.Curve.Boundary.Profile (BoundaryProfileEventEntry)

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Complete condition-profile event families for one CCL boundary

This module lifts the exact box-condition profiles through the already
complete finite boundary-event family.  It also transports the existing
pointwise locator in the safe direction: a supplied displayed rational
polynomial root is assigned to a computed profile event.  No nonzero Sturm
count is converted into a root-existence statement.
-/

namespace Purelib.RootIsolation.Curve.Boundary.Profile.Family

/-- Expand every condition profile below one attached unsplit boundary
event. -/
def profileEntriesOfEvent
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (parent : Curve.Boundary.Event.Basic.SourcePersistentProfileBoundaryEventsBoundaryEventEntryAlias boundary)
    (parentMember : parent ∈
      Curve.Boundary.Event.Family.boundaryEventFamily
        boundary) :
    List (BoundaryProfileEventEntry boundary) :=
  (Curve.Event.Profile.Family.profileEventFamily
    parent.event.1).attach.map fun attached =>
      { parent := parent
        parentMember := parentMember
        event := attached.1
        eventMember := attached.2 }

/-- Complete finite family of every nonzero condition-profile event on one
dispatched Hermitian boundary. -/
def boundaryProfileEventFamily
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom) : List (BoundaryProfileEventEntry boundary) :=
  (Curve.Boundary.Event.Family.boundaryEventFamily
    boundary).attach.flatMap fun attached =>
      profileEntriesOfEvent boundary attached.1 attached.2

/-- A retained member profile event under an original member boundary event occurs in the complete boundary-profile
family. -/
theorem mem_boundaryProfileEventFamily
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (parent : Curve.Boundary.Event.Basic.SourcePersistentProfileBoundaryEventsBoundaryEventEntryAlias boundary)
    (parentMember : parent ∈
      Curve.Boundary.Event.Family.boundaryEventFamily
        boundary)
    (event : Curve.Event.Profile.Family.SourcePersistentProfileBoundaryEventsProfileEventEntryAlias parent.event.1)
    (eventMember : event ∈
      Curve.Event.Profile.Family.profileEventFamily
        parent.event.1) :
    ({ parent := parent
       parentMember := parentMember
       event := event
       eventMember := eventMember } : BoundaryProfileEventEntry boundary) ∈
      boundaryProfileEventFamily boundary := by
  rw [boundaryProfileEventFamily]
  apply Data.List.Flatten.mem_flatMap.mpr
  refine ⟨⟨parent, parentMember⟩, Data.List.Attach.mem_attach _ _, ?_⟩
  rw [profileEntriesOfEvent]
  apply Data.List.Map.mem_map.mpr
  exact ⟨⟨event, eventMember⟩, Data.List.Attach.mem_attach _ _, rfl⟩
end Purelib.RootIsolation.Curve.Boundary.Profile.Family

end
