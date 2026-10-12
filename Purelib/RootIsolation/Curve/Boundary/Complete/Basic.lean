module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Attach
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Curve.Boundary.Analysis
import Purelib.RootIsolation.Curve.Boundary.Profile.Boundary
public import Purelib.RootIsolation.Curve.Boundary.Profile.Family
public import Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Boundary.Event.Basic
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Basic

open Purelib.RootIsolation.Curve.Boundary.Analysis (CurveBoundary)
open Purelib.RootIsolation.Curve.Boundary.Profile (SourcePersistentProfileRequestFamilyBoundaryProfileEventEntryAlias)

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Complete finite refinement families for profile events

`SturmNonzeroEvent.request` deliberately follows one nonzero child.  That is
the right interface for one persistent algebraic event, but it is not a
complete refinement when the starting cell has several nonzero children.
This module builds the full finite binary refinement at a requested width,
filters all and only the nonzero-count children, and retains pointwise
coverage for every supplied displayed rational profile zero.

The construction uses only finite subdivision trees and integer event counts.
In particular, nonzero count is never converted into a root-existence claim.
-/

namespace Purelib.RootIsolation.Curve.Boundary.Complete.Basic

/-! ## Complete requested families through a dispatched boundary -/

section Boundary

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {reference :
  LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current : Box}
variable {denominatorMargin : Fraction.Rational}
variable {marginPositive : 0 < denominatorMargin}
variable {atom : Geometry.Projective.Hermitian.Atom}

set_option genInjectivity false in
/-- One nonzero child in the full requested refinement of one attached
condition-profile boundary event. -/
structure BoundaryCompleteRequestEntry
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (epsilon : Fraction.Rational) where
  /-- The exact retained boundary profile-event parent. -/ parent :
    SourcePersistentProfileRequestFamilyBoundaryProfileEventEntryAlias boundary
  /-- The parent belongs to the original complete boundary-profile family. -/ parentMember : parent ∈
    Curve.Boundary.Profile.Family.boundaryProfileEventFamily
      boundary
  /-- The original nonzero child of that exact profile event at the requested width. -/ child :
    Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf parent.event.2 epsilon
  /-- The retained child belongs to that exact parent's complete requested family. -/ childMember : child ∈
    Curve.Event.Profile.Complete.Basic.completeRequestFamily parent.event.2 epsilon

constructive_injectivity BoundaryCompleteRequestEntry

/-- Expand one attached boundary profile into all of its nonzero requested
children. -/
def completeRequestEntriesOfProfile
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (epsilon : Fraction.Rational) (parent :
      SourcePersistentProfileRequestFamilyBoundaryProfileEventEntryAlias boundary)
    (parentMember : parent ∈
      Curve.Boundary.Profile.Family.boundaryProfileEventFamily
        boundary) :
    List (BoundaryCompleteRequestEntry boundary epsilon) :=
  (Curve.Event.Profile.Complete.Basic.completeRequestFamily parent.event.2 epsilon).attach.map fun attached =>
    { parent := parent
      parentMember := parentMember
      child := attached.1
      childMember := attached.2 }

/-- Complete finite family of all nonzero requested children across every
profile and every bounded chart of one dispatched boundary. -/
def boundaryCompleteRequestFamily
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (epsilon : Fraction.Rational) :
    List (BoundaryCompleteRequestEntry boundary epsilon) :=
  (Curve.Boundary.Profile.Family.boundaryProfileEventFamily
    boundary).attach.flatMap fun attached =>
      completeRequestEntriesOfProfile boundary epsilon attached.1 attached.2

/-- Every member child of a retained member profile appears in the complete requested boundary family. -/
theorem mem_boundaryCompleteRequestFamily
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (epsilon : Fraction.Rational) (parent :
      SourcePersistentProfileRequestFamilyBoundaryProfileEventEntryAlias boundary)
    (parentMember : parent ∈
      Curve.Boundary.Profile.Family.boundaryProfileEventFamily
        boundary)
    (child : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf parent.event.2 epsilon)
    (childMember : child ∈ Curve.Event.Profile.Complete.Basic.completeRequestFamily parent.event.2 epsilon) :
    ({ parent := parent
       parentMember := parentMember
       child := child
       childMember := childMember } :
      BoundaryCompleteRequestEntry boundary epsilon) ∈
        boundaryCompleteRequestFamily boundary epsilon := by
  rw [boundaryCompleteRequestFamily]
  apply Data.List.Flatten.mem_flatMap.mpr
  refine ⟨⟨parent, parentMember⟩, Data.List.Attach.mem_attach _ _, ?_⟩
  rw [completeRequestEntriesOfProfile]
  exact Data.List.Map.mem_map.mpr
    ⟨⟨child, childMember⟩, Data.List.Attach.mem_attach _ _, rfl⟩

end Boundary

end Purelib.RootIsolation.Curve.Boundary.Complete.Basic

end
