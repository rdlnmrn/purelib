module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Curve.Boundary.Analysis
import Purelib.RootIsolation.Curve.Boundary.Event.Basic
public import Purelib.RootIsolation.Curve.Boundary.Event.Family
public import Purelib.RootIsolation.Curve.Event.Profile.Classification
public import Purelib.RootIsolation.Curve.Event.Profile.Family
import Purelib.RootIsolation.Curve.Event.Profile.Sign
public import Purelib.Geometry.Projective.Hermitian.Chart.Bounds
import Purelib.Data.Rat.Interval.Width
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Request
import Purelib.RootIsolation.Sturm.Track.Basic

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Complete condition-profile event families for one CCL boundary

This module lifts the exact box-condition profiles through the already
complete finite boundary-event family.  It also transports the existing
pointwise locator in the safe direction: a supplied displayed rational
polynomial root is assigned to a computed profile event.  No nonzero Sturm
count is converted into a root-existence statement.
-/

namespace Purelib.RootIsolation.Curve.Boundary.Profile

set_option genInjectivity false in
/-- One condition-profile event with its exact parent in the complete
unsplit boundary-event family. -/
structure BoundaryProfileEventEntry
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {reference :
      LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Geometry.Projective.Hermitian.Atom}
    (boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom) where
  /-- The exact parent entry in the unsplit boundary-event family. -/ parent :
    Curve.Boundary.Event.Basic.SourcePersistentProfileBoundaryEventsBoundaryEventEntryAlias boundary
  /-- The retained parent occurs in the original complete boundary-event family. -/ parentMember : parent ∈
    Curve.Boundary.Event.Family.boundaryEventFamily boundary
  /-- The actual condition-profile event belonging to the retained parent factor analysis. -/ event :
    Curve.Event.Profile.Family.SourcePersistentProfileBoundaryEventsProfileEventEntryAlias parent.event.1
  /-- The retained event occurs in that exact parent's complete profile-event family. -/ eventMember : event ∈
    Curve.Event.Profile.Family.profileEventFamily
      parent.event.1

constructive_injectivity BoundaryProfileEventEntry

namespace BoundaryProfileEventEntry

/-- Refine the retained profile event to the supplied parameter-width request. -/
@[expose] def requestAt
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {reference :
      LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Geometry.Projective.Hermitian.Atom}
    {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (epsilon : Fraction.Rational) :=
  entry.event.2.request epsilon

/-- Refine the retained profile event to its computed profile-wide sign width. -/
@[expose] def request
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {reference :
      LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Geometry.Projective.Hermitian.Atom}
    {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) :=
  entry.requestAt
    (Curve.Event.Profile.Sign.profileSignWidth
      entry.event.1)

/-- The sign-control request bounds the retained event interval by its computed profile-wide sign width. -/
theorem request_width_le
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {reference :
      LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Geometry.Projective.Hermitian.Atom}
    {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) :
    (Data.Rat.Interval.Bounds.width entry.request.cell.interval) ≤
      Curve.Event.Profile.Sign.profileSignWidth
      entry.event.1 :=
  entry.event.2.request_width_le _
    (Curve.Event.Profile.Sign.profileSignWidth_pos
      entry.event.1)

/-- A positive requested width bounds the refined profile event interval. -/
theorem requestAt_width_le
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {reference :
      LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Geometry.Projective.Hermitian.Atom}
    {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) :
    (Data.Rat.Interval.Bounds.width (entry.requestAt epsilon).cell.interval) ≤ epsilon :=
  entry.event.2.request_width_le epsilon positive

/-- The profile event has the same chart-wide homogeneous chordal diameter
bound as its parent event, independently of affine poles. -/
theorem chordalSq_requestAt_le
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {reference :
      LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Geometry.Projective.Hermitian.Atom}
    {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    {left right : Fraction.Rational}
    (leftInside : (entry.requestAt epsilon).cell.interval.Contains left)
    (rightInside : (entry.requestAt epsilon).cell.interval.Contains right) :
    Geometry.Projective.Chordal.Basic.chordalSq
        (entry.parent.chart.projective left)
        (entry.parent.chart.projective right) ≤
      entry.parent.chart.uniformChordalVariationCoefficient * epsilon ^ 2 := by
  let requested := entry.requestAt epsilon
  have requestedRefines := entry.event.2.request_refines_chart epsilon
  have leftChart : entry.parent.chart.cell.interval.Contains left :=
    ⟨requestedRefines.1.trans leftInside.1,
      leftInside.2.trans requestedRefines.2⟩
  have rightChart : entry.parent.chart.cell.interval.Contains right :=
    ⟨requestedRefines.1.trans rightInside.1,
      rightInside.2.trans requestedRefines.2⟩
  have parameterBound :=
    Data.Rat.Interval.parameter_sub_sq_le_width_sq
      requested.cell.interval leftInside rightInside
  have widthSquare : (Data.Rat.Interval.Bounds.width requested.cell.interval) ^ 2 ≤ epsilon ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Data.Rat.Interval.Bounds.width_nonneg requested.cell.interval)
      (entry.requestAt_width_le epsilon positive) 2
  exact (entry.parent.chart.chordalSq_le_uniform leftChart rightChart).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (parameterBound.trans widthSquare)
      entry.parent.chart.uniformChordalVariationCoefficient_nonneg)

/-- Total affine classification against the boundary's analysis box. -/
@[expose] def classification
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {reference :
      LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Geometry.Projective.Hermitian.Atom}
    {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) :=
  Curve.Event.Profile.Classification.classifyRequestedProfileEventAffine
    entry.event.2

end BoundaryProfileEventEntry
end Purelib.RootIsolation.Curve.Boundary.Profile

end

section
public section

/-!
# Original-polynomial residuals on condition-profile CCL events

A condition profile is a further finite factor of one squarefree curve-gcd
factor.  Its Sturm request directly bounds only that final profile factor.
This module multiplies through the displayed finite cofactors, then through
the two cleared curve coordinates, to recover a coefficient-computed bound
for the original Gaussian polynomial at every displayed affine point of the
requested profile cylinder.

All parameters and coefficients are constructive rationals.  The estimates
hold pointwise throughout a finite request interval and make no root
existence assertion.
-/

namespace Purelib.RootIsolation.Curve.Boundary.Profile

/-- The original boundary profile-event entry, retaining its exact parent and family membership. -/
abbrev
  SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {reference :
      LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Geometry.Projective.Hermitian.Atom}
    (boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom) :=
  BoundaryProfileEventEntry
    boundary

end Purelib.RootIsolation.Curve.Boundary.Profile

end

section
public section

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

namespace Purelib.RootIsolation.Curve.Boundary.Profile

/-- The same parent-indexed boundary profile-event entry used by complete request families. -/
abbrev
  SourcePersistentProfileRequestFamilyBoundaryProfileEventEntryAlias
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {reference :
      LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Geometry.Projective.Hermitian.Atom}
    (boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom) :=
  SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
    boundary

/-! ## Complete requested families through a dispatched boundary -/

end Purelib.RootIsolation.Curve.Boundary.Profile

end
