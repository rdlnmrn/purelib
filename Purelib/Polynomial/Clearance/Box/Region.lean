module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Uniform polynomial clearance on a zero-winding rectangle

A sufficiently small rational residual in a protected rectangle constructs a
strictly interior winding-one state.  Global nonnegativity would then force
the parent winding to be at least four.  A zero-winding parent therefore has
the point-independent positive residual target as a lower bound everywhere,
including its boundary.  Only the finite target is executable output; the
hypothetical Newton extraction and elimination are confined to the proof.
-/

namespace Purelib.Polynomial.Clearance.Box.Region

set_option genInjectivity false in
/-- Cached quantitative clearance throughout the closed rational box,
stronger than clearance merely on its four boundary sides. -/
structure RegionClearance (p :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box
  : Box) where
  /-- The uniform lower bound on polynomial quadrance throughout the closed box. -/ bound : Fraction.Rational
  /-- The retained region bound is positive. -/ positive : 0 < bound
  /-- Every point contained in the original box satisfies the retained polynomial quadrance bound. -/ lower : ∀ point :
    Gaussian.Basic.Canonical, box.Contains point → bound ≤ Data.Gaussian.Norm.Basic.normSq (p.eval point)

constructive_injectivity RegionClearance

namespace RegionClearance

variable {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}

/-- Restrict the closed-box clearance to its boundary, retaining its exact positive bound. -/
def toBoundaryClearance (clearance :
  RegionClearance p box) : Clearance.Box.Boundary.Basic.BoundaryClearance p box :=
  ⟨clearance.bound, clearance.positive, fun point boundary => by
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using clearance.lower point boundary.1⟩

/-- Restriction copies the cached bound; it never repeats the residual
target calculation on the smaller rectangle. -/
def restrict (clearance :
  RegionClearance p box) {inner : Box} (refines : inner.Refines box) :
  RegionClearance p inner :=
  ⟨clearance.bound, clearance.positive, fun point inside => clearance.lower point (refines.contains inside)⟩

/-- Every point in the retained closed box has nonzero polynomial value. -/
theorem eval_ne_zero (clearance :
  RegionClearance p box) {point : Gaussian.Basic.Canonical} (inside : box.Contains point) : p.eval
  point ≠ 0 := by
  intro zero
  have lower := clearance.lower point inside
  rw [zero, Gaussian.Norm.Basic.normSq_zero] at lower
  exact not_lt_of_ge lower clearance.positive
end RegionClearance

end Purelib.Polynomial.Clearance.Box.Region

end
