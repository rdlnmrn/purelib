module

public import Purelib.RootIsolation.Refinement.Basic

/-! # Successful refinements inside larger retained source regions -/

public section

namespace Purelib.RootIsolation.Refinement

open Purelib.Geometry.Rational
open Purelib.Geometry.Rational.Box.Refinement.StrictInterior
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Data.Rat.Fraction (Rational)

variable {polynomial : CoefficientPolynomial} {ambient : Box}
  {current : State.Raw.RawWindingState polynomial ambient} {epsilon : Rational}

/-- Retain a successful refinement inside a supplied larger original source region.

Only the source index and its strict containment proof change. The actual
winding-one result, all clearances and original accuracy request are retained;
no numerical refinement or winding computation is repeated.
-/
@[expose] def withSource (refinement : Refinement current epsilon)
    (source : State.Raw.RawWindingState polynomial ambient) (contained : current.box.Refines source.box) :
    Refinement source epsilon where
  state := refinement.state
  strict := Boxes.trans_refines refinement.strict contained
  accurate := refinement.accurate

/-- Enlarging the source retains the complete supplied numerical result. -/
theorem withSource_state (refinement : Refinement current epsilon)
    (source : State.Raw.RawWindingState polynomial ambient) (contained : current.box.Refines source.box) :
    (refinement.withSource source contained).state = refinement.state := rfl

/-- Keeping the same source gives the identical complete refinement certificate. -/
theorem withSource_self (refinement : Refinement current epsilon) :
    refinement.withSource current (Box.refines_refl current.box) = refinement := rfl

end Purelib.RootIsolation.Refinement
