module

public import Purelib.RootIsolation.SquareRoot.Preparation.Terminal
public import Purelib.Riemann.Branches.PreparedSheetContinuation.Subdivision.Width
public import Purelib.Approximation.AccuracyRequest
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Finite width checking of an unchanged dyadic acquisition

The original acquired result remains the index of the entire check. The
check caches its actual depth-dependent width bound and either certifies its
identical request list or reports the computed finer depth that pays the
same positive width request. A refinement report does not replace the old
subdivision, execution caches or finish Owner, and proves no global failure.
-/

public section

namespace Purelib.RootIsolation.SquareRoot.Preparation.Terminal.AcquiredDyadic

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment GaussianPolynomial)
open Purelib.Riemann.Paths.PreparedClearPathModels (zeroEndpoint oneEndpoint)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision)

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Canonical}
variable {segment : ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
variable {owner : Owner (polynomial.eval start)} {diameter : Fraction.Rational} {positive : 0 < diameter}

/-- The original acquired depth pays its identical request list at the exact unit-interval dyadic width bound. -/
theorem requests_widthsFit (acquired : AcquiredDyadic segment within owner diameter positive) :
    Subdivision.WidthsFit (Geometric.Basic.quarterRadius 1 acquired.depth) zeroEndpoint acquired.requests := by
  have paid := Subdivision.tryDyadic_widthsFit acquired.depth diameter positive acquired.success
  have unitWidth : (zeroEndpoint.parameter - oneEndpoint.parameter) ^ 2 = (1 : Fraction.Rational) :=
    by decide +kernel
  rewrite [unitWidth, ← acquired.requests_eq] at paid
  exact paid

/-- A finite unsuccessful width comparison retaining its exact additional depth and original acquired result.

The original result is an index, so its subdivision, requests, CachedSources
and terminal Owner remain the same inputs. The computed finer depth pays the
positive width request. Comparison of a later refined terminal Owner with the
old terminal Owner remains an additional geometric obligation.
-/
@[expose] def WidthRefinement (acquired : AcquiredDyadic segment within owner diameter positive)
    (request : AccuracyRequest) (checkedBound : Fraction.Rational) :=
  { required : Nat // required = Geometric.Search.firstQuarterBelow 1 0 request.tolerance ∧
      request.tolerance < checkedBound ∧ acquired.depth < required ∧
        Geometric.Basic.quarterRadius 1 required < request.tolerance }

/-- The retained required depth is the exact original finite search on the unchanged positive width request. -/
theorem WidthRefinement.required_eq {acquired : AcquiredDyadic segment within owner diameter positive}
    {request : AccuracyRequest} {checkedBound : Fraction.Rational}
    (refinement : WidthRefinement acquired request checkedBound) :
    refinement.val = Geometric.Search.firstQuarterBelow 1 0 request.tolerance := refinement.property.1

/-- The additional depth strictly exceeds the same acquired result's retained depth. -/
theorem WidthRefinement.depth_lt {acquired : AcquiredDyadic segment within owner diameter positive}
    {request : AccuracyRequest} {checkedBound : Fraction.Rational}
    (refinement : WidthRefinement acquired request checkedBound) :
    acquired.depth < refinement.val := refinement.property.2.2.1

/-- The exact retained required depth pays the unchanged positive scalar width request. -/
theorem WidthRefinement.required_paid {acquired : AcquiredDyadic segment within owner diameter positive}
    {request : AccuracyRequest} {checkedBound : Fraction.Rational}
    (refinement : WidthRefinement acquired request checkedBound) :
    Geometric.Basic.quarterRadius 1 refinement.val < request.tolerance := refinement.property.2.2.2

/-- The actual finite checked bound missed its same retained positive width request. -/
theorem WidthRefinement.unpaid {acquired : AcquiredDyadic segment within owner diameter positive}
    {request : AccuracyRequest} {checkedBound : Fraction.Rational}
    (refinement : WidthRefinement acquired request checkedBound) :
    request.tolerance < checkedBound := refinement.property.2.1

/-- The finite scalar check retains the actual bound, width payment or unresolved additional depth.

A paid branch supplies the width certificate on the acquired result's exact
request list. The other branch retains the bound that missed the request and
the actual computed stronger depth, without reacquiring any root owner.
-/
@[expose] def WidthOutcome (acquired : AcquiredDyadic segment within owner diameter positive)
    (request : AccuracyRequest) :=
  Σ checked : { retained : Fraction.Rational // retained = Geometric.Basic.quarterRadius 1 acquired.depth },
    { _paid : checked.val ≤ request.tolerance //
        Subdivision.WidthsFit request.tolerance zeroEndpoint acquired.requests } ⊕
      WidthRefinement acquired request checked.val

namespace WidthOutcome

variable {acquired : AcquiredDyadic segment within owner diameter positive} {request : AccuracyRequest}

/-- Retain an already computed original width bound and check it against the exact supplied positive request. -/
def ofChecked (checkedBound : Fraction.Rational)
    (checked_eq : checkedBound = Geometric.Basic.quarterRadius 1 acquired.depth) : WidthOutcome acquired request :=
  if paid : checkedBound ≤ request.tolerance then
    ⟨⟨checkedBound, checked_eq⟩, .inl ⟨paid, Subdivision.WidthsFit.mono
      (checked_eq ▸ paid) zeroEndpoint acquired.requests acquired.requests_widthsFit⟩⟩
  else
    let required := Geometric.Search.firstQuarterBelow 1 0 request.tolerance
    have requiredPaid : Geometric.Basic.quarterRadius 1 required < request.tolerance :=
      Geometric.Search.firstQuarterBelow_accurate 1 (by decide +kernel) 0 request.tolerance request.positive
    have depth : acquired.depth < required := by
      apply Nat.lt_of_not_ge
      intro notFiner
      exact paid ((checked_eq.trans_le
        (Geometric.Basic.quarterRadius_antitone (by decide +kernel) notFiner)).trans requiredPaid.le)
    ⟨⟨checkedBound, checked_eq⟩,
      .inr ⟨required, rfl, Fraction.Order.Arithmetic.lt_of_not_ge_direct paid, depth, requiredPaid⟩⟩

/-- Compute the original depth width once and retain the complete scalar decision on the unchanged acquired result. -/
def check (acquired : AcquiredDyadic segment within owner diameter positive) (request : AccuracyRequest) :
    WidthOutcome acquired request :=
  let checkedBound := Geometric.Basic.quarterRadius 1 acquired.depth
  ofChecked checkedBound rfl

/-- Read the actual cached scalar bound checked for this original acquired depth. -/
@[expose] def bound (outcome : WidthOutcome acquired request) : Fraction.Rational := outcome.1.val

/-- The checked scalar cache is the original exact unit-interval quarter-radius at the retained depth. -/
theorem bound_eq (outcome : WidthOutcome acquired request) :
    outcome.bound = Geometric.Basic.quarterRadius 1 acquired.depth := outcome.1.property

/-- Read the retained typed payment or additional-depth request on the same original acquisition. -/
@[expose] def result (outcome : WidthOutcome acquired request) :
    { _paid : outcome.bound ≤ request.tolerance //
        Subdivision.WidthsFit request.tolerance zeroEndpoint acquired.requests } ⊕
      WidthRefinement acquired request outcome.bound := outcome.2

/-- The completed-bound constructor retains its exact supplied scalar cache in both decision branches. -/
theorem ofChecked_bound (checkedBound : Fraction.Rational)
    (checked_eq : checkedBound = Geometric.Basic.quarterRadius 1 acquired.depth) :
    (ofChecked (request := request) checkedBound checked_eq).bound = checkedBound := by
  unfold ofChecked
  split <;> rfl

end WidthOutcome

/-- Any separately supplied acquisition at the computed required depth or later pays the same physical width request.

Both complete acquired results remain distinct inputs. This statement only
certifies the new request list's widths; it makes no claim identifying their
actual executions, CachedSources or terminal root owners.
-/
theorem WidthRefinement.next_widthsFit {acquired : AcquiredDyadic segment within owner diameter positive}
    {request : AccuracyRequest} {checkedBound : Fraction.Rational}
    (refinement : WidthRefinement acquired request checkedBound)
    (next : AcquiredDyadic segment within owner diameter positive) (deepEnough : refinement.val ≤ next.depth) :
    Subdivision.WidthsFit request.tolerance zeroEndpoint next.requests :=
  Subdivision.WidthsFit.mono
    ((Geometric.Basic.quarterRadius_antitone (by decide +kernel) deepEnough).trans refinement.required_paid.le)
    zeroEndpoint next.requests next.requests_widthsFit

end Purelib.RootIsolation.SquareRoot.Preparation.Terminal.AcquiredDyadic
