module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RootIsolation.Newton.Search.Iteration
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.Raw

public import Purelib.RootIsolation.Sturm.Track.Interface
public import Purelib.Polynomial.Dense.Gaussian.Path.Axis
public import Purelib.Data.Rat.Interval.Bisection
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Checked initial root extraction

The initial positive-winding region can contain several roots.  In particular,
its midpoint may be a critical point even when the polynomial is squarefree.
Try its midpoint and four off-centre seeds before using the total extractor.
These seeds are only proposals: the existing finite checker proves strict
containment, winding four, full-line clearance and the requested accuracy.

No Newton-convergence hypothesis or caller search budget is needed.  Failure
of the bounded shortcut retains the original unconditional finite fallback.
The selected root is whichever checked seed succeeds first; no equality with
the old extractor's ordering of independent roots is asserted.
-/

namespace Purelib.RootIsolation.Newton.Extraction.Initial.Search

/-- The proper real-coordinate cell of the actual retained Gaussian region. -/
@[expose] public def eventCell
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (current : State.Raw.RawWindingState p ambient) : Data.Rat.Interval.Proper.Cell :=
  ⟨⟨current.box.xLower, current.box.xUpper, current.box.x_valid⟩, current.proper.1⟩

/-- A finite real-axis event proposal with its actual coefficient and interval caches.

Zero projection and zero count are typed inconclusive outcomes. A nonzero
count retains the original event and the exact requested event refinement;
no Gaussian-root correspondence or successful Newton check is assumed.
-/
@[expose] public def SturmAttempt
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (current : State.Raw.RawWindingState p ambient) (width : Fraction.Rational) : Type :=
  (projected : {q : Dense.Rational.Basic.CoordinatePolynomial //
    q = Dense.Gaussian.Path.Axis.horizontalPathReal p 0}) ×
  Sum (PLift (projected.val.isZero = true))
    ((_nonzero : PLift (projected.val.isZero = false)) ×
      (count : {value : Int // value = Sturm.Count.Basic.sturmRootCount2 projected.val
        (eventCell current).interval.lower (eventCell current).interval.upper}) ×
      Sum (PLift (count.val = 0))
        ((event : {track : Sturm.Track.Interface.ZeroEventTrack projected.val //
          track.current.cell = eventCell current}) ×
          {refined : Sturm.Track.Interface.ZeroEventTrack projected.val //
            refined = event.val.request width}))

/-- Compute one coefficient-derived event proposal on the original region.

The real-axis polynomial, nonzero count and requested track are computed
once. Every successful event still supplies only a proposed center to the
original finite Gaussian checker.
-/
@[expose] public def sturm
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (current : State.Raw.RawWindingState p ambient) (width : Fraction.Rational) : SturmAttempt current width :=
  let projected := Dense.Gaussian.Path.Axis.horizontalPathReal p 0
  if zero : projected.isZero = true then
    ⟨⟨projected, rfl⟩, .inl ⟨zero⟩⟩
  else
    have nonzero : projected.isZero = false := by
      cases same : projected.isZero with
      | false => rfl
      | true => exact False.elim (zero same)
    let count := Sturm.Count.Basic.sturmRootCount2 projected
      (eventCell current).interval.lower (eventCell current).interval.upper
    if empty : count = 0 then
      ⟨⟨projected, rfl⟩, .inr ⟨⟨nonzero⟩, ⟨count, rfl⟩, .inl ⟨empty⟩⟩⟩
    else
      let event : Sturm.Track.Interface.ZeroEventTrack projected :=
        ⟨nonzero, ⟨eventCell current, empty⟩⟩
      let refined := event.request width
      ⟨⟨projected, rfl⟩, .inr ⟨⟨nonzero⟩, ⟨count, rfl⟩,
        .inr ⟨⟨event, rfl⟩, ⟨refined, rfl⟩⟩⟩⟩

/-- Read at most one checked-search proposal from the retained event attempt.

An unavailable event contributes no extra seed. The midpoint of an actual
refined event contributes the sole extra seed without repeating refinement.
-/
@[expose] public def sturmSeeds
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    {current : State.Raw.RawWindingState p ambient} {width : Fraction.Rational}
    (attempt : SturmAttempt current width) : List Gaussian.Basic.Canonical :=
  match attempt with
  | ⟨_, .inl _⟩ => []
  | ⟨_, .inr ⟨_, _, .inl _⟩⟩ => []
  | ⟨_, .inr ⟨_, _, .inr ⟨_, refined⟩⟩⟩ =>
      [⟨Data.Rat.Interval.Bisection.midpoint refined.val.current.cell.interval, 0⟩]

/-- An event attempt contributes at most one additional original Newton seed. -/
public theorem sturmSeeds_length_le
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    {current : State.Raw.RawWindingState p ambient} {width : Fraction.Rational}
    (attempt : SturmAttempt current width) : (sturmSeeds attempt).length ≤ 1 := by
  rcases attempt with ⟨projected, zero | ⟨nonzero, count, empty | event⟩⟩
  · exact Nat.zero_le 1
  · exact Nat.zero_le 1
  · exact Nat.le_refl 1

/-- Retain the first completely checked root refinement in the supplied seed list.

Each seed supplies the original bounded Newton search. The first accepted
certificate is returned directly; exhaustion returns none without repeating
an accepted iteration or certificate construction. -/
@[expose] public def search {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient
  : Box} {degreeBound :
  Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient)
    (epsilon : Fraction.Rational) : List Gaussian.Basic.Canonical →
    Option (Refinement current epsilon)
  | [] => none
  | center :: rest =>
      match Newton.Search.Iteration.search elimination current epsilon 6 0 center with
      | some accepted => some accepted
      | none => Purelib.RootIsolation.Newton.Extraction.Initial.Search.search elimination current epsilon rest
end Purelib.RootIsolation.Newton.Extraction.Initial.Search
