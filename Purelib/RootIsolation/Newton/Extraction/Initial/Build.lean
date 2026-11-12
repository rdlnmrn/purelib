module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RootIsolation.Newton.Band.Build
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.Raw

import Purelib.Data.Rat.Fraction.Order
public import Purelib.Geometry.Rational.Box.Sample.Five
public import Purelib.RootIsolation.Newton.Extraction.Initial.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

@[expose] public section

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

namespace Purelib.RootIsolation.Newton.Extraction.Initial.Build

/-- A retained complete result of the original ordered five-seed search. -/
def SearchCache
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational) : Type :=
  {value : Option (Refinement current epsilon) //
    value = Search.search elimination current epsilon (Box.Sample.Five.seeds current.box)}

/-- An actual optional event proposal bound to its exact opt-in width request. -/
def SturmCache
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (current : State.Raw.RawWindingState p ambient) (request : Option Fraction.Rational) : Type :=
  match request with
  | none => PUnit
  | some width => {attempt : Search.SturmAttempt current width // attempt = Search.sturm current width}

/-- Read the complete refinement directly from one actual retained Newton band.

The polynomial, original current, squarefree certificate and accuracy remain
its indices. The exact box, full clearances, winding and strictness are
retained without recomputing any part of the band.
-/
def fromBand
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    {squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
    {current : State.Raw.RawWindingState p ambient} {epsilon : Fraction.Rational}
    (output : Newton.Band.Basic.Output squarefree current epsilon) : Refinement current epsilon :=
  { state :=
      { box := output.box
        refinesAmbient := output.refinesAmbient
        proper := output.proper
        clearance := output.clearance
        rawWindingFour := output.rawWindingFour
        ambientLeftClearance := output.ambientLeftClearance
        ambientRightClearance := output.ambientRightClearance
        ambientBottomClearance := output.ambientBottomClearance
        ambientTopClearance := output.ambientTopClearance }
    strict := output.strictCurrent
    accurate := output.diagonalSq_le }

/-- Total initial extraction with checked speculative acceleration.  All
obligations are carried by the returned finite data, including in the
fallback branch; speculation is not an additional trust boundary. -/
def extract {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient)
    {epsilon : Fraction.Rational} (positive : 0 < epsilon)
    (request : Option Fraction.Rational := none)
    (cachedSearch : Option (SearchCache elimination current epsilon) := none)
    (cachedSturm : Option (SturmCache current request) := none) :
    Refinement current epsilon :=
  let fallback := fun (_ : Unit) =>
    fromBand (Newton.Band.Build.extract degreeAtLeastTwo squarefree elimination current positive)
  let first := match cachedSearch with
    | none => Search.search elimination current epsilon (Box.Sample.Five.seeds current.box)
    | some retained => retained.val
  match first with
  | some accepted => accepted
  | none =>
      match request with
      | none => fallback ()
      | some width =>
          let attempt := match cachedSturm with
            | none => Search.sturm current width
            | some retained => retained.val
          match Search.search elimination current epsilon (Search.sturmSeeds attempt) with
          | some accepted => accepted
          | none => fallback ()

end Purelib.RootIsolation.Newton.Extraction.Initial.Build

end

public section

namespace Purelib.RootIsolation.Newton.Extraction.Initial.Build

variable {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
  {degreeBound : Nat} (degreeAtLeastTwo : 2 ≤ p.natDegree)
  (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
  (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational} (positive : 0 < epsilon)

attribute [local irreducible] Newton.Band.Build.extract Search.search

/-- With no event request or supplied caches, the complete original five-seed/total-fallback result is retained. -/
theorem extract_none :
    extract degreeAtLeastTwo squarefree elimination current positive none none none =
      match Search.search elimination current epsilon (Box.Sample.Five.seeds current.box) with
      | some accepted => accepted
      | none => fromBand (Newton.Band.Build.extract degreeAtLeastTwo squarefree elimination current positive) := rfl

/-- Supplying the actual retained five-seed result preserves the complete requested extraction. -/
theorem extract_cachedSearch_eq_default (request : Option Fraction.Rational)
    (cached : SearchCache elimination current epsilon) (proposal : Option (SturmCache current request) := none) :
    extract degreeAtLeastTwo squarefree elimination current positive request (some cached) proposal =
      extract degreeAtLeastTwo squarefree elimination current positive request none proposal := by
  rcases cached with ⟨value, same⟩
  cases same
  rfl

/-- Supplying the actual retained event proposal preserves the complete requested extraction. -/
theorem extract_cachedSturm_eq_default (request : Option Fraction.Rational)
    (cached : SturmCache current request)
    (first : Option (SearchCache elimination current epsilon) := none) :
    extract degreeAtLeastTwo squarefree elimination current positive request first (some cached) =
      extract degreeAtLeastTwo squarefree elimination current positive request first none := by
  cases request with
  | none => rfl
  | some width =>
      rcases cached with ⟨value, same⟩
      cases same
      rfl

/-- An accepted original five-seed search remains authoritative for every opt-in event request. -/
theorem extract_of_first_success (value : Refinement current epsilon)
    (found : Search.search elimination current epsilon (Box.Sample.Five.seeds current.box) = some value)
    (request : Option Fraction.Rational := none) :
    extract degreeAtLeastTwo squarefree elimination current positive request = value := by
  calc
    extract degreeAtLeastTwo squarefree elimination current positive request =
        extract degreeAtLeastTwo squarefree elimination current positive request
          (some ⟨some value, found.symm⟩) :=
      (extract_cachedSearch_eq_default degreeAtLeastTwo squarefree elimination current positive
        request ⟨some value, found.symm⟩).symm
    _ = value := rfl

/-- The original five-seed result supplied as a cache is consumed directly before any event request. -/
theorem extract_of_cached_success (value : Refinement current epsilon)
    (found : some value = Search.search elimination current epsilon (Box.Sample.Five.seeds current.box))
    (request : Option Fraction.Rational := none) :
    extract degreeAtLeastTwo squarefree elimination current positive request (some ⟨some value, found⟩) = value :=
  rfl

/-- After the canonical seeds miss, the actual extra finite search selects the requested result.

The equality consumes the supplied complete five-seed and event caches.
The unsuccessful extra branch is the same original total extraction with
no event request; no successful proposal or root correspondence is assumed.
-/
theorem extract_sturm_eq (width : Fraction.Rational)
    (first : SearchCache elimination current epsilon) (missed : first.val = none)
    (proposal : SturmCache current (some width))
    (result : Option (Refinement current epsilon))
    (found : Search.search elimination current epsilon (Search.sturmSeeds proposal.val) = result) :
    extract degreeAtLeastTwo squarefree elimination current positive (some width) =
      match result with
      | some accepted => accepted
      | none => extract degreeAtLeastTwo squarefree elimination current positive := by
  have select : extract degreeAtLeastTwo squarefree elimination current positive
        (some width) (some first) (some proposal) =
      match result with
      | some accepted => accepted
      | none => extract degreeAtLeastTwo squarefree elimination current positive
          none (some first) := by
    rcases first with ⟨first, firstEq⟩
    dsimp only at missed
    cases missed
    change (match Search.search elimination current epsilon (Search.sturmSeeds proposal.val) with
      | some accepted => accepted
      | none => extract degreeAtLeastTwo squarefree elimination current positive
          none (some ⟨none, firstEq⟩)) = _
    cases result with
    | none =>
        exact congrArg (fun selected : Option (Refinement current epsilon) =>
          match selected with
          | some accepted => accepted
          | none => extract degreeAtLeastTwo squarefree elimination current positive
              none (some ⟨none, firstEq⟩)) found
    | some accepted =>
        exact congrArg (fun selected : Option (Refinement current epsilon) =>
          match selected with
          | some accepted => accepted
          | none => extract degreeAtLeastTwo squarefree elimination current positive
              none (some ⟨none, firstEq⟩)) found
  have sameFirst := extract_cachedSearch_eq_default degreeAtLeastTwo squarefree elimination current positive
    (some width) first (some proposal)
  have sameProposal := extract_cachedSturm_eq_default degreeAtLeastTwo squarefree elimination current positive
    (some width) proposal
  have sameFallback := extract_cachedSearch_eq_default degreeAtLeastTwo squarefree elimination current positive
    none first
  calc
    extract degreeAtLeastTwo squarefree elimination current positive (some width) =
        extract degreeAtLeastTwo squarefree elimination current positive
          (some width) (some first) (some proposal) := (sameFirst.trans sameProposal).symm
    _ = _ := select
    _ = _ := by
      cases result with
      | some accepted => rfl
      | none => exact sameFallback

end Purelib.RootIsolation.Newton.Extraction.Initial.Build

end
