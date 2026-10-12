module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Data.Fin
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RootIsolation.Nonnegativity.Step
import Purelib.RootIsolation.State.Negative
import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

public section

/-!
# Choice-free global winding nonnegativity

If a clear box had negative raw winding, one eliminant-safe Newton band of
raw winding four can be removed and a negative complement cell retained.
Finite iteration would then create one more pairwise-separated shrinking
track than the explicit rational grid can contain.
-/

namespace Purelib.RootIsolation.Nonnegativity

open Purelib.Data

set_option genInjectivity false in
/-- After `count` removal steps, retain the current negative region and all
pairwise-separated tracks constructed so far.

The retained negative region and original finite track table have the same polynomial and ambient box. Each track
remains separated from every other retained track and every strict inner box of that current region. -/
structure Sequence
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box) (count : Nat)
      where
  /-- The negative-winding region retained after the displayed number of removal steps. -/ current :
    State.Negative.NegativeState p ambient
  /-- The exact finite family of extracted winding-one tracks indexed by the removal count. -/ tracks : Fin count →
    Track.Basic.WindingOneTrack p ambient
  /-- Tracks at distinct retained indices have separated initial boxes. -/ pairwise : ∀ i j, i ≠ j →
    (tracks i).initial.box.Separated (tracks j).initial.box
  /-- Every retained track avoids each strict inner box of the current negative region. -/ avoidsCurrent : ∀ i {small :
    Box},
    small.StrictInterior current.box →
      (tracks i).initial.box.Separated small

constructive_injectivity Sequence

namespace Sequence

/-- Start the negative-region removal sequence with the supplied state and no tracks.

The original negative state is retained verbatim, and the impossible Fin zero index supplies the empty track table and
its vacuous separation certificates. -/
@[expose] def nil
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (current : State.Negative.NegativeState p ambient) : Sequence p ambient 0 where
  current := current
  tracks := Fin.elim0
  pairwise := fun i => Fin.elim0 i
  avoidsCurrent := fun i => Fin.elim0 i

/-- Extract one new track and retain the selected negative complementary state.

The original finite indices are shifted behind the new track, preserving pairwise separation and avoidance of every
strict inner box of the current region. -/
@[expose] def step
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (sequence : Sequence p ambient count) : Sequence p ambient (count + 1) := open Purelib in by
  let extracted := Nonnegativity.Step.extractStep degreeAtLeastTwo squarefree elimination
    sequence.current
  let tracks : Fin (count + 1) → Track.Basic.WindingOneTrack p ambient :=
    fun index => Data.Fin.cases extracted.track sequence.tracks index
  exact
    { current := extracted.next
      tracks := tracks
      pairwise := by
        intro i
        refine Data.Fin.cases_induction ?_ (fun oldI => ?_) i
        · intro j
          refine Data.Fin.cases_induction ?_ (fun oldJ => ?_) j
          · intro different
            exact (different rfl).elim
          · intro _different
            exact Box.separated_symm
              (sequence.avoidsCurrent oldJ extracted.center_strict_current)
        · intro j
          refine Data.Fin.cases_induction ?_ (fun oldJ => ?_) j
          · intro _different
            exact sequence.avoidsCurrent oldI extracted.center_strict_current
          · intro different
            have oldDifferent : oldI ≠ oldJ := by
              intro equal
              apply different
              exact congrArg Fin.succ equal
            exact sequence.pairwise oldI oldJ oldDifferent
      avoidsCurrent := by
        intro i small strict
        refine Data.Fin.cases_induction ?_ (fun oldI => ?_) i
        · exact extracted.center_avoids_next strict
        · have strictCurrent := Box.Refinement.StrictInterior.GlobalNonnegativity.strictInterior_trans_refines
            strict
            extracted.next_refines_current
          exact sequence.avoidsCurrent oldI strictCurrent }

/-- Execute exactly the requested finite number of negative-region removal
steps.

Each successor count retains the actual preceding sequence and applies the same certified one-step extraction; neither
the selected negative cell nor earlier finite track indices are recomputed. -/
@[expose] def iterate
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
      :
    (count : Nat) → State.Negative.NegativeState p ambient → Sequence p ambient count
  | 0, current => Sequence.nil current
  | count + 1, current =>
      (Purelib.RootIsolation.Nonnegativity.Sequence.iterate degreeAtLeastTwo squarefree elimination count current).step
        degreeAtLeastTwo squarefree elimination

end Sequence

end Purelib.RootIsolation.Nonnegativity

end
