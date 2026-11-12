module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.Newton.Refinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free shrinking winding-one tracks

The local Newton-square extractor is stable under iteration because every
returned square carries a new finite boundary-clearance certificate.  This
module packages those repeated finite calls as the numerical track interface
used by box isolation and any independently shrinking finite envelope.
-/

namespace Purelib.RootIsolation.Track.Newton.Build

/-- Concrete total track generated from one winding-one state. -/
def ofInitial
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (initial : State.WindingOne.Basic.WindingOneState p ambient) : Track.Basic.WindingOneTrack p ambient where
  initial := initial
  refine := Track.Newton.Refinement.refineState degreeAtLeastTwo squarefree elimination
  nested := Track.Newton.Refinement.refineState_refines degreeAtLeastTwo squarefree elimination
  strict := Track.Newton.Refinement.refineState_strict degreeAtLeastTwo squarefree elimination
  accurate := Track.Newton.Refinement.refineState_accurate degreeAtLeastTwo squarefree elimination

/-- A retained track is the complete original Newton constructor on one actual initial state.

This exact existential view preserves the entire track, including its actual
refiner and initial owner. It neither chooses a replacement root nor infers
constructor identity from equal numerical readings.
-/
abbrev Origin
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p) {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (track : Track.Basic.WindingOneTrack p ambient) : Prop :=
  ∃ initial, track = ofInitial degreeAtLeastTwo squarefree elimination initial

/-- The original Newton constructor retains its actual complete initial state as an origin witness. -/
theorem ofInitial_origin
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p) {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (initial : State.WindingOne.Basic.WindingOneState p ambient) :
    Origin degreeAtLeastTwo squarefree elimination (ofInitial degreeAtLeastTwo squarefree elimination initial) :=
  ⟨initial, rfl⟩

/-- Whole original constructor identity supplies the actual Newton operation at each supplied state and accuracy. -/
theorem Origin.refine
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    {degreeAtLeastTwo : 2 ≤ p.natDegree}
    {squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p} {degreeBound : Nat}
    {elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound}
    {track : Track.Basic.WindingOneTrack p ambient}
    (origin : Origin degreeAtLeastTwo squarefree elimination track)
    (current : State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Purelib.Data.Rat.Fraction.Rational) (positive : 0 < epsilon) :
    track.refine current epsilon positive =
      Track.Newton.Refinement.refineState degreeAtLeastTwo squarefree elimination current epsilon positive := by
  rcases origin with ⟨initial, same⟩
  cases same
  rfl

end Purelib.RootIsolation.Track.Newton.Build

end
