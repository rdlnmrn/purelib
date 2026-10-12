module
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.Newton.Build
import Purelib.RootIsolation.Track.Newton.Refinement

import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

public section

/-! Every track produced by canonical isolation retains the original Newton
refinement operation, for every supplied current state. This identifies the
operation needed when restoring branch-cell refinements from checkpoints. -/
namespace Purelib.RootIsolation.Track.Newton

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
  (degreeAtLeastTwo : 2 ≤ p.natDegree) (squarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)

/-- Every positive-width refinement of this track equals the original checked Newton refinement. -/
@[expose] def Canonical (track : Basic.WindingOneTrack p ambient) : Prop :=
  ∀ (current : State.WindingOne.Basic.WindingOneState p ambient) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon),
    track.refine current epsilon positive = Track.Newton.Refinement.refineState degreeAtLeastTwo squarefree elimination
      current epsilon positive

namespace Canonical

/-- Every track in the displayed finite list has the original canonical Newton refinement. -/
@[expose] def All (tracks : List (Basic.WindingOneTrack p ambient)) : Prop :=
  ∀ track ∈ tracks, Canonical degreeAtLeastTwo squarefree elimination track

/-- The original Newton track built from an initial winding-one state is canonical. -/
theorem initial (state : State.WindingOne.Basic.WindingOneState p ambient) :
    Canonical degreeAtLeastTwo squarefree elimination (Track.Newton.Build.ofInitial
      degreeAtLeastTwo squarefree elimination state) := by
  intro current epsilon positive
  rfl

/-- The empty track list satisfies pointwise canonical refinement. -/
theorem nil : Track.Newton.Canonical.All (ambient := ambient) degreeAtLeastTwo squarefree elimination [] := by
  intro track member
  nomatch member

/-- Prepending one canonical Newton track preserves canonical refinement of the whole list. -/
theorem cons {track : Basic.WindingOneTrack p ambient} {tracks : List
  (Basic.WindingOneTrack p ambient)}
    (head : Canonical degreeAtLeastTwo squarefree elimination track)
    (tail : Track.Newton.Canonical.All degreeAtLeastTwo squarefree elimination tracks) :
    Track.Newton.Canonical.All degreeAtLeastTwo squarefree elimination (track :: tracks) := by
  intro found member
  rcases Purelib.Data.List.Membership.mem_cons.mp member with same | member
  · cases same
    exact head
  · exact tail found member

end Canonical

end Purelib.RootIsolation.Track.Newton

end
