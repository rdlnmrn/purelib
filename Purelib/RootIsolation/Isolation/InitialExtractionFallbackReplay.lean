module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.RootIsolation.Newton.Band.Build
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.Newton.Extraction.Initial.Build

public import Purelib.RootIsolation.Isolation.InitialExtractionReplay
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

@[expose] public section

/-! Restore the original total initial-extraction branch after every bounded
seed has missed. The retained band belongs to the canonical Newton extraction,
not to an independently selected root. -/
namespace Purelib.RootIsolation.Isolation.InitialExtractionReplay

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
  (degreeAtLeastTwo : 2 ≤ p.natDegree) (squarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
  (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational)
  (positive : 0 < epsilon)

/-- A retained Newton-band output equal to the original fallback extraction on the same inputs. -/
abbrev SavedBand := {band : Newton.Band.Basic.Output squarefree current epsilon //
  band = Newton.Band.Build.extract degreeAtLeastTwo squarefree elimination current positive}

/-- Read the requested refinement directly from the retained original fallback band.

The construction reuses its exact state box, boundary and ambient line clearances, strict containment and requested
accuracy certificate. -/
def fallback (saved : SavedBand degreeAtLeastTwo squarefree elimination current epsilon positive) :
    Refinement current epsilon :=
  { state :=
      { box := saved.val.box
        refinesAmbient := saved.val.refinesAmbient
        proper := saved.val.proper
        clearance := saved.val.clearance
        rawWindingFour := saved.val.rawWindingFour
        ambientLeftClearance := saved.val.ambientLeftClearance
        ambientRightClearance := saved.val.ambientRightClearance
        ambientBottomClearance := saved.val.ambientBottomClearance
        ambientTopClearance := saved.val.ambientTopClearance }
    strict := saved.val.strictCurrent
    accurate := saved.val.diagonalSq_le }

/-- After the retained canonical seed search fails, reading its saved fallback band equals the original total extractor
exactly. -/
theorem fallback_eq (replay : Replay elimination current epsilon) (missed : replay.value = none)
    (saved : SavedBand degreeAtLeastTwo squarefree elimination current epsilon positive) :
    fallback degreeAtLeastTwo squarefree elimination current epsilon positive saved =
      Newton.Extraction.Initial.Build.extract degreeAtLeastTwo squarefree elimination current positive := by
  rcases saved with ⟨band, same⟩
  cases same
  unfold Newton.Extraction.Initial.Build.extract
  rw [replay.equation, missed]
  rfl

end Purelib.RootIsolation.Isolation.InitialExtractionReplay
