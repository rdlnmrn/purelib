module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RootIsolation.Newton.Extraction.Source
import Purelib.RootIsolation.Subdivision.Raw.Iteration.Forward
public import Purelib.RootIsolation.Subdivision.Raw.Rebase
import Purelib.RootIsolation.Subdivision.Raw.Request
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-! Restore the original Newton source selection from checked safe-subdivision
stages, then reuse that source in the unchanged local extraction construction.
The source ownership equation is exact, including its boundary bound. -/
namespace Purelib.RootIsolation.Newton.Extraction.Source.Replay

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
  (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
  (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational)

/-- Read the original squarefree Newton source threshold for the retained state and requested accuracy. -/
def threshold : Fraction.Rational :=
  Dense.Gaussian.Newton.Box.Budget.Squarefree.sourceDiagonalThreshold squarefree current.box current.clearance epsilon

/-- A positive accuracy request makes the original retained source threshold strictly positive. -/
theorem threshold_positive (positive : 0 < epsilon) : 0 <
  threshold squarefree current epsilon :=
  Dense.Gaussian.Newton.Box.Budget.Squarefree.sourceDiagonalThreshold_pos squarefree current.clearance current.proper
    positive

/-- Compute the original finite raw-subdivision depth for the retained Newton source threshold. -/
def depth : Nat := Subdivision.Raw.Request.refinementDepth
  (Subdivision.Raw.Rebase.initial current) (threshold squarefree current epsilon)

/-- A cached raw state equal to the original forward subdivision at its computed source depth. -/
abbrev Refined := {state : State.Raw.RawWindingState p
  current.box //
  state = Subdivision.Raw.Iteration.Forward.refineForwardN elimination (depth squarefree
    current epsilon) (Subdivision.Raw.Rebase.initial current)}

/-- Restore the checked Newton source output from its retained raw-state cache.

The saved equality transports the original finite subdivision bound without recomputing the source state. -/
def source (positive : 0 < epsilon) (saved :
  Refined squarefree elimination current epsilon) :
    Newton.Extraction.Source.SourceOutput squarefree current epsilon where
  source := saved.val
  diagonalSq_le := by
    rw [saved.property]
    exact Subdivision.Raw.Request.refineTo_diagonalSq_le elimination (Subdivision.Raw.Rebase.initial current)
      (threshold_positive squarefree current epsilon positive)

/-- Restoring the checked raw-state cache gives the exact original selected Newton source. -/
theorem source_eq (positive : 0 < epsilon) (saved :
  Refined squarefree elimination current epsilon) :
    source squarefree elimination current epsilon positive saved =
      Newton.Extraction.Source.selectSource squarefree elimination current positive := by
  rcases saved with ⟨value, same⟩
  cases same
  rfl
end Purelib.RootIsolation.Newton.Extraction.Source.Replay

end
