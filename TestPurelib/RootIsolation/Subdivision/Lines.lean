module

import Purelib.RootIsolation.Subdivision.WindingOne

/-!
# Retained ambient-line subdivision reconstruction

The quantified client retains actual canonical coordinate values and accepts
full line certificates independently of their producers. Provider agreement
recovers the complete original step, including the selected state's caches.
-/

namespace TestPurelib.RootIsolation.Subdivision.Lines

open Purelib.RootIsolation
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Purelib.Polynomial.Clearance.Box.Line.Basic (VerticalLineClearance HorizontalLineClearance)

variable {p : CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}

/-- Reconstruct a step using only the retained coordinates and supplied ambient columns. -/
private def restored (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound) (current : WindingOneState p ambient)
    (cuts : Subdivision.WindingOne.Coordinates elimination current)
    (vertical : VerticalLineClearance p ambient cuts.x)
    (horizontal : HorizontalLineClearance p ambient cuts.y) : Subdivision.WindingOne.Step current :=
  Subdivision.WindingOne.fromLines input elimination current cuts vertical horizontal

/-- Every provider-equal column pair restores the whole original step for every original owner. -/
private theorem restored_eq (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound) (current : WindingOneState p ambient)
    (cuts : Subdivision.WindingOne.Coordinates elimination current)
    (provider : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination)
    (vertical : VerticalLineClearance p ambient cuts.x)
    (horizontal : HorizontalLineClearance p ambient cuts.y)
    (verticalEq : vertical = provider.vertical ambient cuts.x cuts.vertical_spec.1)
    (horizontalEq : horizontal = provider.horizontal ambient cuts.y cuts.horizontal_spec.1) :
    restored input elimination current cuts vertical horizontal =
      Subdivision.WindingOne.refineOnce input elimination current provider :=
  Subdivision.WindingOne.fromLines_eq_refineOnce
    input elimination current cuts provider vertical horizontal verticalEq horizontalEq

end TestPurelib.RootIsolation.Subdivision.Lines
