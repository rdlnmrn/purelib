module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute
public import Purelib.RootIsolation.Multiplicity.Side.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.RootIsolation.Multiplicity.Family.Build
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Total finite rational-function zero and pole sites

This module packages the signed multiplicity theorem over every finite
degree branch.  Linear factors return only exact displayed Gaussian-rational
zeros or poles.  Higher factors retain shrinking box tracks.  Constants have
no finite sites, and the identically-zero numerator has its own constructor.
-/

namespace Purelib.RootIsolation.Multiplicity.Side.Build

/-- Construct the finite multiplicity-aware result for a normalized nonzero side of a coprime pair.

Retain the original constant or positive preprocessing branch; the positive branch builds the complete original factor
family. -/
@[expose] def buildSide
    (source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (sourceNormalized : source.normalize = source)
    (sourceNonzero : source.isZero = false)
    (oppositeNonzero : opposite.isZero = false)
    (coprime : Dense.Gaussian.Coprime.Basic.CoprimeCertificate source opposite) :
    Multiplicity.Side.Basic.SideResult source opposite := by
  match preprocessing : Dense.Gaussian.Squarefree.Decomposition.Compute.preprocess source with
  | .zero certificate =>
      rw [sourceNonzero] at certificate
      exact Bool.noConfusion certificate
  | .constant _ degreeZero =>
      exact .constant sourceNonzero degreeZero oppositeNonzero
  | .positive positive =>
      let input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite :=
        { sourceNormalized := sourceNormalized
          preprocessing := positive
          oppositeNonzero := oppositeNonzero
          sourceOppositeCoprime := coprime }
      exact .positive input input.buildFamily

end Purelib.RootIsolation.Multiplicity.Side.Build

end
