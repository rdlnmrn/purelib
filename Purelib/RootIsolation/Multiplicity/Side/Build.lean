module
import Purelib.Data.Rat.Fraction.Basic
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

open Purelib.Data.Rat.Fraction (Rational)

section
public section

open Purelib.Polynomial.Dense.Gaussian

/-!
# Total finite rational-function zero and pole sites

This module packages the signed multiplicity theorem over every finite
degree branch.  Linear factors return only exact displayed Gaussian-rational
zeros or poles.  Higher factors retain shrinking box tracks.  Constants have
no finite sites, and the identically-zero numerator has its own constructor.
-/

namespace Purelib.RootIsolation.Multiplicity.Side.Build

universe u

open Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Dense.Gaussian.Squarefree.Decomposition

/-- Consume the original constant or positive preprocessing branch of a normalized coprime side.

The positive callback receives the actual retained input and its original
preprocessing identity. Pure construction and checked replay share this
same branch selection, source certificates and original multiplicity data.
-/
@[expose] def withInput {α : Sort u}
    (source opposite : CoefficientPolynomial)
    (sourceNormalized : source.normalize = source)
    (sourceNonzero : source.isZero = false)
    (oppositeNonzero : opposite.isZero = false)
    (coprime : Coprime.Basic.CoprimeCertificate source opposite)
    (constant : (degreeZero : source.natDegree = 0) →
      Compute.preprocess source = .constant sourceNonzero degreeZero → α)
    (positive : (input : PositiveSideInput source opposite) →
      Compute.preprocess source = .positive input.preprocessing →
      input.sourceOppositeCoprime = coprime → α) : α := by
  match preprocessing : Compute.preprocess source with
  | .zero certificate =>
      rw [sourceNonzero] at certificate
      exact Bool.noConfusion certificate
  | .constant _ degreeZero => exact constant degreeZero preprocessing
  | .positive retained =>
      let input : PositiveSideInput source opposite :=
        { sourceNormalized := sourceNormalized
          preprocessing := retained
          oppositeNonzero := oppositeNonzero
          sourceOppositeCoprime := coprime }
      exact positive input preprocessing rfl

/-- Construct the finite multiplicity-aware result for a normalized nonzero side of a coprime pair.

The shared original preprocessing selects the constant or positive branch.
The positive branch constructs and retains its complete original factor family.
-/
@[expose] def buildSide
    (source opposite : CoefficientPolynomial)
    (sourceNormalized : source.normalize = source)
    (sourceNonzero : source.isZero = false)
    (oppositeNonzero : opposite.isZero = false)
    (coprime : Coprime.Basic.CoprimeCertificate source opposite)
    (request : Option Rational := none) :
    Multiplicity.Side.Basic.SideResult source opposite :=
  withInput source opposite sourceNormalized sourceNonzero oppositeNonzero coprime
    (fun degreeZero _ => .constant sourceNonzero degreeZero oppositeNonzero)
    (fun input _ _ => .positive input (input.buildFamily request))

/-- The original constant preprocessing branch yields the same complete constant side result. -/
theorem buildSide_eq_constant
    (source opposite : CoefficientPolynomial)
    (sourceNormalized : source.normalize = source)
    (sourceNonzero : source.isZero = false)
    (oppositeNonzero : opposite.isZero = false)
    (coprime : Coprime.Basic.CoprimeCertificate source opposite)
    (degreeZero : source.natDegree = 0)
    (same : Compute.preprocess source = .constant sourceNonzero degreeZero)
    (request : Option Rational := none) :
    buildSide source opposite sourceNormalized sourceNonzero oppositeNonzero coprime request =
      .constant sourceNonzero degreeZero oppositeNonzero := by
  unfold buildSide withInput
  rewrite [same]
  rfl

/-- Original positive preprocessing and a retained original family yield the same complete side result. -/
theorem buildSide_eq_positive
    (source opposite : CoefficientPolynomial)
    (sourceNormalized : source.normalize = source)
    (sourceNonzero : source.isZero = false)
    (oppositeNonzero : opposite.isZero = false)
    (coprime : Coprime.Basic.CoprimeCertificate source opposite)
    (input : PositiveSideInput source opposite)
    (same : Compute.preprocess source = .positive input.preprocessing)
    (coprimeSame : input.sourceOppositeCoprime = coprime) (request : Option Rational := none) :
    buildSide source opposite sourceNormalized sourceNonzero oppositeNonzero coprime request =
      .positive input (input.buildFamily request) := by
  cases input
  cases coprimeSame
  unfold buildSide withInput
  rewrite [same]
  rfl

/-- The absent event request preserves both complete original preprocessing branches. -/
theorem buildSide_none
    (source opposite : CoefficientPolynomial)
    (sourceNormalized : source.normalize = source) (sourceNonzero : source.isZero = false)
    (oppositeNonzero : opposite.isZero = false)
    (coprime : Coprime.Basic.CoprimeCertificate source opposite) :
    buildSide source opposite sourceNormalized sourceNonzero oppositeNonzero coprime none =
      withInput source opposite sourceNormalized sourceNonzero oppositeNonzero coprime
        (fun degreeZero _ => .constant sourceNonzero degreeZero oppositeNonzero)
        (fun input _ _ => .positive input input.buildFamily) := rfl

end Purelib.RootIsolation.Multiplicity.Side.Build

namespace Purelib.RootIsolation.Multiplicity.Side.Basic.SideResult

open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

/-- The actual higher tracks at every retained side observation have their original Newton constructors. -/
@[expose] def NewtonOrigins {source opposite : CoefficientPolynomial} : SideResult source opposite → Prop
  | .constant _ _ _ => True
  | .positive _ family => ∀ index, (family.observationAt index).NewtonOrigins

end Purelib.RootIsolation.Multiplicity.Side.Basic.SideResult

namespace Purelib.RootIsolation.Multiplicity.Side.Build

open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Dense.Gaussian.Squarefree.Decomposition

/-- Original side preprocessing and its retained family preserve every higher track's complete Newton origin. -/
theorem buildSide_newtonOrigins
    (source opposite : CoefficientPolynomial) (sourceNormalized : source.normalize = source)
    (sourceNonzero : source.isZero = false) (oppositeNonzero : opposite.isZero = false)
    (coprime : Coprime.Basic.CoprimeCertificate source opposite) (request : Option Rational) :
    (buildSide source opposite sourceNormalized sourceNonzero oppositeNonzero coprime request).NewtonOrigins := by
  cases preprocessing : Compute.preprocess source with
  | zero certificate =>
      have impossible : false = true := sourceNonzero.symm.trans certificate
      exact Bool.noConfusion impossible
  | constant nonzero degreeZero =>
      rewrite [buildSide_eq_constant source opposite sourceNormalized sourceNonzero oppositeNonzero
        coprime degreeZero preprocessing request]
      exact True.intro
  | positive retained =>
      let input : PositiveSideInput source opposite :=
        { sourceNormalized := sourceNormalized
          preprocessing := retained
          oppositeNonzero := oppositeNonzero
          sourceOppositeCoprime := coprime }
      rewrite [buildSide_eq_positive source opposite sourceNormalized sourceNonzero oppositeNonzero
        coprime input preprocessing rfl request]
      exact input.buildFamily_newtonOrigins request

end Purelib.RootIsolation.Multiplicity.Side.Build

end
