module

import Purelib.Data.Gaussian.Certificate.Raw
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Certificate.Raw
public import Purelib.Geometry.Rational.Box.Certificate
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Gaussian.Certificate.Raw (GaussianData)
open Purelib.Data.Rat.Certificate.Raw (RationalData)

open Purelib.Data

open Purelib

open Purelib.Geometry.Rational

public section

/-!
# Kernel verifier for generated quartic period data

The companion Python program performs only search and exact integer
arithmetic.  This module is the trust boundary: generated certificates store
displayed integer numerators and positive natural denominators, and the Lean
kernel checks the resulting cross-products before any fact is promoted to a
statement about constructive rationals.

Keeping the unreduced displayed fractions as data is deliberate.  It avoids
asking the elaborator to normalize a large expression in the canonical
rational implementation merely to check an inequality.
-/

namespace Purelib.RootIsolation.Certificate.Approximation

set_option genInjectivity false in
/-- Pure generated data for one rational approximation to a selected square
root.  All proof fields reduce to comparisons of integer cross-products. -/
structure RootApproximationCertificate where
  /-- The displayed Gaussian parameter whose square root is approximated. -/ parameter :
    GaussianData
  /-- The displayed Gaussian rational candidate. -/ candidate : GaussianData
  /-- The retained rational box containing the candidate. -/ sourceBox : Box.Certificate.RationalBoxData
  /-- The displayed upper bound for the candidate's squared residual norm. -/ residualUpper :
    RationalData
  /-- The displayed lower bound for the candidate's squared norm. -/ candidateNormLower :
    RationalData
  /-- An exact integer cross-product check bounds the squared residual norm. -/ residualChecked :
    Data.Rat.Certificate.Raw.RationalData.Le
    ((candidate.mul candidate).sub parameter).normSq residualUpper
  /-- Exact rational comparisons place the candidate in the retained box. -/ insideChecked : sourceBox.Contains
    candidate
  /-- An exact integer cross-product check proves the candidate norm lower bound. -/ normLowerChecked :
    Data.Rat.Certificate.Raw.RationalData.Le candidateNormLower candidate.normSq

constructive_injectivity RootApproximationCertificate

namespace RootApproximationCertificate

open Purelib.RootIsolation
/-- The checked raw residual bound holds after conversion to canonical Gaussian rationals. -/
theorem residual_le (certificate :
  Certificate.Approximation.RootApproximationCertificate) :
    Data.Gaussian.Norm.Basic.normSq
        (certificate.candidate.toGaussian *
            certificate.candidate.toGaussian -
          certificate.parameter.toGaussian) <=
      certificate.residualUpper.toRational := by
  rw [← GaussianData.mul_toGaussian, ← GaussianData.sub_toGaussian,
    ← GaussianData.normSq_toRational]
  exact RationalData.le_sound certificate.residualChecked

/-- The candidate lies in the retained box after conversion to canonical rational coordinates. -/
theorem candidate_inside
  (certificate : Certificate.Approximation.RootApproximationCertificate) :
    certificate.sourceBox.toBox.Contains
      certificate.candidate.toGaussian :=
  Box.Certificate.RationalBoxData.contains_sound certificate.insideChecked

/-- The checked lower bound holds for the canonical candidate's squared norm. -/
theorem candidate_norm_lower
  (certificate : Certificate.Approximation.RootApproximationCertificate) :
    certificate.candidateNormLower.toRational <=
      Data.Gaussian.Norm.Basic.normSq
        certificate.candidate.toGaussian := by
  rw [← GaussianData.normSq_toRational]
  exact RationalData.le_sound certificate.normLowerChecked

end RootApproximationCertificate

end Purelib.RootIsolation.Certificate.Approximation

end
