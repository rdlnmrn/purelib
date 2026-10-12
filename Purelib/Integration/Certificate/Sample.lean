module

import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Certificate.Raw
public import Purelib.Data.Gaussian.Field
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Gaussian.Certificate.Raw (GaussianData)

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

namespace Purelib.Integration.Certificate.Sample

open Purelib.Data.Gaussian in
set_option genInjectivity false in
/-- An exact raw Gaussian sample whose product with the retained candidate is the supplied displacement.

The certificate stores executable raw data and a checked equality for that exact product, before requiring the candidate
to be nonzero. -/
structure CandidateIntegralSampleCertificate
    (candidate displacement : GaussianData) where
  /-- The retained executable raw Gaussian integral sample. -/ sample : GaussianData
  /-- The exact raw sample-candidate product equals the original displacement. -/ productChecked :
    Certificate.Raw.GaussianData.Eq (sample.mul candidate) displacement

constructive_injectivity CandidateIntegralSampleCertificate

namespace CandidateIntegralSampleCertificate

open Purelib in
open Purelib.Algebra in
open Purelib.Data.Gaussian in
/-- For a nonzero retained candidate, the checked sample equals displacement times the candidate's reciprocal. -/
theorem sample_eq {candidate
  displacement : GaussianData}
    (certificate : Integration.Certificate.Sample.CandidateIntegralSampleCertificate candidate displacement)
    (candidateNonzero : candidate.toGaussian ≠ 0) :
    certificate.sample.toGaussian =
      displacement.toGaussian * (1 / candidate.toGaussian) := by
  apply Field.mul_right_cancel_of_ne
    candidateNonzero
  calc
    certificate.sample.toGaussian * candidate.toGaussian =
        displacement.toGaussian := by
      rw [← GaussianData.mul_toGaussian]
      exact GaussianData.eq_sound certificate.productChecked
    _ = (displacement.toGaussian * (1 / candidate.toGaussian)) *
          candidate.toGaussian := by
      rw [Field.ExplicitField.div_eq_mul_inv,
        Basic.one_mul,
        Basic.mul_assoc,
        Field.inv_eq,
        Field.inv_mul _ candidateNonzero,
        Basic.mul_one]

end CandidateIntegralSampleCertificate

end Purelib.Integration.Certificate.Sample

end
