import CCL.Riemann.ExplicitLegendreNormalizedAcquisition
import CCL.Riemann.ExplicitLegendrePeriodTransport

/-!
# Explicit normalized Legendre monodromy

This downstream facade joins a successful lightweight normalization attempt
to the fully displayed standard-loop geometry.  Keeping the join separate
lets executable normalization clients avoid initializing the much larger
zero/one-loop data until they actually request a monodromy certificate.
-/

namespace CCL.Riemann.ExplicitLegendreNormalizedAcquisition

namespace ExplicitNormalizationCertificate

/-- The theorem-facing normalized payload at the explicit loop base. -/
def base (certificate : ExplicitNormalizationCertificate) :
    CCL.Riemann.LegendrePeriodMonodromy.NormalizedData
      CCL.Riemann.ExplicitLegendreSegment.sourceFrame where
  normalized := certificate.normalized

/-- Join an intrinsic A-period lower certificate to the displayed standard
loops without introducing an executable acquisition dependency. -/
def monodromyData (certificate : ExplicitNormalizationCertificate) :
    CCL.Riemann.LegendrePeriodMonodromy.Data
      CCL.Riemann.ExplicitLegendreOneLoop.standardLoops where
  base := certificate.base

/-- A uniform finite A-period theorem yields the unconditional
fraction-free standard-loop certificate directly. -/
def fractionFreeCertificate
    (certificate : ExplicitNormalizationCertificate) :
    CCL.Riemann.LegendrePeriodMonodromy.FractionFreeCertificate
      certificate.monodromyData :=
  CCL.Riemann.LegendrePeriodMonodromy.certificate certificate.monodromyData

end ExplicitNormalizationCertificate

namespace ProductiveExplicitNormalizationCertificate

/-- Productive denominator evidence extends, rather than replaces, the
unconditional fraction-free theorem. -/
def fractionFreeCertificate
    (certificate : ProductiveExplicitNormalizationCertificate) :=
  certificate.normalization.fractionFreeCertificate

/-- The two retained preparations feed the productive modular theorem at
their original process indices. -/
def certificate
    (prepared : ProductiveExplicitNormalizationCertificate) :
    CCL.Riemann.LegendrePeriodMonodromy.ProductiveCertificate
      prepared.normalization.monodromyData prepared.onePreparation
        prepared.infinityPreparation :=
  CCL.Riemann.LegendrePeriodMonodromy.productiveCertificate
    prepared.normalization.monodromyData prepared.onePreparation
      prepared.infinityPreparation

end ProductiveExplicitNormalizationCertificate

namespace Ready

def base {bound : Nat} (ready : Ready bound) :
    CCL.Riemann.LegendrePeriodMonodromy.NormalizedData
      CCL.Riemann.ExplicitLegendreSegment.sourceFrame where
  normalized := ready.normalized

/-- Concrete normalized data on the already-certified standard loops. -/
def monodromyData {bound : Nat} (ready : Ready bound) :
    CCL.Riemann.LegendrePeriodMonodromy.Data
      CCL.Riemann.ExplicitLegendreOneLoop.standardLoops where
  base := ready.base

/-- A successful finite normalization scan immediately yields the
unconditional fraction-free standard-loop theorem. -/
def fractionFreeCertificate {bound : Nat} (ready : Ready bound) :
    CCL.Riemann.LegendrePeriodMonodromy.FractionFreeCertificate
      ready.monodromyData :=
  CCL.Riemann.LegendrePeriodMonodromy.certificate ready.monodromyData

end Ready

namespace ProductiveReady

/-- The unconditional conclusions remain available from a productive result
without rebuilding the normalized data. -/
def fractionFreeCertificate {bound : Nat} (ready : ProductiveReady bound) :=
  ready.normalization.fractionFreeCertificate

/-- Both retained denominator preparations feed the dual productive theorem
without rebasing either process index. -/
def certificate {bound : Nat} (ready : ProductiveReady bound) :
    CCL.Riemann.LegendrePeriodMonodromy.ProductiveCertificate
      ready.normalization.monodromyData ready.onePreparation
        ready.infinityPreparation :=
  CCL.Riemann.LegendrePeriodMonodromy.productiveCertificate
    ready.normalization.monodromyData ready.onePreparation
      ready.infinityPreparation

end ProductiveReady

end CCL.Riemann.ExplicitLegendreNormalizedAcquisition
