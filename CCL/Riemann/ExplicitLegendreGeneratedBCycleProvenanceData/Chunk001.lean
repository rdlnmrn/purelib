import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk001

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard001_positionTrace (token : Unit) :
    (geometricShard001Summary token).range.run.positionTrace =
      PositionTrace.consecutive 8 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
