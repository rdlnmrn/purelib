import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk001

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard001_positionTrace (token : Unit) :
    (geometricShard001Summary token).range.run.positionTrace =
      PositionTrace.consecutive 16 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
