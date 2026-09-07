import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk008

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard008_positionTrace (token : Unit) :
    (geometricShard008Summary token).range.run.positionTrace =
      PositionTrace.consecutive 128 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
