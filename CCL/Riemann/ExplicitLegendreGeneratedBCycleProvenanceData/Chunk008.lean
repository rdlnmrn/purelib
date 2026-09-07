import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk008

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard008_positionTrace (token : Unit) :
    (geometricShard008Summary token).range.run.positionTrace =
      PositionTrace.consecutive 64 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
