import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk006

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard006_positionTrace (token : Unit) :
    (geometricShard006Summary token).range.run.positionTrace =
      PositionTrace.consecutive 96 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
