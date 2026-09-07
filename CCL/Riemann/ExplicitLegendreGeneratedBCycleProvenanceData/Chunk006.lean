import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk006

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard006_positionTrace (token : Unit) :
    (geometricShard006Summary token).range.run.positionTrace =
      PositionTrace.consecutive 48 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
