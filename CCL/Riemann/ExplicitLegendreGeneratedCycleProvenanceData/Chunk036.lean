import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk036

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard036_positionTrace (token : Unit) :
    (geometricShard036Summary token).range.run.positionTrace =
      PositionTrace.consecutive 576 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
