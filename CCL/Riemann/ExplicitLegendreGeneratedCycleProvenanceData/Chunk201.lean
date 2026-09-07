import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk201

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard201_positionTrace (token : Unit) :
    (geometricShard201Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3216 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
