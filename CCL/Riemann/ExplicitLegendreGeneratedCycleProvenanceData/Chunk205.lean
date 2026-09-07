import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk205

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard205_positionTrace (token : Unit) :
    (geometricShard205Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3280 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
