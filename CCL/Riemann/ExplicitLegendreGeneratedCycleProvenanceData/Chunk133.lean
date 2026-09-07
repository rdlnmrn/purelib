import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk133

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard133_positionTrace (token : Unit) :
    (geometricShard133Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2128 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
