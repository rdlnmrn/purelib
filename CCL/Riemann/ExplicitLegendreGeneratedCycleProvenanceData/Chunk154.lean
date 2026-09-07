import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk154

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard154_positionTrace (token : Unit) :
    (geometricShard154Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2464 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
