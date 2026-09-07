import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk199

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard199_positionTrace (token : Unit) :
    (geometricShard199Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3184 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
