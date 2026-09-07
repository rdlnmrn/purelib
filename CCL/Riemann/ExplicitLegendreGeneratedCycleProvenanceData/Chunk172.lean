import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk172

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard172_positionTrace (token : Unit) :
    (geometricShard172Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2752 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
