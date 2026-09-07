import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk145

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard145_positionTrace (token : Unit) :
    (geometricShard145Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2320 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
