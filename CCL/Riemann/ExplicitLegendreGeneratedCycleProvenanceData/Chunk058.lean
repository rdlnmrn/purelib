import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk058

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard058_positionTrace (token : Unit) :
    (geometricShard058Summary token).range.run.positionTrace =
      PositionTrace.consecutive 928 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
