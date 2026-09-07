import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk012

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard012_positionTrace (token : Unit) :
    (geometricShard012Summary token).range.run.positionTrace =
      PositionTrace.consecutive 192 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
