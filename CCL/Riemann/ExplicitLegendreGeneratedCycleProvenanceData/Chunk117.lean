import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk117

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard117_positionTrace (token : Unit) :
    (geometricShard117Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1872 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
