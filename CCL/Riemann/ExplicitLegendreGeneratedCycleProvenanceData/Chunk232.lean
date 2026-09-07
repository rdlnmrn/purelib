import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk232

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard232_positionTrace (token : Unit) :
    (geometricShard232Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3712 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
