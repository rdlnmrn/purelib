import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk236

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard236_positionTrace (token : Unit) :
    (geometricShard236Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3776 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
