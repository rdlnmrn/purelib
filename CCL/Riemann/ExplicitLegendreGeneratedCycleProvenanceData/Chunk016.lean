import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk016

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard016_positionTrace (token : Unit) :
    (geometricShard016Summary token).range.run.positionTrace =
      PositionTrace.consecutive 256 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
