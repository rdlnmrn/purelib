import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk228

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard228_positionTrace (token : Unit) :
    (geometricShard228Summary token).range.run.positionTrace =
      PositionTrace.consecutive 3648 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
