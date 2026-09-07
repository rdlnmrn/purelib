import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk146

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard146_positionTrace (token : Unit) :
    (geometricShard146Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2336 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
