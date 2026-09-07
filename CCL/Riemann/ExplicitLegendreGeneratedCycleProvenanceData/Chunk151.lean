import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk151

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard151_positionTrace (token : Unit) :
    (geometricShard151Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2416 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
