import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk185

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard185_positionTrace (token : Unit) :
    (geometricShard185Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2960 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
