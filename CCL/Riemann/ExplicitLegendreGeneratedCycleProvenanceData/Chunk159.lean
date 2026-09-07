import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk159

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard159_positionTrace (token : Unit) :
    (geometricShard159Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2544 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
