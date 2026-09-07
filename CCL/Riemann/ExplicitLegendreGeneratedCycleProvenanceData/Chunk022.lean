import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk022

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard022_positionTrace (token : Unit) :
    (geometricShard022Summary token).range.run.positionTrace =
      PositionTrace.consecutive 352 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
