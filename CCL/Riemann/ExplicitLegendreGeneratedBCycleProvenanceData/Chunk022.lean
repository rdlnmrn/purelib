import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk022

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard022_positionTrace (token : Unit) :
    (geometricShard022Summary token).range.run.positionTrace =
      PositionTrace.consecutive 176 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
