import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk179

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard179_positionTrace (token : Unit) :
    (geometricShard179Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2864 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
