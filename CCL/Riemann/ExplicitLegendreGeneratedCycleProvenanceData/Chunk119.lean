import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk119

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard119_positionTrace (token : Unit) :
    (geometricShard119Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1904 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
