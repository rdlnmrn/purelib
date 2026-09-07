import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk005

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard005_positionTrace (token : Unit) :
    (geometricShard005Summary token).range.run.positionTrace =
      PositionTrace.consecutive 80 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
