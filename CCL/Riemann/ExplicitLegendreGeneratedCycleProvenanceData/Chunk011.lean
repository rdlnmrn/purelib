import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk011

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard011_positionTrace (token : Unit) :
    (geometricShard011Summary token).range.run.positionTrace =
      PositionTrace.consecutive 176 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
