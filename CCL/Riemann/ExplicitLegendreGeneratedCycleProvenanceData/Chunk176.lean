import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk176

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard176_positionTrace (token : Unit) :
    (geometricShard176Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2816 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
