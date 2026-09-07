import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk026

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard026_positionTrace (token : Unit) :
    (geometricShard026Summary token).range.run.positionTrace =
      PositionTrace.consecutive 208 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
