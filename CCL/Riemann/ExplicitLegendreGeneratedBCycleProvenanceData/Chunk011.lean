import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk011

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard011_positionTrace (token : Unit) :
    (geometricShard011Summary token).range.run.positionTrace =
      PositionTrace.consecutive 88 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
