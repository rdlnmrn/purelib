import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificateData.Chunk005

/-!
Shard-local row-order provenance for generated Legendre B-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard005_positionTrace (token : Unit) :
    (geometricShard005Summary token).range.run.positionTrace =
      PositionTrace.consecutive 40 8 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
