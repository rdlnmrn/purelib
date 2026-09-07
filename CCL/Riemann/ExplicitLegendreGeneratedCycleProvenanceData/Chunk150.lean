import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk150

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard150_positionTrace (token : Unit) :
    (geometricShard150Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2400 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
