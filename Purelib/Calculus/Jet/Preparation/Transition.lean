module
public import Purelib.Calculus.Jet.Preparation.Diagnostic

section
@[expose] public section

/-!
# Explicit finite failure states for partial progressive operations

Reciprocal, division, logarithm, chart transition, and branch selection are
not total operations on opaque CCL names.  Their constructors below consume a
finite evidence state and return either a constructed program or a visible
reason why the request cannot proceed.  Thus failure is data; it is never a
silent appeal to a completed nonzero value or a globally chosen branch.
-/

namespace Purelib.Calculus.Jet.Preparation.Transition
universe u

/-! ## Chart and branch transitions -/

/-- Finite evidence for chart overlap and branch alignment.

The supplied case retains both proofs. Missing overlap carries no proof, while missing alignment retains the overlap
proof already available. -/
inductive TransitionEvidence (overlap alignment : Prop) where
  /-- Retain both the overlap and alignment proofs. -/ | supplied : overlap → alignment →
    TransitionEvidence overlap alignment
  /-- Record that overlap evidence is still needed. -/ | missingOverlap :
    TransitionEvidence overlap alignment
  /-- Retain overlap evidence while recording missing alignment evidence. -/ | missingAlignment : overlap →
    TransitionEvidence overlap alignment

/-- The overlap and alignment proofs for a certified transition.

The two fields establish their respective supplied propositions independently; neither is inferred from the other. -/
structure TransitionProof (overlap alignment : Prop) : Type where
  /-- Proof of the required overlap proposition. -/ overlapProof : overlap
  /-- Proof of the required branch-alignment proposition. -/ alignmentProof : alignment

open Purelib.Calculus.Jet.Preparation
/-- Package supplied transition proofs or report the missing certificate kind.

Complete evidence produces the pair of proofs. The two incomplete evidence constructors produce the corresponding
overlap or alignment tag. -/
def transition {overlap alignment : Prop} :
    TransitionEvidence overlap alignment →
      Diagnostic.Decision (TransitionProof overlap alignment)
  | .supplied overlapProof alignmentProof =>
      .accepted ⟨overlapProof, alignmentProof⟩
  | .missingOverlap => .rejected .chartOverlap
  | .missingAlignment _ => .rejected .branchAlignment

/-- A transition with missing overlap evidence reports the chart-overlap tag. -/
@[simp] theorem transition_missing_overlap {overlap alignment : Prop}
  :
    (transition (overlap := overlap) (alignment := alignment)
      .missingOverlap).missing? = some .chartOverlap := rfl

/-- A transition with overlap but no alignment evidence reports the branch-alignment tag. -/
@[simp] theorem transition_missing_alignment {overlap alignment :
  Prop}
    (overlapProof : overlap) :
    (transition (.missingAlignment overlapProof :
      TransitionEvidence overlap alignment)).missing? =
        some .branchAlignment := rfl

end Purelib.Calculus.Jet.Preparation.Transition

end
