module
import Purelib.Topology.Knot.Braid.ThreeStrand.Word
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Run
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.State
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Comparison
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Curves.Legendre.Acquisition.Automatic.Basic
public import Purelib.Curves.Legendre.FractionalWords.Periods
import Purelib.Topology.Knot.Braid.Word.Basic
import Init.Prelude
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Output
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.FractionalAction.Integral

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words

open Purelib.Approximation.Gaussian.Name

open Purelib.Curves.Legendre.Acquisition

open Purelib.Curves.Legendre.FractionalWords

open Purelib.Topology.Knot

open Purelib.Topology.Knot.Braid

section
@[expose] public section

/-!
# Resumable automatic acquisition for stepwise dual words

Each cursor retains completed head and suffix preparations, plus the exact
current denominator search state. Exhausting a budget preserves the cursor;
resumption neither reconstructs earlier outputs nor starts their searches
again. The final preparation is consumed directly by the existing arbitrary
finite-word period theorem.
-/

namespace Purelib.Curves.Legendre.Acquisition.Automatic.Fold

/-- Starting the acquisition needs only an input ratio, finite word, and budget. Its exhausted cursor can be passed
straight back to `attempt`. -/
def attemptWord (tau : Coherent.CoherentNamed) (word :
  Braid.Word 3)
    (fuel : Nat) : Run.Result tau (Periods.periodBraidMatrices word) :=
  Run.attempt tau (Periods.periodBraidMatrices word) (State.initial tau (Periods.periodBraidMatrices word)) fuel

end Purelib.Curves.Legendre.Acquisition.Automatic.Fold

end

section
@[expose] public section

/-!
# Automatic finite-word dual period outputs

The public result caches the exact word matrix, its denominator preparation,
and the productive output. A positive enclosure constructs it directly;
bounded acquisition returns either this same result or an exact resumable
state. The transport proof is shared by both construction routes.
-/

namespace Purelib.Curves.Legendre.Acquisition.Automatic.Fold.Ready

/-- Any automatically constructed final output agrees with any fully prepared stepwise execution of the same dual word.
-/
def equivalent_fold {tau : Coherent.CoherentNamed} {word
  : ThreeStrand.Word}
    (result : Automatic.Basic.Ready tau word) (preparations : Periods.PeriodFoldPreparations word tau) :
    Gaussian.Equivalence.NamedEquivalent result.output.name
      (Fold.Basic.foldAction tau (Periods.periodBraidMatrices word) preparations).name := by
  rw [result.output_eq]
  exact NamedEquivalent.trans
    (Comparison.fractionalLinear_of_matrix_eq
      result.matrix_eq tau result.preparation
      (preparations.periodPreparation word tau))
    (Periods.periodOutput_equivalent_foldAction word tau preparations)
end Purelib.Curves.Legendre.Acquisition.Automatic.Fold.Ready

end
