import CCL.Encoding.CCF.Encoder
import CCL.Encoding.Baseline
import CCL.Encoding.Encoder

/-!
# Exact executable examples

The example expansions in the paper are checked against the executable CCF
and CCL encoders.  `native_decide` evaluates only finite integer/rational data;
the general termination and reconstruction facts are proved in the preceding
modules.
-/

namespace CCL

open Integral

namespace Examples

def threePlusFourIOverFive : Frac := ⟨⟨3, 4⟩, ⟨5, 0⟩, by decide⟩
def thirteenOverFive : Frac := ⟨⟨13, 0⟩, ⟨5, 0⟩, by decide⟩
def threeFiftyFiveOverOneThirteen : Frac := ⟨⟨355, 0⟩, ⟨113, 0⟩, by decide⟩

theorem ccf_threePlusFourIOverFive :
    CCFEncoder.encode threePlusFourIOverFive =
      [⟨0, 0⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨2, 0⟩] := by
  native_decide

theorem ccf_thirteenOverFive :
    CCFEncoder.encode thirteenOverFive =
      [⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨2, 2⟩] := by
  native_decide

theorem ccf_threeFiftyFiveOverOneThirteen :
    CCFEncoder.encode threeFiftyFiveOverOneThirteen =
      [⟨3, 0⟩, ⟨7, 7⟩, ⟨16, 0⟩] := by
  native_decide

/-- Readable notation for the paper's displayed raw bit strings. -/
def bits (s : String) : List Bool := s.toList.map (fun c => c = '1')

theorem continuedFraction_threeFiftyFiveOverOneThirteen :
    BaselineAlgorithms.cfEncode 355 113 (by decide) = [3, 7, 16] := by
  native_decide

theorem continuedLogarithm_threeFiftyFiveOverOneThirteen :
    BaselineAlgorithms.clEncode 355 113 (by decide) (by decide) =
      bits "1000100011100111001100101" := by
  native_decide

theorem continuedLogarithm_thirteenOverFive :
    BaselineAlgorithms.clEncode 13 5 (by decide) (by decide) = bits "101001" := by
  native_decide

theorem ccl_threePlusFourIOverFive_raw :
    CCLEncoder.encode threePlusFourIOverFive (by decide) =
      bits "00001100010011" := by
  native_decide

theorem ccl_threePlusFourIOverFive_blocks :
    CCLEncoder.encode threePlusFourIOverFive (by decide) =
      CCLDecoder.lowWord 0 .northEast ++
      CCLDecoder.regularWord 1 .northEast ++
      CCLDecoder.regularWord 0 .northWest := by
  native_decide

theorem ccl_thirteenOverFive_raw :
    CCLEncoder.encode thirteenOverFive (by decide) =
      bits "110110110111111000110001" := by
  native_decide

theorem ccl_thirteenOverFive_blocks :
    CCLEncoder.encode thirteenOverFive (by decide) =
      CCLDecoder.regularWord 2 .south ++
      CCLDecoder.regularWord 2 .southEast ++
      CCLDecoder.regularWord 3 .northEast ++
      CCLDecoder.regularWord 1 .northEast := by
  native_decide

theorem ccl_threeFiftyFiveOverOneThirteen_raw :
    CCLEncoder.encode threeFiftyFiveOverOneThirteen (by decide) =
      bits "11101011101001111011111001011111111010111111110111" := by
  native_decide

theorem ccl_threeFiftyFiveOverOneThirteen_blocks :
    CCLEncoder.encode threeFiftyFiveOverOneThirteen (by decide) =
      CCLDecoder.regularWord 3 .southWest ++
      CCLDecoder.regularWord 2 .west ++
      CCLDecoder.regularWord 4 .southEast ++
      CCLDecoder.regularWord 2 .north ++
      CCLDecoder.regularWord 8 .southWest ++
      CCLDecoder.regularWord 7 .southEast := by
  native_decide

end Examples

end CCL
