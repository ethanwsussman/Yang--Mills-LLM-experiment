import YangMills.Construction.Torus.BoundOnTheScaledRemainderBlocksProof
import YangMills.Construction.Torus.ApproximateInverseAndRemainderOfTheCubes
import YangMills.Construction.Torus.FloorOfTheInverseBounds
import YangMills.Construction.Torus.TermsOfTheChangeOfTheSequence
import YangMills.Construction.Torus.BoundsOnTheCompressedOperatorsProof
import YangMills.Construction.Torus.BoundsOnTheInversesOfTheCubes
import YangMills.Construction.Torus.ChangeOfTheSequenceOfACube
import YangMills.Construction.Torus.ColumnsOfTheGreenOperatorOnTheTori
import YangMills.Construction.Torus.CubesOfASequenceAreFinitelyMany
import YangMills.Construction.Torus.GeometryOfCubesAndCutSequences
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.GeneralTorus.RemainderTermsProof
open Set TorusMetric GreenBounds
noncomputable section
section Estimates
end Estimates
theorem coarseSpacing_pos {W : GaugeSetting} (c : W.CoarseBond) :
    0 < GaugeSetting.coarseSpacing c := by apply _root_.YangMills.Construction.GeneralTorus.CompressedBoundsProof.coarseSpacing_pos <;> assumption
section MatrixEntries
variable (hrows : CoarseBondFormsAndMatricesHold) (W : GaugeSetting)
include hrows
theorem matrixEntry_eq (K : Module.End ℝ W.CoarseField) (c c' : W.CoarseBond) :
    W.matrixEntry K c c' =
      (GaugeSetting.coarseSpacing c / GaugeSetting.coarseSpacing c') ^ 2 *
        K (W.coarseDelta c') c := by
  have h := (hrows W).2.2.2.2.2.2.2.1.1 K c c'
  have h1 := (coarseSpacing_pos c).ne'
  have h2 := (coarseSpacing_pos c').ne'
  unfold GaugeSetting.kernelEntry at h
  rw [h]
  field_simp
theorem matrixEntry_add (K K' : Module.End ℝ W.CoarseField) (c c' : W.CoarseBond) :
    W.matrixEntry (K + K') c c' = W.matrixEntry K c c' + W.matrixEntry K' c c' := by
  rw [matrixEntry_eq hrows, matrixEntry_eq hrows, matrixEntry_eq hrows, LinearMap.add_apply,
    Pi.add_apply]
  ring
theorem matrixEntry_sub (K K' : Module.End ℝ W.CoarseField) (c c' : W.CoarseBond) :
    W.matrixEntry (K - K') c c' = W.matrixEntry K c c' - W.matrixEntry K' c c' := by
  rw [matrixEntry_eq hrows, matrixEntry_eq hrows, matrixEntry_eq hrows, LinearMap.sub_apply,
    Pi.sub_apply]
  ring
theorem matrixEntry_comp (K K' : Module.End ℝ W.CoarseField) (c c'' : W.CoarseBond) :
    W.matrixEntry (K ∘ₗ K') c c'' =
      ∑ᶠ c' : W.CoarseBond, W.matrixEntry K c c' * W.matrixEntry K' c' c'' := (hrows W).2.2.2.2.2.2.2.1.2.1 K K' c c''
end MatrixEntries
structure Hypotheses (C : CubeGaugeSetting) (m K t : ℕ) : Prop where
  standingConstraints : CoarseBondFormsAndMatricesHold
  cols : GreenColumnsStatement
  inner : InnerProductsAdjointsProjections.SettingInnerProductFacts
  cells : SeparatedChainStructure
  floors : InverseBoundsStatement
  geom : CubeGeometryAndLocalChains
  cube : CubeInverseBounds
  change : LocalChainChange
  comp : CubeGreenCompression
  fin : ChainCubesFinite
  read : GreenBoundsStatement
  onTorus : C.IsExpansionSetting m K t
  above : C.ChangeAboveThresholds
namespace Hypotheses
variable {C : CubeGaugeSetting} {m K t : ℕ} (G : Hypotheses C m K t)
include G
theorem L_pos : 0 < C.data.L := by
  have := C.data.blocking.thirteen_le
  omega
theorem L_le_blockCount : C.data.L ≤ C.data.blockCount := by
  have := C.twelve_mul_L_le_blockCount
  omega
theorem blockCount_pos : (0 : ℝ) < (C.data.blockCount : ℝ) := by
  have h1 := G.L_pos
  have h2 := G.L_le_blockCount
  exact_mod_cast (by omega : 0 < C.data.blockCount)
theorem rate_pos : 0 < (chosen C.data.L).rate :=
  (G.read C.data.L C.data.blocking).rate_pos
theorem decayRateOfInverse_pos : 0 < InverseBounds.decayRateOfInverse C.data.L :=
  (G.floors.1 C.data.L C.data.blocking).1
theorem decayRateOfInverse_le :
    InverseBounds.decayRateOfInverse C.data.L ≤ (chosen C.data.L).rate / 4 :=
  (G.floors.1 C.data.L C.data.blocking).2.1
theorem gapLower_le : (chosen C.data.L).gapLower ≤
    (C.data.gapCount : ℝ) * (C.data.blockCount : ℝ) :=
  (G.floors.1 C.data.L C.data.blocking).2.2.trans G.above.2
theorem sum_exp_le (c : C.CoarseBond) :
    ∑ᶠ c₁ : C.CoarseBond,
        Real.exp (-((chosen C.data.L).rate / 4) * GaugeSetting.coarseDist c c₁) ≤
      2 * 4 * SeparatedSequences.expSumConstant 4 C.data.L ((chosen C.data.L).rate / 4) := by
  obtain ⟨hsite, -⟩ := G.standingConstraints C.toGaugeSetting
  have hall : GaugeSetting.coarseAnchor c ∈ C.chain.shellSitesUnion :=
    mem_iUnion₂.2 ⟨c.1, mem_Iic.2 (Nat.lt_succ_iff.1 c.1.2), (hsite.1 c).2⟩
  have hα : 1 / 2 * InverseBounds.decayRateOfInverse C.data.L ≤
      (chosen C.data.L).rate / 4 := by
    have h1 := G.decayRateOfInverse_pos
    have h2 := G.decayRateOfInverse_le
    linarith
  exact (((G.floors.2 C.toGaugeSetting G.L_le_blockCount G.above.2).1 _ hα _ hall).2)
end Hypotheses
section Cubes
variable (C : CubeGaugeSetting) (Q : C.data.CubeIndex)
end Cubes
namespace Hypotheses
variable {C : CubeGaugeSetting} {m K t : ℕ} (G : Hypotheses C m K t)
include G
theorem cubeScale_pos (Q : C.data.CubeIndex) : 0 < ScaleData.cubeScale Q := by
  have h1 : 0 < C.data.levelSpacing Q.1 := by
    have hL' : (0 : ℝ) < C.data.L := by exact_mod_cast G.L_pos
    exact mul_pos (pow_pos hL' _) C.data.baseSpacing_pos
  exact mul_pos G.blockCount_pos h1
end Hypotheses
section Constants
def entryConstant (L : ℕ) : ℝ :=
  SeparatedSequences.compressedEntryConstant 4 L (chosen L).rate (chosen L).bound
end Constants
namespace Hypotheses
variable {C : CubeGaugeSetting} {m K t : ℕ} (G : Hypotheses C m K t)
include G
end Hypotheses
namespace Hypotheses
variable {C : CubeGaugeSetting} {m K t : ℕ} (G : Hypotheses C m K t)
include G
end Hypotheses
end
end YangMills.Construction.GeneralTorus.RemainderTermsProof
