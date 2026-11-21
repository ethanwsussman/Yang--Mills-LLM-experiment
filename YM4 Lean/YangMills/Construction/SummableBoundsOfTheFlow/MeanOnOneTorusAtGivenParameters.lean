import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionHasTheConditionsOfThirdOrder
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfTheMeanAtATop
import YangMills.Construction.SummableBoundsOfTheFlow.LawAtATopFromTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOnOneTorus
import YangMills.Construction.SummableBoundsOfTheFlow.TransportScalesWithTheFamily
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.BlockMeans
def singleTorusMeanConstant (Cs E η₃ B W Cg Cm Cth N₀ : ℝ) : ℝ :=
  N₀ * Cg * W * (1 + Cm) / (2 * η₃) + 2 * Cs ^ 2 * Cth * (E / η₃) + 7 * B * (Cs / η₃) * (Cs * (1 + E / η₃)) +
    7 * B * (Cs / η₃) * (Cs * (1 + E / η₃)) ^ 2 + B * (Cs / η₃) * (Cs * (1 + E / η₃)) ^ 3
structure SingleTorusMeanHypotheses (T : ColdStepAtMirrorFrames.StepParameters) (Cq Cz : ℕ → ℝ)
    (Cr : ℕ → ℕ → ℕ → ℝ) (C : ℝ) (Ck Cth : ℕ → ℝ) (B W : ℝ) : Prop
    extends LawAtTop.LawAtTopHypotheses T Cq Cz Cr C Ck where
  C_pos : 0 < C
  B_nonneg : 0 ≤ B
  W_nonneg : 0 ≤ W
  Cth_nonneg : ∀ q, 0 ≤ Cth q
  familyTransport : ∀ ε : ℝ, 0 < ε → Interpolation.TransportAtScale T ε
  thirdOrder : Interpolation.thirdOrderCovarianceBoundAt T Cth
  blockExpansion : Interpolation.blockExpansionThirdOrderAt T Cth
  cumulants : ∀ (F : BlockAverages.BlockFrame) (star : Bool) (x : ℝ) (m : ℕ) (α β : ℝ)
    (φ h : ColdStepAtMirrorFrames.LocalFamily) (V : F.GaugeField F.top),
    LawAtTop.LawAtTop star T.a T.chainParams.ρA x m (T.σ / 64) T.chainParams.lam T.κ α β T.p
      (fun q => |Cz q|) (4 * T.L ^ 4) (1 + (BlockAverages.centredCube T.L).card) φ h V → ∀ Y : F.Cell,
    Cumulants.MeanCumulantBounds star T.a T.chainParams.ρA x m (T.σ / 64) T.κ T.p φ h V Y (B * (α * β))
      (B * (α * β ^ 2)) (B * (α * β ^ 3))
  weight_sum_le : ∀ (t : ℕ) (F : BlockAverages.BlockFrame), ColdStepAtMirrorFrames.IsCubicTopTorus T.L t T.n₀ F →
    ∀ Y : F.Cell, ∑ b : ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells F)),
      Real.exp (-(2 ^ 6 * T.κ * (BlockAverages.cellSupDist (BlockAverages.enclosingCell b.1.1) Y : ℝ))) ≤ W
def singleTorusMeanAtSlotsStatement : Prop :=
  ∀ (T : ColdStepAtMirrorFrames.StepParameters) (Cq Cz : ℕ → ℝ) (Cr : ℕ → ℕ → ℕ → ℝ) (C : ℝ)
    (Ck Cth : ℕ → ℝ) (B W CE : ℝ),
    SingleTorusMeanHypotheses T Cq Cz Cr C Ck Cth B W →
    singleTorusMeanConstant T.Cs T.E T.η₃ B W C |Cq 1| (1 + ∑ q ∈ Finset.range 7, Cth q)
      ((BlockAverages.centredCube T.L).card : ℝ) ≤ CE →
    ∀ (t : ℕ) (x : ℝ) (φ h : ColdStepAtMirrorFrames.LocalFamily) (ε : ℝ) (star : Bool), T.coupling ≤ x → 0 < ε →
      FamilyNorms.IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E (T.E / T.η₃) φ →
      ColdStepAtMirrorFrames.IsRegularFamily T.L t T.n₀ T.σ T.decayRate ε (ε / T.η₃) h →
      SingleTorusMeanBounds star T.a T.chainParams.ρA T.σ x T.κ T.decayRate ε (ε / T.η₃) CE T.L t T.n₀
        (ColdStepAtMirrorFrames.frameRadius x) T.p φ h
end YangMills.Construction.BlockMeans
end
