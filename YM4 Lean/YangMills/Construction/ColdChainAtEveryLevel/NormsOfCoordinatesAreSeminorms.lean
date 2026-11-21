import YangMills.Construction.ColdChainAtEveryLevel.SeminormsOfCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.ChartNorms
variable {F : BlockFrame}
theorem linearizedCurl_add_smul (R : F.GaugeField 0) (u v : F.Site 0 → Fin 4 → imaginaryQuaternions) (t : ℝ)
    (p : F.Site 0 × Fin 4 × Fin 4) :
    linearizedCurl R (fun x i => u x i + t • v x i) p = linearizedCurl R u p + t • linearizedCurl R v p := by apply _root_.YangMills.Construction.CoordinateSeminorms.linearizedCurl_add_smul <;> assumption
theorem localNormSq_nonneg (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) :
    0 ≤ localNormSq S B R U w := by apply _root_.YangMills.Construction.CoordinateSeminorms.localNormSq_nonneg <;> assumption
theorem localNorm_chartMove_le (S : Finset F.Cell) (R : F.FieldChain) (U A : ChainChart F) (t : ℝ)
    (w : F.SiteWeights) (hw : ∀ j x, 0 ≤ w j x) (z : F.Cell) :
    localNorm S R (chartMove U A t) w z ≤ localNorm S R U w z + |t| * localNorm S R A w z := by apply _root_.YangMills.Construction.CoordinateSeminorms.localNorm_chartMove_le <;> assumption
theorem weightedNorm_nonneg (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) :
    0 ≤ weightedNorm S R U w := Real.sqrt_nonneg _
theorem weightedNorm_sq (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) :
    weightedNorm S R U w ^ 2 = ∑ z ∈ S, localNormSq S (cellBall S z 3) R U w := by apply _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_sq <;> assumption
instance instNonemptyCell : Nonempty F.Cell := ⟨0⟩
theorem supWeightedNorm_nonneg (S : Finset F.Cell) (del : ℝ) (R : F.FieldChain) (U : ChainChart F) :
    0 ≤ supWeightedNorm S del R U :=
  Real.iSup_nonneg fun _ => weightedNorm_nonneg _ _ _ _
theorem supWeightedNorm_le (S : Finset F.Cell) (del : ℝ) (R : F.FieldChain) (U : ChainChart F) (β : ℝ)
    (h : ∀ y0, weightedNorm S R U (decayWeights F del 0 0 y0) ≤ β) : supWeightedNorm S del R U ≤ β :=
  ciSup_le h
theorem supWeightedNorm_chartMove_le (S : Finset F.Cell) (hL : 0 < F.blockSide) (del : ℝ) (hdel : 0 ≤ del)
    (R : F.FieldChain) (U A : ChainChart F) (t : ℝ) :
    supWeightedNorm S del R (chartMove U A t) ≤ supWeightedNorm S del R U + |t| * supWeightedNorm S del R A := by apply _root_.YangMills.Construction.CoordinateSeminorms.supWeightedNorm_chartMove_le <;> assumption
theorem localNorm_nonneg (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights)
    (z : F.Cell) : 0 ≤ localNorm S R U w z := Real.sqrt_nonneg _
theorem localNorm_constOne_le_supWeightedNorm (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    {del : ℝ} (hdel : 0 < del) {z : F.Cell} (hz : z ∈ S) :
    localNorm S R U (constOneWeights F) z ≤ Real.exp (3 * del) * supWeightedNorm S del R U := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.localNorm_le_supWeightedNorm <;> assumption
end YangMills.Construction.BlockAverages.ChartNorms
end
