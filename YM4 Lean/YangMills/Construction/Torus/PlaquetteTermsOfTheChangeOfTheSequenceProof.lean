import YangMills.Construction.Torus.BoundsOfTheColumnsOnASetting
import YangMills.Construction.Torus.BoundsOnTheExtensionOperatorProof
import YangMills.Construction.Torus.CompressionOfTheCutOperatorToACubeProof
import YangMills.Construction.Torus.CubeSetsBumpsCutOffsAndProductRule
import YangMills.Construction.Torus.ExponentialSumsOverSitesAndExpansionsProof
import YangMills.Construction.Torus.TermsOfTheChangeOfTheSequence
import YangMills.Construction.Torus.QuadraticFormsAndMatricesOfTheAveragesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace GeneralTorus
namespace ChainChangeCurl
section TorusNorm
variable {S : ℝ}
theorem torusSupNorm_le_of_forall {x : Torus4 S} {r : ℝ} (h : ∀ μ, ‖x μ‖ ≤ r) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm x ≤ r := by apply _root_.YangMills.Construction.SequenceGeometryProof.torusSupNorm_le_of_forall <;> assumption
theorem torusSupNorm_add_le (x y : Torus4 S) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm (x + y) ≤ _root_.YangMills.Construction.TorusMetric.torusSupNorm x + _root_.YangMills.Construction.TorusMetric.torusSupNorm y := by apply _root_.YangMills.Construction.SequenceGeometryProof.torusSupNorm_add_le <;> assumption
theorem torusSupNorm_sub_le (a b c : Torus4 S) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm (a - c) ≤ _root_.YangMills.Construction.TorusMetric.torusSupNorm (a - b) + _root_.YangMills.Construction.TorusMetric.torusSupNorm (b - c) := by
  have h : a - c = (a - b) + (b - c) := by abel
  rw [h]
  exact torusSupNorm_add_le _ _
theorem torusSupNorm_sub_comm (a b : Torus4 S) : _root_.YangMills.Construction.TorusMetric.torusSupNorm (a - b) = _root_.YangMills.Construction.TorusMetric.torusSupNorm (b - a) := by apply _root_.YangMills.Construction.Weighted.LayerCutoff.torusSupNorm_sub_comm <;> assumption
theorem torusSupNorm_zero_le {r : ℝ} (hr : 0 ≤ r) : _root_.YangMills.Construction.TorusMetric.torusSupNorm (0 : Torus4 S) ≤ r := by apply _root_.YangMills.Construction.GeneralTorus.CubeGreenCompressionProof.torusSupNorm_zero_le <;> assumption
theorem torusSupNorm_unitStep_le {σ : ℝ} (hσ : 0 ≤ σ) (μ : Fin 4) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm ((unitStep S σ μ : LatticeSite S σ) : Torus4 S) ≤ σ := by
  refine torusSupNorm_le_of_forall fun ν => ?_
  show ‖(((Pi.single μ σ : Fin 4 → ℝ) ν : ℝ) : AddCircle S)‖ ≤ σ
  refine (addCircle_norm_coe_le_abs _).trans ?_
  by_cases h : ν = μ
  · subst h
    simp [abs_of_nonneg hσ]
  · simp [Pi.single_eq_of_ne h, hσ]
end TorusNorm
section LevelSpacings
variable (D : ScaleData)
theorem thirteen_le_L_real : (13 : ℝ) ≤ D.L := by
  exact_mod_cast D.blocking.thirteen_le
theorem levelSpacing_pos (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem levelSpacing_mono {m n : ℕ} (h : m ≤ n) : D.levelSpacing m ≤ D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.SupDistBound.levelSpacing_mono <;> assumption
theorem levelSpacing_succ (n : ℕ) : D.levelSpacing (n + 1) = (D.L : ℝ) * D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ClosedMeanFree.levelSpacing_succ <;> assumption
theorem admitsPartition_levelSpacing {n : ℕ} (hn : n ≤ D.lastLevel) :
    D.AdmitsPartition (D.levelSpacing n) := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.admitsPartition_levelSpacing_of_le_lastLevel <;> assumption
end LevelSpacings
section PlaquetteBonds
variable {D : ScaleData}
instance instFiniteBasePlaquette : Finite D.BasePlaquette := by
  refine Finite.of_injective (fun p : D.BasePlaquette => (p.basePoint, p.dir₁, p.dir₂)) ?_
  intro p q h
  simp only [Prod.mk.injEq] at h
  exact LatticePlaquette.ext h.1 h.2.1 h.2.2
end PlaquetteBonds
section Chain
variable {D : ScaleData} (B : SeparatedChain D)
theorem set_antitone {a b : ℕ} (hab : a ≤ b) (hb : b ≤ D.lastLevel) : B.set b ⊆ B.set a := by apply _root_.YangMills.Construction.GeneralTorus.CoarseTestFormMeansAux.set_antitone <;> assumption
theorem shellSitesUnion_finite : B.shellSitesUnion.Finite := by apply _root_.YangMills.Construction.GeneralTorus.ScaledDistExpSums.shellSitesUnion_finite <;> assumption
theorem anchor_eq (b : D.BaseBond) : B.anchor b = b.1.src ∨ B.anchor b = b.1.tgt := by
  unfold SeparatedChain.anchor
  split_ifs <;> simp
end Chain
theorem anchor_mem (W : GaugeSetting) {b : W.data.BaseBond} (hb : b ∈ W.bondSet) :
    (W.chain.anchor b : W.data.Space) ∈ W.chain.set 0 := by
  unfold SeparatedChain.anchor
  split_ifs with h
  · exact h
  · unfold GaugeSetting.bondSet at hb
    cases hc : W.choice <;> simp only [hc] at hb
    · exact hb.resolve_left h
    · exact absurd hb.1 h
section NearCube
variable {C : CubeGaugeSetting} {Q : C.data.CubeIndex}
theorem cubeScale_ge (C : CubeGaugeSetting) (Q : C.data.CubeIndex) :
    12 * (C.data.L : ℝ) * C.data.levelSpacing Q.1 ≤ ScaleData.cubeScale Q := by
  have h : 12 * (C.data.L : ℝ) ≤ C.data.blockCount := by
    exact_mod_cast C.twelve_mul_L_le_blockCount
  show _ ≤ (C.data.blockCount : ℝ) * C.data.levelSpacing Q.1
  exact mul_le_mul_of_nonneg_right h (levelSpacing_pos _ _).le
theorem base_le_cubeScale (C : CubeGaugeSetting) (Q : C.data.CubeIndex) :
    156 * C.data.levelSpacing 0 ≤ ScaleData.cubeScale Q := by
  have h1 := cubeScale_ge C Q
  have h2 := thirteen_le_L_real C.data
  have h3 := levelSpacing_mono C.data (Nat.zero_le Q.1)
  have h4 := levelSpacing_pos C.data Q.1
  nlinarith
theorem cubeScale_pos (C : CubeGaugeSetting) (Q : C.data.CubeIndex) : 0 < ScaleData.cubeScale Q := by
  have := levelSpacing_pos C.data 0
  linarith [base_le_cubeScale C Q]
end NearCube
theorem abs_sub_mul_le {d₁ d₂ a₁ a₂ R X : ℝ} (h₁ : |d₁| ≤ R) (h₂ : |d₂| ≤ R) (h₃ : |a₁| ≤ X)
    (h₄ : |a₂| ≤ X) : |d₁ * a₁ - d₂ * a₂| ≤ 2 * R * X := by
  have hR : 0 ≤ R := (abs_nonneg _).trans h₁
  have e₁ : |d₁ * a₁| ≤ R * X := by
    rw [abs_mul]
    exact mul_le_mul h₁ h₃ (abs_nonneg _) hR
  have e₂ : |d₂ * a₂| ≤ R * X := by
    rw [abs_mul]
    exact mul_le_mul h₂ h₄ (abs_nonneg _) hR
  have h := norm_sub_le (d₁ * a₁) (d₂ * a₂)
  simp only [Real.norm_eq_abs] at h
  linarith
section PlaquetteSum
variable {C : CubeGaugeSetting} {Q : C.data.CubeIndex}
end PlaquetteSum
end ChainChangeCurl
end GeneralTorus
end YangMills.Construction
