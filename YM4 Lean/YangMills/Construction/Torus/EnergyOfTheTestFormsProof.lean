import YangMills.Construction.SeparatedSequences.ExplicitConstants
import YangMills.Construction.Torus.ProfilesAndTestForms
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.Torus.LayersCellsBlocksAndTheDistanceProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric
namespace GeneralTorus.TestFormEnergy
def profileProduct (N : ℕ) (β : ℝ) (μ : Fin 4) (k : Fin 4 → ℤ) : ℝ :=
  tiltedParabolicProfile β N (k μ) * ∏ ν ∈ Finset.univ.erase μ, parabolicProfile N (k ν)
def shiftedSite (D : ScaleData) (y : D.Space) (k : Fin 4 → ℤ) : D.Space :=
  y + torusProj D.torusSide fun ν => D.levelSpacing 0 * (k ν : ℝ)
theorem levelSpacing_zero_pos (D : ScaleData) : 0 < D.levelSpacing 0 := by
  simpa [ScaleData.levelSpacing] using D.baseSpacing_pos
theorem L_pos (D : ScaleData) : 0 < D.L := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.L_pos <;> assumption
theorem exists_torusSide_eq_mul (D : ScaleData) {n : ℕ} (hn : n ≤ D.lastLevel) :
    ∃ M : ℤ, 2 * (D.blockSize n : ℤ) ≤ M ∧ D.torusSide = (M : ℝ) * D.levelSpacing 0 := by
  obtain ⟨k, hk, hS⟩ := D.torusSide_evenMultiple
  refine ⟨2 * k * (D.L : ℤ) ^ D.lastLevel, ?_, ?_⟩
  · have h1 : D.blockSize n ≤ D.L ^ D.lastLevel :=
      Nat.pow_le_pow_right (L_pos D) hn
    have h2 : D.L ^ D.lastLevel ≤ k * D.L ^ D.lastLevel := Nat.le_mul_of_pos_left _ hk
    have h3 : 2 * D.blockSize n ≤ 2 * k * D.L ^ D.lastLevel := by
      calc 2 * D.blockSize n ≤ 2 * (k * D.L ^ D.lastLevel) := by omega
        _ = 2 * k * D.L ^ D.lastLevel := by ring
    exact_mod_cast h3
  · rw [hS]
    simp only [ScaleData.levelSpacing]
    push_cast
    ring
theorem torusProj_add (S : ℝ) (a b : Fin 4 → ℝ) :
    torusProj S (a + b) = torusProj S a + torusProj S b := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_add <;> assumption
theorem unitStep_injective (D : ScaleData) {M : ℤ} (hM : 2 ≤ M)
    (hS : D.torusSide = (M : ℝ) * D.levelSpacing 0) {μ ν : Fin 4}
    (h : unitStep D.torusSide (D.levelSpacing 0) μ = unitStep D.torusSide (D.levelSpacing 0) ν) :
    μ = ν := by
  by_contra hne
  have hξ := levelSpacing_zero_pos D
  have h1 : coordPoint D.torusSide μ (D.levelSpacing 0) = coordPoint D.torusSide ν (D.levelSpacing 0) :=
    congrArg Subtype.val h
  have h2 : ((D.levelSpacing 0 : ℝ) : AddCircle D.torusSide) = 0 := by
    have := congrFun h1 μ
    simpa [coordPoint, torusProj, Pi.single_eq_of_ne hne] using this
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff D.torusSide).1 h2
  rw [zsmul_eq_mul, hS] at hm
  have hr : (m : ℝ) * (M : ℝ) = 1 := by
    apply mul_left_cancel₀ hξ.ne'
    linarith
  have hi : m * M = 1 := by exact_mod_cast hr
  have := Int.eq_one_or_neg_one_of_mul_eq_one' hi
  omega
theorem posBondDir_bondFrom (D : ScaleData) {M : ℤ} (hM : 2 ≤ M)
    (hS : D.torusSide = (M : ℝ) * D.levelSpacing 0) (x : D.BaseSite) (μ : Fin 4) :
    ScaleData.posBondDir (ScaleData.bondFrom x μ) = μ := by
  have hc : (ScaleData.bondFrom x μ).1.tgt - (ScaleData.bondFrom x μ).1.src =
      unitStep D.torusSide (D.levelSpacing 0) (ScaleData.posBondDir (ScaleData.bondFrom x μ)) :=
    (ScaleData.bondFrom x μ).2.choose_spec
  apply unitStep_injective D hM hS
  rw [← hc]
  simp [ScaleData.bondFrom, LatticeBond.plus]
end GeneralTorus.TestFormEnergy
end YangMills.Construction
