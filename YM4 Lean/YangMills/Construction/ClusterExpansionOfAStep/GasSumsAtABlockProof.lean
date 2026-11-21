import YangMills.Construction.ClusterExpansionOfAStep.ClassesOfAStepAreCounted
import YangMills.Construction.ClusterExpansionOfAStep.ColumnsOfCores
import YangMills.Construction.ClusterExpansionOfAStep.GasIsAWeight
import Mathlib
import YangMills.Construction.ClusterExpansionOfAStep.SumsOverATorus
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction
open StepSettings StepGas TorusFields TorusLumps CoreColumns
namespace StepGas
def GasSumNearBlockBound : Prop :=
  ∀ (R : StepSetup) (n : ℕ) [NeZero n] (G : GasGround R n) (c κ B : ℝ) (Y : TorusSite n)
    (I₀ : Finset G.GasSpin) (t : G.GasSpin → ℝ), R.params.Admissible → 0 < c → R.params.RangeFloor c →
    R.params.y₁ ≤ R.coupling → 0 < κ → 0 ≤ B →
    (∀ i ∈ I₀, t i ≤ B * (G.spinActivity c i * (i.1.core.card : ℝ) ^ 4 *
      Real.exp (2 * R.params.rt * (i.1.coreDiam : ℝ))) * Real.exp (-(κ * (setGap {Y} i.1.core : ℝ)))) →
    ∑ i ∈ I₀, t i ≤ B * Real.exp (-(8 * c * R.coupling)) * (2 / (1 - Real.exp (-(κ / 4)))) ^ 4
end StepGas
end YangMills.Construction
end

noncomputable section
namespace YangMills.Construction
namespace StepGas
open TorusFields StepSettings TorusLumps CoreColumns
theorem core_nonempty_of_gasSpin {S : StepSetup} {N : ℕ} [NeZero N] (G : GasGround S N) (i : G.GasSpin) :
    i.1.core.Nonempty := by
  classical
  obtain ⟨z, hz⟩ := i.2.isCluster.1
  refine ⟨parentBlock S.params.side z, ?_⟩
  simp only [GasSupport.core, supportCore, coreBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨z, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · simp [sitesInBlocks]
  · exact (mem_thickening _ _ _).mpr ⟨z, hz, by rw [supDist_self]; exact Nat.zero_le _⟩
theorem exists_mem_supDist_eq_setGap {N : ℕ} [NeZero N] (x : TorusSite N) {X : Finset (TorusSite N)}
    (h : X.Nonempty) : ∃ y ∈ X, supDist x y = setGap {x} X := by
  obtain ⟨y₀, hy₀⟩ := h
  have hne : {d | ∃ y ∈ ({x} : Finset (TorusSite N)), ∃ y' ∈ X, supDist y y' = d}.Nonempty :=
    ⟨_, x, by simp, y₀, hy₀, rfl⟩
  obtain ⟨y, hy, y', hy', e⟩ := Nat.sInf_mem hne
  rw [Finset.mem_singleton] at hy
  subst hy
  exact ⟨y', hy', e⟩
theorem gasSumNearBlockBound_of_clusterSumBound (hC : ClusterSumBound) (hS : TorusSumBounds) :
    GasSumNearBlockBound := by
  intro S N _ G c κ B x I₀ t hfit hc hfl hx hκ hB ht
  classical
  set u : G.GasSpin → ℝ := fun i =>
    G.spinActivity c i * (i.1.core.card : ℝ) ^ 4 * Real.exp (2 * S.params.rt * (i.1.coreDiam : ℝ)) with hu
  have hu0 : ∀ i, 0 ≤ u i := by
    intro i
    simp only [hu, GasGround.spinActivity, clusterWeight]
    positivity
  have hblock : ∀ y : TorusSite N, ∑ i ∈ I₀.filter (fun i => y ∈ i.1.core), u i ≤
      Real.exp (-(8 * c * S.coupling)) := by
    intro y
    have h1 := hC S.params c hfit hc hfl S.coupling hx N y
    refine le_trans ?_ h1
    have h2 : ∑ i ∈ I₀.filter (fun i => y ∈ i.1.core), u i =
        ∑ θ ∈ (I₀.filter (fun i => y ∈ i.1.core)).image Subtype.val,
          clusterWeight S.params.side c S.coupling (clusterRange S.coupling) θ *
            ((supportCore S.params.side (clusterRange S.coupling) θ).card : ℝ) ^ 4 *
            Real.exp (2 * S.params.rt *
              (siteDiameter (supportCore S.params.side (clusterRange S.coupling) θ) : ℝ)) := by
      rw [Finset.sum_image (fun _ _ _ _ hh => Subtype.ext hh)]
      rfl
    rw [h2]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun θ _ _ => by
      simp only [clusterWeight]
      positivity
    intro θ hθ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hθ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2.isCluster, (Finset.mem_filter.mp hi).2⟩
  have hpt : ∀ i ∈ I₀, t i ≤ ∑ y : TorusSite N,
      B * (if y ∈ i.1.core then u i else 0) * Real.exp (-(κ * (supDist y x : ℝ))) := by
    intro i hi
    obtain ⟨y, hy, e⟩ := exists_mem_supDist_eq_setGap x (core_nonempty_of_gasSpin G i)
    have h1 := ht i hi
    rw [← e, supDist_comm] at h1
    refine h1.trans ?_
    have := Finset.single_le_sum (f := fun y' : TorusSite N =>
      B * (if y' ∈ i.1.core then u i else 0) * Real.exp (-(κ * (supDist y' x : ℝ))))
      (fun y' _ => by
        have : 0 ≤ (if y' ∈ i.1.core then u i else 0) := by
          split_ifs
          · exact hu0 i
          · exact le_rfl
        positivity) (Finset.mem_univ y)
    simp only [if_pos hy] at this
    exact this
  calc ∑ i ∈ I₀, t i ≤ ∑ i ∈ I₀, ∑ y : TorusSite N,
        B * (if y ∈ i.1.core then u i else 0) * Real.exp (-(κ * (supDist y x : ℝ))) :=
        Finset.sum_le_sum hpt
    _ = ∑ y : TorusSite N, B * (∑ i ∈ I₀.filter (fun i => y ∈ i.1.core), u i) *
          Real.exp (-(κ * (supDist y x : ℝ))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_filter, Finset.mul_sum, Finset.sum_mul]
    _ ≤ ∑ y : TorusSite N, B * Real.exp (-(8 * c * S.coupling)) * Real.exp (-(κ * (supDist y x : ℝ))) := by
        refine Finset.sum_le_sum fun y _ => ?_
        have := hblock y
        have h2 : 0 ≤ Real.exp (-(κ * (supDist y x : ℝ))) := (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hB) h2
    _ = B * Real.exp (-(8 * c * S.coupling)) * ∑ y : TorusSite N, Real.exp (-(κ * (supDist y x : ℝ))) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left ((hS N x).1 κ hκ) (by positivity)
end StepGas
end YangMills.Construction
end
