import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.RunningCouplingSlope.CompositionKeepsTheCoefficientProof
import YangMills.Construction.RunningCouplingSlope.SumsOverToriTendToSumsOverTheLattice
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages TorusLumps TorusFields SlopeCoefficient
namespace TorusSumLimit
private theorem natAbs_le_offsetNorm (z : Fin 4 → ℤ) (i : Fin 4) : (z i).natAbs ≤ offsetNorm z := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
private theorem summable_exp_neg_offsetNormReal {θ : ℝ} (hθ : 0 < θ) :
    Summable fun z : Fin 4 → ℤ => Real.exp (-(θ * offsetNormReal z)) := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.summable_exp_neg_offsetNormReal <;> assumption
private theorem summable_exp_neg_offsetNormReal_bond {θ : ℝ} (hθ : 0 < θ) :
    Summable fun b : LatticeBond => Real.exp (-(θ * offsetNormReal b.1)) := by
  have h := Summable.mul_of_nonneg (summable_exp_neg_offsetNormReal hθ)
    (hasSum_fintype (fun _ : Fin 4 => (1 : ℝ))).summable (fun _ => (Real.exp_pos _).le) (fun _ => zero_le_one)
  exact h.congr fun b => by simp
private def minimalLift (N : ℕ) (b : TorusBond N) : LatticeBond := (fun i => (b.1 i).valMinAbs, b.2)
private theorem bondFrom_minimalLift (N : ℕ) (b : TorusBond N) : bondFrom 0 (minimalLift N b) = b := by
  refine Prod.ext ?_ rfl
  funext i
  simp [bondFrom, minimalLift, siteOfInt]
private theorem minimalLift_injective (N : ℕ) : Function.Injective (minimalLift N) := fun b b' h => by
  rw [← bondFrom_minimalLift N b, ← bondFrom_minimalLift N b', h]
private theorem supDist_eq_offsetNormReal (N : ℕ) (b : TorusBond N) :
    (supDist b.1 0 : ℝ) = offsetNormReal (minimalLift N b).1 := by
  simp [supDist, offsetNormReal, offsetNorm, minimalLift]
private theorem minimalLift_bondFrom {N : ℕ} [NeZero N] {c : LatticeBond} (h : 2 * offsetNorm c.1 < N) :
    minimalLift N (bondFrom 0 c) = c := by
  refine Prod.ext ?_ rfl
  funext i
  have h1 := natAbs_le_offsetNorm c.1 i
  have h2 : ((c.1 i : ℤ) : ZMod N).valMinAbs = c.1 i := by
    rw [ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_, ?_⟩ <;> omega
  simpa [bondFrom, minimalLift, siteOfInt] using h2
end TorusSumLimit
open TorusSumLimit in
theorem tendstoLatticeSumOfTorusSums : TendstoLatticeSumOfTorusSums := by
  intro s M θ f g F hs hθ hf hg hF
  have hM : 0 ≤ M := by
    obtain ⟨n, hn⟩ := hf.exists
    exact nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hn (0, 0))) (Real.exp_pos _)
  have hsum : Summable fun c : LatticeBond => M * Real.exp (-(θ * offsetNormReal c.1)) :=
    (summable_exp_neg_offsetNormReal_bond hθ).mul_left M
  let E : ℕ → LatticeBond → ℝ := fun n => Function.extend (minimalLift (s n)) (f n) 0
  have hEb : ∀ n b, E n (minimalLift (s n) b) = f n b := fun n b =>
    (minimalLift_injective (s n)).extend_apply (f n) 0 b
  have hE : ∀ᶠ n in Filter.atTop, ∀ c, ‖E n c‖ ≤ M * Real.exp (-(θ * offsetNormReal c.1)) := by
    filter_upwards [hf] with n hn c
    by_cases h : ∃ b, minimalLift (s n) b = c
    · obtain ⟨b, rfl⟩ := h
      rw [hEb, Real.norm_eq_abs, ← supDist_eq_offsetNormReal]
      exact hn b
    · have h0 : E n c = 0 := Function.extend_apply' _ _ _ h
      rw [h0, norm_zero]
      positivity
  have hlim : ∀ c, Filter.Tendsto (fun n => E n c) Filter.atTop (𝓝 (g c)) := by
    intro c
    refine (hg c).congr' ?_
    filter_upwards [hs.eventually (Filter.eventually_gt_atTop (2 * offsetNorm c.1))] with n hn
    have : NeZero (s n) := ⟨by omega⟩
    have h := hEb n (bondFrom 0 c)
    rw [minimalLift_bondFrom hn] at h
    exact h.symm
  have hgb : ∀ c, ‖g c‖ ≤ M * Real.exp (-(θ * offsetNormReal c.1)) := fun c =>
    le_of_tendsto (hlim c).norm (hE.mono fun n h => h c)
  refine ⟨Summable.of_norm_bounded hsum hgb, ?_⟩
  refine (tendsto_tsum_of_dominated_convergence hsum hlim hE).congr' ?_
  filter_upwards [hF, hs.eventually (Filter.eventually_gt_atTop 0)] with n hn hpos
  have : NeZero (s n) := ⟨by omega⟩
  have hsupp : Function.support (E n) ⊆ Set.range (minimalLift (s n)) := by
    intro c hc
    by_contra h
    exact hc (Function.extend_apply' _ _ _ h)
  rw [hn, ← (minimalLift_injective (s n)).tsum_eq hsupp, tsum_fintype]
  exact Finset.sum_congr rfl fun b _ => hEb n b
end YangMills.Construction.RunningCouplingSlope
end
