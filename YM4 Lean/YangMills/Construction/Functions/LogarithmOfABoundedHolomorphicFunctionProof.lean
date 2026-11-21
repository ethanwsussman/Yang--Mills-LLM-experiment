import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionsOfSeveralVariables
import YangMills.Construction.Functions.CauchyInequalityForTheMixedDerivativeAlongCoordinates
import YangMills.Construction.Functions.LogarithmOfABoundedHolomorphicFunction
import YangMills.Construction.Lattice.SublevelSetsAndSourceDiscs
import Mathlib
set_option autoImplicit false
open Set Metric Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.LogBounds
open WeightedModulusSum TorusBoundNotation
variable {n : ℕ}
theorem norm_iteratedDeriv_zero_le_factorial_mul {f : ℂ → ℂ} {M : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hM : ∀ w ∈ ball (0 : ℂ) 1, ‖f w‖ ≤ M) (k : ℕ) :
    ‖iteratedDeriv k f 0‖ ≤ k.factorial * M := by
  have hr : ∀ r ∈ Ioo (0 : ℝ) 1, ‖iteratedDeriv k f 0‖ ≤ k.factorial * M / r ^ k := by
    intro r hr
    have hsub : closedBall (0 : ℂ) r ⊆ ball 0 1 := closedBall_subset_ball hr.2
    refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr.1
      (hf.diffContOnCl_ball hsub) fun w hw => hM w (hsub (sphere_subset_closedBall hw))
  have hc : ContinuousAt (fun r : ℝ => (k.factorial : ℝ) * M / r ^ k) 1 :=
    ContinuousAt.div continuousAt_const (continuousAt_id.pow k) (by simp)
  have hlim : Tendsto (fun r : ℝ => (k.factorial : ℝ) * M / r ^ k) (𝓝[Ioo (0 : ℝ) 1] 1)
      (𝓝 ((k.factorial : ℝ) * M / (1 : ℝ) ^ k)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have : (𝓝[Ioo (0 : ℝ) 1] (1 : ℝ)).NeBot := right_nhdsWithin_Ioo_neBot one_pos
  have := ge_of_tendsto hlim (eventually_mem_nhdsWithin.mono hr)
  simpa using this
theorem norm_sub_one_le_geometric {f : ℂ → ℂ} {M x : ℝ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hf0 : f 0 = 1) (hM : ∀ w ∈ ball (0 : ℂ) 1, ‖f w‖ ≤ M) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ‖f (x : ℂ) - 1‖ ≤ M * x * (1 - x)⁻¹ := by
  have hmem : (x : ℂ) ∈ ball (0 : ℂ) ((1 : NNReal) : ℝ) := by
    simpa [abs_of_nonneg hx0] using hx1
  have hs := Complex.hasSum_taylorSeries_on_ball (c := 0) (r := 1) (z := (x : ℂ)) (f := f)
    (by simpa using hf) hmem
  have hs1 := (hasSum_nat_add_iff' 1).mpr hs
  have hg : HasSum (fun k : ℕ => M * x * x ^ k) (M * x * (1 - x)⁻¹) :=
    (hasSum_geometric_of_lt_one hx0 hx1).mul_left _
  have hb := hs1.norm_le_of_bounded hg fun k => ?_
  · simpa [hf0] using hb
  · have hD := norm_iteratedDeriv_zero_le_factorial_mul hf hM (k + 1)
    have hn : ‖((((k + 1).factorial : ℕ) : ℂ))⁻¹ • ((x : ℂ) - 0) ^ (k + 1) •
        iteratedDeriv (k + 1) f 0‖ =
        (((k + 1).factorial : ℝ))⁻¹ * (x ^ (k + 1) * ‖iteratedDeriv (k + 1) f 0‖) := by
      simp [abs_of_nonneg hx0]
    rw [hn]
    calc (((k + 1).factorial : ℝ))⁻¹ * (x ^ (k + 1) * ‖iteratedDeriv (k + 1) f 0‖)
        ≤ (((k + 1).factorial : ℝ))⁻¹ * (x ^ (k + 1) * (((k + 1).factorial : ℝ) * M)) := by
          gcongr
      _ = M * x * x ^ k := by
          field_simp
          ring
theorem norm_sub_one_le_linear {f : ℂ → ℂ} {M x : ℝ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hf0 : f 0 = 1) (hM : ∀ w ∈ ball (0 : ℂ) 1, ‖f w‖ ≤ M) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ‖f (x : ℂ) - 1‖ ≤ (M + 1) * x := by
  have hmaps : MapsTo f (ball 0 1) (closedBall (f 0) (M + 1)) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm, hf0]
    calc ‖f w - 1‖ ≤ ‖f w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ M + 1 := by simpa using hM w hw
  have hmem : (x : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa [abs_of_nonneg hx0] using hx1
  have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hf hmaps hmem
  simpa [dist_eq_norm, hf0, abs_of_nonneg hx0] using this
theorem weightedNorm_smul (a : Weights n) (c : ℂ) (z : Coordinates.ComplexCoordinates n) :
    a.weightedNorm (c • z) = ‖c‖ * a.weightedNorm z := by
  simp only [Weights.weightedNorm, Pi.smul_apply, smul_eq_mul, norm_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring
theorem weightedNorm_nonneg (a : Weights n) (z : Coordinates.ComplexCoordinates n) :
    0 ≤ a.weightedNorm z :=
  Finset.sum_nonneg fun i _ => mul_nonneg (a.c_pos i).le (norm_nonneg _)
theorem weightedNorm_zero (a : Weights n) : a.weightedNorm 0 = 0 := by
  simp [Weights.weightedNorm]
theorem weightedNorm_pos (a : Weights n) {z : Coordinates.ComplexCoordinates n} (hz : z ≠ 0) :
    0 < a.weightedNorm z := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
  exact Finset.sum_pos' (fun j _ => mul_nonneg (a.c_pos j).le (norm_nonneg _))
    ⟨i, Finset.mem_univ i, mul_pos (a.c_pos i) (norm_pos_iff.mpr hi)⟩
theorem norm_sub_one_bounds_of_mem_unitSet (hCalc : SeveralComplexVariables.HolomorphicCalculusRules)
    (a : Weights n) {g : Coordinates.ComplexCoordinates n → ℂ} {M : ℝ}
    (hg : ComplexVariables.IsHolomorphicScalar a.unitSet g) (hg0 : g 0 = 1)
    (hM : ∀ z ∈ a.unitSet, ‖g z‖ ≤ M) {z : Coordinates.ComplexCoordinates n} (hz : z ∈ a.unitSet) :
    ‖g z - 1‖ ≤ (M + 1) * a.weightedNorm z ∧
      ‖g z - 1‖ ≤ M * a.weightedNorm z * (1 - a.weightedNorm z)⁻¹ := by
  by_cases hz0 : z = 0
  · subst hz0
    simp [hg0, weightedNorm_zero]
  have hx0 : 0 < a.weightedNorm z := weightedNorm_pos a hz0
  have hx1 : a.weightedNorm z < 1 := hz
  set x : ℝ := a.weightedNorm z with hxdef
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hU : IsOpen a.unitSet := hg.1
  obtain ⟨-, -, -, -, hAff, -⟩ := hCalc n a.one_le a.unitSet hU g g hg hg
  let v : Fin 1 → Coordinates.ComplexCoordinates n := fun _ => (x : ℂ)⁻¹ • z
  obtain ⟨hO, hF⟩ := hAff 1 le_rfl 0 v
  have hdiff := (isHolomorphicScalar_fin_one_iff hO _).mp hF
  let f : ℂ → ℂ := fun w => (g ∘ SeveralComplexVariables.affineParam 0 v) fun _ => w
  have hfv : ∀ w : ℂ, f w = g (w • (x : ℂ)⁻¹ • z) := fun w => by
    simp [f, v, SeveralComplexVariables.affineParam]
  have hin : ∀ w ∈ ball (0 : ℂ) 1, w • (x : ℂ)⁻¹ • z ∈ a.unitSet := by
    intro w hw
    have hw1 : ‖w‖ < 1 := by simpa using hw
    change a.weightedNorm _ < 1
    rw [weightedNorm_smul, weightedNorm_smul, ← hxdef, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hx0, inv_mul_cancel₀ hx0.ne', mul_one]
    exact hw1
  have hfd : DifferentiableOn ℂ f (ball 0 1) := by
    intro w hw
    have hpre : (fun _ : Fin 1 => w) ∈
        SeveralComplexVariables.affineParam 0 v ⁻¹' a.unitSet := by
      have hv : SeveralComplexVariables.affineParam 0 v (fun _ => w) =
          w • (x : ℂ)⁻¹ • z := by
        simp [v, SeveralComplexVariables.affineParam]
      rw [mem_preimage, hv]
      exact hin w hw
    exact (hdiff _ hpre).differentiableWithinAt
  have hf0 : f 0 = 1 := by
    rw [hfv]
    simpa using hg0
  have hfM : ∀ w ∈ ball (0 : ℂ) 1, ‖f w‖ ≤ M := fun w hw => by
    rw [hfv]
    exact hM _ (hin w hw)
  have hfx : f (x : ℂ) = g z := by
    rw [hfv, smul_smul, mul_inv_cancel₀ hxC, one_smul]
  have h1 := norm_sub_one_le_linear hfd hf0 hfM hx0.le hx1
  have h2 := norm_sub_one_le_geometric hfd hf0 hfM hx0.le hx1
  rw [hfx] at h1 h2
  exact ⟨h1, h2⟩
theorem boundedLogEstimate_holds (hDisk : SublevelSets.SublevelAndDiskStatement)
    (hCauchy : CauchyEstimates.MixedDerivCauchyBound)
    (hCalc : SeveralComplexVariables.HolomorphicCalculusRules) : BoundedLogEstimate := by
  intro n a g M hg hg0 hM
  have hU : IsOpen a.unitSet := hg.1
  have h00 : (0 : Coordinates.ComplexCoordinates n) ∈ a.unitSet := by
    change a.weightedNorm 0 < 1
    rw [weightedNorm_zero]
    exact one_pos
  have hM1 : 1 ≤ M := by
    have := hM 0 h00
    rwa [hg0, norm_one] at this
  have hM0 : 0 < M := by linarith
  have hMp : 0 < M + 1 := by linarith
  have hAB : ∀ z ∈ a.unitSet, _ := fun z hz => norm_sub_one_bounds_of_mem_unitSet hCalc a hg hg0 hM hz
  obtain ⟨-, hRes, -, -, -, -, -, -, -, hlogD, hlogE, hlog1, hlog2⟩ :=
    hCalc n a.one_le a.unitSet hU g g hg hg
  have hr : 0 < (M + 1)⁻¹ := inv_pos.mpr hMp
  have hS : IsOpen (sublevelSet a M) := (hDisk.1 n a _ hr).1
  have hr1 : (M + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hSU : sublevelSet a M ⊆ a.unitSet := fun z hz => lt_of_lt_of_le hz hr1
  have hgS : ComplexVariables.IsHolomorphicScalar (sublevelSet a M) g := hRes _ hS hSU
  obtain ⟨-, -, -, hComp, -⟩ := hCalc n a.one_le _ hS g g hgS hgS
  have hlt : ∀ z ∈ sublevelSet a M, ‖g z - 1‖ < 1 := by
    intro z hz
    have hx0 := weightedNorm_nonneg a z
    have hz' : a.weightedNorm z < (M + 1)⁻¹ := hz
    have hm : a.weightedNorm z * (M + 1) < 1 := by
      have := mul_lt_mul_of_pos_right hz' hMp
      rwa [inv_mul_cancel₀ hMp.ne'] at this
    have hx1 : 0 < 1 - a.weightedNorm z := by nlinarith
    refine lt_of_le_of_lt (hAB z (hSU hz)).2 ?_
    rw [← div_eq_mul_inv, div_lt_one hx1]
    nlinarith
  have hdisk : IsOpen discAtOne := isOpen_lt (by fun_prop) continuous_const
  have hLog : ComplexVariables.IsHolomorphicScalar (sublevelSet a M) (logOf g) :=
    hComp discAtOne principalLog hdisk hlogD fun z hz => hlt z hz
  have hhalf : ∀ z, a.weightedNorm z ≤ 1 / 2 * (M + 1)⁻¹ →
      ‖g z - 1‖ ≤ M / (2 * M + 1) ∧ 1 / 2 < ‖g z‖ ∧ ‖g z‖ < 3 / 2 ∧
        ‖logOf g z‖ ≤ Real.log 2 := by
    intro z hz
    have hx0 := weightedNorm_nonneg a z
    have hm : a.weightedNorm z * (2 * M + 2) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hz (by linarith : (0 : ℝ) ≤ 2 * M + 2)
      have he : 1 / 2 * (M + 1)⁻¹ * (2 * M + 2) = 1 := by
        field_simp
      rwa [he] at this
    have hx1 : 0 < 1 - a.weightedNorm z := by nlinarith
    have hzU : z ∈ a.unitSet := by
      change a.weightedNorm z < 1
      linarith
    have hd : 0 < 2 * M + 1 := by linarith
    have hle : ‖g z - 1‖ ≤ M / (2 * M + 1) := by
      refine (hAB z hzU).2.trans ?_
      rw [← div_eq_mul_inv, div_le_div_iff₀ hx1 hd]
      nlinarith [mul_nonneg hM0.le (sub_nonneg.mpr hm)]
    have hhalf' : M / (2 * M + 1) < 1 / 2 := by
      rw [div_lt_iff₀ hd]
      linarith
    have hlt2 := lt_of_le_of_lt hle hhalf'
    have hup : ‖g z‖ ≤ ‖g z - 1‖ + 1 := by
      simpa using norm_add_le (g z - 1) 1
    have hlo : 1 ≤ ‖g z‖ + ‖g z - 1‖ := by
      simpa using norm_sub_le (g z) (g z - 1)
    exact ⟨hle, by linarith, by linarith, hlog2 _ hlt2.le⟩
  refine ⟨hM1, fun z hz => le_min (hAB z hz).1 (hAB z hz).2, ⟨fun z hz => ⟨hlt z hz, ?_⟩, hLog,
    fun z hz => hlogE _ (hlt z hz), ?_, ?_, hhalf⟩, ?_⟩
  · intro hz0
    have := hlt z hz
    rw [hz0] at this
    simp at this
  · change principalLog (g 0) = 0
    rw [hg0, hlog1]
  · have hd : 0 < 2 * M + 1 := by linarith
    rw [div_lt_iff₀ hd]
    linarith
  · have hn : (0 : ℝ) < n := by exact_mod_cast a.one_le
    have hP : (0 : ℝ) < 2 * M + 2 := by linarith
    let r : Fin n → ℝ := fun i => ((2 * M + 2) * n * a.c i)⁻¹
    have hrpos : ∀ i, 0 < r i := fun i => inv_pos.mpr (mul_pos (mul_pos hP hn) (a.c_pos i))
    have hsmall : ∀ z ∈ CauchyEstimates.closedPolydisk r,
        a.weightedNorm z ≤ 1 / 2 * (M + 1)⁻¹ := by
      intro z hz
      have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          a.c i * ‖z i‖ ≤ ((2 * M + 2) * n)⁻¹ := by
        intro i _
        have hi := mul_le_mul_of_nonneg_left (hz i) (a.c_pos i).le
        refine hi.trans (le_of_eq ?_)
        have := (a.c_pos i).ne'
        simp only [r]
        field_simp
      have hsum := Finset.sum_le_sum hterm
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
      refine le_trans hsum (le_of_eq ?_)
      field_simp
    have hPS : CauchyEstimates.closedPolydisk r ⊆ sublevelSet a M := by
      intro z hz
      have hz' := hsmall z hz
      change a.weightedNorm z < (M + 1)⁻¹
      linarith
    have hmain := hCauchy.1 n a.one_le r hrpos (sublevelSet a M) (logOf g) (Real.log 2) hLog hPS
      (Real.log_nonneg one_le_two) fun z hz => (hhalf z (hsmall z hz)).2.2.2
    refine hmain.trans (le_of_eq ?_)
    simp only [r, inv_inv, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    ring
end YangMills.Construction.LogBounds
