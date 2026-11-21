import YangMills.Construction.TorusOrFourSpace.ContinuousPartialsAreContinuousDifferentiability
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.PartialsSmooth
open Filter Topology Asymptotics Coords
variable {p : ℕ+}
def blendPoint (x h : Coords p) (S : Finset (Fin (4 * (p : ℕ)))) : Coords p :=
  fun i => if i ∈ S then x i + h i else x i
theorem hasDerivAt_partialAlong_line (G : Coords p → ℂ) (j : Fin (4 * (p : ℕ)))
    (hd : ∀ x, LineDifferentiableAt ℝ G x (Pi.single j 1)) (y : Coords p) (s : ℝ) :
    HasDerivAt (fun u : ℝ => G (y + u • (Pi.single j 1 : Coords p)))
      (partialAlong j G (y + s • (Pi.single j 1 : Coords p))) s := by
  have h0 : HasDerivAt
      (fun t : ℝ => G (y + s • (Pi.single j 1 : Coords p) +
        t • (Pi.single j 1 : Coords p)))
      (partialAlong j G (y + s • (Pi.single j 1 : Coords p))) (s - s) := by
    rw [sub_self]
    exact (hd (y + s • (Pi.single j 1 : Coords p))).hasLineDerivAt
  have h1 := HasDerivAt.comp_sub_const s s h0
  have h2 : (fun u : ℝ => G (y + s • (Pi.single j 1 : Coords p) +
      (u - s) • (Pi.single j 1 : Coords p))) =
      fun u : ℝ => G (y + u • (Pi.single j 1 : Coords p)) := by
    funext u
    congr 1
    rw [sub_smul]
    abel
  rw [h2] at h1
  exact h1
theorem norm_sub_sum_partialAlong_le (G : Coords p → ℂ)
    (hd : ∀ j, ∀ x, LineDifferentiableAt ℝ G x (Pi.single j 1))
    {x h : Coords p} {ε : ℝ}
    (hb : ∀ j z, (∀ i, |z i - x i| ≤ |h i|) →
      ‖partialAlong j G z - partialAlong j G x‖ ≤ ε)
    (S : Finset (Fin (4 * (p : ℕ)))) :
    ‖G (blendPoint x h S) - G x - ∑ j ∈ S, (h j : ℂ) * partialAlong j G x‖ ≤
      ε * ∑ j ∈ S, |h j| := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have : blendPoint x h ∅ = x := by
      funext i
      simp [blendPoint]
    simp [this]
  | insert a S ha ih =>
    have hy : blendPoint x h (insert a S) =
        blendPoint x h S + h a • (Pi.single a 1 : Coords p) := by
      funext i
      by_cases hia : i = a
      · subst hia
        simp [blendPoint, ha]
      · simp [blendPoint, hia]
    have key : ‖G (blendPoint x h S + h a • (Pi.single a 1 : Coords p)) -
        G (blendPoint x h S) - (h a : ℂ) * partialAlong a G x‖ ≤ ε * |h a| := by
      have hφ : ∀ s : ℝ, HasDerivAt
          (fun u : ℝ => G (blendPoint x h S + u • (Pi.single a 1 : Coords p)) -
            (u : ℂ) * partialAlong a G x)
          (partialAlong a G (blendPoint x h S + s • (Pi.single a 1 : Coords p)) -
            partialAlong a G x) s := by
        intro s
        have h1 := hasDerivAt_partialAlong_line G a (hd a) (blendPoint x h S) s
        have h2 : HasDerivAt (fun u : ℝ => (u : ℂ) * partialAlong a G x)
            (partialAlong a G x) s := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const
            (partialAlong a G x)
        exact h1.sub h2
      have hbound : ∀ s ∈ Set.uIcc (0 : ℝ) (h a),
          ‖partialAlong a G (blendPoint x h S + s • (Pi.single a 1 : Coords p)) -
            partialAlong a G x‖ ≤ ε := by
        intro s hs
        refine hb a _ fun i => ?_
        have hs' : |s| ≤ |h a| := by
          have := Set.abs_sub_left_of_mem_uIcc hs
          simpa using this
        by_cases hia : i = a
        · subst hia
          simpa [blendPoint, ha] using hs'
        · by_cases hiS : i ∈ S
          · simp [blendPoint, hiS, hia]
          · simp [blendPoint, hiS, hia]
      have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (s := Set.uIcc (0 : ℝ) (h a)) (fun s _ => (hφ s).hasDerivWithinAt) hbound
        (convex_uIcc 0 (h a)) Set.left_mem_uIcc Set.right_mem_uIcc
      simpa [sub_sub, add_comm, Real.norm_eq_abs] using this
    rw [hy, Finset.sum_insert ha, Finset.sum_insert ha, mul_add]
    have hsplit : G (blendPoint x h S + h a • (Pi.single a 1 : Coords p)) - G x -
        ((h a : ℂ) * partialAlong a G x + ∑ j ∈ S, (h j : ℂ) * partialAlong j G x) =
        (G (blendPoint x h S + h a • (Pi.single a 1 : Coords p)) -
          G (blendPoint x h S) - (h a : ℂ) * partialAlong a G x) +
        (G (blendPoint x h S) - G x - ∑ j ∈ S, (h j : ℂ) * partialAlong j G x) := by
      ring
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add key ih)
def partialsCLM (G : Coords p → ℂ) (x : Coords p) : Coords p →L[ℝ] ℂ :=
  ∑ j, (ContinuousLinearMap.proj j : Coords p →L[ℝ] ℝ).smulRight (partialAlong j G x)
theorem partialsCLM_apply (G : Coords p → ℂ) (x h : Coords p) :
    partialsCLM G x h = ∑ j, (h j : ℂ) * partialAlong j G x := by
  simp [partialsCLM, Complex.real_smul]
theorem hasFDerivAt_of_continuous_partialAlong (G : Coords p → ℂ)
    (hd : ∀ j, ∀ x, LineDifferentiableAt ℝ G x (Pi.single j 1))
    (hc : ∀ j, Continuous (partialAlong j G)) (x : Coords p) :
    HasFDerivAt G (partialsCLM G x) x := by
  classical
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hcpos
  set n : ℝ := ((4 * (p : ℕ) : ℕ) : ℝ) with hn
  set ε : ℝ := c / (n + 1) with hε
  have hεpos : 0 < ε := div_pos hcpos (by linarith)
  have hev : ∀ᶠ z in 𝓝 x, ∀ j,
      ‖partialAlong j G z - partialAlong j G x‖ < ε := by
    rw [Filter.eventually_all]
    intro j
    have := (hc j).continuousAt (x := x)
    have h2 := (Metric.tendsto_nhds.1 this) ε hεpos
    simpa [dist_eq_norm] using h2
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  filter_upwards [Metric.ball_mem_nhds (0 : Coords p) hδ] with h hh
  have hhδ : ‖h‖ < δ := by simpa using hh
  have hb : ∀ j z, (∀ i, |z i - x i| ≤ |h i|) →
      ‖partialAlong j G z - partialAlong j G x‖ ≤ ε := by
    intro j z hz
    refine (hball ?_ j).le
    rw [dist_pi_lt_iff hδ]
    intro i
    rw [Real.dist_eq]
    exact ((hz i).trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm h i)).trans_lt hhδ
  have hmain := norm_sub_sum_partialAlong_le G hd hb Finset.univ
  have huniv : blendPoint x h Finset.univ = x + h := by
    funext i
    simp [blendPoint]
  rw [huniv, ← partialsCLM_apply] at hmain
  have hsum : ∑ j, |h j| ≤ n * ‖h‖ := by
    calc ∑ j, |h j| ≤ ∑ _j : Fin (4 * (p : ℕ)), ‖h‖ :=
          Finset.sum_le_sum fun j _ => by simpa [Real.norm_eq_abs] using norm_le_pi_norm h j
      _ = n * ‖h‖ := by simp [hn]
  calc ‖G (x + h) - G x - partialsCLM G x h‖ ≤ ε * ∑ j, |h j| := hmain
    _ ≤ ε * (n * ‖h‖) := by gcongr
    _ ≤ c * ‖h‖ := by
      have : ε * n ≤ c := by
        rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
      nlinarith [norm_nonneg h]
theorem contDiff_of_contPartialsUpTo :
    ∀ (ν : ℕ) (G : Coords p → ℂ), ContPartialsUpTo ν G → ContDiff ℝ ν G
  | 0, G, h => by
    have h' : Continuous G := h
    simpa using (contDiff_zero (𝕜 := ℝ)).2 h'
  | ν + 1, G, h => by
    obtain ⟨-, hj⟩ := h
    have hp : ∀ j, ContDiff ℝ ν (partialAlong j G) :=
      fun j => contDiff_of_contPartialsUpTo ν _ (hj j).2
    have hF := hasFDerivAt_of_continuous_partialAlong G (fun j => (hj j).1)
      (fun j => (hp j).continuous)
    have hfd : fderiv ℝ G = partialsCLM G := funext fun x => (hF x).fderiv
    have hgrad : ContDiff ℝ ν (partialsCLM G) := by
      unfold partialsCLM
      exact ContDiff.sum fun j _ => contDiff_const.smulRight (hp j)
    rw [Nat.cast_add, Nat.cast_one]
    refine contDiff_succ_iff_fderiv.2 ⟨fun x => (hF x).differentiableAt, by simp, ?_⟩
    rw [hfd]
    exact hgrad
theorem contPartialsUpTo_of_contDiff :
    ∀ (ν : ℕ) (G : Coords p → ℂ), ContDiff ℝ ν G → ContPartialsUpTo ν G
  | 0, G, h => h.continuous
  | ν + 1, G, h => by
    refine ⟨h.continuous, fun j => ?_⟩
    rw [Nat.cast_add, Nat.cast_one] at h
    have hdiff : Differentiable ℝ G := (contDiff_succ_iff_fderiv.1 h).1
    have hder : ContDiff ℝ ν (fderiv ℝ G) := (contDiff_succ_iff_fderiv.1 h).2.2
    refine ⟨fun x => (hdiff x).lineDifferentiableAt, ?_⟩
    have hpart : partialAlong j G =
        fun x => fderiv ℝ G x (Pi.single j 1 : Coords p) :=
      funext fun x => (hdiff x).lineDeriv_eq_fderiv
    apply contPartialsUpTo_of_contDiff
    rw [hpart]
    exact hder.clm_apply contDiff_const
theorem contPartialsIffContDiff_holds : ContPartialsIffContDiff :=
  fun _ ν G => ⟨contDiff_of_contPartialsUpTo ν G, contPartialsUpTo_of_contDiff ν G⟩
end YangMills.Construction.PeriodicSpace.PartialsSmooth
