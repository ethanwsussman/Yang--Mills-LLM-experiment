import YangMills.Construction.ColdChainAtEveryLevel.GaugeMapAgainstTheCurl
import YangMills.Construction.ColdChainAtEveryLevel.GaugeMapOnDifferences
import YangMills.Construction.ColdChainAtEveryLevel.GaugeMotionsOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.NormsOnNearCells
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.GaugeDirectionKernel
open BlockAverages GaugeMap NearCellNorms GaugeMotions LatticePaths
variable {F : BlockFrame} {S : Finset F.Cell}
theorem cellBondNorm_eq_finLpNorm (q : ℝ) (f : F.Site 0 → Fin 4 → ℍ[ℝ]) (z : F.Cell) :
    cellBondNorm q S (fun _ => 1) f z = finLpNorm (bondsOver S {z} 0) q (fun b => ‖f b.1 b.2‖) := by
  simp [cellBondNorm, finLpNorm]
theorem cellPlaquetteNorm_eq_finLpNorm (q : ℝ) (g : F.Site 0 × Fin 4 × Fin 4 → ℍ[ℝ]) (z : F.Cell) :
    cellPlaquetteNorm q S (fun _ => 1) g z = finLpNorm (plaquettesOver S {z} 0) q (fun p => ‖g p‖) := by
  simp [cellPlaquetteNorm, finLpNorm]
theorem cellSiteNorm_eq_finLpNorm (q : ℝ) (ξ : F.Site 0 → ℍ[ℝ]) (z : F.Cell) :
    cellSiteNorm q S (fun _ => 1) ξ z = finLpNorm (sitesInCell S z) q (fun x => ‖ξ x‖) := by
  simp [cellSiteNorm, finLpNorm, sitesInCell]
section FiniteSums
variable {ι : Type} {A : Finset ι}
theorem finLpNorm_le_mul_of_sum_rpow_le {p K Y M : ℝ} (hp : 0 < p) (hK : 0 ≤ K) (hY : 0 ≤ Y) {f : ι → ℝ}
    (hf : ∀ i ∈ A, 0 ≤ f i) (hM : M ≤ K ^ p) (h : ∑ i ∈ A, f i ^ p ≤ M * Y ^ p) : finLpNorm A p f ≤ K * Y := by
  refine finLpNorm_le_of_sum_rpow_le A hp hf (by positivity) ?_
  rw [Real.mul_rpow hK hY]
  exact h.trans (mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg hY _))
theorem finLpNorm_add_add_add_le {p : ℝ} (hp : 1 ≤ p) {f₁ f₂ f₃ f₄ : ι → ℝ} (h₁ : ∀ i ∈ A, 0 ≤ f₁ i)
    (h₂ : ∀ i ∈ A, 0 ≤ f₂ i) (h₃ : ∀ i ∈ A, 0 ≤ f₃ i) (h₄ : ∀ i ∈ A, 0 ≤ f₄ i) :
    finLpNorm A p (fun i => f₁ i + f₂ i + f₃ i + f₄ i) ≤
      finLpNorm A p f₁ + finLpNorm A p f₂ + finLpNorm A p f₃ + finLpNorm A p f₄ := by
  have a1 := finLpNorm_add_le A hp (f := fun i => f₁ i + f₂ i + f₃ i) (g := f₄)
    (fun i hi => add_nonneg (add_nonneg (h₁ i hi) (h₂ i hi)) (h₃ i hi)) h₄
  have a2 := finLpNorm_add_le A hp (f := fun i => f₁ i + f₂ i) (g := f₃)
    (fun i hi => add_nonneg (h₁ i hi) (h₂ i hi)) h₃
  have a3 := finLpNorm_add_le A hp h₁ h₂
  linarith
end FiniteSums
theorem finLpNorm_form_and_curl_le (hodd : Odd F.blockSide) {C₀ A Y T : ℝ} (hC₀ : 0 ≤ C₀) (hA : 0 ≤ A)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (Rz : F.GaugeField 0) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (ξ : F.Site 0 → imaginaryQuaternions) (f : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (hbond : ∀ b ∈ innerBonds S 0, ‖f b.1 b.2‖ ≤ C₀ * ‖u b.1 b.2‖ * (‖ξ b.1‖ + ‖ξ (b.1 + unitStep 0 b.2)‖))
    (hcurl : ∀ p ∈ innerPlaquettes S 0, ‖linearizedCurl Rz f p‖ ≤
      C₀ * ((‖linearizedCurl Rz u p‖ + plaquetteBondSum (fun x i => ‖u x i‖) p ^ 2) *
          plaquetteCornerSum (fun x => ‖ξ x‖) p +
        plaquetteBondSum (fun x i => ‖u x i‖) p *
          plaquetteBondSum (fun x i => ‖covariantDiff Rz (fun x => ξ x) x i‖) p))
    (hu : ∀ z ∈ S, ∑ b ∈ bondsOver S {z} 0, ‖u b.1 b.2‖ ^ (4 : ℝ) ≤ A ^ (4 : ℝ))
    (hc : ∀ z ∈ S, finLpNorm (plaquettesOver S {z} 0) 2 (fun p => ‖linearizedCurl Rz u p‖) ≤ A)
    (hξ : ∀ z ∈ S, ∑ x ∈ sitesInCell S z, ‖ξ x‖ ^ (12 : ℝ) ≤ Y ^ (12 : ℝ))
    (hD : ∀ z ∈ S, ∑ b ∈ bondsOver S {z} 0, ‖covariantDiff Rz (fun x => ξ x) b.1 b.2‖ ^ (3 : ℝ) ≤ T ^ (3 : ℝ))
    (z : F.Cell) (hz : z ∈ S) :
    finLpNorm (bondsOver S {z} 0) 3 (fun b => ‖f b.1 b.2‖) ≤ C₀ * (A * (4 * Y)) ∧
    finLpNorm (plaquettesOver S {z} 0) (12 / 7) (fun p => ‖linearizedCurl Rz f p‖) ≤
      C₀ * (A * (8 * Y) + (12 * A) * ((12 * A) * (8 * Y)) + (12 * A) * (16 * T)) := by
  set B := bondsOver S {z} 0 with hB
  set P := plaquettesOver S {z} 0 with hP
  have hA4 : 0 ≤ A ^ (4 : ℝ) := Real.rpow_nonneg hA _
  have hY12 : 0 ≤ Y ^ (12 : ℝ) := Real.rpow_nonneg hY _
  have hT3 : 0 ≤ T ^ (3 : ℝ) := Real.rpow_nonneg hT _
  have nξ : ∀ x, 0 ≤ ‖ξ x‖ ^ (12 : ℝ) := fun x => Real.rpow_nonneg (norm_nonneg _) _
  constructor
  · have c1 : finLpNorm B 12 (fun b => ‖ξ b.1‖) ≤ 2 * Y := by
      refine finLpNorm_le_mul_of_sum_rpow_le (M := 4) (by norm_num) (by norm_num) hY (fun _ _ => norm_nonneg _)
        (by norm_num) ?_
      exact sum_bondsOver_tail_le (f := fun x => ‖ξ x‖ ^ (12 : ℝ)) hodd nξ hY12 hξ z
    have c2 : finLpNorm B 12 (fun b => ‖ξ (b.1 + unitStep 0 b.2)‖) ≤ 2 * Y := by
      refine finLpNorm_le_mul_of_sum_rpow_le (M := 8) (by norm_num) (by norm_num) hY (fun _ _ => norm_nonneg _)
        (by norm_num) ?_
      exact sum_bondsOver_head_le (f := fun x => ‖ξ x‖ ^ (12 : ℝ)) hodd nξ hY12 hξ z
    have c3 : finLpNorm B 12 (fun b => ‖ξ b.1‖ + ‖ξ (b.1 + unitStep 0 b.2)‖) ≤ 4 * Y := by
      refine (finLpNorm_add_le B (by norm_num) (fun _ _ => norm_nonneg _) fun _ _ => norm_nonneg _).trans ?_
      linarith
    have c4 : finLpNorm B 4 (fun b => ‖u b.1 b.2‖) ≤ A :=
      finLpNorm_le_of_sum_rpow_le B (by norm_num) (fun _ _ => norm_nonneg _) hA (hu z hz)
    have h1 : finLpNorm B 3 (fun b => ‖f b.1 b.2‖) ≤
        finLpNorm B 3 (fun b => C₀ * (‖u b.1 b.2‖ * (‖ξ b.1‖ + ‖ξ (b.1 + unitStep 0 b.2)‖))) := by
      refine finLpNorm_mono B (by norm_num) (fun _ _ => norm_nonneg _) fun b hb => ?_
      have := hbond b (mem_bondsOver_singleton z b hb).1
      linarith [mul_assoc C₀ ‖u b.1 b.2‖ (‖ξ b.1‖ + ‖ξ (b.1 + unitStep 0 b.2)‖)]
    rw [finLpNorm_const_mul B (by norm_num) hC₀ (fun _ _ => by positivity)] at h1
    have h2 := finLpNorm_mul_le B (a := 4) (b := 12) (c := 3) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (f := fun b => ‖u b.1 b.2‖) (g := fun b => ‖ξ b.1‖ + ‖ξ (b.1 + unitStep 0 b.2)‖)
      (fun _ _ => norm_nonneg _) (fun _ _ => by positivity)
    refine h1.trans (mul_le_mul_of_nonneg_left (h2.trans ?_) hC₀)
    exact mul_le_mul c4 c3 (finLpNorm_nonneg _ _ fun _ _ => by positivity) hA
  · have nu : ∀ b : F.Site 0 × Fin 4, 0 ≤ ‖u b.1 b.2‖ ^ (4 : ℝ) := fun b => Real.rpow_nonneg (norm_nonneg _) _
    have nd : ∀ b : F.Site 0 × Fin 4, 0 ≤ ‖covariantDiff Rz (fun x => ξ x) b.1 b.2‖ ^ (3 : ℝ) :=
      fun b => Real.rpow_nonneg (norm_nonneg _) _
    obtain ⟨u1, u2, u3, u4⟩ := sum_plaquettesOver_bond_le (g := fun b => ‖u b.1 b.2‖ ^ (4 : ℝ)) hodd nu hA4 hu z
    obtain ⟨d1, d2, d3, d4⟩ :=
      sum_plaquettesOver_bond_le (g := fun b => ‖covariantDiff Rz (fun x => ξ x) b.1 b.2‖ ^ (3 : ℝ)) hodd nd hT3 hD z
    obtain ⟨x1, x2, x3, x4⟩ := sum_plaquettesOver_corner_le (f := fun x => ‖ξ x‖ ^ (12 : ℝ)) hodd nξ hY12 hξ z
    set Up : F.Site 0 × Fin 4 × Fin 4 → ℝ := plaquetteBondSum (fun x i => ‖u x i‖) with hUp
    set Xp : F.Site 0 × Fin 4 × Fin 4 → ℝ := plaquetteCornerSum (fun x => ‖ξ x‖) with hXp
    set Dp : F.Site 0 × Fin 4 × Fin 4 → ℝ :=
      plaquetteBondSum (fun x i => ‖covariantDiff Rz (fun x => ξ x) x i‖) with hDp
    have nUp : ∀ p, 0 ≤ Up p := fun p => by
      simp only [hUp, plaquetteBondSum]; positivity
    have nXp : ∀ p, 0 ≤ Xp p := fun p => by
      simp only [hXp, plaquetteCornerSum]; positivity
    have nDp : ∀ p, 0 ≤ Dp p := fun p => by
      simp only [hDp, plaquetteBondSum]; positivity
    have lU : finLpNorm P 4 Up ≤ 12 * A := by
      have q1 : finLpNorm P 4 (fun p => ‖u p.1 p.2.1‖) ≤ 3 * A :=
        finLpNorm_le_mul_of_sum_rpow_le (M := 32) (by norm_num) (by norm_num) hA (fun _ _ => norm_nonneg _)
          (by norm_num) u1
      have q2 : finLpNorm P 4 (fun p => ‖u (p.1 + unitStep 0 p.2.1) p.2.2‖) ≤ 3 * A :=
        finLpNorm_le_mul_of_sum_rpow_le (M := 32) (by norm_num) (by norm_num) hA (fun _ _ => norm_nonneg _)
          (by norm_num) u2
      have q3 : finLpNorm P 4 (fun p => ‖u (p.1 + unitStep 0 p.2.2) p.2.1‖) ≤ 3 * A :=
        finLpNorm_le_mul_of_sum_rpow_le (M := 32) (by norm_num) (by norm_num) hA (fun _ _ => norm_nonneg _)
          (by norm_num) u3
      have q4 : finLpNorm P 4 (fun p => ‖u p.1 p.2.2‖) ≤ 3 * A :=
        finLpNorm_le_mul_of_sum_rpow_le (M := 32) (by norm_num) (by norm_num) hA (fun _ _ => norm_nonneg _)
          (by norm_num) u4
      have := finLpNorm_add_add_add_le (A := P) (p := 4) (by norm_num) (f₁ := fun p => ‖u p.1 p.2.1‖)
        (f₂ := fun p => ‖u (p.1 + unitStep 0 p.2.1) p.2.2‖) (f₃ := fun p => ‖u (p.1 + unitStep 0 p.2.2) p.2.1‖)
        (f₄ := fun p => ‖u p.1 p.2.2‖) (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
        (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
      have e : Up = fun p => ‖u p.1 p.2.1‖ + ‖u (p.1 + unitStep 0 p.2.1) p.2.2‖ +
        ‖u (p.1 + unitStep 0 p.2.2) p.2.1‖ + ‖u p.1 p.2.2‖ := rfl
      rw [e]
      linarith
    have lX : finLpNorm P 12 Xp ≤ 8 * Y := by
      have q1 : finLpNorm P 12 (fun p => ‖ξ p.1‖) ≤ 2 * Y :=
        finLpNorm_le_mul_of_sum_rpow_le (M := 64) (by norm_num) (by norm_num) hY (fun _ _ => norm_nonneg _)
          (by norm_num) x1
      have q2 : finLpNorm P 12 (fun p => ‖ξ (p.1 + unitStep 0 p.2.1)‖) ≤ 2 * Y :=
        finLpNorm_le_mul_of_sum_rpow_le (M := 64) (by norm_num) (by norm_num) hY (fun _ _ => norm_nonneg _)
          (by norm_num) x2
      have q3 : finLpNorm P 12 (fun p => ‖ξ (p.1 + unitStep 0 p.2.2)‖) ≤ 2 * Y :=
        finLpNorm_le_mul_of_sum_rpow_le (M := 64) (by norm_num) (by norm_num) hY (fun _ _ => norm_nonneg _)
          (by norm_num) x3
      have q4 : finLpNorm P 12 (fun p => ‖ξ (p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2)‖) ≤ 2 * Y :=
        finLpNorm_le_mul_of_sum_rpow_le (M := 64) (by norm_num) (by norm_num) hY (fun _ _ => norm_nonneg _)
          (by norm_num) x4
      have := finLpNorm_add_add_add_le (A := P) (p := 12) (by norm_num) (f₁ := fun p => ‖ξ p.1‖)
        (f₂ := fun p => ‖ξ (p.1 + unitStep 0 p.2.1)‖) (f₃ := fun p => ‖ξ (p.1 + unitStep 0 p.2.2)‖)
        (f₄ := fun p => ‖ξ (p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2)‖) (fun _ _ => norm_nonneg _)
        (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
      have e : Xp = fun p => ‖ξ p.1‖ + ‖ξ (p.1 + unitStep 0 p.2.1)‖ + ‖ξ (p.1 + unitStep 0 p.2.2)‖ +
        ‖ξ (p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2)‖ := rfl
      rw [e]
      linarith
    have lD : finLpNorm P 3 Dp ≤ 16 * T := by
      have q1 : finLpNorm P 3 (fun p => ‖covariantDiff Rz (fun x => ξ x) p.1 p.2.1‖) ≤ 4 * T :=
        finLpNorm_le_mul_of_sum_rpow_le (M := 32) (by norm_num) (by norm_num) hT (fun _ _ => norm_nonneg _)
          (by norm_num) d1
      have q2 : finLpNorm P 3 (fun p => ‖covariantDiff Rz (fun x => ξ x) (p.1 + unitStep 0 p.2.1) p.2.2‖) ≤ 4 * T :=
        finLpNorm_le_mul_of_sum_rpow_le (M := 32) (by norm_num) (by norm_num) hT (fun _ _ => norm_nonneg _)
          (by norm_num) d2
      have q3 : finLpNorm P 3 (fun p => ‖covariantDiff Rz (fun x => ξ x) (p.1 + unitStep 0 p.2.2) p.2.1‖) ≤ 4 * T :=
        finLpNorm_le_mul_of_sum_rpow_le (M := 32) (by norm_num) (by norm_num) hT (fun _ _ => norm_nonneg _)
          (by norm_num) d3
      have q4 : finLpNorm P 3 (fun p => ‖covariantDiff Rz (fun x => ξ x) p.1 p.2.2‖) ≤ 4 * T :=
        finLpNorm_le_mul_of_sum_rpow_le (M := 32) (by norm_num) (by norm_num) hT (fun _ _ => norm_nonneg _)
          (by norm_num) d4
      have := finLpNorm_add_add_add_le (A := P) (p := 3) (by norm_num)
        (f₁ := fun p => ‖covariantDiff Rz (fun x => ξ x) p.1 p.2.1‖)
        (f₂ := fun p => ‖covariantDiff Rz (fun x => ξ x) (p.1 + unitStep 0 p.2.1) p.2.2‖)
        (f₃ := fun p => ‖covariantDiff Rz (fun x => ξ x) (p.1 + unitStep 0 p.2.2) p.2.1‖)
        (f₄ := fun p => ‖covariantDiff Rz (fun x => ξ x) p.1 p.2.2‖) (fun _ _ => norm_nonneg _)
        (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
      have e : Dp = fun p => ‖covariantDiff Rz (fun x => ξ x) p.1 p.2.1‖ +
        ‖covariantDiff Rz (fun x => ξ x) (p.1 + unitStep 0 p.2.1) p.2.2‖ +
        ‖covariantDiff Rz (fun x => ξ x) (p.1 + unitStep 0 p.2.2) p.2.1‖ +
        ‖covariantDiff Rz (fun x => ξ x) p.1 p.2.2‖ := rfl
      rw [e]
      linarith
    set Cu : F.Site 0 × Fin 4 × Fin 4 → ℝ := fun p => ‖linearizedCurl Rz u p‖ with hCu
    have nCu : ∀ p, 0 ≤ Cu p := fun p => norm_nonneg _
    have hA2 : finLpNorm P 2 Cu ≤ A := hc z hz
    have t1 := finLpNorm_mul_le P (a := 2) (b := 12) (c := 12 / 7) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (f := Cu) (g := Xp) (fun p _ => nCu p) (fun p _ => nXp p)
    have t2 := finLpNorm_mul_le P (a := 4) (b := 12) (c := 3) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (f := Up) (g := Xp) (fun p _ => nUp p) (fun p _ => nXp p)
    have t3 := finLpNorm_mul_le P (a := 4) (b := 3) (c := 12 / 7) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (f := Up) (g := fun p => Up p * Xp p) (fun p _ => nUp p) (fun p _ => mul_nonneg (nUp p) (nXp p))
    have t4 := finLpNorm_mul_le P (a := 4) (b := 3) (c := 12 / 7) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (f := Up) (g := Dp) (fun p _ => nUp p) (fun p _ => nDp p)
    have lX0 : 0 ≤ finLpNorm P 12 Xp := finLpNorm_nonneg _ _ fun p _ => nXp p
    have lD0 : 0 ≤ finLpNorm P 3 Dp := finLpNorm_nonneg _ _ fun p _ => nDp p
    have r1 : finLpNorm P (12 / 7) (fun p => Cu p * Xp p) ≤ A * (8 * Y) :=
      t1.trans (mul_le_mul hA2 lX lX0 hA)
    have r2' : finLpNorm P 3 (fun p => Up p * Xp p) ≤ (12 * A) * (8 * Y) :=
      t2.trans (mul_le_mul lU lX lX0 (by positivity))
    have r2 : finLpNorm P (12 / 7) (fun p => Up p * (Up p * Xp p)) ≤ (12 * A) * ((12 * A) * (8 * Y)) :=
      t3.trans (mul_le_mul lU r2' (finLpNorm_nonneg _ _ fun p _ => mul_nonneg (nUp p) (nXp p)) (by positivity))
    have r3 : finLpNorm P (12 / 7) (fun p => Up p * Dp p) ≤ (12 * A) * (16 * T) :=
      t4.trans (mul_le_mul lU lD lD0 (by positivity))
    have hpt : finLpNorm P (12 / 7) (fun p => ‖linearizedCurl Rz f p‖) ≤
        finLpNorm P (12 / 7) (fun p => C₀ * (Cu p * Xp p + Up p * (Up p * Xp p) + Up p * Dp p)) := by
      refine finLpNorm_mono P (by norm_num) (fun _ _ => norm_nonneg _) fun p hp => ?_
      have := hcurl p (mem_plaquettesOver_singleton z p hp).1
      refine this.trans (le_of_eq ?_)
      simp only [hCu]
      ring
    rw [finLpNorm_const_mul P (by norm_num) hC₀ (fun p _ => by
      have := nCu p; have := nUp p; have := nXp p; have := nDp p; positivity)] at hpt
    refine hpt.trans (mul_le_mul_of_nonneg_left ?_ hC₀)
    have a1 := finLpNorm_add_le P (p := 12 / 7) (by norm_num) (f := fun p => Cu p * Xp p + Up p * (Up p * Xp p))
      (g := fun p => Up p * Dp p) (fun p _ => by
        have := nCu p; have := nUp p; have := nXp p; positivity) (fun p _ => mul_nonneg (nUp p) (nDp p))
    have a2 := finLpNorm_add_le P (p := 12 / 7) (by norm_num) (f := fun p => Cu p * Xp p)
      (g := fun p => Up p * (Up p * Xp p))
      (fun p _ => mul_nonneg (nCu p) (nXp p)) (fun p _ => mul_nonneg (nUp p) (mul_nonneg (nUp p) (nXp p)))
    linarith
theorem eq_zero_of_le_self_bound {T Q κ s A C₀ C₃ C₄ C₅ Yb Tb : ℝ} (hT0 : 0 ≤ T) (hQ0 : 0 ≤ Q) (hκ : 0 ≤ κ)
    (hs : 0 ≤ s) (hA : 0 ≤ A) (hC₀ : 0 ≤ C₀) (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄) (hC₅ : 0 ≤ C₅) (hQ : Q ≤ κ * T)
    (hκ1 : κ ≤ 1) (hs1 : s ≤ 1) (hA1 : A ≤ 1) (h1 : C₄ * s ≤ 1 / 8) (h2 : (C₃ * (C₅ * 2) + C₅) * κ ≤ 1 / 8)
    (h3 : (C₃ + 1) * (1356 * C₀ * A * (C₄ + C₅ + 1)) ≤ 1 / 8)
    (hYb : Yb = C₄ * T + C₅ * Q) (hTb : Tb = T + C₅ * Q)
    (hT : T ≤ C₄ * s * T + C₃ * (C₅ * (1 + s) * Q) + C₅ * Q +
      C₃ * (C₀ * (A * (4 * Yb)) + C₀ * (A * (8 * Yb) + (12 * A) * ((12 * A) * (8 * Yb)) + (12 * A) * (16 * Tb))) +
      C₀ * (A * (4 * Yb))) : T = 0 := by
  set G := C₄ + C₅ + 1 with hG
  have hQT : Q ≤ T := hQ.trans (by nlinarith)
  have hYG : Yb ≤ G * T := by
    rw [hYb, hG]
    nlinarith [mul_le_mul_of_nonneg_left hQT hC₅]
  have hTG : Tb ≤ G * T := by
    rw [hTb, hG]
    nlinarith [mul_le_mul_of_nonneg_left hQT hC₅, mul_nonneg hC₄ hT0]
  have hY0 : 0 ≤ Yb := by rw [hYb]; positivity
  have hTb0 : 0 ≤ Tb := by rw [hTb]; positivity
  have hAA : A * A ≤ A := by nlinarith
  have e1 : C₀ * (A * (4 * Yb)) ≤ 4 * (C₀ * A * G * T) := by
    have : C₀ * A * Yb ≤ C₀ * A * (G * T) := mul_le_mul_of_nonneg_left hYG (by positivity)
    nlinarith
  have e2 : C₀ * (A * (8 * Yb) + (12 * A) * ((12 * A) * (8 * Yb)) + (12 * A) * (16 * Tb)) ≤
      1352 * (C₀ * A * G * T) := by
    have a2 : C₀ * A * Tb ≤ C₀ * A * (G * T) := mul_le_mul_of_nonneg_left hTG (by positivity)
    have a3 : C₀ * (A * A) * Yb ≤ C₀ * A * Yb :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAA hC₀) hY0
    nlinarith
  have hX : 0 ≤ C₀ * A * G * T := by positivity
  have e3 : C₃ * (C₀ * (A * (4 * Yb)) + C₀ * (A * (8 * Yb) + (12 * A) * ((12 * A) * (8 * Yb)) +
      (12 * A) * (16 * Tb))) + C₀ * (A * (4 * Yb)) ≤ (C₃ + 1) * (1356 * (C₀ * A * G * T)) := by
    have : C₃ * (C₀ * (A * (4 * Yb)) + C₀ * (A * (8 * Yb) + (12 * A) * ((12 * A) * (8 * Yb)) +
        (12 * A) * (16 * Tb))) ≤ C₃ * (1356 * (C₀ * A * G * T)) := mul_le_mul_of_nonneg_left (by linarith) hC₃
    nlinarith
  have e4 : (C₃ + 1) * (1356 * (C₀ * A * G * T)) ≤ (1 / 8) * T := by
    have := mul_le_mul_of_nonneg_right h3 hT0
    calc _ = (C₃ + 1) * (1356 * C₀ * A * G) * T := by ring
      _ ≤ _ := this
  have e5 : C₄ * s * T ≤ (1 / 8) * T := mul_le_mul_of_nonneg_right h1 hT0
  have e6 : C₃ * (C₅ * (1 + s) * Q) + C₅ * Q ≤ (1 / 8) * T := by
    have b1 : C₃ * (C₅ * (1 + s) * Q) ≤ C₃ * (C₅ * 2 * Q) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hQ0) hC₃
      exact mul_le_mul_of_nonneg_left (by linarith) hC₅
    have b2 : (C₃ * (C₅ * 2) + C₅) * Q ≤ (C₃ * (C₅ * 2) + C₅) * (κ * T) :=
      mul_le_mul_of_nonneg_left hQ (by positivity)
    have b3 := mul_le_mul_of_nonneg_right h2 hT0
    nlinarith
  linarith
structure GaugeSliceHypotheses (S : Finset F.Cell) (V : F.GaugeField F.top) (s C₃ C₄ C₅ : ℝ) : Prop where
  gaugeDiff_bound : ∀ (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (B : ℝ),
    (∀ z ∈ S, cellPlaquetteNorm (12 / 7) S (fun _ => 1) (linearizedCurl (referenceFieldChain S V 0) u) z +
      cellBondNorm 3 S (fun _ => 1) (fun x i => u x i) z ≤ B) →
    ∀ z ∈ S, cellBondNorm 3 S (fun _ => 1) (formPlusGaugeDiff S V u) z ≤ C₃ * B
  remainder_bound : ∀ ξ : F.Site 0 → ℍ[ℝ], CellMeanFree S V ξ → ∀ B : ℝ,
    (∀ z ∈ S, cellBondNorm 3 S (fun _ => 1) (covariantDiff (referenceFieldChain S V 0) ξ) z ≤ B) →
    ∀ z ∈ S, cellBondNorm 3 S (fun _ => 1)
      (covariantDiff (referenceFieldChain S V 0) (gaugeRemainder S V ξ)) z ≤ C₄ * s * B
  poincare : ∀ ξ : F.Site 0 → ℍ[ℝ], CellMeanFree S V ξ → ∀ z ∈ S,
    cellSiteNorm 12 S (fun _ => 1) ξ z ≤
      C₄ * cellBondNorm 3 S (fun _ => 1) (covariantDiff (referenceFieldChain S V 0) ξ) z
  bump_mean : ∀ (b : F.Cell → ℍ[ℝ]), ∀ y ∈ S, frameCellMean S V y (cellBumpSection S V b) = b y
  bump_lp4 : ∀ (b : F.Cell → ℍ[ℝ]), ∀ z ∈ S, cellSiteNorm 4 S (fun _ => 1) (cellBumpSection S V b) z ≤
    C₅ * (cellSideLength F : ℝ) * ‖b z‖
  bump_lp12 : ∀ (b : F.Cell → ℍ[ℝ]), ∀ z ∈ S, cellSiteNorm 12 S (fun _ => 1) (cellBumpSection S V b) z ≤
    C₅ * (cellSideLength F : ℝ) ^ (1 / 3 : ℝ) * ‖b z‖
  bump_diff : ∀ (b : F.Cell → ℍ[ℝ]) (B : ℝ), (∀ y ∈ S, ‖b y‖ ≤ B) → ∀ z ∈ S, cellBondNorm 3 S (fun _ => 1)
    (covariantDiff (referenceFieldChain S V 0) (cellBumpSection S V b)) z ≤
      C₅ * (cellSideLength F : ℝ) ^ (1 / 3 : ℝ) * B
  bump_curl : ∀ (b : F.Cell → ℍ[ℝ]) (B : ℝ), (∀ y ∈ S, ‖b y‖ ≤ B) → ∀ z ∈ S,
    cellPlaquetteNorm (12 / 7) S (fun _ => 1)
      (fun p => _root_.YangMills.Construction.BlockAverages.adjointAction (plaquetteHolonomy (referenceFieldChain S V 0) p) (cellBumpSection S V b p.1) -
        cellBumpSection S V b p.1) z ≤ C₅ * s * (cellSideLength F : ℝ) ^ (1 / 3 : ℝ) * B
theorem card_sitesInCell_le (hodd : Odd F.blockSide) (z : F.Cell) :
    ((sitesInCell S z).card : ℝ) ≤ (cellSideLength F : ℝ) ^ 4 := by
  classical
  have hsub : sitesInCell S z ⊆
      (centredCube (F.blockSide ^ (F.top - 0))).image fun h => cellCentre 0 z + siteOfCoords 0 h := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    obtain ⟨y, _, h, hh, rfl⟩ := mem_sitesOfCells.1 h1
    rw [GaugeMapLinear.enclosingCell_cellCentre_add hodd y h hh] at h2
    subst h2
    exact Finset.mem_image.2 ⟨h, hh, rfl⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [card_centredCube (hodd.pow)] at h1
  have e : (cellSideLength F : ℝ) = ((F.blockSide ^ (F.top - 0) : ℕ) : ℝ) := by
    simp [cellSideLength]
  rw [e]
  exact_mod_cast h1
theorem one_le_cellSideLength (hodd : Odd F.blockSide) : (1 : ℝ) ≤ (cellSideLength F : ℝ) := by
  have h : (1 : ℤ) ≤ cellSideLength F := cellSideLength_pos hodd.pos
  exact_mod_cast h
theorem finLpNorm_four_le_twelve (hodd : Odd F.blockSide) (z : F.Cell) {f : F.Site 0 → ℝ} (hf : ∀ x, 0 ≤ f x) :
    finLpNorm (sitesInCell S z) 4 f ≤ finLpNorm (sitesInCell S z) 12 f * (cellSideLength F : ℝ) ^ (2 / 3 : ℝ) := by
  have hN := one_le_cellSideLength (F := F) hodd
  have h := finLpNorm_mul_le (sitesInCell S z) (a := 12) (b := 6) (c := 4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (f := f) (g := fun _ => 1) (fun x _ => hf x) (fun _ _ => zero_le_one)
  simp only [mul_one] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (finLpNorm_nonneg _ _ fun x _ => hf x))
  rw [finLpNorm_const _ (by norm_num) 1 zero_le_one, one_mul]
  have h2 := card_sitesInCell_le (S := S) hodd z
  calc ((sitesInCell S z).card : ℝ) ^ (1 / 6 : ℝ) ≤ ((cellSideLength F : ℝ) ^ 4) ^ (1 / 6 : ℝ) :=
        Real.rpow_le_rpow (by positivity) h2 (by norm_num)
    _ = (cellSideLength F : ℝ) ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
        norm_num
theorem linearizedCurl_of_covariantDiff (Rz : F.GaugeField 0) (g : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (ξ : F.Site 0 → ℍ[ℝ]) (hg : ∀ x i, ((g x i : imaginaryQuaternions) : ℍ[ℝ]) = covariantDiff Rz ξ x i)
    (p : F.Site 0 × Fin 4 × Fin 4) :
    linearizedCurl Rz g p = _root_.YangMills.Construction.BlockAverages.adjointAction (plaquetteHolonomy Rz p) (ξ p.1) - ξ p.1 := by
  obtain ⟨x, μ, ν⟩ := p
  have hval : plaquetteHolonomy Rz (x, μ, ν) =
      Rz x μ * Rz (x + unitStep 0 μ) ν * (Rz (x + unitStep 0 ν) μ)⁻¹ * (Rz x ν)⁻¹ := by
    have e1 : x + unitStep 0 μ + unitStep 0 ν - unitStep 0 μ = x + unitStep 0 ν := by abel
    have e2 : x + unitStep 0 μ + unitStep 0 ν + -unitStep 0 μ - unitStep 0 ν = x := by abel
    simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true, if_false,
      mul_one]
    rw [e1, e2]
    group
  simp only [linearizedCurl, hg, covariantDiff, hval]
  set r1 := Rz x μ
  set r2 := Rz (x + unitStep 0 μ) ν
  set r3 := Rz (x + unitStep 0 ν) μ
  set r4 := Rz x ν
  have c : x + unitStep 0 ν + unitStep 0 μ = x + unitStep 0 μ + unitStep 0 ν := add_right_comm _ _ _
  rw [c]
  have a1 : _root_.YangMills.Construction.BlockAverages.adjointAction (r1 * r2 * r3⁻¹) (_root_.YangMills.Construction.BlockAverages.adjointAction r3 (ξ (x + unitStep 0 μ + unitStep 0 ν))) =
      _root_.YangMills.Construction.BlockAverages.adjointAction r1 (_root_.YangMills.Construction.BlockAverages.adjointAction r2 (ξ (x + unitStep 0 μ + unitStep 0 ν))) := by
    rw [← PlaquetteLinearization.adjointAction_mul, ← PlaquetteLinearization.adjointAction_mul]
    simp
  have a2 : _root_.YangMills.Construction.BlockAverages.adjointAction (r1 * r2 * r3⁻¹ * r4⁻¹) (_root_.YangMills.Construction.BlockAverages.adjointAction r4 (ξ (x + unitStep 0 ν))) =
      _root_.YangMills.Construction.BlockAverages.adjointAction (r1 * r2 * r3⁻¹) (ξ (x + unitStep 0 ν)) := by
    rw [← PlaquetteLinearization.adjointAction_mul]
    simp
  simp only [PlaquetteLinearization.adjointAction_sub, a1, a2]
  abel
theorem eq_zero_of_mem_kernel (hodd : Odd F.blockSide) {V : F.GaugeField F.top} {s e Cm C₀ C₃ C₄ C₅ A : ℝ}
    (hs : 0 ≤ s) (he : 0 ≤ e) (hCm : 0 ≤ Cm) (hC₀ : 0 ≤ C₀) (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄) (hC₅ : 0 ≤ C₅)
    (hA : 0 ≤ A) (hf : GaugeSliceHypotheses S V s C₃ C₄ C₅) (σ β η : F.Site 0 → imaginaryQuaternions)
    (b : F.Cell → ℍ[ℝ]) (hβ : ∀ x, ((β x : imaginaryQuaternions) : ℍ[ℝ]) = cellBumpSection S V b x)
    (hη : ∀ x, ((η x : imaginaryQuaternions) : ℍ[ℝ]) = σ x + β x)
    (hσ : CellMeanFree S V (fun x => (σ x : ℍ[ℝ])))
    (Hf u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (hbond : ∀ c ∈ innerBonds S 0, ‖Hf c.1 c.2‖ ≤ C₀ * ‖u c.1 c.2‖ * (‖η c.1‖ + ‖η (c.1 + unitStep 0 c.2)‖))
    (hcurl : ∀ p ∈ innerPlaquettes S 0, ‖linearizedCurl (referenceFieldChain S V 0) Hf p‖ ≤
      C₀ * ((‖linearizedCurl (referenceFieldChain S V 0) u p‖ + plaquetteBondSum (fun x i => ‖u x i‖) p ^ 2) *
          plaquetteCornerSum (fun x => ‖η x‖) p +
        plaquetteBondSum (fun x i => ‖u x i‖) p *
          plaquetteBondSum (fun x i => ‖covariantDiff (referenceFieldChain S V 0) (fun x => η x) x i‖) p))
    (hu : ∀ z ∈ S, ∑ c ∈ bondsOver S {z} 0, ‖u c.1 c.2‖ ^ (4 : ℝ) ≤ A ^ (4 : ℝ))
    (hc : ∀ z ∈ S,
      finLpNorm (plaquettesOver S {z} 0) 2 (fun p => ‖linearizedCurl (referenceFieldChain S V 0) u p‖) ≤ A)
    (hgen : ∀ y ∈ S, ‖frameCellMean S V y (fun x => (η x : ℍ[ℝ]))‖ ≤
      Cm * e * (cellSiteNorm 4 S (fun _ => 1) (fun x => (η x : ℍ[ℝ])) y / (cellSideLength F : ℝ)))
    (hmap : ∀ x ∈ sitesOfCells S 0, gaugeMap S V (referenceFieldChain S V 0)
      (fun x i => - covariantDiff (referenceFieldChain S V 0) (fun x => η x) x i + Hf x i) x = 0)
    (hCe : Cm * e * C₅ ≤ 1 / 2) (hκ1 : 2 * (Cm * e * C₄) ≤ 1) (hs1 : s ≤ 1) (hA1 : A ≤ 1) (h1 : C₄ * s ≤ 1 / 8)
    (h2 : (C₃ * (C₅ * 2) + C₅) * (2 * (Cm * e * C₄)) ≤ 1 / 8)
    (h3 : (C₃ + 1) * (1356 * C₀ * A * (C₄ + C₅ + 1)) ≤ 1 / 8) :
    (∀ x ∈ sitesOfCells S 0, ((σ x : imaginaryQuaternions) : ℍ[ℝ]) = 0) ∧ ∀ y ∈ S, b y = 0 := by
  classical
  by_cases hS : S.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    subst hS
    refine ⟨fun x hx => ?_, fun y hy => by simp at hy⟩
    simp [sitesOfCells] at hx
  set R0 := referenceFieldChain S V 0 with hR0
  set Dσ := covariantDiff R0 (fun x => (σ x : ℍ[ℝ])) with hDσ
  set Dβ := covariantDiff R0 (fun x => (β x : ℍ[ℝ])) with hDβ
  set N : ℝ := (cellSideLength F : ℝ) with hNdef
  have hN1 : 1 ≤ N := one_le_cellSideLength hodd
  have hN0 : 0 < N := by linarith
  set Nq : ℝ := N ^ (1 / 3 : ℝ) with hNq
  have hNq0 : 0 < Nq := Real.rpow_pos_of_pos hN0 _
  have hNN : N ^ (2 / 3 : ℝ) * Nq = N := by
    rw [hNq, ← Real.rpow_add hN0]
    norm_num
  obtain ⟨z₀, hz₀, hmax⟩ := Finset.exists_max_image S (fun z => cellBondNorm 3 S (fun _ => 1) Dσ z) hS
  set T := cellBondNorm 3 S (fun _ => 1) Dσ z₀ with hT
  have nT : ∀ z, 0 ≤ cellBondNorm 3 S (fun _ => 1) Dσ z := fun z => by
    rw [cellBondNorm_eq_finLpNorm]
    exact finLpNorm_nonneg _ _ fun _ _ => norm_nonneg _
  have hT0 : 0 ≤ T := nT z₀
  obtain ⟨y₁, hy₁, hmaxb⟩ := Finset.exists_max_image S (fun y => ‖b y‖) hS
  set Bm := ‖b y₁‖ with hBm
  have hβfun : (fun x => ((β x : imaginaryQuaternions) : ℍ[ℝ])) = cellBumpSection S V b := funext hβ
  have stepA : ∀ y ∈ S, ‖b y‖ * Nq ≤ 2 * (Cm * e * C₄) * T := by
    intro y hy
    have e1 : frameCellMean S V y (fun x => (η x : ℍ[ℝ])) = b y := by
      have h := GaugeMapLinear.frameCellMean_linComb S V 1 1 y (fun x => (σ x : ℍ[ℝ])) (fun x => (β x : ℍ[ℝ]))
      simp only [one_smul] at h
      have e2 : (fun x => (η x : ℍ[ℝ])) = fun x => (σ x : ℍ[ℝ]) + (β x : ℍ[ℝ]) := funext hη
      rw [e2, h, hσ y hy, hβfun, hf.bump_mean b y hy, zero_add]
    have e3 : cellSiteNorm 4 S (fun _ => 1) (fun x => (η x : ℍ[ℝ])) y ≤
        cellSiteNorm 4 S (fun _ => 1) (fun x => (σ x : ℍ[ℝ])) y +
          cellSiteNorm 4 S (fun _ => 1) (cellBumpSection S V b) y := by
      rw [cellSiteNorm_eq_finLpNorm, cellSiteNorm_eq_finLpNorm, cellSiteNorm_eq_finLpNorm]
      have h := finLpNorm_add_le (sitesInCell S y) (p := 4) (by norm_num) (f := fun x => ‖(σ x : ℍ[ℝ])‖)
        (g := fun x => ‖cellBumpSection S V b x‖) (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
      refine (finLpNorm_mono _ (by norm_num) (fun _ _ => norm_nonneg _) fun x _ => ?_).trans h
      rw [hη, hβ]
      exact norm_add_le _ _
    have e4 : cellSiteNorm 4 S (fun _ => 1) (fun x => (σ x : ℍ[ℝ])) y ≤ C₄ * T * N ^ (2 / 3 : ℝ) := by
      rw [cellSiteNorm_eq_finLpNorm]
      refine (finLpNorm_four_le_twelve hodd y fun _ => norm_nonneg _).trans ?_
      rw [← cellSiteNorm_eq_finLpNorm]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact (hf.poincare _ hσ y hy).trans (mul_le_mul_of_nonneg_left (hmax y hy) hC₄)
    have e5 := hf.bump_lp4 b y hy
    have e6 := hgen y hy
    rw [e1] at e6
    have hsn : cellSiteNorm 4 S (fun _ => 1) (fun x => (η x : ℍ[ℝ])) y / N ≤
        C₄ * T * N ^ (2 / 3 : ℝ) / N + C₅ * ‖b y‖ := by
      have : cellSiteNorm 4 S (fun _ => 1) (fun x => (η x : ℍ[ℝ])) y ≤
          C₄ * T * N ^ (2 / 3 : ℝ) + C₅ * N * ‖b y‖ := by
        linarith
      calc _ ≤ (C₄ * T * N ^ (2 / 3 : ℝ) + C₅ * N * ‖b y‖) / N := div_le_div_of_nonneg_right this hN0.le
        _ = _ := by
          field_simp
    have hce : 0 ≤ Cm * e := by positivity
    have e7 : ‖b y‖ ≤ Cm * e * (C₄ * T * N ^ (2 / 3 : ℝ) / N) + (Cm * e * C₅) * ‖b y‖ := by
      have := mul_le_mul_of_nonneg_left hsn hce
      nlinarith
    have e8 : ‖b y‖ ≤ 2 * (Cm * e * (C₄ * T * N ^ (2 / 3 : ℝ) / N)) := by
      have := mul_le_mul_of_nonneg_right hCe (norm_nonneg (b y))
      linarith
    have e9 : (C₄ * T * N ^ (2 / 3 : ℝ) / N) * Nq = C₄ * T := by
      rw [div_mul_eq_mul_div, mul_assoc, hNN]
      field_simp
    calc ‖b y‖ * Nq ≤ (2 * (Cm * e * (C₄ * T * N ^ (2 / 3 : ℝ) / N))) * Nq :=
          mul_le_mul_of_nonneg_right e8 hNq0.le
      _ = 2 * (Cm * e * ((C₄ * T * N ^ (2 / 3 : ℝ) / N) * Nq)) := by ring
      _ = _ := by rw [e9]; ring
  set Q := Nq * Bm with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hQκ : Q ≤ 2 * (Cm * e * C₄) * T := by
    rw [hQ, mul_comm]
    exact stepA y₁ hy₁
  set Yb := C₄ * T + C₅ * Q with hYb
  set Tb := T + C₅ * Q with hTb
  have hYb0 : 0 ≤ Yb := by positivity
  have hTb0 : 0 ≤ Tb := by positivity
  have hbB : ∀ y ∈ S, ‖b y‖ ≤ Bm := hmaxb
  have hη12 : ∀ z ∈ S, ∑ x ∈ sitesInCell S z, ‖η x‖ ^ (12 : ℝ) ≤ Yb ^ (12 : ℝ) := by
    intro z hz
    have h1 : finLpNorm (sitesInCell S z) 12 (fun x => ‖η x‖) ≤ Yb := by
      have a1 := finLpNorm_add_le (sitesInCell S z) (p := 12) (by norm_num) (f := fun x => ‖(σ x : ℍ[ℝ])‖)
        (g := fun x => ‖cellBumpSection S V b x‖) (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
      have a2 : finLpNorm (sitesInCell S z) 12 (fun x => ‖η x‖) ≤
          finLpNorm (sitesInCell S z) 12 (fun x => ‖(σ x : ℍ[ℝ])‖ + ‖cellBumpSection S V b x‖) := by
        refine finLpNorm_mono _ (by norm_num) (fun _ _ => norm_nonneg _) fun x _ => ?_
        have e : ‖η x‖ = ‖((η x : imaginaryQuaternions) : ℍ[ℝ])‖ := rfl
        rw [e, hη, hβ]
        exact norm_add_le _ _
      have a3 : finLpNorm (sitesInCell S z) 12 (fun x => ‖(σ x : ℍ[ℝ])‖) ≤ C₄ * T := by
        rw [← cellSiteNorm_eq_finLpNorm]
        exact (hf.poincare _ hσ z hz).trans (mul_le_mul_of_nonneg_left (hmax z hz) hC₄)
      have a4 : finLpNorm (sitesInCell S z) 12 (fun x => ‖cellBumpSection S V b x‖) ≤ C₅ * Q := by
        rw [← cellSiteNorm_eq_finLpNorm]
        refine (hf.bump_lp12 b z hz).trans ?_
        rw [hQ, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hbB z hz) hNq0.le) hC₅
      linarith
    rw [sum_rpow_eq_finLpNorm_rpow _ (by norm_num) fun _ _ => norm_nonneg _]
    exact Real.rpow_le_rpow (finLpNorm_nonneg _ _ fun _ _ => norm_nonneg _) h1 (by norm_num)
  have hDsum : ∀ x i, covariantDiff R0 (fun x => (η x : ℍ[ℝ])) x i = Dσ x i + Dβ x i := by
    intro x i
    simp only [hDσ, hDβ, covariantDiff, hη, GaugeMapLinear.adjointAction_add]
    abel
  have hDβn : ∀ z ∈ S, finLpNorm (bondsOver S {z} 0) 3 (fun c => ‖Dβ c.1 c.2‖) ≤ C₅ * Q := by
    intro z hz
    rw [← cellBondNorm_eq_finLpNorm, hDβ, hβfun]
    refine (hf.bump_diff b Bm hbB z hz).trans (le_of_eq ?_)
    rw [hQ]
    ring
  have hDσn : ∀ z ∈ S, finLpNorm (bondsOver S {z} 0) 3 (fun c => ‖Dσ c.1 c.2‖) ≤ T := by
    intro z hz
    rw [← cellBondNorm_eq_finLpNorm]
    exact hmax z hz
  have hη3 : ∀ z ∈ S, ∑ c ∈ bondsOver S {z} 0,
      ‖covariantDiff R0 (fun x => (η x : ℍ[ℝ])) c.1 c.2‖ ^ (3 : ℝ) ≤ Tb ^ (3 : ℝ) := by
    intro z hz
    have h1 : finLpNorm (bondsOver S {z} 0) 3
        (fun c => ‖covariantDiff R0 (fun x => (η x : ℍ[ℝ])) c.1 c.2‖) ≤ Tb := by
      have a1 : finLpNorm (bondsOver S {z} 0) 3 (fun c => ‖covariantDiff R0 (fun x => (η x : ℍ[ℝ])) c.1 c.2‖) ≤
          finLpNorm (bondsOver S {z} 0) 3 (fun c => ‖Dσ c.1 c.2‖ + ‖Dβ c.1 c.2‖) := by
        refine finLpNorm_mono _ (by norm_num) (fun _ _ => norm_nonneg _) fun c _ => ?_
        rw [hDsum]
        exact norm_add_le _ _
      have a2 := finLpNorm_add_le (bondsOver S {z} 0) (p := 3) (by norm_num) (f := fun c => ‖Dσ c.1 c.2‖)
        (g := fun c => ‖Dβ c.1 c.2‖) (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
      have a3 := hDσn z hz
      have a4 := hDβn z hz
      linarith
    rw [sum_rpow_eq_finLpNorm_rpow _ (by norm_num) fun _ _ => norm_nonneg _]
    exact Real.rpow_le_rpow (finLpNorm_nonneg _ _ fun _ _ => norm_nonneg _) h1 (by norm_num)
  have hform := fun z hz =>
    finLpNorm_form_and_curl_le hodd hC₀ hA hYb0 hTb0 R0 u η Hf hbond hcurl hu hc hη12 hη3 z hz
  set g₁ : F.Site 0 → Fin 4 → imaginaryQuaternions := fun x i => pureComponentCLM (Dβ x i) with hg₁
  have hg₁e : ∀ x i, ((g₁ x i : imaginaryQuaternions) : ℍ[ℝ]) = Dβ x i := by
    intro x i
    rw [hg₁, coe_pureComponentCLM, _root_.YangMills.Construction.GaugeMotions.pureComponent_of_re_eq_zero]
    have h1 : ((β x : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := (β x).2
    have h2 : ((β (x + unitStep 0 i) : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := (β (x + unitStep 0 i)).2
    have e' : ∀ p q : ℍ[ℝ], (p - q).re = p.re - q.re := fun _ _ => rfl
    simp only [hDβ, covariantDiff, e', PlaquetteLinearization.adjointAction_re, h1, h2, sub_zero]
  have hB1 : ∀ z ∈ S, cellPlaquetteNorm (12 / 7) S (fun _ => 1) (linearizedCurl R0 g₁) z +
      cellBondNorm 3 S (fun _ => 1) (fun x i => g₁ x i) z ≤ C₅ * (1 + s) * Q := by
    intro z hz
    have e1 : linearizedCurl R0 g₁ = fun p => _root_.YangMills.Construction.BlockAverages.adjointAction (plaquetteHolonomy R0 p) (cellBumpSection S V b p.1) -
        cellBumpSection S V b p.1 := by
      funext p
      rw [linearizedCurl_of_covariantDiff R0 g₁ (cellBumpSection S V b) (fun x i => by rw [hg₁e, hDβ, hβfun]) p]
    have e2 : (fun x i => ((g₁ x i : imaginaryQuaternions) : ℍ[ℝ])) = Dβ := funext fun x => funext fun i => hg₁e x i
    rw [e1, e2]
    have a1 := hf.bump_curl b Bm hbB z hz
    have a2 := hDβn z hz
    rw [← cellBondNorm_eq_finLpNorm] at a2
    have e3 : C₅ * s * N ^ (1 / 3 : ℝ) * Bm = C₅ * s * Q := by rw [hQ]; ring
    rw [e3] at a1
    have e4 : C₅ * (1 + s) * Q = C₅ * s * Q + C₅ * Q := by ring
    rw [e4]
    linarith
  set V₀ := C₀ * (A * (4 * Yb)) with hV₀
  set W₀ := C₀ * (A * (8 * Yb) + (12 * A) * ((12 * A) * (8 * Yb)) + (12 * A) * (16 * Tb)) with hW₀
  have hB2 : ∀ z ∈ S, cellPlaquetteNorm (12 / 7) S (fun _ => 1) (linearizedCurl R0 Hf) z +
      cellBondNorm 3 S (fun _ => 1) (fun x i => Hf x i) z ≤ V₀ + W₀ := by
    intro z hz
    rw [cellPlaquetteNorm_eq_finLpNorm, cellBondNorm_eq_finLpNorm]
    obtain ⟨a1, a2⟩ := hform z hz
    have a3 : finLpNorm (bondsOver S {z} 0) 3 (fun c => ‖((Hf c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖) ≤ V₀ := a1
    exact (add_le_add a2 a3).trans (le_of_eq (add_comm _ _))
  have hf1 := hf.gaugeDiff_bound g₁ _ hB1
  have hf2 := hf.gaugeDiff_bound Hf _ hB2
  have hr := hf.remainder_bound _ hσ T (fun z hz => hmax z hz)
  set rest := gaugeRemainder S V (fun x => (σ x : ℍ[ℝ])) with hrest
  set Λ₁ := gaugeMap S V R0 (fun x i => (g₁ x i : ℍ[ℝ])) with hΛ₁
  set Λ₂ := gaugeMap S V R0 (fun x i => (Hf x i : ℍ[ℝ])) with hΛ₂
  have hsec : ∀ x ∈ sitesOfCells S 0, ((σ x : imaginaryQuaternions) : ℍ[ℝ]) = rest x + Λ₁ x - Λ₂ x := by
    intro x hx
    have e0 := hmap x hx
    have e1 : (fun x i => - covariantDiff R0 (fun x => (η x : ℍ[ℝ])) x i + (Hf x i : ℍ[ℝ])) =
        fun x i => (-1 : ℝ) • ((1 : ℝ) • Dσ x i + (1 : ℝ) • (g₁ x i : ℍ[ℝ])) + (1 : ℝ) • (Hf x i : ℍ[ℝ]) := by
      funext y i
      rw [hDsum, hg₁e]
      simp
      abel
    rw [e1] at e0
    have h1 := GaugeMapLinear.gaugeMap_linComb S V R0 (-1) 1
      (fun x i => (1 : ℝ) • Dσ x i + (1 : ℝ) • (g₁ x i : ℍ[ℝ])) (fun x i => (Hf x i : ℍ[ℝ]))
    have h2 := GaugeMapLinear.gaugeMap_linComb S V R0 1 1 Dσ (fun x i => (g₁ x i : ℍ[ℝ]))
    rw [h1] at e0
    simp only [h2] at e0
    have e2 : rest x = gaugeMap S V R0 Dσ x + (σ x : ℍ[ℝ]) := rfl
    simp only [one_smul] at e0
    rw [e2, hΛ₁, hΛ₂]
    have e3 : gaugeMap S V R0 Dσ x = - gaugeMap S V R0 (fun x i => (g₁ x i : ℍ[ℝ])) x +
        gaugeMap S V R0 (fun x i => (Hf x i : ℍ[ℝ])) x := by
      have : (-1 : ℝ) • (gaugeMap S V R0 Dσ x + gaugeMap S V R0 (fun x i => (g₁ x i : ℍ[ℝ])) x) +
          gaugeMap S V R0 (fun x i => (Hf x i : ℍ[ℝ])) x = 0 := e0
      rw [neg_one_smul] at this
      have h3 : gaugeMap S V R0 Dσ x - (- gaugeMap S V R0 (fun x i => (g₁ x i : ℍ[ℝ])) x +
          gaugeMap S V R0 (fun x i => (Hf x i : ℍ[ℝ])) x) =
          - (-(gaugeMap S V R0 Dσ x + gaugeMap S V R0 (fun x i => (g₁ x i : ℍ[ℝ])) x) +
            gaugeMap S V R0 (fun x i => (Hf x i : ℍ[ℝ])) x) := by abel
      rw [this, neg_zero] at h3
      exact sub_eq_zero.1 h3
    rw [e3]
    abel
  have hbondeq : ∀ c ∈ innerBonds S 0, Dσ c.1 c.2 = covariantDiff R0 rest c.1 c.2 +
      (formPlusGaugeDiff S V g₁ c.1 c.2 - (g₁ c.1 c.2 : ℍ[ℝ])) -
      (formPlusGaugeDiff S V Hf c.1 c.2 - (Hf c.1 c.2 : ℍ[ℝ])) := by
    intro c hc'
    have hx := (ChartCoordinates.innerBonds_ends hc').1
    have hx' := (ChartCoordinates.innerBonds_ends hc').2
    simp only [formPlusGaugeDiff, add_sub_cancel_left, covariantDiff, ← hR0, hDσ]
    rw [hsec _ hx, hsec _ hx', ← hΛ₁, ← hΛ₂]
    simp only [GaugeMapLinear.adjointAction_add, GaugeMapLinear.adjointAction_sub]
    abel
  have hTle : T ≤ C₄ * s * T + C₃ * (C₅ * (1 + s) * Q) + C₅ * Q + C₃ * (V₀ + W₀) + V₀ := by
    have n1 := hr z₀ hz₀
    have n2 := hf1 z₀ hz₀
    have n3 := hf2 z₀ hz₀
    rw [cellBondNorm_eq_finLpNorm] at n1 n2 n3
    have n4 := hDβn z₀ hz₀
    have n5 := (hform z₀ hz₀).1
    set B₀ := bondsOver S {z₀} 0 with hB₀
    have hpt : finLpNorm B₀ 3 (fun c => ‖Dσ c.1 c.2‖) ≤
        finLpNorm B₀ 3 (fun c => ‖covariantDiff R0 rest c.1 c.2‖ + ‖formPlusGaugeDiff S V g₁ c.1 c.2‖ +
          ‖Dβ c.1 c.2‖ + (‖formPlusGaugeDiff S V Hf c.1 c.2‖ + ‖Hf c.1 c.2‖)) := by
      refine finLpNorm_mono _ (by norm_num) (fun _ _ => norm_nonneg _) fun c hc' => ?_
      rw [hbondeq c (mem_bondsOver_singleton z₀ c hc').1]
      have t1 := norm_sub_le
        (covariantDiff R0 rest c.1 c.2 + (formPlusGaugeDiff S V g₁ c.1 c.2 - (g₁ c.1 c.2 : ℍ[ℝ])))
        (formPlusGaugeDiff S V Hf c.1 c.2 - (Hf c.1 c.2 : ℍ[ℝ]))
      have t2 := norm_add_le (covariantDiff R0 rest c.1 c.2)
        (formPlusGaugeDiff S V g₁ c.1 c.2 - (g₁ c.1 c.2 : ℍ[ℝ]))
      have t3 := norm_sub_le (formPlusGaugeDiff S V g₁ c.1 c.2) (g₁ c.1 c.2 : ℍ[ℝ])
      have t4 := norm_sub_le (formPlusGaugeDiff S V Hf c.1 c.2) (Hf c.1 c.2 : ℍ[ℝ])
      have t6 : ‖((g₁ c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖Dβ c.1 c.2‖ := by rw [hg₁e]
      have t5 : ‖((Hf c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖Hf c.1 c.2‖ := rfl
      linarith
    have hsum : finLpNorm B₀ 3 (fun c => ‖covariantDiff R0 rest c.1 c.2‖ + ‖formPlusGaugeDiff S V g₁ c.1 c.2‖ +
          ‖Dβ c.1 c.2‖ + (‖formPlusGaugeDiff S V Hf c.1 c.2‖ + ‖Hf c.1 c.2‖)) ≤
        finLpNorm B₀ 3 (fun c => ‖covariantDiff R0 rest c.1 c.2‖) +
        finLpNorm B₀ 3 (fun c => ‖formPlusGaugeDiff S V g₁ c.1 c.2‖) + finLpNorm B₀ 3 (fun c => ‖Dβ c.1 c.2‖) +
        finLpNorm B₀ 3 (fun c => ‖formPlusGaugeDiff S V Hf c.1 c.2‖ + ‖Hf c.1 c.2‖) :=
      finLpNorm_add_add_add_le (p := 3) (by norm_num) (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
        (fun _ _ => norm_nonneg _) (fun _ _ => by positivity)
    have hsum2 : finLpNorm B₀ 3 (fun c => ‖formPlusGaugeDiff S V Hf c.1 c.2‖ + ‖Hf c.1 c.2‖) ≤
        finLpNorm B₀ 3 (fun c => ‖formPlusGaugeDiff S V Hf c.1 c.2‖) + finLpNorm B₀ 3 (fun c => ‖Hf c.1 c.2‖) :=
      finLpNorm_add_le B₀ (by norm_num) (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
    have hTe : T ≤ finLpNorm B₀ 3 (fun c => ‖Dσ c.1 c.2‖) := le_of_eq (by rw [hT, cellBondNorm_eq_finLpNorm])
    linarith
  have hTz : T = 0 :=
    eq_zero_of_le_self_bound hT0 hQ0 (by positivity) hs hA hC₀ hC₃ hC₄ hC₅ hQκ hκ1 hs1 hA1 h1 h2 h3 hYb hTb hTle
  constructor
  · intro x hx
    have hz : enclosingCell x ∈ S := GaugeMapLinear.enclosingCell_mem S hodd x hx
    have h1 := (hf.poincare _ hσ _ hz).trans (mul_le_mul_of_nonneg_left (hmax _ hz) hC₄)
    rw [hTz, mul_zero, cellSiteNorm_eq_finLpNorm] at h1
    set lp := finLpNorm (sitesInCell S (enclosingCell x)) 12
      (fun x => ‖((σ x : imaginaryQuaternions) : ℍ[ℝ])‖) with hlp
    have h0 : 0 ≤ lp := finLpNorm_nonneg _ _ fun _ _ => norm_nonneg _
    have hl : lp = 0 := le_antisymm h1 h0
    have hsum := sum_rpow_eq_finLpNorm_rpow (sitesInCell S (enclosingCell x)) (p := 12) (by norm_num)
      (f := fun x => ‖((σ x : imaginaryQuaternions) : ℍ[ℝ])‖) (fun _ _ => norm_nonneg _)
    rw [← hlp, hl, Real.zero_rpow (by norm_num)] at hsum
    have hmem : x ∈ sitesInCell S (enclosingCell x) := Finset.mem_filter.2 ⟨hx, rfl⟩
    have hle := Finset.single_le_sum (f := fun x => ‖((σ x : imaginaryQuaternions) : ℍ[ℝ])‖ ^ (12 : ℝ))
      (fun x _ => Real.rpow_nonneg (norm_nonneg _) _) hmem
    simp only [hsum] at hle
    have hz0 : ‖((σ x : imaginaryQuaternions) : ℍ[ℝ])‖ ^ (12 : ℝ) = 0 :=
      le_antisymm hle (Real.rpow_nonneg (norm_nonneg _) _)
    have := (Real.rpow_eq_zero (norm_nonneg _) (by norm_num)).1 hz0
    exact norm_eq_zero.1 this
  · intro y hy
    have h1 := stepA y hy
    rw [hTz, mul_zero] at h1
    have h2 : ‖b y‖ * Nq = 0 := le_antisymm h1 (by positivity)
    have h3 : ‖b y‖ = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · exact h
      · exact absurd h hNq0.ne'
    exact norm_eq_zero.1 h3
end YangMills.Construction.GaugeDirectionKernel
end
