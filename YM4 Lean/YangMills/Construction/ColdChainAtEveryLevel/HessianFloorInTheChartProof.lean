import YangMills.Construction.ColdChainAtEveryLevel.FloorOfTheChartForm
import YangMills.Construction.ColdChainAtEveryLevel.HessianFloorInTheChart
import YangMills.Construction.ColdChainAtEveryLevel.SecondVariationOfAFitInTheChart
import YangMills.Construction.ColdChainAtEveryLevel.SecondVariationOfTheActionInTheChart
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.BlockAverages
namespace HessianLowerBound
variable {F : BlockFrame}
theorem deriv_deriv_add_const_mul_sum {ι : Type} (s : Finset ι) (A : ℝ → ℝ) (f : ι → ℝ → ℝ) (a : ℝ)
    (hA : AnalyticAt ℝ A 0) (hf : ∀ c ∈ s, AnalyticAt ℝ (f c) 0) :
    deriv (deriv fun τ => A τ + a * ∑ c ∈ s, f c τ) 0 =
      deriv (deriv A) 0 + a * ∑ c ∈ s, deriv (deriv (f c)) 0 := by
  have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), AnalyticAt ℝ A τ ∧ ∀ c ∈ s, AnalyticAt ℝ (f c) τ :=
    hA.eventually_analyticAt.and ((Finset.eventually_all s).2 fun c hc => (hf c hc).eventually_analyticAt)
  have h1 : deriv (fun τ => A τ + a * ∑ c ∈ s, f c τ) =ᶠ[𝓝 0]
      fun τ => deriv A τ + a * ∑ c ∈ s, deriv (f c) τ := by
    filter_upwards [hev] with τ hτ
    have d1 : DifferentiableAt ℝ A τ := hτ.1.differentiableAt
    have d2 : ∀ c ∈ s, DifferentiableAt ℝ (f c) τ := fun c hc => (hτ.2 c hc).differentiableAt
    have e2 : HasDerivAt (fun τ => ∑ c ∈ s, f c τ) (∑ c ∈ s, deriv (f c) τ) τ :=
      HasDerivAt.fun_sum fun c hc => (d2 c hc).hasDerivAt
    exact (d1.hasDerivAt.add (e2.const_mul a)).deriv
  rw [h1.deriv_eq]
  have d1 : DifferentiableAt ℝ (deriv A) 0 := hA.deriv.differentiableAt
  have d2 : ∀ c ∈ s, DifferentiableAt ℝ (deriv (f c)) 0 := fun c hc => (hf c hc).deriv.differentiableAt
  have e2 : HasDerivAt (fun τ => ∑ c ∈ s, deriv (f c) τ) (∑ c ∈ s, deriv (deriv (f c)) 0) 0 :=
    HasDerivAt.fun_sum fun c hc => (d2 c hc).hasDerivAt
  exact (d1.hasDerivAt.add (e2.const_mul a)).deriv
theorem sum_chordSqNormOnPair_le (S : Finset F.Cell) (dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) :
    ∑ c ∈ innerBonds S F.top, chordSqNormOnPair S c.1 (c.1 + unitStep F.top c.2) dw ≤ 8 * chordSqNorm S dw := by
  classical
  have hcount : ∀ y : F.Cell, ((innerBonds S F.top).filter
      (fun c => y = c.1 ∨ y = c.1 + unitStep F.top c.2)).card ≤ 8 := by
    intro y
    have hsub : (innerBonds S F.top).filter (fun c => y = c.1 ∨ y = c.1 + unitStep F.top c.2) ⊆
        Finset.univ.image (fun i : Fin 4 => (y, i)) ∪
          Finset.univ.image (fun i : Fin 4 => (y - unitStep F.top i, i)) := by
      rintro ⟨q, i⟩ hc
      obtain ⟨-, h | h⟩ := Finset.mem_filter.1 hc
      · refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, ?_⟩)
        simp only at h
        rw [h]
      · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, ?_⟩)
        simp only at h
        rw [h]
        simp
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    have h1 : (Finset.univ.image (fun i : Fin 4 => (y, i))).card ≤ 4 := by
      simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin 4))) (f := fun i : Fin 4 => (y, i))
    have h2 : (Finset.univ.image (fun i : Fin 4 => (y - unitStep F.top i, i))).card ≤ 4 := by
      simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin 4)))
        (f := fun i : Fin 4 => (y - unitStep F.top i, i))
    omega
  unfold chordSqNormOnPair chordSqNorm
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have h0 : 0 ≤ ‖dw b.1 b.2‖ ^ 2 := by positivity
  have h1 : (((innerBonds S F.top).filter
      (fun c => enclosingCell b.1 = c.1 ∨ enclosingCell b.1 = c.1 + unitStep F.top c.2)).card : ℝ) ≤ 8 := by
    exact_mod_cast hcount (enclosingCell b.1)
  exact mul_le_mul_of_nonneg_right h1 h0
end HessianLowerBound
theorem hessianLowerBound_of_secondVariations (hA : chartActionSecondVariationStatement)
    (hFit : chartFitSecondVariationStatement) (hQ : chartFormFloorStatement) :
    hessianLowerBoundStatement := by
  intro a ha
  obtain ⟨ca, hca, L₁, hA'⟩ := hA a ha
  refine ⟨max L₁ 5, fun L hL hge => ?_⟩
  have g1 : L₁ ≤ L := le_of_max_le_left hge
  have g2 : 5 ≤ L := le_of_max_le_right hge
  obtain ⟨C1, ρ1, σ1, hC1, hρ1, hσ1, h1⟩ := hA' L hL g1
  obtain ⟨C2, ρ2, σ2, hC2, hρ2, hσ2, h2⟩ := hFit L hL g2
  obtain ⟨lam2, C3, ρ3, σ3, hlam2, hC3, hρ3, hσ3, h3⟩ := hQ L hL g2
  set A0 : ℝ := min ca a with hA0
  have hA0pos : 0 < A0 := lt_min hca ha
  set K : ℝ := A0 * C3 + C1 + 8 * a * C2 with hK
  have hKpos : 0 < K := by positivity
  set t : ℝ := min (min ρ1 (min ρ2 ρ3)) (min (min σ1 (min σ2 σ3)) (A0 * lam2 / (4 * K))) with ht
  have htpos : 0 < t := lt_min (lt_min hρ1 (lt_min hρ2 hρ3))
    (lt_min (lt_min hσ1 (lt_min hσ2 hσ3)) (by positivity))
  have t1 : t ≤ ρ1 := (min_le_left _ _).trans (min_le_left _ _)
  have t2 : t ≤ ρ2 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have t3 : t ≤ ρ3 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have u1 : t ≤ σ1 := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have u2 : t ≤ σ2 := (min_le_right _ _).trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have u3 : t ≤ σ3 := (min_le_right _ _).trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have u4 : t ≤ A0 * lam2 / (4 * K) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨A0 * lam2 / 2, t, t, by positivity, htpos, htpos, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hst hcold w dw hw hdw hwb hcw
  have hV : IsCold S F.top t V := fun p hp => (hcold p hp).trans_le hst
  obtain ⟨an1, b1⟩ := h1 F m S hFL hamb hm hreg t t V w dw htpos t1 htpos u1 hV hw hdw hwb hcw
  have f2 := h2 F m S hFL hamb hm hreg t t V w dw htpos t2 htpos u2 hV hw hdw hwb hcw
  have b3 := h3 F m S hFL hamb hm hreg t t V w dw htpos t3 htpos u3 hV hw hdw hwb hcw
  have hE : deriv (deriv fun τ : ℝ =>
        blockEnergy a S F.depth (chartedField (fun x i => w x i + τ • dw x i) V) V) 0 =
      deriv (deriv fun τ : ℝ => minimalAction a S F.depth (chartedField (chartLineShift w dw τ) V)) 0 +
        a * ∑ c ∈ innerBonds S (F.depth + 1),
          deriv (deriv fun τ : ℝ => blockFit (chartedField (chartLineShift w dw τ) V) V c) 0 :=
    HessianLowerBound.deriv_deriv_add_const_mul_sum (innerBonds S (F.depth + 1)) _
      (fun c τ => blockFit (chartedField (chartLineShift w dw τ) V) V c) a an1 (fun c hc => (f2 c hc).1)
  rw [hE]
  set Q : ℝ := chordSqNorm S dw with hQdef
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun _ _ => by positivity
  set Pc : ℝ := ∑ p ∈ innerPlaquettes S F.depth, ‖variationCurl (chartedField w V) dw p‖ ^ 2 with hPc
  set Cc : ℝ := ∑ c ∈ innerBonds S F.top, ‖bondContourVariation (chartedField w V) dw c‖ ^ 2 with hCc
  have hPc0 : 0 ≤ Pc := Finset.sum_nonneg fun _ _ => by positivity
  have hCc0 : 0 ≤ Cc := Finset.sum_nonneg fun _ _ => by positivity
  have sum2 : Cc - C2 * (t + t) * (8 * Q) ≤
      ∑ c ∈ innerBonds S (F.depth + 1),
        deriv (deriv fun τ : ℝ => blockFit (chartedField (chartLineShift w dw τ) V) V c) 0 := by
    have e1 : Cc - C2 * (t + t) * ∑ c ∈ innerBonds S F.top,
          chordSqNormOnPair S c.1 (c.1 + unitStep F.top c.2) dw ≤
        ∑ c ∈ innerBonds S (F.depth + 1),
          deriv (deriv fun τ : ℝ => blockFit (chartedField (chartLineShift w dw τ) V) V c) 0 := by
      rw [hCc, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum fun c hc => (f2 c hc).2
    have e2 := HessianLowerBound.sum_chordSqNormOnPair_le S dw
    have e3 : C2 * (t + t) * ∑ c ∈ innerBonds S F.top,
          chordSqNormOnPair S c.1 (c.1 + unitStep F.top c.2) dw ≤
        C2 * (t + t) * (8 * Q) := mul_le_mul_of_nonneg_left e2 (by positivity)
    linarith
  have hsplit : A0 * (Pc + Cc) ≤ ca * Pc + a * Cc := by
    have e1 : A0 * Pc ≤ ca * Pc := mul_le_mul_of_nonneg_right (min_le_left _ _) hPc0
    have e2 : A0 * Cc ≤ a * Cc := mul_le_mul_of_nonneg_right (min_le_right _ _) hCc0
    linarith
  have hlow : A0 * (lam2 * Q - C3 * (t + t) * Q) ≤ A0 * (Pc + Cc) :=
    mul_le_mul_of_nonneg_left (by linarith) hA0pos.le
  have ha2 := mul_le_mul_of_nonneg_left sum2 ha.le
  have hsmall : 2 * t * K ≤ A0 * lam2 / 2 := by
    have := u4
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have hfin : (A0 * lam2 / 2) * Q ≤ A0 * lam2 * Q - 2 * t * K * Q := by
    have := mul_le_mul_of_nonneg_right hsmall hQ0
    nlinarith
  have hK2 : 2 * t * K * Q =
      A0 * (C3 * (t + t) * Q) + C1 * (t + t) * Q + a * (C2 * (t + t) * (8 * Q)) := by
    rw [hK]
    ring
  have eQ : ∑ b ∈ chordBonds S, ‖dw b.1 b.2‖ ^ 2 = Q := rfl
  rw [eQ]
  linarith
end YangMills.Construction.BlockAverages
end
