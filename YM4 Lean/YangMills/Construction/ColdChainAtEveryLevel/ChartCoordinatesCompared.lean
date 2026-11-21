import YangMills.Construction.ColdChainAtEveryLevel.ChartOnComplexLines
import YangMills.Construction.ColdChainAtEveryLevel.ComparisonOfBoundedMaps
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
open Metric
namespace YangMills.Construction.ChartCoordinateComparison
open BlockAverages ComplexLineChart Analytic ComplexifiedQuaternions
variable {F : BlockFrame} {m : ℕ}
abbrev ComparisonSlot (m : ℕ) : Type := Option (Fin m ⊕ Fin m)
def slotFn {α : Type} (x : α) (a b : Fin m → α) : ComparisonSlot m → α
  | none => x
  | some (Sum.inl l) => a l
  | some (Sum.inr l) => b l
theorem sum_slotFn {M : Type} [AddCommMonoid M] (x : M) (a b : Fin m → M) :
    ∑ i, slotFn x a b i = x + (∑ l, a l + ∑ l, b l) := by
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  rfl
def linePoint (p : ℝ) (a b : Fin m → ℝ) (T : Fin m → ℝ) : ComparisonSlot m → ℝ :=
  slotFn p (fun l => a l * T l) (fun l => b l * T l)
def linePointCLM (a b : Fin m → ℝ) : (Fin m → ℂ) →L[ℂ] (ComparisonSlot m → ℂ) :=
  ContinuousLinearMap.pi (slotFn 0 (fun l => (a l : ℂ) • ContinuousLinearMap.proj l)
    (fun l => (b l : ℂ) • ContinuousLinearMap.proj l))
theorem complexifyCLM_linePoint (p : ℝ) (a b T : Fin m → ℝ) :
    complexifyCLM (linePoint p a b T) = complexifyCLM (linePoint p 0 0 0) + linePointCLM a b (complexifyCLM T) := by
  funext i
  rcases i with _ | l | l
  · simp [linePoint, slotFn, linePointCLM, complexifyCLM_apply]
  · simp [linePoint, slotFn, linePointCLM, complexifyCLM_apply]
  · simp [linePoint, slotFn, linePointCLM, complexifyCLM_apply]
theorem continuous_linePoint (p : ℝ) (a b : Fin m → ℝ) : Continuous (linePoint p a b) := by
  refine continuous_pi fun i => ?_
  rcases i with _ | l | l
  · exact continuous_const
  · exact continuous_const.mul (continuous_apply l)
  · exact continuous_const.mul (continuous_apply l)
theorem linePoint_zero (p : ℝ) (a b : Fin m → ℝ) : linePoint p a b 0 = linePoint p 0 0 0 := by
  funext i
  rcases i with _ | l | l <;> simp [linePoint, slotFn]
theorem norm_linePoint_le {p : ℝ} (hp : 0 ≤ p) : ‖linePoint (m := m) p 0 0 0‖ ≤ p := by
  refine (pi_norm_le_iff_of_nonneg hp).2 fun i => ?_
  rcases i with _ | l | l
  · simp [linePoint, slotFn, abs_of_nonneg hp]
  · simpa [linePoint, slotFn] using hp
  · simpa [linePoint, slotFn] using hp
theorem norm_linePointCLM_single_le {a b : Fin m → ℝ} (ha : ∀ l, 0 ≤ a l) (hb : ∀ l, 0 ≤ b l) (l : Fin m) :
    ‖linePointCLM a b (complexifyCLM (Pi.single l 1 : Fin m → ℝ))‖ ≤ max (a l) (b l) := by
  have h0 : 0 ≤ max (a l) (b l) := le_max_of_le_left (ha l)
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
  rcases i with _ | l' | l'
  · simpa [linePointCLM, slotFn] using h0
  · by_cases h : l' = l
    · subst h
      simp [linePointCLM, slotFn, complexifyCLM_apply, abs_of_nonneg (ha l')]
    · simpa [linePointCLM, slotFn, complexifyCLM_apply, h] using h0
  · by_cases h : l' = l
    · subst h
      simp [linePointCLM, slotFn, complexifyCLM_apply, abs_of_nonneg (hb l')]
    · simpa [linePointCLM, slotFn, complexifyCLM_apply, h] using h0
theorem norm_linePointCLM_single_sub_le {a b : Fin m → ℝ} (hb : ∀ l, 0 ≤ b l) (l : Fin m) :
    ‖linePointCLM a b (complexifyCLM (Pi.single l 1 : Fin m → ℝ)) -
        linePointCLM a 0 (complexifyCLM (Pi.single l 1 : Fin m → ℝ))‖ ≤ b l := by
  refine (pi_norm_le_iff_of_nonneg (hb l)).2 fun i => ?_
  rcases i with _ | l' | l'
  · simpa [linePointCLM, slotFn] using hb l
  · simpa [linePointCLM, slotFn] using hb l
  · by_cases h : l' = l
    · subst h
      simp [linePointCLM, slotFn, complexifyCLM_apply, abs_of_nonneg (hb l')]
    · simpa [linePointCLM, slotFn, complexifyCLM_apply, h] using hb l
theorem norm_iteratedFDeriv_sub_le_of_extension {f : (ComparisonSlot m → ℝ) → imaginaryQuaternions}
    {g : (ComparisonSlot m → ℂ) → ComplexQuat} {ρ : ℝ}
    (h : IsBoundedHolomorphicExtension imagToComplexCLM f g ρ 1)
    (P : ComplexQuat →L[ℝ] imaginaryQuaternions) (hP : ∀ a, P (imagToComplexCLM a) = a)
    {p : ℝ} (hp0 : 0 ≤ p) (hpρ : p ≤ ρ / 4) {a b : Fin m → ℝ} (ha : ∀ l, 0 ≤ a l) (hb : ∀ l, 0 ≤ b l)
    {Ψ₀ Ψ₁ : (Fin m → ℝ) → imaginaryQuaternions} (h₀ : ∀ T, Ψ₀ T = f (linePoint 0 a 0 T))
    (h₁ : ∀ T, Ψ₁ T = f (linePoint p a b T)) :
    ‖iteratedFDeriv ℝ m Ψ₀ 0 (fun l => Pi.single l 1) - iteratedFDeriv ℝ m Ψ₁ 0 (fun l => Pi.single l 1)‖ ≤
      cauchyEstimateBound 1 ρ (m + 1) * (∏ l, a l) * p +
        cauchyEstimateBound 1 ρ m * ∑ l, b l * ∏ l' ∈ Finset.univ.erase l, max (a l') (b l') := by
  have hρ := h.radius_pos
  have key : ∀ (p' : ℝ) (a' b' : Fin m → ℝ) (Ψ : (Fin m → ℝ) → imaginaryQuaternions),
      ‖linePoint (m := m) p' 0 0 0‖ < ρ →
      (∀ T, Ψ T = f (linePoint p' a' b' T)) →
        imagToComplexCLM (iteratedFDeriv ℝ m Ψ 0 (fun l => Pi.single l 1)) =
        iteratedFDeriv ℂ m g (complexifyCLM (linePoint (m := m) p' 0 0 0))
          (fun l => linePointCLM a' b' (complexifyCLM (Pi.single l 1 : Fin m → ℝ))) := by
    intro p' a' b' Ψ hlt hΨ
    set c := complexifyCLM (linePoint (m := m) p' 0 0 0) with hc
    have hcn : ‖c‖ < ρ := by rw [hc, norm_complexifyCLM]; exact hlt
    have hcb : c ∈ ball (0 : ComparisonSlot m → ℂ) ρ := by simpa using hcn
    have hG : AnalyticAt ℂ (fun T => g (c + linePointCLM a' b' T)) 0 := by
      have h1 : AnalyticAt ℂ g (c + linePointCLM a' b' 0) := by
        rw [map_zero, add_zero]
        exact h.analyticOnNhd c hcb
      exact AnalyticAt.fun_comp h1 (analyticAt_const.add ((linePointCLM a' b').analyticAt 0))
    have hev : ∀ᶠ T in nhds (0 : Fin m → ℝ),
        imagToComplexCLM (Ψ T) = (fun T => g (c + linePointCLM a' b' T)) (complexifyCLM T) := by
      have hcont : Filter.Tendsto (linePoint p' a' b') (nhds 0) (nhds (linePoint p' 0 0 0)) := by
        have := (continuous_linePoint p' a' b').tendsto 0
        rwa [linePoint_zero] at this
      have hball : ball (0 : ComparisonSlot m → ℝ) ρ ∈ nhds (linePoint (m := m) p' 0 0 0) :=
        isOpen_ball.mem_nhds (by simpa using hlt)
      filter_upwards [hcont hball] with T hT
      have hT' : ‖linePoint p' a' b' T‖ < ρ := by simpa using hT
      rw [hΨ, h.agrees_real _ hT', complexifyCLM_linePoint]
    rw [iteratedFDeriv_real_eq_complex_of_extension imagToComplexCLM P hP hG hev]
    exact iteratedFDeriv_comp_affine_zero_apply h.analyticOnNhd hcn (linePointCLM a' b') m _
  have hρ4 : p < ρ := by linarith
  have hn0 : ‖linePoint (m := m) 0 0 0 0‖ < ρ := (norm_linePoint_le le_rfl).trans_lt hρ
  have hn1 : ‖linePoint (m := m) p 0 0 0‖ < ρ := (norm_linePoint_le hp0).trans_lt hρ4
  have k₀ := key 0 a 0 Ψ₀ hn0 h₀
  have k₁ := key p a b Ψ₁ hn1 h₁
  have hz : complexifyCLM (linePoint (m := m) 0 0 0 0) = 0 := by
    funext i
    rcases i with _ | l | l <;> simp [linePoint, slotFn, complexifyCLM_apply]
  rw [hz] at k₀
  set u : Fin m → (ComparisonSlot m → ℂ) :=
    fun l => linePointCLM a 0 (complexifyCLM (Pi.single l 1 : Fin m → ℝ)) with hu
  set v : Fin m → (ComparisonSlot m → ℂ) :=
    fun l => linePointCLM a b (complexifyCLM (Pi.single l 1 : Fin m → ℝ)) with hv
  set x := complexifyCLM (linePoint (m := m) p 0 0 0) with hx
  have hxn : ‖x‖ ≤ p := by
    rw [hx, norm_complexifyCLM]
    exact norm_linePoint_le hp0
  have hm := norm_iteratedFDeriv_apply_sub_zero_apply_le m hρ zero_le_one h.analyticOnNhd h.norm_le
    (x := x) (by linarith) u v
  have hun : ∀ l, ‖u l‖ ≤ a l := fun l => by
    have := norm_linePointCLM_single_le (a := a) (b := 0) ha (fun _ => le_rfl) l
    simp only [Pi.zero_apply] at this
    exact this.trans (max_le le_rfl (ha l))
  have hvn : ∀ l, ‖v l‖ ≤ max (a l) (b l) := fun l => norm_linePointCLM_single_le ha hb l
  have hvu : ∀ l, ‖v l - u l‖ ≤ b l := fun l => norm_linePointCLM_single_sub_le hb l
  have hC1 := cauchyEstimateBound_nonneg (M := 1) zero_le_one hρ (m + 1)
  have hC0 := cauchyEstimateBound_nonneg (M := 1) zero_le_one hρ m
  have hprod : ∏ l, ‖u l‖ ≤ ∏ l, a l :=
    Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun l _ => hun l
  have hsum : ∑ l, ‖v l - u l‖ * ∏ l' ∈ Finset.univ.erase l, max ‖v l'‖ ‖u l'‖ ≤
      ∑ l, b l * ∏ l' ∈ Finset.univ.erase l, max (a l') (b l') := by
    refine Finset.sum_le_sum fun l _ => mul_le_mul (hvu l) ?_
      (Finset.prod_nonneg fun _ _ => by positivity) (hb l)
    exact Finset.prod_le_prod (fun _ _ => by positivity) fun l' _ =>
      max_le (hvn l') ((hun l').trans (le_max_left _ _))
  have hfin : ‖iteratedFDeriv ℂ m g x v - iteratedFDeriv ℂ m g 0 u‖ ≤
      cauchyEstimateBound 1 ρ (m + 1) * (∏ l, a l) * p +
        cauchyEstimateBound 1 ρ m * ∑ l, b l * ∏ l' ∈ Finset.univ.erase l, max (a l') (b l') := by
    refine hm.trans (add_le_add ?_ (mul_le_mul_of_nonneg_left hsum hC0))
    have hpa : 0 ≤ ∏ l, a l := Finset.prod_nonneg fun l _ => ha l
    calc cauchyEstimateBound 1 ρ (m + 1) * (∏ l, ‖u l‖) * ‖x‖
          ≤ cauchyEstimateBound 1 ρ (m + 1) * (∏ l, a l) * ‖x‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hC1) (norm_nonneg _)
      _ ≤ cauchyEstimateBound 1 ρ (m + 1) * (∏ l, a l) * p :=
          mul_le_mul_of_nonneg_left hxn (mul_nonneg hC1 hpa)
  rw [← norm_imagToComplexCLM, map_sub, k₀, k₁, norm_sub_rev]
  exact hfin
theorem chartShiftAlong_slotFn (U G : ChainChart F) (A B : Fin m → ChainChart F) (x : ℝ)
    (sa sb : Fin m → ℝ) :
    chartShiftAlong U (slotFn G A B) (slotFn x sa sb) =
      ⟨fun y i => U.fine y i + (x • G.fine y i + (∑ l, sa l • (A l).fine y i + ∑ l, sb l • (B l).fine y i)),
        fun j y i => U.coarse j y i +
          (x • G.coarse j y i + (∑ l, sa l • (A l).coarse j y i + ∑ l, sb l • (B l).coarse j y i))⟩ := by
  unfold chartShiftAlong
  congr 1
  · funext y i
    rw [← sum_slotFn]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rcases s with _ | l | l <;> rfl
  · funext j y i
    rw [← sum_slotFn]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rcases s with _ | l | l <;> rfl
theorem topVariationAlong_slotFn (e : Fin m → F.Site F.top → Fin 4 → imaginaryQuaternions) (x : ℝ)
    (sa sb : Fin m → ℝ) :
    topVariationAlong (slotFn (fun _ _ => 0) e (fun _ _ _ => 0)) (slotFn x sa sb) = topVariationAlong e sa := by
  funext y i
  unfold topVariationAlong
  have h : ∀ s : ComparisonSlot m,
      slotFn x sa sb s • slotFn (fun _ _ => (0 : imaginaryQuaternions)) e (fun _ _ _ => 0) s y i =
      slotFn (0 : imaginaryQuaternions) (fun l => sa l • e l y i) (fun _ => 0) s := by
    intro s
    rcases s with _ | l | l
    · simp [slotFn]
    · rfl
    · simp [slotFn]
  simp only [h]
  rw [sum_slotFn]
  simp
def comparisonRadius (c₀ : ℝ) (m : ℕ) : ℝ := c₀ / (4 * (m : ℝ) + 4)
def comparisonConstant (c₀ : ℝ) (m : ℕ) : ℝ :=
  cauchyEstimateBound 1 (comparisonRadius c₀ m) (m + 1) + cauchyEstimateBound 1 (comparisonRadius c₀ m) m
theorem comparison_constants {c₀ ρ p q₀ η W : ℝ} {m : ℕ} (hc₀ : 0 < c₀) (hρ : ρ * (4 * (m : ℝ) + 4) = c₀)
    (hρ0 : 0 < ρ) (hq : 0 ≤ q₀) (hq8 : q₀ ≤ c₀ / 8) (hη : 0 < η) (hp : p = min (q₀ + η) (ρ / 4))
    (hW : W ≤ 2 * (m : ℝ)) :
    ρ * (p⁻¹ * q₀ + W) ≤ c₀ := by
  have hp0 : 0 < p := by
    rw [hp]
    exact lt_min (by linarith) (by linarith)
  have h1 : ρ * (p⁻¹ * q₀) ≤ ρ + c₀ / 2 := by
    rcases min_choice (q₀ + η) (ρ / 4) with h | h
    · rw [h] at hp
      have : p⁻¹ * q₀ ≤ 1 := by
        rw [inv_mul_le_iff₀ hp0, hp]
        linarith
      nlinarith
    · rw [h] at hp
      have e : ρ * (p⁻¹ * q₀) = 4 * q₀ := by
        rw [hp]
        field_simp
      rw [e]
      linarith
  have h2 : ρ * W ≤ ρ * (2 * (m : ℝ)) := mul_le_mul_of_nonneg_left hW hρ0.le
  nlinarith
theorem norm_sliceIteratedDeriv_sub_le {c₀ : ℝ} (hc₀ : 0 < c₀) {R : F.FieldChain}
    {V : F.GaugeField F.top} {b : F.Site F.depth × Fin 4} {U Ũ : ChainChart F}
    (hfam : ∀ (ι : Type) [Fintype ι] (A : ι → ChainChart F)
      (e : ι → F.Site F.top → Fin 4 → imaginaryQuaternions)
      (w q : ι → ℝ) (ρ : ℝ), (∀ l, 0 ≤ w l) → 0 < ρ → ρ * ∑ l, w l * q l ≤ c₀ →
      (∀ l, SizedOnBondCells b (q l) (A l) (e l)) →
      ∃ g, IsBoundedHolomorphicExtension imagToComplexCLM
        (fun t : ι → ℝ => bondChartCoord R V b (chartShiftAlong U A (fun l => w l * t l))
          (topVariationAlong e (fun l => w l * t l))) g ρ 1)
    (P : ComplexQuat →L[ℝ] imaginaryQuaternions) (hP : ∀ a, P (imagToComplexCLM a) = a)
    (A Ã : Fin m → ChainChart F)
    (e : Fin m → F.Site F.top → Fin 4 → imaginaryQuaternions) (σ γ : Fin m → ℝ) {q₀ : ℝ} (hq0 : 0 ≤ q₀)
    (hq8 : q₀ ≤ c₀ / 8)
    (hσ0 : ∀ l, 0 ≤ σ l) (hγ0 : ∀ l, 0 ≤ γ l) (hσ : ∀ l, SizedOnBondCells b (σ l) (A l) (e l))
    (hγ : ∀ l, SizedOnBondCells b (γ l) (chartMove (Ã l) (A l) (-1)) (fun _ _ => 0))
    (hG : SizedOnBondCells b q₀ (chartMove Ũ U (-1)) (fun _ _ => 0)) :
    ‖localIteratedDeriv (bondChartCoord R V b) U A e - localIteratedDeriv (bondChartCoord R V b) Ũ Ã e‖ ≤
      comparisonConstant c₀ m * (q₀ * ∏ l, σ l + ∑ l, γ l * ∏ l' ∈ Finset.univ.erase l, (σ l' + γ l')) := by
  set ρ := comparisonRadius c₀ m with hρd
  have hm4 : (0 : ℝ) < 4 * (m : ℝ) + 4 := by positivity
  have hρ0 : 0 < ρ := div_pos hc₀ hm4
  have hρm : ρ * (4 * (m : ℝ) + 4) = c₀ := by
    rw [hρd, comparisonRadius]
    field_simp
  set A₁ := cauchyEstimateBound 1 ρ (m + 1) with hA₁
  set A₀ := cauchyEstimateBound 1 ρ m with hA₀
  have hA₁0 : 0 ≤ A₁ := cauchyEstimateBound_nonneg zero_le_one hρ0 _
  have hA₀0 : 0 ≤ A₀ := cauchyEstimateBound_nonneg zero_le_one hρ0 _
  set x := ‖localIteratedDeriv (bondChartCoord R V b) U A e -
    localIteratedDeriv (bondChartCoord R V b) Ũ Ã e‖ with hx
  have hstep : ∀ η : ℝ, 0 < η → x ≤ A₁ * (∏ l, (σ l + η)) * (q₀ + η) +
      A₀ * ∑ l, (γ l + η) * ∏ l' ∈ Finset.univ.erase l, (σ l' + γ l' + 2 * η) := by
    intro η hη
    set a : Fin m → ℝ := fun l => σ l + η with ha
    set bb : Fin m → ℝ := fun l => γ l + η with hbb
    set p := min (q₀ + η) (ρ / 4) with hp
    have ha0 : ∀ l, 0 < a l := fun l => by have := hσ0 l; simp only [ha]; linarith
    have hb0 : ∀ l, 0 < bb l := fun l => by have := hγ0 l; simp only [hbb]; linarith
    have hp0 : 0 < p := lt_min (by linarith) (by linarith)
    let Â : ComparisonSlot m → ChainChart F :=
      slotFn (chartMove Ũ U (-1)) A (fun l => chartMove (Ã l) (A l) (-1))
    let ê : ComparisonSlot m → F.Site F.top → Fin 4 → imaginaryQuaternions :=
      slotFn (fun _ _ => 0) e (fun _ _ _ => 0)
    let w : ComparisonSlot m → ℝ := slotFn p⁻¹ (fun l => (a l)⁻¹) (fun l => (bb l)⁻¹)
    let q : ComparisonSlot m → ℝ := slotFn q₀ σ γ
    have hw : ∀ i, 0 ≤ w i := fun i => by
      rcases i with _ | l | l
      · exact (inv_pos.2 hp0).le
      · exact (inv_pos.2 (ha0 l)).le
      · exact (inv_pos.2 (hb0 l)).le
    have hsum : ∑ i, w i * q i = p⁻¹ * q₀ + (∑ l, (a l)⁻¹ * σ l + ∑ l, (bb l)⁻¹ * γ l) := by
      rw [← sum_slotFn]
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases i with _ | l | l <;> rfl
    have hW : ∑ l, (a l)⁻¹ * σ l + ∑ l, (bb l)⁻¹ * γ l ≤ 2 * (m : ℝ) := by
      have h1 : ∑ l, (a l)⁻¹ * σ l ≤ m := by
        refine (Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun l _ => ?_).trans (by simp)
        rw [inv_mul_le_iff₀ (ha0 l)]
        simp only [ha]
        linarith
      have h2 : ∑ l, (bb l)⁻¹ * γ l ≤ m := by
        refine (Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun l _ => ?_).trans (by simp)
        rw [inv_mul_le_iff₀ (hb0 l)]
        simp only [hbb]
        linarith
      linarith
    have hbud : ρ * ∑ i, w i * q i ≤ c₀ := by
      rw [hsum]
      exact comparison_constants hc₀ hρm hρ0 hq0 hq8 hη hp hW
    have hsz : ∀ i, SizedOnBondCells b (q i) (Â i) (ê i) := fun i => by
      rcases i with _ | l | l
      · exact hG
      · exact hσ l
      · exact hγ l
    obtain ⟨g, hg⟩ := hfam (ComparisonSlot m) Â ê w q ρ hw hρ0 hbud hsz
    have h₀ : ∀ T, bondChartCoord R V b (chartShiftAlong U A T) (topVariationAlong e T) =
        (fun t : ComparisonSlot m → ℝ => bondChartCoord R V b (chartShiftAlong U Â (fun l => w l * t l))
          (topVariationAlong ê (fun l => w l * t l))) (linePoint 0 a 0 T) := by
      intro T
      have hs : (fun l => w l * linePoint 0 a 0 T l) = slotFn 0 T 0 := by
        funext i
        rcases i with _ | l | l
        · simp [linePoint, slotFn]
        · show (a l)⁻¹ * (a l * T l) = T l
          field_simp [(ha0 l).ne']
        · simp [linePoint, slotFn]
      simp only [hs]
      rw [topVariationAlong_slotFn, chartShiftAlong_slotFn]
      congr 1
      simp [chartShiftAlong]
    have h₁ : ∀ T, bondChartCoord R V b (chartShiftAlong Ũ Ã T) (topVariationAlong e T) =
        (fun t : ComparisonSlot m → ℝ => bondChartCoord R V b (chartShiftAlong U Â (fun l => w l * t l))
          (topVariationAlong ê (fun l => w l * t l))) (linePoint p a bb T) := by
      intro T
      have hs : (fun l => w l * linePoint p a bb T l) = slotFn 1 T T := by
        funext i
        rcases i with _ | l | l
        · show p⁻¹ * p = 1
          exact inv_mul_cancel₀ hp0.ne'
        · show (a l)⁻¹ * (a l * T l) = T l
          field_simp [(ha0 l).ne']
        · show (bb l)⁻¹ * (bb l * T l) = T l
          field_simp [(hb0 l).ne']
      simp only [hs]
      rw [topVariationAlong_slotFn, chartShiftAlong_slotFn]
      congr 1
      unfold chartShiftAlong
      congr 1
      · funext y i
        simp only [chartMove]
        have e1 : ∑ l, T l • (A l).fine y i + ∑ l, T l • ((Ã l).fine y i + (-1 : ℝ) • (A l).fine y i) =
            ∑ l, T l • (Ã l).fine y i := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          module
        rw [e1]
        module
      · funext j y i
        simp only [chartMove]
        have e1 : ∑ l, T l • (A l).coarse j y i +
            ∑ l, T l • ((Ã l).coarse j y i + (-1 : ℝ) • (A l).coarse j y i) =
            ∑ l, T l • (Ã l).coarse j y i := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          module
        rw [e1]
        module
    have hcore := norm_iteratedFDeriv_sub_le_of_extension hg P hP hp0.le (min_le_right _ _)
      (fun l => (ha0 l).le) (fun l => (hb0 l).le) h₀ h₁
    refine hcore.trans (add_le_add ?_ (mul_le_mul_of_nonneg_left ?_ hA₀0))
    · exact mul_le_mul_of_nonneg_left (min_le_left _ _)
        (mul_nonneg hA₁0 (Finset.prod_nonneg fun l _ => (ha0 l).le))
    · refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (hb0 l).le
      refine Finset.prod_le_prod (fun l' _ => (le_max_of_le_left (ha0 l').le)) fun l' _ => ?_
      have h1 := hσ0 l'
      have h2 := hγ0 l'
      refine max_le ?_ ?_
      · simp only [ha]
        linarith
      · simp only [hbb]
        linarith
  have hlim : Filter.Tendsto (fun η : ℝ => A₁ * (∏ l, (σ l + η)) * (q₀ + η) +
      A₀ * ∑ l, (γ l + η) * ∏ l' ∈ Finset.univ.erase l, (σ l' + γ l' + 2 * η)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (A₁ * (∏ l, (σ l + 0)) * (q₀ + 0) +
        A₀ * ∑ l, (γ l + 0) * ∏ l' ∈ Finset.univ.erase l, (σ l' + γ l' + 2 * 0))) := by
    have hc : Continuous fun η : ℝ => A₁ * (∏ l, (σ l + η)) * (q₀ + η) +
        A₀ * ∑ l, (γ l + η) * ∏ l' ∈ Finset.univ.erase l, (σ l' + γ l' + 2 * η) := by fun_prop
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  simp only [add_zero, mul_zero] at hlim
  have hle : x ≤ A₁ * (∏ l, σ l) * q₀ + A₀ * ∑ l, γ l * ∏ l' ∈ Finset.univ.erase l, (σ l' + γ l') := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact hstep η hη
  refine hle.trans ?_
  set X := q₀ * ∏ l, σ l with hX
  set Y := ∑ l, γ l * ∏ l' ∈ Finset.univ.erase l, (σ l' + γ l') with hY
  have hX0 : 0 ≤ X := mul_nonneg hq0 (Finset.prod_nonneg fun l _ => hσ0 l)
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun l _ => mul_nonneg (hγ0 l)
    (Finset.prod_nonneg fun l' _ => add_nonneg (hσ0 l') (hγ0 l'))
  have e1 : A₁ * (∏ l, σ l) * q₀ = A₁ * X := by
    rw [hX]
    ring
  rw [e1]
  unfold comparisonConstant
  rw [← hρd, ← hA₁, ← hA₀]
  nlinarith [mul_nonneg hA₁0 hY0, mul_nonneg hA₀0 hX0]
end YangMills.Construction.ChartCoordinateComparison
end
