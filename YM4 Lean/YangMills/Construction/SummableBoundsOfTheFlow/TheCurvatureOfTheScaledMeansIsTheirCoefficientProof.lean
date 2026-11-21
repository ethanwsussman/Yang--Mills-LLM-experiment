import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongARotationOfTheTop
import YangMills.Construction.SummableBoundsOfTheFlow.LimitsOfFunctionsWithBoundedDerivatives
import YangMills.Construction.SummableBoundsOfTheFlow.ParityOfTheScaledMeansProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheBirthsBetweenProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheCurvatureOfTheScaledMeansAtOneTopProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheCurvatureOfTheScaledMeansIsTheirCoefficient
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledMeansAreSmoothInTheTop
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.ScaledVariables
noncomputable section
open YangMills.Construction.BlockAverages hiding bondSpread
open YangMills.Construction.ColdStepAtMirrorFrames Set Filter
open scoped Topology
variable {F : BlockFrame}
private theorem abs_secondDifference_sub_le {g g' g'' : ℝ → ℝ} {x h A ε : ℝ} (hh : 0 ≤ h) (hε : 0 ≤ ε)
    (h1 : ∀ u ∈ Icc (x - h) (x + h), HasDerivAt g (g' u) u)
    (h2 : ∀ u ∈ Icc (x - h) (x + h), HasDerivAt g' (g'' u) u)
    (hb : ∀ u ∈ Icc (x - h) (x + h), |g'' u - A| ≤ ε) :
    |g (x + h) + g (x - h) - 2 * g x - A * h ^ 2| ≤ 2 * ε * h ^ 2 := by apply _root_.YangMills.SharedProofs.p15625 <;> assumption
private theorem abs_sub_limit_le_of_deriv_bound {g g' : ℝ → ℝ} {v x₁ B : ℝ} {n : ℕ} (hB : 0 ≤ B)
    (hd : ∀ x, 0 < x → x ≤ x₁ → HasDerivAt g (g' x) x) (hb : ∀ x, 0 < x → x ≤ x₁ → |g' x| ≤ B * x ^ n)
    (hlim : Tendsto g (𝓝[>] 0) (𝓝 v)) : ∀ x, 0 < x → x ≤ x₁ → |g x - v| ≤ B * x ^ (n + 1) := by apply _root_.YangMills.SharedProofs.p112515 <;> assumption
private theorem hasDerivAt_iteratedDeriv_of_contDiffAt {g : ℝ → ℝ} {n : ℕ} {x : ℝ}
    (h : ContDiffAt ℝ (n + 1 : ℕ) g x) :
    HasDerivAt (iteratedDeriv n g) (iteratedDeriv (n + 1) g x) x := by apply _root_.YangMills.Construction.UniformDerivativeBounds.hasDerivAt_iteratedDeriv_of_contDiffAt <;> assumption
private theorem bondDeriv_zero (G : F.GaugeField F.top → ℝ) (U : F.GaugeField F.top)
    (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G U c X = G U := by apply _root_.YangMills.SharedProofs.p1654 <;> assumption
private theorem bondDeriv_secondDifference (m₁ m₂ m₃ : F.GaugeField F.top → ℝ) (w : ℝ) (U : F.GaugeField F.top)
    {j : ℕ} (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions)
    (h₁ : ContDiffAt ℝ j (fun τ : Fin j → ℝ => m₁ (leftTranslate (bondSpread c X τ) U)) 0)
    (h₂ : ContDiffAt ℝ j (fun τ : Fin j → ℝ => m₂ (leftTranslate (bondSpread c X τ) U)) 0)
    (h₃ : ContDiffAt ℝ j (fun τ : Fin j → ℝ => m₃ (leftTranslate (bondSpread c X τ) U)) 0) :
    bondDeriv (fun U' => w * (m₁ U' - 2 * m₂ U' + m₃ U')) U c X =
      w * (bondDeriv m₁ U c X - 2 * bondDeriv m₂ U c X + bondDeriv m₃ U c X) := by
  unfold bondDeriv
  set A : (Fin j → ℝ) → ℝ := fun τ => m₁ (leftTranslate (bondSpread c X τ) U)
  set B : (Fin j → ℝ) → ℝ := fun τ => m₂ (leftTranslate (bondSpread c X τ) U)
  set D : (Fin j → ℝ) → ℝ := fun τ => m₃ (leftTranslate (bondSpread c X τ) U)
  have e : (fun τ : Fin j → ℝ => w * (m₁ (leftTranslate (bondSpread c X τ) U) -
      2 * m₂ (leftTranslate (bondSpread c X τ) U) + m₃ (leftTranslate (bondSpread c X τ) U))) =
      w • (A - (2 : ℝ) • B + D) := by
    funext τ
    simp [A, B, D, smul_eq_mul]
  have h₄ : ContDiffAt ℝ j ((2 : ℝ) • B) 0 := h₂.const_smul (2 : ℝ)
  have h₅ : ContDiffAt ℝ j (A - (2 : ℝ) • B) 0 := h₁.sub h₄
  have h₆ : ContDiffAt ℝ j (A - (2 : ℝ) • B + D) 0 := h₅.add h₃
  rw [e, iteratedFDeriv_const_smul_apply h₆, iteratedFDeriv_add_apply h₅ h₃, iteratedFDeriv_sub_apply h₁ h₄,
    iteratedFDeriv_const_smul_apply h₂]
  simp [smul_eq_mul]
  ring
private theorem tendsto_iteratedDeriv_two_bondDeriv {M : ℝ → F.GaugeField F.top → ℝ}
    {Q₀ : F.GaugeField F.top → ℝ} {S : Set (F.GaugeField F.top)} {l₁ B r C₄ : ℝ}
    {k : ℕ} (U : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hL : YangMills.Construction.UniformLimits.IteratedFDerivTendstoOfUniformLimit)
    (hl₁ : 0 < l₁) (hB : 0 ≤ B) (hr : 0 < r) (hk : k ≤ 2) (hX : AreUnitVectors X)
    (hC : ∀ (f : F.GaugeField F.top → ℝ) (B' : ℝ), 0 ≤ B' →
      (∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ContDiffThreeAlongBonds f (leftTranslate (bondSpread c X τ) U)) →
      (∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ (j : ℕ) (c' : Fin j → F.Site F.top × Fin 4)
        (X' : Fin j → imaginaryQuaternions),
        j ≤ 3 → AreUnitVectors X' → |bondDeriv f (leftTranslate (bondSpread c X τ) U) c' X'| ≤ B') →
      ContDiffOn ℝ 3 (fun τ => f (leftTranslate (bondSpread c X τ) U)) (Metric.ball 0 r) ∧
        ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ j : ℕ, j ≤ 3 →
          ‖iteratedFDeriv ℝ j (fun τ => f (leftTranslate (bondSpread c X τ) U)) τ‖ ≤ C₄ * B')
    (hS : ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, leftTranslate (bondSpread c X τ) U ∈ S)
    (reg : ∀ U' ∈ S, ∀ (j : ℕ) (c' : Fin j → F.Site F.top × Fin 4) (X' : Fin j → imaginaryQuaternions),
      AreUnitVectors X' → j ≤ 3 → ∀ l : ℝ, 0 < l → l ≤ l₁ →
        ContDiffAt ℝ (if j = 3 then 2 else 3) (fun l' => bondDeriv (M l') U' c' X') l)
    (bd : ∀ U' ∈ S, ∀ (j : ℕ) (c' : Fin j → F.Site F.top × Fin 4) (X' : Fin j → imaginaryQuaternions),
      AreUnitVectors X' → ∀ (i : ℕ) (l : ℝ), IsControlledOrder j i → 0 < l → l ≤ l₁ →
        |iteratedDeriv i (fun l' => bondDeriv (M l') U' c' X') l| ≤ B)
    (top : ∀ U' ∈ S, ∀ l : ℝ, 0 < l → l ≤ l₁ → ContDiffThreeAlongBonds (M l) U')
    (lim : ∀ U' ∈ S, Tendsto (iteratedDeriv 2 fun l => M l U') (𝓝[>] 0) (𝓝 (2 * Q₀ U'))) :
    Tendsto (iteratedDeriv 2 fun l => bondDeriv (M l) U c X) (𝓝[>] 0) (𝓝 (2 * bondDeriv Q₀ U c X)) := by
  classical
  have fields : ∀ U' ∈ S, ∀ (j : ℕ) (c' : Fin j → F.Site F.top × Fin 4) (X' : Fin j → imaginaryQuaternions),
      AreUnitVectors X' → j ≤ 3 → ∀ l : ℝ, 0 < l → l ≤ l₁ →
        HasDerivAt (fun l' => bondDeriv (M l') U' c' X') (deriv (fun l' => bondDeriv (M l') U' c' X') l) l ∧
        HasDerivAt (deriv fun l' => bondDeriv (M l') U' c' X')
          (iteratedDeriv 2 (fun l' => bondDeriv (M l') U' c' X') l) l := by
    intro U' hU' j c' X' hX' hj l h0 h1
    have h2 : ContDiffAt ℝ (2 : ℕ) (fun l' => bondDeriv (M l') U' c' X') l := by
      have h3 := reg U' hU' j c' X' hX' hj l h0 h1
      split_ifs at h3 with h4
      · exact h3
      · exact h3.of_le (by norm_num)
    refine ⟨(h2.differentiableAt (by norm_num)).hasDerivAt, ?_⟩
    have h3 := hasDerivAt_iteratedDeriv_of_contDiffAt (n := 1) h2
    rwa [iteratedDeriv_one] at h3
  set fl : ℝ → F.GaugeField F.top → ℝ :=
    fun l U' => 2 / l ^ 2 * (M (3 * l / 2) U' - 2 * M l U' + M (l / 2) U') with hfl
  have range : ∀ l u : ℝ, 0 < l → l ≤ 2 * l₁ / 3 → u ∈ Icc (l - l / 2) (l + l / 2) → 0 < u ∧ u ≤ l₁ := by
    intro l u h0 h1 hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have dfl : ∀ U' ∈ S, ∀ l : ℝ, 0 < l → l ≤ 2 * l₁ / 3 → ∀ (j : ℕ) (c' : Fin j → F.Site F.top × Fin 4)
      (X' : Fin j → imaginaryQuaternions), j ≤ 3 → bondDeriv (fl l) U' c' X' = 2 / l ^ 2 *
        (bondDeriv (M (3 * l / 2)) U' c' X' - 2 * bondDeriv (M l) U' c' X' + bondDeriv (M (l / 2)) U' c' X') := by
    intro U' hU' l h0 h1 j c' X' hj
    have hj' : ((j : ℕ) : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hj
    exact bondDeriv_secondDifference _ _ _ _ U' c' X'
      ((top U' hU' _ (by linarith) (by linarith) j c' X').of_le hj')
      ((top U' hU' _ h0 (by linarith) j c' X').of_le hj')
      ((top U' hU' _ (by linarith) (by linarith) j c' X').of_le hj')
  have bfl : ∀ U' ∈ S, ∀ l : ℝ, 0 < l → l ≤ 2 * l₁ / 3 → ∀ (j : ℕ) (c' : Fin j → F.Site F.top × Fin 4)
      (X' : Fin j → imaginaryQuaternions), j ≤ 3 → AreUnitVectors X' → |bondDeriv (fl l) U' c' X'| ≤ B := by
    intro U' hU' l h0 h1 j c' X' hj hX'
    rw [dfl U' hU' l h0 h1 j c' X' hj]
    have h2 := abs_secondDifference_sub_le (g := fun l' => bondDeriv (M l') U' c' X')
      (g' := deriv fun l' => bondDeriv (M l') U' c' X')
      (g'' := iteratedDeriv 2 fun l' => bondDeriv (M l') U' c' X') (x := l) (h := l / 2) (A := 0) (ε := B)
      (by positivity) hB
      (fun u hu => (fields U' hU' j c' X' hX' hj u (range l u h0 h1 hu).1 (range l u h0 h1 hu).2).1)
      (fun u hu => (fields U' hU' j c' X' hX' hj u (range l u h0 h1 hu).1 (range l u h0 h1 hu).2).2)
      (fun u hu => by
        rw [sub_zero]
        exact bd U' hU' j c' X' hX' 2 u (Or.inl ⟨hj, le_rfl⟩) (range l u h0 h1 hu).1 (range l u h0 h1 hu).2)
    have e₁ : l + l / 2 = 3 * l / 2 := by ring
    have e₂ : l - l / 2 = l / 2 := by ring
    simp only [e₁, e₂, zero_mul, sub_zero] at h2
    have hpos : 0 ≤ 2 / l ^ 2 := by positivity
    rw [abs_mul, abs_of_nonneg hpos]
    have e₃ : bondDeriv (M (3 * l / 2)) U' c' X' - 2 * bondDeriv (M l) U' c' X' + bondDeriv (M (l / 2)) U' c' X' =
        bondDeriv (M (3 * l / 2)) U' c' X' + bondDeriv (M (l / 2)) U' c' X' - 2 * bondDeriv (M l) U' c' X' := by
      ring
    rw [e₃]
    calc 2 / l ^ 2 * _ ≤ 2 / l ^ 2 * (2 * B * (l / 2) ^ 2) := mul_le_mul_of_nonneg_left h2 hpos
      _ = B := by field_simp
  have tfl : ∀ U' ∈ S, ∀ l : ℝ, 0 < l → l ≤ 2 * l₁ / 3 → ContDiffThreeAlongBonds (fl l) U' := by
    intro U' hU' l h0 h1 j c' X'
    exact contDiffAt_const.mul
      (((top U' hU' _ (by linarith) (by linarith) j c' X').sub
        (contDiffAt_const.mul (top U' hU' _ h0 (by linarith) j c' X'))).add
        (top U' hU' _ (by linarith) (by linarith) j c' X'))
  have near : ∀ U' ∈ S, ∀ l : ℝ, 0 < l → l ≤ 2 * l₁ / 3 → |fl l U' - Q₀ U'| ≤ 3 / 2 * B * l := by
    intro U' hU' l h0 h1
    have hX₀ : AreUnitVectors (Fin.elim0 : Fin 0 → imaginaryQuaternions) := fun i => i.elim0
    have hm : (fun l' => bondDeriv (M l') U' (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
        (Fin.elim0 : Fin 0 → imaginaryQuaternions)) = fun l' => M l' U' :=
      funext fun l' => bondDeriv_zero _ _ _ _
    have fo := fields U' hU' 0 Fin.elim0 Fin.elim0 hX₀ (by norm_num)
    have rg := reg U' hU' 0 Fin.elim0 Fin.elim0 hX₀ (by norm_num)
    have b₃ := bd U' hU' 0 Fin.elim0 Fin.elim0 hX₀ 3
    rw [hm] at fo rg b₃
    have d3 : ∀ u, 0 < u → u ≤ l₁ → HasDerivAt (iteratedDeriv 2 fun l' => M l' U')
        (iteratedDeriv 3 (fun l' => M l' U') u) u := fun u p q =>
      hasDerivAt_iteratedDeriv_of_contDiffAt (n := 2) (by simpa using rg u p q)
    have cl := abs_sub_limit_le_of_deriv_bound (n := 0) hB d3 (fun u p q => by
      simpa using b₃ u (Or.inr ⟨by norm_num, le_rfl⟩) p q) (lim U' hU')
    have h2 := abs_secondDifference_sub_le (g := fun l' => M l' U') (g' := deriv fun l' => M l' U')
      (g'' := iteratedDeriv 2 fun l' => M l' U') (x := l) (h := l / 2) (A := 2 * Q₀ U')
      (ε := B * (3 * l / 2)) (by positivity) (by positivity)
      (fun u hu => (fo u (range l u h0 h1 hu).1 (range l u h0 h1 hu).2).1)
      (fun u hu => (fo u (range l u h0 h1 hu).1 (range l u h0 h1 hu).2).2)
      (fun u hu => by
        have h3 := cl u (range l u h0 h1 hu).1 (range l u h0 h1 hu).2
        refine h3.trans ?_
        have h4 : u ≤ 3 * l / 2 := by linarith [hu.2]
        simpa using mul_le_mul_of_nonneg_left h4 hB)
    have e₁ : l + l / 2 = 3 * l / 2 := by ring
    have e₂ : l - l / 2 = l / 2 := by ring
    simp only [e₁, e₂] at h2
    have hpos : 0 ≤ 2 / l ^ 2 := by positivity
    have e₃ : fl l U' - Q₀ U' =
        2 / l ^ 2 * (M (3 * l / 2) U' + M (l / 2) U' - 2 * M l U' - 2 * Q₀ U' * (l / 2) ^ 2) := by
      simp only [hfl]
      field_simp
      ring
    rw [e₃, abs_mul, abs_of_nonneg hpos]
    calc 2 / l ^ 2 * _ ≤ 2 / l ^ 2 * (2 * (B * (3 * l / 2)) * (l / 2) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 hpos
      _ = _ := by field_simp
  set W : ℝ → (Fin k → ℝ) → ℝ := fun l τ => fl l (leftTranslate (bondSpread c X τ) U) with hW
  set Q : (Fin k → ℝ) → ℝ := fun τ => Q₀ (leftTranslate (bondSpread c X τ) U) with hQ
  have small : ∀ᶠ l : ℝ in 𝓝[>] 0, 0 < l ∧ l ≤ 2 * l₁ / 3 := by
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 2 * l₁ / 3 by positivity)] with l hl using hl
  have ev : ∀ᶠ l : ℝ in 𝓝[>] 0, ContDiffOn ℝ 3 (W l) (Metric.ball 0 r) ∧
      ∀ x ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ j : ℕ, j ≤ 3 → ‖iteratedFDeriv ℝ j (W l) x‖ ≤ C₄ * B := by
    filter_upwards [small] with l hl
    exact hC (fl l) B hB (fun τ hτ => tfl _ (hS τ hτ) l hl.1 hl.2)
      (fun τ hτ j c' X' hj hX' => bfl _ (hS τ hτ) l hl.1 hl.2 j c' X' hj hX')
  have un : TendstoUniformlyOn W Q (𝓝[>] 0) (Metric.ball 0 r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h3 : ∀ᶠ l : ℝ in 𝓝[>] 0, l < ε / (3 / 2 * B + 1) := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ε / (3 / 2 * B + 1) by positivity)] with l hl using hl.2
    filter_upwards [small, h3] with l hl hlε τ hτ
    rw [dist_comm, Real.dist_eq]
    refine lt_of_le_of_lt (near _ (hS τ hτ) l hl.1 hl.2) ?_
    rw [lt_div_iff₀ (by positivity)] at hlε
    nlinarith [hl.1]
  have lim₁ := hL k r (C₄ * B) ℝ (𝓝[>] 0) W Q hr ev un k (fun i => Pi.single i 1) hk
  have hU : U ∈ S := by
    have h0 := hS 0 (Metric.mem_ball_self hr)
    have h1 : leftTranslate (bondSpread c X (0 : Fin k → ℝ)) U = U := by
      funext y i
      have h : expUnit (0 : imaginaryQuaternions) = 1 := by
        apply Subtype.ext
        simp [expUnit]
      simp [leftTranslate, bondSpread, h]
    rwa [h1] at h0
  have close : ∀ l : ℝ, 0 < l → l ≤ 2 * l₁ / 3 →
      |iteratedDeriv 2 (fun l' => bondDeriv (M l') U c X) l -
        2 * iteratedFDeriv ℝ k (W l) 0 fun i => Pi.single i 1| ≤ B * l := by
    intro l h0 h1
    have hk3 : k ≤ 3 := by omega
    set G : ℝ → ℝ := fun l' => bondDeriv (M l') U c X with hG
    have fo := fields U hU k c X hX hk3
    have rg := reg U hU k c X hX hk3
    have d3 : ∀ u, 0 < u → u ≤ l₁ → HasDerivAt (iteratedDeriv 2 G) (iteratedDeriv 3 G u) u := fun u p q =>
      hasDerivAt_iteratedDeriv_of_contDiffAt (n := 2) (by
        have := rg u p q
        rw [if_neg (by omega)] at this
        exact this)
    have b3 : ∀ u, 0 < u → u ≤ l₁ → |iteratedDeriv 3 G u| ≤ B := fun u p q =>
      bd U hU k c X hX 3 u (Or.inr ⟨hk, le_rfl⟩) p q
    have vary : ∀ u ∈ Icc (l - l / 2) (l + l / 2), |iteratedDeriv 2 G u - iteratedDeriv 2 G l| ≤ B * (l / 2) := by
      intro u hu
      have hsub := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := iteratedDeriv 2 G)
        (f' := iteratedDeriv 3 G) (C := B) (s := Icc (l - l / 2) (l + l / 2)) (x := l) (y := u)
        (fun x hx => (d3 x (range l x h0 h1 hx).1 (range l x h0 h1 hx).2).hasDerivWithinAt)
        (fun x hx => by
          rw [Real.norm_eq_abs]
          exact b3 x (range l x h0 h1 hx).1 (range l x h0 h1 hx).2)
        (convex_Icc _ _) ⟨by linarith, by linarith⟩ hu
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at hsub
      refine hsub.trans (mul_le_mul_of_nonneg_left ?_ hB)
      rw [abs_le]
      constructor <;> linarith [hu.1, hu.2]
    have h2 := abs_secondDifference_sub_le (g := G) (g' := deriv G) (g'' := iteratedDeriv 2 G) (x := l)
      (h := l / 2) (A := iteratedDeriv 2 G l) (ε := B * (l / 2)) (by positivity) (by positivity)
      (fun u hu => (fo u (range l u h0 h1 hu).1 (range l u h0 h1 hu).2).1)
      (fun u hu => (fo u (range l u h0 h1 hu).1 (range l u h0 h1 hu).2).2) vary
    have e₁ : l + l / 2 = 3 * l / 2 := by ring
    have e₂ : l - l / 2 = l / 2 := by ring
    simp only [e₁, e₂] at h2
    have hd : (iteratedFDeriv ℝ k (W l) 0 fun i => Pi.single i 1) = bondDeriv (fl l) U c X := rfl
    rw [hd, dfl U hU l h0 h1 k c X hk3]
    have e₃ : iteratedDeriv 2 G l - 2 * (2 / l ^ 2 * (G (3 * l / 2) - 2 * G l + G (l / 2))) =
        -(4 / l ^ 2) * (G (3 * l / 2) + G (l / 2) - 2 * G l - iteratedDeriv 2 G l * (l / 2) ^ 2) := by
      field_simp
      ring
    show |iteratedDeriv 2 G l - 2 * (2 / l ^ 2 * (G (3 * l / 2) - 2 * G l + G (l / 2)))| ≤ B * l
    rw [e₃, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 / l ^ 2)]
    calc 4 / l ^ 2 * _ ≤ 4 / l ^ 2 * (2 * (B * (l / 2)) * (l / 2) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by field_simp; ring
  have to₀ : Tendsto (fun l => iteratedDeriv 2 (fun l' => bondDeriv (M l') U c X) l -
      2 * iteratedFDeriv ℝ k (W l) 0 fun i => Pi.single i 1) (𝓝[>] 0) (𝓝 0) := by
    have hu : Tendsto (fun l : ℝ => B * l) (𝓝[>] 0) (𝓝 0) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      have h2 : Tendsto (fun l : ℝ => B * l) (𝓝 0) (𝓝 (B * 0)) :=
        (continuous_const.mul continuous_id : Continuous fun l : ℝ => B * l).tendsto 0
      rwa [mul_zero] at h2
    refine squeeze_zero_norm' ?_ hu
    filter_upwards [small] with l hl
    rw [Real.norm_eq_abs]
    exact close l hl.1 hl.2
  have := to₀.add (lim₁.const_mul 2)
  simp only [sub_add_cancel, zero_add] at this
  exact this
private theorem eventually_isSmallCurvature_leftTranslate {k : ℕ} (hfin : Finite F.Cell) {s : ℝ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) {U : F.GaugeField F.top}
    (hU : IsSmallCurvature s U) :
    ∀ᶠ τ : Fin k → ℝ in 𝓝 0, IsSmallCurvature s (leftTranslate (bondSpread c X τ) U) := by apply _root_.YangMills.Construction.InterpolatedBirths.eventually_isSmallCurvature_translate <;> assumption
theorem scaledMeanSecondDerivTendsToCoeff_holds (hR : scaledMeansSmoothInScale)
    (hB : scaledMeansBounded) (hT : observableMeanContDiffThreeStatement)
    (hZ : ScaledMeanCurvatureLimit)
    (hL : YangMills.Construction.UniformLimits.IteratedFDerivTendstoOfUniformLimit)
    (hC : YangMills.Construction.Estimates.ContDiffBoundAlongRotationOfTop) :
    scaledMeanSecondDerivTendsToCoeff := by
  unfold scaledMeansSmoothInScale ForallSmoothObservables at hR
  unfold scaledMeansBounded ForallSmoothObservables at hB
  unfold observableMeanContDiffThreeStatement ForallSmoothObservables at hT
  unfold ScaledMeanCurvatureLimit ForallSmoothObservables at hZ
  unfold scaledMeanSecondDerivTendsToCoeff ForallSmoothObservables
  refine EventuallyOrdered.mono (EventuallyOrdered.and hR (EventuallyOrdered.and hB (EventuallyOrdered.and hT hZ))) ?_
  rintro T hTd hn₁ ⟨g₁, g₂, g₃, g₄⟩ e
  obtain ⟨a₁, c₁, p₁, q₁, k₁⟩ := g₁ e
  obtain ⟨a₂, C, p₂, pC, k₂⟩ := g₂ e
  obtain ⟨a₃, c₃, p₃, q₃, k₃⟩ := g₃ e
  obtain ⟨a₄, c₄, p₄, q₄, k₄⟩ := g₄ e
  refine ⟨min a₁ (min a₂ (min a₃ a₄)), 1, by positivity, one_pos,
    fun l₁ hl hle t f F U Y law K Ob k c X hf hF hU hLw hK hO hX hk => ?_⟩
  have e₁ : l₁ ≤ a₁ := le_trans hle (min_le_left _ _)
  have e₂ : l₁ ≤ a₂ := le_trans hle (le_trans (min_le_right _ _) (min_le_left _ _))
  have e₃ : l₁ ≤ a₃ := le_trans hle (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have e₄ : l₁ ≤ a₄ := le_trans hle (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hfin : Finite F.Cell := by
    obtain ⟨-, -, n, hside, hn⟩ := hF
    have hper : ∀ i, F.period F.top i = F.extent i := fun i => by simp [BlockFrame.period]
    have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
      rw [hper, hside]
      omega⟩
    exact Pi.finite
  obtain ⟨C₄, hC₄, chart⟩ := hC k
  obtain ⟨r₀, hr₀, hcold⟩ :=
    Metric.eventually_nhds_iff_ball.mp (eventually_isSmallCurvature_leftTranslate hfin c X hU)
  set r : ℝ := min r₀ (1 / (k + 1)) with hr
  have hrpos : 0 < r := lt_min hr₀ (by positivity)
  have hkr : (k : ℝ) * r ≤ 1 := by
    have h1 : r ≤ 1 / (k + 1) := min_le_right _ _
    calc (k : ℝ) * r ≤ k * (1 / (k + 1)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]
        linarith
  have hX₀ : AreUnitVectors (Fin.elim0 : Fin 0 → imaginaryQuaternions) := fun i => i.elim0
  set B : ℝ := C * K with hBdef
  have hB₀ : 0 ≤ B := by positivity
  have hexp : ∀ (j : ℕ) (c' : Fin j → F.Site F.top × Fin 4),
      Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c')) ≤ 1 := fun j c' => by
    apply Real.exp_le_one_iff.mpr
    have hκ := hTd.κ_pos
    have : 0 ≤ T.κ / 2 ^ 6 * (bondSpan Y c' : ℝ) := by positivity
    linarith
  exact tendsto_iteratedDeriv_two_bondDeriv (S := {U' | IsSmallCurvature (5 / 4 * T.σ) U'}) (B := B) (r := r)
    (C₄ := C₄) U c X hL hl hB₀ hrpos hk hX
    (fun f' B' hB' ha hb => chart F U c X f' r B' hX hrpos hkr hB' ha hb)
    (fun τ hτ => hcold τ (Metric.ball_subset_ball (min_le_left _ _) hτ))
    (fun U' hU' j c' X' hX' hj l h0 h1 =>
      k₁ l₁ hl e₁ t f F U' Y law K Ob j c' X' hf hF hU' hLw hK hO hX' hj l h0 h1)
    (fun U' hU' j c' X' hX' i l hi h0 h1 => by
      have := k₂ l₁ hl e₂ t f F U' Y law K Ob j c' X' hf hF hU' hLw hK hO hX' i l hi h0 h1
      refine this.trans ?_
      have h2 := hexp j c'
      calc C * K * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c')) ≤ C * K * 1 := mul_le_mul_of_nonneg_left h2 hB₀
        _ = B := mul_one _)
    (fun U' hU' l h0 h1 =>
      k₃ l₁ hl e₃ t f F U' Y law K Ob 0 Fin.elim0 Fin.elim0 hf hF hU' hLw hK hO hX₀ l h0 h1)
    (fun U' hU' => k₄ l₁ hl e₄ t f F U' Y law K Ob 0 Fin.elim0 Fin.elim0 hf hF hU' hLw hK hO hX₀)
end
end YangMills.Construction.ScaledVariables
