import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeBetweenSizes
import YangMills.Construction.SummableBoundsOfTheFlow.TwoTopsAlongLines
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ColdStepAtMirrorFrames Topology
open BlockAverages hiding bondSpread
namespace DerivativeInterpolation
namespace LineRestriction
variable {F : BlockFrame}
theorem iteratedFDeriv_comp_clm_zero {E' E : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup E] [NormedSpace ℝ E] {P : E → ℝ} (L : E' →L[ℝ] E) {i : ℕ} {n : ℕ}
    (hP : ContDiffAt ℝ n P 0) (hi : i ≤ n) :
    iteratedFDeriv ℝ i (P ∘ L) 0 =
      (iteratedFDeriv ℝ i P 0).compContinuousLinearMap fun _ => L := by
  obtain ⟨u, hu, hc⟩ := hP.contDiffOn (m := n) le_rfl (by simp)
  obtain ⟨v, hvu, hvo, h0⟩ := mem_nhds_iff.1 hu
  have hcv := hc.mono hvu
  have hopen : IsOpen (L ⁻¹' v) := hvo.preimage L.continuous
  have h0' : L 0 ∈ v := by simpa using h0
  have key := L.iteratedFDerivWithin_comp_right hcv hvo.uniqueDiffOn hopen.uniqueDiffOn
    (x := 0) h0' (i := i) (by exact_mod_cast hi)
  rw [iteratedFDerivWithin_of_isOpen i hopen (show (0 : E') ∈ L ⁻¹' v from h0'),
    iteratedFDerivWithin_of_isOpen i hvo h0'] at key
  simpa using key
theorem bondSpread_const {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (s : ℝ) (y : F.Site F.top) (i : Fin 4) :
    bondSpread c X (fun _ => s) y i = s • bondSpread c X (fun _ => 1) y i := by
  simp only [bondSpread, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
theorem alongLine_add {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (s t : ℝ) (V : F.GaugeField F.top) :
    alongLine c X (s + t) V = alongLine c X t (alongLine c X s V) := by
  funext y i
  simp only [alongLine, leftTranslate]
  rw [← mul_assoc]
  congr 1
  rw [bondSpread_const c X (s + t), bondSpread_const c X t, bondSpread_const c X s]
  apply Subtype.ext
  have hcomm : Commute ((t • bondSpread c X (fun _ => 1) y i : imaginaryQuaternions) : Quaternion ℝ)
      ((s • bondSpread c X (fun _ => 1) y i : imaginaryQuaternions) : Quaternion ℝ) := by
    simp only [Submodule.coe_smul]
    exact ((Commute.refl _).smul_left _).smul_right _
  have hr : ∀ z : Quaternion ℝ, z ∈ Metric.eball (0 : Quaternion ℝ)
      (NormedSpace.expSeries ℝ (Quaternion ℝ)).radius := fun z =>
    (NormedSpace.expSeries_radius_eq_top ℝ (Quaternion ℝ)).symm ▸ edist_lt_top _ _
  change NormedSpace.exp (((s + t) • bondSpread c X (fun _ => 1) y i : imaginaryQuaternions) :
      Quaternion ℝ) =
    NormedSpace.exp ((t • bondSpread c X (fun _ => 1) y i : imaginaryQuaternions) : Quaternion ℝ) *
      NormedSpace.exp ((s • bondSpread c X (fun _ => 1) y i : imaginaryQuaternions) : Quaternion ℝ)
  rw [← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hcomm (hr _) (hr _)]
  congr 1
  simp only [Submodule.coe_smul, add_smul]
  exact add_comm _ _
theorem alongLine_zero {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (V : F.GaugeField F.top) :
    alongLine c X 0 V = V := by
  funext y i
  simp only [alongLine, leftTranslate]
  have h1 : bondSpread c X (fun _ => 0) y i = 0 := by
    simp [bondSpread]
  have h2 : expUnit (0 : imaginaryQuaternions) = 1 :=
    Subtype.ext (by simp [expUnit, NormedSpace.exp_zero])
  rw [h1, h2, one_mul]
def paramMap (G : F.GaugeField F.top → ℝ) (W : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) : (Fin k → ℝ) → ℝ :=
  fun τ => G (leftTranslate (bondSpread c X τ) W)
def diagonalLine (k : ℕ) : ℝ →L[ℝ] (Fin k → ℝ) :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight fun _ => 1
theorem diagonalLine_apply (k : ℕ) (t : ℝ) : diagonalLine k t = fun _ => t := by
  funext l
  simp [diagonalLine]
theorem comp_alongLine_eq (G : F.GaugeField F.top → ℝ) (W : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    (fun t : ℝ => G (alongLine c X t W)) = paramMap G W c X ∘ diagonalLine k := by
  funext t
  simp only [Function.comp, paramMap, alongLine, diagonalLine_apply]
theorem contDiffAt_comp_alongLine_zero {G : F.GaugeField F.top → ℝ} {W : F.GaugeField F.top}
    {k : ℕ} {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    (hs : ContDiffThreeAlongBonds G W) :
    ContDiffAt ℝ 3 (fun t : ℝ => G (alongLine c X t W)) 0 := by
  rw [comp_alongLine_eq]
  have h1 : ContDiffAt ℝ 3 (paramMap G W c X) 0 := hs k c X
  have h0 : ContDiffAt ℝ 3 (paramMap G W c X) (diagonalLine k 0) := by simpa using h1
  exact ContDiffAt.comp (0 : ℝ) h0 (diagonalLine k).contDiff.contDiffAt
theorem comp_alongLine_shift (G : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (s : ℝ) :
    (fun t : ℝ => G (alongLine c X (s + t) V)) =
      fun t => G (alongLine c X t (alongLine c X s V)) := by
  funext t
  rw [alongLine_add]
theorem contDiffAt_comp_alongLine {G : F.GaugeField F.top → ℝ} {V : F.GaugeField F.top} {k : ℕ}
    {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {s : ℝ}
    (hs : ContDiffThreeAlongBonds G (alongLine c X s V)) :
    ContDiffAt ℝ 3 (fun z : ℝ => G (alongLine c X z V)) s := by
  have h1 : (fun z : ℝ => G (alongLine c X z V)) =
      (fun t : ℝ => G (alongLine c X t (alongLine c X s V))) ∘ fun z => z - s := by
    funext z
    simp only [Function.comp]
    rw [← alongLine_add]
    congr 2
    ring
  rw [h1]
  have h0 : ContDiffAt ℝ 3 (fun t : ℝ => G (alongLine c X t (alongLine c X s V)))
      ((fun z => z - s) s) := by
    simpa using contDiffAt_comp_alongLine_zero hs
  exact ContDiffAt.comp s h0 (contDiffAt_id.sub contDiffAt_const)
theorem iteratedDeriv_comp_alongLine {G : F.GaugeField F.top → ℝ} {V : F.GaugeField F.top} {k : ℕ}
    {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {s : ℝ}
    (hs : ContDiffThreeAlongBonds G (alongLine c X s V)) {i : ℕ} (hi : i ≤ 3) :
    iteratedDeriv i (fun z : ℝ => G (alongLine c X z V)) s =
      iteratedFDeriv ℝ i (paramMap G (alongLine c X s V) c X) 0 fun _ _ => 1 := by
  have h0 := congrFun (iteratedDeriv_comp_const_add i (fun z : ℝ => G (alongLine c X z V)) s) 0
  simp only [add_zero] at h0
  rw [← h0, comp_alongLine_shift, comp_alongLine_eq, iteratedDeriv_eq_iteratedFDeriv,
    iteratedFDeriv_comp_clm_zero (P := paramMap G (alongLine c X s V) c X) (diagonalLine k)
      (n := 3) (hs k c X) hi]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, diagonalLine_apply]
def coordSelect {k : ℕ} (e : Fin 3 → Fin k) : (Fin 3 → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ∑ r, (ContinuousLinearMap.proj r : (Fin 3 → ℝ) →L[ℝ] ℝ).smulRight (Pi.single (e r) 1)
theorem coordSelect_single {k : ℕ} (e : Fin 3 → Fin k) (r : Fin 3) :
    coordSelect e (Pi.single r 1) = Pi.single (e r) 1 := by
  simp [coordSelect, Pi.single_apply]
theorem bondSpread_comp {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (e : Fin 3 → Fin k) (σ : Fin 3 → ℝ) :
    bondSpread (c ∘ e) (X ∘ e) σ = bondSpread c X (coordSelect e σ) := by
  funext y i
  simp only [bondSpread, coordSelect, sum_apply, Function.comp,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, Finset.sum_apply,
    Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  have : ∀ a : Fin k, (if c a = (y, i) then (∑ r, if a = e r then σ r else 0) • X a else 0) =
      ∑ r, if a = e r then (if c (e r) = (y, i) then σ r • X (e r) else 0) else 0 := by
    intro a
    split_ifs with h
    · rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : a = e r
      · subst hr
        simp [h]
      · simp [hr]
    · symm
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : a = e r
      · subst hr
        simp [h]
      · simp [hr]
  simp only [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp
theorem bondDeriv_eq_iteratedFDeriv {G : F.GaugeField F.top → ℝ} {W : F.GaugeField F.top} {k : ℕ}
    {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    (hs : ContDiffThreeAlongBonds G W) (e : Fin 3 → Fin k) :
    bondDeriv G W (c ∘ e) (X ∘ e) = iteratedFDeriv ℝ 3 (paramMap G W c X) 0
      (fun r => Pi.single (e r) 1) := by
  have h1 : (fun τ : Fin 3 → ℝ => G (leftTranslate (bondSpread (c ∘ e) (X ∘ e) τ) W)) =
      paramMap G W c X ∘ coordSelect e := by
    funext τ
    simp only [Function.comp, paramMap, bondSpread_comp]
  unfold bondDeriv
  rw [h1, iteratedFDeriv_comp_clm_zero (P := paramMap G W c X) (coordSelect e) (n := 3)
    (hs k c X) le_rfl]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, coordSelect_single]
theorem abs_iteratedDeriv_three_le {G : F.GaugeField F.top → ℝ} {V : F.GaugeField F.top} {k : ℕ}
    {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {τ₀ M₃ : ℝ}
    (hR : IsControlledAlongLine G V c X τ₀ M₃) {s : ℝ} (hs : |s| ≤ τ₀) :
    |iteratedDeriv 3 (fun z : ℝ => G (alongLine c X z V)) s| ≤ (k : ℝ) ^ 3 * M₃ := by
  rw [iteratedDeriv_comp_alongLine (hR.smooth s hs) le_rfl]
  have h1 : (fun (_ : Fin 3) (_ : Fin k) => (1 : ℝ)) = fun _ => ∑ a, Pi.single a (1 : ℝ) := by
    funext _ l
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h1, ContinuousMultilinearMap.map_sum]
  calc _ ≤ ∑ e : Fin 3 → Fin k, M₃ := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
        rw [← bondDeriv_eq_iteratedFDeriv (hR.smooth s hs) e]
        exact hR.thirdDeriv_le s hs e
    _ = (k : ℝ) ^ 3 * M₃ := by
        simp [Finset.card_univ]
theorem hasDerivAt_iteratedDeriv_alongLine {G : F.GaugeField F.top → ℝ} {V : F.GaugeField F.top}
    {k : ℕ} {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {s : ℝ}
    (hs : ContDiffThreeAlongBonds G (alongLine c X s V)) {i : ℕ} (hi : i < 3) :
    HasDerivAt (iteratedDeriv i fun z : ℝ => G (alongLine c X z V))
      (iteratedDeriv (i + 1) (fun z : ℝ => G (alongLine c X z V)) s) s := by
  have hc := contDiffAt_comp_alongLine hs
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ i fun z : ℝ => G (alongLine c X z V)) s :=
    hc.differentiableAt_iteratedFDeriv (by exact_mod_cast hi)
  have he : (iteratedDeriv i fun z : ℝ => G (alongLine c X z V)) = fun x =>
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => ℝ) ℝ (fun _ => 1)
        (iteratedFDeriv ℝ i (fun z : ℝ => G (alongLine c X z V)) x) := by
    funext x
    exact iteratedDeriv_eq_iteratedFDeriv
  have hd' : DifferentiableAt ℝ (iteratedDeriv i fun z : ℝ => G (alongLine c X z V)) s := by
    rw [he]
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => ℝ) ℝ
      (fun _ => 1)).differentiableAt.comp s hd
  rw [iteratedDeriv_succ]
  exact hd'.hasDerivAt
theorem mul_rpow_le_sixteen_mul {a q M : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 16) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (hM : 0 ≤ M) : (a * M) ^ q ≤ 16 * M ^ q := by
  rw [Real.mul_rpow ha hM]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hM _)
  calc a ^ q ≤ 16 ^ q := Real.rpow_le_rpow ha ha' hq
    _ ≤ (16 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq'
    _ = 16 := by simp
theorem abs_sub_iteratedFDeriv_le {C : ℝ} {j : ℕ} (hj : j < 3)
    (hC : ∀ (g : ℕ → ℝ → ℝ) (τ₀ M₀ Mp : ℝ), 0 < τ₀ → 0 < M₀ → 0 ≤ Mp →
      (∀ i, i < 3 → ∀ s, |s| ≤ τ₀ → HasDerivAt (g i) (g (i + 1) s) s) →
      (∀ s, |s| ≤ τ₀ → |g 0 s| ≤ M₀) → (∀ s, |s| ≤ τ₀ → |g 3 s| ≤ Mp) →
      |g j 0| ≤ C * (M₀ / τ₀ ^ j + M₀ ^ (1 - (j : ℝ) / (3 : ℕ)) * Mp ^ ((j : ℝ) / (3 : ℕ))))
    {F' : BlockFrame} {G : F.GaugeField F.top → ℝ} {G' : F'.GaugeField F'.top → ℝ}
    {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {k : ℕ} {c : Fin k → F.Site F.top × Fin 4}
    {c' : Fin k → F'.Site F'.top × Fin 4} {X : Fin k → imaginaryQuaternions} {τ₀ M₀ M₃ : ℝ}
    (hτ : 0 < τ₀) (hM₀ : 0 < M₀) (hM₃ : 0 ≤ M₃) (hR : IsControlledAlongLine G V c X τ₀ M₃)
    (hR' : IsControlledAlongLine G' V' c' X τ₀ M₃)
    (hclose : ∀ s : ℝ, |s| ≤ τ₀ → |G (alongLine c X s V) - G' (alongLine c' X s V')| ≤ M₀) :
    |iteratedFDeriv ℝ j (paramMap G V c X) 0 (fun _ _ => 1) -
        iteratedFDeriv ℝ j (paramMap G' V' c' X) 0 (fun _ _ => 1)| ≤
      C * (M₀ / τ₀ ^ j + M₀ ^ (1 - (j : ℝ) / (3 : ℕ)) *
        (2 * ((k : ℝ) ^ 3 * M₃)) ^ ((j : ℝ) / (3 : ℕ))) := by
  have hz : |(0 : ℝ)| ≤ τ₀ := by simpa using hτ.le
  have key := hC (fun i s => iteratedDeriv i (fun z : ℝ => G (alongLine c X z V)) s -
      iteratedDeriv i (fun z : ℝ => G' (alongLine c' X z V')) s) τ₀ M₀ (2 * ((k : ℝ) ^ 3 * M₃))
    hτ hM₀ (by positivity)
    (fun i hi s hs => (hasDerivAt_iteratedDeriv_alongLine (hR.smooth s hs) hi).sub
      (hasDerivAt_iteratedDeriv_alongLine (hR'.smooth s hs) hi))
    (fun s hs => by simpa [iteratedDeriv_zero] using hclose s hs)
    (fun s hs => by
      refine (abs_sub _ _).trans ?_
      have a := abs_iteratedDeriv_three_le hR hs
      have b := abs_iteratedDeriv_three_le hR' hs
      linarith)
  have e1 := iteratedDeriv_comp_alongLine (i := j) (hR.smooth 0 hz) (by omega)
  have e2 := iteratedDeriv_comp_alongLine (i := j) (hR'.smooth 0 hz) (by omega)
  rw [alongLine_zero] at e1 e2
  have hcancelled' : |iteratedDeriv j (fun z : ℝ => G (alongLine c X z V)) 0 -
      iteratedDeriv j (fun z : ℝ => G' (alongLine c' X z V')) 0| ≤ _ := key
  rwa [e1, e2] at hcancelled'
def signScale {k : ℕ} (ς : Fin k → ℝ) : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun l => ς l • (ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ)
theorem signScale_apply {k : ℕ} (ς τ : Fin k → ℝ) (l : Fin k) : signScale ς τ l = ς l * τ l := by
  simp [signScale]
theorem paramMap_smul (G : F.GaugeField F.top → ℝ) (W : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (ς : Fin k → ℝ) :
    paramMap G W c (fun l => ς l • X l) = paramMap G W c X ∘ signScale ς := by
  funext τ
  simp only [Function.comp, paramMap]
  congr 2
  funext y i
  simp only [bondSpread, signScale_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · rw [smul_smul, mul_comm]
  · rfl
theorem polarization {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ u v, Q u v = Q v u) (u v : E) :
    Q (u + v) (u + v) - Q (u - v) (u - v) = 4 * Q u v := by
  simp only [map_add, map_sub, add_apply, sub_apply]
  rw [hsym v u]
  ring
end LineRestriction
open LineRestriction in
theorem derivDiffLeOfCloseAlongLines_of_landauKolmogorov (h : LandauKolmogorovAtZero) :
    DerivDiffLeOfCloseAlongLines := by
  obtain ⟨C₁, hC₁, b₁⟩ := h 3 1 (by norm_num)
  obtain ⟨C₂, hC₂, b₂⟩ := h 3 2 (by norm_num)
  refine ⟨16 * (C₁ + C₂), by positivity, ?_⟩
  intro F F' G G' V V' k c c' X τ₀ M₀ M₃ hk1 hk2 hτ hM₀ hM₃ hread
  have hz : |(0 : ℝ)| ≤ τ₀ := by simpa using hτ.le
  obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
  · obtain ⟨r1, r2, r3⟩ := hread (fun _ => 1) (fun _ => Or.inl rfl)
    have eX : (fun l => (1 : ℝ) • X l) = X := by
      funext l
      simp
    rw [eX] at r1 r2 r3
    have key := abs_sub_iteratedFDeriv_le (j := 1) (by norm_num) b₁ hτ hM₀ hM₃ r1 r2 r3
    have hv : (fun l : Fin 1 => (Pi.single l 1 : Fin 1 → ℝ)) = fun _ _ => 1 := by
      funext l m
      have : l = m := Subsingleton.elim _ _
      simp [this]
    have d1 : bondDeriv G V c X = iteratedFDeriv ℝ 1 (paramMap G V c X) 0 (fun _ _ => 1) := by
      rw [← hv]
      rfl
    have d2 : bondDeriv G' V' c' X = iteratedFDeriv ℝ 1 (paramMap G' V' c' X) 0 (fun _ _ => 1) := by
      rw [← hv]
      rfl
    rw [d1, d2]
    refine key.trans ?_
    have hb := mul_rpow_le_sixteen_mul (a := 2 * (((1 : ℕ) : ℝ) ^ 3))
      (q := ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ))
      (M := M₃) (by positivity) (by norm_num) (by positivity) (by norm_num) hM₃
    have hb' : (2 * (((1 : ℕ) : ℝ) ^ 3 * M₃)) ^ (((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) ≤
        16 * M₃ ^ (((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) := by
      rwa [mul_assoc] at hb
    have p0 : 0 ≤ M₀ ^ (1 - ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) := Real.rpow_nonneg hM₀.le _
    have p1 : 0 ≤ M₃ ^ (((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) := Real.rpow_nonneg hM₃ _
    have p2 : 0 ≤ M₀ / τ₀ ^ 1 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hb' p0
    have hmul2 : C₁ * (M₀ / τ₀ ^ 1 + M₀ ^ (1 - ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) *
        (2 * (((1 : ℕ) : ℝ) ^ 3 * M₃)) ^ (((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ))) ≤
        C₁ * (16 * (M₀ / τ₀ ^ 1 + M₀ ^ (1 - ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) *
          M₃ ^ (((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)))) := by
      refine mul_le_mul_of_nonneg_left ?_ hC₁.le
      nlinarith
    refine hmul2.trans ?_
    have hnn : 0 ≤ M₀ / τ₀ ^ 1 + M₀ ^ (1 - ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) *
        M₃ ^ (((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) := by positivity
    have hfin : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
    rw [hfin]
    nlinarith [mul_nonneg hC₂.le hnn]
  · obtain ⟨r1, r2, r3⟩ := hread (fun _ => 1) (fun _ => Or.inl rfl)
    obtain ⟨q1, q2, q3⟩ := hread ![1, -1] (by
      intro l
      fin_cases l <;> simp)
    have keyp := abs_sub_iteratedFDeriv_le (j := 2) (by norm_num) b₂ hτ hM₀ hM₃ r1 r2 r3
    have keym := abs_sub_iteratedFDeriv_le (j := 2) (by norm_num) b₂ hτ hM₀ hM₃ q1 q2 q3
    have sG : ContDiffThreeAlongBonds G V := by
      have := r1.smooth 0 hz
      rwa [alongLine_zero] at this
    have sG' : ContDiffThreeAlongBonds G' V' := by
      have := r2.smooth 0 hz
      rwa [alongLine_zero] at this
    have c2 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (paramMap G V c X) 0 :=
      (show ContDiffAt ℝ 3 (paramMap G V c X) 0 from sG 2 c X).of_le (by norm_num)
    have c2' : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (paramMap G' V' c' X) 0 :=
      (show ContDiffAt ℝ 3 (paramMap G' V' c' X) 0 from sG' 2 c' X).of_le (by norm_num)
    have sgn : ∀ (ς : Fin 2 → ℝ),
        iteratedFDeriv ℝ 2 (paramMap G V c fun l => ς l • X l) 0 (fun _ _ => 1) =
          fderiv ℝ (fderiv ℝ (paramMap G V c X)) 0 ς ς := by
      intro ς
      rw [paramMap_smul, iteratedFDeriv_comp_clm_zero (P := paramMap G V c X) (signScale ς)
        (n := 2) c2 le_rfl]
      have h1 : signScale ς (fun _ => 1) = ς := by
        funext l
        simp [signScale_apply]
      simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, h1,
        iteratedFDeriv_two_apply]
    have sgn' : ∀ (ς : Fin 2 → ℝ),
        iteratedFDeriv ℝ 2 (paramMap G' V' c' fun l => ς l • X l) 0 (fun _ _ => 1) =
          fderiv ℝ (fderiv ℝ (paramMap G' V' c' X)) 0 ς ς := by
      intro ς
      rw [paramMap_smul, iteratedFDeriv_comp_clm_zero (P := paramMap G' V' c' X) (signScale ς)
        (n := 2) c2' le_rfl]
      have h1 : signScale ς (fun _ => 1) = ς := by
        funext l
        simp [signScale_apply]
      simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, h1,
        iteratedFDeriv_two_apply]
    rw [sgn, sgn'] at keyp keym
    have sym : ∀ u v, fderiv ℝ (fderiv ℝ (paramMap G V c X)) 0 u v =
        fderiv ℝ (fderiv ℝ (paramMap G V c X)) 0 v u := fun u v =>
      (c2.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])) u v
    have sym' : ∀ u v, fderiv ℝ (fderiv ℝ (paramMap G' V' c' X)) 0 u v =
        fderiv ℝ (fderiv ℝ (paramMap G' V' c' X)) 0 v u := fun u v =>
      (c2'.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])) u v
    set e₀ : Fin 2 → ℝ := Pi.single 0 1 with he₀
    set e₁ : Fin 2 → ℝ := Pi.single 1 1 with he₁
    have hp : (fun _ : Fin 2 => (1 : ℝ)) = e₀ + e₁ := by
      funext l
      fin_cases l <;> simp [he₀, he₁]
    have hm : (![1, -1] : Fin 2 → ℝ) = e₀ - e₁ := by
      funext l
      fin_cases l <;> simp [he₀, he₁]
    rw [hp] at keyp
    rw [hm] at keym
    have d1 : bondDeriv G V c X = fderiv ℝ (fderiv ℝ (paramMap G V c X)) 0 e₀ e₁ := by
      unfold bondDeriv
      rw [iteratedFDeriv_two_apply]
      rfl
    have d2 : bondDeriv G' V' c' X = fderiv ℝ (fderiv ℝ (paramMap G' V' c' X)) 0 e₀ e₁ := by
      unfold bondDeriv
      rw [iteratedFDeriv_two_apply]
      rfl
    have pl := polarization _ sym e₀ e₁
    have pl' := polarization _ sym' e₀ e₁
    rw [d1, d2]
    have hb := mul_rpow_le_sixteen_mul (a := 2 * (((2 : ℕ) : ℝ) ^ 3))
      (q := ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ))
      (M := M₃) (by positivity) (by norm_num) (by positivity) (by norm_num) hM₃
    have hb' : (2 * (((2 : ℕ) : ℝ) ^ 3 * M₃)) ^ (((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) ≤
        16 * M₃ ^ (((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) := by
      rwa [mul_assoc] at hb
    have p0 : 0 ≤ M₀ ^ (1 - ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) := Real.rpow_nonneg hM₀.le _
    have p1 : 0 ≤ M₃ ^ (((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) := Real.rpow_nonneg hM₃ _
    have p2 : 0 ≤ M₀ / τ₀ ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hb' p0
    have hU : C₂ * (M₀ / τ₀ ^ 2 + M₀ ^ (1 - ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) *
        (2 * (((2 : ℕ) : ℝ) ^ 3 * M₃)) ^ (((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ))) ≤
        C₂ * (16 * (M₀ / τ₀ ^ 2 + M₀ ^ (1 - ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) *
          M₃ ^ (((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)))) := by
      refine mul_le_mul_of_nonneg_left ?_ hC₂.le
      nlinarith
    have hnn : 0 ≤ M₀ / τ₀ ^ 2 + M₀ ^ (1 - ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) *
        M₃ ^ (((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) := by positivity
    have hfin : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
    rw [hfin]
    set R := M₀ / τ₀ ^ 2 + M₀ ^ (1 - ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) *
        M₃ ^ (((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) with hR
    have a1 := keyp.trans hU
    have a2 := keym.trans hU
    set a := fderiv ℝ (fderiv ℝ (paramMap G V c X)) 0 e₀ e₁
    set b := fderiv ℝ (fderiv ℝ (paramMap G' V' c' X)) 0 e₀ e₁
    have e4 : 4 * (a - b) = (fderiv ℝ (fderiv ℝ (paramMap G V c X)) 0 (e₀ + e₁) (e₀ + e₁) -
        fderiv ℝ (fderiv ℝ (paramMap G' V' c' X)) 0 (e₀ + e₁) (e₀ + e₁)) -
        (fderiv ℝ (fderiv ℝ (paramMap G V c X)) 0 (e₀ - e₁) (e₀ - e₁) -
        fderiv ℝ (fderiv ℝ (paramMap G' V' c' X)) 0 (e₀ - e₁) (e₀ - e₁)) := by
      rw [mul_sub, ← pl, ← pl']
      ring
    have a3 : 4 * |a - b| ≤ 2 * (C₂ * (16 * R)) := by
      have : |4 * (a - b)| = 4 * |a - b| := by
        rw [abs_mul]
        norm_num
      rw [← this, e4]
      exact (abs_sub _ _).trans (by linarith)
    have hR0 : 0 ≤ R := hnn
    have hCR : 0 ≤ C₁ * R := mul_nonneg hC₁.le hR0
    have hCR2 : 0 ≤ C₂ * R := mul_nonneg hC₂.le hR0
    nlinarith
end DerivativeInterpolation
end YangMills.Construction
end
