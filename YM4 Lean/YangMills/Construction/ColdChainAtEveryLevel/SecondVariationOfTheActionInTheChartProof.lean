import YangMills.Construction.ColdChainAtEveryLevel.SecondVariationOfAFitInTheChartProof
import YangMills.Construction.ColdChainAtEveryLevel.CurlOfTheTopAverageProof
import YangMills.Construction.ColdChainAtEveryLevel.CurveOfAChartCoordinate
import YangMills.Construction.ColdChainAtEveryLevel.SecondVariationOfTheActionInTheChart
import YangMills.Construction.ColdChainAtEveryLevel.SecondVariationOfTheLeastActionAtAColdField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.ChartSecondVariation
open BlockAverages
variable {F : BlockFrame}
theorem deriv_deriv_comp_of_analyticAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Φ : E → ℝ) (s : ℝ → E) (hΦ : AnalyticAt ℝ Φ 0) (hs : AnalyticAt ℝ s 0) (hs0 : s 0 = 0) :
    deriv (deriv (Φ ∘ s)) 0 =
      fderiv ℝ (fderiv ℝ Φ) 0 (deriv s 0) (deriv s 0) + fderiv ℝ Φ 0 (deriv (deriv s) 0) := by
  have hc : Filter.Tendsto s (𝓝 0) (𝓝 0) := by
    have := hs.continuousAt.tendsto
    rwa [hs0] at this
  have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), AnalyticAt ℝ Φ (s τ) ∧ AnalyticAt ℝ s τ :=
    (hc.eventually hΦ.eventually_analyticAt).and hs.eventually_analyticAt
  have h1 : deriv (Φ ∘ s) =ᶠ[𝓝 0] fun τ => fderiv ℝ Φ (s τ) (deriv s τ) := by
    filter_upwards [hev] with τ hτ
    exact fderiv_comp_deriv τ hτ.1.differentiableAt hτ.2.differentiableAt
  rw [h1.deriv_eq]
  have hD : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) (s 0)) (s 0) := by
    rw [hs0]
    exact hΦ.fderiv.differentiableAt.hasFDerivAt
  have hsd : HasDerivAt s (deriv s 0) 0 := hs.differentiableAt.hasDerivAt
  have hA : HasDerivAt (fun τ => fderiv ℝ Φ (s τ)) (fderiv ℝ (fderiv ℝ Φ) (s 0) (deriv s 0)) 0 :=
    hD.comp_hasDerivAt 0 hsd
  have hB : HasDerivAt (deriv s) (deriv (deriv s) 0) 0 := hs.deriv.differentiableAt.hasDerivAt
  have := (hA.clm_apply hB).deriv
  rw [this, hs0]
theorem deriv_deriv_smul_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Φ : E → ℝ) (u : E) (hΦ : AnalyticAt ℝ Φ 0) :
    deriv (deriv fun τ : ℝ => Φ (τ • u)) 0 = fderiv ℝ (fderiv ℝ Φ) 0 u u ∧
      deriv (fun τ : ℝ => Φ (τ • u)) 0 = fderiv ℝ Φ 0 u := by
  have hl : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => τ • u) u τ := fun τ => by
    simpa using (hasDerivAt_id τ).smul_const u
  have hd : deriv (fun τ : ℝ => τ • u) = fun _ => u := funext fun τ => (hl τ).deriv
  have han : AnalyticAt ℝ (fun τ : ℝ => τ • u) 0 := by fun_prop
  constructor
  · have := deriv_deriv_comp_of_analyticAt Φ (fun τ : ℝ => τ • u) hΦ han (by simp)
    rw [hd] at this
    simpa [Function.comp_def] using this
  · have h0 : (fun τ : ℝ => τ • u) 0 = 0 := by simp
    have : AnalyticAt ℝ Φ ((fun τ : ℝ => τ • u) 0) := by rw [h0]; exact hΦ
    have h := fderiv_comp_deriv (0 : ℝ) this.differentiableAt (hl 0).differentiableAt
    rw [(hl 0).deriv] at h
    simpa [Function.comp_def] using h
theorem deriv_deriv_comp_eq_line_add {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Φ : E → ℝ) (s : ℝ → E) (hΦ : AnalyticAt ℝ Φ 0) (hs : AnalyticAt ℝ s 0) (hs0 : s 0 = 0) :
    deriv (deriv (Φ ∘ s)) 0 = deriv (deriv fun τ : ℝ => Φ (τ • deriv s 0)) 0 +
      deriv (fun τ : ℝ => Φ (τ • deriv (deriv s) 0)) 0 := by
  rw [deriv_deriv_comp_of_analyticAt Φ s hΦ hs hs0, (deriv_deriv_smul_line Φ _ hΦ).1,
    (deriv_deriv_smul_line Φ _ hΦ).2]
theorem deriv_pi_of_analyticAt {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (η : ι → ℝ → E) (h : ∀ l, AnalyticAt ℝ (η l) 0) :
    deriv (fun τ l => η l τ) 0 = (fun l => deriv (η l) 0) ∧
      deriv (deriv fun τ l => η l τ) 0 = fun l => deriv (deriv (η l)) 0 := by
  have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ l, AnalyticAt ℝ (η l) τ :=
    Filter.eventually_all.2 fun l => (h l).eventually_analyticAt
  have h1 : ∀ τ : ℝ, (∀ l, AnalyticAt ℝ (η l) τ) →
      deriv (fun τ l => η l τ) τ = fun l => deriv (η l) τ := fun τ hτ =>
    (hasDerivAt_pi.2 fun l => (hτ l).differentiableAt.hasDerivAt).deriv
  refine ⟨h1 0 h, ?_⟩
  have h2 : deriv (fun τ l => η l τ) =ᶠ[𝓝 0] fun τ l => deriv (η l) τ := by
    filter_upwards [hev] with τ hτ using h1 τ hτ
  rw [h2.deriv_eq]
  exact (hasDerivAt_pi.2 fun l => (h l).deriv.differentiableAt.hasDerivAt).deriv
def pathBondList {j : ℕ} : F.Site j → List PathStep → List (F.Site j × Fin 4)
  | _, [] => []
  | x, st :: r => (if st.2 then (x, st.1) else (x - unitStep j st.1, st.1)) ::
      pathBondList (x + stepDisplacement j st) r
theorem linkValueVariation_sub {j : ℕ} (X : F.GaugeField j) (v v' : F.Site j → Fin 4 → imaginaryQuaternions)
    (x : F.Site j) (st : PathStep) : linkValueVariation X v x st - linkValueVariation X v' x st =
      linkValueVariation X (fun x i => v x i - v' x i) x st := by
  unfold linkValueVariation
  by_cases h : st.2
  · simp [h]
  · simp only [h, Bool.false_eq_true, if_false, Submodule.coe_sub, _root_.YangMills.Construction.BlockAverages.adjointAction_sub]
    abel
theorem pathHolonomyVariation_sub {j : ℕ} (X : F.GaugeField j)
    (v v' : F.Site j → Fin 4 → imaginaryQuaternions) (l : List PathStep) :
    ∀ x : F.Site j, pathHolonomyVariation X v x l - pathHolonomyVariation X v' x l =
      pathHolonomyVariation X (fun x i => v x i - v' x i) x l := by
  induction l with
  | nil => intro x; simp [pathHolonomyVariation]
  | cons st r ih =>
    intro x
    simp only [pathHolonomyVariation]
    rw [← ih, ← linkValueVariation_sub, _root_.YangMills.Construction.BlockAverages.adjointAction_sub]
    abel
theorem norm_linkValueVariation {j : ℕ} (X : F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions)
    (x : F.Site j) (st : PathStep) :
    ‖linkValueVariation X v x st‖ =
      ‖v (if st.2 then (x, st.1) else (x - unitStep j st.1, st.1)).1
        (if st.2 then (x, st.1) else (x - unitStep j st.1, st.1)).2‖ := by apply _root_.YangMills.Construction.BlockAverages.ChartFit.norm_linkValueVariation <;> assumption
theorem norm_pathHolonomyVariation_le {j : ℕ} (X : F.GaugeField j)
    (v : F.Site j → Fin 4 → imaginaryQuaternions) (l : List PathStep) :
    ∀ x : F.Site j, ‖pathHolonomyVariation X v x l‖ ≤
      ((pathBondList x l).map fun b => ‖v b.1 b.2‖).sum := by
  induction l with
  | nil => intro x; simp [pathHolonomyVariation, pathBondList]
  | cons st r ih =>
    intro x
    simp only [pathHolonomyVariation, pathBondList, List.map_cons, List.sum_cons]
    refine (norm_add_le _ _).trans ?_
    rw [norm_adjointAction, norm_linkValueVariation]
    exact add_le_add le_rfl (ih _)
def plaquetteEdge₁ {j : ℕ} (p : F.Site j × Fin 4 × Fin 4) : F.Site j × Fin 4 := (p.1, p.2.1)
def plaquetteEdge₂ {j : ℕ} (p : F.Site j × Fin 4 × Fin 4) : F.Site j × Fin 4 :=
  (p.1 + unitStep j p.2.1, p.2.2)
def plaquetteEdge₃ {j : ℕ} (p : F.Site j × Fin 4 × Fin 4) : F.Site j × Fin 4 :=
  (p.1 + unitStep j p.2.2, p.2.1)
def plaquetteEdge₄ {j : ℕ} (p : F.Site j × Fin 4 × Fin 4) : F.Site j × Fin 4 := (p.1, p.2.2)
theorem pathBondList_plaquette {j : ℕ} (p : F.Site j × Fin 4 × Fin 4) :
    pathBondList p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] =
      [plaquetteEdge₁ p, plaquetteEdge₂ p, plaquetteEdge₃ p, plaquetteEdge₄ p] := by
  have e3 : p.1 + unitStep j p.2.1 + unitStep j p.2.2 - unitStep j p.2.1 = p.1 + unitStep j p.2.2 := by abel
  have e4 : p.1 + unitStep j p.2.1 + unitStep j p.2.2 + -unitStep j p.2.1 - unitStep j p.2.2 = p.1 := by
    abel
  simp [pathBondList, stepDisplacement, plaquetteEdge₁, plaquetteEdge₂, plaquetteEdge₃, plaquetteEdge₄, e3, e4]
theorem sq_norm_variationCurl_le {j : ℕ} (X : F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions)
    (p : F.Site j × Fin 4 × Fin 4) :
    ‖variationCurl X v p‖ ^ 2 ≤ 4 * (‖v (plaquetteEdge₁ p).1 (plaquetteEdge₁ p).2‖ ^ 2 +
      ‖v (plaquetteEdge₂ p).1 (plaquetteEdge₂ p).2‖ ^ 2 +
      ‖v (plaquetteEdge₃ p).1 (plaquetteEdge₃ p).2‖ ^ 2 +
      ‖v (plaquetteEdge₄ p).1 (plaquetteEdge₄ p).2‖ ^ 2) := by
  have h := norm_pathHolonomyVariation_le X v
    [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] p.1
  rw [pathBondList_plaquette] at h
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  have h' : ‖variationCurl X v p‖ ≤ ‖v (plaquetteEdge₁ p).1 (plaquetteEdge₁ p).2‖ +
      (‖v (plaquetteEdge₂ p).1 (plaquetteEdge₂ p).2‖ +
      (‖v (plaquetteEdge₃ p).1 (plaquetteEdge₃ p).2‖ + ‖v (plaquetteEdge₄ p).1 (plaquetteEdge₄ p).2‖)) := h
  set A := ‖v (plaquetteEdge₁ p).1 (plaquetteEdge₁ p).2‖
  set B := ‖v (plaquetteEdge₂ p).1 (plaquetteEdge₂ p).2‖
  set C := ‖v (plaquetteEdge₃ p).1 (plaquetteEdge₃ p).2‖
  set D := ‖v (plaquetteEdge₄ p).1 (plaquetteEdge₄ p).2‖
  have h2 : ‖variationCurl X v p‖ ^ 2 ≤ (A + (B + (C + D))) ^ 2 := by gcongr
  nlinarith [sq_nonneg (A - B), sq_nonneg (A - C), sq_nonneg (A - D), sq_nonneg (B - C),
    sq_nonneg (B - D), sq_nonneg (C - D)]
theorem sum_comp_le_card_mul_sum {α β ι : Type} [Fintype ι] (P : Finset α) (B : Finset β) (f : α → β)
    (g : β → ℝ) (hg : ∀ b, 0 ≤ g b) (hm : ∀ p ∈ P, f p ∈ B) (r : α → ι)
    (hr : ∀ p ∈ P, ∀ q ∈ P, f p = f q → r p = r q → p = q) :
    ∑ p ∈ P, g (f p) ≤ Fintype.card ι * ∑ b ∈ B, g b := by apply _root_.YangMills.Construction.TopAverageCurl.sum_comp_le_card_mul_sum <;> assumption
theorem plaquetteEdges_mem_innerBonds {j : ℕ} (S : Finset F.Cell) {p : F.Site j × Fin 4 × Fin 4}
    (hp : p ∈ innerPlaquettes S j) :
    plaquetteEdge₁ p ∈ innerBonds S j ∧ plaquetteEdge₂ p ∈ innerBonds S j ∧
      plaquetteEdge₃ p ∈ innerBonds S j ∧ plaquetteEdge₄ p ∈ innerBonds S j := by
  have hc := (Finset.mem_filter.1 hp).2.2
  have c1 : p.1 ∈ sitesOfCells S j := hc (by simp [plaquetteCorners])
  have c2 : p.1 + unitStep j p.2.1 ∈ sitesOfCells S j := hc (by simp [plaquetteCorners])
  have c3 : p.1 + unitStep j p.2.2 ∈ sitesOfCells S j := hc (by simp [plaquetteCorners])
  have c4 : p.1 + unitStep j p.2.1 + unitStep j p.2.2 ∈ sitesOfCells S j := hc (by simp [plaquetteCorners])
  have c4' : p.1 + unitStep j p.2.2 + unitStep j p.2.1 ∈ sitesOfCells S j := by
    rwa [add_right_comm]
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, plaquetteEdge₁,
    plaquetteEdge₂, plaquetteEdge₃, plaquetteEdge₄]
  exact ⟨⟨c1, c2⟩, ⟨c2, c4⟩, ⟨c3, c4'⟩, ⟨c1, c3⟩⟩
theorem sum_sq_norm_variationCurl_le {j : ℕ} (S : Finset F.Cell) (X : F.GaugeField j)
    (v : F.Site j → Fin 4 → imaginaryQuaternions) :
    ∑ p ∈ innerPlaquettes S j, ‖variationCurl X v p‖ ^ 2 ≤
      64 * ∑ b ∈ innerBonds S j, ‖v b.1 b.2‖ ^ 2 := by
  set g : F.Site j × Fin 4 → ℝ := fun b => ‖v b.1 b.2‖ ^ 2 with hg
  have hg0 : ∀ b, 0 ≤ g b := fun b => by positivity
  have s1 : ∑ p ∈ innerPlaquettes S j, g (plaquetteEdge₁ p) ≤
      (Fintype.card (Fin 4)) * ∑ b ∈ innerBonds S j, g b :=
    sum_comp_le_card_mul_sum _ _ plaquetteEdge₁ g hg0
      (fun p hp => (plaquetteEdges_mem_innerBonds S hp).1) (fun p => p.2.2) (by
      rintro ⟨x, μ, ν⟩ _ ⟨x', μ', ν'⟩ _ h h'
      simp only [plaquetteEdge₁, Prod.mk.injEq] at h
      simp only at h'
      simp [h.1, h.2, h'])
  have s2 : ∑ p ∈ innerPlaquettes S j, g (plaquetteEdge₂ p) ≤
      (Fintype.card (Fin 4)) * ∑ b ∈ innerBonds S j, g b :=
    sum_comp_le_card_mul_sum _ _ plaquetteEdge₂ g hg0
      (fun p hp => (plaquetteEdges_mem_innerBonds S hp).2.1) (fun p => p.2.1) (by
      rintro ⟨x, μ, ν⟩ _ ⟨x', μ', ν'⟩ _ h h'
      simp only [plaquetteEdge₂, Prod.mk.injEq] at h
      simp only at h'
      subst h'
      simp [add_right_cancel h.1, h.2])
  have s3 : ∑ p ∈ innerPlaquettes S j, g (plaquetteEdge₃ p) ≤
      (Fintype.card (Fin 4)) * ∑ b ∈ innerBonds S j, g b :=
    sum_comp_le_card_mul_sum _ _ plaquetteEdge₃ g hg0
      (fun p hp => (plaquetteEdges_mem_innerBonds S hp).2.2.1) (fun p => p.2.2) (by
      rintro ⟨x, μ, ν⟩ _ ⟨x', μ', ν'⟩ _ h h'
      simp only [plaquetteEdge₃, Prod.mk.injEq] at h
      simp only at h'
      subst h'
      simp [add_right_cancel h.1, h.2])
  have s4 : ∑ p ∈ innerPlaquettes S j, g (plaquetteEdge₄ p) ≤
      (Fintype.card (Fin 4)) * ∑ b ∈ innerBonds S j, g b :=
    sum_comp_le_card_mul_sum _ _ plaquetteEdge₄ g hg0
      (fun p hp => (plaquetteEdges_mem_innerBonds S hp).2.2.2) (fun p => p.2.1) (by
      rintro ⟨x, μ, ν⟩ _ ⟨x', μ', ν'⟩ _ h h'
      simp only [plaquetteEdge₄, Prod.mk.injEq] at h
      simp only at h'
      simp [h.1, h.2, h'])
  have h1 : ∑ p ∈ innerPlaquettes S j, ‖variationCurl X v p‖ ^ 2 ≤
      ∑ p ∈ innerPlaquettes S j, 4 * (g (plaquetteEdge₁ p) + g (plaquetteEdge₂ p) +
        g (plaquetteEdge₃ p) + g (plaquetteEdge₄ p)) :=
    Finset.sum_le_sum fun p _ => sq_norm_variationCurl_le X v p
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at h1
  simp only [Fintype.card_fin, Nat.cast_ofNat] at s1 s2 s3 s4
  linarith
theorem bondListSpread_apply_self {j k : ℕ} {c : Fin k → F.Site j × Fin 4} (hc : Function.Injective c)
    (ζ : Fin k → imaginaryQuaternions) (l : Fin k) : bondListSpread c ζ (c l).1 (c l).2 = ζ l := by
  unfold bondListSpread
  rw [Finset.sum_eq_single l]
  · simp
  · intro l' _ hl
    rw [if_neg]
    intro h
    exact hl (hc h)
  · simp
theorem bondListSpread_apply_of_ne {j k : ℕ} {c : Fin k → F.Site j × Fin 4}
    (ζ : Fin k → imaginaryQuaternions) {y : F.Site j} {i : Fin 4}
    (h : ∀ l, c l ≠ (y, i)) : bondListSpread c ζ y i = 0 := by
  unfold bondListSpread
  exact Finset.sum_eq_zero fun l _ => if_neg (h l)
theorem bondListSpread_smul {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (τ : ℝ)
    (ζ : Fin k → imaginaryQuaternions) :
    bondListSpread c (τ • ζ) = fun y i => τ • bondListSpread c ζ y i := by
  funext y i
  unfold bondListSpread
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
theorem chart_second_variation_arith (ca C₁ K ρ σ Q Cd Cv Vv Zz E D2 D1 : ℝ) (hca : 0 < ca) (hC₁ : 0 < C₁)
    (hK : 0 < K) (hρ : 0 < ρ) (hσ : 0 < σ) (hρ1 : ρ ≤ 1) (hQ : 0 ≤ Q) (hVv : Vv ≤ 4 * Q)
    (hZz : Zz ≤ K * Q) (hE : E ≤ K ^ 2 * ρ ^ 2 * Q) (hCd : Cd ≤ 2 * Cv + 2 * (64 * E))
    (hF2 : ca * Cv - C₁ * σ * Vv ≤ D2) (hF1 : -(C₁ * σ * Zz) ≤ D1) :
    ca / 2 * Cd - (64 * ca * K ^ 2 + 4 * C₁ + C₁ * K) * (ρ + σ) * Q ≤ D2 + D1 := by
  have a1 : C₁ * σ * Vv ≤ C₁ * σ * (4 * Q) := by gcongr
  have a2 : C₁ * σ * Zz ≤ C₁ * σ * (K * Q) := by gcongr
  have a3 : ca / 2 * Cd ≤ ca / 2 * (2 * Cv + 2 * (64 * E)) := by gcongr
  have a4 : 64 * ca * E ≤ 64 * ca * (K ^ 2 * ρ ^ 2 * Q) := by gcongr
  have a5 : 64 * ca * K ^ 2 * Q * ρ ^ 2 ≤ 64 * ca * K ^ 2 * Q * ρ := by
    have h7 : ρ ^ 2 ≤ ρ := by nlinarith
    gcongr
  have a6 : 0 ≤ 64 * ca * K ^ 2 * σ * Q := by positivity
  have a7 : 0 ≤ 4 * C₁ * ρ * Q := by positivity
  have a8 : 0 ≤ C₁ * K * ρ * Q := by positivity
  have e3 : (64 * ca * K ^ 2 + 4 * C₁ + C₁ * K) * (ρ + σ) * Q = 64 * ca * K ^ 2 * Q * ρ +
      64 * ca * K ^ 2 * σ * Q + 4 * C₁ * ρ * Q + C₁ * σ * (4 * Q) + C₁ * K * ρ * Q + C₁ * σ * (K * Q) := by
    ring
  rw [e3]
  linarith
theorem second_variation_at_chart_field (a ca C₁ K ρ σ : ℝ) (hca : 0 < ca) (hC₁ : 0 < C₁) (hK : 0 < K)
    (hρ : 0 < ρ) (hσ : 0 < σ) (hρ1 : ρ ≤ 1) (hKρ : K * ρ ≤ 1) (S : Finset F.Cell) (V : F.GaugeField F.top)
    (w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) (hw : SupportedOnChords S w)
    (hdw : SupportedOnChords S dw)
    (hwρ : ∀ b ∈ chordBonds S, ‖w b.1 b.2‖ ≤ ρ)
    (hcurve : ∀ b ∈ chordBonds S, ∃ η : ℝ → imaginaryQuaternions, AnalyticAt ℝ η 0 ∧ η 0 = 0 ∧
      (∀ᶠ τ : ℝ in 𝓝 0, expUnit (η τ) * expUnit (w b.1 b.2) = expUnit (w b.1 b.2 + τ • dw b.1 b.2)) ∧
      ‖deriv η 0 - dw b.1 b.2‖ ≤ K * ‖w b.1 b.2‖ * ‖dw b.1 b.2‖ ∧
      ‖deriv (deriv η) 0‖ ≤ K * ‖dw b.1 b.2‖ ^ 2)
    (hAn : ∀ (k : ℕ) (c : Fin k → F.Site F.depth × Fin 4),
      AnalyticAt ℝ (fun ζ : Fin k → imaginaryQuaternions =>
        minimalAction a S F.depth (expRotatedField (bondListSpread c ζ) (chartedField w V))) 0)
    (hFl : ∀ v : F.Site F.depth → Fin 4 → imaginaryQuaternions,
      (∀ b, b ∉ innerBonds S F.depth → v b.1 b.2 = 0) →
      ca * ∑ p ∈ innerPlaquettes S F.depth, ‖variationCurl (chartedField w V) v p‖ ^ 2 -
            C₁ * σ * ∑ b ∈ innerBonds S F.depth, ‖v b.1 b.2‖ ^ 2 ≤
          deriv (deriv fun τ : ℝ => minimalAction a S F.depth
            (expRotatedField (fun x i => τ • v x i) (chartedField w V))) 0 ∧
        |deriv (fun τ : ℝ => minimalAction a S F.depth
            (expRotatedField (fun x i => τ • v x i) (chartedField w V))) 0| ≤
          C₁ * σ * ∑ b ∈ innerBonds S F.depth, ‖v b.1 b.2‖) :
    AnalyticAt ℝ (fun τ : ℝ => minimalAction a S F.depth (chartedField (chartLineShift w dw τ) V)) 0 ∧
      ca / 2 * ∑ p ∈ innerPlaquettes S F.depth, ‖variationCurl (chartedField w V) dw p‖ ^ 2 -
          (64 * ca * K ^ 2 + 4 * C₁ + C₁ * K) * (ρ + σ) * chordSqNorm S dw ≤
        deriv (deriv fun τ : ℝ =>
          minimalAction a S F.depth (chartedField (chartLineShift w dw τ) V)) 0 := by
  classical
  have : CompleteSpace imaginaryQuaternions := FiniteDimensional.complete ℝ imaginaryQuaternions
  set W := chartedField w V with hW
  set B := chordBonds S with hB
  let e := B.equivFin
  let c : Fin B.card → F.Site F.depth × Fin 4 := fun l => (e.symm l).1
  have hcB : ∀ l, c l ∈ B := fun l => (e.symm l).2
  have hcinj : Function.Injective c := Subtype.val_injective.comp e.symm.injective
  have hcsurj : ∀ b ∈ B, ∃ l, c l = b := fun b hb => ⟨e ⟨b, hb⟩, by simp [c]⟩
  choose η hηan hη0 hηev hηv hηa using fun l => hcurve (c l) (hcB l)
  let s : ℝ → Fin B.card → imaginaryQuaternions := fun τ l => η l τ
  have hsan : AnalyticAt ℝ s 0 := analyticAt_pi_iff.2 hηan
  have hs0 : s 0 = 0 := funext hη0
  let Φ : (Fin B.card → imaginaryQuaternions) → ℝ :=
    fun ζ => minimalAction a S F.depth (expRotatedField (bondListSpread c ζ) W)
  have hΦ : AnalyticAt ℝ Φ 0 := hAn _ c
  have hfield : ∀ᶠ τ in 𝓝 (0 : ℝ),
      chartedField (chartLineShift w dw τ) V = expRotatedField (bondListSpread c (s τ)) W := by
    filter_upwards [Filter.eventually_all.2 hηev] with τ hτ
    funext x i
    by_cases hb : (x, i) ∈ B
    · obtain ⟨l, hl⟩ := hcsurj _ hb
      have h1 := hτ l
      have hs : bondListSpread c (s τ) x i = η l τ := by
        have := bondListSpread_apply_self hcinj (s τ) l
        rwa [hl] at this
      rw [hl] at h1
      have htree : ¬ IsAxialTreeBond (x, i) := (Finset.mem_filter.1 hb).2
      simp only at h1
      simp only [expRotatedField, hs, hW, chartedField, chartLineShift]
      by_cases hx : IsCrossingBond (x, i)
      · simp only [hx, if_true]
        rw [← mul_assoc, h1]
      · simp only [hx, if_false, htree]
        exact h1.symm
    · have h1 : w x i = 0 := hw (x, i) hb
      have h2 : dw x i = 0 := hdw (x, i) hb
      have hs : bondListSpread c (s τ) x i = 0 :=
        bondListSpread_apply_of_ne _ fun l h => hb (h ▸ hcB l)
      have h3 : expUnit (0 : imaginaryQuaternions) = 1 := Subtype.ext (by simp [expUnit])
      simp only [expRotatedField, hs, h3, one_mul, hW, chartedField, chartLineShift, h1, h2, smul_zero,
        add_zero]
  have hf : (fun τ : ℝ => minimalAction a S F.depth (chartedField (chartLineShift w dw τ) V)) =ᶠ[𝓝 0]
      Φ ∘ s := by
    filter_upwards [hfield] with τ hτ
    simp only [Function.comp, Φ, hτ]
  have hΦ' : AnalyticAt ℝ Φ (s 0) := by rw [hs0]; exact hΦ
  have hcomp : AnalyticAt ℝ (Φ ∘ s) 0 := hΦ'.comp hsan
  refine ⟨hcomp.congr hf.symm, ?_⟩
  rw [hf.deriv.deriv_eq, deriv_deriv_comp_eq_line_add Φ s hΦ hsan hs0]
  obtain ⟨hd1, hd2⟩ := deriv_pi_of_analyticAt η hηan
  have hds : deriv s 0 = fun l => deriv (η l) 0 := hd1
  have hdds : deriv (deriv s) 0 = fun l => deriv (deriv (η l)) 0 := hd2
  set v := bondListSpread c (deriv s 0) with hv
  set z := bondListSpread c (deriv (deriv s) 0) with hz
  have hΦv : (fun τ : ℝ => Φ (τ • deriv s 0)) =
      fun τ : ℝ => minimalAction a S F.depth (expRotatedField (fun x i => τ • v x i) W) := by
    funext τ
    simp only [Φ, bondListSpread_smul, hv]
  have hΦz : (fun τ : ℝ => Φ (τ • deriv (deriv s) 0)) =
      fun τ : ℝ => minimalAction a S F.depth (expRotatedField (fun x i => τ • z x i) W) := by
    funext τ
    simp only [Φ, bondListSpread_smul, hz]
  rw [hΦv, hΦz]
  have hsub : B ⊆ innerBonds S F.depth := Finset.filter_subset _ _
  have hcoff : ∀ b, b ∉ B → ∀ l, c l ≠ (b.1, b.2) := fun b hb l h => hb (by
    have := hcB l
    rwa [h] at this)
  have hvoff : ∀ b, b ∉ B → v b.1 b.2 = 0 := fun b hb => bondListSpread_apply_of_ne _ (hcoff b hb)
  have hzoff : ∀ b, b ∉ B → z b.1 b.2 = 0 := fun b hb => bondListSpread_apply_of_ne _ (hcoff b hb)
  have hvon : ∀ l, v (c l).1 (c l).2 = deriv (η l) 0 := fun l => by
    rw [hv, bondListSpread_apply_self hcinj, hds]
  have hzon : ∀ l, z (c l).1 (c l).2 = deriv (deriv (η l)) 0 := fun l => by
    rw [hz, bondListSpread_apply_self hcinj, hdds]
  obtain ⟨hF2, -⟩ := hFl v fun b hb => hvoff b fun h => hb (hsub h)
  obtain ⟨-, hF1⟩ := hFl z fun b hb => hzoff b fun h => hb (hsub h)
  set Q := chordSqNorm S dw with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun b _ => by positivity
  have hVv : ∑ b ∈ innerBonds S F.depth, ‖v b.1 b.2‖ ^ 2 ≤ 4 * Q := by
    rw [← Finset.sum_subset hsub (fun b _ hb => by rw [hvoff b hb]; simp), hQ, chordSqNorm,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    obtain ⟨l, rfl⟩ := hcsurj b hb
    rw [hvon]
    have h1 := hηv l
    have h2 : K * ‖w (c l).1 (c l).2‖ ≤ 1 :=
      (mul_le_mul_of_nonneg_left (hwρ _ hb) hK.le).trans hKρ
    have h3 : ‖deriv (η l) 0‖ ≤ 2 * ‖dw (c l).1 (c l).2‖ := by
      have h4 : ‖deriv (η l) 0‖ ≤ ‖deriv (η l) 0 - dw (c l).1 (c l).2‖ + ‖dw (c l).1 (c l).2‖ := by
        simpa using norm_add_le (deriv (η l) 0 - dw (c l).1 (c l).2) (dw (c l).1 (c l).2)
      nlinarith [norm_nonneg (dw (c l).1 (c l).2)]
    have h5 : ‖deriv (η l) 0‖ ^ 2 ≤ (2 * ‖dw (c l).1 (c l).2‖) ^ 2 := by gcongr
    nlinarith
  have hZz : ∑ b ∈ innerBonds S F.depth, ‖z b.1 b.2‖ ≤ K * Q := by
    rw [← Finset.sum_subset hsub (fun b _ hb => by rw [hzoff b hb]; simp), hQ, chordSqNorm,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    obtain ⟨l, rfl⟩ := hcsurj b hb
    rw [hzon]
    exact hηa l
  have hE : ∑ b ∈ innerBonds S F.depth, ‖dw b.1 b.2 - v b.1 b.2‖ ^ 2 ≤ K ^ 2 * ρ ^ 2 * Q := by
    rw [← Finset.sum_subset hsub (fun b _ hb => by
        rw [hvoff b hb, hdw b hb]; simp), hQ, chordSqNorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    obtain ⟨l, rfl⟩ := hcsurj b hb
    rw [hvon, norm_sub_rev]
    have h1 := hηv l
    have h2 : ‖deriv (η l) 0 - dw (c l).1 (c l).2‖ ≤ K * ρ * ‖dw (c l).1 (c l).2‖ :=
      h1.trans (by gcongr; exact hwρ _ hb)
    have h3 : ‖deriv (η l) 0 - dw (c l).1 (c l).2‖ ^ 2 ≤ (K * ρ * ‖dw (c l).1 (c l).2‖) ^ 2 := by gcongr
    nlinarith
  have hCd : ∑ p ∈ innerPlaquettes S F.depth, ‖variationCurl W dw p‖ ^ 2 ≤
      2 * ∑ p ∈ innerPlaquettes S F.depth, ‖variationCurl W v p‖ ^ 2 +
        2 * (64 * ∑ b ∈ innerBonds S F.depth, ‖dw b.1 b.2 - v b.1 b.2‖ ^ 2) := by
    have h1 := sum_sq_norm_variationCurl_le S W fun x i => dw x i - v x i
    have h2 : ∑ p ∈ innerPlaquettes S F.depth, ‖variationCurl W dw p‖ ^ 2 ≤
        ∑ p ∈ innerPlaquettes S F.depth, (2 * ‖variationCurl W v p‖ ^ 2 +
          2 * ‖variationCurl W (fun x i => dw x i - v x i) p‖ ^ 2) := by
      refine Finset.sum_le_sum fun p _ => ?_
      have h3 : variationCurl W dw p =
          variationCurl W v p + variationCurl W (fun x i => dw x i - v x i) p := by
        have := pathHolonomyVariation_sub W dw v
          [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] p.1
        simp only [variationCurl]
        rw [← this]
        abel
      rw [h3]
      have h4 := norm_add_le (variationCurl W v p) (variationCurl W (fun x i => dw x i - v x i) p)
      have h5 : ‖variationCurl W v p + variationCurl W (fun x i => dw x i - v x i) p‖ ^ 2 ≤
          (‖variationCurl W v p‖ + ‖variationCurl W (fun x i => dw x i - v x i) p‖) ^ 2 := by gcongr
      nlinarith [sq_nonneg (‖variationCurl W v p‖ - ‖variationCurl W (fun x i => dw x i - v x i) p‖)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h2
    linarith
  exact chart_second_variation_arith ca C₁ K ρ σ Q _ _ _ _ _ _ _ hca hC₁ hK hρ hσ hρ1 hQ0 hVv hZz hE hCd
    hF2 (abs_le.1 hF1).1
theorem chartActionSecondVariation_holds (hA : coldFieldSecondVariationStatement)
    (hC : ExpShiftCurve) : chartActionSecondVariationStatement := by
  intro a ha
  obtain ⟨ca, hca, L₀, hL⟩ := hA a ha
  obtain ⟨K, ρc, hK, hρc, hcurve⟩ := hC
  refine ⟨ca / 2, by positivity, L₀, fun L hodd hL₀ => ?_⟩
  obtain ⟨C₁, σ₁, hC₁, hσ₁, hmain⟩ := hL L hodd hL₀
  refine ⟨64 * ca * K ^ 2 + 4 * C₁ + C₁ * K, min ρc (min 1 (1 / K)), σ₁, by positivity,
    lt_min hρc (lt_min one_pos (by positivity)), hσ₁, ?_⟩
  intro F m S hFL hamb hm hreg ρ σ V w dw hρ hρ₀ hσ hσ₀ _ hw hdw hwρ hcold
  obtain ⟨hAn, hFl⟩ := hmain F m S hFL hamb hm hreg σ (chartedField w V) hσ hσ₀ hcold
  have h1 : ρ ≤ ρc := hρ₀.trans (min_le_left _ _)
  have h2 : ρ ≤ 1 := hρ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : ρ ≤ 1 / K := hρ₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h4 : K * ρ ≤ 1 := by
    rw [le_div_iff₀ hK] at h3
    linarith
  exact second_variation_at_chart_field a ca C₁ K ρ σ hca hC₁ hK hρ hσ h2 h4 S V w dw hw hdw hwρ
    (fun b hb => hcurve _ _ ((hwρ b hb).trans h1)) hAn hFl
end YangMills.Construction.ChartSecondVariation
end
