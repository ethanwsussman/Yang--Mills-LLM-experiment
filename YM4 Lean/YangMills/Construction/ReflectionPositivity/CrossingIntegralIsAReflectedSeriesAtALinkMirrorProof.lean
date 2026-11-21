import YangMills.Construction.InfiniteLattice.EightLoopsRoundAPlaquette
import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfATorusOfAnyShape
import YangMills.Construction.Matrices.GluingFamiliesPreservesProductsOfHaarMeasuresForm
import YangMills.Construction.ReflectionPositivity.CrossingIntegralIsAReflectedSeriesAtALinkMirror
import YangMills.Construction.ReflectionPositivity.GaugeAveragedCrossingIntegral
import YangMills.Construction.ReflectionPositivity.OneReflectionTwoMirrorsAndWhatTheyCut
import YangMills.Construction.ReflectionPositivity.PullBacksOnASplitTorus
import YangMills.Construction.ReflectionPositivity.ReflectedSeriesMultiply
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.ReflectionPositivity.CrossingGaugeAverage YangMills.Construction.ReflectionPositivity.CrossingWeight YangMills.Construction.SpinHarmonics YangMills.Construction.Matrices
open YangMills.Construction.PeriodicLattice (coordVec)
open scoped Matrix ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open NormalFamilies
namespace CrossingReflectionSeries
theorem hasReflectionSeries_of_linkLayer
    (hL : ReflectionPositivity.CrossingGaugeAverage.GaugeAverageStatement)
    (Γ : PeriodSublattice 1) (z : ℤ) (P : NormalLevelPair 1) {β : ℝ} (hβ : 0 < β)
    {S E : Type} [Finite S] [Fintype E] (o t : E → S) (own other : E → Γ.QuotientLink)
    (hown : ∀ e, own e ∈ Γ.plusLinks P.normal z P.level)
    (hθ : ∀ (U : Γ.QuotientField) (e : E),
      Γ.pullbackField P.reflectSymmetry U (own e) = U (other e)) :
    Γ.HasReflectionSeries z P
      (fun U => weightIntegral β o t (fun e => U (own e), fun e => U (other e)))
      (Real.exp (β * (Fintype.card E : ℝ))) := by
  obtain ⟨hα, hsum, hcont, hbound, -, -, hnorm, hunif⟩ := hL β hβ S E o t
  have := (chosenExpansion β).countable
  let Y : Γ.QuotientField → E → ComplexMatrix2.specialUnitary := fun U e => U (own e)
  let Y' : Γ.QuotientField → E → ComplexMatrix2.specialUnitary := fun U e => U (other e)
  let H : (E → (chosenExpansion β).index) → Γ.QuotientField → ℂ :=
    fun γ U => gaugeAveraged (chosenExpansion β) o t γ (Y U)
  have hY : Continuous Y := continuous_pi fun e => continuous_apply _
  have hconj : ∀ γ U, Γ.conjReflect P (H γ) U =
      conj (gaugeAveraged (chosenExpansion β) o t γ (Y' U)) := by
    intro γ U
    change conj (gaugeAveraged (chosenExpansion β) o t γ
      (fun e => Γ.pullbackField P.reflectSymmetry U (own e))) = _
    simp only [hθ]
    rfl
  have hterm : ∀ γ U, (linkCoeff (chosenExpansion β) β γ : ℂ) * H γ U *
      Γ.conjReflect P (H γ) U =
      averagedSummand (chosenExpansion β) β o t γ (Y U, Y' U) := by
    intro γ U
    rw [hconj]
    rfl
  refine ⟨E → (chosenExpansion β).index, inferInstance, linkCoeff (chosenExpansion β) β,
    H, hα, hsum, ?_, ?_, ?_, ?_⟩
  · intro γ
    refine ⟨((hcont γ).comp hY).measurable, ⟨1, fun U => hbound γ _⟩, fun U U' h => ?_⟩
    have hYU : Y U = Y U' := funext fun e => h _ (hown e)
    change gaugeAveraged (chosenExpansion β) o t γ (Y U) =
      gaugeAveraged (chosenExpansion β) o t γ (Y U')
    rw [hYU]
  · intro γ
    exact ciSup_le fun U => hbound γ _
  · intro U
    simp only [hterm]
    exact hnorm _
  · have h := (hasSumUniformlyOn_iff_tendstoUniformlyOn.1 hunif)
    rw [tendstoUniformlyOn_univ] at h
    have h' := TendstoUniformly.comp h (fun U : Γ.QuotientField => (Y U, Y' U))
    have hfun : (fun (s : Finset (E → (chosenExpansion β).index)) U =>
        ∑ γ ∈ s, (linkCoeff (chosenExpansion β) β γ : ℂ) * H γ U *
          Γ.conjReflect P (H γ) U) =
        fun s => (fun x => ∑ i ∈ s, averagedSummand (chosenExpansion β) β o t i x) ∘
          fun U : Γ.QuotientField => (Y U, Y' U) := by
      funext s U
      simp only [hterm, Function.comp]
    rw [hfun]
    exact h'
theorem integral_mul_restrict_compl
    (hJ : SpinHarmonics.GlueMeasurePreserving)
    {C : Type} [Finite C] (A : Set C) (g₁ : (↥A → ComplexMatrix2.specialUnitary) → ℂ)
    (g₂ : (↥Aᶜ → ComplexMatrix2.specialUnitary) → ℂ)
    (h₁ : Continuous g₁) (h₂ : Continuous g₂) :
    ∫ V, g₁ (SpinHarmonics.restrictTo A V) * g₂ (SpinHarmonics.restrictTo Aᶜ V)
      ∂ComplexMatrix2.haarPi C =
      (∫ v, g₁ v ∂ComplexMatrix2.haarPi ↥A) * ∫ w, g₂ w ∂ComplexMatrix2.haarPi ↥Aᶜ := by
  have hm := hJ C A
  have r₁ : Continuous fun V : C → ComplexMatrix2.specialUnitary =>
      SpinHarmonics.restrictTo A V :=
    continuous_pi fun b => continuous_apply (b : C)
  have r₂ : Continuous fun V : C → ComplexMatrix2.specialUnitary =>
      SpinHarmonics.restrictTo Aᶜ V :=
    continuous_pi fun b => continuous_apply (b : C)
  have hc : Continuous fun V : C → ComplexMatrix2.specialUnitary =>
      g₁ (SpinHarmonics.restrictTo A V) * g₂ (SpinHarmonics.restrictTo Aᶜ V) :=
    Continuous.mul (f := fun V => g₁ (SpinHarmonics.restrictTo A V))
      (g := fun V => g₂ (SpinHarmonics.restrictTo Aᶜ V)) (h₁.comp r₁) (h₂.comp r₂)
  rw [← hm.map_eq, integral_map hm.measurable.aemeasurable hc.aestronglyMeasurable]
  have hsplit : ∀ p : (↥A → ComplexMatrix2.specialUnitary) × (↥Aᶜ → ComplexMatrix2.specialUnitary),
      SpinHarmonics.restrictTo A (glue A p.1 p.2) = p.1 ∧
        SpinHarmonics.restrictTo Aᶜ (glue A p.1 p.2) = p.2 := fun p =>
    ⟨funext fun b => glue_of_mem A _ _ b, funext fun b => glue_of_notMem A _ _ b⟩
  simp only [(hsplit _).1, (hsplit _).2]
  exact integral_prod_mul g₁ g₂
def forwardLink (Γ : PeriodSublattice 1) (y : LatticePoint 1) (ν : Fin 4) : Γ.QuotientLink :=
  Γ.linkClass ⟨Link.forwardFrom y ν, ν, add_sub_cancel_left _ _⟩
theorem lift_forwardLink (Γ : PeriodSublattice 1) (U : Γ.QuotientField) (y : LatticePoint 1)
    (ν : Fin 4) : Γ.lift U (Link.forwardFrom y ν) = U (forwardLink Γ y ν) :=
  Γ.lift_apply_positive U ⟨Link.forwardFrom y ν, ν, add_sub_cancel_left _ _⟩
theorem linkEndpoints_forwardLink (Γ : PeriodSublattice 1) (y : LatticePoint 1) (ν : Fin 4) :
    Γ.linkEndpoints (forwardLink Γ y ν) =
      {Γ.quotientMap y, Γ.quotientMap (y + axisStep 1 ν)} := by
  rw [Γ.linkEndpoints_eq, forwardLink, Γ.orientedOfLink_linkClass,
    Γ.sourcePoint_orientedClass, Γ.targetPoint_orientedClass]
  rfl
theorem dotProduct_add_axisStep (n : AmbientSpace) (y : LatticePoint 1) (ν : Fin 4) :
    n ⬝ᵥ ((y + axisStep 1 ν : LatticePoint 1) : AmbientSpace) =
      n ⬝ᵥ (y : AmbientSpace) + n ⬝ᵥ (axisStep 1 ν : AmbientSpace) := by
  change n ⬝ᵥ ((y : AmbientSpace) + (axisStep 1 ν : AmbientSpace)) = _
  rw [dotProduct_add]
theorem coordVec_dotProduct_axisStep_self (μ : Fin 4) :
    coordVec μ ⬝ᵥ (axisStep 1 μ : AmbientSpace) = 1 := by
  simp [coordVec, axisStep]
theorem coordVec_dotProduct_axisStep_of_ne {μ lam : Fin 4} (h : lam ≠ μ) :
    coordVec μ ⬝ᵥ (axisStep 1 lam : AmbientSpace) = 0 := by
  simp [coordVec, axisStep, h]
theorem hasHeight_quotientMap (Γ : PeriodSublattice 1) (n : AmbientSpace) (z : ℤ)
    (y : LatticePoint 1) :
    Γ.HasHeight n z (Γ.quotientMap y) (n ⬝ᵥ (y : AmbientSpace)) :=
  ⟨y, rfl, 0, by simp⟩
theorem exists_sub_eq_of_hasHeight {Γ : PeriodSublattice 1} {n : AmbientSpace} {z : ℤ}
    (hd : ∀ x y : LatticePoint 1, Γ.quotientMap x = Γ.quotientMap y →
      ∃ k : ℤ, n ⬝ᵥ (x : AmbientSpace) - n ⬝ᵥ (y : AmbientSpace) = 2 * (z : ℝ) * (k : ℝ))
    {s : Γ.QuotientTorus} {u u' : ℝ} (h : Γ.HasHeight n z s u) (h' : Γ.HasHeight n z s u') :
    ∃ k : ℤ, u - u' = 2 * (z : ℝ) * (k : ℝ) := by
  obtain ⟨x, hx, k, rfl⟩ := h
  obtain ⟨y, hy, k', rfl⟩ := h'
  obtain ⟨m, hm⟩ := hd x y (hx.trans hy.symm)
  refine ⟨m + k - k', ?_⟩
  push_cast
  linear_combination hm
theorem forwardLink_mem_linksInside_slab (Γ : PeriodSublattice 1) {n : AmbientSpace} {z : ℤ}
    {c₁ c₂ : ℝ} {y : LatticePoint 1}
    {ν : Fin 4} (h0 : n ⬝ᵥ (axisStep 1 ν : AmbientSpace) = 0) (m : ℤ)
    (h₁ : c₁ ≤ n ⬝ᵥ (y : AmbientSpace) + 2 * (z : ℝ) * (m : ℝ))
    (h₂ : n ⬝ᵥ (y : AmbientSpace) + 2 * (z : ℝ) * (m : ℝ) ≤ c₂) :
    forwardLink Γ y ν ∈ Γ.linksInside (Γ.slab n z c₁ c₂) := by
  intro s hs
  change s ∈ Γ.linkEndpoints (forwardLink Γ y ν) at hs
  rw [linkEndpoints_forwardLink] at hs
  rcases hs with rfl | hs
  · exact ⟨_, ⟨y, rfl, m, rfl⟩, h₁, h₂⟩
  · have hs' : s = Γ.quotientMap (y + axisStep 1 ν) := hs
    subst hs'
    refine ⟨_, ⟨y + axisStep 1 ν, rfl, m, rfl⟩, ?_, ?_⟩ <;>
      rw [dotProduct_add_axisStep, h0, add_zero] <;> assumption
theorem re_fullTrace_inv_form
    (hcyc : ∀ g₁ g₂ : ComplexMatrix2.specialUnitary,
      (ComplexMatrix2.fullTrace ((g₁ * g₂ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re =
        (ComplexMatrix2.fullTrace ((g₂ * g₁ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re)
    (hinv : ∀ g₁ : ComplexMatrix2.specialUnitary,
      (ComplexMatrix2.fullTrace ((g₁⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re =
        (ComplexMatrix2.fullTrace (g₁ : ComplexMatrix2)).re)
    (a b c d : ComplexMatrix2.specialUnitary) :
    (ComplexMatrix2.fullTrace
        ((a * b * c⁻¹ * d⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re =
      (ComplexMatrix2.fullTrace
        ((a⁻¹ * d * (c⁻¹)⁻¹ * b⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re := by
  rw [← hinv (a * b * c⁻¹ * d⁻¹)]
  have h : (a * b * c⁻¹ * d⁻¹)⁻¹ = (d * c * b⁻¹) * a⁻¹ := by group
  rw [h, hcyc]
  have h' : a⁻¹ * (d * c * b⁻¹) = a⁻¹ * d * (c⁻¹)⁻¹ * b⁻¹ := by group
  rw [h']
theorem halfIntegerLevel_geometry
    (hT : InfiniteLattice.TwoLevelsOfOneReflection)
    (hW : NormalFamilies.CutPlaquettesOfMirror)
    (hB : InfiniteLattice.SplitTorusPullbacks)
    {β : ℝ} (hβ : 0 < β) (Γ : PeriodSublattice 1) (n : AmbientSpace) (hn : n ∈ normalSet) (z : ℤ)
    (hs : Γ.SplitsAlongWithHalfPeriod n z) (c : ℝ) (hc : IsAllowedLevel 1 n c) (k : ℤ)
    (hk : c = (k : ℝ) + 1 / 2) (P : NormalLevelPair 1) (hP : P = ⟨n, hn, c, hc⟩) :
    ∃ (hz : IsAllowedLevel 1 n (c + (z : ℝ))) (μ : Fin 4), n = coordVec μ ∧
      Γ.crossingLinks n z c =
        {b | ∃ x : LatticePoint 1,
          (Γ.HasHeight n z (Γ.quotientMap x) (c - 1 / 2) ∨
            Γ.HasHeight n z (Γ.quotientMap x) (c + (z : ℝ) - 1 / 2)) ∧
          Γ.orientedOfLink b = Γ.orientedClass (Link.forwardFrom x μ)} ∧
      (∀ q : Γ.QuotientPlaquette, Γ.IsSplitPlaquette n z c q ↔
        Γ.HasVertexHeightsAround n z q c ∨ Γ.HasVertexHeightsAround n z q (c + (z : ℝ))) ∧
      ∀ Q : NormalLevelPair 1, (Q = P ∨ Q = ⟨n, hn, c + (z : ℝ), hz⟩) →
        ∀ q : Γ.QuotientPlaquette,
        Γ.HasVertexHeightsAround n z q Q.level →
        ∃ (x : LatticePoint 1) (lam : Fin 4), lam ≠ μ ∧
          n ⬝ᵥ (x : AmbientSpace) = Q.level - 1 / 2 ∧
          (∀ U : Γ.QuotientField, Γ.quotientFaceEnergy U q =
            1 - (1 / 2) * (ComplexMatrix2.fullTrace ((U (forwardLink Γ x μ) *
              U (forwardLink Γ (x + axisStep 1 μ) lam) *
                (U (forwardLink Γ (x + axisStep 1 lam) μ))⁻¹ *
                (U (forwardLink Γ x lam))⁻¹ : ComplexMatrix2.specialUnitary) :
                  ComplexMatrix2)).re) ∧
          (∀ U : Γ.QuotientField,
            Γ.pullbackField P.reflectSymmetry U (forwardLink Γ x lam) =
              U (forwardLink Γ (x + axisStep 1 μ) lam)) ∧
          ∀ U : Γ.QuotientField,
            Γ.pullbackField P.reflectSymmetry U (forwardLink Γ (x + axisStep 1 μ) lam) =
              U (forwardLink Γ x lam) := by
  subst hP
  obtain ⟨hz, -, -, hb, -, -, -, -, -, hd, hlift, hext⟩ := hT Γ n hn z c hc hs
  obtain ⟨μ, hμ, -, hcross, -, hcut, hl⟩ := hb ⟨k, hk⟩
  refine ⟨hz, μ, hμ, hcross, hcut, ?_⟩
  intro Q hQ q hq
  have hQn : Q.normal = n := by rcases hQ with rfl | rfl <;> rfl
  have hQpos : ∃ k' : ℤ, Q.level = (k' : ℝ) + 1 / 2 := by
    rcases hQ with rfl | rfl
    · exact ⟨k, hk⟩
    · refine ⟨k + z, ?_⟩
      change c + (z : ℝ) = _
      push_cast
      rw [hk]
      ring
  obtain ⟨p, x, lam, hp, hcutby⟩ := hl Q hQ q hq
  obtain ⟨hlam, hcorn, hheight, -⟩ := id hcutby
  have hform := (hd Q hQ).2 μ hμ ⟨k, hk⟩ p x lam hcutby
  obtain ⟨hact, -, -, -⟩ := hlift q p hp
  have hmap := (((hW Q).2.2 μ (hQn.trans hμ) hQpos p).2 x lam hlam hcorn hheight).1
  have hinvol := ((hB β hβ Γ n hn z hs).1 c hc).1
  have hQext : ∀ U : Γ.QuotientField, Q.reflectSymmetry.pullbackField
      (Γ.lift U) = Γ.lift (Γ.pullbackField
        (NormalLevelPair.reflectSymmetry ⟨n, hn, c, hc⟩) U) := by
    intro U
    rcases hQ with rfl | rfl
    · exact (hext U).2
    · exact (hext U).1.trans (hext U).2
  have hstep : ∀ U : Γ.QuotientField,
      Γ.pullbackField (NormalLevelPair.reflectSymmetry ⟨n, hn, c, hc⟩) U
        (forwardLink Γ x lam) = U (forwardLink Γ (x + axisStep 1 μ) lam) := by
    intro U
    rw [← lift_forwardLink Γ (Γ.pullbackField
      (NormalLevelPair.reflectSymmetry ⟨n, hn, c, hc⟩) U) x lam, ← hQext]
    change Γ.lift U (Q.reflectSymmetry.linkMap (Link.forwardFrom x lam)) = _
    rw [hmap, lift_forwardLink]
  refine ⟨x, lam, hlam, ?_, ?_, hstep, ?_⟩
  · rw [← hQn]
    exact hheight
  · intro U
    rw [hact U, hform U]
    simp only [crossingHolonomy, lift_forwardLink]
  · intro U
    have h := hstep (Γ.pullbackField (NormalLevelPair.reflectSymmetry ⟨n, hn, c, hc⟩) U)
    rw [hinvol U] at h
    exact h.symm
theorem finsum_split_eq_sum_add_sum (Γ : PeriodSublattice 1) [Finite Γ.QuotientPlaquette]
    {n : AmbientSpace} {z : ℤ} {c : ℝ}
    (T₁ T₂ : Set Γ.QuotientPlaquette) [Fintype ↥T₁] [Fintype ↥T₂]
    (hcut : ∀ q, Γ.IsSplitPlaquette n z c q ↔ q ∈ T₁ ∨ q ∈ T₂) (hdis : Disjoint T₁ T₂)
    (f : Γ.QuotientPlaquette → ℝ) :
    ∑ᶠ (p : Γ.QuotientPlaquette) (_ : Γ.IsSplitPlaquette n z c p), f p =
      ∑ q : ↥T₁, f q + ∑ q : ↥T₂, f q := by
  have hset : {p | Γ.IsSplitPlaquette n z c p} = T₁ ∪ T₂ := Set.ext hcut
  have h : ∑ᶠ (p : Γ.QuotientPlaquette) (_ : Γ.IsSplitPlaquette n z c p), f p =
      ∑ᶠ p ∈ {p | Γ.IsSplitPlaquette n z c p}, f p := rfl
  rw [h, hset, finsum_mem_union hdis (Set.toFinite _) (Set.toFinite _),
    ← finsum_set_coe_eq_finsum_mem T₁, ← finsum_set_coe_eq_finsum_mem T₂,
    finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
theorem numSplitPlaquettes_eq_card_add_card (Γ : PeriodSublattice 1)
    [Finite Γ.QuotientPlaquette] {n : AmbientSpace} {z : ℤ} {c : ℝ}
    (T₁ T₂ : Set Γ.QuotientPlaquette) [Fintype ↥T₁] [Fintype ↥T₂]
    (hcut : ∀ q, Γ.IsSplitPlaquette n z c q ↔ q ∈ T₁ ∨ q ∈ T₂) (hdis : Disjoint T₁ T₂) :
    Γ.numSplitPlaquettes n z c = Fintype.card ↥T₁ + Fintype.card ↥T₂ := by
  have hset : {p | Γ.IsSplitPlaquette n z c p} = T₁ ∪ T₂ := Set.ext hcut
  change Nat.card ↥{p | Γ.IsSplitPlaquette n z c p} = _
  rw [hset, Nat.card_coe_set_eq, Set.ncard_union_eq hdis (Set.toFinite _) (Set.toFinite _),
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
theorem continuous_re_fullTrace :
    Continuous fun g : ComplexMatrix2.specialUnitary =>
      (ComplexMatrix2.fullTrace (g : ComplexMatrix2)).re :=
  Complex.continuous_re.comp (Continuous.matrix_trace continuous_subtype_val)
theorem continuous_linkWeight {E : Type} [Fintype E] (β : ℝ)
    (X₂ : E → ComplexMatrix2.specialUnitary) :
    Continuous fun X₁ : E → ComplexMatrix2.specialUnitary => linkWeight β X₁ X₂ := by
  refine continuous_finsetProd _ fun b _ => Real.continuous_exp.comp ?_
  refine continuous_const.add (continuous_const.mul (continuous_re_fullTrace.comp ?_))
  exact (continuous_apply b).mul continuous_const
theorem continuous_gaugeAct {S E : Type} (o t : E → S) (X : E → ComplexMatrix2.specialUnitary) :
    Continuous fun W : S → ComplexMatrix2.specialUnitary => gaugeAct o t W X :=
  continuous_pi fun b =>
    ((continuous_apply (o b)).mul continuous_const).mul (continuous_apply (t b)).inv
theorem integrateOut_eq_mul_of_two_layers
    (hJ : SpinHarmonics.GlueMeasurePreserving)
    (hL : ReflectionPositivity.CrossingGaugeAverage.GaugeAverageStatement)
    (hcyc : ∀ g₁ g₂ : ComplexMatrix2.specialUnitary,
      (ComplexMatrix2.fullTrace ((g₁ * g₂ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re =
        (ComplexMatrix2.fullTrace ((g₂ * g₁ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re)
    (hinv : ∀ g₁ : ComplexMatrix2.specialUnitary,
      (ComplexMatrix2.fullTrace ((g₁⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re =
        (ComplexMatrix2.fullTrace (g₁ : ComplexMatrix2)).re)
    (Γ : PeriodSublattice 1) [Finite Γ.QuotientLink] {β : ℝ} (hβ : 0 < β)
    (C : Set Γ.QuotientLink)
    (A : Set ↥C) {E₁ E₂ : Type} [Fintype E₁] [Fintype E₂]
    (o₁ t₁ : E₁ → ↥A) (o₂ t₂ : E₂ → ↥Aᶜ) (up₁ lo₁ : E₁ → Γ.QuotientLink)
    (up₂ lo₂ : E₂ → Γ.QuotientLink)
    (hup₁ : ∀ e, up₁ e ∉ C) (hlo₁ : ∀ e, lo₁ e ∉ C) (hup₂ : ∀ e, up₂ e ∉ C) (hlo₂ : ∀ e, lo₂ e ∉ C)
    (w : Γ.QuotientField → ℝ)
    (hw : ∀ U, w U =
      (∏ e, Real.exp (-β + β / 2 * (ComplexMatrix2.fullTrace ((U (o₁ e).1.1 * U (up₁ e) *
        (U (t₁ e).1.1)⁻¹ * (U (lo₁ e))⁻¹ : ComplexMatrix2.specialUnitary) :
          ComplexMatrix2)).re)) *
      ∏ e, Real.exp (-β + β / 2 * (ComplexMatrix2.fullTrace ((U (o₂ e).1.1 * U (up₂ e) *
        (U (t₂ e).1.1)⁻¹ * (U (lo₂ e))⁻¹ : ComplexMatrix2.specialUnitary) :
          ComplexMatrix2)).re)) :
    Γ.integrateOut C (fun U => (w U : ℂ)) =
      (fun U => weightIntegral β o₁ t₁ (fun e => U (up₁ e), fun e => U (lo₁ e))) *
        fun U => weightIntegral β o₂ t₂ (fun e => U (lo₂ e), fun e => U (up₂ e)) := by
  funext U
  let g₁ : (↥A → ComplexMatrix2.specialUnitary) → ℂ := fun v =>
    (linkWeight β (gaugeAct o₁ t₁ v fun e => U (up₁ e)) (fun e => U (lo₁ e)) : ℂ)
  let g₂ : (↥Aᶜ → ComplexMatrix2.specialUnitary) → ℂ := fun v =>
    (linkWeight β (gaugeAct o₂ t₂ v⁻¹ fun e => U (lo₂ e)) (fun e => U (up₂ e)) : ℂ)
  have hg₁ : Continuous g₁ := Complex.continuous_ofReal.comp
    ((continuous_linkWeight β _).comp (continuous_gaugeAct o₁ t₁ _))
  have hg₂ : Continuous g₂ := Complex.continuous_ofReal.comp
    ((continuous_linkWeight β _).comp ((continuous_gaugeAct o₂ t₂ _).comp continuous_inv))
  have hpt : ∀ V : ↥C → ComplexMatrix2.specialUnitary,
      (w (glue C V (SpinHarmonics.restrictTo Cᶜ U)) : ℂ) =
        g₁ (SpinHarmonics.restrictTo A V) * g₂ (SpinHarmonics.restrictTo Aᶜ V) := by
    intro V
    have hin : ∀ b : ↥C, glue C V (SpinHarmonics.restrictTo Cᶜ U) b = V b :=
      fun b => glue_of_mem C V _ b
    have hout : ∀ b (hb : b ∉ C), glue C V (SpinHarmonics.restrictTo Cᶜ U) b = U b :=
      fun b hb => glue_of_notMem C V (SpinHarmonics.restrictTo Cᶜ U) ⟨b, hb⟩
    have e₁ : (∏ e, Real.exp (-β + β / 2 * (ComplexMatrix2.fullTrace
        ((glue C V (SpinHarmonics.restrictTo Cᶜ U) (o₁ e).1.1 *
          glue C V (SpinHarmonics.restrictTo Cᶜ U) (up₁ e) *
          (glue C V (SpinHarmonics.restrictTo Cᶜ U) (t₁ e).1.1)⁻¹ *
          (glue C V (SpinHarmonics.restrictTo Cᶜ U) (lo₁ e))⁻¹ :
            ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re)) =
        linkWeight β (gaugeAct o₁ t₁ (SpinHarmonics.restrictTo A V) fun e => U (up₁ e))
          (fun e => U (lo₁ e)) := by
      unfold linkWeight gaugeAct
      refine Finset.prod_congr rfl fun e _ => ?_
      rw [hin, hin, hout _ (hup₁ e), hout _ (hlo₁ e)]
      rfl
    have e₂ : (∏ e, Real.exp (-β + β / 2 * (ComplexMatrix2.fullTrace
        ((glue C V (SpinHarmonics.restrictTo Cᶜ U) (o₂ e).1.1 *
          glue C V (SpinHarmonics.restrictTo Cᶜ U) (up₂ e) *
          (glue C V (SpinHarmonics.restrictTo Cᶜ U) (t₂ e).1.1)⁻¹ *
          (glue C V (SpinHarmonics.restrictTo Cᶜ U) (lo₂ e))⁻¹ :
            ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re)) =
        linkWeight β (gaugeAct o₂ t₂ (SpinHarmonics.restrictTo Aᶜ V)⁻¹ fun e => U (lo₂ e))
          (fun e => U (up₂ e)) := by
      unfold linkWeight gaugeAct
      refine Finset.prod_congr rfl fun e _ => ?_
      rw [hin, hin, hout _ (hup₂ e), hout _ (hlo₂ e), re_fullTrace_inv_form hcyc hinv]
      rfl
    rw [hw, e₁, e₂, Complex.ofReal_mul]
  have hsecond := (hL β hβ ↥Aᶜ E₂ o₂ t₂).2.2.2.2.1
  change ∫ V, (w (glue C V (SpinHarmonics.restrictTo Cᶜ U)) : ℂ) ∂ComplexMatrix2.haarPi ↥C = _
  simp only [hpt]
  rw [integral_mul_restrict_compl hJ A g₁ g₂ hg₁ hg₂, Pi.mul_apply, hsecond]
  rfl
theorem neg_ne_two_mul_mul {z : ℤ} (hz : 2 ≤ z) (k : ℤ) (h : -(z : ℝ) = 2 * (z : ℝ) * (k : ℝ)) :
    False := by
  have h' : -z = 2 * z * k := by exact_mod_cast h
  have h0 : z * (1 + 2 * k) = 0 := by linarith
  rcases mul_eq_zero.1 h0 with h1 | h1 <;> omega
theorem neg_sub_one_ne_two_mul_mul {z : ℤ} (hz : 2 ≤ z) (k : ℤ)
    (h : -(z : ℝ) - 1 = 2 * (z : ℝ) * (k : ℝ)) : False := by
  have h' : -z - 1 = 2 * z * k := by exact_mod_cast h
  rcases le_or_gt 0 k with hk | hk
  · nlinarith
  · have hk' : k ≤ -1 := by omega
    nlinarith
def facesSplitAt (Γ : PeriodSublattice 1) (n : AmbientSpace) (z : ℤ) (u : ℝ) :
    Set Γ.QuotientPlaquette :=
  {q | Γ.HasVertexHeightsAround n z q u}
theorem disjoint_facesSplitAt {Γ : PeriodSublattice 1} {n : AmbientSpace} {z : ℤ} (hz : 2 ≤ z)
    (hd : ∀ x y : LatticePoint 1, Γ.quotientMap x = Γ.quotientMap y →
      ∃ k : ℤ, n ⬝ᵥ (x : AmbientSpace) - n ⬝ᵥ (y : AmbientSpace) = 2 * (z : ℝ) * (k : ℝ))
    (c : ℝ) :
    Disjoint (facesSplitAt Γ n z c) (facesSplitAt Γ n z (c + (z : ℝ))) := by
  refine Set.disjoint_left.2 fun q h₁ h₂ => ?_
  obtain ⟨-, ⟨s, hs, hat⟩, -⟩ := h₁
  rcases h₂.1 s hs with h | h
  · obtain ⟨k, hk⟩ := exists_sub_eq_of_hasHeight hd hat h
    exact neg_ne_two_mul_mul hz k (by linarith)
  · obtain ⟨k, hk⟩ := exists_sub_eq_of_hasHeight hd hat h
    exact neg_sub_one_ne_two_mul_mul hz k (by linarith)
def layerCrossingLinks (Γ : PeriodSublattice 1) (n : AmbientSpace) (z : ℤ) (c : ℝ) (μ : Fin 4)
    (C : Set Γ.QuotientLink) : Set ↥C :=
  {b | ∃ x : LatticePoint 1, Γ.HasHeight n z (Γ.quotientMap x) (c - 1 / 2) ∧
    Γ.orientedOfLink b.1 = Γ.orientedClass (Link.forwardFrom x μ)}
theorem orientedOfLink_forwardLink (Γ : PeriodSublattice 1) (y : LatticePoint 1) (ν : Fin 4) :
    Γ.orientedOfLink (forwardLink Γ y ν) = Γ.orientedClass (Link.forwardFrom y ν) :=
  Γ.orientedOfLink_linkClass ⟨Link.forwardFrom y ν, ν, add_sub_cancel_left _ _⟩
theorem not_mem_layerCrossingLinks {Γ : PeriodSublattice 1} {n : AmbientSpace} {z : ℤ}
    (hz : 2 ≤ z)
    (hd : ∀ x y : LatticePoint 1, Γ.quotientMap x = Γ.quotientMap y →
      ∃ k : ℤ, n ⬝ᵥ (x : AmbientSpace) - n ⬝ᵥ (y : AmbientSpace) = 2 * (z : ℝ) * (k : ℝ))
    {c : ℝ} {μ : Fin 4} {C : Set Γ.QuotientLink} {y : LatticePoint 1}
    (hy : Γ.HasHeight n z (Γ.quotientMap y) (c + (z : ℝ) - 1 / 2))
    (hC : forwardLink Γ y μ ∈ C) :
    (⟨forwardLink Γ y μ, hC⟩ : ↥C) ∉ layerCrossingLinks Γ n z c μ C := by
  rintro ⟨x, hx, heq⟩
  change Γ.orientedOfLink (forwardLink Γ y μ) = _ at heq
  rw [orientedOfLink_forwardLink] at heq
  obtain ⟨γ, hγ, hb⟩ := Γ.mem_orientedOrbit_of_orientedClass_eq heq
  have hxy : x = y + γ := congrArg Link.initial hb
  have hproj : Γ.quotientMap x = Γ.quotientMap y := by
    rw [hxy]
    exact Γ.quotientMap_add_period y hγ
  rw [hproj] at hx
  obtain ⟨k, hk⟩ := exists_sub_eq_of_hasHeight hd hx hy
  exact neg_ne_two_mul_mul hz k (by linarith)
theorem crossingIntegral_reflectionSeries
    (hT : InfiniteLattice.TwoLevelsOfOneReflection)
    (hW : NormalFamilies.CutPlaquettesOfMirror)
    (hB : InfiniteLattice.SplitTorusPullbacks)
    (hD : InfiniteLattice.SplitTorusDescent)
    (hL : ReflectionPositivity.CrossingGaugeAverage.GaugeAverageStatement)
    (hE : InfiniteLattice.PeriodicQuotient.FinitenessClaim)
    (hH : InfiniteLattice.PlaquetteLoopTraces)
    (hM : InfiniteLattice.ReflectionSeriesMul)
    (hJ : SpinHarmonics.GlueMeasurePreserving) :
    InfiniteLattice.CrossingIntegralReflectionSeriesHalfInteger := by
  intro β hβ Γ n hn z hs c hc ⟨k, hk⟩ P
  classical
  have hfin := hE.1 Γ
  have : Finite Γ.QuotientLink := hfin.finite_quotientLink
  have : Finite Γ.QuotientPlaquette := hfin.finite_quotientPlaquette
  obtain ⟨hz, μ, hμ, hcross, hcut, hdata⟩ :=
    halfIntegerLevel_geometry hT hW hB hβ Γ n hn z hs c hc k hk P rfl
  have hdesc := (hD Γ n hn z c hc 0 hs).2.2.2.1
  have hz2 : (2 : ℤ) ≤ z := hs.2.1
  have hz2r : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
  have hcyc := hH.2.1
  have hinv := hH.2.2.1
  obtain ⟨C, hC⟩ : ∃ C, C = Γ.crossingLinks n z c := ⟨_, rfl⟩
  rw [← hC] at hcross ⊢
  let T₁ := facesSplitAt Γ n z c
  let T₂ := facesSplitAt Γ n z (c + (z : ℝ))
  let _ : Fintype ↥T₁ := Fintype.ofFinite _
  let _ : Fintype ↥T₂ := Fintype.ofFinite _
  have hdis : Disjoint T₁ T₂ := disjoint_facesSplitAt hz2 hdesc c
  have hcut' : ∀ q, Γ.IsSplitPlaquette n z c q ↔ q ∈ T₁ ∨ q ∈ T₂ := hcut
  have hd₁ := fun q : ↥T₁ => hdata P (Or.inl rfl) q.1 q.2
  have hd₂ := fun q : ↥T₂ => hdata ⟨n, hn, c + (z : ℝ), hz⟩ (Or.inr rfl) q.1 q.2
  choose x₁ lam₁ hlam₁ hh₁ hf₁ hB₁ hC₁ using hd₁
  choose x₂ lam₂ hlam₂ hh₂ hf₂ hB₂ hC₂ using hd₂
  have hh₁' : ∀ q, n ⬝ᵥ (x₁ q : AmbientSpace) = c - 1 / 2 := hh₁
  have hh₂' : ∀ q, n ⬝ᵥ (x₂ q : AmbientSpace) = c + (z : ℝ) - 1 / 2 := hh₂
  have hsμ : n ⬝ᵥ (axisStep 1 μ : AmbientSpace) = 1 := by
    rw [hμ]
    exact coordVec_dotProduct_axisStep_self μ
  have hsl : ∀ lam : Fin 4, lam ≠ μ → n ⬝ᵥ (axisStep 1 lam : AmbientSpace) = 0 := by
    intro lam h
    rw [hμ]
    exact coordVec_dotProduct_axisStep_of_ne h
  have hat : ∀ (y : LatticePoint 1) (u : ℝ), n ⬝ᵥ (y : AmbientSpace) = u →
      Γ.HasHeight n z (Γ.quotientMap y) u := by
    intro y u h
    rw [← h]
    exact hasHeight_quotientMap Γ n z y
  have hCmem : ∀ y : LatticePoint 1, (Γ.HasHeight n z (Γ.quotientMap y) (c - 1 / 2) ∨
      Γ.HasHeight n z (Γ.quotientMap y) (c + (z : ℝ) - 1 / 2)) → forwardLink Γ y μ ∈ C := by
    intro y h
    rw [hcross]
    exact ⟨y, h, orientedOfLink_forwardLink Γ y μ⟩
  have hnotU : ∀ b, b ∈ Γ.plusLinks n z c → b ∉ C := by
    intro b hb hbC
    rw [hC] at hbC
    exact hbC (Or.inl hb)
  have hnotL : ∀ b, b ∈ Γ.minusLinks n z c → b ∉ C := by
    intro b hb hbC
    rw [hC] at hbC
    exact hbC (Or.inr hb)
  have hx₁ : ∀ q, Γ.HasHeight n z (Γ.quotientMap (x₁ q)) (c - 1 / 2) :=
    fun q => hat _ _ (hh₁' q)
  have hy₁ : ∀ q, Γ.HasHeight n z (Γ.quotientMap (x₁ q + axisStep 1 (lam₁ q))) (c - 1 / 2) :=
    fun q => hat _ _ (by rw [dotProduct_add_axisStep, hh₁', hsl _ (hlam₁ q), add_zero])
  have hx₂ : ∀ q, Γ.HasHeight n z (Γ.quotientMap (x₂ q)) (c + (z : ℝ) - 1 / 2) :=
    fun q => hat _ _ (hh₂' q)
  have hy₂ : ∀ q, Γ.HasHeight n z (Γ.quotientMap (x₂ q + axisStep 1 (lam₂ q)))
      (c + (z : ℝ) - 1 / 2) :=
    fun q => hat _ _ (by rw [dotProduct_add_axisStep, hh₂', hsl _ (hlam₂ q), add_zero])
  have hCx₁ := fun q => hCmem _ (Or.inl (hx₁ q))
  have hCy₁ := fun q => hCmem _ (Or.inl (hy₁ q))
  have hCx₂ := fun q => hCmem _ (Or.inr (hx₂ q))
  have hCy₂ := fun q => hCmem _ (Or.inr (hy₂ q))
  let A := layerCrossingLinks Γ n z c μ C
  let o₁ : ↥T₁ → ↥A := fun q => ⟨⟨_, hCx₁ q⟩, x₁ q, hx₁ q, orientedOfLink_forwardLink Γ _ μ⟩
  let t₁ : ↥T₁ → ↥A := fun q => ⟨⟨_, hCy₁ q⟩, _, hy₁ q, orientedOfLink_forwardLink Γ _ μ⟩
  let o₂ : ↥T₂ → ↥Aᶜ := fun q =>
    ⟨⟨_, hCx₂ q⟩, not_mem_layerCrossingLinks hz2 hdesc (hx₂ q) (hCx₂ q)⟩
  let t₂ : ↥T₂ → ↥Aᶜ := fun q =>
    ⟨⟨_, hCy₂ q⟩, not_mem_layerCrossingLinks hz2 hdesc (hy₂ q) (hCy₂ q)⟩
  let up₁ : ↥T₁ → Γ.QuotientLink := fun q => forwardLink Γ (x₁ q + axisStep 1 μ) (lam₁ q)
  let lo₁ : ↥T₁ → Γ.QuotientLink := fun q => forwardLink Γ (x₁ q) (lam₁ q)
  let up₂ : ↥T₂ → Γ.QuotientLink := fun q => forwardLink Γ (x₂ q + axisStep 1 μ) (lam₂ q)
  let lo₂ : ↥T₂ → Γ.QuotientLink := fun q => forwardLink Γ (x₂ q) (lam₂ q)
  have hup₁ : ∀ q, up₁ q ∈ Γ.plusLinks n z c := fun q =>
    forwardLink_mem_linksInside_slab Γ (hsl _ (hlam₁ q)) 0
      (by rw [dotProduct_add_axisStep, hh₁', hsμ]; push_cast; linarith)
      (by rw [dotProduct_add_axisStep, hh₁', hsμ]; push_cast; linarith)
  have hlo₁ : ∀ q, lo₁ q ∈ Γ.minusLinks n z c := fun q =>
    forwardLink_mem_linksInside_slab Γ (hsl _ (hlam₁ q)) 1
      (by rw [hh₁']; push_cast; linarith)
      (by rw [hh₁']; push_cast; linarith)
  have hup₂ : ∀ q, up₂ q ∈ Γ.minusLinks n z c := fun q =>
    forwardLink_mem_linksInside_slab Γ (hsl _ (hlam₂ q)) 0
      (by rw [dotProduct_add_axisStep, hh₂', hsμ]; push_cast; linarith)
      (by rw [dotProduct_add_axisStep, hh₂', hsμ]; push_cast; linarith)
  have hlo₂ : ∀ q, lo₂ q ∈ Γ.plusLinks n z c := fun q =>
    forwardLink_mem_linksInside_slab Γ (hsl _ (hlam₂ q)) 0
      (by rw [hh₂']; push_cast; linarith)
      (by rw [hh₂']; push_cast; linarith)
  have S₁ := hasReflectionSeries_of_linkLayer hL Γ z P hβ o₁ t₁ up₁ lo₁ hup₁ (fun U q => hC₁ q U)
  have S₂ := hasReflectionSeries_of_linkLayer hL Γ z P hβ o₂ t₂ lo₂ up₂ hlo₂ (fun U q => hB₂ q U)
  have hprod := (hM Γ z P).2.1 _ _ _ _ S₁ S₂
  have hr : ∀ r : ℝ, -β * (1 - 1 / 2 * r) = -β + β / 2 * r := fun r => by ring
  have heq := integrateOut_eq_mul_of_two_layers hJ hL hcyc hinv Γ hβ C A o₁ t₁ o₂ t₂
    up₁ lo₁ up₂ lo₂
    (fun q => hnotU _ (hup₁ q)) (fun q => hnotL _ (hlo₁ q))
    (fun q => hnotL _ (hup₂ q)) (fun q => hnotU _ (hlo₂ q))
    (Γ.splitFaceWeight β n z c) (by
      intro U
      rw [PeriodSublattice.splitFaceWeight, finsum_split_eq_sum_add_sum Γ T₁ T₂ hcut' hdis,
        mul_add, Real.exp_add, Finset.mul_sum, Finset.mul_sum, Real.exp_sum, Real.exp_sum]
      congr 1
      · refine Finset.prod_congr rfl fun q _ => ?_
        rw [hf₁ q U]
        exact congrArg Real.exp (hr _)
      · refine Finset.prod_congr rfl fun q _ => ?_
        rw [hf₂ q U]
        exact congrArg Real.exp (hr _))
  have hnum : Real.exp (β * (Γ.numSplitPlaquettes n z c : ℝ)) =
      Real.exp (β * (Fintype.card ↥T₁ : ℝ)) * Real.exp (β * (Fintype.card ↥T₂ : ℝ)) := by
    rw [numSplitPlaquettes_eq_card_add_card Γ T₁ T₂ hcut' hdis, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hnum, heq]
  exact hprod
end CrossingReflectionSeries
end YangMills.Construction.InfiniteLattice
