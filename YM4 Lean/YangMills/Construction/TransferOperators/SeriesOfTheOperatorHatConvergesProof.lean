import YangMills.Construction.Matrices.CalculusOfTheFieldsOnPowersOfGProof
import YangMills.Construction.TransferOperators.ComponentFunctionsOfTheProjectionsProof
import YangMills.Construction.TransferOperators.DoubleTermsOfTheOperatorHat
import YangMills.Construction.TransferOperators.RapidDecayGivesASmoothFunctionProof
import YangMills.Construction.TransferOperators.SeriesOfTheOperatorHatConverges
import YangMills.Construction.TransferOperators.SmoothFunctionsDecayRapidly
import YangMills.Construction.TransferOperators.TermsOfTheOperatorHatAsSeriesOfDoubleTerms
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open MeasureTheory Filter Matrices.ComplexMatrix2
open scoped ENNReal
noncomputable section
namespace SpinHarmonics
namespace HatSeries
theorem countable_halfNatural : Countable HalfNatural := by apply _root_.YangMills.Construction.SpinHarmonics.SmoothFromDecay.countable_halfNatural <;> assumption
theorem rightField_mem_smoothSet {J : Type} {G : (J → specialUnitary) → ℂ} (hG : G ∈ smoothSet)
    (b : J) (i : Fin 3) : rightField b i G ∈ smoothSet := by apply _root_.YangMills.Construction.SpinHarmonics.FieldCalculus.rightField_mem_smoothSet <;> assumption
theorem fieldWord_mem_smoothSet {J : Type} {G : (J → specialUnitary) → ℂ} (hG : G ∈ smoothSet)
    (w : List (J × Fin 3)) : fieldWord w G ∈ smoothSet := by
  induction w with
  | nil => exact hG
  | cons p w ih => exact rightField_mem_smoothSet ih p.1 p.2
theorem continuous_of_mem_smoothSet {J : Type} {G : (J → specialUnitary) → ℂ}
    (hG : G ∈ smoothSet) : Continuous G :=
  Set.mem_iInter.1 hG 0
theorem norm_le_supNorm {J : Type} [Finite J] {G : (J → specialUnitary) → ℂ} (hG : Continuous G)
    (u : J → specialUnitary) : ‖G u‖ ≤ supNorm G :=
  le_ciSup (f := fun u => ‖G u‖) (isCompact_range hG.norm).bddAbove u
theorem toHaarL2_eq_toLp {J : Type} [Finite J] (G : C(J → specialUnitary, ℂ)) :
    toHaarL2 (G : (J → specialUnitary) → ℂ) = ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ G := by apply _root_.YangMills.Construction.SpinHarmonics.IsotypicPartSums.toHaarL2_continuousMap <;> assumption
theorem degreeCompatible_finite_card_le {B : Type} [Finite B] (D : B → ℕ) (l' : B → HalfNatural) :
    {l : B → HalfNatural | IsDegreeCompatible D l l'}.Finite ∧
      {l : B → HalfNatural | IsDegreeCompatible D l l'}.ncard ≤ ∏ᶠ b, (2 * D b + 1) := by
  classical
  let _ : Fintype B := Fintype.ofFinite B
  have key : ∀ l : B → HalfNatural, IsDegreeCompatible D l l' → ∀ b,
      (l' b).doubled ≤ (l b).doubled + D b ∧ (l b).doubled + D b - (l' b).doubled < 2 * D b + 1 := by
    intro l hl b
    have h := abs_le.1 (hl b)
    simp only [HalfNatural.toReal] at h
    have h₁ : ((l' b).doubled : ℝ) ≤ (l b).doubled + D b := by linarith [h.2]
    have h₂ : ((l b).doubled : ℝ) ≤ (l' b).doubled + D b := by linarith [h.1]
    have h₁' : (l' b).doubled ≤ (l b).doubled + D b := by exact_mod_cast h₁
    have h₂' : (l b).doubled ≤ (l' b).doubled + D b := by exact_mod_cast h₂
    exact ⟨h₁', by omega⟩
  let S : Set (B → HalfNatural) := {l | IsDegreeCompatible D l l'}
  let g : S → ∀ b, Fin (2 * D b + 1) := fun l b =>
    ⟨(l.1 b).doubled + D b - (l' b).doubled, (key l.1 l.2 b).2⟩
  have hg : Function.Injective g := by
    intro x y hxy
    refine Subtype.ext (funext fun b => ?_)
    have h := congrArg Fin.val (congrFun hxy b)
    have hx := (key x.1 x.2 b).1
    have hy := (key y.1 y.2 b).1
    simp only [g] at h
    have ht : (x.1 b).doubled = (y.1 b).doubled := by omega
    cases hxb : x.1 b
    cases hyb : y.1 b
    simp_all
  have : Finite S := Finite.of_injective g hg
  refine ⟨Set.toFinite S, ?_⟩
  rw [← Nat.card_coe_set_eq]
  calc Nat.card S ≤ Nat.card (∀ b, Fin (2 * D b + 1)) := Nat.card_le_card_of_injective g hg
    _ = ∏ᶠ b, (2 * D b + 1) := by
      simp [finprod_eq_prod_of_fintype]
theorem restrictTo_glue {A : Type*} {J : Type} (B : Set J) (v : ↥B → A) (z : ↥Bᶜ → A) :
    restrictTo B (glue B v z) = v :=
  congrArg Prod.fst ((splitEquiv (X := A) B).right_inv (v, z))
def pairEmbed {J : Type} (B : Set J)
    (x : ((↥B → HalfNatural) × (↥B → HalfNatural)) × (↥Bᶜ → HalfNatural)) :
    (J → HalfNatural) × (J → HalfNatural) :=
  (glue B x.1.2 x.2, glue B x.1.1 x.2)
theorem pairEmbed_injective {J : Type} (B : Set J) :
    Function.Injective (pairEmbed B) := by
  rintro ⟨⟨l₁, l₁'⟩, k₁⟩ ⟨⟨l₂, l₂'⟩, k₂⟩ h
  have h₁ : ((l₁', k₁) : (↥B → HalfNatural) × (↥Bᶜ → HalfNatural)) = (l₂', k₂) :=
    (splitEquiv (X := HalfNatural) B).symm.injective (congrArg Prod.fst h)
  have h₂ : ((l₁, k₁) : (↥B → HalfNatural) × (↥Bᶜ → HalfNatural)) = (l₂, k₂) :=
    (splitEquiv (X := HalfNatural) B).symm.injective (congrArg Prod.snd h)
  simp only [Prod.mk.injEq] at h₁ h₂ ⊢
  exact ⟨⟨h₂.1, h₁.1⟩, h₁.2⟩
theorem glue_restrictTo_of_eq {J : Type} (B : Set J) (a c : J → HalfNatural)
    (h : ∀ b, b ∉ B → a b = c b) :
    glue B (restrictTo B a) (restrictTo Bᶜ c) = a := by
  funext b
  by_cases hb : b ∈ B
  · exact glue_of_mem B _ _ ⟨b, hb⟩
  · exact (glue_of_notMem B _ _ ⟨b, hb⟩).trans (h b hb).symm
theorem hasSum_of_double_series {J P K Q : Type} [Finite J] [Countable P] [Countable K]
    (hSeries : FieldCalculus.SeriesSmooth J)
    (T : Q → C(J → specialUnitary, ℂ)) (H : P → C(J → specialUnitary, ℂ))
    (V : C(J → specialUnitary, ℂ))
    (hVdef : V = ∑' p, H p) (e : P × K → Q) (he : Function.Injective e)
    (hoff : ∀ q, q ∉ Set.range e → T q = 0)
    (hTs : ∀ q, (T q : (J → specialUnitary) → ℂ) ∈ smoothSet)
    (hSum : ∀ w : List (J × Fin 3), Summable fun q => supNorm (fieldWord w (T q)))
    (hTerm : ∀ p, HasSum (fun k => T (e (p, k))) (H p)) :
    (∀ p, (H p : (J → specialUnitary) → ℂ) ∈ smoothSet) ∧
    (∀ w : List (J × Fin 3), ∑' p, esupNorm (fieldWord w (H p)) < ∞) ∧
    Summable (fun p => ‖H p‖) ∧
    HasSum H V ∧
    (∀ w : List (J × Fin 3), HasUniformSum (fun p => fieldWord w (H p))
      (fieldWord w V)) ∧
    (V : (J → specialUnitary) → ℂ) ∈ smoothSet ∧
    HasSum T V := by
  let s : List (J × Fin 3) → P × K → ℝ := fun w x => supNorm (fieldWord w (T (e x)))
  have hs : ∀ w, Summable (s w) := fun w => (hSum w).comp_injective he
  have hsK : ∀ w p, Summable fun k => s w (p, k) := fun w p => (hs w).prod_factor p
  let a : List (J × Fin 3) → P → ℝ := fun w p => ∑' k, s w (p, k)
  have ha : ∀ w, Summable (a w) := fun w => (hs w).prod
  have hanonneg : ∀ w p, 0 ≤ a w p := fun w p =>
    tsum_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hFun : ∀ p, (fun u => ∑' k, T (e (p, k)) u) = (H p : (J → specialUnitary) → ℂ) := fun p =>
    funext fun u => (ContinuousMap.hasSum_apply (hTerm p) u).tsum_eq
  have hser := fun p => hSeries K (fun k => (T (e (p, k)) : (J → specialUnitary) → ℂ))
    (fun k => hTs _) (fun w => hsK w p)
  have hsmooth : ∀ p, (H p : (J → specialUnitary) → ℂ) ∈ smoothSet := fun p => by
    have h := (hser p).1
    rwa [hFun p] at h
  have hderiv : ∀ w p u, HasSum (fun k => fieldWord w (T (e (p, k))) u)
      (fieldWord w (H p) u) := fun w p u => by
    have h := (hser p).2 w u
    rwa [hFun p] at h
  have hbd : ∀ w p u, ‖fieldWord w (H p) u‖ ≤ a w p := fun w p u =>
    (hderiv w p u).norm_le_of_bounded (hsK w p).hasSum fun k =>
      norm_le_supNorm (continuous_of_mem_smoothSet (fieldWord_mem_smoothSet (hTs _) w)) u
  have hsup : ∀ w, Summable fun p => supNorm (fieldWord w (H p)) := fun w =>
    Summable.of_nonneg_of_le (fun _ => Real.iSup_nonneg fun _ => norm_nonneg _)
      (fun p => Real.iSup_le (fun u => hbd w p u) (hanonneg w p)) (ha w)
  have hNorm : Summable fun p => ‖H p‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => (ContinuousMap.norm_le _ (hanonneg [] p)).2 (hbd [] p)) (ha [])
  have hHatSum : HasSum H V := hVdef ▸ hNorm.of_norm.hasSum
  have hV : (fun u => ∑' p, H p u) = (V : (J → specialUnitary) → ℂ) :=
    funext fun u => (ContinuousMap.hasSum_apply hHatSum u).tsum_eq
  have hser₂ := hSeries P (fun p => (H p : (J → specialUnitary) → ℂ)) hsmooth hsup
  have hderiv₂ : ∀ w u, HasSum (fun p => fieldWord w (H p) u) (fieldWord w V u) :=
    fun w u => by
      have h := hser₂.2 w u
      rwa [hV] at h
  have hTnorm : Summable fun q => ‖T q‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => (ContinuousMap.norm_le _ (Real.iSup_nonneg fun _ => norm_nonneg _)).2
        fun u => norm_le_supNorm (T q).continuous u) (hSum [])
  refine ⟨hsmooth, fun w => ?_, hNorm, hHatSum, fun w => ?_, ?_, ?_⟩
  · calc ∑' p, esupNorm (fieldWord w (H p))
        ≤ ∑' p, ENNReal.ofReal (a w p) := ENNReal.tsum_le_tsum fun p => iSup_le fun u => by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hbd w p u)
      _ < ∞ := (ha w).tsum_ofReal_lt_top
  · have h := tendstoUniformly_tsum (ha w) (fun p u => hbd w p u)
    have h' : (fun x => ∑' p, fieldWord w (H p) x) = fieldWord w V :=
      funext fun u => (hderiv₂ w u).tsum_eq
    unfold HasUniformSum
    rwa [h'] at h
  · have h := hser₂.1
    rwa [hV] at h
  · have h₁ : Summable (T ∘ e) := hTnorm.of_norm.comp_injective he
    have h₂ := h₁.hasSum.prod_fiberwise hTerm
    have h₃ := h₂.unique hHatSum
    have h₄ := h₁.hasSum
    rw [h₃] at h₄
    exact (he.hasSum_iff hoff).1 h₄
theorem hasSum_row_isotypicProj {J : Type} [Finite J]
    (hC₁ : ∀ (l : J → HalfNatural) (F : HaarL2 J),
      toHaarL2 (isotypicPartSum l F : (J → specialUnitary) → ℂ) = isotypicProj l F)
    (hC₃ : ∀ (l l' : J → HalfNatural) (ψ : C(J → specialUnitary, ℂ)), ψ ∈ prodCoeffSpan l →
      isotypicPartSum l (toHaarL2 (ψ : (J → specialUnitary) → ℂ)) = ψ ∧
      (l' ≠ l → isotypicPartSum l' (toHaarL2 (ψ : (J → specialUnitary) → ℂ)) = 0))
    (T : (J → HalfNatural) → (J → HalfNatural) → C(J → specialUnitary, ℂ))
    (hMem : ∀ a c, T a c ∈ prodCoeffSpan a) (V : C(J → specialUnitary, ℂ))
    (hTall : HasSum (fun q : (J → HalfNatural) × (J → HalfNatural) => T q.1 q.2) V)
    (lam' : J → HalfNatural) :
    HasSum (fun mu => toHaarL2 (T lam' mu : (J → specialUnitary) → ℂ))
      (isotypicProj lam' (toHaarL2 (V : (J → specialUnitary) → ℂ))) := by
  let L : C(J → specialUnitary, ℂ) →L[ℂ] HaarL2 J :=
    (isotypicProj lam').comp (ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ)
  have hL : ∀ G : C(J → specialUnitary, ℂ),
      L G = isotypicProj lam' (toHaarL2 (G : (J → specialUnitary) → ℂ)) :=
    fun G => by rw [toHaarL2_eq_toLp]; rfl
  have h := L.hasSum hTall
  rw [hL] at h
  have hi : Function.Injective fun mu : J → HalfNatural => (lam', mu) := fun _ _ h =>
    (Prod.mk.inj h).2
  have h₂ := (hi.hasSum_iff
    (f := fun q : (J → HalfNatural) × (J → HalfNatural) => L (T q.1 q.2)) ?_).2 h
  · have h₃ : (fun mu => toHaarL2 (T lam' mu : (J → specialUnitary) → ℂ)) =
        (fun q : (J → HalfNatural) × (J → HalfNatural) => L (T q.1 q.2)) ∘
          fun mu : J → HalfNatural => (lam', mu) := by
      funext mu
      simp only [Function.comp]
      rw [hL, ← hC₁, (hC₃ lam' lam' _ (hMem lam' mu)).1]
    rw [h₃]
    exact h₂
  · rintro ⟨a, c⟩ hq
    have hne : a ≠ lam' := fun hh => hq ⟨c, by simp [hh]⟩
    simp only
    rw [hL, ← hC₁, (hC₃ a lam' _ (hMem a c)).2 hne.symm, toHaarL2_eq_toLp, map_zero]
theorem pow_mul_norm_le_of_expansion {X : Type*} [NormedAddCommGroup X] {I : Type*} (R : I → X) (Y : X)
    (hR : HasSum R Y) (hS : Summable fun i => ‖R i‖) (W C : ℝ) (hW : 0 < W) (q d : ℕ)
    (hb : W ^ (q + d) * ∑' i, ‖R i‖ ≤ C * W ^ d) : W ^ q * ‖Y‖ ≤ C := by
  have h₁ : ‖Y‖ ≤ ∑' i, ‖R i‖ := by
    rw [← hR.tsum_eq]
    exact norm_tsum_le_tsum_norm hS
  have h₂ : W ^ q * ‖Y‖ * W ^ d ≤ C * W ^ d := by
    calc W ^ q * ‖Y‖ * W ^ d = W ^ (q + d) * ‖Y‖ := by rw [pow_add]; ring
      _ ≤ W ^ (q + d) * ∑' i, ‖R i‖ := by gcongr
      _ ≤ C * W ^ d := hb
  exact le_of_mul_le_mul_right h₂ (pow_pos hW d)
end HatSeries
open HatSeries in
theorem hatSeriesConverges_holds
    (hDouble : HatDoubleTerms.Statement)
    (hTerms : HatTermAsDoubleSeriesStatement)
    (hCalc : FieldCalculus.AllRules)
    (hComp : IsotypicPartSums.Statement)
    (hDecay : SmoothToSobolevDecayStatement)
    (hFacts : SeveralVariables.SeveralVariablesFacts) :
    HatSeriesConvergesStatement := by
  intro J _ _ β B f hf D hβ hB hD F hF
  have hcH : Countable HalfNatural := countable_halfNatural
  obtain ⟨hMem, hVan, hRow, -, hBound, hSum⟩ := hDouble J β B f hf D F hβ hB hD hF
  have hSeries : FieldCalculus.SeriesSmooth J :=
    (hCalc.2.2 J).2.2.2.2.2.2.2.1
  have hPoly : ∀ G : (J → specialUnitary) → ℂ, IsEntryPolynomial G → G ∈ smoothSet :=
    (hCalc.2.2 J).2.2.2.2.2.1.1
  have hC₁ := (hComp J).1
  have hC₃ := (hComp J).2.2
  have hTs : ∀ q : (J → HalfNatural) × (J → HalfNatural),
      (hatDoubleTerm β B f hf F q.1 q.2 : (J → specialUnitary) → ℂ) ∈ smoothSet := fun q =>
    hPoly _ ((hFacts J q.1 ⟨0⟩).2.2.2.2.2.1.2.1 _ (hMem q.1 q.2))
  have hoff : ∀ q, q ∉ Set.range (pairEmbed (J := J) B) →
      hatDoubleTerm β B f hf F q.1 q.2 = 0 := by
    intro q hq
    by_contra hne
    have hv := (hVan q.1 q.2 hne).1
    exact hq ⟨((restrictTo B q.2, restrictTo B q.1), restrictTo Bᶜ q.2),
      Prod.ext (glue_restrictTo_of_eq B _ _ hv) (glue_restrictTo_of_eq B _ _ fun _ _ => rfl)⟩
  have hTerm : ∀ p : (↥B → HalfNatural) × (↥B → HalfNatural),
      HasSum (fun k => (fun q : (J → HalfNatural) × (J → HalfNatural) =>
        hatDoubleTerm β B f hf F q.1 q.2) (pairEmbed B (p, k))) (hatSeriesTerm β B f hf F p) :=
    fun p => hTerms J β B f hf D F p.1 p.2 hβ hB hD hF
  obtain ⟨hsmooth, hext, hNorm, hHatSum, hUnif, hVs, hTall⟩ :=
    hasSum_of_double_series hSeries (fun q : (J → HalfNatural) × (J → HalfNatural) =>
      hatDoubleTerm β B f hf F q.1 q.2) (hatSeriesTerm β B f hf F) (hatSum β B f hf F) rfl
      (pairEmbed B) (pairEmbed_injective B) hoff hTs hSum hTerm
  have hRowSum := hasSum_row_isotypicProj (fun l G => (hC₁ l G).2.2) hC₃
    (hatDoubleTerm β B f hf F) hMem (hatSum β B f hf F) hTall
  have hCT : ∀ lam' lam, hatIsotypicTerm β B f F lam' lam =
      toHaarL2 (hatDoubleTerm β B f hf F lam' lam : (J → specialUnitary) → ℂ) := fun lam' lam => by
    have h₁ : (fun u => pullFromPart B f u *
        isotypicPart lam (toHaarL2 (F : (J → specialUnitary) → ℂ)) u) =
        (mulPullback B f hf (isotypicPartSum lam (toHaarL2 (F : (J → specialUnitary) → ℂ))) :
          (J → specialUnitary) → ℂ) := by
      funext u
      rw [← (hC₁ lam _).2.1]
      rfl
    rw [hatIsotypicTerm, hatDoubleTerm, h₁,
      toHaarL2_eq_toLp (charCoeffRatio β (restrictTo B lam) (restrictTo B lam') •
        isotypicPartSum lam' _), map_smul, ← toHaarL2_eq_toLp, (hC₁ lam' _).2.2]
  have hAdm : ∀ l l', hatSeriesTerm β B f hf F (l, l') ≠ 0 → IsDegreeCompatible D l l' := by
    intro l l' hne
    have hex : ∃ k, hatDoubleTerm β B f hf F (glue B l' k) (glue B l k) ≠ 0 := by
      by_contra hk
      simp only [not_exists, not_not] at hk
      have h := hTerms J β B f hf D F l l' hβ hB hD hF
      simp only [hk] at h
      exact hne (h.unique hasSum_zero)
    obtain ⟨k, hk⟩ := hex
    have h := (hVan _ _ hk).2
    rwa [restrictTo_glue, restrictTo_glue] at h
  have hCTsub : ∀ lam', {lam | hatIsotypicTerm β B f F lam' lam ≠ 0} ⊆
      {lam | hatDoubleTerm β B f hf F lam' lam ≠ 0} := fun lam' lam h h₀ => h (by
    rw [hCT, h₀, toHaarL2_eq_toLp, map_zero])
  refine ⟨fun l' => ?_, hsmooth, hext, ?_, ?_, hUnif, ?_, hVs, ?_, fun lam' => ?_⟩
  · have hsub : {l : ↥B → HalfNatural | hatSeriesTerm β B f hf F (l, l') ≠ 0} ⊆
        {l | IsDegreeCompatible D l l'} := fun l h => hAdm l l' h
    obtain ⟨h₁, h₂⟩ := degreeCompatible_finite_card_le D l'
    exact ⟨h₁.subset hsub, (Set.ncard_le_ncard hsub h₁).trans h₂, fun l h => hAdm l l' h⟩
  · simp only [toHaarL2_eq_toLp]
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => ContinuousLinearMap.le_opNorm _ _)
      (hNorm.mul_left ‖ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ‖)
  · simp only [toHaarL2_eq_toLp]
    exact (ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ).hasSum hHatSum
  · show ∑' p : (↥B → HalfNatural) × (↥B → HalfNatural),
      ‖charCoeffRatio β p.1 p.2‖ₑ * ‖hatSummand B f hf F p.1 p.2‖ₑ < ∞
    calc ∑' p : (↥B → HalfNatural) × (↥B → HalfNatural),
        ‖charCoeffRatio β p.1 p.2‖ₑ * ‖hatSummand B f hf F p.1 p.2‖ₑ
        = ∑' p, ENNReal.ofReal ‖hatSeriesTerm β B f hf F p‖ := tsum_congr fun p => by
          rw [ofReal_norm, hatSeriesTerm, enorm_smul]
      _ < ∞ := hNorm.tsum_ofReal_lt_top
  · intro q
    have hfin := ((hDecay J) F hF).1 (q + degreeTotal D)
    have hle : ∀ lam' : J → HalfNatural, ENNReal.ofReal ((1 + weightSum lam') ^ q *
        ‖isotypicProj lam' (toHaarL2 (hatSum β B f hf F : (J → specialUnitary) → ℂ))‖) ≤
        ENNReal.ofReal (derivLossConst β D (esupNorm f).toReal q) *
          sobolevDecay (q + degreeTotal D) (toHaarL2 (F : (J → specialUnitary) → ℂ)) := by
      intro lam'
      have hW : 0 < 1 + weightSum lam' := by
        have h₀ : 0 ≤ weightSum lam' := finsum_nonneg fun b => by
          simp only [HalfNatural.toReal]
          positivity
        linarith
      have hS : Summable fun mu =>
          ‖toHaarL2 (hatDoubleTerm β B f hf F lam' mu : (J → specialUnitary) → ℂ)‖ :=
        summable_of_hasFiniteSupport ((hRow lam').1.subset fun mu h h₀ => h (by
          beta_reduce
          rw [h₀, toHaarL2_eq_toLp, map_zero, norm_zero]))
      have hc := pow_mul_norm_le_of_expansion _ _ (hRowSum lam') hS (1 + weightSum lam') _ hW q
        (degreeTotal D) (hBound (q + degreeTotal D) lam')
      calc _ ≤ ENNReal.ofReal (derivLossConst β D (esupNorm f).toReal q *
            (sobolevDecay (q + degreeTotal D) (toHaarL2 (F : (J → specialUnitary) → ℂ))).toReal) :=
            ENNReal.ofReal_le_ofReal hc
        _ = _ := by
          rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin.ne]
    exact iSup_le hle
  · have hsub := hCTsub lam'
    obtain ⟨h₁, h₂⟩ := hRow lam'
    refine ⟨h₁.subset hsub, (Set.ncard_le_ncard hsub h₁).trans h₂, ?_⟩
    simp only [hCT]
    exact (hRowSum lam').tsum_eq.symm
end SpinHarmonics
end
end YangMills.Construction
