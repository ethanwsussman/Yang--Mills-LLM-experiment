import YangMills.Construction.Matrices.EveryPolynomialOnPowersOfGHasFiniteDegrees
import YangMills.Construction.TransferOperators.ExactEliminationOfAnOutermostLayerProof
import YangMills.Construction.TransferOperators.OperatorHatAlongInjectionsAndPermutations
import YangMills.Construction.TransferOperators.OperatorsHatOfDisjointPartsCommute
import YangMills.Construction.TransferOperators.ReversalOfTheFunctionOfTheStepBetweenSymmetricStacks
import YangMills.Construction.TransferOperators.SeriesOfTheOperatorHatConverges
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice SpinHarmonics Matrices Matrices.ComplexMatrix2
namespace TransferOperators.CenteredStackReversal
section HatOperators
variable {J : Type} [Finite J]
theorem hatSum_congr {β : ℝ} {A C : Set J} (e : A = C)
    {f : (↥A → ComplexMatrix2.specialUnitary) → ℂ}
    {g : (↥C → ComplexMatrix2.specialUnitary) → ℂ} (hf : IsRealEntryPolynomial f)
    (hg : IsRealEntryPolynomial g)
    (hfg : ∀ v : ↥A → ComplexMatrix2.specialUnitary, f v = g fun b => v ⟨b.1, e ▸ b.2⟩)
    (F : C(J → ComplexMatrix2.specialUnitary, ℂ)) :
    hatSum β A f hf F = hatSum β C g hg F := by
  subst e
  have hfg' : f = g := funext hfg
  subst hfg'
  rfl
theorem hatSum_mem_smoothSet [Nonempty J] (hSeries : HatSeriesConvergesStatement)
    (hDegrees : PolynomialDegrees.Statement) {β : ℝ} (hβ : 0 < β)
    {A : Set J} (hA : A.Nonempty) {f : (↥A → ComplexMatrix2.specialUnitary) → ℂ}
    (hf : IsRealEntryPolynomial f) {F : C(J → ComplexMatrix2.specialUnitary, ℂ)}
    (hF : (F : (J → ComplexMatrix2.specialUnitary) → ℂ) ∈ smoothSet) :
    (hatSum β A f hf F : (J → ComplexMatrix2.specialUnitary) → ℂ) ∈ smoothSet := by
  have : Nonempty ↥A := hA.to_subtype
  obtain ⟨-, D, hD⟩ := hDegrees ↥A f hf.1
  exact (hSeries J β A f hf D hβ hA hD F hF).2.2.2.2.2.2.2.1
theorem permuteArgs_hatSum_hatSum [Nonempty J]
    (hNat : HatNaturalityStatement)
    (hCommute : HatDisjointCommuteStatement)
    (hSeries : HatSeriesConvergesStatement)
    (hDegrees : PolynomialDegrees.Statement) {β : ℝ} (hβ : 0 < β)
    (s : Equiv.Perm J) {A C : Set J} (hA : A.Nonempty) (hC : C.Nonempty) (hAC : Disjoint A C)
    (hsA : s '' A = C) (hsC : s '' C = A)
    {fm hm : (↥A → ComplexMatrix2.specialUnitary) → ℂ}
    {fp hp : (↥C → ComplexMatrix2.specialUnitary) → ℂ}
    (hfm : IsRealEntryPolynomial fm) (hhm : IsRealEntryPolynomial hm)
    (hfp : IsRealEntryPolynomial fp) (hhp : IsRealEntryPolynomial hp)
    (ef : ∀ v : ↥(s '' A) → ComplexMatrix2.specialUnitary,
      transportAlong s A fm v = fp fun b => v ⟨b.1, hsA ▸ b.2⟩)
    (eh : ∀ v : ↥(s '' C) → ComplexMatrix2.specialUnitary,
      transportAlong s C hp v = hm fun b => v ⟨b.1, hsC ▸ b.2⟩)
    (F : C(J → ComplexMatrix2.specialUnitary, ℂ))
    (hF : (F : (J → ComplexMatrix2.specialUnitary) → ℂ) ∈ smoothSet)
    (hF' : (precompAlong s F : (J → ComplexMatrix2.specialUnitary) → ℂ) ∈ smoothSet) :
    permuteArgs s
        (hatSum β A fm hfm (hatSum β C hp hhp F) : (J → ComplexMatrix2.specialUnitary) → ℂ) =
      hatSum β A hm hhm (hatSum β C fp hfp (precompAlong s F)) := by
  have hH := hatSum_mem_smoothSet hSeries hDegrees hβ hC hhp hF
  obtain ⟨ht₁, h₁⟩ := (hNat J β A fm hfm hβ hA).2 s
  obtain ⟨ht₂, h₂⟩ := (hNat J β C hp hhp hβ hC).2 s
  have e₂ : precompAlong s (hatSum β C hp hhp F) = hatSum β A hm hhm (precompAlong s F) := by
    apply DFunLike.coe_injective
    rw [coe_precompAlong_perm, h₂ F hF, hatSum_congr hsC ht₂ hhm eh]
  rw [h₁ _ hH, e₂, hatSum_congr hsA ht₁ hfp ef,
    hCommute J β C fp hfp hβ hC A hm hhm _ hA hAC hF']
end HatOperators
section SmoothFunctions
variable (hcalc : FieldCalculus.AllRules) {J : Type} [Finite J] [Nonempty J]
include hcalc
theorem mul_mem_smoothSet {F H : (J → ComplexMatrix2.specialUnitary) → ℂ} (hF : F ∈ smoothSet)
    (hH : H ∈ smoothSet) : (fun u => F u * H u) ∈ smoothSet := by apply _root_.YangMills.Construction.TransferOperators.OutermostSliceElimination.mul_mem_smoothSet <;> assumption
theorem neg_sub_mem_smoothSet {F H : (J → ComplexMatrix2.specialUnitary) → ℂ}
    (hF : F ∈ smoothSet) (hH : H ∈ smoothSet) : (fun u => -F u - H u) ∈ smoothSet := by
  obtain ⟨⟨A, hA⟩, -⟩ := (hcalc.2.2 J).2.1 ⊤
  have hA' : (A : Set ((J → ComplexMatrix2.specialUnitary) → ℂ)) = smoothSet := hA
  rw [← hA'] at hF hH ⊢
  exact A.sub_mem (A.neg_mem hF) hH
theorem one_mem_smoothSet :
    (fun _ : J → ComplexMatrix2.specialUnitary => (1 : ℂ)) ∈ smoothSet := by
  obtain ⟨⟨A, hA⟩, -⟩ := (hcalc.2.2 J).2.1 ⊤
  have hA' : (A : Set ((J → ComplexMatrix2.specialUnitary) → ℂ)) = smoothSet := hA
  rw [← hA']
  exact A.one_mem
theorem finprod_mem_smoothSet {I : Type} [Finite I]
    (G : I → (J → ComplexMatrix2.specialUnitary) → ℂ)
    (hG : ∀ i, G i ∈ smoothSet) : (fun u => ∏ᶠ i, G i u) ∈ smoothSet := by apply _root_.YangMills.Construction.TransferOperators.OutermostSliceElimination.finprod_mem_smoothSet <;> assumption
end SmoothFunctions
theorem isRealEntryPolynomial_comp {K J : Type} [Finite K] [Finite J] (e : K → J)
    {F : (K → ComplexMatrix2.specialUnitary) → ℂ} (hF : IsRealEntryPolynomial F) :
    IsRealEntryPolynomial fun u : J → ComplexMatrix2.specialUnitary => F fun a => u (e a) := by apply _root_.YangMills.Construction.TransferOperators.OutermostSliceElimination.isRealEntryPolynomial_comp_reindex <;> assumption
section StepData
variable {μ : Fin 4} (D : CenteredStackStep μ)
abbrev levelSwap : Equiv.Perm D.InnerPairs := reflectPairPerm D.center D.halfWidth D.vertexSet
theorem levelSwap_innerPair {j j' : ℤ} (hj : D.IsInnerLevel j) (hj' : D.IsInnerLevel j')
    (h : reflectedLevel D.center j = j') (b : SliceLink μ) (hb : b ∈ D.block.thickened) :
    levelSwap D (D.innerPair hj b hb) = D.innerPair hj' b hb := by
  subst h
  rfl
theorem levelSwap_levelSwap (p : D.InnerPairs) : levelSwap D (levelSwap D p) = p :=
  (reflectPairPerm D.center D.halfWidth D.vertexSet).left_inv p
theorem reflectedLevel_bottom : reflectedLevel D.center D.bottom = D.top := by
  simp only [reflectedLevel, CenteredStackStep.bottom, CenteredStackStep.top]
  ring
theorem reflectedLevel_top : reflectedLevel D.center D.top = D.bottom := by
  simp only [reflectedLevel, CenteredStackStep.bottom, CenteredStackStep.top]
  ring
theorem reflectedLevel_bottom_add_one : reflectedLevel D.center (D.bottom + 1) = D.top - 1 := by
  simp only [reflectedLevel, CenteredStackStep.bottom, CenteredStackStep.top]
  ring
theorem reflectedLevel_top_sub_one : reflectedLevel D.center (D.top - 1) = D.bottom + 1 := by
  simp only [reflectedLevel, CenteredStackStep.bottom, CenteredStackStep.top]
  ring
theorem blockRestrict_levelSwap {j j' : ℤ} (hj : D.IsInnerLevel j) (hj' : D.IsInnerLevel j')
    (h : reflectedLevel D.center j = j') (u : D.InnerPairs → ComplexMatrix2.specialUnitary) :
    D.blockRestrict hj (fun p => u (levelSwap D p)) = D.blockRestrict hj' u := by
  funext b
  simp only [CenteredStackStep.blockRestrict]
  rw [levelSwap_innerPair D hj hj' h]
theorem collarRestrict_levelSwap {j j' : ℤ} (hj : D.IsInnerLevel j) (hj' : D.IsInnerLevel j')
    (h : reflectedLevel D.center j = j') (u : D.InnerPairs → ComplexMatrix2.specialUnitary) :
    D.collarRestrict hj (fun p => u (levelSwap D p)) = D.collarRestrict hj' u := by
  funext b
  simp only [CenteredStackStep.collarRestrict]
  rw [levelSwap_innerPair D hj hj' h]
theorem sliceEnergyAt_levelSwap (β : ℝ) {j j' : ℤ} (hj : D.IsInnerLevel j)
    (hj' : D.IsInnerLevel j') (h : reflectedLevel D.center j = j')
    (u : D.InnerPairs → ComplexMatrix2.specialUnitary) :
    D.sliceEnergyAt β hj (fun p => u (levelSwap D p)) = D.sliceEnergyAt β hj' u := by
  simp only [CenteredStackStep.sliceEnergyAt]
  rw [blockRestrict_levelSwap D hj hj' h, collarRestrict_levelSwap D hj hj' h]
theorem bottomKernel_levelSwap (β : ℝ) (u : D.InnerPairs → ComplexMatrix2.specialUnitary) :
    D.bottomKernel β (fun p => u (levelSwap D p)) = D.topKernel β u := by
  simp only [CenteredStackStep.bottomKernel, CenteredStackStep.topKernel]
  rw [blockRestrict_levelSwap D _ D.isInnerLevel_top (reflectedLevel_bottom D),
    blockRestrict_levelSwap D _ D.isInnerLevel_top_sub_one (reflectedLevel_bottom_add_one D)]
theorem topKernel_levelSwap (β : ℝ) (u : D.InnerPairs → ComplexMatrix2.specialUnitary) :
    D.topKernel β (fun p => u (levelSwap D p)) = D.bottomKernel β u := by
  simp only [CenteredStackStep.bottomKernel, CenteredStackStep.topKernel]
  rw [blockRestrict_levelSwap D _ D.isInnerLevel_bottom (reflectedLevel_top D),
    blockRestrict_levelSwap D _ D.isInnerLevel_bottom_add_one (reflectedLevel_top_sub_one D)]
theorem blockRestrict_congr {j j' : ℤ} (hj : D.IsInnerLevel j) (hj' : D.IsInnerLevel j')
    (h : j = j') (u : D.InnerPairs → ComplexMatrix2.specialUnitary) :
    D.blockRestrict hj u = D.blockRestrict hj' u := by
  subst h
  rfl
theorem topKernel_eq_bottomKernel_of_halfWidth_eq_one
    (hker : KernelSymmetryAndGaugeInvariance.Statement) {β : ℝ}
    (hβ : 0 < β) (hk : D.halfWidth = 1) (u : D.InnerPairs → ComplexMatrix2.specialUnitary) :
    D.topKernel β u = D.bottomKernel β u := by
  have h₁ : D.top - 1 = D.bottom := by
    simp only [CenteredStackStep.bottom, CenteredStackStep.top, hk]
    ring
  have h₂ : D.bottom + 1 = D.top := by
    simp only [CenteredStackStep.bottom, CenteredStackStep.top, hk]
    ring
  have : Nonempty D.block.links := D.block.links_nonempty.to_subtype
  simp only [CenteredStackStep.bottomKernel, CenteredStackStep.topKernel]
  rw [blockRestrict_congr D D.isInnerLevel_top_sub_one D.isInnerLevel_bottom h₁,
    blockRestrict_congr D D.isInnerLevel_bottom_add_one D.isInnerLevel_top h₂]
  exact (((hker β hβ).1 D.block.links).1 _ _).1
theorem boundaryWeight_levelSwap
    (hker : KernelSymmetryAndGaugeInvariance.Statement) {β : ℝ}
    (hβ : 0 < β) (u : D.InnerPairs → ComplexMatrix2.specialUnitary) :
    D.boundaryWeight β (fun p => u (levelSwap D p)) = D.boundaryWeight β u := by
  simp only [CenteredStackStep.boundaryWeight]
  rw [sliceEnergyAt_levelSwap D β _ D.isInnerLevel_top (reflectedLevel_bottom D),
    sliceEnergyAt_levelSwap D β _ D.isInnerLevel_bottom (reflectedLevel_top D),
    bottomKernel_levelSwap,
    show -D.sliceEnergyAt β D.isInnerLevel_top u - D.sliceEnergyAt β D.isInnerLevel_bottom u =
      -D.sliceEnergyAt β D.isInnerLevel_bottom u - D.sliceEnergyAt β D.isInnerLevel_top u by ring]
  by_cases hk : D.halfWidth = 1
  · simp only [if_pos hk]
    rw [topKernel_eq_bottomKernel_of_halfWidth_eq_one D hker hβ hk]
  · simp only [if_neg hk]
    rw [topKernel_levelSwap]
    ring
theorem isRealEntryPolynomial_sliceEnergyAt
    (hker : KernelSymmetryAndGaugeInvariance.Statement) {β : ℝ}
    (hβ : 0 < β) {j : ℤ} (hj : D.IsInnerLevel j) :
    IsRealEntryPolynomial (D.sliceEnergyAt β hj) :=
  isRealEntryPolynomial_comp (fun a : D.block.thickened => D.innerPair hj a.1 a.2)
    ((hker β hβ).2.2.2 μ D.block).1
theorem linkProductKernel_mem_smoothSet (hcalc : FieldCalculus.AllRules) [Nonempty D.InnerPairs]
    {β : ℝ} (hβ : 0 < β) {j j' : ℤ} (hj : D.IsInnerLevel j) (hj' : D.IsInnerLevel j')
    (hne : j ≠ j') :
    (fun u => linkProductKernel β (D.blockRestrict hj u) (D.blockRestrict hj' u)) ∈ smoothSet := by
  have hw : ∀ b : D.block.links,
      (fun u : D.InnerPairs → ComplexMatrix2.specialUnitary => singleBondWeight β
        (u (D.innerPair hj b.1 (D.block.subset_thickened b.2)) *
          (u (D.innerPair hj' b.1 (D.block.subset_thickened b.2)))⁻¹)) ∈ smoothSet :=
    fun b => ((hcalc.2.2 D.InnerPairs).2.2.2.2.2.1.2 β hβ _ _
      fun h => hne (congrArg (fun p : D.InnerPairs => p.1.1) h)).1
  exact finprod_mem_smoothSet hcalc _ hw
theorem boundaryWeight_mem_smoothSet (hcalc : FieldCalculus.AllRules)
    (hker : KernelSymmetryAndGaugeInvariance.Statement)
    [Nonempty D.InnerPairs] {β : ℝ} (hβ : 0 < β) : D.boundaryWeight β ∈ smoothSet := by
  have hpol := (hcalc.2.2 D.InnerPairs).2.2.2.2.2.1.1
  have hl := isRealEntryPolynomial_sliceEnergyAt D hker hβ D.isInnerLevel_bottom
  have hh := isRealEntryPolynomial_sliceEnergyAt D hker hβ D.isInnerLevel_top
  have hexp := (hcalc.2.2 D.InnerPairs).2.2.2.2.1.1 _
    (neg_sub_mem_smoothSet hcalc (hpol _ hl.1) (hpol _ hh.1)) fun u => by
      simp [hl.2 u, hh.2 u]
  have hlow : D.bottomKernel β ∈ smoothSet :=
    linkProductKernel_mem_smoothSet D hcalc hβ D.isInnerLevel_bottom
      D.isInnerLevel_bottom_add_one (by omega)
  have hup : D.topKernel β ∈ smoothSet :=
    linkProductKernel_mem_smoothSet D hcalc hβ D.isInnerLevel_top
      D.isInnerLevel_top_sub_one (by omega)
  have hlast : (fun u => if D.halfWidth = 1 then (1 : ℂ) else D.topKernel β u) ∈
      smoothSet := by
    by_cases hk : D.halfWidth = 1
    · simp only [if_pos hk]
      exact one_mem_smoothSet hcalc
    · simp only [if_neg hk]
      exact hup
  exact mul_mem_smoothSet hcalc (mul_mem_smoothSet hcalc hexp hlow) hlast
theorem levelPart_nonempty {j : ℤ} (hj : D.IsInnerLevel j) : (D.levelPart j).Nonempty := by
  obtain ⟨b, hb⟩ := D.block.links_nonempty
  exact ⟨D.innerPair hj b (D.block.subset_thickened hb), rfl, hb⟩
theorem disjoint_levelPart_bottom_top : Disjoint (D.levelPart D.bottom) (D.levelPart D.top) := by
  refine Set.disjoint_left.2 fun p h₁ h₂ => ?_
  have e : D.bottom = D.top := h₁.1.symm.trans h₂.1
  have := D.one_le_halfWidth
  simp only [CenteredStackStep.bottom, CenteredStackStep.top] at e
  omega
theorem levelSwap_image_levelPart {j j' : ℤ} (h : reflectedLevel D.center j = j') :
    levelSwap D '' D.levelPart j = D.levelPart j' := by
  ext p
  constructor
  · rintro ⟨q, ⟨h₁, h₂⟩, rfl⟩
    refine ⟨?_, h₂⟩
    change reflectedLevel D.center q.1.1 = j'
    rw [h₁, h]
  · rintro ⟨h₁, h₂⟩
    refine ⟨levelSwap D p, ⟨?_, h₂⟩, levelSwap_levelSwap D p⟩
    change reflectedLevel D.center p.1.1 = j
    rw [h₁, ← h, reflectedLevel_reflectedLevel]
theorem transportAlong_pullToLevel {j j' : ℤ} (hj : D.IsInnerLevel j) (hj' : D.IsInnerLevel j')
    (h : reflectedLevel D.center j = j') (e : levelSwap D '' D.levelPart j = D.levelPart j')
    (g : (D.block.links → ComplexMatrix2.specialUnitary) → ℂ)
    (v : ↥(levelSwap D '' D.levelPart j) → ComplexMatrix2.specialUnitary) :
    transportAlong (levelSwap D) (D.levelPart j) (D.pullToLevel hj g) v =
      D.pullToLevel hj' g fun b => v ⟨b.1, by rw [e]; exact b.2⟩ := by
  simp only [transportAlong, CenteredStackStep.pullToLevel]
  congr 1
  funext b
  exact congrArg v
    (Subtype.ext (levelSwap_innerPair D hj hj' h b.1 (D.block.subset_thickened b.2)))
theorem levelReversal_transferStepFunction
    (hNat : HatNaturalityStatement)
    (hCommute : HatDisjointCommuteStatement)
    (hSeries : HatSeriesConvergesStatement)
    (hDegrees : PolynomialDegrees.Statement)
    (hcalc : FieldCalculus.AllRules)
    (hker : KernelSymmetryAndGaugeInvariance.Statement) {β : ℝ}
    (hβ : 0 < β) {f h : (D.block.links → ComplexMatrix2.specialUnitary) → ℂ}
    (hf : IsRealEntryPolynomial f) (hh : IsRealEntryPolynomial h)
    (Φ : C(D.InnerPairs → ComplexMatrix2.specialUnitary, ℂ))
    (hΦ : IsRealEntryPolynomial (Φ : (D.InnerPairs → ComplexMatrix2.specialUnitary) → ℂ)) :
    levelReversal D.center D.halfWidth D.vertexSet (D.transferStepFunction β hf hh Φ) =
      D.transferStepFunction β hh hf (levelExchanged (levelSwap D) Φ) := by
  have hne : Nonempty D.InnerPairs :=
    (levelPart_nonempty D D.isInnerLevel_bottom).to_subtype.map Subtype.val
  have hpol := (hcalc.2.2 D.InnerPairs).2.2.2.2.2.1.1
  have hW := boundaryWeight_mem_smoothSet D hcalc hker hβ
  have hΦs : (Φ : (D.InnerPairs → ComplexMatrix2.specialUnitary) → ℂ) ∈ smoothSet := hpol _ hΦ.1
  have hΦr : (levelExchanged (levelSwap D) Φ :
      (D.InnerPairs → ComplexMatrix2.specialUnitary) → ℂ) ∈ smoothSet :=
    hpol _ (isRealEntryPolynomial_comp (levelSwap D) hΦ).1
  have hF : (D.boundaryWeightMap β * Φ : C(D.InnerPairs → ComplexMatrix2.specialUnitary, ℂ)) ∈
      {X : C(D.InnerPairs → ComplexMatrix2.specialUnitary, ℂ) |
        (X : (D.InnerPairs → ComplexMatrix2.specialUnitary) → ℂ) ∈ smoothSet} :=
    mul_mem_smoothSet hcalc hW hΦs
  have hread : precompAlong (levelSwap D) (D.boundaryWeightMap β * Φ) =
      D.boundaryWeightMap β * levelExchanged (levelSwap D) Φ := by
    ext u
    change D.boundaryWeight β (fun p => u (levelSwap D p)) * Φ (fun p => u (levelSwap D p)) =
      D.boundaryWeight β u * Φ (fun p => u (levelSwap D p))
    rw [boundaryWeight_levelSwap D hker hβ]
  have hF' : (precompAlong (levelSwap D) (D.boundaryWeightMap β * Φ) :
      (D.InnerPairs → ComplexMatrix2.specialUnitary) → ℂ) ∈ smoothSet := by
    rw [hread]
    exact mul_mem_smoothSet hcalc hW hΦr
  have esl := levelSwap_image_levelPart D (reflectedLevel_bottom D)
  have esh := levelSwap_image_levelPart D (reflectedLevel_top D)
  have key := permuteArgs_hatSum_hatSum hNat hCommute hSeries hDegrees hβ (levelSwap D)
    (levelPart_nonempty D D.isInnerLevel_bottom) (levelPart_nonempty D D.isInnerLevel_top)
    (disjoint_levelPart_bottom_top D)
    esl esh (D.isRealEntryPolynomial_pullToLevel D.isInnerLevel_bottom hf)
    (D.isRealEntryPolynomial_pullToLevel D.isInnerLevel_bottom hh)
    (D.isRealEntryPolynomial_pullToLevel D.isInnerLevel_top hf)
    (D.isRealEntryPolynomial_pullToLevel D.isInnerLevel_top hh)
    (transportAlong_pullToLevel D _ _ (reflectedLevel_bottom D) esl f)
    (transportAlong_pullToLevel D _ _ (reflectedLevel_top D) esh h)
    (D.boundaryWeightMap β * Φ) hF hF'
  rw [hread] at key
  funext u
  have ku := congrFun key u
  have e₁ : levelReversal D.center D.halfWidth D.vertexSet (D.transferStepFunction β hf hh Φ) u =
      D.transferStepFunction β hf hh Φ fun p => u (levelSwap D p) := rfl
  rw [e₁]
  simp only [CenteredStackStep.transferStepFunction]
  rw [boundaryWeight_levelSwap D hker hβ]
  exact congrArg (fun z => (D.boundaryWeight β u)⁻¹ * z) ku
end StepData
theorem reversalStatement_holds (hNat : HatNaturalityStatement)
    (hCommute : HatDisjointCommuteStatement)
    (hSeries : HatSeriesConvergesStatement)
    (hDegrees : PolynomialDegrees.Statement)
    (hcalc : FieldCalculus.AllRules)
    (hker : KernelSymmetryAndGaugeInvariance.Statement) :
    CenteredStack.ReversalStatement := by
  intro μ β hβ D f h hf hh Φ hΦ
  exact levelReversal_transferStepFunction D hNat hCommute hSeries hDegrees hcalc hker hβ hf hh
    Φ hΦ
end TransferOperators.CenteredStackReversal
end YangMills.Construction
end
