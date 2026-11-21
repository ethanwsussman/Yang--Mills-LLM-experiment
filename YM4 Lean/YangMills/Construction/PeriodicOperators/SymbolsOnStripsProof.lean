import YangMills.Construction.PeriodicOperators.AssociativityOfProductsOfPeriodicOperators
import YangMills.Construction.PeriodicOperators.InverseOfAPeriodicOperatorOnAnOpenStrip
import YangMills.Construction.PeriodicOperators.KernelOfAHolomorphicMatrixFunctionOnAnOpenStrip
import YangMills.Construction.PeriodicOperators.SymbolAtAPoint
import YangMills.Construction.PeriodicOperators.SymbolOfAnOperatorWithDecayProof
import YangMills.Construction.PeriodicOperators.SymbolsOfCombinationsAndProductsAtAPoint
import YangMills.Construction.PeriodicOperators.SymbolsOnStrips
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.StripSymbols
open TorusMetric (euclidNormVec)
theorem isOpen_openImStrip (υ : ℝ) : IsOpen (openImStrip υ) := by apply _root_.YangMills.Construction.PeriodicOperators.ExpDecaySymbol.isOpen_openImStrip <;> assumption
theorem openStripInterior_eq_openImStrip (υ : ℝ) : openStripInterior υ = openImStrip υ := by
  ext κ
  constructor
  · rintro ⟨O, hO, hκ, hOS⟩ μ
    have hmap : IsOpenMap fun z : Fin 4 → ℂ => (z μ).im :=
      Complex.isOpenMap_im.comp (isOpenMap_eval μ)
    have himg := hmap O hO
    have hsub : (fun z : Fin 4 → ℂ => (z μ).im) '' O ⊆ Icc (-υ) υ := by
      rintro _ ⟨z, hz, rfl⟩
      exact abs_le.mp (hOS hz μ)
    have hin : (κ μ).im ∈ interior (Icc (-υ) υ) :=
      interior_maximal hsub himg ⟨κ, hκ rfl, rfl⟩
    rw [interior_Icc] at hin
    exact abs_lt.mpr hin
  · intro hκ
    refine ⟨openImStrip υ, isOpen_openImStrip υ, ?_, ?_⟩
    · rintro _ rfl
      exact hκ
    · intro z hz μ
      exact (hz μ).le
theorem interiorOfStripChar_holds (υ : ℝ) : InteriorOfStripChar υ := by
  refine ⟨openStripInterior_eq_openImStrip υ, isOpen_openImStrip υ, fun z hz μ => (hz μ).le, ?_⟩
  intro υ' _ hlt z hz μ
  exact (hz μ).trans_lt hlt
theorem euclidNormVec_nonneg (v : InfiniteLattice.AmbientSpace) : 0 ≤ euclidNormVec v :=
  Real.sqrt_nonneg _
theorem isDecayRate_of_isFiniteRange {I I' : PeriodicData} {T : I'.Carrier → I.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hR : IsFiniteRange I I' T) {δ : ℝ} (hδ : 0 < δ) :
    IsDecayRate I I' T δ := by
  obtain ⟨-, C, δ₀, hC, hδ₀, hb⟩ := hT
  obtain ⟨ϱ, hϱ⟩ := hR
  refine ⟨hδ, C * Real.exp (δ * ϱ), by positivity, fun ι' ι => ?_⟩
  set d := euclidNormVec (I'.pos ι' - I.pos ι) with hd
  have hd0 : 0 ≤ d := euclidNormVec_nonneg _
  by_cases h : d ≤ ϱ
  · have h1 : ‖T ι' ι‖ ≤ C := by
      refine (hb ι' ι).trans ?_
      have : Real.exp (-δ₀ * d) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      nlinarith
    have h2 : 1 ≤ Real.exp (δ * ϱ) * Real.exp (-δ * d) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    calc ‖T ι' ι‖ ≤ C * 1 := by simpa using h1
      _ ≤ C * (Real.exp (δ * ϱ) * Real.exp (-δ * d)) := by gcongr
      _ = C * Real.exp (δ * ϱ) * Real.exp (-δ * d) := by ring
  · rw [hϱ ι' ι h, norm_zero]
    positivity
theorem symbolSummableOn_univ_of_isFiniteRange (hId : IdKernelFacts.Claim)
    (hFacts : Symbols.Claim) {I I' : PeriodicData}
    (hI : IsPeriodic I) (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hR : IsFiniteRange I I' T) :
    SymbolSummableOn I I' T univ := by
  intro κ _
  have hδ : 0 < euclidNormVec (imVec κ) + 1 := by
    have := euclidNormVec_nonneg (imVec κ)
    linarith
  have hrate := isDecayRate_of_isFiniteRange hT hR hδ
  have hid := hId I hI
  have hf := hFacts.1 I I' I hI hI' hI T (idKernel I) _ hT hrate hid.1 (hid.2.1 _ hδ)
  exact hf.summable_on_strip κ (by
    show euclidNormVec (imVec κ) < euclidNormVec (imVec κ) + 1
    linarith)
section Bracketing
variable {b : ℕ} {J : Fin (b + 1) → PeriodicData}
  {F : (s : Fin b) → (J s.castSucc).Carrier → (J s.succ).Carrier → ℂ}
theorem _root_.YangMills.Construction.PeriodicOperators.IsBracketing.src_lt {u v : Fin (b + 1)}
    {K : (J u).Carrier → (J v).Carrier → ℂ} (h : IsBracketing J F u v K) : u < v := by
  induction h with
  | leaf s => exact Fin.castSucc_lt_succ
  | node _ _ _ _ _ _ ihP ihQ => exact ihP.trans ihQ
theorem _root_.YangMills.Construction.PeriodicOperators.IsBracketing.isPeriodicKernel
    (hCalc : SymbolCalculus.Claim)
    (hJ : ∀ s, IsPeriodic (J s))
    (hF : ∀ s, IsPeriodicKernel (J s.succ) (J s.castSucc) (F s)) {u v : Fin (b + 1)}
    {K : (J u).Carrier → (J v).Carrier → ℂ} (h : IsBracketing J F u v K) :
    IsPeriodicKernel (J v) (J u) K := by
  cases h with
  | leaf s => exact hF s
  | node P Q hP hQ pP pQ =>
    rename_i m
    have hc := hCalc (J m) (J u) (hJ m) (hJ u)
    exact ((hc.2.2.2.2.2.2.2.2 (J v) (hJ v)).1 P Q pP pQ).2
theorem _root_.YangMills.Construction.PeriodicOperators.IsBracketing.heq_of_leaf {u v : Fin (b + 1)}
    {K : (J u).Carrier → (J v).Carrier → ℂ}
    (h : IsBracketing J F u v K) (s : Fin b) (hu : u = s.castSucc) (hv : v = s.succ) :
    HEq K (F s) := by
  cases h with
  | leaf s' =>
    have : s' = s := Fin.castSucc_injective _ hu
    subst this
    rfl
  | node P Q hP hQ pP pQ =>
    have h1 := hP.src_lt
    have h2 := hQ.src_lt
    subst hu hv
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h1 h2
    omega
theorem _root_.YangMills.Construction.PeriodicOperators.IsBracketing.exists_split_last
    (hCalc : SymbolCalculus.Claim)
    (hAssoc : CompAssoc.Claim)
    (hJ : ∀ s, IsPeriodic (J s))
    (hF : ∀ s, IsPeriodicKernel (J s.succ) (J s.castSucc) (F s)) {u v : Fin (b + 1)}
    {K : (J u).Carrier → (J v).Carrier → ℂ} (h : IsBracketing J F u v K) :
    ∀ (s : Fin b), v = s.succ → u < s.castSucc →
      ∃ K' : (J u).Carrier → (J s.castSucc).Carrier → ℂ, IsBracketing J F u s.castSucc K' ∧
        HEq K (compKernel K' (F s)) := by
  induction h with
  | leaf s' =>
    intro s hv hu
    have : s' = s := Fin.succ_injective _ hv
    subst this
    exact absurd hu (lt_irrefl _)
  | @node u m v P Q hP hQ pP pQ _ ihQ =>
    intro s hv hu
    subst hv
    by_cases hm : m = s.castSucc
    · subst hm
      refine ⟨P, hP, ?_⟩
      have := eq_of_heq (hQ.heq_of_leaf s rfl rfl)
      subst this
      rfl
    · have hlt : m < s.castSucc := by
        have h1 := hQ.src_lt
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h1 ⊢
        have h2 : (m : ℕ) ≠ s := fun e => hm (Fin.ext (by simpa using e))
        omega
      obtain ⟨Q', hQ', e⟩ := ihQ s rfl hlt
      have e' := eq_of_heq e
      subst e'
      have pQ' := hQ'.isPeriodicKernel hCalc hJ hF
      have has := hAssoc (J m) (J u) (J s.castSucc) (J s.succ) (hJ _) (hJ _) (hJ _) (hJ _) P Q' (F s)
        pP pQ' (hF s)
      refine ⟨compKernel P Q', IsBracketing.node P Q' hP hQ' pP pQ', ?_⟩
      exact heq_of_eq has.2.2.2.2.2.2.2.2.symm
theorem _root_.YangMills.Construction.PeriodicOperators.IsBracketing.eq_of_val_eq
    (hCalc : SymbolCalculus.Claim)
    (hAssoc : CompAssoc.Claim)
    (hJ : ∀ s, IsPeriodic (J s))
    (hF : ∀ s, IsPeriodicKernel (J s.succ) (J s.castSucc) (F s)) (u : Fin (b + 1)) (n : ℕ) :
    ∀ (v : Fin (b + 1)), (v : ℕ) = n → ∀ K K' : (J u).Carrier → (J v).Carrier → ℂ,
      IsBracketing J F u v K → IsBracketing J F u v K' → K = K' := by
  induction n with
  | zero =>
    intro v hv K K' hK _
    have := hK.src_lt
    simp only [Fin.lt_def] at this
    omega
  | succ n ih =>
    intro v hv K K' hK hK'
    have hn : n < b := by
      have := v.isLt
      omega
    have hvs : v = (⟨n, hn⟩ : Fin b).succ := Fin.ext (by simpa using hv)
    subst hvs
    by_cases hu : u = (⟨n, hn⟩ : Fin b).castSucc
    · have e := eq_of_heq ((hK.heq_of_leaf _ hu rfl).trans (hK'.heq_of_leaf _ hu rfl).symm)
      exact e
    · have hlt : u < (⟨n, hn⟩ : Fin b).castSucc := by
        have h1 := hK.src_lt
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h1 ⊢
        have h2 : (u : ℕ) ≠ n := fun e => hu (Fin.ext (by simpa using e))
        omega
      obtain ⟨L, hL, e⟩ := hK.exists_split_last hCalc hAssoc hJ hF _ rfl hlt
      obtain ⟨L', hL', e'⟩ := hK'.exists_split_last hCalc hAssoc hJ hF _ rfl hlt
      have := ih _ (by simp) L L' hL hL'
      subst this
      exact eq_of_heq (e.trans e'.symm)
theorem exists_isBracketing_prefix (hCalc : SymbolCalculus.Claim)
    (hJ : ∀ s, IsPeriodic (J s))
    (hF : ∀ s, IsPeriodicKernel (J s.succ) (J s.castSucc) (F s)) (k : ℕ) (hk : k < b) :
    ∃ K, IsBracketing J F 0 (⟨k, hk⟩ : Fin b).succ K := by
  induction k with
  | zero => exact ⟨F ⟨0, hk⟩, IsBracketing.leaf ⟨0, hk⟩⟩
  | succ k ih =>
    obtain ⟨K, hK⟩ := ih (by omega)
    have pK := hK.isPeriodicKernel hCalc hJ hF
    exact ⟨compKernel K (F ⟨k + 1, hk⟩), IsBracketing.node K (F ⟨k + 1, hk⟩) hK
      (IsBracketing.leaf ⟨k + 1, hk⟩) pK (hF ⟨k + 1, hk⟩)⟩
theorem symbolHom_of_isBracketing_prefix (hCalc : SymbolCalculus.Claim)
    (hAssoc : CompAssoc.Claim)
    (hProd : SymbolAtPoint.CompSymbol)
    (hJ : ∀ s, IsPeriodic (J s))
    (hF : ∀ s, IsPeriodicKernel (J s.succ) (J s.castSucc) (F s)) (κ' : Fin 4 → ℂ)
    (hf : ∀ s, SymbolSummableAt (J s.succ) (J s.castSucc) (F s) κ') (k : ℕ) (hk : k < b) :
    ∀ K, IsBracketing J F 0 (⟨k, hk⟩ : Fin b).succ K →
      SymbolSummableAt (J (⟨k, hk⟩ : Fin b).succ) (J 0) K κ' ∧
        symbolHom (J (⟨k, hk⟩ : Fin b).succ) (J 0) K κ' =
          chainProd J (fun s => symbolHom (J s.succ) (J s.castSucc) (F s) κ') (k + 1)
            (Nat.succ_lt_succ hk) := by
  induction k with
  | zero =>
    intro K hK
    have e := eq_of_heq (hK.heq_of_leaf ⟨0, hk⟩ rfl rfl)
    subst e
    refine ⟨hf _, ?_⟩
    simp only [chainProd]
    exact (LinearMap.id_comp _).symm
  | succ k ih =>
    intro K hK
    have hlt : (0 : Fin (b + 1)) < (⟨k + 1, hk⟩ : Fin b).castSucc := by
      simp [Fin.lt_def]
    obtain ⟨L, hL, e⟩ := hK.exists_split_last hCalc hAssoc hJ hF _ rfl hlt
    have e' := eq_of_heq e
    subst e'
    have hL' : IsBracketing J F 0 (⟨k, by omega⟩ : Fin b).succ L := hL
    obtain ⟨fL, sL⟩ := ih (by omega) L hL'
    have pL := hL.isPeriodicKernel hCalc hJ hF
    have hp := hProd (J (⟨k + 1, hk⟩ : Fin b).castSucc) (J 0) (J (⟨k + 1, hk⟩ : Fin b).succ)
      (hJ _) (hJ _) (hJ _) L (F ⟨k + 1, hk⟩) κ' pL fL (hF _) (hf _)
    refine ⟨hp.2.2.1, ?_⟩
    rw [hp.2.2.2]
    simp only [chainProd]
    exact congrArg (fun A => LinearMap.comp A _) sL
end Bracketing
theorem bracketingsAgree_holds (hCalc : SymbolCalculus.Claim)
    (hAssoc : CompAssoc.Claim)
    (hProd : SymbolAtPoint.CompSymbol) (b : ℕ) (hb : 1 ≤ b)
    (J : Fin (b + 1) → PeriodicData)
    (F : (s : Fin b) → (J s.castSucc).Carrier → (J s.succ).Carrier → ℂ)
    (hJ : ∀ s, IsPeriodic (J s))
    (hF : ∀ s, IsPeriodicKernel (J s.succ) (J s.castSucc) (F s)) :
    BracketingsAgree J F := by
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
  refine ⟨fun K hK => hK.isPeriodicKernel hCalc hJ hF, ?_, ?_, ?_⟩
  · exact exists_isBracketing_prefix hCalc hJ hF k (Nat.lt_succ_self k)
  · intro K K' hK hK'
    exact IsBracketing.eq_of_val_eq hCalc hAssoc hJ hF 0 (k + 1) _ rfl K K' hK hK'
  · intro κ' hf K hK
    exact symbolHom_of_isBracketing_prefix hCalc hAssoc hProd hJ hF κ' hf k (Nat.lt_succ_self k) K hK
theorem claim_holds (hId : IdKernelFacts.Claim)
    (hFacts : Symbols.Claim) (hCalc : SymbolCalculus.Claim)
    (hDecay : ExpDecaySymbol.HolomorphicOnStrip) (hPoint : SymbolPointwise.Properties)
    (hCP : SymbolAtPoint.Claim)
    (hAssoc : CompAssoc.Claim)
    (hKernel : OpenStripHolomorphicKernel.Claim)
    (hInverse : OpenStripInverse.Claim) : Claim := by
  refine ⟨fun υ _ => interiorOfStripChar_holds υ, ?_,
    fun b hb J F hJ hF => bracketingsAgree_holds hCalc hAssoc hCP.2 b hb J F hJ hF, ?_⟩
  · intro I I' hI hI'
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro T hT hR
      exact symbolSummableOn_univ_of_isFiniteRange hId hFacts hI hI' hT hR
    · intro κ
      have hid := hId I hI
      exact ⟨hid.2.2.1 κ (mem_univ κ), hid.2.2.2.2.1 κ⟩
    · intro υ hυ C T hT hb
      rw [openStripInterior_eq_openImStrip]
      exact hDecay I I' hI hI' υ hυ C T hT hb
    · intro T κ hT hf
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hPoint I I' hI hI' T κ hT hf
      refine ⟨h1, h2, h3, h4, h5, ⟨h6, h7, h8⟩, ?_, ?_⟩
      · intro T' hT' hf' c c'
        exact hCP.1 I I' hI hI' T T' κ c c' hT hf hT' hf'
      · intro I'' hI'' S hS hfS
        exact hCP.2 I I' I'' hI hI' hI'' T S κ hT hf hS hfS
    · intro υ hυ M
      rw [openStripInterior_eq_openImStrip]
      exact hKernel I I' hI hI' υ hυ M
    · intro I'' I''' hI'' hI''' T S S' hT hS hS'
      exact hAssoc I I' I'' I''' hI hI' hI'' hI''' T S S' hT hS hS'
  · intro I hI υ hυ T
    rw [openStripInterior_eq_openImStrip]
    exact hInverse I hI υ hυ T
end YangMills.Construction.PeriodicOperators.StripSymbols
end
