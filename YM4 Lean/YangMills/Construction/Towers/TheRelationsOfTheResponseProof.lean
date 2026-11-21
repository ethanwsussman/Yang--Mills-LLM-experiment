import YangMills.Construction.PeriodicOperators.AssociativityOfProductsOfPeriodicOperators
import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.OrderOfHermitianMatricesUnderARootProof
import YangMills.Construction.PeriodicOperators.SymbolsOfCombinationsAndProductsAtAPoint
import YangMills.Construction.PeriodicOperators.TransposeOfAProductOfKernels
import YangMills.Construction.Towers.CalculusOfPlaneWaves
import YangMills.Construction.Towers.FreeOperatorsAtTheRealPoints
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.RelationsOfTheIteratedAveragesOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.StepsAtTheTrivialConfigurationOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.TheRelationsOfTheResponse
import YangMills.Construction.Towers.TheResponseOperators
import YangMills.Construction.Towers.TheSaddleSystemOfTheResponse
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.ResponseRelationsAtAllHeights
open YangMills.Construction.PeriodicOperators
def HasSymbolOnReals (I I' : PeriodicData) (T : I'.Carrier → I.Carrier → ℂ) : Prop :=
  IsPeriodicKernel I I' T ∧ SymbolSummableOn I I' T realDualPoints
def oneSubComp (A : PeriodicData) {D : PeriodicData} (Rt : A.Carrier → D.Carrier → ℂ)
    (R : D.Carrier → A.Carrier → ℂ) : A.Carrier → A.Carrier → ℂ :=
  fun ι' ι => idKernel A ι' ι - compKernel Rt R ι' ι
theorem zero_mem_realDualPoints : (0 : Fin 4 → ℂ) ∈ realDualPoints := fun _ => rfl
section Calculus
variable {I I' I'' I''' : PeriodicData}
theorem comp_symbol_facts (hp : SymbolAtPoint.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    (hT : HasSymbolOnReals I I' T) (hS : HasSymbolOnReals I'' I S) :
    (∀ ι' ι'', CompSummableAt T S ι' ι'') ∧ HasSymbolOnReals I'' I' (compKernel T S) ∧
      ∀ κ ∈ realDualPoints, symbolHom I'' I' (compKernel T S) κ =
        (symbolHom I I' T κ).comp (symbolHom I'' I S κ) := by
  have e := fun κ (hκ : κ ∈ realDualPoints) =>
    hp.2 I I' I'' hI hI' hI'' T S κ hT.1 (hT.2 κ hκ) hS.1 (hS.2 κ hκ)
  exact ⟨(e 0 zero_mem_realDualPoints).1, ⟨(e 0 zero_mem_realDualPoints).2.1, fun κ hκ => (e κ hκ).2.2.1⟩,
    fun κ hκ => (e κ hκ).2.2.2⟩
theorem linComb_symbol_facts (hp : SymbolAtPoint.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T T' : I'.Carrier → I.Carrier → ℂ} (hT : HasSymbolOnReals I I' T) (hT' : HasSymbolOnReals I I' T')
    (c c' : ℂ) :
    HasSymbolOnReals I I' (kernelLinComb c c' T T') ∧
      ∀ κ ∈ realDualPoints, symbolHom I I' (kernelLinComb c c' T T') κ =
        c • symbolHom I I' T κ + c' • symbolHom I I' T' κ := by
  have e := fun κ (hκ : κ ∈ realDualPoints) =>
    hp.1 I I' hI hI' T T' κ c c' hT.1 (hT.2 κ hκ) hT'.1 (hT'.2 κ hκ)
  exact ⟨⟨(e 0 zero_mem_realDualPoints).1, fun κ hκ => (e κ hκ).2.1⟩, fun κ hκ => (e κ hκ).2.2⟩
theorem zero_symbol_facts (hp : SymbolAtPoint.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : I'.Carrier → I.Carrier → ℂ} (hT : HasSymbolOnReals I I' T) :
    HasSymbolOnReals I I' (0 : I'.Carrier → I.Carrier → ℂ) ∧
      ∀ κ ∈ realDualPoints, symbolHom I I' (0 : I'.Carrier → I.Carrier → ℂ) κ = 0 := by
  have e : kernelLinComb 0 0 T T = 0 := by
    funext ι' ι
    simp [kernelLinComb]
  have f := linComb_symbol_facts hp hI hI' hT hT 0 0
  rw [e] at f
  exact ⟨f.1, fun κ hκ => by rw [f.2 κ hκ]; simp⟩
theorem eq_zero_of_symbol_eq_zero (hc : SymbolCalculus.Claim)
    (hp : SymbolAtPoint.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : I'.Carrier → I.Carrier → ℂ} (hT : HasSymbolOnReals I I' T)
    (h0 : ∀ κ ∈ realDualPoints, symbolHom I I' T κ = 0) : T = 0 := by
  have hs := (hc I I' hI hI').2.2.2.2.2.2.1 1 one_pos
  have K := hs.2.1 _ hs.2.2.1
  have z := zero_symbol_facts hp hI hI' hT
  exact (K.unique T hT.1 ⟨hT.2, h0⟩).trans (K.unique 0 z.1.1 ⟨z.1.2, z.2⟩).symm
theorem comp_idKernel (hc : SymbolCalculus.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T) :
    compKernel T (idKernel I) = T ∧ compKernel (idKernel I') T = T := by
  have u := (hc I I' hI hI').2.2.2.2.2.2.2.1 T hT
  exact ⟨u.2.2.2.2.1, u.2.2.2.2.2⟩
theorem linComb_comp (hc : SymbolCalculus.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    {T T' : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hT' : IsPeriodicKernel I I' T')
    (hS : IsPeriodicKernel I'' I S) (c c' : ℂ) :
    compKernel (kernelLinComb c c' T T') S =
      kernelLinComb c c' (compKernel T S) (compKernel T' S) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, e, -, -, -⟩ :=
    ((hc I I' hI hI').2.2.2.2.2.2.2.2 I'' hI'').2 T T' S S c c' hT hT' hS hS
  exact e
theorem comp_linComb (hc : SymbolCalculus.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    {T : I'.Carrier → I.Carrier → ℂ} {S S' : I.Carrier → I''.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hS : IsPeriodicKernel I'' I S)
    (hS' : IsPeriodicKernel I'' I S') (c c' : ℂ) :
    compKernel T (kernelLinComb c c' S S') =
      kernelLinComb c c' (compKernel T S) (compKernel T S') := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, e, -, -⟩ :=
    ((hc I I' hI hI').2.2.2.2.2.2.2.2 I'' hI'').2 T T S S' c c' hT hT hS hS'
  exact e
theorem comp_assoc (ha : CompAssoc.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    (hI''' : IsPeriodic I''') {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    {S' : I''.Carrier → I'''.Carrier → ℂ} (hT : IsPeriodicKernel I I' T)
    (hS : IsPeriodicKernel I'' I S) (hS' : IsPeriodicKernel I''' I'' S') :
    compKernel (compKernel T S) S' = compKernel T (compKernel S S') :=
  (ha I I' I'' I''' hI hI' hI'' hI''' T S S' hT hS hS').2.2.2.2.2.2.2.2
theorem zero_comp {J J' J'' : Type} (S : J → J'' → ℂ) :
    compKernel (0 : J' → J → ℂ) S = 0 := by
  funext a b
  simp [compKernel]
theorem comp_zero {J J' J'' : Type} (T : J' → J → ℂ) :
    compKernel T (0 : J → J'' → ℂ) = 0 := by
  funext a b
  simp [compKernel]
theorem symbolHom_idKernel (hid : IdKernelFacts.Claim)
    (hI : IsPeriodic I) (κ : Fin 4 → ℂ) :
    symbolHom I I (idKernel I) κ = LinearMap.id := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.symbolHom_idKernel <;> assumption
theorem idKernel_hasSymbolOnReals (hid : IdKernelFacts.Claim)
    (hI : IsPeriodic I) : HasSymbolOnReals I I (idKernel I) :=
  ⟨(hid I hI).1, fun κ _ => (hid I hI).2.2.1 κ (mem_univ κ)⟩
theorem oneSubComp_eq {D : PeriodicData} (Rt : I.Carrier → D.Carrier → ℂ)
    (R : D.Carrier → I.Carrier → ℂ) :
    oneSubComp I Rt R = kernelLinComb 1 (-1) (idKernel I) (compKernel Rt R) := by
  funext ι' ι
  simp [oneSubComp, kernelLinComb, sub_eq_add_neg]
theorem oneSubComp_hasSymbolOnReals (hp : SymbolAtPoint.Claim)
    (hid : IdKernelFacts.Claim) {D : PeriodicData}
    (hI : IsPeriodic I) (hD : IsPeriodic D)
    {Rt : I.Carrier → D.Carrier → ℂ} {R : D.Carrier → I.Carrier → ℂ}
    (oRt : HasSymbolOnReals D I Rt) (oR : HasSymbolOnReals I D R) :
    HasSymbolOnReals I I (oneSubComp I Rt R) := by
  rw [oneSubComp_eq]
  exact (linComb_symbol_facts hp hI hI (idKernel_hasSymbolOnReals hid hI)
    (comp_symbol_facts hp hD hI hI oRt oR).2.1 1 (-1)).1
theorem symbolHom_add_eq (hp : SymbolAtPoint.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T T' Z : I'.Carrier → I.Carrier → ℂ} (hT : HasSymbolOnReals I I' T) (hT' : HasSymbolOnReals I I' T')
    (hZ : Z = kernelLinComb 1 1 T T') {M : (Fin 4 → ℂ) → QuotHom I I'}
    (hM : ∀ κ ∈ realDualPoints, symbolHom I I' T' κ = M κ) :
    ∀ κ ∈ realDualPoints, symbolHom I I' Z κ = symbolHom I I' T κ + M κ := by
  subst hZ
  intro κ hκ
  rw [(linComb_symbol_facts hp hI hI' hT hT' 1 1).2 κ hκ, hM κ hκ, one_smul, one_smul]
end Calculus
theorem relations_of_saddle (hc : SymbolCalculus.Claim)
    (hp : SymbolAtPoint.Claim)
    (ha : CompAssoc.Claim)
    (hid : IdKernelFacts.Claim)
    {A B C D E : PeriodicData} (iA : IsPeriodic A) (iB : IsPeriodic B)
    (iC : IsPeriodic C) (iD : IsPeriodic D) (iE : IsPeriodic E)
    {d : B.Carrier → A.Carrier → ℂ} {dt : A.Carrier → B.Carrier → ℂ}
    {c : C.Carrier → B.Carrier → ℂ} {ct : B.Carrier → C.Carrier → ℂ}
    {et : D.Carrier → E.Carrier → ℂ} {Qt : B.Carrier → E.Carrier → ℂ}
    {R : D.Carrier → A.Carrier → ℂ} {Rt : A.Carrier → D.Carrier → ℂ}
    {h : B.Carrier → E.Carrier → ℂ} {ν : E.Carrier → E.Carrier → ℂ} {X : B.Carrier → B.Carrier → ℂ}
    (od : HasSymbolOnReals A B d) (odt : HasSymbolOnReals B A dt) (oc : HasSymbolOnReals B C c)
    (oct : HasSymbolOnReals C B ct) (oet : HasSymbolOnReals E D et) (oQt : HasSymbolOnReals E B Qt)
    (oR : HasSymbolOnReals A D R) (oRt : HasSymbolOnReals D A Rt) (oh : HasSymbolOnReals E B h)
    (oν : HasSymbolOnReals E E ν)
    (hX : X = kernelLinComb 1 1 (compKernel ct c)
      (compKernel (compKernel d (oneSubComp A Rt R)) dt))
    (hRRt : compKernel R Rt = idKernel D)
    (hdd : compKernel dt ct = 0)
    (hQ : compKernel dt Qt = compKernel Rt et)
    (hS : compKernel X h = compKernel Qt ν)
    (hpos : ∀ κ ∈ realDualPoints, ∀ (ρ : A.UnitQuot → ℂ) (w : D.UnitQuot → ℂ),
      symbolHom A D R κ ρ = 0 →
      symbolHom A A (compKernel dt d) κ ρ = symbolHom D A Rt κ w → ρ = 0) :
    compKernel (oneSubComp A Rt R) (compKernel dt h) = 0 ∧ compKernel et ν = 0 ∧
      compKernel (compKernel ct c) h = compKernel Qt ν := by
  have oId := idKernel_hasSymbolOnReals hid iA
  have oP := (comp_symbol_facts hp iD iA iA oRt oR).2.1
  have oE0 := oneSubComp_hasSymbolOnReals hp hid iA iD oRt oR
  have eE0 := oneSubComp_eq Rt R
  obtain ⟨F, hF⟩ : ∃ F, F = oneSubComp A Rt R := ⟨_, rfl⟩
  rw [← hF] at oE0 eE0 hX ⊢
  have oG0 := (comp_symbol_facts hp iB iA iE odt oh).2.1
  obtain ⟨G, hG⟩ : ∃ G, G = compKernel dt h := ⟨_, rfl⟩
  rw [← hG] at oG0 ⊢
  have oρ := (comp_symbol_facts hp iA iA iE oE0 oG0).2.1
  obtain ⟨P, hP⟩ : ∃ P, P = compKernel F G := ⟨_, rfl⟩
  rw [← hP] at oρ ⊢
  have oW := (comp_symbol_facts hp iE iD iE oet oν).2.1
  obtain ⟨W, hW⟩ : ∃ W, W = compKernel et ν := ⟨_, rfl⟩
  rw [← hW] at oW ⊢
  have oΔ := (comp_symbol_facts hp iB iA iA odt od).2.1
  have hRP : compKernel R (compKernel Rt R) = R := by
    rw [← comp_assoc ha iA iD iD iA oR.1 oRt.1 oR.1, hRRt, (comp_idKernel hc iA iD oR.1).2]
  have hRE : compKernel R F = 0 := by
    rw [eE0, comp_linComb hc iA iD iA oR.1 oId.1 oP.1 1 (-1), (comp_idKernel hc iA iD oR.1).1, hRP]
    funext a b
    simp [kernelLinComb]
  have hRρ : compKernel R P = 0 := by
    rw [hP, ← comp_assoc ha iA iD iA iE oR.1 oE0.1 oG0.1, hRE, zero_comp]
  have odE := (comp_symbol_facts hp iA iB iA od oE0).2.1
  have oB := (comp_symbol_facts hp iA iB iB odE odt).2.1
  have oA := (comp_symbol_facts hp iC iB iB oct oc).2.1
  have hBh : compKernel (compKernel (compKernel d F) dt) h = compKernel d P := by
    rw [comp_assoc ha iA iB iB iE odE.1 odt.1 oh.1, ← hG, comp_assoc ha iA iB iA iE od.1 oE0.1 oG0.1, ← hP]
  have hXh : compKernel X h =
      kernelLinComb 1 1 (compKernel (compKernel ct c) h) (compKernel d P) := by
    rw [hX, linComb_comp hc iB iB iE oA.1 oB.1 oh.1 1 1, hBh]
  have och := (comp_symbol_facts hp iB iC iE oc oh).2.1
  have oAh := (comp_symbol_facts hp iB iB iE oA oh).2.1
  have odρ := (comp_symbol_facts hp iA iB iE od oρ).2.1
  have hΔ : compKernel (compKernel dt d) P = compKernel Rt W := by
    have s1 : compKernel dt (compKernel X h) = compKernel (compKernel dt d) P := by
      rw [hXh, comp_linComb hc iB iA iE odt.1 oAh.1 odρ.1 1 1,
        comp_assoc ha iC iB iB iE oct.1 oc.1 oh.1, ← comp_assoc ha iB iA iC iE odt.1 oct.1 och.1, hdd,
        zero_comp, ← comp_assoc ha iB iA iA iE odt.1 od.1 oρ.1]
      funext a b
      simp [kernelLinComb]
    have s2 : compKernel dt (compKernel Qt ν) = compKernel Rt W := by
      rw [← comp_assoc ha iB iA iE iE odt.1 oQt.1 oν.1, hQ, comp_assoc ha iD iA iE iE oRt.1 oet.1 oν.1, ← hW]
    rw [← s1, hS, s2]
  have hsym : ∀ κ ∈ realDualPoints, symbolHom E A P κ = 0 ∧ symbolHom E D W κ = 0 := by
    intro κ hκ
    have a1 := (comp_symbol_facts hp iA iD iE oR oρ).2.2 κ hκ
    rw [hRρ, (zero_symbol_facts hp iE iD oW).2 κ hκ] at a1
    have a2 := (comp_symbol_facts hp iA iA iE oΔ oρ).2.2 κ hκ
    have a3 := (comp_symbol_facts hp iD iA iE oRt oW).2.2 κ hκ
    rw [hΔ, a3] at a2
    have a4 := (comp_symbol_facts hp iA iD iD oR oRt).2.2 κ hκ
    rw [hRRt, symbolHom_idKernel hid iD κ] at a4
    have key : ∀ ε, symbolHom E A P κ ε = 0 := fun ε =>
      hpos κ hκ _ (symbolHom E D W κ ε) (by simpa using (LinearMap.congr_fun a1 ε).symm)
        (by simpa using (LinearMap.congr_fun a2 ε).symm)
    refine ⟨LinearMap.ext key, LinearMap.ext fun ε => ?_⟩
    have b : symbolHom D A Rt κ (symbolHom E D W κ ε) = 0 := by
      have e := LinearMap.congr_fun a2 ε
      simp only [LinearMap.comp_apply] at e
      rw [e, key ε, map_zero]
    have e := LinearMap.congr_fun a4 (symbolHom E D W κ ε)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, b, map_zero] at e
    simpa using e
  have zρ : P = 0 := eq_zero_of_symbol_eq_zero hc hp iE iA oρ fun κ hκ => (hsym κ hκ).1
  have zW : W = 0 := eq_zero_of_symbol_eq_zero hc hp iE iD oW fun κ hκ => (hsym κ hκ).2
  refine ⟨zρ, zW, ?_⟩
  rw [← hS, hXh, zρ, comp_zero]
  funext a b
  simp [kernelLinComb]
theorem wInner_sub_smul {J : Type} [Finite J] (w : J → ℝ) (f g g' g'' : J → ℂ) (a b : ℂ) :
    wInner w f (g - a • g' - b • g'') =
      wInner w f g - a * wInner w f g' - b * wInner w f g'' := by
  classical
  have := Fintype.ofFinite J
  simp only [wInner, wPairing, tsum_fintype, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem wInner_self {J : Type} [Fintype J] (w : J → ℝ) (f : J → ℂ) :
    wInner w f f = ((∑ i, w i * ‖f i‖ ^ 2 : ℝ) : ℂ) := by apply _root_.YangMills.Construction.PeriodicOperators.RootConjugationOrder.wInner_self_eq <;> assumption
theorem eq_zero_of_coercive {A D : PeriodicData} (iA : IsPeriodic A)
    (hw : ∀ x, 0 < A.quotWeight 1 x) {Rm : QuotHom A D} {Rtm : QuotHom D A}
    {Dl Ym : QuotHom A A} {c : ℝ} (hc : 0 < c) (hadj : IsAdjointQuotHom Rm Rtm)
    (hY : Ym = Dl + Rtm.comp Rm)
    (hlow : LoewnerLE ((c : ℂ) • (Dl + scalarQuotHom A 1)) Ym)
    (hnn : LoewnerLE (scalarQuotHom A 0) Dl) {ρ : A.UnitQuot → ℂ} {w : D.UnitQuot → ℂ}
    (h0 : Rm ρ = 0) (h1 : Dl ρ = Rtm w) : ρ = 0 := by
  classical
  have := iA.finite_quot
  have := Fintype.ofFinite A.UnitQuot
  have e1 : Ym ρ = Rtm w := by
    rw [hY]
    simp [h0, h1]
  have e2 : wInner (A.quotWeight 1) ρ (Ym ρ) = 0 := by
    rw [← hlow.isSelfAdjoint_right ρ ρ, e1, ← hadj ρ w, h0]
    simp [wInner, wPairing]
  have e3 : (Ym - (c : ℂ) • (Dl + scalarQuotHom A 1)) ρ =
      Ym ρ - (c : ℂ) • Dl ρ - (c : ℂ) • ρ := by
    simp [scalarQuotHom, smul_add, sub_sub]
  have n1 := hlow.re_nonneg ρ
  rw [e3, wInner_sub_smul, e2, wInner_self] at n1
  have n2 := hnn.re_nonneg ρ
  have e4 : (Dl - scalarQuotHom A 0) ρ = Dl ρ := by
    simp [scalarQuotHom]
  rw [e4] at n2
  simp only [zero_sub, Complex.sub_re, Complex.neg_re, Complex.re_ofReal_mul,
    Complex.ofReal_re] at n1
  have hs : (∑ i, A.quotWeight 1 i * ‖ρ i‖ ^ 2) ≤ 0 := by
    by_contra hneg
    have : 0 < c * ∑ i, A.quotWeight 1 i * ‖ρ i‖ ^ 2 := mul_pos hc (not_le.mp hneg)
    have := mul_nonneg hc.le n2
    linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg (hw i).le (by positivity))).mp
    (le_antisymm hs (Finset.sum_nonneg fun i _ => mul_nonneg (hw i).le (by positivity)))
  funext i
  have hi := hz i (Finset.mem_univ i)
  have hn : ‖ρ i‖ ^ 2 = 0 := (mul_eq_zero.mp hi).resolve_left (hw i).ne'
  simpa using hn
open YangMills.Construction.Tower.ResponseProperties (ResponseRelations coboundaryLaplacian
  oneMinusSmoothingSquare responseDivergenceKernel)
open YangMills.Construction.Tower.FreeResolvents (trivialRescaledOperators)
open YangMills.Construction.Tower.BackgroundFieldResponse (responseKernel responseDefect)
open YangMills.Construction.Tower.PlaneWaveCalculus (vertexCoboundaryT edgeCoboundaryT)
theorem mem_openImStrip_of_real {κ : Fin 4 → ℂ} (hκ : κ ∈ realDualPoints) {υ : ℝ} (hυ : 0 < υ) :
    κ ∈ openImStrip υ := by
  intro μ
  rw [hκ μ]
  simpa using hυ
theorem nonneg_of_mem_halfSupRate {δ : ℝ} (hδ : δ ∈ FreeStrip.halfSupRate) : 0 ≤ δ := by
  obtain ⟨_, e⟩ := hδ
  rw [← e]
  have : 0 ≤ sSup FreeStrip.admissibleRates :=
    Real.sSup_nonneg fun x hx => by
      obtain ⟨C, hC⟩ := hx
      exact hC.1.1.le
  change 0 ≤ 1 / 2 * sSup FreeStrip.admissibleRates
  positivity
theorem responseRelations_holds (h₁ : ResponseSaddle.SaddleEquations) (h₂ : ResponseOperators.Claim)
    (h₃ : FreeOperators.FreeOperatorsArePeriodic) (h₄ : PeriodicOperators.TowerIndexSets.Claim)
    (h₅ : SymbolCalculus.Claim) (h₆ : SymbolAtPoint.Claim)
    (h₇ : CompAssoc.Claim)
    (h₈ : IdKernelFacts.Claim) (h₉ : TransposeComp.Claim)
    (h₁₀ : FullSpace.RescaledTrivialRelations)
    (h₁₁ : FreeCoercivity.FreeOperatorsCoercive) (h₁₂ : FreeSymbolsAtRealPoints)
    (h₁₃ : FullSpace.RescaledIterRelations)
    (h₁₄ : FullSpace.RescaledTrivialSteps)
    (h₁₅ : PlaneWaveCalculus.PlaneWaveCalculusHolds) (h₁₆ : Quotients.QuotientTransposeNorm) :
    ResponseRelationsHold := by
  intro L hL k hk
  have hk0 : 0 ≤ k := Nat.zero_le k
  have iA := (h₄ L hL k 0 hk0).1
  have iB := (h₄ L hL k 0 hk0).2.1
  have iC := (h₄ L hL k 0 hk0).2.2
  have iD := (h₄ L hL k k le_rfl).1
  have iE := (h₄ L hL k k le_rfl).2.1
  obtain ⟨hm, ho⟩ := h₃.2 L hL k hk
  have op : ∀ {I I' : PeriodicData} {T : I'.Carrier → I.Carrier → ℂ}, IsPeriodic I →
      IsPeriodic I' → FreeOperators.HasFiniteRangeEveryRate I I' T →
      HasSymbolOnReals I I' T := fun iI iI' h =>
    ⟨h.1, fun κ _ => ((h₅ _ _ iI iI').1 _ h.1 h.2.1).1 κ (mem_univ κ)⟩
  have od : HasSymbolOnReals (colourVertices L k 0) (colourEdges L k 0)
      (FullSpace.scaledVertexCoboundaryKernel L k 0) :=
    op iA iB (hm.vertexCoboundary 0 hk0).finite_range
  have odk : HasSymbolOnReals (colourVertices L k k) (colourEdges L k k)
      (FullSpace.scaledVertexCoboundaryKernel L k k) :=
    op iD iE (hm.vertexCoboundary k le_rfl).finite_range
  have odt : HasSymbolOnReals (colourEdges L k 0) (colourVertices L k 0)
      (vertexCoboundaryT L k 0) := op iB iA (ho.vertexCoboundary_transpose 0 hk0)
  have oc : HasSymbolOnReals (colourEdges L k 0) (colourFaces L k 0)
      (FullSpace.scaledEdgeCoboundaryKernel L k 0) :=
    op iB iC (hm.edgeCoboundary 0 hk0).finite_range
  have oct : HasSymbolOnReals (colourFaces L k 0) (colourEdges L k 0)
      (edgeCoboundaryT L k 0) := op iC iB (ho.edgeCoboundary_transpose 0 hk0)
  have oet : HasSymbolOnReals (colourEdges L k k) (colourVertices L k k)
      (vertexCoboundaryT L k k) := op iE iD (ho.vertexCoboundary_transpose k le_rfl)
  have oQ : HasSymbolOnReals (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q :=
    op iB iE hm.edgeAverage.finite_range
  have oQt : HasSymbolOnReals (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt :=
    op iE iB ho.edgeAverage_transpose
  have oR : HasSymbolOnReals (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R :=
    op iA iD hm.vertexAverage.finite_range
  have oRt : HasSymbolOnReals (colourVertices L k k) (colourVertices L k 0) (trivialRescaledOperators L k).Rt :=
    op iD iA ho.vertexAverage_transpose
  obtain ⟨δ₀, hδ, hall⟩ := h₂
  have hr := hall L hL k hk
  obtain ⟨υ, hυ, -, hrh, hrν⟩ := hr.exists_rate
  have hυ0 : 0 < υ := by
    have := nonneg_of_mem_halfSupRate hδ
    linarith
  have oh : HasSymbolOnReals (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) :=
    ⟨hr.resp_periodic, fun κ hκ => hrh.summable κ (mem_openImStrip_of_real hκ hυ0)⟩
  have oν : HasSymbolOnReals (colourEdges L k k) (colourEdges L k k) (responseDefect L k) :=
    ⟨hr.defect_periodic, fun κ hκ => hrν.summable κ (mem_openImStrip_of_real hκ hυ0)⟩
  have rel := h₁₀ L hL k hk
  have hX : (trivialRescaledOperators L k).X = kernelLinComb 1 1
      (compKernel (edgeCoboundaryT L k 0)
        (FullSpace.scaledEdgeCoboundaryKernel L k 0))
      (compKernel (compKernel (FullSpace.scaledVertexCoboundaryKernel L k 0)
        (oneSubComp (colourVertices L k 0) (D := colourVertices L k k) (trivialRescaledOperators L k).Rt
          (trivialRescaledOperators L k).R))
        (vertexCoboundaryT L k 0)) := by
    refine rel.X_eq.trans ?_
    funext a b
    simp only [kernelLinComb, one_mul]
    rfl
  have hRRt : compKernel (trivialRescaledOperators L k).R (trivialRescaledOperators L k).Rt =
      idKernel (colourVertices L k k) :=
    (h₁₃ L hL k hk _ (h₁₄ L hL k hk).1).R_comp_Rt
  have hdd : compKernel (vertexCoboundaryT L k 0)
      (edgeCoboundaryT L k 0) = 0 :=
    (h₁₅ L hL k hk).2.2.2.2.2.1.transpose_comp_transpose
  have hQ : compKernel (vertexCoboundaryT L k 0) (trivialRescaledOperators L k).Qt =
      compKernel (trivialRescaledOperators L k).Rt (vertexCoboundaryT L k k) := by
    have t₁ := (h₉ (.lattice _ iB) (.lattice _ iE) (.lattice _ iA) (trivialRescaledOperators L k).Q
      (FullSpace.scaledVertexCoboundaryKernel L k 0) (comp_symbol_facts h₆ iB iE iA oQ od).1).2
    have t₂ := (h₉ (.lattice _ iD) (.lattice _ iE) (.lattice _ iA)
      (FullSpace.scaledVertexCoboundaryKernel L k k) (trivialRescaledOperators L k).R
      (comp_symbol_facts h₆ iD iE iA odk oR).1).2
    have q : compKernel (trivialRescaledOperators L k).Q (FullSpace.scaledVertexCoboundaryKernel L k 0) =
        compKernel (FullSpace.scaledVertexCoboundaryKernel L k k) (trivialRescaledOperators L k).R :=
      rel.Q_comp_d
    exact t₁.trans ((congrArg (fun Z => wTranspose (KernelDomain.lattice _ iA).weight
      (KernelDomain.lattice _ iE).weight Z) q).trans t₂.symm)
  have sys := h₁ L hL k hk
  have hDelta : compKernel (vertexCoboundaryT L k 0)
      (FullSpace.scaledVertexCoboundaryKernel L k 0) = (trivialRescaledOperators L k).Delta :=
    rel.Delta_eq.symm
  have hpos : ∀ κ ∈ realDualPoints, ∀ (ρ : (colourVertices L k 0).UnitQuot → ℂ)
      (w : (colourVertices L k k).UnitQuot → ℂ),
      symbolHom (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R κ ρ = 0 →
      symbolHom (colourVertices L k 0) (colourVertices L k 0)
          (compKernel (vertexCoboundaryT L k 0)
            (FullSpace.scaledVertexCoboundaryKernel L k 0)) κ ρ =
        symbolHom (colourVertices L k k) (colourVertices L k 0) (trivialRescaledOperators L k).Rt κ w →
          ρ = 0 := by
    intro κ hκ ρ w e0 e1
    have e1' : symbolHom (colourVertices L k 0) (colourVertices L k 0)
          (trivialRescaledOperators L k).Delta κ ρ =
        symbolHom (colourVertices L k k) (colourVertices L k 0) (trivialRescaledOperators L k).Rt κ w :=
      (congrArg (fun Z => symbolHom (colourVertices L k 0) (colourVertices L k 0) Z κ ρ)
        hDelta).symm.trans e1
    obtain ⟨_, -, cY, hcY, _, -, hco⟩ := h₁₁
    have hY := ((hco L hL k hk).2.2.2 κ hκ).2.Y_lower
    obtain ⟨-, hnn, -, hadj, -, -⟩ := h₁₂ L hL k hk κ hκ
    have oΔ : HasSymbolOnReals (colourVertices L k 0) (colourVertices L k 0)
        (trivialRescaledOperators L k).Delta :=
      (congrArg (HasSymbolOnReals (colourVertices L k 0) (colourVertices L k 0)) hDelta).mp
        (comp_symbol_facts h₆ iB iA iA odt od).2.1
    have oP := comp_symbol_facts h₆ iD iA iA oRt oR
    have eY : (trivialRescaledOperators L k).Y = kernelLinComb 1 1 (trivialRescaledOperators L k).Delta
        (compKernel (trivialRescaledOperators L k).Rt (trivialRescaledOperators L k).R) := by
      funext a b
      simp only [kernelLinComb, one_mul]
      rfl
    have hYs : symbolHom (colourVertices L k 0) (colourVertices L k 0) (trivialRescaledOperators L k).Y κ =
        symbolHom (colourVertices L k 0) (colourVertices L k 0) (trivialRescaledOperators L k).Delta κ +
          (symbolHom (colourVertices L k k) (colourVertices L k 0) (trivialRescaledOperators L k).Rt κ).comp
            (symbolHom (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R κ) :=
      symbolHom_add_eq h₆ iA iA oΔ oP.2.1 eY oP.2.2 κ hκ
    have hw : ∀ x, 0 < (colourVertices L k 0).quotWeight 1 x := by
      intro x
      obtain ⟨ι, rfl⟩ := Quot.exists_rep x
      have h := ((h₁₆ _ _ iA iA 1 one_pos).2.1 1 (Or.inl rfl)).1.2 ι
      have e : (colourVertices L k 0).quotWeight 1 (Quot.mk _ ι) =
        (colourVertices L k 0).weightOf ι := h
      rw [e]
      exact iA.weight_pos _
    exact eq_zero_of_coercive iA hw hcY.1 hadj hYs hY hnn e0 e1'
  obtain ⟨g₀, e₀, c₀⟩ := relations_of_saddle h₅ h₆ h₇ h₈ iA iB iC iD iE od odt oc oct oet oQt oR
    oRt oh oν hX hRRt hdd hQ sys.hessian_eq hpos
  have oE := oneSubComp_hasSymbolOnReals h₆ h₈ iA iD oRt oR
  have fG := comp_symbol_facts h₆ iB iA iE odt oh
  have fA := comp_symbol_facts h₆ iC iB iB oct oc
  exact
    { smoothing_comp_summable := sys.smoothing_summable
      smoothing_comp := sys.smoothing_eq
      laplacian_summable := fA.1
      laplacian_comp_summable := (comp_symbol_facts h₆ iB iB iE fA.2.1 oh).1
      defect_summable := sys.defect_summable
      laplacian_comp := c₀
      smoothing_square_summable := (comp_symbol_facts h₆ iD iA iA oRt oR).1
      divergence_summable := fG.1
      gauge_summable := (comp_symbol_facts h₆ iA iA iE oE fG.2.1).1
      gauge_comp := g₀
      defect_divergence_summable := (comp_symbol_facts h₆ iE iD iE oet oν).1
      defect_divergence := e₀ }
end YangMills.Construction.Tower.ResponseRelationsAtAllHeights
end
