import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import YangMills.Construction.PeriodicOperators.InvertibilityNearTheRealPoints
import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHom
import YangMills.Construction.PeriodicOperators.OrderOfHermitianMatricesUnderARoot
import YangMills.Construction.PeriodicOperators.SandwichesOfARootedPair
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.RootedSandwiches
open StripSymbols (openStripInterior)
section Matrices
variable {I : PeriodicData}
theorem isUnit_toEnd {M : QuotHom I I} (hM : IsInvertibleQuotHom M) :
    IsUnit (M : Module.End ℂ (I.UnitQuot → ℂ)) := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.isUnit_of_isInvertibleQuotHom <;> assumption
theorem of_isUnit_toEnd {M : QuotHom I I}
    (hM : IsUnit (M : Module.End ℂ (I.UnitQuot → ℂ))) : IsInvertibleQuotHom M := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.isInvertibleQuotHom_of_isUnit <;> assumption
theorem invertible_of_conj {P Pinv Y : QuotHom I I} (hleft : Pinv.comp P = LinearMap.id)
    (hright : P.comp Pinv = LinearMap.id) (hconj : IsInvertibleQuotHom (P.comp (Y.comp P))) :
    IsInvertibleQuotHom Y ∧
      quotHomInverse Y = P.comp ((quotHomInverse (P.comp (Y.comp P))).comp P) := by
  let p : Module.End ℂ (I.UnitQuot → ℂ) := P
  let pinv : Module.End ℂ (I.UnitQuot → ℂ) := Pinv
  let y : Module.End ℂ (I.UnitQuot → ℂ) := Y
  have hl : pinv * p = 1 := hleft
  have hr : p * pinv = 1 := hright
  have hunit : IsUnit (p * (y * p)) := isUnit_toEnd hconj
  let w : Module.End ℂ (I.UnitQuot → ℂ) := Ring.inverse (p * (y * p))
  have hw : (p * (y * p)) * w = 1 := Ring.mul_inverse_cancel _ hunit
  have hw' : w * (p * (y * p)) = 1 := Ring.inverse_mul_cancel _ hunit
  have hyw : y * (p * w) = pinv := by
    calc y * (p * w) = (pinv * p) * (y * (p * w)) := by rw [hl, one_mul]
      _ = pinv * ((p * (y * p)) * w) := by simp only [mul_assoc]
      _ = pinv := by rw [hw, mul_one]
  have hwy : w * (p * y) = pinv := by
    calc w * (p * y) = (w * (p * y)) * (p * pinv) := by rw [hr, mul_one]
      _ = (w * (p * (y * p))) * pinv := by simp only [mul_assoc]
      _ = pinv := by rw [hw', one_mul]
  have hyr : y * (p * (w * p)) = 1 := by
    calc y * (p * (w * p)) = (y * (p * w)) * p := by simp only [mul_assoc]
      _ = 1 := by rw [hyw, hl]
  have hyl : (p * (w * p)) * y = 1 := by
    calc (p * (w * p)) * y = p * (w * (p * y)) := by simp only [mul_assoc]
      _ = 1 := by rw [hwy, hr]
  have hy : IsUnit y := ⟨⟨y, p * (w * p), hyr, hyl⟩, rfl⟩
  exact ⟨of_isUnit_toEnd hy, left_inv_eq_right_inv (Ring.inverse_mul_cancel y hy) hyr⟩
end Matrices
section Holomorphy
variable {I I' I'' : PeriodicData}
theorem familyHolomorphicOn_mono {U U' : Set (Fin 4 → ℂ)} (hU' : IsOpen U') (hsub : U' ⊆ U)
    {M : (Fin 4 → ℂ) → QuotHom I I'} (hM : QuotHomFamilyHolomorphicOn (n := 4) U M) :
    QuotHomFamilyHolomorphicOn (n := 4) U' M :=
  ⟨hM.1, hU', fun e => ⟨hU', (hM.2.2 e).2.1.mono hsub, fun z hz => (hM.2.2 e).2.2 z (hsub hz)⟩⟩
theorem familyHolomorphicOn_comp (hE : EntriesDets.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    {U : Set (Fin 4 → ℂ)} {F : (Fin 4 → ℂ) → QuotHom I I'} {G : (Fin 4 → ℂ) → QuotHom I'' I}
    (hF : QuotHomFamilyHolomorphicOn (n := 4) U F) (hG : QuotHomFamilyHolomorphicOn (n := 4) U G) :
    QuotHomFamilyHolomorphicOn (n := 4) U fun κ => (F κ).comp (G κ) := by
  have hpoly := (hE.2.2.2.2.2.2.1 4 U (by norm_num) hF.2.1).2.2.2.2.2.1
  have hent := (hE.1 I I' I'' hI hI' hI'').2.2
  have := hI.finite_quot
  let eqv : Fin (Nat.card I.UnitQuot) ≃ I.UnitQuot := (Finite.equivFin I.UnitQuot).symm
  refine ⟨hF.1, hF.2.1, fun e => ?_⟩
  have hmul : ∀ i, EntriesDets.HolomorphicFnOn (n := 4) U
      fun z => linearMapEntry (F z) e.1 (eqv i) * linearMapEntry (G z) (eqv i) e.2 := by
    intro i
    have hprod := (hpoly.2.2.1 2 ![fun z => linearMapEntry (F z) e.1 (eqv i),
      fun z => linearMapEntry (G z) (eqv i) e.2] (by
        intro j
        fin_cases j
        · exact hF.2.2 (e.1, eqv i)
        · exact hG.2.2 (eqv i, e.2))).2
    simpa [Fin.prod_univ_two] using hprod
  have hsum := (hpoly.2.2.1 _ _ hmul).1
  have heq : (fun (z : Fin 4 → ℂ) (_ : Fin 1) => quotHomEntries ((F z).comp (G z)) e) =
      fun z _ => ∑ i, linearMapEntry (F z) e.1 (eqv i) * linearMapEntry (G z) (eqv i) e.2 := by
    funext z _
    simp only [quotHomEntries]
    rw [hent (F z) (G z) e.1 e.2, ← finsum_comp_equiv eqv, finsum_eq_sum_of_fintype]
  rw [heq]
  exact hsum
theorem familyHolomorphicOn_add (hE : EntriesDets.Claim)
    {U : Set (Fin 4 → ℂ)} {F G : (Fin 4 → ℂ) → QuotHom I I'}
    (hF : QuotHomFamilyHolomorphicOn (n := 4) U F) (hG : QuotHomFamilyHolomorphicOn (n := 4) U G) :
    QuotHomFamilyHolomorphicOn (n := 4) U fun κ => F κ + G κ := by
  have hpoly := (hE.2.2.2.2.2.2.1 4 U (by norm_num) hF.2.1).2.2.2.2.2.1
  refine ⟨hF.1, hF.2.1, fun e => ?_⟩
  have hpair := (hpoly.2.2.1 2 ![fun z => quotHomEntries (F z) e, fun z => quotHomEntries (G z) e] (by
      intro j
      fin_cases j
      · exact hF.2.2 e
      · exact hG.2.2 e)).1
  have heq : (fun (z : Fin 4 → ℂ) (_ : Fin 1) => quotHomEntries (F z + G z) e) =
      fun z _ => ∑ i, (![fun z => quotHomEntries (F z) e, fun z => quotHomEntries (G z) e] :
        Fin 2 → (Fin 4 → ℂ) → ℂ) i z := by
    funext z _
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rfl
  rw [heq]
  exact hpair
theorem familyHolomorphicOn_smul (hE : EntriesDets.Claim)
    {U : Set (Fin 4 → ℂ)} {F : (Fin 4 → ℂ) → QuotHom I I'} (w : ℂ)
    (hF : QuotHomFamilyHolomorphicOn (n := 4) U F) :
    QuotHomFamilyHolomorphicOn (n := 4) U fun κ => w • F κ := by
  have hpoly := (hE.2.2.2.2.2.2.1 4 U (by norm_num) hF.2.1).2.2.2.2.2.1
  exact ⟨hF.1, hF.2.1, fun e => hpoly.2.2.2 w _ (hF.2.2 e)⟩
theorem familyHolomorphicOn_const (hE : EntriesDets.Claim)
    {U : Set (Fin 4 → ℂ)} (hU : IsOpen U) (M : QuotHom I I') :
    QuotHomFamilyHolomorphicOn (n := 4) U fun _ => M := by
  have hpoly := (hE.2.2.2.2.2.2.1 4 U (by norm_num) hU).2.2.2.2.2.1
  exact ⟨by norm_num, hU, fun e => hpoly.2.1 _⟩
theorem symbolHom_holomorphicOn_univ (hS : StripSymbols.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T)
    (hent : FourierSymbolIsEntire I I' T) :
    QuotHomFamilyHolomorphicOn (n := 4) univ (symbolHom I I' T) := by
  refine ⟨by norm_num, isOpen_univ, fun e => ?_⟩
  obtain ⟨c', c⟩ := e
  obtain ⟨x', rfl⟩ := Quot.exists_rep c'
  obtain ⟨x, rfl⟩ := Quot.exists_rep c
  have hfun : (fun (κ : Fin 4 → ℂ) (_ : Fin 1) =>
      quotHomEntries (symbolHom I I' T κ) (Quot.mk _ x', Quot.mk _ x)) =
      fun κ _ => fourierSymbol I I' T κ x' x := by
    funext κ _
    exact ((hS.2.1 I I' hI hI').2.1 T κ hT (hent.1 κ (mem_univ κ))).carrierEntry_symbolHom x' x
  rw [hfun]
  exact (hent.2 x' x).2
end Holomorphy
section Norms
variable {I I' I'' : PeriodicData}
theorem quotHomNorm_comp_le (hN : HomNorm.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (hI'' : IsPeriodic I'') {M : QuotHom I I'}
    {M' : QuotHom I'' I} {x y : ℝ} (hx : 0 ≤ x) (hM : quotHomNorm M ≤ ENNReal.ofReal x)
    (hM' : quotHomNorm M' ≤ ENNReal.ofReal y) :
    quotHomNorm (M.comp M') ≤ ENNReal.ofReal (x * y) := by
  have hsub := ((hN I I' hI hI').2.2.2.2.2.2.1 I'' hI'').2 M M'
  rw [ENNReal.ofReal_mul hx]
  exact hsub.trans (mul_le_mul' hM hM')
theorem quotHomNorm_combo_le (hN : HomNorm.Claim) (hI : IsPeriodic I)
    (M₁ M₂ M₃ : QuotHom I I) {p q d B : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d) (hB : 0 ≤ B)
    (h₁ : quotHomNorm M₁ ≤ ENNReal.ofReal B) (h₂ : quotHomNorm M₂ ≤ ENNReal.ofReal B)
    (h₃ : quotHomNorm M₃ ≤ ENNReal.ofReal B) :
    quotHomNorm ((p : ℂ) • M₁ + (q : ℂ) • M₂ + (d : ℂ) • M₃) ≤
      ENNReal.ofReal ((p + q + d) * B) := by
  have hs := (hN I I hI hI).2.2.2.2.2.1
  have hsm : ∀ (s : ℝ) (M : QuotHom I I), 0 ≤ s → quotHomNorm M ≤ ENNReal.ofReal B →
      quotHomNorm ((s : ℂ) • M) ≤ ENNReal.ofReal (s * B) := by
    intro s M hs0 hMB
    rw [hs.2.2.2.2 (s : ℂ) M, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0, mul_comm s B,
      ENNReal.ofReal_mul hB]
    exact mul_le_mul' hMB le_rfl
  have hsplit : ENNReal.ofReal ((p + q + d) * B) =
      ENNReal.ofReal (p * B) + ENNReal.ofReal (q * B) + ENNReal.ofReal (d * B) := by
    rw [← ENNReal.ofReal_add (mul_nonneg hp hB) (mul_nonneg hq hB),
      ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hp hB) (mul_nonneg hq hB)) (mul_nonneg hd hB)]
    congr 1
    ring
  rw [hsplit]
  exact (hs.2.2.2.1 _ _).trans (add_le_add ((hs.2.2.2.1 _ _).trans
    (add_le_add (hsm p M₁ hp h₁) (hsm q M₂ hq h₂))) (hsm d M₃ hd h₃))
end Norms
section Pair
variable {I J : PeriodicData} {N Ni K X : I.Carrier → I.Carrier → ℂ} {A : J.Carrier → I.Carrier → ℂ}
  {At : I.Carrier → J.Carrier → ℂ} {r a B c cC : ℝ}
abbrev conjCombo (I : PeriodicData) (N K X : I.Carrier → I.Carrier → ℂ) (p q d : ℝ) (κ : Fin 4 → ℂ) :
    QuotHom I I :=
  (symbolHom I I N κ).comp
    (((p : ℂ) • symbolHom I I X κ + (q : ℂ) • symbolHom I I K κ +
      scalarQuotHom I d).comp (symbolHom I I N κ))
theorem conjCombo_eq (p q d : ℝ) (κ : Fin 4 → ℂ) :
    conjCombo I N K X p q d κ =
      (p : ℂ) • (symbolHom I I N κ).comp ((symbolHom I I X κ).comp (symbolHom I I N κ)) +
        (q : ℂ) • (symbolHom I I N κ).comp ((symbolHom I I K κ).comp (symbolHom I I N κ)) +
        (d : ℂ) • (symbolHom I I N κ).comp (symbolHom I I N κ) := by
  refine LinearMap.ext fun f => ?_
  simp [scalarQuotHom]
theorem symbolHom_holomorphicOn_of_finiteRange (hS : StripSymbols.Claim)
    (hC : SymbolCalculus.Claim) {I I' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T ∧ IsFiniteRange I I' T) {U : Set (Fin 4 → ℂ)}
    (hU : IsOpen U) : QuotHomFamilyHolomorphicOn (n := 4) U (symbolHom I I' T) :=
  familyHolomorphicOn_mono hU (subset_univ U)
    (symbolHom_holomorphicOn_univ hS hI hI' hT.1 ((hC I I' hI hI').1 T hT.1 hT.2))
theorem conjCombo_invertible (hS : StripSymbols.Claim)
    (hV : InvertibilityNearReal.InvertibleNearRealAxis)
    (hE : EntriesDets.Claim)
    (hN : HomNorm.Claim) (hC : SymbolCalculus.Claim)
    (h : RootedPair I J N Ni K X A At r a B c cC) (hB : 0 ≤ B) (hc : 0 < c) {ε : ℝ}
    (hε : 0 < ε) (hε32 : ε ≤ 1 / 32) (hεB : 256 * B * ε ≤ c / 2) {p q d : ℝ} (hp : 0 ≤ p)
    (hq : 0 ≤ q) (hd : 0 ≤ d) (hpqd : p + q + d ≤ 2)
    (hreal : ∀ κ ∈ realDualPoints, LoewnerLE (scalarQuotHom I c) (conjCombo I N K X p q d κ)) :
    ∀ κ ∈ imStrip (2 * ε), IsInvertibleQuotHom (conjCombo I N K X p q d κ) ∧
      quotHomNorm (quotHomInverse (conjCombo I N K X p q d κ)) ≤ ENNReal.ofReal (2 / c) := by
  have hI := h.source_periodic
  have hU : IsOpen (openStripInterior (1 / 8)) := h.N_holomorphic.2.1
  have hX := symbolHom_holomorphicOn_of_finiteRange hS hC hI hI h.X_finiteRange hU
  have hK := symbolHom_holomorphicOn_of_finiteRange hS hC hI hI h.K_finiteRange hU
  have hhol : QuotHomFamilyHolomorphicOn (n := 4) (openStripInterior (1 / 8))
      (conjCombo I N K X p q d) :=
    familyHolomorphicOn_comp hE hI hI hI h.N_holomorphic
      (familyHolomorphicOn_comp hE hI hI hI
        (familyHolomorphicOn_add hE (familyHolomorphicOn_add hE (familyHolomorphicOn_smul hE _ hX)
          (familyHolomorphicOn_smul hE _ hK)) (familyHolomorphicOn_const hE hU _)) h.N_holomorphic)
  have hbound : ∀ κ ∈ openStripInterior (1 / 8),
      quotHomNorm (conjCombo I N K X p q d κ) ≤ ENNReal.ofReal (2 * B) := by
    intro κ hκ
    obtain ⟨b₁, b₂, b₃⟩ := h.sandwich_norm_le κ hκ
    rw [conjCombo_eq]
    refine (quotHomNorm_combo_le hN hI _ _ _ hp hq hd hB b₁ b₂ b₃).trans ?_
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpqd hB)
  refine hV I hI (1 / 8) (2 * B) c (2 * ε) _ (by norm_num) (by positivity) hc (by positivity)
    (by linarith) ?_ hhol hbound hreal
  have hrw : 8 * (2 * B) * (2 * ε) / (1 / 8) = 256 * B * ε := by ring
  rw [hrw]
  exact hεB
end Pair
theorem sandwichBounds_holds (hS : StripSymbols.Claim)
    (hO : RootConjugationOrder.ConjugatedOrderBounds)
    (hV : InvertibilityNearReal.InvertibleNearRealAxis)
    (hE : EntriesDets.Claim)
    (hN : HomNorm.Claim) (hC : SymbolCalculus.Claim)
    (hId : IdKernelFacts.Claim) : SandwichBounds := by
  intro r a B c cC hr ha hB hc hc1 hcC
  obtain ⟨η, hη, hη32, hηB⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 32 ∧ 256 * B * η ≤ c / 2 := by
    refine ⟨min (1 / 32) (c / (512 * (B + 1))), lt_min (by norm_num) (by positivity),
      min_le_left _ _, ?_⟩
    have hpos : 0 < min (1 / 32 : ℝ) (c / (512 * (B + 1))) :=
      lt_min (by norm_num) (by positivity)
    have hle := (le_div_iff₀ (by positivity : (0 : ℝ) < 512 * (B + 1))).1
      (min_le_right (1 / 32 : ℝ) (c / (512 * (B + 1))))
    nlinarith
  obtain ⟨M, hM, hMdef⟩ : ∃ M : ℝ, 0 ≤ M ∧ M = a * ((r * ((2 / c) * r)) * a) :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨δ, hδ, hδη, hδM⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ η / 2 ∧
      8 * M * (2 * δ) / (2 * η) ≤ cC / 2 / 2 := by
    refine ⟨min (η / 2) (η * cC / (32 * (M + 1))), lt_min (by positivity) (by positivity),
      min_le_left _ _, ?_⟩
    have hpos : 0 < min (η / 2) (η * cC / (32 * (M + 1))) :=
      lt_min (by positivity) (by positivity)
    have hle := (le_div_iff₀ (by positivity : (0 : ℝ) < 32 * (M + 1))).1
      (min_le_right (η / 2) (η * cC / (32 * (M + 1))))
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨δ, ⟨hδ, by linarith⟩, 1 + 2 / c + 2 / (cC / 2), ?_, ?_⟩
  · have h1 : 0 ≤ 2 / c := by positivity
    have h2 : 0 ≤ 2 / (cC / 2) := by positivity
    linarith
  intro I J N Ni K X A At h t ht τ hτ
  have hI := h.source_periodic
  have hJ := h.target_periodic
  have hle₁ : 2 / c ≤ 1 + 2 / c + 2 / (cC / 2) := by
    have h2 : 0 ≤ 2 / (cC / 2) := by positivity
    linarith
  have hle₂ : 2 / (cC / 2) ≤ 1 + 2 / c + 2 / (cC / 2) := by
    have h1 : 0 ≤ 2 / c := by positivity
    linarith
  have hw : 0 < 2 * η := by positivity
  have hint := hS.1 (2 * η) hw
  have hint₀ := hS.1 (1 / 8) (by norm_num)
  have hsub₀ : imStrip (2 * η) ⊆ openStripInterior (1 / 8) := by
    rw [hint₀.1]
    exact hint₀.2.2.2 _ hw (by linarith)
  have hopen : IsOpen (openStripInterior (2 * η)) := by
    rw [hint.1]
    exact hint.2.1
  have hinStrip : openStripInterior (2 * η) ⊆ imStrip (2 * η) := by
    rw [hint.1]
    exact hint.2.2.1
  have hnarrow : imStrip (2 * δ) ⊆ openStripInterior (2 * η) := by
    rw [hint.1]
    exact hint.2.2.2 _ (by positivity) (by linarith)
  have hnarrow' : imStrip (2 * δ) ⊆ imStrip (2 * η) := hnarrow.trans hinStrip
  have hreal : realDualPoints ⊆ openStripInterior (2 * η) := by
    rw [hint.1]
    intro κ hκ μ
    have : (κ μ).im = 0 := hκ μ
    rw [this, abs_zero]
    exact hw
  have hord := fun κ (hκ : κ ∈ realDualPoints) =>
    hO I J hI hJ (symbolHom I I N κ) (symbolHom I I K κ) (symbolHom I I X κ) (symbolHom I J A κ)
      (symbolHom J I At κ) c cC hc hc1 hcC (h.N_selfAdjoint κ hκ) (h.K_nonneg κ hκ)
      (h.X_lower_bound κ hκ) (h.X_upper_bound κ hκ) (h.N_sandwich_eq_one κ hκ) (h.At_adjoint κ hκ)
      (h.A_sandwich_lower κ hκ) t ht τ hτ
  have hmix := conjCombo_invertible hS hV hE hN hC h hB hc hη hη32 hηB (p := t) (q := 1 - t)
    (d := 1) ht.1 (by linarith [ht.2]) zero_le_one (by linarith) fun κ hκ => (hord κ hκ).1
  have hshift : ∀ κ, conjCombo I N K X 1 0 τ κ =
      (symbolHom I I N κ).comp ((symbolHom I I X κ + scalarQuotHom I τ).comp
        (symbolHom I I N κ)) := by
    intro κ
    simp only [conjCombo, Complex.ofReal_one, Complex.ofReal_zero, one_smul, zero_smul, add_zero]
  have hconj : ∀ κ ∈ imStrip (2 * η),
      IsInvertibleQuotHom ((symbolHom I I N κ).comp ((symbolHom I I X κ +
        scalarQuotHom I τ).comp (symbolHom I I N κ))) ∧
      quotHomNorm (quotHomInverse ((symbolHom I I N κ).comp ((symbolHom I I X κ +
        scalarQuotHom I τ).comp (symbolHom I I N κ)))) ≤ ENNReal.ofReal (2 / c) := by
    intro κ hκ
    have := conjCombo_invertible hS hV hE hN hC h hB hc hη hη32 hηB (p := 1) (q := 0)
      (d := τ) zero_le_one le_rfl hτ.1 (by linarith [hτ.2])
      (fun κ hκ => by rw [hshift]; exact (hord κ hκ).2.1) κ hκ
    rwa [hshift] at this
  have hY : ∀ κ ∈ imStrip (2 * η), IsInvertibleQuotHom (symbolHom I I X κ + scalarQuotHom I τ) ∧
      quotHomInverse (symbolHom I I X κ + scalarQuotHom I τ) =
        (symbolHom I I N κ).comp ((quotHomInverse ((symbolHom I I N κ).comp
          ((symbolHom I I X κ + scalarQuotHom I τ).comp (symbolHom I I N κ)))).comp
            (symbolHom I I N κ)) :=
    fun κ hκ => invertible_of_conj (h.inverse_pair κ (hsub₀ hκ)).1
      (h.inverse_pair κ (hsub₀ hκ)).2 (hconj κ hκ).1
  have hF := hS.2.1 I I hI hI
  have hXs : SymbolSummableOn I I X univ := hF.1.finiteRange X h.X_finiteRange.1 h.X_finiteRange.2
  have hIdP := (hId I hI).1
  have hIds := (hId I hI).2.2.1
  have hlin := fun κ => (hF.2.1 X κ h.X_finiteRange.1 (hXs κ (mem_univ κ))).linComb
    (idKernel I) hIdP (hIds κ (mem_univ κ)) 1 (τ : ℂ)
  have hidHom : ∀ κ, symbolHom I I (idKernel I) κ = LinearMap.id := by
    intro κ
    have h1 : symbolHom I I (idKernel I) κ =
        linearMapOfEntries (quotSymbol I I (idKernel I) κ) := rfl
    rw [h1, (hF.1.identity κ).2]
    exact (hN I I hI hI).2.2.2.2.2.2.2.1.1
  have hsym : ∀ κ, symbolHom I I (addScalar I X τ) κ =
      symbolHom I I X κ + scalarQuotHom I τ := by
    intro κ
    have h1 : symbolHom I I (addScalar I X τ) κ = _ := (hlin κ).2.2
    rw [h1, hidHom, one_smul]
    rfl
  have hTper : IsPeriodicKernel I I (addScalar I X τ) := (hlin 0).1
  have hYhol : QuotHomFamilyHolomorphicOn (n := 4) (openStripInterior (2 * η))
      fun κ => symbolHom I I X κ + scalarQuotHom I τ :=
    familyHolomorphicOn_add hE (symbolHom_holomorphicOn_of_finiteRange hS hC hI hI h.X_finiteRange hopen)
      (familyHolomorphicOn_const hE hopen _)
  have hThol : QuotHomFamilyHolomorphicOn (n := 4) (openStripInterior (2 * η))
      (symbolHom I I (addScalar I X τ)) := by
    rw [funext hsym]
    exact hYhol
  have hQ := hS.2.2.2 I hI (2 * η) hw (addScalar I X τ) hTper
    (fun κ _ => (hlin κ).2.1) hThol (fun κ hκ => by
      rw [hsym]
      exact (hY κ (hinStrip hκ)).1)
  have hYinv : QuotHomFamilyHolomorphicOn (n := 4) (openStripInterior (2 * η))
      fun κ => quotHomInverse (symbolHom I I X κ + scalarQuotHom I τ) :=
    ((hE.2.2.1 I hI).2.2.1 _ _ (fun κ hκ => (hY κ (hinStrip hκ)).1)).2 hopen hYhol
  have hGhol : QuotHomFamilyHolomorphicOn (n := 4) (openStripInterior (2 * η))
      fun κ => (symbolHom I J A κ).comp
        ((quotHomInverse (symbolHom I I X κ + scalarQuotHom I τ)).comp
          (symbolHom J I At κ)) :=
    familyHolomorphicOn_comp hE hI hJ hJ
      (symbolHom_holomorphicOn_of_finiteRange hS hC hI hJ h.A_finiteRange hopen)
      (familyHolomorphicOn_comp hE hI hI hJ hYinv
        (symbolHom_holomorphicOn_of_finiteRange hS hC hJ hI h.At_finiteRange hopen))
  have hGbound : ∀ κ ∈ openStripInterior (2 * η),
      quotHomNorm ((symbolHom I J A κ).comp
        ((quotHomInverse (symbolHom I I X κ + scalarQuotHom I τ)).comp
          (symbolHom J I At κ))) ≤ ENNReal.ofReal M := by
    intro κ hκ
    have hκ₀ := hsub₀ (hinStrip hκ)
    rw [(hY κ (hinStrip hκ)).2, hMdef]
    have hn := h.N_norm_le κ hκ₀
    have hav := h.A_norm_le κ hκ₀
    have hc₂ : (0 : ℝ) ≤ 2 / c := by positivity
    exact quotHomNorm_comp_le hN hI hJ hJ ha hav.1
      (quotHomNorm_comp_le hN hI hI hJ (by positivity)
        (quotHomNorm_comp_le hN hI hI hI hr hn
          (quotHomNorm_comp_le hN hI hI hI hc₂ (hconj κ (hinStrip hκ)).2 hn)) hav.2)
  have hGreal : ∀ κ ∈ realDualPoints, LoewnerLE (scalarQuotHom J (cC / 2))
      ((symbolHom I J A κ).comp
        ((quotHomInverse (symbolHom I I X κ + scalarQuotHom I τ)).comp
          (symbolHom J I At κ))) := by
    intro κ hκ
    rw [(hY κ (hinStrip (hreal hκ))).2]
    exact (hord κ hκ).2.2.2
  have hG := hV J hJ (2 * η) M (cC / 2) (2 * δ) _ hw hM (by positivity) (by positivity)
    (by linarith) hδM hGhol hGbound hGreal
  refine ⟨fun κ hκ => ⟨(hmix κ (hnarrow' hκ)).1,
      (hmix κ (hnarrow' hκ)).2.trans (ENNReal.ofReal_le_ofReal hle₁)⟩,
    fun κ hκ => ⟨(hconj κ (hnarrow' hκ)).1,
      (hconj κ (hnarrow' hκ)).2.trans (ENNReal.ofReal_le_ofReal hle₁)⟩,
    hQ.1, fun κ hκ => (hY κ (hnarrow' hκ)).1, hQ.2.1,
    fun κ hκ => hQ.2.2.2.2.2.2.1 κ (hnarrow hκ), fun κ hκ => ?_,
    fun κ hκ => ⟨(hG κ hκ).1, (hG κ hκ).2.trans (ENNReal.ofReal_le_ofReal hle₂)⟩⟩
  rw [hQ.2.2.2.2.2.2.2 κ (hnarrow hκ), hsym]
end YangMills.Construction.PeriodicOperators.RootedSandwiches
end
