import YangMills.Construction.Towers.SandwichesOfTheFreeOperatorsInCoefficientsProof
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.SymbolsOfPeriodicOperators
import YangMills.Construction.Towers.TheFreeOperatorsArePeriodicOperators
import YangMills.Construction.Towers.TheRootsOfTheFreePropagatorsOnTheStrip
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ResolventRootsOnStrip
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.StripSymbols (openStripInterior)
open YangMills.Construction.Tower.FreeResolvents
theorem isHolomorphicIn_congr {O : Set (Fin 4 → ℂ)} {f g : (Fin 4 → ℂ) → ℂ}
    (hf : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun x _ => f x)
    (hfg : ∀ x ∈ O, g x = f x) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun x _ => g x := by
  refine ⟨hf.1, hf.2.1.congr fun x hx => funext fun _ => hfg x hx, fun a ha j => ?_⟩
  have hc : Continuous fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j := by
    fun_prop
  have hpre : (fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) ⁻¹' O ∈
      nhds (0 : ℂ) :=
    (hf.1.preimage hc).mem_nhds (by simpa using ha)
  filter_upwards [hf.2.2 a ha j, eventually_eventually_nhds.2 hpre] with ζ hd he
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [he] with ζ' hζ'
  exact funext fun _ => hfg _ hζ'
theorem linearMapOfEntries_quotOne {I : PeriodicData} [Finite I.UnitQuot] :
    linearMapOfEntries (quotOne I) = LinearMap.id := by
  refine LinearMap.ext fun f => ?_
  rw [linearMapOfEntries_eq_applyKernel]
  funext c'
  simp only [applyKernel, quotOne, LinearMap.id_apply]
  rw [tsum_eq_single c' fun b hb => by simp [Ne.symm hb]]
  simp
theorem isSelfAdjointQuotHom_of_transpose_eq (hSym : PeriodicOperators.Symbols.Claim)
    {I : PeriodicData} (hI : IsPeriodic I) {T : I.Carrier → I.Carrier → ℂ}
    (hT : IsPeriodicKernel I I T) (hreal : ∀ ι' ι, (T ι' ι).im = 0)
    (htr : kernelTranspose I I T = T) {κ : Fin 4 → ℂ} (hκ : κ ∈ realDualPoints) :
    IsSelfAdjointQuotHom (symbolHom I I T κ) := by apply _root_.YangMills.Construction.Tower.FreeSandwiches.symbolHom_selfAdjoint_of_transpose_eq <;> assumption
theorem sqrtFacts_of_powerMatrixFacts (hS : StripSymbols.Claim)
    (hSym : PeriodicOperators.Symbols.Claim) {I : PeriodicData} (hI : IsPeriodic I)
    {Mult : ℝ → (Fin 4 → ℂ) → QuotHom I I → Prop} {M : ℝ → (Fin 4 → ℂ) → QuotHom I I}
    {P K : I.Carrier → I.Carrier → ℂ} (hF : PowerMatrixFacts I Mult M P)
    (hP : P = fun ι' ι => K ι' ι + idKernel I ι' ι) (hK : IsPeriodicKernel I I K)
    (hKf : SymbolSummableOn I I K Set.univ) :
    SqrtFacts I M (matFunKernel I I (M (-(1 / 2))))
      (matFunKernel I I (M (1 / 2))) (periodicInverse I P) K := by
  have : Finite I.UnitQuot := hI.finite_quot
  obtain ⟨hi1, -, hi3, hi4⟩ := hS.1 (1 / 8) (by norm_num)
  obtain ⟨hform, hcalc, hker, -⟩ := hS.2.1 I I hI hI
  have hsub : openStripInterior (1 / 8) ⊆ imStrip (1 / 8) := by
    rw [hi1]
    exact hi3
  have KT := fun σ (hσ : σ ∈ resolventExponents) =>
    hker (1 / 8) (by norm_num) (M σ) (hF.holomorphicOn σ hσ)
      (fun υ' h0 h1 e =>
        let ⟨B, hB⟩ := hF.boundedOn σ hσ e
        ⟨B, fun κ hκ => hB κ (by rw [hi1]; exact hi4 υ' h0 h1 hκ)⟩)
      (fun e κ hκ => hF.quasiPeriodic σ hσ e κ (hsub hκ))
  have mem0 : (-1 : ℝ) ∈ resolventExponents := by simp [resolventExponents]
  have mem1 : (-(1 / 2) : ℝ) ∈ resolventExponents := by simp [resolventExponents]
  have mem2 : (1 / 2 : ℝ) ∈ resolventExponents := by simp [resolventExponents]
  obtain ⟨-, -, -, pG, fG, sG⟩ := KT _ mem0
  obtain ⟨-, -, -, pN, fN, sN⟩ := KT _ mem1
  obtain ⟨-, -, -, pNi, fNi, sNi⟩ := KT _ mem2
  have symId : ∀ κ, symbolHom I I (idKernel I) κ = LinearMap.id := fun κ => by
    have e : symbolHom I I (idKernel I) κ =
        linearMapOfEntries (quotSymbol I I (idKernel I) κ) := rfl
    rw [e, (hform.identity κ).2, linearMapOfEntries_quotOne]
  have left : ∀ κ ∈ openStripInterior (1 / 8),
      (symbolHom I I (matFunKernel I I (M (1 / 2))) κ).comp
        (symbolHom I I (matFunKernel I I (M (-(1 / 2)))) κ) = LinearMap.id := by
    intro κ hκ
    have h := ((hcalc _ κ pNi (fNi κ hκ)).comp I hI _ pN (fN κ hκ)).2.2.2
    rw [hF.sqrt_comp_invSqrt.2, symId] at h
    exact h.symm
  have right : ∀ κ ∈ openStripInterior (1 / 8),
      (symbolHom I I (matFunKernel I I (M (-(1 / 2)))) κ).comp
        (symbolHom I I (matFunKernel I I (M (1 / 2))) κ) = LinearMap.id := by
    intro κ hκ
    exact (mul_eq_one_comm
      (a := (symbolHom I I (matFunKernel I I (M (1 / 2))) κ : Module.End ℂ (I.UnitQuot → ℂ)))
      (b := symbolHom I I (matFunKernel I I (M (-(1 / 2)))) κ)).1 (left κ hκ)
  have square : ∀ κ ∈ openStripInterior (1 / 8),
      symbolHom I I (matFunKernel I I (M (-1))) κ =
        (symbolHom I I (matFunKernel I I (M (-(1 / 2)))) κ).comp
          (symbolHom I I (matFunKernel I I (M (-(1 / 2)))) κ) := by
    intro κ hκ
    rw [← hF.invSqrt_comp_invSqrt.2]
    exact ((hcalc _ κ pN (fN κ hκ)).comp I hI _ pN (fN κ hκ)).2.2.2
  have hPper : IsPeriodicKernel I I P := hF.symbol_invertible.1
  have zero_mem : (0 : Fin 4 → ℂ) ∈ openStripInterior (1 / 8) := by
    rw [hi1]
    intro μ
    simp
  have idPer : IsPeriodicKernel I I (idKernel I) := by
    have h := ((hcalc _ 0 pNi (fNi 0 zero_mem)).comp I hI _ pN (fN 0 zero_mem)).2.1
    rwa [hF.sqrt_comp_invSqrt.2] at h
  have hcomb : StripSymbols.linCombKernel 1 1 K (idKernel I) = P := by
    rw [hP]
    funext ι' ι
    simp [StripSymbols.linCombKernel]
  have comb := fun κ => (hcalc K κ hK (hKf κ trivial)).linComb (idKernel I) idPer
    (hform.identity κ).1 1 1
  simp only [hcomb] at comb
  have symP : ∀ κ, symbolHom I I P κ = symbolHom I I K κ + scalarQuotHom I 1 := fun κ => by
    rw [(comb κ).2.2, symId]
    simp [scalarQuotHom]
  have sandwich : ∀ κ ∈ openStripInterior (1 / 8),
      (symbolHom I I (matFunKernel I I (M (-(1 / 2)))) κ).comp
        ((symbolHom I I K κ + scalarQuotHom I 1).comp
          (symbolHom I I (matFunKernel I I (M (-(1 / 2)))) κ)) = LinearMap.id := by
    intro κ hκ
    have h := ((hcalc P κ hPper (comb κ).2.1).comp I hI _ pG (fG κ hκ)).2.2.2
    rw [hF.comp_inv.2, symId, square κ hκ, symP] at h
    generalize symbolHom I I K κ + scalarQuotHom I 1 = A at h ⊢
    have r := right κ hκ
    generalize symbolHom I I (matFunKernel I I (M (-(1 / 2)))) κ = n at h r ⊢
    generalize symbolHom I I (matFunKernel I I (M (1 / 2))) κ = m at r
    have h1 : A.comp n = m := by
      calc A.comp n = A.comp (n.comp (n.comp m)) := by rw [r]; rfl
        _ = (A.comp (n.comp n)).comp m := by simp only [LinearMap.comp_assoc]
        _ = m := by rw [← h]; rfl
    rw [h1, r]
  have holo : ∀ σ ∈ resolventExponents, (∀ κ ∈ openStripInterior (1 / 8),
      symbolHom I I (matFunKernel I I (M σ)) κ = M σ κ) →
      QuotHomFamilyHolomorphicOn (n := 4) (openStripInterior (1 / 8))
        (symbolHom I I (matFunKernel I I (M σ))) := by
    intro σ hσ hs
    obtain ⟨a, b, c⟩ := hF.holomorphicOn σ hσ
    exact ⟨a, b, fun e => isHolomorphicIn_congr (c e) fun κ hκ => by
      simp only [quotHomEntries]
      rw [hs κ hκ]⟩
  exact
    { sqrt_periodic := pN
      invSqrt_periodic := pNi
      sqrt_summable := fN
      invSqrt_summable := fNi
      sqrt_symbol := sN
      invSqrt_symbol := sNi
      sqrt_holomorphicOn := holo _ mem1 sN
      invSqrt_holomorphicOn := holo _ mem2 sNi
      invSqrt_inverse := fun κ hκ => ⟨left κ hκ, right κ hκ⟩
      resolvent_eq_sq := fun κ hκ => by
        rw [hF.inverse_eq]
        exact ⟨fG κ hκ, square κ hκ⟩
      sqrt_conj_add_one := sandwich
      sqrt_selfAdjoint := fun κ hκ =>
        isSelfAdjointQuotHom_of_transpose_eq hSym hI pN (hF.im_eq_zero _ mem1)
          (hF.transpose_eq _ mem1) hκ }
theorem resolventRootsHold_of_facts (hG : FreeResolvents.FreeResolventRoots)
    (hS : StripSymbols.Claim) (hSym : PeriodicOperators.Symbols.Claim)
    (hIx : PeriodicOperators.TowerIndexSets.Claim)
    (hFO : Tower.FreeOperators.FreeOperatorsArePeriodic) : ResolventRootsHold := by
  intro L hL k hk
  obtain ⟨-, -, -, fB, fS, -, -⟩ := hG L hL k hk
  obtain ⟨hIs, hIb, -⟩ := hIx L hL k 0 (Nat.zero_le k)
  have hOp := (hFO.2 L hL k hk).2
  exact ⟨sqrtFacts_of_powerMatrixFacts hS hSym hIb fB rfl hOp.K.1
      ((hS.2.1 _ _ hIb hIb).1.finiteRange _ hOp.K.1 hOp.K.2.1),
    sqrtFacts_of_powerMatrixFacts hS hSym hIs fS rfl hOp.Delta.1
      ((hS.2.1 _ _ hIs hIs).1.finiteRange _ hOp.Delta.1 hOp.Delta.2.1)⟩
end YangMills.Construction.Tower.ResolventRootsOnStrip
end
