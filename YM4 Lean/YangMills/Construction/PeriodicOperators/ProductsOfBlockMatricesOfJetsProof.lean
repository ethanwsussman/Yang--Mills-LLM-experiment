import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHomProof
import YangMills.Construction.PeriodicOperators.ProductsOfBlockMatricesOfJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.BlockJetProducts
open BlockJets
section Entries
variable {A B C : Type}
private theorem ext_of_linearMapEntry [Finite A] {M N : (A → ℂ) →ₗ[ℂ] (B → ℂ)}
    (h : linearMapEntry M = linearMapEntry N) : M = N := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMap_ext_of_entry <;> assumption
private theorem linearMapEntry_linearMapOfEntries [Fintype A] (K : B → A → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.linearMapEntry_linearMapOfEntries <;> assumption
private theorem linearMapEntry_add (M N : (A → ℂ) →ₗ[ℂ] (B → ℂ)) (c' : B) (c : A) :
    linearMapEntry (M + N) c' c = linearMapEntry M c' c + linearMapEntry N c' c := rfl
private theorem linearMapEntry_comp [Fintype B] (M : (B → ℂ) →ₗ[ℂ] (C → ℂ))
    (N : (A → ℂ) →ₗ[ℂ] (B → ℂ)) (c' : C) (c : A) :
    linearMapEntry (M.comp N) c' c = ∑ d, linearMapEntry M c' d * linearMapEntry N d c := by
  classical
  have hdecomp : ∀ f : B → ℂ, f = ∑ d, f d • (Pi.single d 1 : B → ℂ) := fun f => by
    funext b
    simp [Finset.sum_apply, Pi.single_apply]
  change M (N (Pi.single c 1)) c' = _
  conv_lhs => rw [hdecomp (N (Pi.single c 1))]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_comm]
  rfl
end Entries
section Blocks
variable {J : Fin 2 → PeriodicData}
private theorem sigmaQuotPlace_sigmaQuotIn (b : Fin 2) (c : (J b).UnitQuot) :
    sigmaQuotPlace J (sigmaQuotIn J b c) = ⟨b, c⟩ := by
  induction c using Quot.ind with
  | mk i => rfl
private theorem sigmaQuotIn_sigmaQuotPlace (c : (PeriodicData.sigma J).UnitQuot) :
    sigmaQuotIn J (sigmaQuotPlace J c).1 (sigmaQuotPlace J c).2 = c := by
  induction c using Quot.ind with
  | mk i => rfl
private def sigmaQuotEquiv : (Σ b, (J b).UnitQuot) ≃ (PeriodicData.sigma J).UnitQuot where
  toFun := fun x => sigmaQuotIn J x.1 x.2
  invFun := sigmaQuotPlace J
  left_inv := fun x => sigmaQuotPlace_sigmaQuotIn x.1 x.2
  right_inv := sigmaQuotIn_sigmaQuotPlace
private theorem sum_sigmaQuot [∀ b, Fintype (J b).UnitQuot]
    [Fintype (PeriodicData.sigma J).UnitQuot] (f : (PeriodicData.sigma J).UnitQuot → ℂ) :
    ∑ c, f c = ∑ l, ∑ d : (J l).UnitQuot, f (sigmaQuotIn J l d) := by
  rw [← Equiv.sum_comp (sigmaQuotEquiv (J := J)) f, Fintype.sum_sigma]
  rfl
private theorem linearMapEntry_blockQuotHom [Fintype (PeriodicData.sigma J).UnitQuot]
    (M : ∀ i j, QuotHom (J j) (J i)) (i j : Fin 2) (a : (J i).UnitQuot) (b : (J j).UnitQuot) :
    linearMapEntry (blockQuotHom J M) (sigmaQuotIn J i a) (sigmaQuotIn J j b) =
      linearMapEntry (M i j) a b := by
  rw [blockQuotHom, linearMapEntry_linearMapOfEntries, sigmaQuotPlace_sigmaQuotIn,
    sigmaQuotPlace_sigmaQuotIn]
  rfl
private theorem blockQuotHom_ext [Finite (PeriodicData.sigma J).UnitQuot]
    {A B : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)}
    (h : ∀ (i j : Fin 2) (a : (J i).UnitQuot) (b : (J j).UnitQuot),
      linearMapEntry A (sigmaQuotIn J i a) (sigmaQuotIn J j b) =
        linearMapEntry B (sigmaQuotIn J i a) (sigmaQuotIn J j b)) : A = B := by
  refine ext_of_linearMapEntry ?_
  funext c' c
  rw [← sigmaQuotIn_sigmaQuotPlace c', ← sigmaQuotIn_sigmaQuotPlace c]
  exact h _ _ _ _
private theorem blockQuotHom_add [Finite (PeriodicData.sigma J).UnitQuot]
    (M N : ∀ i j, QuotHom (J j) (J i)) :
    blockQuotHom J (fun i j => M i j + N i j) = blockQuotHom J M + blockQuotHom J N := by
  have := Fintype.ofFinite (PeriodicData.sigma J).UnitQuot
  refine blockQuotHom_ext fun i j a b => ?_
  rw [linearMapEntry_add, linearMapEntry_blockQuotHom, linearMapEntry_blockQuotHom,
    linearMapEntry_blockQuotHom, linearMapEntry_add]
private theorem blockQuotHom_comp (hJ : ∀ b, Finite (J b).UnitQuot)
    [Finite (PeriodicData.sigma J).UnitQuot] (M N : ∀ i j, QuotHom (J j) (J i)) :
    (blockQuotHom J M).comp (blockQuotHom J N) =
      blockQuotHom J fun i j => (M i 0).comp (N 0 j) + (M i 1).comp (N 1 j) := by
  have : ∀ b, Fintype (J b).UnitQuot := fun b =>
    have := hJ b
    Fintype.ofFinite _
  have := Fintype.ofFinite (PeriodicData.sigma J).UnitQuot
  refine blockQuotHom_ext fun i j a b => ?_
  rw [linearMapEntry_blockQuotHom, linearMapEntry_add, linearMapEntry_comp, linearMapEntry_comp,
    linearMapEntry_comp, sum_sigmaQuot, Fin.sum_univ_two]
  simp only [linearMapEntry_blockQuotHom]
end Blocks
private theorem mulBlockJet_holds (δ : ℝ) (p : Fin 4 → ℂ) (J : Fin 2 → PeriodicData)
    (hJ : ∀ b, IsPeriodic (J b)) : MulBlockJet δ p J := by
  intro T S _ _
  have hfin : ∀ b, Finite (J b).UnitQuot := fun b => (hJ b).finite_quot
  have : Finite (PeriodicData.sigma J).UnitQuot := (IsPeriodic.sigma hJ).finite_quot
  refine ⟨fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_⟩
  · simp only [JetQuad.mul, JetQuad.add, blockJet, blockQuotHom_comp hfin, Pi.add_apply]
  · simp only [JetQuad.mul, JetQuad.add, blockJet, blockQuotHom_comp hfin, Pi.add_apply,
      ← blockQuotHom_add]
    congr 1
    funext i j
    abel
  · simp only [JetQuad.mul, JetQuad.add, blockJet, blockQuotHom_comp hfin, Pi.add_apply,
      ← blockQuotHom_add]
    congr 1
    funext i j
    abel
  · simp only [JetQuad.mul, JetQuad.add, blockJet, blockQuotHom_comp hfin, Pi.add_apply,
      ← blockQuotHom_add]
    congr 1
    funext i j
    abel
theorem claim_holds : Claim :=
  fun δ p _ _ J hJ => mulBlockJet_holds δ p J hJ
end YangMills.Construction.PeriodicOperators.BlockJetProducts
end
