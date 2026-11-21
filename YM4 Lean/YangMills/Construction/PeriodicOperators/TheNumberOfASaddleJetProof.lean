import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJets
import YangMills.Construction.PeriodicOperators.BlockMatricesOfJetsAreJets
import YangMills.Construction.PeriodicOperators.CalculusOfJets
import YangMills.Construction.PeriodicOperators.CopiesAndUnionsOfPeriodicIndexSets
import YangMills.Construction.PeriodicOperators.JetsOfPeriodicOperatorsAndConstantParts
import YangMills.Construction.PeriodicOperators.NormsOfJetsAndAffineFamiliesOfInvertibleJets
import YangMills.Construction.PeriodicOperators.ProductsOfBlockMatricesOfJets
import YangMills.Construction.PeriodicOperators.ProductsOfJets
import YangMills.Construction.PeriodicOperators.SumsAndMultiplesOfJets
import YangMills.Construction.PeriodicOperators.TheNumberOfASaddleJet
import YangMills.Construction.PeriodicOperators.TransposesOfJets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.SaddleJetNumber
open BlockJets
open JetQuad
section Identities
variable {A B C : PeriodicData}
private theorem jetQuad_mul_one (p : Fin 4 → ℂ) (T : JetQuad A B) : mul p T (one A) = T := by
  apply JetQuad.ext <;> funext κ <;> simp [JetQuad.mul, JetQuad.one]
private theorem jetQuad_one_mul (p : Fin 4 → ℂ) (T : JetQuad A B) : mul p (one B) T = T := by
  apply JetQuad.ext <;> funext κ <;> simp [JetQuad.mul, JetQuad.one]
private theorem jetQuad_mul_zero (p : Fin 4 → ℂ) (T : JetQuad A B) :
    mul p T (zeroJet C A) = zeroJet C B := by
  apply JetQuad.ext <;> funext κ <;> simp [JetQuad.mul, JetQuad.zeroJet]
private theorem jetQuad_zero_mul (p : Fin 4 → ℂ) (T : JetQuad C A) :
    mul p (zeroJet A B) T = zeroJet C B := by
  apply JetQuad.ext <;> funext κ <;> simp [JetQuad.mul, JetQuad.zeroJet]
private theorem jetQuad_add_zero (T : JetQuad A B) : add T (zeroJet A B) = T := by
  apply JetQuad.ext <;> funext κ <;> simp [JetQuad.add, JetQuad.zeroJet]
private theorem jetQuad_zero_add (T : JetQuad A B) : add (zeroJet A B) T = T := by
  apply JetQuad.ext <;> funext κ <;> simp [JetQuad.add, JetQuad.zeroJet]
private theorem jetQuad_smul_zero (a : ℂ) : smul a (zeroJet A B) = zeroJet A B := by
  apply JetQuad.ext <;> funext κ <;> simp [JetQuad.smul, JetQuad.zeroJet]
private theorem jetQuad_smul_mul (p : Fin 4 → ℂ) (a : ℂ) (T : JetQuad A B) (S : JetQuad C A) :
    mul p (smul a T) S = smul a (mul p T S) := by
  apply JetQuad.ext <;> funext κ <;>
    simp [JetQuad.mul, JetQuad.smul, LinearMap.smul_comp, smul_add]
private theorem jetQuad_mul_smul (p : Fin 4 → ℂ) (a : ℂ) (T : JetQuad A B) (S : JetQuad C A) :
    mul p T (smul a S) = smul a (mul p T S) := by
  apply JetQuad.ext <;> funext κ <;>
    simp [JetQuad.mul, JetQuad.smul, LinearMap.comp_smul, smul_add]
private theorem jetQuad_smul_smul (a b : ℂ) (T : JetQuad A B) :
    smul a (smul b T) = smul (a * b) T := by
  apply JetQuad.ext <;> funext κ <;> simp [JetQuad.smul, smul_smul]
private theorem jetQuad_one_smul (T : JetQuad A B) : smul 1 T = T := by
  apply JetQuad.ext <;> funext κ <;> simp [JetQuad.smul]
private theorem quotHom_add_neg_one_smul (M : QuotHom A B) : M + (-1 : ℂ) • M = 0 := by
  apply LinearMap.ext
  intro f
  funext c
  simp [LinearMap.add_apply, LinearMap.smul_apply]
abbrev _root_.YangMills.SharedProofs.p42708 := @quotHom_add_neg_one_smul
private theorem jetQuad_add_neg (T : JetQuad A B) : add T (smul (-1) T) = zeroJet A B := by
  apply JetQuad.ext <;> funext κ <;> exact quotHom_add_neg_one_smul _
private theorem jetQuad_neg_add (T : JetQuad A B) : add (smul (-1) T) T = zeroJet A B := by
  apply JetQuad.ext <;> funext κ <;> exact (add_comm _ _).trans (quotHom_add_neg_one_smul _)
private theorem jetQuad_add_self (T : JetQuad A B) : add T T = smul 2 T := by
  apply JetQuad.ext <;> funext κ <;> simp [JetQuad.add, JetQuad.smul, two_smul]
end Identities
section EqualJets
variable {δ : ℝ} {p : Fin 4 → ℂ} {A B : PeriodicData}
private theorem eqAsJet_refl (T : JetQuad A B) : EqAsJet δ p T T :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
private theorem eqAsJet_symm {T S : JetQuad A B} (h : EqAsJet δ p T S) : EqAsJet δ p S T :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩
private theorem eqAsJet_trans {T S R : JetQuad A B} (h : EqAsJet δ p T S)
    (h' : EqAsJet δ p S R) : EqAsJet δ p T R :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1, h.2.2.2.trans h'.2.2.2⟩
end EqualJets
private structure JetToolkit (δ : ℝ) (p : Fin 4 → ℂ) : Prop where
  mulJet : ∀ {A B C : PeriodicData}, IsPeriodic A → IsPeriodic B →
    IsPeriodic C → ∀ {T : JetQuad A B} {S : JetQuad C A},
      IsJet δ p T → IsJet δ p S → IsJet δ p (mul p T S)
  addJet : ∀ {A B : PeriodicData}, IsPeriodic A → IsPeriodic B →
    ∀ {T S : JetQuad A B}, IsJet δ p T → IsJet δ p S → IsJet δ p (add T S)
  smulJet : ∀ {A B : PeriodicData}, IsPeriodic A → IsPeriodic B → ∀ (a : ℂ)
    {T : JetQuad A B}, IsJet δ p T → IsJet δ p (smul a T)
  oneJet : ∀ {A : PeriodicData}, IsPeriodic A → IsJet δ p (one A)
  assoc : ∀ {A B C D : PeriodicData}, IsPeriodic A → IsPeriodic B →
    IsPeriodic C → IsPeriodic D →
    ∀ {T : JetQuad B A} {S : JetQuad C B} {R : JetQuad D C},
      IsJet δ p T → IsJet δ p S → IsJet δ p R →
        EqAsJet δ p (mul p (mul p T S) R) (mul p T (mul p S R))
  inverseFacts : ∀ {A : PeriodicData}, IsPeriodic A → ∀ {T : JetQuad A A},
    IsInvertibleJet δ p T → IsJet δ p (invJet p T) ∧ EqAsJet δ p (mul p (invJet p T) T) (one A) ∧
      EqAsJet δ p (mul p T (invJet p T)) (one A)
  numberAdd : ∀ {A : PeriodicData}, IsPeriodic A → ∀ {T S : JetQuad A A},
    IsInvertibleJet δ p T → IsInvertibleJet δ p S → IsInvertibleJet δ p (mul p T S) ∧
      logNumber p (mul p T S) = logNumber p T + logNumber p S
  finiteNorm : ∀ {A B : PeriodicData}, IsPeriodic A → IsPeriodic B →
    ∀ {T : JetQuad A B}, IsJet δ p T → jetNorm δ p T < ∞
  eqMul : ∀ {A B C : PeriodicData}, IsPeriodic A → IsPeriodic B →
    IsPeriodic C → ∀ {T T' : JetQuad A B} {S S' : JetQuad C A},
      IsJet δ p T → IsJet δ p T' → IsJet δ p S → IsJet δ p S' → EqAsJet δ p T T' →
        EqAsJet δ p S S' → EqAsJet δ p (mul p T S) (mul p T' S')
  eqAdd : ∀ {A B : PeriodicData}, IsPeriodic A → IsPeriodic B →
    ∀ {T T' S S' : JetQuad A B}, IsJet δ p T → IsJet δ p T' → IsJet δ p S → IsJet δ p S' →
      EqAsJet δ p T T' → EqAsJet δ p S S' → EqAsJet δ p (add T S) (add T' S')
  eqNumber : ∀ {A : PeriodicData}, IsPeriodic A → ∀ {T T' : JetQuad A A},
    IsJet δ p T → IsJet δ p T' → EqAsJet δ p T T' → IsInvertibleJet δ p T →
      IsInvertibleJet δ p T' ∧ logNumber p T = logNumber p T'
private theorem jetToolkit (hC : JetCalculus.Claim)
    (hEq : JetArgumentsAndEqualJets)
    (hSum : JetAddSMul.Claim) (hPr : JetProducts.Claim)
    (hOne : ZeroPartJets.Claim)
    (hNorm : JetNormsAffine.Claim)
    (δ : ℝ) (p : Fin 4 → ℂ) (hδ : 0 < δ) (hp : p ∈ imStrip δ) : JetToolkit δ p := by
  obtain ⟨hProd, -, -, -, hInv, -, hLog, -, -⟩ := hC δ p hδ hp
  exact
    { mulJet := fun hA hB hC' _ _ hT hS => (hPr _ _ _ hA hB hC' δ p hδ hp).2 _ _ hT hS
      addJet := fun hA hB _ _ hT hS => (hSum _ _ hA hB δ p hδ hp).2.1 _ _ hT hS
      smulJet := fun hA hB a _ hT => (hSum _ _ hA hB δ p hδ hp).2.2.2 a _ hT
      oneJet := fun hA => (hOne _ _ hA hA δ p hδ hp).2.1
      assoc := fun hA hB hC' hD _ _ _ hT hS hR => (hProd _ _ _ _ hA hB hC' hD _ _ _ hT hS hR).1
      inverseFacts := fun hA _ hT =>
        ⟨(hInv _ hA _ hT).1, (hInv _ hA _ hT).2.1, (hInv _ hA _ hT).2.2.1⟩
      numberAdd := fun hA _ _ hT hS => (hLog _ hA).1 _ _ hT hS
      finiteNorm := fun hA hB _ hT => (hNorm δ p hδ hp _ _ hA hB).1 _ hT
      eqMul := fun hA hB hC' _ _ _ _ hT hT' hS hS' h h' =>
        (hEq.2.1 δ p _ _ hA hB _ _ hT hT' h).2.2.2.2 _ hC' _ _ hS hS' h'
      eqAdd := fun hA hB _ _ _ _ hT hT' hS hS' h h' =>
        (hEq.2.1 δ p _ _ hA hB _ _ hT hT' h).2.2.2.1 _ _ hS hS' h'
      eqNumber := fun hA _ _ hT hT' h hi =>
        ⟨((hEq.2.2 δ p _ hA _ _ hT hT' h).2 hi).1, ((hEq.2.2 δ p _ hA _ _ hT hT' h).2 hi).2.2.2⟩ }
section Invertible
variable {δ : ℝ} {p : Fin 4 → ℂ}
private theorem isInvertibleJet_of_twoSided (t : JetToolkit δ p) {A : PeriodicData}
    (hA : IsPeriodic A) {T S : JetQuad A A} (hT : IsJet δ p T) (hS : IsJet δ p S)
    (h₁ : EqAsJet δ p (mul p T S) (one A)) (h₂ : EqAsJet δ p (mul p S T) (one A)) :
    IsInvertibleJet δ p T := by
  have unit : ∀ κ ∈ imStrip (2 * δ), ∃ u : (Module.End ℂ (A.UnitQuot → ℂ))ˣ,
      (u : Module.End ℂ (A.UnitQuot → ℂ)) = T.f00 κ ∧
        ((u⁻¹ : (Module.End ℂ (A.UnitQuot → ℂ))ˣ) : Module.End ℂ (A.UnitQuot → ℂ)) = S.f00 κ :=
    fun κ hκ => ⟨⟨T.f00 κ, S.f00 κ, h₁.1 hκ, h₂.1 hκ⟩, rfl, rfl⟩
  refine ⟨hT, fun κ hκ => ?_, ?_⟩
  · obtain ⟨u, hu, -⟩ := unit κ hκ
    exact ⟨u, hu⟩
  · refine lt_of_le_of_lt (iSup₂_le fun κ hκ => ?_) (t.finiteNorm hA hA hS)
    obtain ⟨u, hu, hv⟩ := unit κ hκ
    have hinv : quotHomInverse (T.f00 κ) = S.f00 κ := by
      show Ring.inverse (T.f00 κ : Module.End ℂ (A.UnitQuot → ℂ)) = _
      rw [← hu, Ring.inverse_unit]
      exact hv
    rw [hinv]
    exact le_trans (le_iSup₂_of_le (f := fun κ _ => quotHomNorm (S.f00 κ)) κ hκ le_rfl)
      (le_trans (le_trans le_self_add le_self_add) le_self_add)
private theorem isInvertibleJet_one (t : JetToolkit δ p) {A : PeriodicData} (hA : IsPeriodic A) :
    IsInvertibleJet δ p (one A) := by
  have h : EqAsJet δ p (mul p (one A) (one A)) (one A) := by
    rw [jetQuad_mul_one]
    exact eqAsJet_refl _
  exact isInvertibleJet_of_twoSided t hA (t.oneJet hA) (t.oneJet hA) h h
private theorem logNumber_one (t : JetToolkit δ p) {A : PeriodicData} (hA : IsPeriodic A) :
    logNumber p (one A) = 0 := by
  have h := (t.numberAdd hA (isInvertibleJet_one t hA) (isInvertibleJet_one t hA)).2
  rw [jetQuad_mul_one] at h
  linear_combination -h
private theorem isInvertibleJet_smul_one (t : JetToolkit δ p) {A : PeriodicData}
    (hA : IsPeriodic A) {a : ℂ} (ha : a ≠ 0) : IsInvertibleJet δ p (smul a (one A)) := by
  have h₁ : EqAsJet δ p (mul p (smul a (one A)) (smul a⁻¹ (one A))) (one A) := by
    rw [jetQuad_smul_mul, jetQuad_mul_smul, jetQuad_mul_one, jetQuad_smul_smul,
      mul_inv_cancel₀ ha, jetQuad_one_smul]
    exact eqAsJet_refl _
  have h₂ : EqAsJet δ p (mul p (smul a⁻¹ (one A)) (smul a (one A))) (one A) := by
    rw [jetQuad_smul_mul, jetQuad_mul_smul, jetQuad_mul_one, jetQuad_smul_smul,
      inv_mul_cancel₀ ha, jetQuad_one_smul]
    exact eqAsJet_refl _
  exact isInvertibleJet_of_twoSided t hA (t.smulJet hA hA a (t.oneJet hA))
    (t.smulJet hA hA a⁻¹ (t.oneJet hA)) h₁ h₂
private theorem logNumber_neg (t : JetToolkit δ p) {A : PeriodicData} (hA : IsPeriodic A)
    {T : JetQuad A A} (hT : IsInvertibleJet δ p T) :
    IsInvertibleJet δ p (smul (-1) T) ∧ logNumber p (smul (-1) T) = logNumber p T := by
  have hm := isInvertibleJet_smul_one t hA (δ := δ) (p := p) (a := -1) (by norm_num)
  have hsq := (t.numberAdd hA hm hm).2
  have hsq' : mul p (smul (-1) (one A)) (smul (-1) (one A)) = one A := by
    rw [jetQuad_smul_mul, jetQuad_mul_smul, jetQuad_mul_one, jetQuad_smul_smul]
    norm_num
    exact jetQuad_one_smul _
  rw [hsq', logNumber_one t hA] at hsq
  have hprod := t.numberAdd hA hm hT
  have hform : mul p (smul (-1) (one A)) T = smul (-1) T := by
    rw [jetQuad_smul_mul, jetQuad_one_mul]
  rw [hform] at hprod
  refine ⟨hprod.1, ?_⟩
  rw [hprod.2]
  linear_combination (-1 / 2) * hsq
end Invertible
section Blocks
variable {δ : ℝ} {p : Fin 4 → ℂ} {I₁ I₂ : PeriodicData}
private def fourBlocks (a : JetQuad I₁ I₁) (b : JetQuad I₂ I₁) (c : JetQuad I₁ I₂)
    (d : JetQuad I₂ I₂) :
    ∀ i j : Fin 2, JetQuad (pairData I₁ I₂ j) (pairData I₁ I₂ i)
  | 0, 0 => a
  | 0, 1 => b
  | 1, 0 => c
  | 1, 1 => d
private def blockOfFour (a : JetQuad I₁ I₁) (b : JetQuad I₂ I₁) (c : JetQuad I₁ I₂)
    (d : JetQuad I₂ I₂) :
    JetQuad (PeriodicData.sigma (pairData I₁ I₂)) (PeriodicData.sigma (pairData I₁ I₂)) :=
  blockJet (pairData I₁ I₂) (fourBlocks a b c d)
private theorem saddleJet_eq_blockOfFour (X : JetQuad I₁ I₁) (Q : JetQuad I₁ I₂) :
    saddleJet p X Q = blockOfFour X (transposeAt p Q) Q (zeroJet I₂ I₂) := by
  have h : saddleBlocks p X Q = fourBlocks X (transposeAt p Q) Q (zeroJet I₂ I₂) := by
    funext i j
    fin_cases i <;> fin_cases j <;> rfl
  simp only [saddleJet, blockOfFour, h]
private theorem blockOfFour_congr {a a' : JetQuad I₁ I₁} {b b' : JetQuad I₂ I₁}
    {c c' : JetQuad I₁ I₂} {d d' : JetQuad I₂ I₂} (ha : EqAsJet δ p a a')
    (hb : EqAsJet δ p b b') (hc : EqAsJet δ p c c') (hd : EqAsJet δ p d d') :
    EqAsJet δ p (blockOfFour a b c d) (blockOfFour a' b' c' d') := by
  have h : ∀ i j, EqAsJet δ p (fourBlocks a b c d i j) (fourBlocks a' b' c' d' i j) := by
    intro i j
    fin_cases i <;> fin_cases j
    exacts [ha, hb, hc, hd]
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_, fun κ hκ => ?_, fun κ hκ => ?_⟩
  · show blockQuotHom _ (fun i j => (fourBlocks a b c d i j).f00 κ) =
      blockQuotHom _ (fun i j => (fourBlocks a' b' c' d' i j).f00 κ)
    congr 1
    funext i j
    exact (h i j).1 hκ
  · show blockQuotHom _ (fun i j => (fourBlocks a b c d i j).f10 κ) =
      blockQuotHom _ (fun i j => (fourBlocks a' b' c' d' i j).f10 κ)
    congr 1
    funext i j
    exact (h i j).2.1 hκ
  · show blockQuotHom _ (fun i j => (fourBlocks a b c d i j).f01 κ) =
      blockQuotHom _ (fun i j => (fourBlocks a' b' c' d' i j).f01 κ)
    congr 1
    funext i j
    exact (h i j).2.2.1 hκ
  · show blockQuotHom _ (fun i j => (fourBlocks a b c d i j).f11 κ) =
      blockQuotHom _ (fun i j => (fourBlocks a' b' c' d' i j).f11 κ)
    congr 1
    funext i j
    exact (h i j).2.2.2 hκ
private structure BlockToolkit (δ : ℝ) (p : Fin 4 → ℂ) (I₁ I₂ : PeriodicData) : Prop where
  sigmaPeriodic : IsPeriodic (PeriodicData.sigma (pairData I₁ I₂))
  zero11 : IsJet δ p (zeroJet I₁ I₁)
  zero12 : IsJet δ p (zeroJet I₂ I₁)
  zero21 : IsJet δ p (zeroJet I₁ I₂)
  zero22 : IsJet δ p (zeroJet I₂ I₂)
  blockIsJet : ∀ {a : JetQuad I₁ I₁} {b : JetQuad I₂ I₁} {c : JetQuad I₁ I₂}
    {d : JetQuad I₂ I₂}, IsJet δ p a → IsJet δ p b → IsJet δ p c → IsJet δ p d →
      IsJet δ p (blockOfFour a b c d)
  blockMul : ∀ {a a' : JetQuad I₁ I₁} {b b' : JetQuad I₂ I₁} {c c' : JetQuad I₁ I₂}
    {d d' : JetQuad I₂ I₂}, IsJet δ p a → IsJet δ p b → IsJet δ p c → IsJet δ p d →
      IsJet δ p a' → IsJet δ p b' → IsJet δ p c' → IsJet δ p d' →
      EqAsJet δ p (mul p (blockOfFour a b c d) (blockOfFour a' b' c' d'))
        (blockOfFour (add (mul p a a') (mul p b c')) (add (mul p a b') (mul p b d'))
          (add (mul p c a') (mul p d c')) (add (mul p c b') (mul p d d')))
  oneBlock : EqAsJet δ p (one (PeriodicData.sigma (pairData I₁ I₂)))
    (blockOfFour (one I₁) (zeroJet I₂ I₁) (zeroJet I₁ I₂) (one I₂))
  upper : ∀ {a : JetQuad I₁ I₁} {b : JetQuad I₂ I₁} {d : JetQuad I₂ I₂},
    IsInvertibleJet δ p a → IsJet δ p b → IsInvertibleJet δ p d →
      IsInvertibleJet δ p (blockOfFour a b (zeroJet I₁ I₂) d) ∧
        logNumber p (blockOfFour a b (zeroJet I₁ I₂) d) = logNumber p a + logNumber p d
private theorem blockToolkit (hC : JetCalculus.Claim)
    (hBP : BlockJetProducts.Claim) (hBJ : BlockJetsAreJets.Claim)
    (hU : CopiesUnions.Claim) (t : JetToolkit δ p)
    (hδ : 0 < δ) (hp : p ∈ imStrip δ) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂) :
    BlockToolkit δ p I₁ I₂ := by
  have hJ : ∀ b, IsPeriodic (pairData I₁ I₂ b) := by
    intro b
    fin_cases b
    exacts [h₁, h₂]
  have bj := hBJ δ p hδ hp (pairData I₁ I₂) hJ
  have bp := hBP δ p hδ hp (pairData I₁ I₂) hJ
  have z11 : IsJet δ p (zeroJet I₁ I₁) := bj.zero_isJet 0 0
  have z12 : IsJet δ p (zeroJet I₂ I₁) := bj.zero_isJet 0 1
  have z21 : IsJet δ p (zeroJet I₁ I₂) := bj.zero_isJet 1 0
  have z22 : IsJet δ p (zeroJet I₂ I₂) := bj.zero_isJet 1 1
  have jets : ∀ {a : JetQuad I₁ I₁} {b : JetQuad I₂ I₁} {c : JetQuad I₁ I₂}
      {d : JetQuad I₂ I₂}, IsJet δ p a → IsJet δ p b → IsJet δ p c → IsJet δ p d →
        ∀ i j, IsJet δ p (fourBlocks a b c d i j) := by
    intro a b c d ha hb hc hd i j
    fin_cases i <;> fin_cases j
    exacts [ha, hb, hc, hd]
  refine ⟨hU.2.2 _ hJ, z11, z12, z21, z22, fun ha hb hc hd => bj.block_isJet _ (jets ha hb hc hd),
    ?_, ?_, ?_⟩
  · intro a a' b b' c c' d d' ha hb hc hd ha' hb' hc' hd'
    have h := bp _ _ (jets ha hb hc hd) (jets ha' hb' hc' hd')
    have e : (fun i j => add (mul p (fourBlocks a b c d i 0) (fourBlocks a' b' c' d' 0 j))
        (mul p (fourBlocks a b c d i 1) (fourBlocks a' b' c' d' 1 j))) =
        fourBlocks (add (mul p a a') (mul p b c')) (add (mul p a b') (mul p b d'))
          (add (mul p c a') (mul p d c')) (add (mul p c b') (mul p d d')) := by
      funext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [e] at h
    exact h
  · exact bj.one_eq_blockJet _ rfl rfl rfl rfl
  · intro a b d ha hb hd
    have hj := jets ha.isJet hb z21 hd.isJet
    have tri := bj.blockTriangular _ hj rfl
    obtain ⟨-, hbt⟩ := (hC δ p hδ hp).2.2.2.2.2.2.2.1 (pairData I₁ I₂) hJ
    have hbt' := hbt _ (bj.block_isJet _ hj) tri
    have d0 := bj.diagBlock_blockJet _ hj 0
    have d1 := bj.diagBlock_blockJet _ hj 1
    have e0 := t.eqNumber h₁ (T := a)
      (T' := diagBlock (pairData I₁ I₂) 0 (blockOfFour a b (zeroJet I₁ I₂) d))
      ha.isJet d0.1 (eqAsJet_symm d0.2) ha
    have e1 := t.eqNumber h₂ (T := d)
      (T' := diagBlock (pairData I₁ I₂) 1 (blockOfFour a b (zeroJet I₁ I₂) d))
      hd.isJet d1.1 (eqAsJet_symm d1.2) hd
    have hall : ∀ b', IsInvertibleJet δ p
        (diagBlock (pairData I₁ I₂) b' (blockOfFour a b (zeroJet I₁ I₂) d)) := by
      intro b'
      fin_cases b'
      exacts [e0.1, e1.1]
    obtain ⟨hi, hn⟩ := hbt'.2 hall
    refine ⟨hi, ?_⟩
    rw [e0.2, e1.2]
    exact hn
private def lowerUnipotent (n : JetQuad I₁ I₂) :
    JetQuad (PeriodicData.sigma (pairData I₁ I₂)) (PeriodicData.sigma (pairData I₁ I₂)) :=
  blockOfFour (one I₁) (zeroJet I₂ I₁) n (one I₂)
private def upperUnipotent (m : JetQuad I₂ I₁) :
    JetQuad (PeriodicData.sigma (pairData I₁ I₂)) (PeriodicData.sigma (pairData I₁ I₂)) :=
  blockOfFour (one I₁) m (zeroJet I₁ I₂) (one I₂)
private theorem lowerUnipotent_mul (t : JetToolkit δ p) (bt : BlockToolkit δ p I₁ I₂)
    (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂) {n m : JetQuad I₁ I₂}
    (hn : IsJet δ p n) (hm : IsJet δ p m) :
    EqAsJet δ p (mul p (lowerUnipotent n) (lowerUnipotent m)) (lowerUnipotent (add n m)) := by
  have h := bt.blockMul (t.oneJet h₁) bt.zero12 hn (t.oneJet h₂) (t.oneJet h₁) bt.zero12 hm
    (t.oneJet h₂)
  simpa only [lowerUnipotent, upperUnipotent, jetQuad_mul_one, jetQuad_one_mul, jetQuad_mul_zero,
    jetQuad_zero_mul, jetQuad_add_zero, jetQuad_zero_add] using h
private theorem lowerUnipotent_invertible (t : JetToolkit δ p) (bt : BlockToolkit δ p I₁ I₂)
    (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂) {n : JetQuad I₁ I₂}
    (hn : IsJet δ p n) : IsInvertibleJet δ p (lowerUnipotent n) := by
  have hneg := t.smulJet h₁ h₂ (-1) hn
  have hL : ∀ {m : JetQuad I₁ I₂}, IsJet δ p m → IsJet δ p (lowerUnipotent m) := fun hm =>
    bt.blockIsJet (t.oneJet h₁) bt.zero12 hm (t.oneJet h₂)
  have e₁ := lowerUnipotent_mul t bt h₁ h₂ hn hneg
  have e₂ := lowerUnipotent_mul t bt h₁ h₂ hneg hn
  rw [jetQuad_add_neg] at e₁
  rw [jetQuad_neg_add] at e₂
  exact isInvertibleJet_of_twoSided t bt.sigmaPeriodic (hL hn) (hL hneg)
    (eqAsJet_trans e₁ (eqAsJet_symm bt.oneBlock)) (eqAsJet_trans e₂ (eqAsJet_symm bt.oneBlock))
private theorem logNumber_lowerUnipotent (t : JetToolkit δ p) (bt : BlockToolkit δ p I₁ I₂)
    (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂) {n : JetQuad I₁ I₂}
    (hn : IsJet δ p n) : logNumber p (lowerUnipotent n) = 0 := by
  have o₁ := t.oneJet (δ := δ) (p := p) h₁
  have o₂ := t.oneJet (δ := δ) (p := p) h₂
  have h2n := t.smulJet h₁ h₂ 2 hn
  have two₂ := isInvertibleJet_smul_one t h₂ (δ := δ) (p := p) (a := 2) (by norm_num)
  have hD := (bt.upper (isInvertibleJet_one t h₁) bt.zero12 two₂).1
  have hL := lowerUnipotent_invertible t bt h₁ h₂ hn
  have hL2 := lowerUnipotent_invertible t bt h₁ h₂ h2n
  have e₁ := t.numberAdd bt.sigmaPeriodic hD hL
  have e₂ := t.numberAdd bt.sigmaPeriodic hL2 hD
  have e₃ := t.numberAdd bt.sigmaPeriodic hL hL
  have l₁ : EqAsJet δ p
      (mul p (blockOfFour (one I₁) (zeroJet I₂ I₁) (zeroJet I₁ I₂) (smul 2 (one I₂)))
        (lowerUnipotent n))
      (blockOfFour (one I₁) (zeroJet I₂ I₁) (smul 2 n) (smul 2 (one I₂))) := by
    have h := bt.blockMul o₁ bt.zero12 bt.zero21 two₂.isJet o₁ bt.zero12 hn o₂
    simpa only [lowerUnipotent, upperUnipotent, jetQuad_mul_one, jetQuad_one_mul,
      jetQuad_mul_zero, jetQuad_zero_mul, jetQuad_add_zero, jetQuad_zero_add, jetQuad_smul_mul,
      jetQuad_mul_smul, jetQuad_smul_zero] using h
  have l₂ : EqAsJet δ p
      (mul p (lowerUnipotent (smul 2 n))
        (blockOfFour (one I₁) (zeroJet I₂ I₁) (zeroJet I₁ I₂) (smul 2 (one I₂))))
      (blockOfFour (one I₁) (zeroJet I₂ I₁) (smul 2 n) (smul 2 (one I₂))) := by
    have h := bt.blockMul o₁ bt.zero12 h2n o₂ o₁ bt.zero12 bt.zero21 two₂.isJet
    simpa only [lowerUnipotent, upperUnipotent, jetQuad_mul_one, jetQuad_one_mul,
      jetQuad_mul_zero, jetQuad_zero_mul, jetQuad_add_zero, jetQuad_zero_add, jetQuad_smul_mul,
      jetQuad_mul_smul, jetQuad_smul_zero] using h
  have s₁ := (t.eqNumber bt.sigmaPeriodic e₁.1.isJet e₂.1.isJet
    (eqAsJet_trans l₁ (eqAsJet_symm l₂)) e₁.1).2
  have l₃ := lowerUnipotent_mul t bt h₁ h₂ hn hn
  rw [jetQuad_add_self] at l₃
  have s₂ := (t.eqNumber bt.sigmaPeriodic e₃.1.isJet hL2.isJet l₃ e₃.1).2
  rw [e₁.2, e₂.2] at s₁
  rw [e₃.2] at s₂
  linear_combination s₂ - s₁
private theorem upperUnipotent_facts (t : JetToolkit δ p) (bt : BlockToolkit δ p I₁ I₂)
    (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂) {m : JetQuad I₂ I₁}
    (hm : IsJet δ p m) :
    IsInvertibleJet δ p (upperUnipotent m) ∧ logNumber p (upperUnipotent m) = 0 := by
  have h := bt.upper (isInvertibleJet_one t h₁) hm (isInvertibleJet_one t h₂)
  refine ⟨h.1, ?_⟩
  show logNumber p (blockOfFour (one I₁) m (zeroJet I₁ I₂) (one I₂)) = 0
  rw [h.2, logNumber_one t h₁, logNumber_one t h₂, add_zero]
private theorem saddleJet_factorization (t : JetToolkit δ p) (bt : BlockToolkit δ p I₁ I₂)
    (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂) {X Y : JetQuad I₁ I₁}
    {Q : JetQuad I₁ I₂} {R : JetQuad I₂ I₁} (hX : IsJet δ p X) (hY : IsJet δ p Y)
    (hQ : IsJet δ p Q) (hR : IsJet δ p R) (hYX : EqAsJet δ p (mul p Y X) (one I₁))
    (hXY : EqAsJet δ p (mul p X Y) (one I₁)) :
    EqAsJet δ p
      (mul p (mul p (lowerUnipotent (mul p Q Y))
          (blockOfFour X (zeroJet I₂ I₁) (zeroJet I₁ I₂) (smul (-1) (mul p (mul p Q Y) R))))
        (upperUnipotent (mul p Y R)))
      (blockOfFour X R Q (zeroJet I₂ I₂)) := by
  have o₁ := t.oneJet (δ := δ) (p := p) h₁
  have o₂ := t.oneJet (δ := δ) (p := p) h₂
  have hN : IsJet δ p (mul p Q Y) := t.mulJet h₁ h₂ h₁ hQ hY
  have hM : IsJet δ p (mul p Y R) := t.mulJet h₁ h₁ h₂ hY hR
  have hC : IsJet δ p (mul p (mul p Q Y) R) := t.mulJet h₁ h₂ h₂ hN hR
  have hNeg := t.smulJet h₂ h₂ (-1) hC
  have hNX : IsJet δ p (mul p (mul p Q Y) X) := t.mulJet h₁ h₂ h₁ hN hX
  have a₁ : EqAsJet δ p
      (mul p (lowerUnipotent (mul p Q Y))
        (blockOfFour X (zeroJet I₂ I₁) (zeroJet I₁ I₂) (smul (-1) (mul p (mul p Q Y) R))))
      (blockOfFour X (zeroJet I₂ I₁) (mul p (mul p Q Y) X)
        (smul (-1) (mul p (mul p Q Y) R))) := by
    have h := bt.blockMul o₁ bt.zero12 hN o₂ hX bt.zero12 bt.zero21 hNeg
    simpa only [lowerUnipotent, upperUnipotent, jetQuad_mul_one, jetQuad_one_mul,
      jetQuad_mul_zero, jetQuad_zero_mul, jetQuad_add_zero, jetQuad_zero_add] using h
  have a₂ : EqAsJet δ p (mul p (mul p Q Y) X) Q := by
    have h := eqAsJet_trans (t.assoc h₂ h₁ h₁ h₁ hQ hY hX)
      (t.eqMul h₁ h₂ h₁ hQ hQ (t.mulJet h₁ h₁ h₁ hY hX) o₁ (eqAsJet_refl Q) hYX)
    rwa [jetQuad_mul_one] at h
  have a₃ := blockOfFour_congr (eqAsJet_refl X) (eqAsJet_refl (zeroJet I₂ I₁)) a₂
    (eqAsJet_refl (smul (-1) (mul p (mul p Q Y) R)))
  have hG := bt.blockIsJet hX bt.zero12 hQ hNeg
  have hLD : IsJet δ p (mul p (lowerUnipotent (mul p Q Y))
      (blockOfFour X (zeroJet I₂ I₁) (zeroJet I₁ I₂) (smul (-1) (mul p (mul p Q Y) R)))) :=
    t.mulJet bt.sigmaPeriodic bt.sigmaPeriodic bt.sigmaPeriodic
      (bt.blockIsJet o₁ bt.zero12 hN o₂) (bt.blockIsJet hX bt.zero12 bt.zero21 hNeg)
  have hU : IsJet δ p (upperUnipotent (mul p Y R)) := bt.blockIsJet o₁ hM bt.zero21 o₂
  have a₄ := t.eqMul bt.sigmaPeriodic bt.sigmaPeriodic bt.sigmaPeriodic hLD hG hU hU
    (eqAsJet_trans a₁ a₃) (eqAsJet_refl _)
  have a₅ : EqAsJet δ p
      (mul p (blockOfFour X (zeroJet I₂ I₁) Q (smul (-1) (mul p (mul p Q Y) R)))
        (upperUnipotent (mul p Y R)))
      (blockOfFour X (mul p X (mul p Y R)) Q
        (add (mul p Q (mul p Y R)) (smul (-1) (mul p (mul p Q Y) R)))) := by
    have h := bt.blockMul hX bt.zero12 hQ hNeg o₁ hM bt.zero21 o₂
    simpa only [lowerUnipotent, upperUnipotent, jetQuad_mul_one, jetQuad_one_mul,
      jetQuad_mul_zero, jetQuad_zero_mul, jetQuad_add_zero, jetQuad_zero_add,
      jetQuad_smul_zero, jetQuad_smul_mul] using h
  have a₆ : EqAsJet δ p (mul p X (mul p Y R)) R := by
    have h := eqAsJet_trans (eqAsJet_symm (t.assoc h₁ h₁ h₁ h₂ hX hY hR))
      (t.eqMul h₁ h₁ h₂ (t.mulJet h₁ h₁ h₁ hX hY) o₁ hR hR hXY (eqAsJet_refl R))
    rwa [jetQuad_one_mul] at h
  have a₇ : EqAsJet δ p (add (mul p Q (mul p Y R)) (smul (-1) (mul p (mul p Q Y) R)))
      (zeroJet I₂ I₂) := by
    have h := t.eqAdd h₂ h₂ (t.mulJet h₁ h₂ h₂ hQ hM) hC hNeg hNeg
      (eqAsJet_symm (t.assoc h₂ h₁ h₁ h₂ hQ hY hR)) (eqAsJet_refl _)
    rwa [jetQuad_add_neg] at h
  exact eqAsJet_trans a₄
    (eqAsJet_trans a₅ (blockOfFour_congr (eqAsJet_refl X) a₆ (eqAsJet_refl Q) a₇))
end Blocks
theorem holds (hC : JetCalculus.Claim) (hBP : BlockJetProducts.Claim)
    (hBJ : BlockJetsAreJets.Claim)
    (hU : CopiesUnions.Claim)
    (hEq : JetArgumentsAndEqualJets)
    (hSum : JetAddSMul.Claim) (hTr : JetTransposition.Holds)
    (hPr : JetProducts.Claim) (hOne : ZeroPartJets.Claim)
    (hNorm : JetNormsAffine.Claim) : Claim := by
  intro I₁ I₂ h₁ h₂ δ p hδ hp Ξ Q hΞ hQ hCon
  have t := jetToolkit hC hEq hSum hPr hOne hNorm δ p hδ hp
  have bt : BlockToolkit δ p I₁ I₂ := blockToolkit hC hBP hBJ hU t hδ hp h₁ h₂
  have o₁ := t.oneJet (δ := δ) (p := p) h₁
  have o₂ := t.oneJet (δ := δ) (p := p) h₂
  have hR : IsJet δ p (transposeAt p Q) := (hTr I₁ I₂ h₁ h₂ δ p hδ hp).2 Q hQ
  obtain ⟨hY, hYX, hXY⟩ := t.inverseFacts h₁ hΞ
  have hN : IsJet δ p (mul p Q (invJet p Ξ)) := t.mulJet h₁ h₂ h₁ hQ hY
  have hM : IsJet δ p (mul p (invJet p Ξ) (transposeAt p Q)) := t.mulJet h₁ h₁ h₂ hY hR
  have hfac := saddleJet_factorization t bt h₁ h₂ hΞ.isJet hY hQ hR hYX hXY
  obtain ⟨hnegI, hnegN⟩ := logNumber_neg t h₂ hCon
  have hLI := lowerUnipotent_invertible t bt h₁ h₂ hN
  have hLN := logNumber_lowerUnipotent t bt h₁ h₂ hN
  have hD := bt.upper hΞ bt.zero12 hnegI
  obtain ⟨hRI, hRN⟩ := upperUnipotent_facts t bt h₁ h₂ hM
  have p₁ := t.numberAdd bt.sigmaPeriodic hLI hD.1
  have p₂ := t.numberAdd bt.sigmaPeriodic p₁.1 hRI
  have hSJ := bt.blockIsJet hΞ.isJet hR hQ bt.zero22
  have hS := t.eqNumber bt.sigmaPeriodic p₂.1.isJet hSJ hfac p₂.1
  have hNR := t.smulJet h₂ h₁ (-1) hR
  obtain ⟨hUI, hUN⟩ := upperUnipotent_facts t bt h₁ h₂ hNR
  have p₃ := t.numberAdd bt.sigmaPeriodic hUI hS.1
  have hA : EqAsJet δ p
      (mul p (upperUnipotent (smul (-1) (transposeAt p Q)))
        (blockOfFour Ξ (transposeAt p Q) Q (zeroJet I₂ I₂)))
      (blockOfFour (subGramJet p Ξ Q) (transposeAt p Q) Q (zeroJet I₂ I₂)) := by
    have h := bt.blockMul o₁ hNR bt.zero21 o₂ hΞ.isJet hR hQ bt.zero22
    simpa only [lowerUnipotent, upperUnipotent, subGramJet, jetQuad_mul_one, jetQuad_one_mul,
      jetQuad_mul_zero, jetQuad_zero_mul, jetQuad_add_zero, jetQuad_zero_add,
      jetQuad_smul_zero, jetQuad_smul_mul] using h
  have hAJ : IsJet δ p (blockOfFour (subGramJet p Ξ Q) (transposeAt p Q) Q (zeroJet I₂ I₂)) :=
    bt.blockIsJet (t.addJet h₁ h₁ hΞ.isJet
      (t.smulJet h₁ h₁ (-1) (t.mulJet h₂ h₁ h₁ hR hQ))) hR hQ bt.zero22
  have hfin := t.eqNumber bt.sigmaPeriodic p₃.1.isJet hAJ hA p₃.1
  rw [saddleJet_eq_blockOfFour]
  refine ⟨hfin.1, ?_⟩
  show logNumber p (blockOfFour (subGramJet p Ξ Q) (transposeAt p Q) Q (zeroJet I₂ I₂)) =
    logNumber p Ξ + logNumber p (schurJet p Ξ Q)
  rw [← hfin.2, p₃.2, ← hS.2, p₂.2, p₁.2, hD.2, hLN, hRN, hUN, hnegN]
  simp only [schurJet, zero_add, add_zero]
end YangMills.Construction.PeriodicOperators.SaddleJetNumber
end
