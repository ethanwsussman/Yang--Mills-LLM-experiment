import YangMills.Construction.PeriodicOperators.BlockMatricesOfJetsAreJets
import YangMills.Construction.PeriodicOperators.BoundOfTheKernelOfAMatrixFunctionProof
import YangMills.Construction.PeriodicOperators.JetsOfPeriodicOperatorsAndConstantPartsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.BlockJetsAreJets
open JetQuad (IsJet EqAsJet)
open BlockJets (BlockJetFacts)
section MatrixEntries
variable {A B : Type}
private theorem linearMap_ext_of_entry [Finite A] {M N : (A → ℂ) →ₗ[ℂ] (B → ℂ)}
    (h : linearMapEntry M = linearMapEntry N) : M = N := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMap_ext_of_entry <;> assumption
private theorem linearMapOfEntries_linearMapEntry [Finite A] (N : (A → ℂ) →ₗ[ℂ] (B → ℂ)) :
    linearMapOfEntries (linearMapEntry N) = N :=
  linearMap_ext_of_entry
    (Classical.epsilon_spec (p := fun M => linearMapEntry M = linearMapEntry N) ⟨N, rfl⟩)
private theorem linearMapEntry_linearMapOfEntries [Finite A] (K : B → A → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMapEntry_linearMapOfEntries <;> assumption
private theorem linearMapEntry_zero (b : B) (a : A) :
    linearMapEntry (0 : (A → ℂ) →ₗ[ℂ] (B → ℂ)) b a = 0 := by
  simp [linearMapEntry]
open Classical in
private theorem linearMapEntry_id (a' a : A) :
    linearMapEntry (LinearMap.id : (A → ℂ) →ₗ[ℂ] (A → ℂ)) a' a = if a' = a then 1 else 0 := by
  simp [linearMapEntry, Pi.single_apply]
end MatrixEntries
section Phase
variable {I I' : PeriodicData}
private theorem cexp_two_pi_I_intDot (e k : Fin 4 → ℤ) :
    Complex.exp (2 * Real.pi * Complex.I *
      bilinDot (toComplexVec (castVec e)) (toComplexVec (castVec k))) = 1 := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolTranslation.exp_two_pi_I_bilinDot_int <;> assumption
private def phasePoint (I : PeriodicData) (e : Fin 4 → ℤ) (x : I.Carrier) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I *
    bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos x)))
private theorem phasePoint_translate (hI : IsPeriodic I) (e k : Fin 4 → ℤ) (x : I.Carrier) :
    phasePoint I e (I.translate k x) = phasePoint I e x := by
  have h : bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos x + castVec k)) =
      bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos x)) +
        bilinDot (toComplexVec (castVec e)) (toComplexVec (castVec k)) := by
    simp [bilinDot, toComplexVec, mul_add, Finset.sum_add_distrib]
  unfold phasePoint
  rw [hI.pos_translate, h, mul_add, Complex.exp_add, cexp_two_pi_I_intDot, mul_one]
private theorem phaseOn_mkQuot (hI : IsPeriodic I) (e : Fin 4 → ℤ) (x : I.Carrier) :
    phaseOn I e (I.mkQuot 1 x) = phasePoint I e x := by
  have hL : ∀ x₁ x₂ : I.Carrier, I.mkQuot 1 x₁ = I.mkQuot 1 x₂ →
      phasePoint I e x₁ = phasePoint I e x₂ := by
    intro x₁ x₂ hc
    let L : I.QuotMod 1 → ℂ := Quot.lift (phasePoint I e) (by
      rintro a _ ⟨k, rfl⟩
      exact (phasePoint_translate hI e _ a).symm)
    exact congrArg L hc
  have hex : ∃ z, ∀ x', I.mkQuot 1 x' = I.mkQuot 1 x →
      Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos x'))) = z :=
    ⟨phasePoint I e x, fun x' h => hL x' x h⟩
  exact ((Classical.epsilon_spec hex) x rfl).symm
private theorem linearMapEntry_conj (hI' : IsPeriodic I') (e : Fin 4 → ℤ) (M : QuotHom I I')
    (c' : I'.UnitQuot) (c : I.UnitQuot) :
    linearMapEntry ((quotHomInverse (phaseMul I' e)).comp
        (M.comp (phaseMul I e))) c' c =
      (phaseOn I' e c')⁻¹ * linearMapEntry M c' c * phaseOn I e c := by apply _root_.YangMills.Construction.PeriodicOperators.MatrixFunctionKernel.linearMapEntry_conj_phaseMul <;> assumption
end Phase
section SigmaQuot
variable {J : Fin 2 → PeriodicData}
private theorem sigmaQuotPlace_sigmaQuotIn (b : Fin 2) (c : (J b).UnitQuot) :
    sigmaQuotPlace J (sigmaQuotIn J b c) = ⟨b, c⟩ := by
  induction c using Quot.ind with
  | mk i => rfl
private theorem sigmaQuotIn_sigmaQuotPlace (c : (PeriodicData.sigma J).UnitQuot) :
    sigmaQuotIn J (sigmaQuotPlace J c).1 (sigmaQuotPlace J c).2 = c := by
  induction c using Quot.ind with
  | mk x => rfl
private theorem exists_sigmaQuotIn_eq (c : (PeriodicData.sigma J).UnitQuot) :
    ∃ b, ∃ c', sigmaQuotIn J b c' = c :=
  ⟨_, _, sigmaQuotIn_sigmaQuotPlace c⟩
private theorem sigmaQuotIn_inj {b b' : Fin 2} {c : (J b).UnitQuot} {c' : (J b').UnitQuot}
    (h : sigmaQuotIn J b c = sigmaQuotIn J b' c') :
    (⟨b, c⟩ : Σ b, (J b).UnitQuot) = ⟨b', c'⟩ := by
  rw [← sigmaQuotPlace_sigmaQuotIn, ← sigmaQuotPlace_sigmaQuotIn, h]
private theorem phaseOn_sigmaQuotIn (hJ : ∀ b, IsPeriodic (J b)) (e : Fin 4 → ℤ) (b : Fin 2)
    (c : (J b).UnitQuot) :
    phaseOn (PeriodicData.sigma J) e (sigmaQuotIn J b c) = phaseOn (J b) e c := by
  induction c using Quot.ind with
  | mk x =>
    exact (phaseOn_mkQuot (IsPeriodic.sigma hJ) e ⟨b, x⟩).trans
      (phaseOn_mkQuot (hJ b) e x).symm
private theorem linearMapEntry_blockQuotHom (hJ : ∀ b, IsPeriodic (J b))
    (M : ∀ i j, QuotHom (J j) (J i)) (i j : Fin 2) (c' : (J i).UnitQuot) (c : (J j).UnitQuot) :
    linearMapEntry (blockQuotHom J M) (sigmaQuotIn J i c') (sigmaQuotIn J j c) =
      linearMapEntry (M i j) c' c := by
  have : Finite (PeriodicData.sigma J).UnitQuot := (IsPeriodic.sigma hJ).finite_quot
  unfold blockQuotHom
  rw [linearMapEntry_linearMapOfEntries, sigmaQuotPlace_sigmaQuotIn, sigmaQuotPlace_sigmaQuotIn]
  rfl
private theorem quotHom_ext_sigma (hJ : ∀ b, IsPeriodic (J b))
    {M N : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)}
    (h : ∀ (i j : Fin 2) (c' : (J i).UnitQuot) (c : (J j).UnitQuot),
      linearMapEntry M (sigmaQuotIn J i c') (sigmaQuotIn J j c) =
        linearMapEntry N (sigmaQuotIn J i c') (sigmaQuotIn J j c)) : M = N := by
  have : Finite (PeriodicData.sigma J).UnitQuot := (IsPeriodic.sigma hJ).finite_quot
  refine linearMap_ext_of_entry (funext fun y' => funext fun y => ?_)
  obtain ⟨i, c', rfl⟩ := exists_sigmaQuotIn_eq y'
  obtain ⟨j, c, rfl⟩ := exists_sigmaQuotIn_eq y
  exact h i j c' c
private theorem blockQuotHom_conj (hJ : ∀ b, IsPeriodic (J b)) (e : Fin 4 → ℤ)
    (M : ∀ i j, QuotHom (J j) (J i)) :
    blockQuotHom J (fun i j => (quotHomInverse (phaseMul (J i) e)).comp
        ((M i j).comp (phaseMul (J j) e))) =
      (quotHomInverse (phaseMul (PeriodicData.sigma J) e)).comp
        ((blockQuotHom J M).comp (phaseMul (PeriodicData.sigma J) e)) := by
  refine quotHom_ext_sigma hJ fun i j c' c => ?_
  rw [linearMapEntry_blockQuotHom hJ, linearMapEntry_conj (hJ i),
    linearMapEntry_conj (IsPeriodic.sigma hJ), linearMapEntry_blockQuotHom hJ,
    phaseOn_sigmaQuotIn hJ, phaseOn_sigmaQuotIn hJ]
private theorem isHolomorphicNbhd_blockQuotHom (hJ : ∀ b, IsPeriodic (J b))
    (D : Set (Fin 4 → ℂ)) (M : (Fin 4 → ℂ) → ∀ i j, QuotHom (J j) (J i))
    (h : ∀ i j, IsHolomorphicNbhd D fun κ => M κ i j) :
    IsHolomorphicNbhd D fun κ => blockQuotHom J (M κ) := by
  choose U hU hD hH using h
  have hopen : IsOpen (⋂ i, ⋂ j, U i j) :=
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hU i j
  refine ⟨⋂ i, ⋂ j, U i j, hopen, subset_iInter fun i => subset_iInter fun j => hD i j,
    fun y' y => ?_⟩
  obtain ⟨i, c', rfl⟩ := exists_sigmaQuotIn_eq y'
  obtain ⟨j, c, rfl⟩ := exists_sigmaQuotIn_eq y
  have hsub : (⋂ i, ⋂ j, U i j) ⊆ U i j :=
    (iInter_subset _ i).trans (iInter_subset _ j)
  have hfun : (fun (κ : Fin 4 → ℂ) (_ : Fin 1) =>
      linearMapEntry (blockQuotHom J (M κ)) (sigmaQuotIn J i c') (sigmaQuotIn J j c)) =
      fun κ _ => linearMapEntry (M κ i j) c' c := by
    funext κ _
    exact linearMapEntry_blockQuotHom hJ (M κ) i j c' c
  rw [hfun]
  have hij := hH i j c' c
  exact ⟨hopen, hij.2.1.mono hsub, fun a ha => hij.2.2 a (hsub ha)⟩
private theorem isQuasiPeriodic_blockQuotHom (hJ : ∀ b, IsPeriodic (J b))
    (D : Set (Fin 4 → ℂ)) (M : (Fin 4 → ℂ) → ∀ i j, QuotHom (J j) (J i))
    (h : ∀ i j, IsQuasiPeriodic D fun κ => M κ i j) :
    IsQuasiPeriodic D fun κ => blockQuotHom J (M κ) := by
  intro e κ hκ
  show blockQuotHom J (M (addTwoPiInt κ e)) = _
  rw [← blockQuotHom_conj hJ e (M κ)]
  congr 1
  funext i j
  exact h i j e κ hκ
private theorem quotHomBlock_blockQuotHom (hJ : ∀ b, IsPeriodic (J b)) (b : Fin 2)
    (M : ∀ i j, QuotHom (J j) (J i)) : quotHomBlock J b (blockQuotHom J M) = M b b := by
  have : Finite (J b).UnitQuot := (hJ b).finite_quot
  have h : (fun c' c => linearMapEntry (blockQuotHom J M) (sigmaQuotIn J b c')
      (sigmaQuotIn J b c)) = linearMapEntry (M b b) := by
    funext c' c
    exact linearMapEntry_blockQuotHom hJ M b b c' c
  unfold quotHomBlock
  rw [h]
  exact linearMapOfEntries_linearMapEntry _
private theorem diagBlock_blockJet (hJ : ∀ b, IsPeriodic (J b))
    (T : ∀ i j, JetQuad (J j) (J i)) (b : Fin 2) :
    JetQuad.diagBlock J b (blockJet J T) = T b b := by
  refine JetQuad.ext ?_ ?_ ?_ ?_
  · funext κ
    exact quotHomBlock_blockQuotHom hJ b fun i j => (T i j).f00 κ
  · funext κ
    exact quotHomBlock_blockQuotHom hJ b fun i j => (T i j).f10 κ
  · funext κ
    exact quotHomBlock_blockQuotHom hJ b fun i j => (T i j).f01 κ
  · funext κ
    exact quotHomBlock_blockQuotHom hJ b fun i j => (T i j).f11 κ
private theorem linearMapEntry_blockQuotHom_of_eq_zero (hJ : ∀ b, IsPeriodic (J b))
    (M : ∀ i j, QuotHom (J j) (J i)) {i j : Fin 2} (h : M i j = 0)
    (c' : (J i).UnitQuot) (c : (J j).UnitQuot) :
    linearMapEntry (blockQuotHom J M) (sigmaQuotIn J i c') (sigmaQuotIn J j c) = 0 := by
  rw [linearMapEntry_blockQuotHom hJ, h, linearMapEntry_zero]
private theorem blockQuotHom_eq_zero (hJ : ∀ b, IsPeriodic (J b))
    (M : ∀ i j, QuotHom (J j) (J i)) (h : ∀ i j, M i j = 0) : blockQuotHom J M = 0 :=
  quotHom_ext_sigma hJ fun i j c' c => by
    rw [linearMapEntry_blockQuotHom_of_eq_zero hJ M (h i j), linearMapEntry_zero]
private theorem id_eq_blockQuotHom (hJ : ∀ b, IsPeriodic (J b))
    (M : ∀ i j, QuotHom (J j) (J i)) (h00 : M 0 0 = LinearMap.id) (h11 : M 1 1 = LinearMap.id)
    (h01 : M 0 1 = 0) (h10 : M 1 0 = 0) : LinearMap.id = blockQuotHom J M := by
  classical
  have hdiag : ∀ (b : Fin 2) (c' c : (J b).UnitQuot), M b b = LinearMap.id →
      linearMapEntry (LinearMap.id : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J))
          (sigmaQuotIn J b c') (sigmaQuotIn J b c) = linearMapEntry (M b b) c' c := by
    intro b c' c hb
    rw [hb, linearMapEntry_id, linearMapEntry_id]
    by_cases hc : c' = c
    · simp [hc]
    · have hne : sigmaQuotIn J b c' ≠ sigmaQuotIn J b c := fun e =>
        hc (by simpa using sigmaQuotIn_inj e)
      simp [hc, hne]
  have hoff : ∀ (i j : Fin 2) (c' : (J i).UnitQuot) (c : (J j).UnitQuot), i ≠ j → M i j = 0 →
      linearMapEntry (LinearMap.id : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J))
          (sigmaQuotIn J i c') (sigmaQuotIn J j c) = linearMapEntry (M i j) c' c := by
    intro i j c' c hij hb
    have hne : sigmaQuotIn J i c' ≠ sigmaQuotIn J j c := fun e =>
      hij (congrArg Sigma.fst (sigmaQuotIn_inj e))
    rw [hb, linearMapEntry_id, linearMapEntry_zero]
    simp [hne]
  refine quotHom_ext_sigma hJ fun i j c' c => ?_
  rw [linearMapEntry_blockQuotHom hJ]
  revert c' c
  revert i j
  refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
  · exact fun c' c => hdiag 0 c' c h00
  · exact fun c' c => hoff 0 1 c' c (by decide) h01
  · exact fun c' c => hoff 1 0 c' c (by decide) h10
  · exact fun c' c => hdiag 1 c' c h11
end SigmaQuot
section ZeroJet
variable {I I' : PeriodicData}
private theorem isHolomorphicNbhd_zero (D : Set (Fin 4 → ℂ)) :
    IsHolomorphicNbhd D (0 : (Fin 4 → ℂ) → QuotHom I I') := by
  refine ⟨univ, isOpen_univ, subset_univ _, fun c' c => ?_⟩
  have hfun : (fun (κ : Fin 4 → ℂ) (_ : Fin 1) =>
      linearMapEntry ((0 : (Fin 4 → ℂ) → QuotHom I I') κ) c' c) = fun _ _ => 0 := by
    funext κ _
    exact linearMapEntry_zero c' c
  rw [hfun]
  exact ⟨isOpen_univ, continuousOn_const, fun _ _ _ =>
    Filter.Eventually.of_forall fun _ => differentiableAt_const _⟩
private theorem isQuasiPeriodic_zero (D : Set (Fin 4 → ℂ)) :
    IsQuasiPeriodic D (0 : (Fin 4 → ℂ) → QuotHom I I') := by apply _root_.YangMills.Construction.PeriodicOperators.ZeroPartJets.isQuasiPeriodic_zero <;> assumption
private theorem isJet_zeroJet {δ : ℝ} {p : Fin 4 → ℂ} (hδ : 0 < δ) (hp : p ∈ imStrip δ) :
    IsJet δ p (JetQuad.zeroJet I I') :=
  ⟨hδ, hp, isHolomorphicNbhd_zero _, isHolomorphicNbhd_zero _, isHolomorphicNbhd_zero _,
    isHolomorphicNbhd_zero _, isQuasiPeriodic_zero _, isQuasiPeriodic_zero _,
    isQuasiPeriodic_zero _, isQuasiPeriodic_zero _⟩
end ZeroJet
theorem claim_holds : BlockJetsAreJets.Claim := by
  intro δ p hδ hp J hJ
  have hblock : ∀ T : ∀ i j, JetQuad (J j) (J i), (∀ i j, IsJet δ p (T i j)) →
      IsJet δ p (blockJet J T) := fun T h =>
    ⟨hδ, hp,
      isHolomorphicNbhd_blockQuotHom hJ _ (fun κ i j => (T i j).f00 κ)
        fun i j => (h i j).holo_f00,
      isHolomorphicNbhd_blockQuotHom hJ _ (fun κ i j => (T i j).f10 κ)
        fun i j => (h i j).holo_f10,
      isHolomorphicNbhd_blockQuotHom hJ _ (fun κ i j => (T i j).f01 κ)
        fun i j => (h i j).holo_f01,
      isHolomorphicNbhd_blockQuotHom hJ _ (fun κ i j => (T i j).f11 κ)
        fun i j => (h i j).holo_f11,
      isQuasiPeriodic_blockQuotHom hJ _ (fun κ i j => (T i j).f00 κ)
        fun i j => (h i j).quasiPeriodic_f00,
      isQuasiPeriodic_blockQuotHom hJ _ (fun κ i j => (T i j).f10 κ)
        fun i j => (h i j).quasiPeriodic_f10,
      isQuasiPeriodic_blockQuotHom hJ _ (fun κ i j => (T i j).f01 κ)
        fun i j => (h i j).quasiPeriodic_f01,
      isQuasiPeriodic_blockQuotHom hJ _ (fun κ i j => (T i j).f11 κ)
        fun i j => (h i j).quasiPeriodic_f11⟩
  refine
    { quot_sigma := ⟨fun c => ⟨sigmaQuotPlace J c, sigmaQuotIn_sigmaQuotPlace c, fun y hy => ?_⟩,
        fun x => sigmaQuotPlace_sigmaQuotIn x.1 x.2⟩
      zero_isJet := fun i j => isJet_zeroJet hδ hp
      block_isJet := hblock
      diagBlock_blockJet := fun T h b => ?_
      blockTriangular := fun T _ h c' c => ?_
      blockTriangularRev := fun T _ h c' c => ?_
      one_eq_blockJet := fun T h00 h11 h01 h10 => ?_ }
  · rw [← hy, sigmaQuotPlace_sigmaQuotIn]
  · rw [diagBlock_blockJet hJ]
    exact ⟨h b b, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · refine ⟨fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_⟩
    · exact linearMapEntry_blockQuotHom_of_eq_zero hJ (fun i j => (T i j).f00 κ)
        (by simp only [h]; rfl) c' c
    · exact linearMapEntry_blockQuotHom_of_eq_zero hJ (fun i j => (T i j).f10 κ)
        (by simp only [h]; rfl) c' c
    · exact linearMapEntry_blockQuotHom_of_eq_zero hJ (fun i j => (T i j).f01 κ)
        (by simp only [h]; rfl) c' c
    · exact linearMapEntry_blockQuotHom_of_eq_zero hJ (fun i j => (T i j).f11 κ)
        (by simp only [h]; rfl) c' c
  · refine ⟨fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_⟩
    · exact linearMapEntry_blockQuotHom_of_eq_zero hJ (fun i j => (T i j).f00 κ)
        (by simp only [h]; rfl) c' c
    · exact linearMapEntry_blockQuotHom_of_eq_zero hJ (fun i j => (T i j).f10 κ)
        (by simp only [h]; rfl) c' c
    · exact linearMapEntry_blockQuotHom_of_eq_zero hJ (fun i j => (T i j).f01 κ)
        (by simp only [h]; rfl) c' c
    · exact linearMapEntry_blockQuotHom_of_eq_zero hJ (fun i j => (T i j).f11 κ)
        (by simp only [h]; rfl) c' c
  · have hz10 : ∀ i j, (T i j).f10 = 0 := Fin.forall_fin_two.2
      ⟨Fin.forall_fin_two.2 ⟨by rw [h00]; rfl, by rw [h01]; rfl⟩,
        Fin.forall_fin_two.2 ⟨by rw [h10]; rfl, by rw [h11]; rfl⟩⟩
    have hz01 : ∀ i j, (T i j).f01 = 0 := Fin.forall_fin_two.2
      ⟨Fin.forall_fin_two.2 ⟨by rw [h00]; rfl, by rw [h01]; rfl⟩,
        Fin.forall_fin_two.2 ⟨by rw [h10]; rfl, by rw [h11]; rfl⟩⟩
    have hz11 : ∀ i j, (T i j).f11 = 0 := Fin.forall_fin_two.2
      ⟨Fin.forall_fin_two.2 ⟨by rw [h00]; rfl, by rw [h01]; rfl⟩,
        Fin.forall_fin_two.2 ⟨by rw [h10]; rfl, by rw [h11]; rfl⟩⟩
    refine ⟨fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_⟩
    · exact id_eq_blockQuotHom hJ (fun i j => (T i j).f00 κ) (by simp only [h00]; rfl)
        (by simp only [h11]; rfl) (by simp only [h01]; rfl) (by simp only [h10]; rfl)
    · exact (blockQuotHom_eq_zero hJ (fun i j => (T i j).f10 κ)
        fun i j => by simp only [hz10]; rfl).symm
    · exact (blockQuotHom_eq_zero hJ (fun i j => (T i j).f01 κ)
        fun i j => by simp only [hz01]; rfl).symm
    · exact (blockQuotHom_eq_zero hJ (fun i j => (T i j).f11 κ)
        fun i j => by simp only [hz11]; rfl).symm
end YangMills.Construction.PeriodicOperators.BlockJetsAreJets
end
