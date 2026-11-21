import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposesProof
import YangMills.Construction.Lattice.HolomorphyOfTheContinuationsUnderIsometries
import YangMills.Construction.Lattice.IsometryCovarianceOfRegularSetsAndAxialRepresentatives
import YangMills.Construction.Lattice.IsometryCovarianceOfTowersAndCubesOfAStep
import YangMills.Construction.Lattice.IsometryGroupsAndTheirActionOnRegions
import YangMills.Construction.Matrices.TracelessLinearComposition
import YangMills.Construction.Towers.CovariantAveragesAsDifferentialsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace ContinuationHolomorphy
variable {L m K k : ℕ}
theorem mem_tracelessPi {ι : Type} {A : ι → Matrices.ComplexMatrix2} :
    A ∈ Matrices.GroupLieProduct.tracelessPi ι ↔ ∀ a, A a ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.AsDifferentials.mem_tracelessPi_iff <;> assumption
theorem conj_mem_traceless (g : Matrices.ComplexMatrix2) {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    Matrices.ComplexMatrix2.conjugateBy g X ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.PeriodicLattice.conjugateBy_mem_traceless <;> assumption
theorem conjugateBy_add (g X Y : Matrices.ComplexMatrix2) :
    Matrices.ComplexMatrix2.conjugateBy g (X + Y) =
      Matrices.ComplexMatrix2.conjugateBy g X + Matrices.ComplexMatrix2.conjugateBy g Y := by
  simp [Matrices.ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_smul (g : Matrices.ComplexMatrix2) (z : ℂ) (X : Matrices.ComplexMatrix2) :
    Matrices.ComplexMatrix2.conjugateBy g (z • X) = z • Matrices.ComplexMatrix2.conjugateBy g X := by apply _root_.YangMills.Construction.LieInnerProductProof.conjugateBy_smul <;> assumption
section Families
variable {S : Set (Σ j : ℕ, BondAtLevel L m K j)}
theorem familyAtLevel_add (B C : PositiveBondIn S → Matrices.ComplexMatrix2) (j : ℕ) :
    familyAtLevel (B + C) j = familyAtLevel B j + familyAtLevel C j := by
  funext b
  simp only [familyAtLevel, Pi.add_apply]
  split_ifs <;> simp
theorem familyAtLevel_smul (z : ℂ) (B : PositiveBondIn S → Matrices.ComplexMatrix2) (j : ℕ) :
    familyAtLevel (z • B) j = z • familyAtLevel B j := by
  funext b
  simp only [familyAtLevel, Pi.smul_apply]
  split_ifs <;> simp
theorem familyAtLevel_mem {B : PositiveBondIn S → Matrices.ComplexMatrix2}
    (hB : ∀ q, B q ∈ Matrices.ComplexMatrix2.traceless) (j : ℕ)
    (b : BondAtLevel L m K j) : familyAtLevel B j b ∈ Matrices.ComplexMatrix2.traceless := by
  simp only [familyAtLevel]
  split_ifs
  · exact hB _
  · exact (Matrices.ComplexMatrix2.traceless).zero_mem
end Families
section Twisting
variable {j : ℤ} (σ : FourTorus L m ≃ FourTorus L m) (g : Bond L m j → Matrices.ComplexMatrix2)
theorem twistedFormValue_add (X Y : Bond L m j → Matrices.ComplexMatrix2) (b : Bond L m j) :
    twistedFormValue σ g (X + Y) b = twistedFormValue σ g X b + twistedFormValue σ g Y b := by
  simp only [twistedFormValue, Pi.add_apply]
  split_ifs
  · rfl
  · rw [conjugateBy_add, neg_add]
theorem twistedFormValue_smul (z : ℂ) (X : Bond L m j → Matrices.ComplexMatrix2) (b : Bond L m j) :
    twistedFormValue σ g (z • X) b = z • twistedFormValue σ g X b := by
  simp only [twistedFormValue, Pi.smul_apply]
  split_ifs
  · rfl
  · rw [conjugateBy_smul, smul_neg]
theorem twistedFormValue_mem {X : Bond L m j → Matrices.ComplexMatrix2}
    (hX : ∀ c, X c ∈ Matrices.ComplexMatrix2.traceless) (b : Bond L m j) :
    twistedFormValue σ g X b ∈ Matrices.ComplexMatrix2.traceless := by
  simp only [twistedFormValue]
  split_ifs
  · exact hX _
  · exact (Matrices.ComplexMatrix2.traceless).neg_mem (conj_mem_traceless _ (hX _))
end Twisting
def twistLinearMap (σ : FourTorus L m ≃ FourTorus L m) (Ω : ℕ → Set (FourTorus L m))
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    ActiveFamily L m K k Ω →ₗ[ℂ] ActiveFamily L m K k (imageChain σ Ω) where
  toFun := twistedActiveFamily σ V₀
  map_add' B C := by
    funext p
    simp only [twistedActiveFamily, familyAtLevel_add, twistedFormValue_add, Pi.add_apply]
  map_smul' z B := by
    funext p
    simp only [twistedActiveFamily, familyAtLevel_smul, twistedFormValue_smul, Pi.smul_apply,
      RingHom.id_apply]
theorem twistLinearMap_mapsTo (σ : FourTorus L m ≃ FourTorus L m) (Ω : ℕ → Set (FourTorus L m))
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    MapsTo (twistLinearMap (k := k) σ Ω V₀) (Matrices.GroupLieProduct.tracelessPi _)
      (Matrices.GroupLieProduct.tracelessPi _) := by
  intro B hB
  rw [mem_tracelessPi] at hB ⊢
  intro p
  exact twistedFormValue_mem σ _ (familyAtLevel_mem hB _) _
theorem mem_complexFamilyBall_of_eq {S T : Set (Σ j : ℕ, BondAtLevel L m K j)} (h : S = T)
    (f : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) (ρ : ℝ)
    (hS : (fun p : PositiveBondIn S => f p.1.1 p.1.2) ∈ complexFamilyBall S ρ) :
    (fun p : PositiveBondIn T => f p.1.1 p.1.2) ∈ complexFamilyBall T ρ := by
  subst h
  exact hS
theorem minimizerContinuation_spec {ε εBar rB : ℝ} {Ω : ℕ → Set (FourTorus L m)}
    {V₀ : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2}
    (h : HasUniqueMinimizerContinuation ε εBar rB K k Ω V₀) :
    IsMinimizerContinuation ε εBar rB K k Ω V₀
      (minimizerContinuation ε εBar rB K k Ω V₀) := by
  obtain ⟨Φ, hΦ, -⟩ := h
  exact Classical.epsilon_spec (p := IsMinimizerContinuation ε εBar rB K k Ω V₀) ⟨Φ, hΦ⟩
def relabelLinearMap (σ : FourTorus L m ≃ FourTorus L m) (X Y : Set (FourTorus L m))
    (h : ∀ c : (bondsInside Y : Set (BondAtLevel L m K 0)),
      bondPreimage σ c.1 ∈ (bondsInside X : Set (BondAtLevel L m K 0))) :
    (↥(bondsInside X : Set (BondAtLevel L m K 0)) → Matrices.ComplexMatrix2) →ₗ[ℂ]
      (↥(bondsInside Y : Set (BondAtLevel L m K 0)) → Matrices.ComplexMatrix2) :=
  LinearMap.funLeft ℂ Matrices.ComplexMatrix2 fun c => ⟨bondPreimage σ c.1, h c⟩
theorem holomorphic_comp_linear_right
    (hLin : Matrices.GroupLieProduct.HolomorphicLinearComp)
    {ι ι' κ : Type} [Fintype ι] [Fintype ι'] [Fintype κ] {U : Set (ι → Matrices.ComplexMatrix2)}
    {U' : Set (ι' → Matrices.ComplexMatrix2)}
    {F : (ι → Matrices.ComplexMatrix2) → κ → Matrices.ComplexMatrix2}
    (H : IsHolomorphicMatrixValued U F)
    (P : (ι' → Matrices.ComplexMatrix2) →ₗ[ℂ] (ι → Matrices.ComplexMatrix2))
    (hopen : ∀ _ : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
      Matrices.GroupLieProduct.IsSupOpen U')
    (hP : MapsTo P (Matrices.GroupLieProduct.tracelessPi ι') (Matrices.GroupLieProduct.tracelessPi ι))
    (hU : MapsTo P U' U) : IsHolomorphicMatrixValued U' fun x => F (P x) := by
  intro b ν
  exact (hLin ι κ b U F (H b)).2 ι' κ P LinearMap.id U' (hopen b) hP hU ν
theorem holomorphic_linear_comp_left
    (hLin : Matrices.GroupLieProduct.HolomorphicLinearComp)
    {ι κ κ' : Type} [Fintype ι] [Fintype κ] [Fintype κ'] {U : Set (ι → Matrices.ComplexMatrix2)}
    {F : (ι → Matrices.ComplexMatrix2) → κ → Matrices.ComplexMatrix2}
    (H : IsHolomorphicMatrixValued U F)
    (Q : (κ → Matrices.ComplexMatrix2) →ₗ[ℂ] (κ' → Matrices.ComplexMatrix2))
    (hopen : ∀ _ : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
      Matrices.GroupLieProduct.IsSupOpen U) :
    IsHolomorphicMatrixValued U fun x => Q (F x) := by
  intro b ν
  exact (hLin ι κ b U F (H b)).2 ι κ' LinearMap.id Q U (hopen b) (fun _ h => h) (fun _ h => h) ν
end ContinuationHolomorphy
open ContinuationHolomorphy in
theorem ContinuationHolomorphy.continuationsUnderIsometriesHolomorphic_holds
    (hLin : Matrices.GroupLieProduct.HolomorphicLinearComp)
    (hG : LatticeIsometryGroupActionStatement)
    (hTow : IsometriesPreserveTowersAndStepCubes)
    (hReg : IsometryCovariantRegularSetsAndAxialGauge) :
    ContinuationsUnderIsometriesHolomorphic := by
  intro L m hL hm i hi σ hσ ε εBar rB hε hεB hrB K k e r Ω hF hS V₀ h₁ h₂
  have c₁ := minimizerContinuation_spec h₁
  have c₂ := minimizerContinuation_spec h₂
  have hDet : IsDeterminingChainFrom K k i Ω := ⟨hF.2.2.1, hF.2.2.2.1, hF.2.2.2.2⟩
  have hK : 0 < K := lt_of_lt_of_le hF.2.1 hF.2.2.1
  have hSet : activeBondSet K k (imageChain σ Ω) = bondSetImage σ (activeBondSet K k Ω) :=
    ((hTow.1 L m i σ hL hm hi hσ).2.2.1 K k Ω hDet).2.1
  have hCarry := (hReg L m K hL hm hK i σ hi hσ).2.2.2.1 ε εBar rB e r k Ω V₀ hε hεB hrB hDet hS
    c₁.1.1 c₁.1.2
  have hball : ∀ B ∈ complexFamilyBall (activeBondSet K k Ω) rB,
      twistedActiveFamily σ V₀ B ∈
        complexFamilyBall (activeBondSet K k (imageChain σ Ω)) rB := by
    intro B hB
    have hmem : twistedFamily (B := activeBondSet K k Ω) σ V₀ B ∈
        complexFamilyBall (bondSetImage σ (activeBondSet K k Ω)) rB := by
      rw [hCarry]
      exact mem_image_of_mem _ hB
    exact mem_complexFamilyBall_of_eq hSet.symm
      (fun j => twistedFormValue σ (V₀ j) (familyAtLevel B j)) rB hmem
  refine ⟨?_, hball⟩
  obtain ⟨-, ⟨f₁, f₂, H₁⟩, -⟩ := c₁
  obtain ⟨-, ⟨f₃, f₄, H₂⟩, -⟩ := c₂
  have hs := (by
    obtain ⟨H, hH⟩ := (hG L m i hL hm hi).1.1
    have h1 : σ ∈ H := by
      have : σ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := by rw [hH]; exact hσ
      exact this
    have h3 : σ⁻¹ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := H.inv_mem h1
    rw [hH] at h3
    exact h3 : σ.symm ∈ latticeIsometries L m i)
  have hdep : i ≤ levelDepth K 0 := by
    obtain ⟨c, hc, hc', -⟩ := hF.2.2.2.2 0 (Nat.zero_le _)
    exact hc.trans hc'
  have hpull : ∀ c : (bondsInside (imageChain σ Ω 0) : Set (BondAtLevel L m K 0)),
      bondPreimage σ c.1 ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) := by
    rintro ⟨c, ht, hh⟩
    have hends := ((hG L m i hL hm hi).2.2.2.2 σ.symm hs (levelDepth K 0) hdep).1.2.2.2.1 c
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx, hxe⟩ := ht
      have e₁ : ((bondPreimage σ c).source : FourTorus L m) = σ.symm c.source := hends.1
      rw [e₁, ← hxe]
      simpa using hx
    · obtain ⟨x, hx, hxe⟩ := hh
      have e₂ : ((bondPreimage σ c).target : FourTorus L m) = σ.symm c.target := hends.2
      rw [e₂, ← hxe]
      simpa using hx
  have hopen : ∀ _ : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
      Matrices.GroupLieProduct.IsSupOpen (complexFamilyBall (activeBondSet K k Ω) rB) :=
    fun b => (H₁ b (Fintype.equivFin _)).1
  refine ⟨f₁, f₄, ?_, ?_⟩
  · exact holomorphic_comp_linear_right hLin H₂ (twistLinearMap σ Ω V₀) hopen
      (twistLinearMap_mapsTo σ Ω V₀) hball
  · have key := holomorphic_linear_comp_left hLin
      (F := fun (B : ActiveFamily L m K k Ω)
        (c : (bondsInside (Ω 0) : Set (BondAtLevel L m K 0))) =>
          minimizerContinuation ε εBar rB K k Ω V₀ B c) H₁
      (relabelLinearMap σ (Ω 0) (imageChain σ Ω 0) hpull) hopen
    exact key
end YangMills.Construction.PeriodicLattice
end
