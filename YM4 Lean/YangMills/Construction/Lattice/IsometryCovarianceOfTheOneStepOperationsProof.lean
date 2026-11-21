import YangMills.Construction.Lattice.BondOrientationDichotomy
import YangMills.Construction.Lattice.EliminationFactorAtAnImageBond
import YangMills.Construction.Lattice.IsometryCovarianceOfTheOneStepOperations
import YangMills.Construction.Lattice.OneStepIdentitiesAtAnImageBond
import YangMills.Construction.Lattice.OneStepOperationsOfAnImageSet
import YangMills.Construction.Lattice.RealConstraintAtAnImageBond
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction.PeriodicLattice
theorem exists_isOrientedImage_of_dichotomy (hOr : BondOrientationDichotomy) {L m K k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hk : k < K)
    (σ : FourTorus L m ≃ FourTorus L m) (c : BondAtLevel L m K (k + 1)) :
    ∃ c', IsOrientedImage σ c c' := by
  have hlev : -(m : ℤ) < levelDepth K (k + 1) := by
    unfold levelDepth
    omega
  rcases hOr L m hL hm _ hlev (bondImage σ c) with h | h
  · exact ⟨_, h.1, Or.inl rfl⟩
  · exact ⟨_, h.1, Or.inr rfl⟩
theorem twistedTransportForm_of_isPositivelyOriented {L m : ℕ} {j : ℤ}
    (σ : FourTorus L m ≃ FourTorus L m) (W A : Bond L m j → Matrices.ComplexMatrix2)
    {b : Bond L m j} (hb : b.IsPositivelyOriented) :
    twistedTransportForm σ W A b = twistedFormValue σ W A b := by
  simp only [twistedTransportForm, hb, ↓reduceIte]
theorem isometryCovarianceOneStep_of
    (hOr : BondOrientationDichotomy)
    (hId : TransportIdentitiesAtImageBond)
    (hEl : EliminationWeightAtImageBond)
    (hSet : ImageSetIntertwining.Statement)
    (hRe : RealConstraintAtImageStatement) :
    IsometryCovarianceOneStep := by
  intro L m K k i σ hL hm hi hσ hk hik V Γ hf
  have hreal : ∀ c ∈ Γ, ∀ c', IsOrientedImage σ c c' → RealConstraintAtImage σ V c c' :=
    fun c hc c' hp => hRe L m K k i σ hL hm hi hσ hk hik V c c' (hf.positive c hc) hp.1 hp.2
      (hf.real_defined c hc).1 (hf.real_defined c hc).2 (hf.complex_defined c hc)
  have hids : ∀ c ∈ Γ, ∀ c', IsOrientedImage σ c c' →
      TransportIdentitiesAt σ V (blockAverage (Averaging.smoothingRadius L) V) c c' :=
    fun c hc c' hp => hId L m K k i σ hL hm hi hσ hk hik V _ c c' (hf.positive c hc) hp.1 hp.2
      (hf.complex_defined c hc) (hreal c hc c' hp).mem_complexDomain
      (hreal c hc c' hp).blockAverage_eq
  have hdef : LinearizedObjectsDefined (Averaging.smoothingRadius L) (transportGaugeField σ V)
      (orientedImage σ Γ) :=
    { positive := fun c' ⟨_, _, hp⟩ => hp.1
      real_defined := fun c' ⟨c, hc, hp⟩ =>
        ⟨(hreal c hc c' hp).regular_near_image,
          (hreal c hc c' hp).differentiableAt_logRatioCurve⟩
      complex_defined := fun c' ⟨c, hc, hp⟩ => (hreal c hc c' hp).mem_complexDomain
      pivotCoeff_invertible := fun c' ⟨c, hc, hp⟩ =>
        (hids c hc c' hp).invertible_iff.1 (hf.pivotCoeff_invertible c hc) }
  have hmem : ∀ c', c' ∈ orientedImage σ Γ ↔ ∃ c ∈ Γ, c'.IsPositivelyOriented ∧
      (c' = bondImage σ c ∨ c' = (bondImage σ c).opposite) := fun _ => Iff.rfl
  have hW : ∀ c ∈ Γ, blockAverage (Averaging.smoothingRadius L) V c = complexBlockAverage V c :=
    fun c hc => (hreal c hc _
      (exists_isOrientedImage_of_dichotomy hOr hL hm hk σ c).choose_spec).blockAverage_eq
  have hcomm : IsometryIntertwinesStepMaps σ V (blockAverage (Averaging.smoothingRadius L) V) Γ
      (orientedImage σ Γ) :=
    hSet L m K k i σ hL hm hi hσ hk hik V _ Γ _ hf.positive hmem hf.complex_defined
      hf.pivotCoeff_invertible hdef.complex_defined hdef.pivotCoeff_invertible hW
  exact
    { defined := hdef
      linearized_comm := fun A hA c' ⟨c, hc, hp⟩ => by
        rw [twistedTransportForm_of_isPositivelyOriented _ _ _ hp.1]
        exact (hids c hc c' hp).linearized A hA
      linearizedReal_comm := fun A hA c' ⟨c, hc, hp⟩ => by
        rw [twistedTransportForm_of_isPositivelyOriented _ _ _ hp.1]
        exact (hreal c hc c' hp).linearizedConstraint_eq A hA
      constraintMap_comm := fun F hF c hc c' hp h₁ h₂ =>
        (hids c hc c' hp).constraint_map F hF h₁ h₂
      constraintMap_defined_iff := fun F hF c hc c' hp =>
        (hreal c hc c' hp).constraintMapDefined_iff F hF
      eliminate_comm := hcomm.eliminate_comm
      pivotCorrectionLift_comm := hcomm.pivotLift_comm
      linearizingCorrection_comm := hcomm.correction_comm
      linearizingChange_comm := hcomm.change_comm
      pivotCoeff_conj := fun c hc c' hp X => (hids c hc c' hp).pivotCoeff_conj X
      eliminationWeight_eq := fun c hc c' hp =>
        hEl L m K k i σ hL hm hi hσ hk hik V c c' (hf.positive c hc) hp.1 hp.2
          (hf.complex_defined c hc) (hreal c hc c' hp).mem_complexDomain
      constraintBilinear_comm := fun F₁ F₂ h₁ h₂ c' ⟨c, hc, hp⟩ =>
        (hids c hc c' hp).bilinear F₁ F₂ h₁ h₂ }
end YangMills.Construction.PeriodicLattice
