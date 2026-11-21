import YangMills.Construction.Lattice.DirichletOperatorsOfASeparatedSequence
import YangMills.Construction.Lattice.KernelOfTheSiteAverageOfASequenceProof
import YangMills.Construction.Lattice.FactsOfTheFormExtensionProof
import YangMills.Construction.Lattice.SymmetryOfTheDirichletSiteOperatorsProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators YangMills.Construction.FiniteDimReal YangMills.Construction.RealInnerForms YangMills.Construction.SeparatedSequences YangMills.Construction.SeparatedSequences.BaseParameters
noncomputable section
namespace YangMills.Construction.OneFormPositivity
section
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
structure IsInnerForm (ip : V → V → ℝ) : Prop where
  symm : ∀ f g, ip f g = ip g f
  add_right : ∀ f g h, ip f (g + h) = ip f g + ip f h
  smul_right : ∀ (c : ℝ) f g, ip f (c • g) = c * ip f g
  pos : ∀ f, f ≠ 0 → 0 < ip f f
theorem IsInnerForm.apply_zero_right {ip : V → V → ℝ} (h : IsInnerForm ip) (f : V) : ip f 0 = 0 := by
  have := h.smul_right 0 f 0
  simpa using this
theorem IsInnerForm.sub_left {ip : V → V → ℝ} (h : IsInnerForm ip) (f g w : V) :
    ip (f - g) w = ip f w - ip g w := by
  rw [h.symm (f - g), h.symm f, h.symm g, sub_eq_add_neg, h.add_right, ← neg_one_smul ℝ g,
    h.smul_right]
  ring
theorem IsInnerForm.self_nonneg {ip : V → V → ℝ} (h : IsInnerForm ip) (f : V) : 0 ≤ ip f f := by
  by_cases hf : f = 0
  · rw [hf, h.apply_zero_right]
  · exact (h.pos f hf).le
theorem IsInnerForm.eq_zero_of_self {ip : V → V → ℝ} (h : IsInnerForm ip) {f : V} (hf : ip f f = 0) :
    f = 0 := by
  by_contra hne
  exact (h.pos f hne).ne' hf
theorem IsInnerForm.restrict {ip : V → V → ℝ} (h : IsInnerForm ip) (S : Submodule ℝ V) :
    IsInnerForm (fun a b : S => ip a b) where
  symm a b := h.symm _ _
  add_right a b c := h.add_right _ _ _
  smul_right r a b := h.smul_right _ _ _
  pos a ha := h.pos _ (by simpa using ha)
end
section
theorem formalAdjoint_spec {ι κ : Type} [Finite ι] [Finite κ] (L t : ℕ)
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    ∀ f g, latticeInner L t g (T f) = latticeInner L t (formalAdjoint L t T g) f := by apply _root_.YangMills.Construction.SeparatedSequences.GreenDecomposition.formalAdjoint_spec <;> assumption
variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ι : ℕ → Type} [∀ n, Finite (ι n)]
end
section
variable (D : BaseParameters) (Ω : ℕ → Set D.Torus) (φ : BondFrame)
theorem finestMesh_pos : 0 < finestMeshInLevelUnits D.L D.t := by apply _root_.YangMills.Construction.SeparatedSequences.OneExtensionProof.finestMesh_pos <;> assumption
theorem levelMeshRatio_pos (n : ℕ) : 0 < D.levelMeshRatio n := by apply _root_.YangMills.Construction.SeparatedSequences.OneExtensionProof.levelMeshRatio_pos <;> assumption
theorem finite_bareSite : Finite (BareSite D.L D.m D.K) := instFiniteLatticeSite D 0
def levelRestriction (n : ℕ) : D.CoarseOneForms Ω φ →ₗ[ℝ] (↥(D.layerBondSet Ω φ n) → ℝ) where
  toFun B c := principalBondValue B ⟨n, c.1⟩
  map_add' B B' := by
    funext c
    simp only [Pi.add_apply, principalBondValue_add]
  map_smul' r B := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, principalBondValue_smul]
theorem siteProjection_of_mem (f : ↥(zeroFormsOn D.K (Ω 0))) :
    siteProjection D.K (Ω 0) f.1 = f.1 := by apply _root_.YangMills.Construction.SeparatedSequences.DirichletSymmetry.siteProjection_coe <;> assumption
end
section
variable {S : SequenceDatum}
end
end YangMills.Construction.OneFormPositivity
end
