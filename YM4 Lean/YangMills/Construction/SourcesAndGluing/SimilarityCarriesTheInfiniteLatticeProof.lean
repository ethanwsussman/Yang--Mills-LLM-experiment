import YangMills.Construction.SourcesAndGluing.LinksUnderLatticeSimilaritiesOfFourSpaceForm
import YangMills.Construction.SourcesAndGluing.PlaquettesUnderLatticeSimilaritiesOfFourSpaceForm
import YangMills.Construction.SourcesAndGluing.ScalingOfLatticeSimilaritiesOfFourSpaceForm
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesTheInfiniteLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.RescalingMapsInfiniteLattice
open Set YangMills.Construction.TorusLifts
open YangMills.Construction.InfiniteLattice (AmbientSpace LatticePoint Link axisStep)
variable {D : GluingSetup} (Ψ : LatticeRescaling D)
theorem eq_one_of_isSignedPermOn_one {σ : Equiv.Perm (Fin 4)} {ε : Fin 4 → ℤˣ}
    (h : IsSignedPermOn (⇑(1 : Equiv.Perm AmbientSpace)) σ ε) (μ : Fin 4) :
    σ μ = μ ∧ ε μ = 1 := by
  have h₁ := congrFun (h μ) μ
  by_cases hσ : σ μ = μ
  · refine ⟨hσ, ?_⟩
    rw [hσ] at h₁
    simp only [Equiv.Perm.coe_one, id_eq, Pi.single_eq_same, Pi.smul_apply, smul_eq_mul,
      mul_one] at h₁
    have h₂ : (((ε μ : ℤˣ) : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by simpa using h₁.symm
    have h₃ : ((ε μ : ℤˣ) : ℤ) = 1 := by exact_mod_cast h₂
    exact Units.ext (h₃.trans Units.val_one.symm)
  · simp [Pi.single_eq_of_ne (Ne.symm hσ)] at h₁
theorem isSignedPermOn_one :
    IsSignedPermOn (⇑(1 : Equiv.Perm AmbientSpace)) 1 fun _ => 1 := fun μ => by simp
theorem perm_apply (μ : Fin 4) : Ψ.toMotion.perm μ = μ := by
  obtain ⟨ε, hε⟩ : ∃ ε, IsSignedPermOn (⇑(1 : Equiv.Perm AmbientSpace))
      (axisPerm (⇑(1 : Equiv.Perm AmbientSpace))) ε :=
    Classical.epsilon_spec (p := fun σ => ∃ ε,
      IsSignedPermOn (⇑(1 : Equiv.Perm AmbientSpace)) σ ε) ⟨1, _, isSignedPermOn_one⟩
  exact (eq_one_of_isSignedPermOn_one hε μ).1
theorem signs_apply (μ : Fin 4) : Ψ.toMotion.signs μ = 1 := by
  obtain ⟨ε, hε⟩ : ∃ ε, IsSignedPermOn (⇑(1 : Equiv.Perm AmbientSpace))
      (axisPerm (⇑(1 : Equiv.Perm AmbientSpace))) ε :=
    Classical.epsilon_spec (p := fun σ => ∃ ε,
      IsSignedPermOn (⇑(1 : Equiv.Perm AmbientSpace)) σ ε) ⟨1, _, isSignedPermOn_one⟩
  have h : IsSignedPermOn (⇑(1 : Equiv.Perm AmbientSpace))
      (axisPerm (⇑(1 : Equiv.Perm AmbientSpace))) (axisSigns (⇑(1 : Equiv.Perm AmbientSpace))) :=
    Classical.epsilon_spec (p := fun ε => IsSignedPermOn (⇑(1 : Equiv.Perm AmbientSpace))
      (axisPerm (⇑(1 : Equiv.Perm AmbientSpace))) ε) ⟨ε, hε⟩
  exact (eq_one_of_isSignedPermOn_one h μ).2
theorem onLink_sub (c : Link D.mesh) :
    (((Ψ.toMotion.onLink c).terminal - (Ψ.toMotion.onLink c).initial :
        LatticePoint Ψ.scaleExponent.target.mesh) : AmbientSpace) =
      (D.L : ℝ) ^ Ψ.exp • ((c.terminal - c.initial : LatticePoint D.mesh) : AmbientSpace) := by
  rw [AddSubgroup.coe_sub, AddSubgroup.coe_sub, Ψ.onLink_terminal, Ψ.onLink_initial]
  simp only [LatticeRescaling.toSpace, smul_add, smul_sub]
  abel
theorem zpow_smul_axisStep (μ : Fin 4) :
    (D.L : ℝ) ^ Ψ.exp • ((axisStep D.mesh μ : LatticePoint D.mesh) : AmbientSpace) =
      ((axisStep Ψ.scaleExponent.target.mesh μ : LatticePoint Ψ.scaleExponent.target.mesh) :
        AmbientSpace) := by
  funext κ
  by_cases h : κ = μ
  · subst h
    simp [InfiniteLattice.axisStep, Ψ.target_mesh_eq]
  · simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne h]
theorem target_mesh_pos : 0 < Ψ.scaleExponent.target.mesh := by
  rw [Ψ.target_mesh_eq]
  exact mul_pos Ψ.zpow_L_pos D.mesh_pos
theorem axisStep_ne_neg_axisStep {a : ℝ} (ha : 0 < a) (μ ν : Fin 4) :
    ((axisStep a μ : LatticePoint a) : AmbientSpace) ≠ -((axisStep a ν : LatticePoint a) : AmbientSpace) := by
  intro h
  have h₁ := congrFun h μ
  by_cases hν : μ = ν
  · subst hν
    simp [InfiniteLattice.axisStep] at h₁
    linarith
  · simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne hν] at h₁
    linarith
theorem onLink_image_positive (hs : Function.Surjective Ψ.toMotion.onLink) :
    Ψ.toMotion.onLink '' {c | c.IsPositivelyOriented} = {c | c.IsPositivelyOriented} := by
  ext c'
  constructor
  · rintro ⟨c, ⟨μ, hμ⟩, rfl⟩
    refine ⟨μ, Subtype.ext ?_⟩
    rw [onLink_sub, hμ, zpow_smul_axisStep]
  · rintro ⟨μ, hμ⟩
    obtain ⟨c, rfl⟩ := hs c'
    refine ⟨c, ?_, rfl⟩
    obtain ⟨ν, hν | hν⟩ := c.isAdjacent
    · exact ⟨ν, hν⟩
    · exfalso
      have h₁ := onLink_sub Ψ c
      rw [hμ, hν, AddSubgroup.coe_neg, smul_neg, zpow_smul_axisStep] at h₁
      exact axisStep_ne_neg_axisStep (target_mesh_pos Ψ) μ ν h₁
theorem onPlaquette_eq (p : InfiniteLattice.ElementaryPlaquette D.mesh) :
    Ψ.toMotion.onPlaquette p =
      ⟨Ψ.toMotion.onPoint p.corner, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩ := by
  apply InfiniteLattice.ElementaryPlaquette.ext
  · apply Subtype.ext
    simp [ScaledLatticeMotion.onPlaquette, ScaledLatticeMotion.plaquetteCorner, signs_apply,
      signDefect]
  · simp [ScaledLatticeMotion.onPlaquette, perm_apply, min_eq_left p.lowAxis_lt_highAxis.le]
  · simp [ScaledLatticeMotion.onPlaquette, perm_apply, max_eq_right p.lowAxis_lt_highAxis.le]
theorem rescalingMapsInfiniteLattice (hs : ScaledMotionDilationOfSpaceClaim)
    (hl : ScaledMotionLinksOfSpaceClaim)
    (hp : ScaledMotionPlaquettesOfSpaceClaim) :
    RescalingMapsInfiniteLatticeClaim := by
  intro D Ψ
  have hsurj : Function.Surjective Ψ.toMotion.onLink :=
    (hl D Ψ.scaleExponent Ψ.toMotion).1.2
  have hplaq := hp D Ψ.scaleExponent Ψ.toMotion
  have hcenter : ∀ p : InfiniteLattice.ElementaryPlaquette D.mesh,
      Ψ.toSpace p.center = (Ψ.toMotion.onPlaquette p).center := fun p => by
    rw [hplaq.2.2.2 p, Ψ.toMotion_onSpace]
  refine ⟨?_, hsurj, onLink_image_positive Ψ hsurj, onPlaquette_eq Ψ, hcenter, ?_⟩
  · rw [← Ψ.toMotion_onSpace]
    exact (hs D Ψ.scaleExponent Ψ.toMotion).2.2.2.2
  · ext y
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨Ψ.toMotion.onPlaquette p, (hcenter p).symm⟩
    · rintro ⟨p', rfl⟩
      obtain ⟨p, rfl⟩ := hplaq.2.1.2 p'
      exact ⟨_, ⟨p, rfl⟩, hcenter p⟩
end YangMills.Construction.SourcesAndGluing.RescalingMapsInfiniteLattice
end
