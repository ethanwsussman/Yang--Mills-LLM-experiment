import YangMills.Construction.SourcesAndGluing.CompositeOfLatticeSimilarities
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusLifts TorusMetric
namespace SourcesAndGluing
open InfiniteLattice (AmbientSpace)
namespace CompositionOfScaledMotions
theorem map_smul_of_mem_hyperoctahedral {S : Equiv.Perm AmbientSpace}
    (hS : S ∈ hyperoctahedralGroupEuclidean) (c : ℝ) (x : AmbientSpace) : S (c • x) = c • S x := by
  obtain ⟨σ, ε, rfl⟩ := hS
  funext μ
  change ((ε μ : ℤ) : ℝ) * (c * x (σ μ)) = c * (((ε μ : ℤ) : ℝ) * x (σ μ))
  ring
theorem scaledMotion_scaledMotion {L : ℕ} (hL : 0 < L) {b b₂ : ℤ} {S S₂ : Equiv.Perm AmbientSpace}
    (hS₂ : S₂ ∈ hyperoctahedralGroupEuclidean) (w w₂ x : AmbientSpace) :
    scaledMotion L b₂ S₂ w₂ (scaledMotion L b S w x) =
      scaledMotion L (b + b₂) (S₂ * S : Equiv.Perm AmbientSpace) (scaledMotion L b₂ S₂ w₂ w) x := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  simp only [scaledMotion, Equiv.Perm.mul_apply, map_add_of_mem_hyperoctahedral hS₂,
    map_smul_of_mem_hyperoctahedral hS₂, smul_add, smul_smul, zpow_add₀ hL']
  rw [mul_comm ((L : ℝ) ^ b₂), add_assoc]
theorem transport_torusProj {X X' : GluingSetup} (h : X = X') (y : AmbientSpace) :
    transport (F := fun Y : GluingSetup => Y.Torus) h
        (torusProj (PeriodicLattice.torusSide X.L (X.m : ℕ)) y) =
      torusProj (PeriodicLattice.torusSide X'.L (X'.m : ℕ)) y := by
  subst h
  rfl
variable {G : GluingSetup} {e : ScaleExponent G} {e₂ : ScaleExponent e.target}
def compose (Φ : ScaledLatticeMotion e) (Ψ : ScaledLatticeMotion e₂) :
    ScaledLatticeMotion (e.add e₂) where
  rotation := Ψ.rotation * Φ.rotation
  rotation_mem := mul_mem Ψ.rotation_mem Φ.rotation_mem
  offset := Ψ.onSpace Φ.offset
  offset_mem := by
    rw [← e.target_add e₂]
    exact (Ψ.onPoint ⟨Φ.offset, Φ.offset_mem⟩).2
theorem onSpace_compose (Φ : ScaledLatticeMotion e) (Ψ : ScaledLatticeMotion e₂) :
    (compose Φ Ψ).onSpace = Ψ.onSpace ∘ Φ.onSpace := by
  funext x
  exact (scaledMotion_scaledMotion ScaleExponent.L_pos Ψ.rotation_mem
    Φ.offset Ψ.offset x).symm
theorem onTorus_compose (Φ : ScaledLatticeMotion e) (Ψ : ScaledLatticeMotion e₂) :
    (compose Φ Ψ).onTorus = Φ.torusComp Ψ := by
  funext u
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
  have h₂ : Ψ.onTorus (Φ.onTorus (torusProj (PeriodicLattice.torusSide G.L (G.m : ℕ)) x)) =
      torusProj (PeriodicLattice.torusSide e₂.target.L (e₂.target.m : ℕ))
        (Ψ.onSpace (Φ.onSpace x)) := by
    rw [Φ.onTorus_torusProj]
    exact Ψ.onTorus_torusProj _
  rw [ScaledLatticeMotion.onTorus_torusProj, onSpace_compose, ScaledLatticeMotion.torusComp, h₂,
    transport_torusProj]
  rfl
theorem proof : CompositionOfScaledMotions.Statement := by
  intro G e Φ e₂ Ψ
  exact ⟨⟨compose Φ Ψ, rfl, onSpace_compose Φ Ψ⟩,
    ⟨compose Φ Ψ, rfl, onTorus_compose Φ Ψ⟩⟩
end CompositionOfScaledMotions
end SourcesAndGluing
end YangMills.Construction
end
