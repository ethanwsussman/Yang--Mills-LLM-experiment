import YangMills.Construction.Lattice.FactsOfTheFormExtensionProof
import YangMills.Construction.Lattice.LatticesAndCubesOfOrder
import YangMills.Construction.Lattice.RepresentationOfTheGaugeProjections
import YangMills.Construction.Lattice.SymmetryOfTheDirichletSiteOperators
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators FiniteDimReal RealInnerForms
  SeparatedSequences SeparatedSequences.BaseParameters
namespace GaugeProjections.Representation
section Abstract
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
structure IsRealInner (ip : V → V → ℝ) : Prop where
  add_right : ∀ f g k, ip f (g + k) = ip f g + ip f k
  smul_right : ∀ (r : ℝ) f g, ip f (r • g) = r * ip f g
  symm : ∀ f g, ip f g = ip g f
  pos : ∀ f, f ≠ 0 → 0 < ip f f
variable {ip : V → V → ℝ}
theorem IsRealInner.inner_zero_right (h : IsRealInner ip) (f : V) : ip f 0 = 0 := by
  simpa using h.smul_right 0 f 0
theorem IsRealInner.inner_sub_right (h : IsRealInner ip) (f g k : V) :
    ip f (g - k) = ip f g - ip f k := by
  have hadd := h.add_right f (g - k) k
  rw [sub_add_cancel] at hadd
  linarith
def formula (A : V →ₗ[ℝ] W) (As : W →ₗ[ℝ] V) (G : Module.End ℝ V) : Module.End ℝ V :=
  G ∘ₗ As ∘ₗ Ring.inverse (A ∘ₗ (G ^ 2) ∘ₗ As) ∘ₗ A ∘ₗ G
variable [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
structure Hypotheses (ip : V → V → ℝ) (ipW : W → W → ℝ) (A : V →ₗ[ℝ] W) (As : W →ₗ[ℝ] V)
    (T G : Module.End ℝ V) : Prop where
  inner_form : IsRealInner ip
  adj : FiniteDimReal.IsAdjointFor ip ipW A As
  comp_adj : A ∘ₗ As = LinearMap.id
  posDef : FiniteDimReal.IsPosDefFor ip T
  apply_inv : ∀ v, T (G v) = v
  inv_apply : ∀ v, G (T v) = v
variable {ipW : W → W → ℝ} {A : V →ₗ[ℝ] W} {As : W →ₗ[ℝ] V} {T G : Module.End ℝ V}
namespace Hypotheses
variable (s : Hypotheses ip ipW A As T G)
include s
end Hypotheses
end Abstract
theorem finestMesh_pos (D : BaseParameters) : 0 < finestMeshInLevelUnits D.L D.t := by apply _root_.YangMills.Construction.SeparatedSequences.OneExtensionProof.finestMesh_pos <;> assumption
section Parameters
variable (D : BaseParameters) (Ω : ℕ → Set D.Torus)
end Parameters
end GaugeProjections.Representation
end YangMills.Construction
end
