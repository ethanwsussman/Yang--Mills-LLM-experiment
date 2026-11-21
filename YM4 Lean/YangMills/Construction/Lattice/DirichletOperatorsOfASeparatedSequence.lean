import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators
noncomputable section
namespace YangMills.Construction
namespace RealInnerForms
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
def IsOrthogonalProjectionFor (ip : V → V → ℝ) (W : Submodule ℝ V) (P : V →ₗ[ℝ] V) : Prop :=
  ∀ f, P f ∈ W ∧ ∀ w ∈ W, ip (f - P f) w = 0
def orthProjectionFor (ip : V → V → ℝ) (W : Submodule ℝ V) : V →ₗ[ℝ] V :=
  Classical.epsilon (IsOrthogonalProjectionFor ip W)
end RealInnerForms
namespace SeparatedSequences.BaseParameters
variable (D : BaseParameters) (Ω : ℕ → Set D.Torus) (φ : BondFrame)
def massiveZeroOperator : Module.End ℝ ↥(zeroFormsOn D.K (Ω 0)) :=
  dirichletLaplacian D.K D.t (Ω 0) + D.weightedAverageZero Ω
def zeroGreen : Module.End ℝ ↥(zeroFormsOn D.K (Ω 0)) := Ring.inverse (D.massiveZeroOperator Ω)
def averageZeroKernel : Submodule ℝ ↥(zeroFormsOn D.K (Ω 0)) := LinearMap.ker (D.averageZero Ω)
def laplacianImageOfAverageZeroKernel : Submodule ℝ ↥(zeroFormsOn D.K (Ω 0)) :=
  (D.averageZeroKernel Ω).map (dirichletLaplacian D.K D.t (Ω 0))
def gaugeRangeProjection : Module.End ℝ ↥(zeroFormsOn D.K (Ω 0)) :=
  RealInnerForms.orthProjectionFor (D.restrictedZeroInner Ω)
    (D.laplacianImageOfAverageZeroKernel Ω)
def gaugeComplementProjection : Module.End ℝ ↥(zeroFormsOn D.K (Ω 0)) :=
  1 - D.gaugeRangeProjection Ω
def averagedZeroGreenSq : Module.End ℝ (D.CoarseZeroForms Ω) :=
  D.averageZero Ω ∘ₗ (D.zeroGreen Ω ^ 2) ∘ₗ D.averageZeroAdjoint Ω
def constrainedZeroGreen : Module.End ℝ ↥(zeroFormsOn D.K (Ω 0)) :=
  D.zeroGreen Ω ^ 2 -
    (D.zeroGreen Ω ^ 2) ∘ₗ D.averageZeroAdjoint Ω ∘ₗ Ring.inverse (D.averagedZeroGreenSq Ω) ∘ₗ
      D.averageZero Ω ∘ₗ (D.zeroGreen Ω ^ 2)
def gaugeFixingTerm : Module.End ℝ ↥(oneFormsOn D.K (Ω 0) φ) :=
  dirichletGrad D.K D.t (Ω 0) φ ∘ₗ D.gaugeRangeProjection Ω ∘ₗ
    dirichletGradAdjoint D.K D.t (Ω 0) φ
def massiveOneOperator : Module.End ℝ ↥(oneFormsOn D.K (Ω 0) φ) :=
  dirichletCurlCurl D.K D.t (Ω 0) φ + D.gaugeFixingTerm Ω φ + D.weightedAverageOne Ω φ
def oneGreen : Module.End ℝ ↥(oneFormsOn D.K (Ω 0) φ) := Ring.inverse (D.massiveOneOperator Ω φ)
def averagedOneGreen : Module.End ℝ (D.CoarseOneForms Ω φ) :=
  D.averageOne Ω φ ∘ₗ D.oneGreen Ω φ ∘ₗ D.averageOneAdjoint Ω φ
def oneExtension : D.CoarseOneForms Ω φ →ₗ[ℝ] ↥(oneFormsOn D.K (Ω 0) φ) :=
  D.oneGreen Ω φ ∘ₗ D.averageOneAdjoint Ω φ ∘ₗ Ring.inverse (D.averagedOneGreen Ω φ)
def oneProjection : Module.End ℝ ↥(oneFormsOn D.K (Ω 0) φ) :=
  1 - D.oneGreen Ω φ ∘ₗ D.gaugeFixingTerm Ω φ -
    D.oneExtension Ω φ ∘ₗ D.averageOne Ω φ
def constrainedOneForms : Submodule ℝ ↥(oneFormsOn D.K (Ω 0) φ) :=
  LinearMap.ker (D.averageOne Ω φ) ⊓
    LinearMap.ker (D.gaugeRangeProjection Ω ∘ₗ dirichletGradAdjoint D.K D.t (Ω 0) φ)
def coarseZeroSupported : Submodule ℝ (D.CoarseZeroForms (D.withWholeTorus Ω)) where
  carrier := {ω | ∀ y, y.1 ∉ D.allLayerPoints Ω → ω y = 0}
  add_mem' := fun hω hω' y hy => by simp [hω y hy, hω' y hy]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c _ hω y hy => by simp [hω y hy]
def coarseOneSupported : Submodule ℝ (D.CoarseOneForms (D.withWholeTorus Ω) φ) where
  carrier := {B | ∀ c, c.1 ∉ D.principalBonds Ω φ → B c = 0}
  add_mem' := fun hB hB' c hc => by simp [hB c hc, hB' c hc]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun r _ hB c hc => by simp [hB c hc]
variable {D Ω φ} in
theorem principalBondValue_add (B B' : D.CoarseOneForms Ω φ) (c : Σ n : ℕ, D.LevelBond n) :
    principalBondValue (B + B') c = principalBondValue B c + principalBondValue B' c := by
  simp only [principalBondValue]
  split_ifs <;> simp
variable {D Ω φ} in
theorem principalBondValue_smul (r : ℝ) (B : D.CoarseOneForms Ω φ)
    (c : Σ n : ℕ, D.LevelBond n) : principalBondValue (r • B) c = r * principalBondValue B c := by
  simp only [principalBondValue]
  split_ifs <;> simp
def coarseZeroSupportProjection : Module.End ℝ (D.CoarseZeroForms (D.withWholeTorus Ω)) :=
  RealInnerForms.orthProjectionFor (D.coarseZeroInner (D.withWholeTorus Ω))
    (D.coarseZeroSupported Ω)
def coarseOneSupportProjection : Module.End ℝ (D.CoarseOneForms (D.withWholeTorus Ω) φ) :=
  RealInnerForms.orthProjectionFor (D.coarseOneInner (D.withWholeTorus Ω) φ)
    (D.coarseOneSupported Ω φ)
end SeparatedSequences.BaseParameters
end YangMills.Construction
end
