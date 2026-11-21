import YangMills.Construction.Torus.FormsAveragesAndOperatorsOnAGeneralTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus
namespace GaugeSetting
variable (W : GaugeSetting)
def GradOfMeansKerFacts : Prop :=
  ∀ l : ↥W.chain.dirichletSites, l ∈ W.chain.siteMeansKer →
    ∃ h : W.data.grad (l : W.data.SiteField) ∈ W.formSubspace,
      W.data.plaquetteCurl (W.data.grad (l : W.data.SiteField)) = 0 ∧
      W.meanOp ⟨W.data.grad (l : W.data.SiteField), h⟩ = 0 ∧
      W.chain.siteProj
          (W.data.gradAdjoint (W.data.grad (l : W.data.SiteField))) =
        W.chain.dirichletLap l ∧
      W.greenOp (W.formProj
          (W.data.grad (W.chain.dirichletLap l : W.data.SiteField))) =
        ⟨W.data.grad (l : W.data.SiteField), h⟩
def gradLapProj : ↥W.chain.dirichletSites →ₗ[ℝ] ↥W.formSubspace :=
  W.formProj ∘ₗ W.data.grad ∘ₗ W.chain.dirichletSites.subtype ∘ₗ W.chain.lapImageProj
def lapProjDiv : ↥W.formSubspace →ₗ[ℝ] ↥W.chain.dirichletSites :=
  W.chain.lapImageProj ∘ₗ W.chain.siteProj ∘ₗ W.data.gradAdjoint ∘ₗ W.formSubspace.subtype
def GreenProjIdentities : Prop :=
  W.meanOp ∘ₗ W.greenOp ∘ₗ W.gradLapProj = 0 ∧
    W.lapProjDiv ∘ₗ W.greenOp ∘ₗ W.meanOpAdjoint = 0 ∧
    W.lapProjDiv ∘ₗ W.greenOp ∘ₗ W.gradLapProj = W.chain.lapImageProj
def CoarseGreenPosDef : Prop :=
  (∀ f f' : W.CoarseField,
    W.coarseInner (W.coarseGreen f) f' = W.coarseInner f (W.coarseGreen f')) ∧
  ∀ f : W.CoarseField, f ≠ 0 → 0 < W.coarseInner f (W.coarseGreen f)
def MinFormsWithMeans (f : W.CoarseField) : Prop :=
  IsLeast {r : ℝ | ∃ A : ↥W.formSubspace, W.meanOp A = f ∧ r = W.formInner A (W.gaugeLap A)}
      (W.coarseInner f (Ring.inverse W.coarseGreen f)) ∧
    IsLeast {r : ℝ | ∃ A : ↥W.formSubspace, W.meanOp A = f ∧
        r = W.data.plaquetteL2Norm (W.data.plaquetteCurl (A : W.data.BondField)) ^ 2}
      (W.coarseInner f (W.coarseLap f)) ∧
    W.coarseInner f (W.coarseLap f) =
      W.data.plaquetteL2Norm (W.data.plaquetteCurl (W.harmonicExt f : W.data.BondField)) ^ 2
end GaugeSetting
def GreenIdentitiesAndBlockFormHold : Prop :=
  ∀ W : GaugeSetting, W.data.L ≤ W.data.blockCount →
    W.GradOfMeansKerFacts ∧
    W.GreenProjIdentities ∧
    W.curlLap ∘ₗ W.greenOp ∘ₗ W.meanOpAdjoint = W.meanOpAdjoint ∧
    W.CoarseGreenPosDef ∧
    ∀ f : W.CoarseField, W.MinFormsWithMeans f
end YangMills.Construction.GeneralTorus
end
