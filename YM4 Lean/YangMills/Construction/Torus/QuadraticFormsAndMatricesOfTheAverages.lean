import YangMills.Construction.Torus.FormsAveragesAndOperatorsOnAGeneralTorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.GeneralTorus
def SeparatedChain.LinksShellToNext {D : ScaleData} (B : SeparatedChain D) {n : ℕ}
    (c : D.PosBond n) : Prop :=
  ((c.1.src : D.Space) ∈ B.set n \ B.set (n + 1) ∧
      (c.1.tgt : D.Space) ∈ B.set (n + 1)) ∨
    ((c.1.tgt : D.Space) ∈ B.set n \ B.set (n + 1) ∧
      (c.1.src : D.Space) ∈ B.set (n + 1))
def IsSelfAdjointFor {V : Type*} (p : V → V → ℝ) (K : V → V) : Prop :=
  ∀ v v', p v (K v') = p (K v) v'
namespace GaugeSetting
variable (W : GaugeSetting)
def AnchorsLieOnShells : Prop :=
  (∀ c : W.CoarseBond, (coarseAnchor c = coarseSrc c ∨ coarseAnchor c = coarseTgt c) ∧
      coarseAnchor c ∈ W.chain.shellSites c.1) ∧
    ∀ y : W.data.Space, {c : W.CoarseBond | coarseAnchor c = y}.encard ≤ 2 * 4
def BaseMeansAreRestrictions : Prop :=
  (∀ (f : W.data.SiteField) (y : W.data.BaseSite),
      W.data.blockSiteMean 0 f (y : W.data.Space) = f y) ∧
    (∀ (A : W.data.BondField) (c : W.data.BaseBond), W.data.blockBondMean 0 A c = A c) ∧
    ∀ (A : ↥W.formSubspace) (c : ↥(W.coarseBondsAt 0)),
      W.meanOp A ⟨⟨0, W.data.lastLevel.succ_pos⟩, c⟩ = (A : W.data.BondField) c.1
def MassFormIsCoarseSum : Prop :=
  ∀ A : ↥W.formSubspace,
    W.formInner A (W.massPart A) = W.coarseInner (W.meanOp A) (W.massMul (W.meanOp A)) ∧
      W.coarseInner (W.meanOp A) (W.massMul (W.meanOp A)) =
        ∑ᶠ c : W.CoarseBond, W.mass * coarseSpacing c ^ 2 * |W.meanOp A c| ^ 2
def MeanFreeFieldsVanishOffFirstSet : Prop :=
  ∀ f : ↥W.chain.dirichletSites, f ∈ W.chain.siteMeansKer → ∀ x : W.data.BaseSite,
    (x : W.data.Space) ∉ W.chain.set 1 → (f : W.data.SiteField) x = 0
def LaplaciansAreSelfAdjoint : Prop :=
  IsSelfAdjointFor W.formInner ⇑W.gaugeLap ∧ IsSelfAdjointFor W.formInner ⇑W.curlLap
def QuadraticFormsOfLaplacians : Prop :=
  (∀ A : ↥W.formSubspace,
    W.formInner A (W.gaugeLap A) =
      W.data.plaquetteL2Norm (W.data.plaquetteCurl (A : W.data.BondField)) ^ 2 +
        W.data.siteL2Norm (W.chain.lapImageProj
          (W.chain.siteProj (W.data.gradAdjoint (A : W.data.BondField))) : W.data.SiteField) ^ 2 +
        W.coarseInner (W.meanOp A) (W.massMul (W.meanOp A))) ∧
    ∀ A : ↥W.formSubspace,
      W.formInner A (W.curlLap A) =
        W.data.plaquetteL2Norm (W.data.plaquetteCurl (A : W.data.BondField)) ^ 2 +
          W.coarseInner (W.meanOp A) (W.massMul (W.meanOp A))
open Classical in
def CoarseUnitsAreOrthonormalBasis : Prop :=
  (∀ c c' : W.CoarseBond,
      W.coarseInner (W.coarseUnit c) (W.coarseUnit c') = if c = c' then 1 else 0) ∧
    Submodule.span ℝ (range W.coarseUnit) = ⊤
open Classical in
def MatrixEntriesCompose : Prop :=
  (∀ (K : Module.End ℝ W.CoarseField) (c c' : W.CoarseBond),
      W.kernelEntry K c c' = (coarseSpacing c' / coarseSpacing c) ^ 2 * W.matrixEntry K c c') ∧
    (∀ (K K' : Module.End ℝ W.CoarseField) (c c'' : W.CoarseBond),
      W.matrixEntry (K ∘ₗ K') c c'' =
        ∑ᶠ c' : W.CoarseBond, W.matrixEntry K c c' * W.matrixEntry K' c' c'') ∧
    (∀ K : Module.End ℝ W.CoarseField, IsSelfAdjointFor W.coarseInner ⇑K →
      ∀ c c' : W.CoarseBond, W.matrixEntry K c c' = W.matrixEntry K c' c) ∧
    ∀ (f : W.CoarseField) (c c' : W.CoarseBond),
      W.matrixEntry (LinearMap.mulLeft ℝ f) c c' = if c = c' then f c else 0
def ShellLinksCarryUnitGradients : Prop :=
  ∀ n : ℕ, n < W.data.lastLevel → ∀ c : W.data.PosBond n, W.chain.LinksShellToNext c →
    (∀ c' : W.CoarseBond, ¬(coarseSrc c' = (c.1.src : W.data.Space) ∧
        coarseTgt c' = (c.1.tgt : W.data.Space))) ∧
      ∃ f : ↥W.chain.dirichletSites, f ∈ W.chain.siteMeansKer ∧
        |W.data.blockBondMean n (W.data.grad (f : W.data.SiteField)) c| =
          (W.data.levelSpacing n)⁻¹
end GaugeSetting
def CoarseBondFormsAndMatricesHold : Prop :=
  ∀ W : GaugeSetting,
    W.AnchorsLieOnShells ∧ W.BaseMeansAreRestrictions ∧ W.MassFormIsCoarseSum ∧
      W.MeanFreeFieldsVanishOffFirstSet ∧ W.LaplaciansAreSelfAdjoint ∧
      W.QuadraticFormsOfLaplacians ∧ W.CoarseUnitsAreOrthonormalBasis ∧
      W.MatrixEntriesCompose ∧ W.ShellLinksCarryUnitGradients
end YangMills.Construction.GeneralTorus
