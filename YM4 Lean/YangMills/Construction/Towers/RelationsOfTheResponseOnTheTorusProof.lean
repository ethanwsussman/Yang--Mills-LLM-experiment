import YangMills.Construction.Towers.ImagesUnderTheResponseReadAtTheSideInfinity
import YangMills.Construction.Towers.PeriodicRestrictionDeterminesAForm
import YangMills.Construction.Towers.PropertiesOfTheResponse
import YangMills.Construction.Towers.RelationsOfTheResponseOnTheTorus
import YangMills.Construction.Towers.TheCrossingAverageReadAtTheSideInfinity
import YangMills.Construction.Towers.TheDifferencesOfFormsReadAtTheSideInfinity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.TorusResponseRelations
open YangMills.Construction.PeriodicOperators (ApplySummableAt RowFinite KernelMatrix colourEdges idKernel
  applyKernel compKernel)
open YangMills.Construction.Tower.PeriodicForm (coeffsOnEdges)
open YangMills.Construction.Tower.CriticalBranchResponse
open YangMills.Construction.Tower.FreeResolvents (trivialRescaledOperators)
theorem applyKernel_compKernel {X Y Z : Type} (T : KernelMatrix Y Z) (S : KernelMatrix X Y)
    (hT : RowFinite T) (f : X → ℂ) (hS : ∀ y, ApplySummableAt S f y) :
    applyKernel (compKernel T S) f = applyKernel T (applyKernel S f) := by
  classical
  funext z
  have hfin := hT z
  set F := hfin.toFinset with hFdef
  have hvanish : ∀ y, y ∉ F → T z y = 0 := by
    intro y hy
    by_contra hne
    exact hy (by simpa [hFdef] using hne)
  have hrow : ∀ g : Y → ℂ, ∑' y, T z y * g y = ∑ y ∈ F, T z y * g y := by
    intro g
    exact tsum_eq_sum fun y hy => by simp [hvanish y hy]
  have hsumm : ∀ y, Summable fun x => S y x * f x := fun y => (hS y).of_norm
  unfold applyKernel compKernel
  simp only [hrow]
  simp only [Finset.sum_mul, mul_assoc]
  rw [Summable.tsum_finsetSum fun y _ => (hsumm y).mul_left _]
  exact Finset.sum_congr rfl fun y _ => tsum_mul_left
theorem applyKernel_idKernel (I : PeriodicOperators.PeriodicData) (f : I.Carrier → ℂ) :
    applyKernel (idKernel I) f = f := by
  classical
  funext x
  unfold applyKernel
  rw [tsum_eq_single x]
  · simp [idKernel]
  · intro y hy
    simp [idKernel, Ne.symm hy]
theorem holds (hProps : ResponseProperties.AllProperties) (hDet : PeriodicCoeffsDetermineForm.Statement)
    (hImg : ResponseImagesFullSide.ResponseImagesHold)
    (hCross : CrossingSmoothingAtInfinity.Claim)
    (hCob : FormCoboundariesAtInfinity.Claim) : TorusResponseRelations.statement := by
  intro L hL k hk n hn B
  have hTop := hDet L hL k n k hn le_rfl
  have hBot := hDet L hL k n 0 hn (Nat.zero_le k)
  have im := hImg L hL k hk n hn B
  have cr := hCross L hL k hk n hn
  have df := hCob L hL k hk n hn
  have rel := hProps.1 L hL k hk
  have qh : applyKernel (trivialRescaledOperators L k).Q
      (applyKernel (BackgroundFieldResponse.responseKernel L k) (coeffsOnEdges L n k k B)) =
      coeffsOnEdges L n k k B :=
    (applyKernel_compKernel (trivialRescaledOperators L k).Q (BackgroundFieldResponse.responseKernel L k)
      cr.Q_rowFinite _ im.resp_summable).symm.trans
      ((congrArg (fun K => applyKernel K (coeffsOnEdges L n k k B)) rel.smoothing_comp).trans
        (applyKernel_idKernel _ _))
  have dh : applyKernel (ResponseProperties.coboundaryLaplacian L k)
      (applyKernel (BackgroundFieldResponse.responseKernel L k) (coeffsOnEdges L n k k B)) =
      applyKernel (trivialRescaledOperators L k).Qt (coeffsOnEdges L n k k (periodicDefect L n k B)) := by
    have e₁ := applyKernel_compKernel (ResponseProperties.coboundaryLaplacian L k)
      (BackgroundFieldResponse.responseKernel L k) df.laplacian_rowFinite _ im.resp_summable
    have e₂ := applyKernel_compKernel (trivialRescaledOperators L k).Qt
      (BackgroundFieldResponse.responseDefect L k) cr.Qt_rowFinite _ im.defect_summable
    have e₃ := congrArg (fun K => applyKernel K (coeffsOnEdges L n k k B)) rel.laplacian_comp
    exact e₁.symm.trans (e₃.trans (e₂.trans
      (congrArg (applyKernel (trivialRescaledOperators L k).Qt) im.defect_coeffs.symm)))
  have dν : applyKernel (PlaneWaveCalculus.vertexCoboundaryT L k k)
      (applyKernel (BackgroundFieldResponse.responseDefect L k) (coeffsOnEdges L n k k B)) = 0 := by
    have e₁ := applyKernel_compKernel (PlaneWaveCalculus.vertexCoboundaryT L k k)
      (BackgroundFieldResponse.responseDefect L k) df.divergence_rowFinite _ im.defect_summable
    have e₂ := congrArg (fun K => applyKernel K (coeffsOnEdges L n k k B)) rel.defect_divergence
    refine e₁.symm.trans (e₂.trans ?_)
    funext x
    simp [applyKernel]
  have smoothing : crossingSmoothingToTop L n k (meshScaledResponse L n k B) = B := by
    apply hTop.1
    unfold meshScaledResponse
    rw [map_smul, hTop.2, cr.coeffs_smoothing, im.resp_coeffs]
    exact qh
  refine ⟨im.resp_isImage, im.defect_isImage, ?_, ?_, ?_⟩
  · rw [← cr.coe_eq_iter, smoothing]
  · apply hBot.1
    unfold meshScaledResponse
    rw [map_smul, map_smul, hBot.2, df.evaluation_laplacian, im.resp_coeffs, cr.coeffs_transpose]
    refine (congrArg (fun x => (finestMesh L k : ℂ) • ((finestMesh L k : ℂ) ^ 2) • x) dh).trans ?_
    refine (smul_smul _ _ _).trans ?_
    congr 1
    ring
  · refine df.pairing_coboundary_eq_zero (periodicDefect L n k B) ?_
    rw [im.defect_coeffs]
    exact dν
end YangMills.Construction.Tower.TorusResponseRelations
end
