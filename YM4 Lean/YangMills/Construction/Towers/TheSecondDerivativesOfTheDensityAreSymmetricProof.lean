import YangMills.Construction.Towers.SecondDerivativesOfTheLogarithmicDensity
import YangMills.Construction.Towers.TheAbelianOperatorsGiveLocalSettingsProof
import YangMills.Construction.Towers.TheSecondDerivativesOfTheDensityAreSymmetric
import Mathlib
set_option autoImplicit false
open Filter Topology YangMills.Construction.OperatorCalculus YangMills.Construction.OneLoopNotation
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.LocalFamilies
open YangMills.Construction.Tower.AbelianFieldFacts
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity.SecondDerivativeSymmetry
theorem deriv_deriv_comp_eq_fderiv_fderiv {g : ℝ × ℝ → ℂ} (hg : ContDiffAt ℝ 2 g 0) (u v : ℝ × ℝ) :
    deriv (fun a : ℝ => deriv (fun w : ℝ => g (a • u + w • v)) 0) 0 =
      fderiv ℝ (fderiv ℝ g) 0 u v := by
  have hdiff : ∀ᶠ y in 𝓝 (0 : ℝ × ℝ), HasFDerivAt g (fderiv ℝ g y) y := by
    filter_upwards [hg.eventually (by simp)] with y hy
    exact (hy.differentiableAt (by simp)).hasFDerivAt
  have hD : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) 0) 0 :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt
  have hlim : Tendsto (fun a : ℝ => a • u) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun a : ℝ => a • u) := by fun_prop
    simpa using hcont.tendsto 0
  have heq : (fun a : ℝ => deriv (fun w : ℝ => g (a • u + w • v)) 0) =ᶠ[𝓝 0]
      fun a => fderiv ℝ g (a • u) v := by
    filter_upwards [hlim.eventually hdiff] with a ha
    have hline : HasDerivAt (fun w : ℝ => a • u + w • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (a • u)
    have ha' : HasFDerivAt g (fderiv ℝ g (a • u)) (a • u + (0 : ℝ) • v) := by simpa using ha
    exact (ha'.comp_hasDerivAt (0 : ℝ) hline).deriv
  rw [heq.deriv_eq]
  have hline : HasDerivAt (fun a : ℝ => a • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  have hat : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) 0) ((0 : ℝ) • u) := by simpa using hD
  have hcomp := hat.comp_hasDerivAt (0 : ℝ) hline
  have happ := hcomp.clm_apply (hasDerivAt_const (0 : ℝ) v)
  simpa using happ.deriv
theorem deriv_deriv_swap_of_contDiffAt {g : ℝ × ℝ → ℂ} (hg : ContDiffAt ℝ 2 g 0) :
    deriv (fun a : ℝ => deriv (fun w : ℝ => g (a, w)) 0) 0 =
      deriv (fun w : ℝ => deriv (fun a : ℝ => g (a, w)) 0) 0 := by
  have hsymm : IsSymmSndFDerivAt ℝ g 0 := hg.isSymmSndFDerivAt (by simp)
  have hfirst := deriv_deriv_comp_eq_fderiv_fderiv hg (1, 0) (0, 1)
  have hsecond := deriv_deriv_comp_eq_fderiv_fderiv hg (0, 1) (1, 0)
  simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, Prod.mk_add_mk, add_zero, zero_add]
    at hfirst hsecond
  rw [hfirst, hsecond]
  exact hsymm _ _
theorem isBoundedBelowBy_addScalar {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {A : BddOp E} {c w c' : ℝ} (hA : IsBoundedBelowBy A c) (hle : c' ≤ c + w) :
    IsBoundedBelowBy (addScalar A w) c' := by apply _root_.YangMills.Construction.Tower.LocalFamilies.AbelianLocalExpansion.isBoundedBelowBy_addScalar <;> assumption
variable {L : ℕ}
theorem massiveOp_addScalar_bounded_near_zero
    (hlow : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, SpectralLowerBounds θ)
    {w : ℝ} (hw : 0 < w) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, (∀ e, |θ e| ≤ ρ) →
      IsBoundedBelowBy (addScalar (AbelianFieldDensity.massiveOp θ) w) (w / 2) := by apply _root_.YangMills.Construction.Tower.LocalFamilies.AbelianLocalExpansion.massiveOp_add_boundedBelow <;> assumption
theorem laplacianOp_addScalar_bounded
    (hlow : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, SpectralLowerBounds θ)
    {w : ℝ} (hw : 0 < w) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, (∀ e, |θ e| ≤ ρ) →
      IsBoundedBelowBy (addScalar (laplacianOp θ) w) (w / 2) :=
  ⟨1, one_pos, fun θ _ => isBoundedBelowBy_addScalar (hlow θ).2 (by linarith)⟩
theorem secondDerivativeSymm_holds (hFormula : LogTraceSecondDerivative.IntegralFormula)
    (hSmooth : AbelianOperatorsLocallySmooth)
    (hIndexed : UnitLatticeIndexedSpaces)
    (hFacts : AbelianFieldFacts.AllFacts) :
    AbelianFieldDensity.SecondDerivativeSymm := by
  intro w hw L hL x e e'
  obtain ⟨C, hC, hloc⟩ := hSmooth
  obtain ⟨hvert, hedge⟩ := hloc L hL
  obtain ⟨isV, isE, initials⟩ := hIndexed L hL w C hw hC
  have hlow : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, SpectralLowerBounds θ := fun θ =>
    ((hFacts.2.2 L hL w hw).2.2.2 θ).2.2.2.2.2.1
  have setV : IsLocalExpansionSetting (vertexPos L) (positiveEdgeInitial (L := L)) 3 4 w C
      (laplacianOp (L := L)) := ⟨isV, initials, hvert, laplacianOp_addScalar_bounded hlow hw⟩
  have setE : IsLocalExpansionSetting (edgePos L) (positiveEdgeInitial (L := L)) 12 4 w C
      (AbelianFieldDensity.massiveOp (L := L)) :=
    ⟨isE, initials, hedge, massiveOp_addScalar_bounded_near_zero hlow hw⟩
  obtain ⟨k, hk⟩ := isV.placement.on_lattice ((0 : Fin 3), x)
  have hx : (x : InfiniteLattice.AmbientSpace) = PeriodicOperators.castVec k := hk
  let g : ℝ × ℝ → ℂ :=
    fun y => densityAt w (fun c => y.1 * edgeIndicator e c + y.2 * edgeIndicator e' c) x
  have hg : ContDiffAt ℝ 2 g 0 := by
    have hV := (hFormula (VertexIndex L) _ (vertexPos L) (positiveEdgeInitial (L := L)) 3 4 w C
      (laplacianOp (L := L)) hw hC setV k e e').1
    have hE := (hFormula (EdgeIndex L) _ (edgePos L) (positiveEdgeInitial (L := L)) 12 4 w C
      (AbelianFieldDensity.massiveOp (L := L)) hw hC setE k e e').1
    have hform : g = fun y : ℝ × ℝ =>
        logTraceAt (vertexPos L) (laplacianOp (L := L)) w (twoBondField e e' y.1 y.2)
            (PeriodicOperators.castVec k) -
          (1 / 2 : ℂ) * logTraceAt (edgePos L) (AbelianFieldDensity.massiveOp (L := L)) w
            (twoBondField e e' y.1 y.2) (PeriodicOperators.castVec k) := by
      funext y
      have hy : (fun c => y.1 * edgeIndicator e c + y.2 * edgeIndicator e' c) =
          twoBondField e e' y.1 y.2 := by
        funext c
        simp only [twoBondField, bondIndicator, edgeIndicator]
        congr!
      rw [← hx]
      simp only [g, hy, densityAt, logTraceAt]
    have hdiff := hV.sub (contDiffAt_const (c := (1 / 2 : ℂ)) |>.mul hE)
    exact hdiff.congr_of_eventuallyEq (Eventually.of_forall fun y => congrFun hform y)
  have hswap : ∀ a b : ℝ,
      densityAt w (fun c => a * edgeIndicator e' c + b * edgeIndicator e c) x = g (b, a) := by
    intro a b
    simp only [g]
    congr 1
    funext c
    ring
  unfold secondDerivative
  simp only [hswap]
  exact deriv_deriv_swap_of_contDiffAt hg
end YangMills.Construction.Tower.AbelianFieldDensity.SecondDerivativeSymmetry
end
