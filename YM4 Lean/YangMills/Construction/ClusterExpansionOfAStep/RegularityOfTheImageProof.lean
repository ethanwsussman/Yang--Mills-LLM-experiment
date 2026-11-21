import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.ImageDensityIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.ImageFactorIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsSmoothOffItsHull
import YangMills.Construction.ClusterExpansionOfAStep.RegularityOfTheImage
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
theorem imageHasHullExpansionRegularity_holds (hS : StepSettings.coarseWeightSmoothStatement)
    (hIS : StepGas.CoarseWeightExpansionMeasurable) (hIF : StepGas.CoarseFactorExpansionMeasurable)
    (hID : ImageStateDensityMeasurable) (hFl : StepFloors.EventuallyFloorConditions) :
    ImageHasHullExpansionRegularity := by
  intro T hT
  obtain ⟨y₁, h₁⟩ := hIS T hT
  obtain ⟨y₂, h₂⟩ := hIF T hT
  obtain ⟨y₃, h₃⟩ := hID T hT
  have hLpos : (0 : ℝ) < 2 ^ 40 * (T.side : ℝ) + 4 * (T.n₀ : ℝ) + 2 ^ 16 + 2 := by positivity
  obtain ⟨y₄, h₄⟩ := hFl T hT (2 ^ 40 * (T.side : ℝ) + 4 * (T.n₀ : ℝ) + 2 ^ 16 + 2) 1 hLpos one_pos
  refine ⟨max (max (max y₁ y₂) (max y₃ y₄)) (max T.floorMin 1),
    fun y hy R hpar hball hbar hyx hrow hfun hx' hclose h => ?_⟩
  have hy₁ : y₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hy)
  have hy₂ : y₂ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hy)
  have hy₃ : y₃ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hy)
  have hy₄ : y₄ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hy)
  have hy₅ : T.floorMin ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hy₆ : 1 ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
  have hfl := h₄ R.coupling (hy₄.trans hyx)
  have hB : R.params.B = T.B := by rw [hpar]; rfl
  have hnear := hfl.stable_nearby.2 R.nextCoupling (by rw [← hB]; simpa [abs_sub_comm] using hclose)
  obtain ⟨hxx, -, hr1, hr2⟩ := hnear
  have hrC : 2 ^ 40 * (T.side : ℝ) + 4 * (T.n₀ : ℝ) + 2 ^ 16 + 2 ≤
      (TorusLumps.clusterRange R.coupling : ℝ) := hfl.range_ge
  have hLL : R.params.side = T.side := by rw [hpar]; rfl
  have hrN : 2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 16 + 2 ≤ TorusLumps.clusterRange R.coupling := by
    exact_mod_cast hrC
  have hn₀ : R.params.n₀ = T.n₀ := by rw [hpar]; rfl
  have hadm : R.params.Admissible := by
    rw [hpar]
    exact hT.fits y hy₅
  have hcut : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn := by
    have : R.ballRadius = T.ballRadius := by
      show R.params.threshold / 64 = T.threshold / 64
      rw [hpar]
      rfl
    rw [this, hbar]
    exact hT.cut
  have hwell : R.IsWellPosed :=
    { hasExpansions := hrow
      admissible := hadm
      isCutoff := hcut
      range_le := hr1
      nextRange_le := hr2
      nextRange_ge := by
        show 2 ^ 16 ≤ TorusLumps.clusterRange R.nextCoupling
        omega
      range_ge_side := by
        show 2 ^ 40 * R.params.side ≤ TorusLumps.clusterRange R.coupling
        rw [hLL]
        omega
      range_ge_base := by
        show 4 * R.params.n₀ + 2 ^ 16 ≤ TorusLumps.clusterRange R.coupling
        rw [hn₀]
        omega
      coupling_pos := by linarith
      functional_spec := hfun }
  have hstep : R.IsStep := ⟨hrow, hxx, hr1⟩
  have htab : R.OnParameters T y := ⟨hpar, hball, hbar, hyx, hstep⟩
  have hcoup : R.params.coupling = T.coupling := by rw [hpar]; rfl
  have hder : R.params.derivBound = T.derivBound := by rw [hpar]; rfl
  have hax : 1 ≤ R.params.coupling * R.coupling := by
    rw [hcoup]
    nlinarith [hT.a_ge]
  have hx'pos : 0 < R.nextCoupling := by
    by_contra hcon
    have : R.nextCoupling ≤ 0 := not_lt.mp hcon
    nlinarith
  refine ⟨fun n _ hb Y => ⟨h₁ y hy₁ R htab hwell n hb Y, h₂ y hy₂ R htab hwell n hb Y, fun y' =>
    h₃ y hy₃ R htab hwell n hb Y y'⟩, ?_⟩
  intro n _ hb W Y ω hh hpos k c X hfar
  exact hS R hwell hax (by rw [hcoup, hder]; exact hT.Cder_ge) hx'pos hxx n hb W Y ω hh hpos k c X hfar
end YangMills.Construction.ClusterExpansionOfAStep
end
