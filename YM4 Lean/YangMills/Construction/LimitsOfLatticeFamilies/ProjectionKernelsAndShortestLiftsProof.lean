import YangMills.Construction.ChessboardTori.CoveringMapOnTheCellsOfAGridProof
import YangMills.Construction.LimitsOfLatticeFamilies.ClassC1AndTheGradientThroughTheLiftProof
import YangMills.Construction.LimitsOfLatticeFamilies.ProjectionKernelsAndShortestLifts
import YangMills.Construction.Torus.CellsOfATranslatedLatticeAndBallsOfTheTorusProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LatticeLimits.ProjKernelAndMinimalLifts
open YangMills.Construction.LatticeLimits.ModelSpace
theorem torusSide_pos (s : Conventions.StandingParameters) :
    0 < PeriodicLattice.torusSide s.L s.m := by apply _root_.YangMills.Construction.TorusMeasure.TranslatedLatticeCells.torusSide_pos <;> assumption
theorem abs_apply_le_euclidNormVec (x : Fin 4 → ℝ) (μ : Fin 4) :
    |x μ| ≤ TorusMetric.euclidNormVec x := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem euclidNormVec_mono_abs {a b : Fin 4 → ℝ} (h : ∀ μ, |a μ| ≤ |b μ|) :
    TorusMetric.euclidNormVec a ≤ TorusMetric.euclidNormVec b := by apply _root_.YangMills.Construction.ChessboardTori.ProjOnGridCellsProof.euclidNormVec_mono <;> assumption
theorem norm_torus_eq_of_lift (s : Conventions.StandingParameters) (z : s.Torus) (b : Fin 4 → ℝ)
    (hb : torusCover s b = z)
    (hn : ∀ μ, |b μ| = ‖(z μ : AddCircle (PeriodicLattice.torusSide s.L s.m))‖) :
    ModelSpace.norm s torus z = TorusMetric.euclidNormVec b := by
  refine le_antisymm ?_ ?_
  · refine csInf_le ⟨0, ?_⟩ ⟨b, hb, rfl⟩
    rintro _ ⟨w, -, rfl⟩
    exact Real.sqrt_nonneg _
  · refine le_csInf ⟨_, b, hb, rfl⟩ ?_
    rintro _ ⟨w, hw, rfl⟩
    refine euclidNormVec_mono_abs fun μ => ?_
    have hw' : TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) w = z := hw
    rw [hn μ, ← hw']
    exact TorusMetric.addCircle_norm_coe_le_abs _
theorem exists_lift_abs_eq_norm (s : Conventions.StandingParameters) (z : s.Torus) :
    ∃ b : Fin 4 → ℝ, torusCover s b = z ∧
      ∀ μ, |b μ| = ‖(z μ : AddCircle (PeriodicLattice.torusSide s.L s.m))‖ := by
  choose b hb hb' using fun μ => TorusMetric.exists_coe_eq_abs_eq_norm (z μ)
  exact ⟨b, funext hb, hb'⟩
theorem proj_add (s : Conventions.StandingParameters) (Y : ModelSpace) (x x' : Fin 4 → ℝ) :
    proj s Y (x + x') = proj s Y x + proj s Y x' := by
  cases Y with
  | euclidean => rfl
  | torus =>
    funext μ
    exact AddCircle.coe_add _ _ _ |>.trans rfl
theorem proj_sub (s : Conventions.StandingParameters) (Y : ModelSpace) (x x' : Fin 4 → ℝ) :
    proj s Y (x - x') = proj s Y x - proj s Y x' := by
  have h := proj_add s Y (x - x') x'
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]
theorem proj_surjective (s : Conventions.StandingParameters) (Y : ModelSpace) :
    Function.Surjective (proj s Y) := by apply _root_.YangMills.Construction.LatticeLimits.C1ViaLift.proj_surj <;> assumption
theorem exists_isMinimalLiftOf (s : Conventions.StandingParameters) (Y : ModelSpace)
    (z : Y.Carrier s) : ∃ v, IsMinimalLiftOf s Y z v := by
  cases Y with
  | euclidean => exact ⟨z, rfl, rfl⟩
  | torus =>
    obtain ⟨b, hb, hn⟩ := exists_lift_abs_eq_norm s z
    exact ⟨b, hb, (norm_torus_eq_of_lift s z b hb hn).symm⟩
theorem norm_proj_le (s : Conventions.StandingParameters) (Y : ModelSpace) (x : Fin 4 → ℝ) :
    ModelSpace.norm s Y (proj s Y x) ≤ TorusMetric.euclidNormVec x := by
  cases Y with
  | euclidean => exact le_rfl
  | torus =>
    refine csInf_le ⟨0, ?_⟩ ⟨x, rfl, rfl⟩
    rintro _ ⟨w, -, rfl⟩
    exact Real.sqrt_nonneg _
theorem norm_proj_torus_of_lt (s : Conventions.StandingParameters) (x : Fin 4 → ℝ)
    (hx : TorusMetric.euclidNormVec x < s.side / 2) :
    ModelSpace.norm s torus (proj s torus x) = TorusMetric.euclidNormVec x := by
  have hS := torusSide_pos s
  refine norm_torus_eq_of_lift s _ x rfl fun μ => ?_
  have hμ : |x μ| ≤ |PeriodicLattice.torusSide s.L s.m| / 2 := by
    rw [abs_of_pos hS]
    exact (abs_apply_le_euclidNormVec x μ).trans hx.le
  exact ((AddCircle.norm_coe_eq_abs_iff _ hS.ne').2 hμ).symm
theorem ker_proj_torus (s : Conventions.StandingParameters) :
    {x | proj s torus x = 0} = {x | ∃ k : Fin 4 → ℤ, x = fun μ => s.side * k μ} := by
  ext x
  constructor
  · intro hx
    have hμ : ∀ μ, ∃ n : ℤ, n • PeriodicLattice.torusSide s.L s.m = x μ := fun μ =>
      (AddCircle.coe_eq_zero_iff _).1 (congrFun hx μ)
    choose k hk using hμ
    refine ⟨k, funext fun μ => ?_⟩
    rw [← hk μ, zsmul_eq_mul, mul_comm]
    rfl
  · rintro ⟨k, rfl⟩
    funext μ
    exact (AddCircle.coe_eq_zero_iff _).2 ⟨k μ, by
      rw [zsmul_eq_mul, mul_comm]
      rfl⟩
theorem claim_holds : Claim := by
  intro s
  refine ⟨⟨?_, ker_proj_torus s⟩, fun Y => ⟨proj_add s Y, proj_surjective s Y,
    exists_isMinimalLiftOf s Y, norm_proj_le s Y, fun x x' => ?_, fun x hx => ?_⟩⟩
  · ext x
    rfl
  · rw [← proj_sub]
    exact norm_proj_le s Y _
  · rcases hx with rfl | ⟨rfl, hx⟩
    · rfl
    · exact norm_proj_torus_of_lt s x hx
end YangMills.Construction.LatticeLimits.ProjKernelAndMinimalLifts
end
