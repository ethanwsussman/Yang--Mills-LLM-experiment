import YangMills.Construction.ChessboardTori.CoveringMapOnTheCellsOfAGridProof
import YangMills.Construction.Geometry.MinimalLift
import YangMills.Construction.Torus.CollinearQuadruplesProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusMetric.LiftUniqueness
variable {S : ℝ}
theorem euclidNormVec_sub_le (v w : Fin 4 → ℝ) :
    euclidNormVec (v - w) ≤ euclidNormVec v + euclidNormVec w := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.euclidNormVec_sub_le <;> assumption
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem euclidNormVec_le_of_abs_le {a b : Fin 4 → ℝ} (h : ∀ μ, |a μ| ≤ |b μ|) :
    euclidNormVec a ≤ euclidNormVec b := by apply _root_.YangMills.Construction.ChessboardTori.ProjOnGridCellsProof.euclidNormVec_mono <;> assumption
theorem le_abs_sub_of_addCircle_coe_eq (hS : 0 < S) {x y : ℝ} (h : (x : AddCircle S) = y)
    (hne : x ≠ y) : S ≤ |x - y| := by
  have h0 : ((x - y : ℝ) : AddCircle S) = 0 := by rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff S).1 h0
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (sub_eq_zero.1 (by simpa using hn.symm))
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    exact_mod_cast this
  rw [← hn, zsmul_eq_mul, abs_mul, abs_of_pos hS]
  nlinarith
theorem minimalLift_of_side_pos (hS : 0 < S) (z : Torus4 S) (hz : torusEuclidNorm z < S / 2) :
    (∃! v : Fin 4 → ℝ, IsMinimalLift z v) ∧ IsMinimalLift z (minimalLift z) ∧
      ∀ v' : Fin 4 → ℝ, torusProj S v' = z → v' ≠ minimalLift z →
        S - torusEuclidNorm z ≤ euclidNormVec v' ∧ S / 2 < S - torusEuclidNorm z := by
  choose b hb hb' using fun μ => exists_coe_eq_abs_eq_norm (z μ)
  have hproj : torusProj S b = z := funext hb
  have hmin : ∀ v, torusProj S v = z → euclidNormVec b ≤ euclidNormVec v := by
    intro v hv
    refine euclidNormVec_le_of_abs_le fun μ => ?_
    rw [hb', ← hv]
    exact addCircle_norm_coe_le_abs _
  have heq : torusEuclidNorm z = euclidNormVec b := by
    apply le_antisymm
    · refine csInf_le ⟨0, ?_⟩ ⟨b, hproj, rfl⟩
      rintro _ ⟨v, -, rfl⟩
      exact Real.sqrt_nonneg _
    · refine le_csInf ⟨_, b, hproj, rfl⟩ ?_
      rintro _ ⟨v, hv, rfl⟩
      exact hmin v hv
  have hfar : ∀ v', torusProj S v' = z → v' ≠ b → S - torusEuclidNorm z ≤ euclidNormVec v' := by
    intro v' hv' hne
    obtain ⟨μ, hμ⟩ := Function.ne_iff.1 hne
    have hc : (v' μ : AddCircle S) = b μ := by
      have h1 : torusProj S v' μ = z μ := congrFun hv' μ
      exact h1.trans (hb μ).symm
    have h2 := le_abs_sub_of_addCircle_coe_eq hS hc hμ
    have h3 : |v' μ - b μ| ≤ euclidNormVec (v' - b) := abs_apply_le_euclidNormVec (v' - b) μ
    have h4 := euclidNormVec_sub_le v' b
    rw [heq]
    linarith
  have hbmin : IsMinimalLift z b := ⟨hproj, heq.symm⟩
  have huniq : ∀ v, IsMinimalLift z v → v = b := by
    intro v hv
    by_contra hne
    have h1 := hfar v hv.1 hne
    rw [hv.2] at h1
    linarith
  have hspec : IsMinimalLift z (minimalLift z) := Classical.epsilon_spec ⟨b, hbmin⟩
  have hbeq : minimalLift z = b := huniq _ hspec
  refine ⟨⟨b, hbmin, huniq⟩, hspec, fun v' hv' hne => ⟨hfar v' hv' (hbeq ▸ hne), by linarith⟩⟩
theorem minimalLiftUnique_holds : MinimalLiftUnique := by
  intro s z hz
  have hL : (0 : ℝ) < s.L := by
    have := s.isAdmissible.2
    exact_mod_cast (by omega : 0 < s.L)
  have hS : 0 < PeriodicLattice.torusSide s.L s.m := by
    unfold PeriodicLattice.torusSide
    positivity
  exact minimalLift_of_side_pos hS z hz
end YangMills.Construction.TorusMetric.LiftUniqueness
end
