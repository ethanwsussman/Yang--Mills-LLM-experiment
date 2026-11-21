import YangMills.Construction.GeneralTorus.ShellsCubesAndScaledDistance
import YangMills.Construction.Geometry.UnitLatticeBlocks
import YangMills.Construction.Torus.FormsAveragesAndOperatorsOnAGeneralTorus
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.GeneralTorus.MeanCurlBound
variable {D : ScaleData}
theorem levelSpacing_zero : D.levelSpacing 0 = D.baseSpacing := by simp [ScaleData.levelSpacing]
theorem levelSpacing_lastLevel :
    D.levelSpacing D.lastLevel = (D.blockSize D.lastLevel : ℝ) * D.levelSpacing 0 := by
  simp [ScaleData.levelSpacing, ScaleData.blockSize]
theorem L_pos : 0 < D.L := D.blocking.odd_blockingFactor.pos
def halfWidth (D : ScaleData) : ℕ := D.blockSize D.lastLevel / 2
def toBaseSite (y : D.SiteAt D.lastLevel) : D.BaseSite :=
  ⟨y.1, by
    obtain ⟨k, hk⟩ := y.2
    refine ⟨fun μ => (D.blockSize D.lastLevel : ℤ) * k μ, ?_⟩
    rw [hk]
    funext μ
    simp only [torusProj]
    rw [levelSpacing_lastLevel]
    congr 1
    push_cast
    ring⟩
def latticeVector (k : Fin 4 → ℤ) : D.BaseSite :=
  ⟨torusProj D.torusSide fun μ => D.levelSpacing 0 * (k μ : ℝ), ⟨k, rfl⟩⟩
def cubeIndices (D : ScaleData) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(halfWidth D : ℤ)) (halfWidth D)
theorem posBondDir_bondFrom (unit : D.levelSpacing D.lastLevel = 1)
    (multiple : IsEvenMultipleOf D.torusSide (D.L : ℝ))
    (y : D.SiteAt D.lastLevel) (μ : Fin 4) : ScaleData.posBondDir (ScaleData.bondFrom y μ) = μ := by
  by_contra hne
  have hs := (ScaleData.bondFrom y μ).2.choose_spec
  change (y + unitStep D.torusSide (D.levelSpacing D.lastLevel) μ) - y =
    unitStep D.torusSide (D.levelSpacing D.lastLevel)
      (ScaleData.posBondDir (ScaleData.bondFrom y μ)) at hs
  rw [add_sub_cancel_left] at hs
  have hc := congrArg (fun z : D.SiteAt D.lastLevel => (z : D.Space) μ) hs
  simp only [unitStep, coordPoint, torusProj, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne),
    unit] at hc
  obtain ⟨m, -, hS⟩ := multiple
  have h0 : ((1 : ℝ) : AddCircle D.torusSide) = 0 := by simpa using hc
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff D.torusSide).1 h0
  rw [zsmul_eq_mul, hS] at hn
  have hz : 2 * (n * (m : ℤ) * (D.L : ℤ)) = 1 := by
    have : (2 : ℝ) * ((n : ℝ) * (m : ℝ) * (D.L : ℝ)) = 1 := by linear_combination hn
    exact_mod_cast this
  omega
end YangMills.Construction.GeneralTorus.MeanCurlBound
