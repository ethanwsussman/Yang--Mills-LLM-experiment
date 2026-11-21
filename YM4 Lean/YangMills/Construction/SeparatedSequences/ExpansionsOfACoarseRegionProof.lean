import YangMills.Construction.Torus.SeparatedSequenceOfACoarseRegion
import YangMills.Construction.SeparatedSequences.PropertiesOfTheOperatorsOfASequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus.CoarseRegionExpansions
open Set TorusMetric
theorem torusSupNorm_proj_le {S r : ℝ} {w : Fin 4 → ℝ} (h : ∀ μ, |w μ| ≤ r) :
    torusSupNorm (torusProj S w) ≤ r := by
  refine le_trans (csInf_le ⟨0, ?_⟩ ⟨w, rfl, rfl⟩) (Finset.sup'_le _ _ fun μ _ => h μ)
  rintro _ ⟨v, -, rfl⟩
  exact le_trans (abs_nonneg (v 0)) (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ (0 : Fin 4)))
theorem unitStep_injective {S σ : ℝ} (hσ : 0 < σ) (hS : σ < S) {μ ν : Fin 4}
    (h : unitStep S σ μ = unitStep S σ ν) : μ = ν := by
  by_contra hne
  have h1 : coordPoint S μ σ = coordPoint S ν σ := congrArg Subtype.val h
  have h2 := congrFun h1 μ
  simp only [coordPoint, torusProj, Pi.single_eq_same, Pi.single_eq_of_ne hne,
    AddCircle.coe_zero] at h2
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff S).1 h2
  rw [zsmul_eq_mul] at hn
  rcases le_or_gt n 0 with h3 | h3
  · have : (n : ℝ) ≤ 0 := by exact_mod_cast h3
    nlinarith
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h3
    nlinarith
theorem posBondDir_bondFrom {D : ScaleData} {n : ℕ} (hσ : 0 < D.levelSpacing n)
    (hS : D.levelSpacing n < D.torusSide) (x : D.SiteAt n) (μ : Fin 4) :
    ScaleData.posBondDir (ScaleData.bondFrom x μ) = μ := by
  have spec := (ScaleData.bondFrom x μ).2.choose_spec
  refine unitStep_injective hσ hS (spec.symm.trans ?_)
  simp [ScaleData.bondFrom, LatticeBond.plus]
section Blocks
variable {L j N : ℕ} (S : PeriodicLattice.Scales 4 L j N)
end Blocks
namespace Restriction
variable (W : CoarseCubeRegion)
abbrev Point : Type := PeriodicLattice.Torus 4 W.period
theorem odd_L : Odd W.L := W.blocking.odd_blockingFactor
def toSiteAt (s : PeriodicLattice.Mesh W.period) (n : ℕ) (h : W.scaleData.levelSpacing n = s.h)
    (x : PeriodicLattice.GridPoint 4 s) : W.scaleData.SiteAt n :=
  ⟨x.1, by rw [h]; exact mem_spacingLattice_of_mem_sublattice s x.2⟩
theorem baseSite_injective : Function.Injective W.baseSite := by
  intro x y h
  have h' : (W.baseSite x).1 = (W.baseSite y).1 := by rw [h]
  exact Subtype.ext h'
theorem fineScale_pos : 0 < PeriodicLattice.fineScale W.L W.depth := W.scales.fineMesh.h_pos
def bondValue (A : W.scaleData.BondField) (μ : Fin 4)
    (x : PeriodicLattice.GridPoint 4 W.scales.fineMesh) (i : ℕ) : ℝ :=
  W.fieldRestriction A (μ, x + i • W.scales.fineMesh.basisStep μ)
end Restriction
end YangMills.Construction.GeneralTorus.CoarseRegionExpansions
end
