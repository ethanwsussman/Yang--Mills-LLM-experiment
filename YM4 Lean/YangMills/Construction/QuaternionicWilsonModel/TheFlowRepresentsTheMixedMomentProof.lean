import YangMills.Construction.QuaternionicWilsonModel.TheFlowRepresentsTheMixedMoment
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction
namespace TopAux
open BlockAverages WeightedResponses TorusLumps SlopeCoefficient TotalDensityFlow
private theorem sideFilter_le_atTop {L : ℕ} (hL : 2 ≤ L) : TotalDensityFlow.sideFilter L ≤ atTop := by
  have h : Tendsto (fun q : ℕ => 2 * L ^ q) atTop atTop :=
    tendsto_atTop_mono (fun q => (Nat.lt_pow_self (by omega : 1 < L)).le.trans (Nat.le_mul_of_pos_left _ (by norm_num)))
      tendsto_id
  exact h
abbrev _root_.YangMills.SharedProofs.p17016 := @sideFilter_le_atTop
private instance sideFilter_neBot (L : ℕ) : (TotalDensityFlow.sideFilter L).NeBot := by
  unfold TotalDensityFlow.sideFilter
  infer_instance
private def quaternionUnitI : BlockAverages.imaginaryQuaternions := ⟨⟨0, 1, 0, 0⟩, rfl⟩
private theorem inner_quaternionUnitI_self :
    inner ℝ ((quaternionUnitI : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])
      ((quaternionUnitI : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) = 1 := by
  have h : Quaternion.normSq ((quaternionUnitI : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) = 1 := by
    rw [Quaternion.normSq_def']
    have h0 : ((quaternionUnitI : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]).re = 0 := rfl
    have h1 : ((quaternionUnitI : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]).imI = 1 := rfl
    have h2 : ((quaternionUnitI : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]).imJ = 0 := rfl
    have h3 : ((quaternionUnitI : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]).imK = 0 := rfl
    rw [h0, h1, h2, h3]
    norm_num
  rw [real_inner_self_eq_norm_sq, sq, ← Quaternion.normSq_eq_norm_mul_self, h]
abbrev _root_.YangMills.DeltaSharedProofs.p500886 := @inner_quaternionUnitI_self
private theorem hasMixedSecondMoment_eq {l : Filter ℕ} [l.NeBot] {H : SlopeCoefficient.GaugeTotal} {b b' : ℝ}
    (h : SlopeCoefficient.HasMixedSecondMoment l H b) (h' : SlopeCoefficient.HasMixedSecondMoment l H b') : b = b' := by
  obtain ⟨P, hP, hs⟩ := h
  obtain ⟨P', hP', hs'⟩ := h'
  have e : ∀ (μ ν : Fin 4) (u : Fin 4 → ℤ), P μ ν u = P' μ ν u := by
    intro μ ν u
    have h1 := hP (0, μ) (u, ν) quaternionUnitI quaternionUnitI
    have h2 := hP' (0, μ) (u, ν) quaternionUnitI quaternionUnitI
    have h3 := tendsto_nhds_unique h1 h2
    simpa only [sub_zero, inner_quaternionUnitI_self, one_mul] using h3
  have n01 : (0 : Fin 4) ≠ 1 := by decide
  have h1 := hs 0 1 n01
  have h2 := hs' 0 1 n01
  simp only [e] at h1
  exact h1.unique h2
abbrev _root_.YangMills.SharedProofs.p57451 := @hasMixedSecondMoment_eq
theorem flowReadsMixedMomentStatement_holds (h : SlopeCoefficient.SlopeIsMixedMoment) :
    TopAux.flowReadsMixedMomentStatement := by
  intro ℓ β t hL hrun j hj b
  have hm := h (TotalDensityFlow.sideFilter ℓ.side) (sideFilter_le_atTop hL) _ _ (hrun.succ j hj).2
  exact ⟨fun hb => hasMixedSecondMoment_eq hb hm, fun hb => hb ▸ hm⟩
end TopAux
end YangMills.Construction
end
