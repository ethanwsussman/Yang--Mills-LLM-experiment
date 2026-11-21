import YangMills.Construction.Towers.BoundsOfTheIteratedAveragesOnASide
import YangMills.Construction.Towers.IteratedAveragesAreHolomorphicOnASide
import YangMills.Construction.Towers.IteratedAveragesBoundsAtTheSideInfinity
import YangMills.Construction.Towers.IteratedAveragesOfSmallRegularFields
import YangMills.Construction.Towers.IteratedAveragesReadOnlyTheBlocksAtTheSideInfinity
import YangMills.Construction.Towers.IteratedAveragesReadOnlyTheBlocksOnASide
import YangMills.Construction.Towers.IteratesAreHolomorphicInTheFormAtTheSideInfinity
import YangMills.Construction.Towers.ScaledKernelsAreHolomorphicInTheFormAtTheSideInfinity
import YangMills.Construction.Towers.ScaledKernelsOfIteratedAveragesAreHolomorphicOnASide
import YangMills.Construction.Towers.ScaledNormsOfSmallIteratesAtTheSideInfinity
import YangMills.Construction.Towers.ScaledNormsOfTheIteratedAveragesOnASide
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
open PeriodicOperators (colourEdges colourVertices)
open SmoothingContraction (OpNormLE TorusOpNormLE)
open LeftChartFields (scalarCoords)
namespace IteratedSmallFieldMeans
theorem torusConditions_of_steps
    (hH : IteratedMeansHolomorphic.IteratedMeansHolomorphicOnSide)
    (hN : RescaledNormBounds.OperatorNormsBounded)
    (hK : RescaledKernelsHolomorphicOnTorus)
    (hO : BlockLocality.LocalDependence)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) {ρ C : ℝ}
    (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 41) (hC : 20 ≤ C)
    (hC' : Real.exp (30 * smoothingStepConstant L) ≤ C)
    (hb : ∀ a ∈ complexEdgeForms L n k 0, maxOperatorNorm a ≤ ENNReal.ofReal ρ →
      IteratedMeanBounds.FormConditions L n k a) :
    TorusConditions L n k ρ C := by
  have hlt : ∀ a ∈ complexEdgeForms L n k 0, maxOperatorNorm a < ENNReal.ofReal ρ → ∀ j < k,
      PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a) ∈
          fieldsIn L n k j PeriodicLattice.complexGaugeGroup ∧
        ∀ b : Edge L n k j,
          Matrices.ComplexMatrix2.operatorNorm
              (PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a) b - 1) <
            polydiscRadius L / 2 := fun a ha hs j hj =>
    ⟨(hb a ha hs.le).mem_fields j hj.le, (hb a ha hs.le).norm_sub_one_lt_half j hj.le⟩
  refine ⟨fun a ha => ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · have h := hb a ha.1 ha.2
    have hnorm := hN L hL n k hn hk a ha.1
      (ha.2.trans (ENNReal.ofReal_le_ofReal hρ'))
      ⟨fun j hj => h.mem_fields j hj.le, fun j hj => h.norm_sub_one_le j hj.le,
        fun j hj => h.norm_sub_one_lt_half j hj.le⟩
    refine ⟨h.mem_fields, h.mem_polydisc, fun j hj b => (h.norm_sub_one_le j hj b).trans ?_,
      h.norm_sub_one_lt_half,
      ⟨h.mem_fields 0 (Nat.zero_le k), fun j hj => ⟨h.mem_fields j hj.le, fun b =>
        ?_⟩⟩, ⟨hnorm.1.1, hnorm.1.2.trans (ENNReal.ofReal_le_ofReal hC')⟩,
      ⟨hnorm.2.1, hnorm.2.2.trans (ENNReal.ofReal_le_ofReal hC')⟩⟩
    · have hl : 0 ≤ meshAt L k j := zpow_nonneg (Nat.cast_nonneg L) _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hl) ENNReal.toReal_nonneg
    · have h₁ := h.norm_sub_one_lt_half j hj.le b
      have h₀ : 0 ≤ Matrices.ComplexMatrix2.operatorNorm
          (PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a) b - 1) :=
        norm_nonneg _
      linarith
  · exact fun j hj c => hH L hL ρ hρ n k hn hk hlt j hj c
  · exact fun ι' ι => (hK L hL ρ hρ k hk n hn hlt).1 ι' ι
  · exact fun ι' ι => (hK L hL ρ hρ k hk n hn hlt).2 ι' ι
  · obtain ⟨hq, hr⟩ := hO L hL n k hn hk ρ hρ fun a ha j hj =>
      ⟨(hb a ha.1 ha.2).mem_fields j hj.le, (hb a ha.1 ha.2).norm_sub_one_lt_half j hj.le⟩
    exact ⟨fun c a ha a' ha' B hB B' hB' e₁ e₂ => hq c a ha a' ha' B hB B' hB' e₁ e₂,
      fun y a ha a' ha' l l' hl hl' e₁ e₂ => hr y a ha a' ha' l l' hl hl' e₁ e₂⟩
end IteratedSmallFieldMeans
namespace FullSpace.IteratedSmallFieldMeans
theorem iteratedAverages_of_steps
    (hH : FullSpace.IterHolomorphy.IteratesHolomorphicInForm)
    (hN : FullSpace.RescaledNormBounds.RescaledNormsBounded)
    (hK : FullSpace.HolomorphicRescaledKernels.KernelEntriesHolomorphic)
    (hO : FullSpace.IterLocality.IterLocalityHolds)
    {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {ρ C : ℝ}
    (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 41) (hC : 20 ≤ C)
    (hC' : Real.exp (30 * smoothingStepConstant L) ≤ C)
    (hb : ∀ a ∈ FullSpace.complexEdgeForms (meshAt L k 0),
      maxOperatorNorm a ≤ ENNReal.ofReal ρ →
      FullSpace.IterBounds.BoundsAtForm L k a) :
    FullConditions L k ρ C := by
  have hconst : Real.exp (30 * ((12 * (L : ℝ) ^ 3 + 2) *
      (2560 * (polydiscRadius L ^ 2)⁻¹))) ≤ C := by
    have he : smoothingStepConstant L =
        (12 * (L : ℝ) ^ 3 + 2) * (2560 * (polydiscRadius L ^ 2)⁻¹) := by
      unfold smoothingStepConstant
      rw [inv_pow]
    rw [← he]
    exact hC'
  have hlt : FullSpace.HolomorphicRescaledKernels.SmallIterates L k ρ :=
    fun a ha hs j hj =>
      ⟨(hb a ha hs.le).mem_complexGroup j hj.le, (hb a ha hs.le).norm_sub_one_lt_half j hj.le⟩
  refine ⟨fun a ha => ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · have h := hb a ha.1 ha.2
    have hnorm := hN L hL k hk a ha.1
      (ha.2.trans (ENNReal.ofReal_le_ofReal hρ'))
      ⟨fun j hj => h.mem_complexGroup j hj.le, fun j hj => h.norm_sub_one_le j hj.le,
        fun j hj => h.norm_sub_one_lt_half j hj.le⟩
    refine ⟨h.mem_complexGroup, h.mem_polydisc, fun j hj b => (h.norm_sub_one_le j hj b).trans ?_,
      h.norm_sub_one_lt_half,
      ⟨h.mem_complexGroup 0 (Nat.zero_le k), fun j hj => ⟨h.mem_complexGroup j hj.le, fun b =>
        ?_⟩⟩, ⟨hnorm.1.1, hnorm.1.2.1, hnorm.1.2.2.trans (ENNReal.ofReal_le_ofReal hconst)⟩,
      ⟨hnorm.2.1, hnorm.2.2.1, hnorm.2.2.2.trans (ENNReal.ofReal_le_ofReal hconst)⟩⟩
    · have hl : 0 ≤ meshAt L k j := zpow_nonneg (Nat.cast_nonneg L) _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hl) ENNReal.toReal_nonneg
    · have h₁ := h.norm_sub_one_lt_half j hj.le b
      have h₀ : 0 ≤ Matrices.ComplexMatrix2.operatorNorm
          (FullSpace.complexIter L k j (FullSpace.remainderGaugeField a) b - 1) := norm_nonneg _
      linarith
  · exact fun j hj c => hH L hL ρ hρ k hk hlt j hj c
  · exact fun ι' ι => (hK L hL ρ hρ k hk hlt).1 ι' ι
  · exact fun ι' ι => (hK L hL ρ hρ k hk hlt).2 ι' ι
  · obtain ⟨hq, hr⟩ := hO L hL k hk ρ hρ fun a ha j hj =>
      ⟨(hb a ha.1 ha.2).mem_complexGroup j hj.le,
        (hb a ha.1 ha.2).norm_sub_one_lt_half j hj.le⟩
    exact ⟨fun c a ha a' ha' B hB B' hB' e₁ e₂ => hq c a ha a' ha' B hB B' hB' e₁ e₂,
      fun y a ha a' ha' l l' hl hl' e₁ e₂ => hr y a ha a' ha' l l' hl hl' e₁ e₂⟩
end FullSpace.IteratedSmallFieldMeans
namespace IteratedSmallFieldMeans
theorem iteratedMeansClaim_of_steps
    (hB : IteratedMeanBounds.SmallRadiusAdmissible)
    (hH : IteratedMeansHolomorphic.IteratedMeansHolomorphicOnSide)
    (hN : RescaledNormBounds.OperatorNormsBounded)
    (hK : RescaledKernelsHolomorphicOnTorus)
    (hO : BlockLocality.LocalDependence)
    (hB' : FullSpace.IterBounds.UniformIterBounds)
    (hH' : FullSpace.IterHolomorphy.IteratesHolomorphicInForm)
    (hN' : FullSpace.RescaledNormBounds.RescaledNormsBounded)
    (hK' : FullSpace.HolomorphicRescaledKernels.KernelEntriesHolomorphic)
    (hO' : FullSpace.IterLocality.IterLocalityHolds) :
    IteratedMeansClaim := by
  refine ⟨fun L hL => ?_, fun D l => ⟨⟨smallRadius, fun _ => rfl⟩, ⟨boundConstant, fun _ => rfl⟩⟩⟩
  obtain ⟨hp, hp', hfin⟩ := hB L hL
  obtain ⟨r, hr, hr', hinf⟩ := hB' L hL
  have hρ : 0 < min (IteratedMeanBounds.smallRadius L) r := lt_min hp hr
  have hρ' : min (IteratedMeanBounds.smallRadius L) r ≤ 1 / 41 :=
    (min_le_right _ _).trans hr'
  have hex : ∃ p : ℝ × ℝ, AdmissibleConstants L p.1 p.2 := by
    refine ⟨(min (IteratedMeanBounds.smallRadius L) r,
      max 20 (Real.exp (30 * smoothingStepConstant L))), hρ,
      hρ'.trans (by norm_num), le_trans (by norm_num) (le_max_left _ _), fun k hk =>
        ⟨fun n hn => ?_, ?_⟩⟩
    · exact torusConditions_of_steps hH hN hK hO hL hn hk hρ hρ' (le_max_left _ _)
        (le_max_right _ _) fun a ha hs => hfin n hn k hk a ha
          (hs.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
    · exact FullSpace.IteratedSmallFieldMeans.iteratedAverages_of_steps hH' hN' hK' hO' hL hk
        hρ hρ' (le_max_left _ _) (le_max_right _ _) fun a ha hs => hinf k hk a ha
          (hs.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _)))
  exact Classical.epsilon_spec (p := fun p : ℝ × ℝ => AdmissibleConstants L p.1 p.2) hex
end IteratedSmallFieldMeans
end YangMills.Construction.Tower
end
