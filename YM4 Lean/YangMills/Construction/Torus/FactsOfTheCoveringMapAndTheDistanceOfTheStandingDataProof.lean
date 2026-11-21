import YangMills.Construction.ReflectionPositivity.FactsOfTheCoveringMap
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctions
import YangMills.Construction.Torus.FactsOfTheCoveringMapAndTheDistanceOfTheStandingData
import YangMills.Construction.Torus.IntegralOverTheTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace Conventions.StandingParameters.CoveringAndDistanceFacts
theorem intCombination_eq (α : ℝ) (n : Fin 4 → ℤ) :
    ReflectionPositivity.AxisMirror.intCombination α n = fun μ => α * (n μ : ℝ) := by
  funext μ
  simp [ReflectionPositivity.AxisMirror.intCombination, Finset.sum_apply,
    PeriodicLattice.coordVec, Pi.single_apply]
theorem compactSpace_of_isCompactWrt (s : StandingParameters)
    (hsymm : ∀ x x' : s.Torus, torusEuclidNorm (x - x') = torusEuclidNorm (x' - x))
    (h : MetricNotions.IsCompactWrt (PeriodicLattice.torusEuclidDist s.L s.m)
      (Set.univ : Set s.Torus)) :
    @CompactSpace _ (PeriodicLattice.metricTopology s.L s.m) := by
  classical
  let _ : TopologicalSpace s.Torus := PeriodicLattice.metricTopology s.L s.m
  refine ⟨isCompact_of_finite_subcover fun {ι} U hU hcov => ?_⟩
  have hopen : ∀ V ∈ Set.range U,
      MetricNotions.IsOpenWrt (PeriodicLattice.torusEuclidDist s.L s.m) V := by
    rintro _ ⟨i, rfl⟩ x hx
    obtain ⟨r, hr, hsub⟩ := hU i x hx
    refine ⟨r, hr, fun y hy => hsub ?_⟩
    show torusEuclidNorm (y - x) < r
    rw [hsymm]
    exact hy
  have hcover : (Set.univ : Set s.Torus) ⊆ ⋃₀ Set.range U := by
    rw [Set.sUnion_range]
    exact hcov
  obtain ⟨W, hW, hfin, hsub⟩ := h (Set.range U) hopen hcover
  choose f hf using fun V (hV : V ∈ W) => hW hV
  refine ⟨hfin.toFinset.attach.image fun V => f V.1 (hfin.mem_toFinset.1 V.2), fun x hx => ?_⟩
  obtain ⟨V, hV, hxV⟩ := hsub hx
  refine Set.mem_iUnion₂.2 ⟨f V hV, Finset.mem_image.2
    ⟨⟨V, hfin.mem_toFinset.2 hV⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
  rw [hf V hV]
  exact hxV
theorem holds (hC : ReflectionPositivity.AxisMirror.ProjectionFacts)
    (hM : ReflectionPositivity.CutoffMirrors.TorusMetricSpace.MetricTorusFacts) :
    CoveringAndDistanceFacts := by
  intro s
  obtain ⟨⟨hsurj, -, hiff, -⟩, ⟨-, hle, -⟩, -⟩ := hC ⟨s, 1, one_pos⟩
  obtain ⟨⟨-, hdist, -, -, hcompact⟩, -⟩ := hM ⟨s, 1, one_pos, 0⟩
  have hsymm : ∀ x x' : s.Torus, torusEuclidNorm (x - x') = torusEuclidNorm (x' - x) :=
    hdist.symm
  refine ⟨hsurj, fun y y' => (hiff y y').trans ?_, hdist.nonneg, hdist.eq_zero_iff, hsymm,
    hdist.triangle, hle, PeriodicLattice.continuous_torusProj,
    compactSpace_of_isCompactWrt s hsymm hcompact⟩
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← hn, intCombination_eq]
    rfl
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn, intCombination_eq]
    rfl
end Conventions.StandingParameters.CoveringAndDistanceFacts
end YangMills.Construction
end
