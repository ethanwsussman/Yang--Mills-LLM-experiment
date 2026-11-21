import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndWhatAnObservableReads
import YangMills.Construction.InfiniteLattice.TopologyAndDensityOnTheConfigurationsOfOneLattice
import YangMills.Construction.Measures.ContinuousFunctionsAndProbabilityMeasuresOnACompactMetricSpace
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.LatticePhases.TopologyDensityProof
open YangMills.Construction.InfiniteLattice
open ObservableRegions
section Compact
theorem uniformSup_le {Y : Type*} {f : Y → ℂ} {c : ℝ} (hc : 0 ≤ c) (hf : ∀ y, ‖f y‖ ≤ c) :
    uniformSup f ≤ c :=
  Real.iSup_le hf hc
variable {X : Type} [MetricSpace X] [CompactSpace X]
theorem norm_le_uniformSup (f : C(X, ℂ)) (x : X) : ‖f x‖ ≤ uniformSup (f : X → ℂ) :=
  le_ciSup (f := fun x => ‖f x‖) ⟨‖f‖, by rintro _ ⟨y, rfl⟩; exact f.norm_coe_le_norm y⟩ x
omit [CompactSpace X] in
theorem exists_dense_pnat_seq (hsep : TopologicalSpace.SeparableSpace C(X, ℂ)) :
    ∃ s : ℕ+ → C(X, ℂ), Dense (Set.range s) := by
  obtain ⟨t, ht⟩ := TopologicalSpace.exists_dense_seq C(X, ℂ)
  refine ⟨t ∘ Equiv.pnatEquivNat, ?_⟩
  rw [Equiv.pnatEquivNat.surjective.range_comp]
  exact ht
theorem exists_uniform_approx_comp (φ : ℕ → X → X)
    (hφ : ∀ δ : ℝ, 0 < δ → ∃ N, ∀ n, N ≤ n → ∀ x, dist (φ n x) x < δ) {f : X → ℂ}
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n, N ≤ n → ∀ x, ‖f x - f (φ n x)‖ < ε := by
  have huc := CompactSpace.uniformContinuous_of_continuous hf
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.1 huc ε hε
  obtain ⟨N, hN⟩ := hφ δ hδ
  refine ⟨N, fun n hn x => ?_⟩
  have := hclose (hN n hn x)
  rwa [dist_comm, dist_eq_norm] at this
theorem exists_countable_uniform_approx
    (hc : Measures.CompactMetricProbability.CompactMetricProbabilityFacts) (X : Type)
    [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] :
    ∃ s : ℕ+ → X → ℂ, (∀ k, Continuous (s k)) ∧
      ∀ f : X → ℂ, Continuous f → ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x, ‖f x - s k x‖ < ε := by
  obtain ⟨⟨-, -, hsep⟩, -⟩ := hc X
  obtain ⟨s, hs⟩ := exists_dense_pnat_seq hsep
  refine ⟨fun k => s k, fun k => (s k).continuous, fun f hf ε hε => ?_⟩
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := hs.exists_dist_lt (⟨f, hf⟩ : C(X, ℂ)) hε
  refine ⟨k, fun x => ?_⟩
  have := (ContinuousMap.dist_lt_iff hε).1 hk x
  rwa [dist_eq_norm] at this
theorem compact_metrizable_probMeasure
    (hc : Measures.CompactMetricProbability.CompactMetricProbabilityFacts) (X : Type)
    [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] :
    CompactSpace (ProbMeasure X) ∧ TopologicalSpace.MetrizableSpace (ProbMeasure X) := by
  obtain ⟨⟨-, -, hsep⟩, -, -, -, hext⟩ := hc X
  obtain ⟨s, hs⟩ := exists_dense_pnat_seq hsep
  obtain ⟨⟨d, -, htop⟩, hcpt, -⟩ := hext s hs
  refine ⟨hcpt, ?_⟩
  have hm : @TopologicalSpace.MetrizableSpace (ProbMeasure X) d.toUniformSpace.toTopologicalSpace :=
    inferInstance
  exact htop ▸ hm
theorem dense_continuous_Lp1
    (hc : Measures.CompactMetricProbability.CompactMetricProbabilityFacts) (X : Type)
    [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : ProbMeasure X) :
    Dense {g : μ.Lp1 | ∃ f : C(X, ℂ), (g : X → ℂ) =ᵐ[μ.toMeasure] f} :=
  ((hc X).2.1 μ).1.mono (by
    rintro _ ⟨f, rfl⟩
    exact ⟨f, ContinuousMap.coeFn_toLp _ f⟩)
theorem dense_continuous_Lp2
    (hc : Measures.CompactMetricProbability.CompactMetricProbabilityFacts) (X : Type)
    [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : ProbMeasure X) :
    Dense {g : μ.Lp2 | ∃ f : C(X, ℂ), (g : X → ℂ) =ᵐ[μ.toMeasure] f} :=
  ((hc X).2.1 μ).2.mono (by
    rintro _ ⟨f, rfl⟩
    exact ⟨f, ContinuousMap.coeFn_toLp _ f⟩)
theorem probMeasure_ext_of_dense
    (hc : Measures.CompactMetricProbability.CompactMetricProbabilityFacts) (X : Type)
    [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set (X → ℂ))
    (hA : IsUniformlyDenseIn A {f | Continuous f}) (μ ν : ProbMeasure X)
    (h : ∀ f ∈ A, μ.eval f = ν.eval f) : μ = ν := by
  obtain ⟨-, -, -, hd, -⟩ := hc X
  refine hd {g : C(X, ℂ) | (g : X → ℂ) ∈ A} ?_ μ ν fun f hf => h _ hf
  rw [Metric.dense_iff]
  intro f ε hε
  obtain ⟨h', hh', hlt⟩ := hA.2 f f.continuous ε hε
  let g : C(X, ℂ) := ⟨h', hA.1 hh'⟩
  refine ⟨g, ?_, hh'⟩
  rw [Metric.mem_ball, dist_comm]
  refine lt_of_le_of_lt ?_ hlt
  refine (ContinuousMap.dist_le (Real.iSup_nonneg fun _ => norm_nonneg _)).2 fun x => ?_
  rw [dist_eq_norm]
  exact norm_le_uniformSup (f - g) x
end Compact
section Cubes
variable (D : Setup)
theorem scaledCube_isBounded (j : ℕ) : Bornology.IsBounded (scaledCube D j) := by
  have hpi : scaledCube D j = Set.pi univ fun _ => Icc (D.mesh * -(j : ℝ)) (D.mesh * (j : ℝ)) := by
    ext x
    simp only [scaledCube, Set.mem_ofPred_eq, Set.mem_pi, mem_univ, true_implies]
  rw [hpi]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).isBounded
theorem scaledCube_mono {i j : ℕ} (hij : i ≤ j) : scaledCube D i ⊆ scaledCube D j := by
  intro x hx μ
  have hpos := D.mesh_pos
  have hle : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hm : D.mesh * (i : ℝ) ≤ D.mesh * (j : ℝ) := mul_le_mul_of_nonneg_left hle hpos.le
  obtain ⟨h₁, h₂⟩ := hx μ
  constructor <;> nlinarith
theorem exists_mem_scaledCube (x : AmbientSpace) : ∃ N : ℕ, x ∈ scaledCube D N := by
  obtain ⟨N, hN⟩ := exists_nat_ge ((∑ μ, |x μ|) / D.mesh)
  refine ⟨N, fun μ => ?_⟩
  have h₁ : |x μ| ≤ ∑ μ, |x μ| :=
    Finset.single_le_sum (f := fun μ => |x μ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ μ)
  have h₂ : ∑ μ, |x μ| ≤ D.mesh * (N : ℝ) := (div_le_iff₀' D.mesh_pos).1 hN
  obtain ⟨h₃, h₄⟩ := abs_le.1 (h₁.trans h₂)
  exact ⟨by linarith, h₄⟩
theorem eventually_link_mem (ℓ : Link D.mesh) :
    ∃ N : ℕ, ∀ n, N ≤ n → ℓ ∈ linksWithin (scaledCube D n) := by
  obtain ⟨N₁, h₁⟩ := exists_mem_scaledCube D (ℓ.initial : AmbientSpace)
  obtain ⟨N₂, h₂⟩ := exists_mem_scaledCube D (ℓ.terminal : AmbientSpace)
  exact ⟨max N₁ N₂, fun n hn =>
    ⟨scaledCube_mono D (le_of_max_le_left hn) h₁, scaledCube_mono D (le_of_max_le_right hn) h₂⟩⟩
open Classical in
theorem truncate_apply {a : ℝ} (S : Set AmbientSpace) (U : GaugeField a) (ℓ : Link a) :
    truncate S U ℓ = if ℓ ∈ linksWithin S then U ℓ else 1 :=
  rfl
theorem norm_specialUnitary (g : Matrices.ComplexMatrix2.specialUnitary) :
    ‖(g : Matrices.ComplexMatrix2)‖ = 1 :=
  CStarRing.norm_of_mem_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
theorem fieldDist_truncate_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ U, D.fieldDist (truncate (scaledCube D n) U) U < δ := by
  have hsum : Summable fun k : ℕ+ => (2 : ℝ)⁻¹ ^ (k : ℕ) * 2 :=
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      PNat.coe_injective).mul_right 2
  obtain ⟨T, hT⟩ := summable_iff_vanishing_norm.1 hsum (δ / 2) (by positivity)
  choose Nℓ hNℓ using fun k : ℕ+ => eventually_link_mem D (D.linkEnum k).1
  refine ⟨T.sup Nℓ, fun n hn U => ?_⟩
  have hzero : ∀ k ∈ T, (2 : ℝ)⁻¹ ^ (k : ℕ) * Matrices.ComplexMatrix2.operatorNorm
      ((truncate (scaledCube D n) U (D.linkEnum k).1 : Matrices.ComplexMatrix2) -
        (U (D.linkEnum k).1 : Matrices.ComplexMatrix2)) = 0 := by
    intro k hk
    have hmem := hNℓ k n ((Finset.le_sup hk).trans hn)
    rw [truncate_apply, if_pos hmem, sub_self]
    simp
  have hle : ∀ k : ℕ+, (2 : ℝ)⁻¹ ^ (k : ℕ) * Matrices.ComplexMatrix2.operatorNorm
      ((truncate (scaledCube D n) U (D.linkEnum k).1 : Matrices.ComplexMatrix2) -
        (U (D.linkEnum k).1 : Matrices.ComplexMatrix2)) ≤ (2 : ℝ)⁻¹ ^ (k : ℕ) * 2 := by
    intro k
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sub_le _ _).trans ?_
    rw [norm_specialUnitary, norm_specialUnitary]
    norm_num
  refine lt_of_le_of_lt (tsum_le_of_sum_le' (by positivity) fun s => ?_) (half_lt_self hδ)
  rw [← Finset.sum_subset (Finset.sdiff_subset (s := s) (t := T)) fun k hks hk =>
    hzero k (by simpa [hks] using hk)]
  refine (Finset.sum_le_sum fun k _ => hle k).trans ?_
  exact ((le_abs_self _).trans_lt (hT (s \ T) Finset.sdiff_disjoint)).le
theorem comp_truncate_mem (hr : ObservableRegions.Statement) {f : GaugeField D.mesh → ℂ}
    (hf : Continuous f) (n : ℕ) :
    f ∘ truncate (scaledCube D n) ∈ continuousLocalFunctions D.mesh := by
  obtain ⟨-, -, -, hobs, -⟩ := hr D (scaledCube D n) (scaledCube D n)
  obtain ⟨hcont, ⟨hob, hmeas⟩, -⟩ := hobs ⟨f, hf⟩
  exact ⟨hob, ⟨scaledCube D n, scaledCube_isBounded D n, hmeas⟩, hcont⟩
theorem exists_subalgebra_local (hr : ObservableRegions.Statement) :
    ∃ A : NonUnitalSubalgebra ℂ (GaugeField D.mesh → ℂ),
      (A : Set (GaugeField D.mesh → ℂ)) = continuousLocalFunctions D.mesh := by
  have hpair : ∀ f ∈ continuousLocalFunctions D.mesh, ∀ g ∈ continuousLocalFunctions D.mesh,
      f + g ∈ continuousLocalFunctions D.mesh ∧ f * g ∈ continuousLocalFunctions D.mesh := by
    rintro f ⟨hof, ⟨S, hS, hmf⟩, hcf⟩ g ⟨hog, ⟨S', hS', hmg⟩, hcg⟩
    obtain ⟨-, -, ⟨-, h₁, -, -⟩, -, -⟩ := hr D S (S ∪ S')
    obtain ⟨-, -, ⟨-, h₂, -, -⟩, -, -⟩ := hr D S' (S ∪ S')
    obtain ⟨-, -, ⟨⟨-, hadd, -, -⟩, -, -, -⟩, -, -⟩ := hr D (S ∪ S') ∅
    obtain ⟨hs, hp⟩ := hadd f (h₁ subset_union_left ⟨hof, hmf⟩) g (h₂ subset_union_right ⟨hog, hmg⟩)
    exact ⟨⟨hs.1, ⟨S ∪ S', hS.union hS', hs.2⟩, hcf.add hcg⟩,
      ⟨hp.1, ⟨S ∪ S', hS.union hS', hp.2⟩, hcf.mul hcg⟩⟩
  have hzero : (0 : GaugeField D.mesh → ℂ) ∈ continuousLocalFunctions D.mesh := by
    obtain ⟨-, -, ⟨⟨hconst, -, -, -⟩, -, -, -⟩, -, -⟩ := hr D ∅ ∅
    have h0 := hconst 0
    exact ⟨h0.1, ⟨∅, Bornology.isBounded_empty, h0.2⟩, continuous_const⟩
  have hsmul : ∀ (c : ℂ) (f : GaugeField D.mesh → ℂ), f ∈ continuousLocalFunctions D.mesh →
      c • f ∈ continuousLocalFunctions D.mesh := by
    rintro c f ⟨hof, ⟨S, hS, hmf⟩, hcf⟩
    obtain ⟨-, -, ⟨⟨-, -, hs, -⟩, -, -, -⟩, -, -⟩ := hr D S ∅
    have hc' := hs c f ⟨hof, hmf⟩
    exact ⟨hc'.1, ⟨S, hS, hc'.2⟩, hcf.const_smul c⟩
  exact ⟨{ carrier := continuousLocalFunctions D.mesh
           add_mem' := fun hf hg => (hpair _ hf _ hg).1
           zero_mem' := hzero
           mul_mem' := fun hf hg => (hpair _ hf _ hg).2
           smul_mem' := fun c _ hf => hsmul c _ hf }, rfl⟩
end Cubes
theorem topologyDensity_of
    (hc : Measures.CompactMetricProbability.CompactMetricProbabilityFacts)
    (hr : ObservableRegions.Statement) (D : Setup) : TopologyDensity D := by
  obtain ⟨⟨⟨d, hdist, htop⟩, hcpt, -⟩, -⟩ := hr D ∅ ∅
  have hmetrizable : TopologicalSpace.MetrizableSpace (GaugeField D.mesh) := by
    have hm : @TopologicalSpace.MetrizableSpace (GaugeField D.mesh)
        d.toUniformSpace.toTopologicalSpace := inferInstance
    rw [htop] at hm
    exact hm
  have hgeneral : (∀ f : GaugeField D.mesh → ℂ, Continuous f → ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ x, ‖f x - f (truncate (scaledCube D N) x)‖ < ε) ∧
      (∃ s : ℕ+ → GaugeField D.mesh → ℂ, (∀ k, Continuous (s k)) ∧
        ∀ f : GaugeField D.mesh → ℂ, Continuous f → ∀ ε : ℝ, 0 < ε →
          ∃ k, ∀ x, ‖f x - s k x‖ < ε) ∧
      (CompactSpace (ProbMeasure (GaugeField D.mesh)) ∧
        TopologicalSpace.MetrizableSpace (ProbMeasure (GaugeField D.mesh))) ∧
      (∀ μ : ProbMeasure (GaugeField D.mesh), Dense {g : μ.Lp1 |
        ∃ f : C(GaugeField D.mesh, ℂ), (g : GaugeField D.mesh → ℂ) =ᵐ[μ.toMeasure] f}) ∧
      (∀ μ : ProbMeasure (GaugeField D.mesh), Dense {g : μ.Lp2 |
        ∃ f : C(GaugeField D.mesh, ℂ), (g : GaugeField D.mesh → ℂ) =ᵐ[μ.toMeasure] f}) ∧
      (∀ A : Set (GaugeField D.mesh → ℂ), IsUniformlyDenseIn A {f | Continuous f} →
        ∀ μ ν : ProbMeasure (GaugeField D.mesh), (∀ f ∈ A, μ.eval f = ν.eval f) → μ = ν) := by
    let dm : MetricSpace (GaugeField D.mesh) := d.replaceTopology htop.symm
    have hcm : @CompactSpace (GaugeField D.mesh) dm.toUniformSpace.toTopologicalSpace := hcpt
    have hbm : @BorelSpace (GaugeField D.mesh) dm.toUniformSpace.toTopologicalSpace _ := ⟨rfl⟩
    refine ⟨fun f hf ε hε => ?_, exists_countable_uniform_approx hc (GaugeField D.mesh),
      compact_metrizable_probMeasure hc (GaugeField D.mesh),
      dense_continuous_Lp1 hc (GaugeField D.mesh),
      dense_continuous_Lp2 hc (GaugeField D.mesh), probMeasure_ext_of_dense hc (GaugeField D.mesh)⟩
    obtain ⟨N, hN⟩ := exists_uniform_approx_comp (fun n => truncate (scaledCube D n))
      (fun δ hδ => by
        obtain ⟨N, hN⟩ := fieldDist_truncate_lt D hδ
        exact ⟨N, fun n hn U => lt_of_eq_of_lt (hdist _ _) (hN n hn U)⟩) hf hε
    exact ⟨N, hN N le_rfl⟩
  obtain ⟨hcut, ⟨s, hsc, hs⟩, ⟨hprobc, hprobm⟩, hLp1, hLp2, hext⟩ := hgeneral
  have hdense : ∀ f : GaugeField D.mesh → ℂ, Continuous f → ∀ ε : ℝ, 0 < ε →
      ∃ (k : ℕ+) (N : ℕ), uniformSup (f - s k ∘ truncate (scaledCube D N)) < ε := by
    intro f hf ε hε
    obtain ⟨N, hN⟩ := hcut f hf (ε / 2) (by positivity)
    obtain ⟨k, hk⟩ := hs f hf (ε / 4) (by positivity)
    refine ⟨k, N, lt_of_le_of_lt (uniformSup_le (c := 3 * ε / 4) (by positivity) fun x => ?_)
      (by linarith)⟩
    have htri := norm_add_le (f x - f (truncate (scaledCube D N) x))
      (f (truncate (scaledCube D N) x) - s k (truncate (scaledCube D N) x))
    have hsplit : f x - s k (truncate (scaledCube D N) x) =
        (f x - f (truncate (scaledCube D N) x)) +
        (f (truncate (scaledCube D N) x) - s k (truncate (scaledCube D N) x)) := by ring
    show ‖f x - s k (truncate (scaledCube D N) x)‖ ≤ _
    rw [hsplit]
    linarith [hN x, hk (truncate (scaledCube D N) x)]
  have hA : Set.range (fun p : ℕ+ × ℕ => s p.1 ∘ truncate (scaledCube D p.2)) ⊆
      continuousLocalFunctions D.mesh := by
    rintro _ ⟨p, rfl⟩
    exact comp_truncate_mem D hr (hsc p.1) p.2
  have hd : ∀ f ∈ {f : GaugeField D.mesh → ℂ | Continuous f}, ∀ ε : ℝ, 0 < ε →
      ∃ g ∈ Set.range (fun p : ℕ+ × ℕ => s p.1 ∘ truncate (scaledCube D p.2)),
        uniformSup (f - g) < ε := by
    intro f hf ε hε
    obtain ⟨k, N, hlt⟩ := hdense f hf ε hε
    exact ⟨_, ⟨(k, N), rfl⟩, hlt⟩
  exact
    { compact := hcpt
      metrizable := hmetrizable
      compact_prob := hprobc
      metrizable_prob := hprobm
      exists_nonUnitalSubalgebra := exists_subalgebra_local D hr
      dense_local := ⟨fun f hf => hf.2.2, fun f hf ε hε => by
        obtain ⟨N, hN⟩ := hcut f hf (ε / 2) (by positivity)
        exact ⟨f ∘ truncate (scaledCube D N), comp_truncate_mem D hr hf N, lt_of_le_of_lt
          (uniformSup_le (by positivity) fun x => (hN x).le) (half_lt_self hε)⟩⟩
      countable_dense := ⟨Set.range s, countable_range s, by
        rintro _ ⟨k, rfl⟩
        exact hsc k, fun f hf ε hε => by
        obtain ⟨k, hk⟩ := hs f hf (ε / 2) (by positivity)
        exact ⟨s k, ⟨k, rfl⟩, lt_of_le_of_lt
          (uniformSup_le (by positivity) fun x => (hk x).le) (half_lt_self hε)⟩⟩
      countable_dense_local := ⟨_, countable_range _,
        ⟨hA, fun f hf ε hε => hd f hf.2.2 ε hε⟩, ⟨fun f hf => (hA hf).2.2, hd⟩⟩
      dense_Lp1 := hLp1
      dense_Lp2 := hLp2
      ext_of_dense := hext
      countable_finite_linkSets := Set.Countable.ofPred_finite
      countable_points := inferInstance }
theorem topologyDensityHolds
    (hc : Measures.CompactMetricProbability.CompactMetricProbabilityFacts)
    (hr : ObservableRegions.Statement) : TopologyDensityHolds := by apply _root_.YangMills.Construction.LatticePhases.TopologyDensityProof.topologyDensity_of <;> assumption
end YangMills.Construction.LatticePhases.TopologyDensityProof
