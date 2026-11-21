import YangMills.Construction.InfiniteLattice.EquationOfABondSetUnderTheTorusMeasure
import YangMills.Construction.InfiniteLattice.FactsOfOneLatticeAtOneSpacing
import YangMills.Construction.InfiniteLattice.GibbsStatesByWindowsAndPeriodGroups
import YangMills.Construction.InfiniteLattice.OperatorsOfTheWilsonSpecification
import YangMills.Construction.InfiniteLattice.SpecificationDensityReadsTheBoundary
import YangMills.Construction.InfiniteLattice.SpecificationInTheTorusMeasuresAndTheirLimitPoints
import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsProperty
import YangMills.Construction.InfiniteLattice.TorusMeasureIsAnInvariantProbabilityMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter YangMills.Construction.InfiniteLattice YangMills.Construction.GibbsAtFixedSpacing
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace FixedSpacing
namespace TorusSpecification
variable (D : Setup)
theorem conditionalKernel_eq_conditionalAverage (𝓛 : LinkWindow D.mesh) (F : D.Fields → ℂ) :
    D.conditionalKernel 𝓛 F = 𝓛.conditionalAverage D.mesh_pos D.β F := by
  funext U
  have hE : ∀ W : D.Fields, D.localAction 𝓛 W = -D.β * 𝓛.windowAction W := fun _ => rfl
  simp only [Setup.conditionalKernel, LinkWindow.conditionalAverage, Setup.conditionalDensity,
    Setup.localPartition, hE]
  rw [← integral_div]
  refine integral_congr_ae (ae_of_all _ fun V => ?_)
  simp only [Complex.ofReal_div, mul_div_assoc]
def liftedGibbsProb (hT : LiftedGibbsIsInvariantProbability) (n : ℕ+) : BorelProb D.mesh :=
  (Subtype.mk (D.withExponent n).liftedGibbs (hT (D.withExponent n)).1 :
    {ν : Measure (GaugeField D.mesh) // IsProbabilityMeasure ν})
theorem torusLimitsSubsequential (hF : BasicFacts)
    (hT : LiftedGibbsIsInvariantProbability) :
    D.TorusLimitsSubsequential := by
  intro n hn
  obtain ⟨-, -, -, ⟨-, -, -, -, hlim, -⟩, -, -⟩ := hF D
  obtain ⟨ρ', φ, hφ, -, hconv⟩ := hlim (fun i => liftedGibbsProb D hT (n i))
  refine ⟨φ, fun i => liftedGibbsProb D hT (n (φ i)), ρ', hφ, fun i => rfl, ?_, hconv⟩
  exact ⟨n ∘ φ, fun i => liftedGibbsProb D hT (n (φ i)), ρ', hn.comp hφ.tendsto_atTop, fun _ => rfl, rfl,
    hconv⟩
theorem tendsto_side_withExponent :
    Tendsto (fun i : ℕ => (D.withExponent i.succPNat).side) atTop atTop := by
  have hL : (1 : ℝ) < D.L := by
    have h := D.admissible.2
    exact_mod_cast (by omega : 1 < D.L)
  have h1 : Tendsto (fun i : ℕ => (D.L : ℝ) ^ (i + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hL).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun i : ℕ => 2 * (D.L : ℝ) ^ (i + 1)) atTop atTop :=
    h1.const_mul_atTop (by norm_num)
  refine h2.congr fun i => ?_
  simp [Setup.side, Setup.withExponent, PeriodicLattice.torusSide]
theorem isBoundedObservable_of_continuous (hF : BasicFacts) {F : D.Fields → ℂ}
    (hc : Continuous F) : IsBoundedObservable F := by
  obtain ⟨-, ⟨hcpt, -⟩, -⟩ := hF D
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨hc.measurable, C, fun U => hC U (mem_univ U)⟩
theorem integral_eq_complexExpectation {n : ℕ+} (ρ : BorelProb D.mesh)
    (hρ : ρ.1 = (D.withExponent n).liftedGibbs) (G : D.Fields → ℂ) :
    ρ.integral G =
      YangMills.Construction.Probability.complexExpectation (D.withExponent n).liftedGibbs G := by
  change ∫ U, G U ∂ρ.1 = _
  rw [hρ]
  rfl
theorem limit_preserves_kernel_on_local (hF : BasicFacts)
    (hD : ConditionalDensityDependsOnRim.Statement)
    (hB : KernelPreservesTorusExpectation.Statement)
    {n : ℕ → ℕ+} {ρ : ℕ → BorelProb D.mesh} {ρ' : BorelProb D.mesh}
    (hn : Tendsto (fun i => (D.withExponent (n i)).side) atTop atTop)
    (hρ : ∀ i, (ρ i).1 = (D.withExponent (n i)).liftedGibbs) (hc : BorelProb.TendstoWeak ρ ρ')
    (𝓛 : LinkWindow D.mesh) {F : D.Fields → ℂ} (hFl : F ∈ finiteLinkFunctions D.mesh) :
    ρ'.integral (D.conditionalKernel 𝓛 F) = ρ'.integral F := by
  obtain ⟨-, -, ⟨hsub, -⟩, -⟩ := hF D
  obtain ⟨𝓕, hread⟩ := id hFl
  have hS : ((𝓛.links : Set (Link D.mesh)) ∪ 𝓕).Finite := (Finset.finite_toSet _).union hread.1
  obtain ⟨r₀, hr₀⟩ := (hS.image fun b => max (linfNorm (b.initial : AmbientSpace))
    (linfNorm (b.terminal : AmbientSpace))).bddAbove
  set r := max r₀ 0 with hr
  have hr0 : 0 ≤ r := le_max_right _ _
  have hb : ∀ b ∈ (𝓛.links : Set (Link D.mesh)) ∪ 𝓕,
      (b.initial : AmbientSpace) ∈ closedCube r ∧ (b.terminal : AmbientSpace) ∈ closedCube r := by
    intro b hb
    have h := (hr₀ (mem_image_of_mem _ hb)).trans (le_max_left r₀ 0)
    exact ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩
  have hev : ∀ᶠ i in atTop, (ρ i).integral (D.conditionalKernel 𝓛 F) = (ρ i).integral F := by
    filter_upwards [hn.eventually_gt_atTop (2 * (r + D.mesh))] with i hi
    rw [integral_eq_complexExpectation D (ρ i) (hρ i), integral_eq_complexExpectation D (ρ i) (hρ i)]
    exact hB (D.withExponent (n i)) 𝓛 𝓕 F hread r hr0 hb (by
      change r + D.mesh < (D.withExponent (n i)).side / 2
      linarith)
  have hkl : D.conditionalKernel 𝓛 F ∈ finiteLinkFunctions D.mesh := (hD D 𝓛).2.2.1 F hFl
  exact tendsto_nhds_unique_of_eventuallyEq (hc _ (hsub hkl)) (hc _ (hsub hFl)) hev
theorem limit_isShiftInvariant (hF : BasicFacts)
    (hT : LiftedGibbsIsInvariantProbability)
    {n : ℕ → ℕ+} {ρ : ℕ → BorelProb D.mesh} {ρ' : BorelProb D.mesh}
    (hρ : ∀ i, (ρ i).1 = (D.withExponent (n i)).liftedGibbs) (hc : BorelProb.TendstoWeak ρ ρ') :
    IsShiftInvariant ρ'.1 := by
  intro v
  obtain ⟨-, -, ⟨hsub, -, -, -, huniq⟩, -⟩ := hF D
  have hτ : Continuous (shift v).pullbackField :=
    LatticeSymmetry.continuous_pullbackField _
  have : IsProbabilityMeasure ρ'.1 := ρ'.2
  have hprob : IsProbabilityMeasure (ρ'.1.map (shift v).pullbackField) :=
    Measure.isProbabilityMeasure_map hτ.measurable.aemeasurable
  let ρ'' : BorelProb D.mesh := (Subtype.mk (ρ'.1.map (shift v).pullbackField) hprob :
    {ν : Measure (GaugeField D.mesh) // IsProbabilityMeasure ν})
  have hint : ∀ A : D.Fields → ℂ, Measurable A →
      ρ''.integral A = ρ'.integral ((shift v).actOn A) := fun A hA =>
    integral_map hτ.measurable.aemeasurable hA.aestronglyMeasurable
  have heq : ρ'' = ρ' := by
    refine huniq _ _ fun F hFl => ?_
    have hcF : Continuous F := hsub hFl
    have hcτ : Continuous ((shift v).actOn F) := hcF.comp hτ
    rw [hint F hcF.measurable]
    have hev : ∀ i, (ρ i).integral ((shift v).actOn F) = (ρ i).integral F := by
      intro i
      rw [integral_eq_complexExpectation D (ρ i) (hρ i),
        integral_eq_complexExpectation D (ρ i) (hρ i)]
      exact (hT (D.withExponent (n i))).2 v F (isBoundedObservable_of_continuous D hF hcF)
    exact tendsto_nhds_unique_of_eventuallyEq (hc _ hcτ) (hc _ hcF) (Eventually.of_forall hev)
  intro A hA
  have h := hint A hA.1
  rw [heq] at h
  exact h.symm
theorem mem_finiteLinkFunctions {F : D.Fields → ℂ}
    (hFl : F ∈ YangMills.Construction.FieldsAtSpacing.continuousFiniteLinkFunctions D.mesh) :
    F ∈ finiteLinkFunctions D.mesh := by
  obtain ⟨-, 𝓕, hfin, hpos, f, hf, hFU⟩ := hFl
  exact ⟨𝓕, hfin, hpos, f, hf, hFU⟩
end TorusSpecification
open TorusSpecification in
theorem TorusSpecification.holds
    (hF : BasicFacts)
    (hD : ConditionalDensityDependsOnRim.Statement)
    (hB : KernelPreservesTorusExpectation.Statement)
    (hT : LiftedGibbsIsInvariantProbability)
    (hOp : ConditionalAverageProperties.claim)
    (hThree : GibbsCharacterizations) :
    TorusSpecification.Statement := by
  intro D
  have hsides := torusLimitsSubsequential D hF hT
  have hforms : ∀ ν ∈ D.torusLimits, D.SatisfiesDLR ν ∧ IsShiftInvariant ν ∧
      IsGibbs D.β ν := by
    rintro ν ⟨n, ρ, ρ', hn, hρ, rfl, hc⟩
    have hloc : ∀ (W : LinkWindow D.mesh) {F : D.Fields → ℂ},
        F ∈ finiteLinkFunctions D.mesh →
        ρ'.integral (D.conditionalKernel W F) = ρ'.integral F :=
      fun W _ hFl => limit_preserves_kernel_on_local D hF hD hB hn hρ hc W hFl
    have hTFAE := hThree D.mesh D.mesh_pos D.β D.β_pos ρ'
    have hthird : ∀ (W : LinkWindow D.mesh),
        ∀ F ∈ YangMills.Construction.FieldsAtSpacing.continuousFiniteLinkFunctions D.mesh,
          ρ'.integral (W.conditionalAverage D.mesh_pos D.β F) = ρ'.integral F := by
      intro W F hFl
      rw [← conditionalKernel_eq_conditionalAverage]
      exact hloc W (mem_finiteLinkFunctions D hFl)
    have hsecond := (hTFAE.out 2 1).mp hthird
    have hgibbs := (hTFAE.out 2 0).mp hthird
    refine ⟨fun 𝓛 => ⟨fun F hFl => hloc 𝓛 hFl, fun F hFo => ?_⟩,
      limit_isShiftInvariant D hF hT hρ hc, hgibbs⟩
    have hobs := (hOp D.mesh D.mesh_pos D.β D.β_pos 𝓛 F F hFo hFo).2.1.1
    rw [conditionalKernel_eq_conditionalAverage]
    exact ⟨hobs, hsecond 𝓛 F hFo⟩
  obtain ⟨φ, ρ, ρ', hφ, hρ, hmem, hc⟩ := hsides (fun i => i.succPNat) (tendsto_side_withExponent D)
  refine ⟨fun 𝓛 => ?_, ⟨ρ'.1, hmem⟩, hsides, fun ν hν => ⟨(hforms ν hν).1, (hforms ν hν).2.1⟩,
    (hT D).2, fun ν hν => ⟨(hforms ν hν).2.2, ⊤, inferInstance, fun v _ => (hforms ν hν).2.1 v⟩⟩
  obtain ⟨h1, h2, h3, h4⟩ := hD D 𝓛
  exact ⟨h1, h2, ⟨h3, h4⟩, fun 𝓕 F hread r hr hb hlt => hB D 𝓛 𝓕 F hread r hr hb hlt⟩
end FixedSpacing
end YangMills.Construction
