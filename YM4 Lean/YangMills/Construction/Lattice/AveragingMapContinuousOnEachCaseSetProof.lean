import YangMills.Construction.Matrices.LogarithmicChartsOfASpaceOfConfigurationsProof
import YangMills.Construction.Averaging.AveragingMapRealAnalyticAtSmallRadiiProof
import YangMills.Construction.Lattice.AveragingMapContinuousOnEachCaseSet
import YangMills.Construction.Matrices.UnitaryLogarithmClosedForm
import YangMills.Construction.SourcesOnAFlow.MeanInAPeriodicExtensionProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice.BlockAverageContinuity
variable {L m : ℕ} {j j' : ℤ}
theorem continuous_pathHolonomy (Γ : List (Bond L m j')) :
    Continuous fun U : Bond L m j' → Matrices.ComplexMatrix2 => pathHolonomy U Γ := by apply _root_.YangMills.Construction.PeriodicExtension.continuous_pathHolonomy <;> assumption
theorem pathHolonomy_mem_compactGaugeGroup {U : Bond L m j' → Matrices.ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m j') (Γ : List (Bond L m j')) :
    pathHolonomy U Γ ∈ compactGaugeGroup := by
  induction Γ with
  | nil => simp [pathHolonomy]
  | cons b Γ ih =>
    have e : pathHolonomy U (b :: Γ) = U b * pathHolonomy U Γ := by simp [pathHolonomy]
    rw [e]
    exact (Matrices.ComplexMatrix2.specialUnitary).mul_mem (hU.1 b (mem_univ b)) ih
theorem inv_eq_star_of_mem {X : Matrices.ComplexMatrix2} (hX : X ∈ compactGaugeGroup) :
    X⁻¹ = star X := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.inv_eq_star_of_mem <;> assumption
theorem inv_mem_compactGaugeGroup {X : Matrices.ComplexMatrix2} (hX : X ∈ compactGaugeGroup) :
    X⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.DeltaSharedProofs.p3037 <;> assumption
theorem inv_inv_of_mem_compactGaugeGroup {X : Matrices.ComplexMatrix2}
    (hX : X ∈ compactGaugeGroup) : (X⁻¹)⁻¹ = X := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_inv_of_mem_specialUnitary <;> assumption
theorem continuousOn_pathHolonomy_inv (Γ : List (Bond L m j')) :
    ContinuousOn (fun U : Bond L m j' → Matrices.ComplexMatrix2 => (pathHolonomy U Γ)⁻¹)
      (compactGaugeFields L m j') :=
  (continuous_star.comp (continuous_pathHolonomy Γ)).continuousOn.congr fun _ hU =>
    inv_eq_star_of_mem (pathHolonomy_mem_compactGaugeGroup hU Γ)
theorem continuousOn_contourCrossingDefect (c : Bond L m j) (x : Site L m j')
    (σ : AxisOrdering c.source x) (σ' : AxisOrdering c.target (shiftAcross c x)) :
    ContinuousOn
      (fun U : Bond L m j' → Matrices.ComplexMatrix2 => contourCrossingDefect U c x σ σ')
      (compactGaugeFields L m j') := by
  unfold contourCrossingDefect parallelTransport
  exact (((continuous_pathHolonomy _).continuousOn.mul
    (continuous_pathHolonomy _).continuousOn).mul
    (continuousOn_pathHolonomy_inv _)).mul (continuousOn_pathHolonomy_inv _)
theorem contourCrossingDefect_mem {U : Bond L m j' → Matrices.ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m j') (c : Bond L m j) (x : Site L m j')
    (σ : AxisOrdering c.source x) (σ' : AxisOrdering c.target (shiftAcross c x)) :
    contourCrossingDefect U c x σ σ' ∈ compactGaugeGroup := by
  unfold contourCrossingDefect parallelTransport
  exact (Matrices.ComplexMatrix2.specialUnitary).mul_mem
    ((Matrices.ComplexMatrix2.specialUnitary).mul_mem
      ((Matrices.ComplexMatrix2.specialUnitary).mul_mem
        (pathHolonomy_mem_compactGaugeGroup hU _) (pathHolonomy_mem_compactGaugeGroup hU _))
      (inv_mem_compactGaugeGroup (pathHolonomy_mem_compactGaugeGroup hU _)))
    (inv_mem_compactGaugeGroup (pathHolonomy_mem_compactGaugeGroup hU _))
theorem continuous_matExp :
    Continuous (Matrices.ComplexMatrix2.matExp :
      Matrices.ComplexMatrix2 → Matrices.ComplexMatrix2) := by
  let +nondep : NormedAlgebra ℚ Matrices.ComplexMatrix2 :=
    .restrictScalars ℚ ℂ Matrices.ComplexMatrix2
  exact NormedSpace.exp_continuous
theorem continuousOn_const_smul_of_continuousOn {X : Type*} [TopologicalSpace X] {S : Set X}
    {f : X → Matrices.ComplexMatrix2} (a : ℂ) (h : ContinuousOn f S) :
    ContinuousOn (fun x => a • f x) S :=
  (continuous_const_smul a).comp_continuousOn h
theorem continuousOn_logAverageValue [Finite (Site L m j')]
    (hI : ContinuousOn Matrices.ComplexMatrix2.unitaryLog
      Matrices.ComplexMatrix2.unitaryLogDomain) (c : Bond L m j) :
    ContinuousOn (fun U : Bond L m j' → Matrices.ComplexMatrix2 => logAverageValue U c)
      {U | U ∈ compactGaugeFields L m j' ∧ NoCrossingDefectIsNegOne U c} := by
  have hY : ∀ x ∈ sitesInBlock j' c.source, ∀ σ σ',
      ContinuousOn (fun U : Bond L m j' → Matrices.ComplexMatrix2 =>
          Matrices.ComplexMatrix2.unitaryLog (contourCrossingDefect U c x σ σ'))
        {U | U ∈ compactGaugeFields L m j' ∧ NoCrossingDefectIsNegOne U c} :=
    fun x hx σ σ' => hI.comp
      ((continuousOn_contourCrossingDefect c x σ σ').mono fun U hU => hU.1)
      fun U hU => ⟨contourCrossingDefect_mem hU.1 c x σ σ', hU.2 x hx σ σ'⟩
  have hfin : (sitesInBlock j' c.source).Finite := Set.toFinite _
  unfold logAverageValue parallelTransport
  refine ContinuousOn.mul ?_ (continuous_pathHolonomy _).continuousOn
  refine continuous_matExp.comp_continuousOn (continuousOn_const_smul_of_continuousOn _ ?_)
  simp_rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine continuousOn_finsetSum _ fun x hx => ?_
  have hx' := hfin.mem_toFinset.1 hx
  refine continuousOn_const_smul_of_continuousOn _ (continuousOn_finsetSum _ fun σ _ => ?_)
  exact continuousOn_const_smul_of_continuousOn _
    (continuousOn_finsetSum _ fun σ' _ => hY x hx' σ σ')
theorem continuousOn_logSeries :
    ContinuousOn Matrices.ComplexMatrix2.logSeries
      {X | Matrices.ComplexMatrix2.operatorNorm (X - 1) ≤ 1 / 5} := by
  unfold Matrices.ComplexMatrix2.logSeries
  refine ContinuousOn.neg ?_
  refine continuousOn_tsum (u := fun n : ℕ => ((1 : ℝ) / 5) ^ (n + 1)) (fun n => ?_) ?_ ?_
  · exact (Continuous.continuousOn (by fun_prop))
  · exact (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  · intro n X hX
    have hX' : ‖1 - X‖ ≤ 1 / 5 := by rw [norm_sub_rev]; exact hX
    have hc : ‖((n + 1 : ℂ))⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      have : (1 : ℝ) ≤ ‖(n + 1 : ℂ)‖ := by
        have e : ‖(n + 1 : ℂ)‖ = (n : ℝ) + 1 := by
          have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; rfl
          rw [this, Complex.norm_natCast]
          push_cast
          rfl
        rw [e]
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      exact inv_le_one_of_one_le₀ this
    calc ‖((n + 1 : ℂ))⁻¹ • (1 - X) ^ (n + 1)‖
        ≤ ‖((n + 1 : ℂ))⁻¹‖ * ‖(1 - X) ^ (n + 1)‖ := norm_smul_le _ _
      _ ≤ 1 * ‖(1 - X) ^ (n + 1)‖ := by gcongr
      _ = ‖(1 - X) ^ (n + 1)‖ := one_mul _
      _ ≤ ‖1 - X‖ ^ (n + 1) := norm_pow_le' _ (Nat.succ_pos n)
      _ ≤ (1 / 5) ^ (n + 1) := by gcongr
theorem continuousOn_of_isRealAnalyticBetween {ι κ : Type} [Fintype ι] [Fintype κ]
    {D : Set (ι → Matrices.ComplexMatrix2)}
    {f : (ι → Matrices.ComplexMatrix2) → κ → Matrices.ComplexMatrix2}
    (h : Matrices.ComplexMatrix2.IsRealAnalyticBetween
      (fun _ : ι => Matrices.ComplexMatrix2.FactorKind.group)
      (fun _ : κ => Matrices.ComplexMatrix2.FactorKind.group) D f) : ContinuousOn f D := by
  intro x hx
  obtain ⟨O, -, hD⟩ := h.1
  obtain ⟨W, g, hxW, hW, hev⟩ := h.2 x hx
  obtain ⟨F, hF, hev'⟩ := hW.2.2 x hxW
  obtain ⟨O', hO', hW'⟩ := hW.1
  have hxO' : x ∈ O' := by
    rw [hW'] at hxW
    exact hxW.1
  have hreal : ∀ y ∈ D, y ∈ Matrices.ComplexMatrix2.complexifiedProduct
      (fun _ : ι => Matrices.ComplexMatrix2.FactorKind.group) := by
    intro y hy i
    rw [hD] at hy
    exact (Matrix.mem_specialUnitaryGroup_iff.1 (hy.2 i)).2
  have hDW : ∀ᶠ y in 𝓝[D] x, y ∈ W := by
    have h₁ : ∀ᶠ y in 𝓝[D] x, y ∈ O' := nhdsWithin_le_nhds (hO'.mem_nhds hxO')
    filter_upwards [h₁, self_mem_nhdsWithin] with y hy hyD
    rw [hW']
    exact ⟨hy, hreal y hyD⟩
  have hgF : ∀ᶠ y in 𝓝[D] x, g y = F y := by
    have h₁ : ∀ᶠ y in 𝓝 x, y ∈ W → g y = F y := eventually_nhdsWithin_iff.1 hev'
    filter_upwards [nhdsWithin_le_nhds h₁, hDW] with y hy hyW
    exact hy hyW
  have hfF : ∀ᶠ y in 𝓝[D] x, f y = F y := by
    filter_upwards [hev, hgF] with y h₁ h₂
    exact h₁.trans h₂
  have hx0 : f x = F x := (hev.self_of_nhdsWithin hx).trans (hev'.self_of_nhdsWithin hxW)
  exact hF.continuousAt.continuousWithinAt.congr_of_eventuallyEq hfF hx0
theorem fieldOfPositiveValues_valuesOnPositiveBonds {U : Bond L m j' → Matrices.ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m j') :
    fieldOfPositiveValues (valuesOnPositiveBonds U) = U := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.fieldOfPositiveValues_valuesOnPositiveBonds <;> assumption
theorem continuous_valuesOnPositiveBonds :
    Continuous (valuesOnPositiveBonds : (Bond L m j' → Matrices.ComplexMatrix2) →
      PositivelyOrientedBond L m j' → Matrices.ComplexMatrix2) :=
  continuous_pi fun b => continuous_apply b.1
theorem continuousOn_of_valuesOnPositiveBonds [Fintype (PositivelyOrientedBond L m j')]
    {D : Set (Bond L m j' → Matrices.ComplexMatrix2)} (hD : D ⊆ compactGaugeFields L m j')
    {f : (Bond L m j' → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    (h : Matrices.ComplexMatrix2.IsRealAnalyticBetween
      (fun _ : PositivelyOrientedBond L m j' => Matrices.ComplexMatrix2.FactorKind.group)
      (fun _ : Fin 1 => Matrices.ComplexMatrix2.FactorKind.group) (valuesOnPositiveBonds '' D)
      fun v _ => f (fieldOfPositiveValues v)) : ContinuousOn f D := by
  have h₁ := continuousOn_of_isRealAnalyticBetween h
  have h₂ : ContinuousOn
      (fun U : Bond L m j' → Matrices.ComplexMatrix2 =>
        f (fieldOfPositiveValues (valuesOnPositiveBonds U))) D :=
    ((continuous_apply (0 : Fin 1)).comp_continuousOn h₁).comp
      continuous_valuesOnPositiveBonds.continuousOn (mapsTo_image _ _)
  refine h₂.congr fun U hU => ?_
  change f U = f (fieldOfPositiveValues (valuesOnPositiveBonds U))
  rw [fieldOfPositiveValues_valuesOnPositiveBonds (hD hU)]
theorem shiftAcross_mem_sitesInBlock {K k : ℕ} (hL : 0 < L) {c : BondAtLevel L m K (k + 1)}
    {x : SiteAtLevel L m K k} (hx : x ∈ sitesInBlock (levelDepth K k) c.source) :
    shiftAcross c x ∈ sitesInBlock (levelDepth K k) c.target := by
  have hle : levelDepth K (k + 1) ≤ levelDepth K k := by
    simp only [levelDepth]; push_cast; omega
  have hin : ((((c.target - c.source).toSublattice (levelDepth K k)) :
      SiteAtLevel L m K k) : FourTorus L m) =
      ((c.target - c.source : SiteAtLevel L m K (k + 1)) : FourTorus L m) :=
    Classical.epsilon_spec (p := fun z : SiteAtLevel L m K k =>
      (z : FourTorus L m) = ((c.target - c.source : SiteAtLevel L m K (k + 1)) : FourTorus L m))
      ⟨⟨_, sublattice_mono hL m hle (c.target - c.source).2⟩, rfl⟩
  have hco : ((shiftAcross c x : SiteAtLevel L m K k) : FourTorus L m) =
      (x : FourTorus L m) + ((c.target : FourTorus L m) - (c.source : FourTorus L m)) := by
    unfold shiftAcross
    rw [AddSubgroup.coe_add, hin]
    rfl
  refine ⟨?_, ?_⟩
  · have h1 : TorusMetric.torusSupNorm ((x : FourTorus L m) - (c.source : FourTorus L m)) ≤
        meshSize L (levelDepth K (k + 1)) / 2 := hx.1
    change TorusMetric.torusSupNorm (((shiftAcross c x : SiteAtLevel L m K k) : FourTorus L m) -
      (c.target : FourTorus L m)) ≤ meshSize L (levelDepth K (k + 1)) / 2
    rw [hco]
    have e : (x : FourTorus L m) + ((c.target : FourTorus L m) - (c.source : FourTorus L m)) -
        (c.target : FourTorus L m) = (x : FourTorus L m) - (c.source : FourTorus L m) := by abel
    rw [e]
    exact h1
  · have e : levelDepth K (k + 1) + ((1 : ℕ) : ℤ) = levelDepth K k := by
      simp only [levelDepth]; push_cast; ring
    change ((shiftAcross c x : SiteAtLevel L m K k) : FourTorus L m) ∈
      (sublattice L m (levelDepth K (k + 1) + ((1 : ℕ) : ℤ)) : Set (FourTorus L m))
    rw [e]
    exact (shiftAcross c x).2
theorem continuousOn_regularAverageValue {K k : ℕ} (hL : 0 < L)
    [Finite (Site L m (levelDepth K k))] {ω : ℝ} {c : BondAtLevel L m K (k + 1)}
    (hc : c.IsPositivelyOriented) (hC : Averaging.SmallRadius.PropertiesAtBond ω k c) :
    ContinuousOn (fun U : BondAtLevel L m K k → Matrices.ComplexMatrix2 =>
        regularAverageValue U c)
      (smallPlaquetteFields ω c) := by
  have hS : (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)) ⊆
      compactGaugeFields L m (levelDepth K k) := fun U hU => hU.1
  have : Finite (Bond L m (levelDepth K k)) :=
    Finite.of_injective (fun b : Bond L m (levelDepth K k) => (b.source, b.target))
      fun b b' hb => Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
  let _ : Fintype (PositivelyOrientedBond L m (levelDepth K k)) := Fintype.ofFinite _
  have hV : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K k) y,
        ContinuousOn (fun U : BondAtLevel L m K k → Matrices.ComplexMatrix2 =>
            meanContourHolonomy U y x)
          (smallPlaquetteFields ω c) ∧
        ContinuousOn (fun U : BondAtLevel L m K k → Matrices.ComplexMatrix2 =>
            (meanContourHolonomy U y x)⁻¹)
          (smallPlaquetteFields ω c) := fun y hy x hx =>
    ⟨continuousOn_of_valuesOnPositiveBonds hS
        (hC.realAnalytic_contourMean inferInstance y hy x hx).1,
      continuousOn_of_valuesOnPositiveBonds hS
        (hC.realAnalytic_contourMean inferInstance y hy x hx).2⟩
  have hE : ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
      ContinuousOn (fun U : BondAtLevel L m K k → Matrices.ComplexMatrix2 =>
          Matrices.ComplexMatrix2.logSeries (crossingDefect U c x))
        (smallPlaquetteFields ω c) := by
    intro x hx
    have h₁ : ContinuousOn (fun U : BondAtLevel L m K k → Matrices.ComplexMatrix2 =>
          crossingDefect U c x)
        (smallPlaquetteFields ω c) := by
      unfold crossingDefect parallelTransport
      exact ((((hV _ (Or.inl rfl) x hx).1.mul (continuous_pathHolonomy _).continuousOn).mul
        (hV _ (Or.inr rfl) _ (shiftAcross_mem_sitesInBlock hL hx)).2).mul
        ((continuousOn_pathHolonomy_inv _).mono hS))
    exact continuousOn_logSeries.comp h₁ fun U hU => (hC.crossingDefect_near hc U hU x hx).2.le
  have hfin : (sitesInBlock (levelDepth K k) c.source).Finite := Set.toFinite _
  unfold regularAverageValue parallelTransport
  refine ContinuousOn.mul ?_ (continuous_pathHolonomy _).continuousOn
  refine continuous_matExp.comp_continuousOn (continuousOn_const_smul_of_continuousOn _ ?_)
  simp_rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  exact continuousOn_finsetSum _ fun x hx => hE x (hfin.mem_toFinset.1 hx)
theorem blockAverageContinuousOnEachCaseSet_holds
    (hR : Averaging.SmallRadius.EverySmallRadiusSuffices)
    (hI : Matrices.ComplexMatrix2.UnitaryLogarithmProperties) :
    BlockAverageContinuousOnEachCaseSet := by
  intro s k hk c hc κ
  have hLpos : 0 < s.L := by have := s.isAdmissible.2; omega
  have : Finite (Site s.L s.m (levelDepth s.K k)) :=
    SeparatedSequences.BaseParameters.site_finite hLpos _ _
  have hω : Averaging.smoothingRadius s.L ∈ Ioc (0 : ℝ) (averagingRadiusCap s.L) :=
    Averaging.isSmoothingRadius_smoothingRadius s.isAdmissible.1 s.isAdmissible.2
  have hC := hR s _ hω k hk c
  have hval : ∀ U : BondAtLevel s.L s.m s.K k → Matrices.ComplexMatrix2,
      blockAverage (Averaging.smoothingRadius s.L) U c =
        blockAverageOnPositive (Averaging.smoothingRadius s.L) U c := fun U => by
    unfold blockAverage
    exact if_pos hc
  cases κ with
  | logarithmOfMeans =>
    refine ((continuousOn_regularAverageValue hLpos hc hC).mono ?_).congr ?_
    · rintro U ⟨hU, hκ⟩
      refine ⟨hU, ?_⟩
      unfold blockAverageCase at hκ
      split_ifs at hκ with h₁
      exact h₁.1
    · rintro U ⟨-, hκ⟩
      change blockAverage _ U c = _
      rw [hval, blockAverageOnPositive_eq_byCase, hκ]
  | intrinsicLogarithmOfDefects =>
    refine ((continuousOn_logAverageValue hI.2.2.2.2.2 c).mono ?_).congr ?_
    · rintro U ⟨hU, hκ⟩
      refine ⟨hU, ?_⟩
      unfold blockAverageCase at hκ
      split_ifs at hκ with h₁ h₂
      exact h₂
    · rintro U ⟨-, hκ⟩
      change blockAverage _ U c = _
      rw [hval, blockAverageOnPositive_eq_byCase, hκ]
  | alongBond =>
    refine (continuous_pathHolonomy (axialPath (c.source.toSublattice _)
      (c.target.toSublattice _))).continuousOn.congr ?_
    rintro U ⟨-, hκ⟩
    change blockAverage _ U c = _
    rw [hval, blockAverageOnPositive_eq_byCase, hκ]
    rfl
end YangMills.Construction.PeriodicLattice.BlockAverageContinuity
end
