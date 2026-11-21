import Formulation.ContinuumLimit
import YangMills.ContinuumLimit.RecordCutoffs
import YangMills.ContinuumLimit.RecurrentWindow
import YangMills.ContinuumLimit.FixedReferenceLevelBound
import YangMills.ContinuumLimit.CovarianceAtTheStoppingLevel

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff
namespace YangMills
open Construction ContinuumLimit Formulation
open Construction.LimitTheorem
open Construction.ConfigSpace (FlatSequence)
open Construction.LimitTheorem.ComponentConditions
open Construction.TheStatementsProvedTogether Construction.PeriodicLattice

/-- The physical bare coupling, infinite-volume states, growing tori,
full separated correlation limits, and component Schwinger representatives. -/
def FixedObservableContinuumWith (P : SystemsWithFiveBounds.LimitConstants → FlatSequence → Prop)
    (L M : ℕ) (g₀ : ℝ) : Prop :=
  ∃ (K m : ℕ → ℕ+) (ν : ∀ j, Measure (InfiniteLattice.GaugeField (meshSize L (K j : ℤ))))
    (S : CumulantFamily) (X₂ : TestSpaces.SepTupleOfCard 2) (X₄ : TestSpaces.SepTupleOfCard 4),
    let g := fun j => renormalizedBareCoupling L M (K j) g₀
    let β := fun j => (g j ^ 2)⁻¹
    StrictMono K ∧
    (∀ j, IsLeast {t : ℝ | 0<t ∧ referenceResponse L M (K j) (t^2)⁻¹ = fixedPhysicalLevel g₀} (g j)) ∧
    Tendsto (fun j => (g j)^2 * (K j : ℝ) * Real.log L) atTop (𝓝 (3*Real.pi^2/11)) ∧
      (∀ j, InfiniteLattice.IsInfiniteVolumeLimit L (K j) (β j) (ν j)) ∧
      Tendsto (fun j => PeriodicLattice.torusSide L (m j)) atTop atTop ∧
      Tendsto (fun j => β j / ((K j : ℝ) * Real.log L))
        atTop (𝓝 (11 / (3 * Real.pi ^ 2) : ℝ)) ∧
      (∀ n hn (X : TestSpaces.SepTupleOfCard n),
        (∀ᶠ j in atTop, SchwingerFunctions.IsR4TestFamily (PeriodicLattice.torusSide L (m j)) X.1) ∧
        Tendsto (fun j => InfiniteLattice.smearedEnergyCumulant (ν j) X.1) atTop (𝓝 (S n hn X : ℂ)) ∧
        Tendsto (fun j => SchwingerFunctions.connectedSchwingerR4 L (m j) (K j) (β j) X.1)
          atTop (𝓝 (S n hn X : ℂ))) ∧
      (∀ n (X : TestSpaces.SepTupleOfCard n), let z : ℂ := TestSpaces.centredOfCumulants S ⟨n,X⟩
        Tendsto (fun j => InfiniteLattice.centeredMoment (ν j) X.1) atTop (𝓝 z) ∧
        Tendsto (fun j => su2_centeredMoment L (m j) (K j) (β j) X) atTop (𝓝 z)) ∧
      (∀ i, ContDiff ℝ ∞ (X₂.1 i)) ∧ 0 < S 2 le_rfl X₂ ∧
      (∀ i, ContDiff ℝ ∞ (X₄.1 i)) ∧ 0 < S 4 (by decide) X₄ ∧
      (∃ (D : SystemsWithFiveBounds.LimitConstants) (T : FlatSequence),
        D.Valid ∧ SystemsWithFiveBounds.HasSchwingerSequence (centredOf S) T ∧
        SystemsWithFiveBounds.SatisfiesGrowth T D.schwartzOrder D.schwartzPrefactor D.schwartzBase D.schwartzExp ∧
        ConfigSpace.IsEuclidInvariant T ∧ ConfigSpace.IsOSPositive T ∧
        ConfigSpace.IsPermSymmetric T ∧ ConfigSpace.IsReflectionReal T ∧ HasCumulants (centredOf S) S) ∧
      ∃ (A : SeparatedTuples.DecompositionData) (D : SystemsWithFiveBounds.LimitConstants),
        D.Valid ∧ A.IsCanonical (centredOf S) ∧
        (∀ ξ, ∃ T : FlatSequence, SystemsWithFiveBounds.HasSchwingerSequence (A.comp ξ) T ∧
          P D T) ∧
        ∀ᵐ ξ ∂A.law, ModelSeams.IsNonGaussianOnSmoothQuadruple (A.comp ξ)

/-- The fixed-observable continuum limit with all OS axioms on each component. -/
abbrev FixedObservableContinuum := FixedObservableContinuumWith SystemsWithFiveBounds.OSAxioms

/-- The common reference torus and physical tuning interval for a continuum limit. -/
def FixedObservableLimit (P : ℕ → ℕ → ℝ → Prop) : Prop :=
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ (M : ℕ+) (δ : ℝ),
      8 ≤ torusSide L M ∧ 0 < δ ∧
        (∀ᶠ k : ℕ in atTop, ∀ g₀ ∈ Ioo (0:ℝ) δ,
          IsLeast {t : ℝ | 0<t ∧ referenceResponse L M k (t^2)⁻¹ = fixedPhysicalLevel g₀}
            (renormalizedBareCoupling L M k g₀)) ∧
        ∀ g₀ ∈ Ioo (0:ℝ) δ, P L M g₀

namespace BranchHot

/-- Exact selection at every sufficiently fine cutoff enters a fixed first-passage
window along a subsequence if a positive fixed reference level cannot escape to
an infinitely cold terminal state. -/
private theorem fixed_observable_continuum_of_no_escape
    {P : SystemsWithFiveBounds.LimitConstants → FlatSequence → Prop} (hP : HoldsForComponents P)
    {Q : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop}
    (hQ : TotalDensities.HoldsAtAdmissibleParameters Q) :
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L →
      ∃ (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ)
        (Kr : WeightedResponses.ResponseParameters) (lam cr : ℝ),
        (T.stepParameters y).side = L ∧ RunTable T y Kr lam cr ∧ Q T y ∧
        ∃ (M : ℕ+) (δ : ℝ), 8 ≤ torusSide L M ∧ 0 < δ ∧
          (∀ᶠ k : ℕ in atTop, ∀ g₀ ∈ Ioo (0:ℝ) δ,
            IsLeast {t : ℝ | 0 < t ∧ referenceResponse L M k (t^2)⁻¹ = fixedPhysicalLevel g₀}
              (renormalizedBareCoupling L M k g₀)) ∧
          (NoEscapingLevel T y L M → ∀ g₀ ∈ Ioo (0:ℝ) δ, FixedObservableContinuumWith P L M g₀) := by
  obtain ⟨L₀, head⟩ := bare_root_with_window_data (hQ.and refined_tables)
  refine ⟨L₀,fun L ho hL₀ => ?_⟩
  obtain ⟨T,y,Kr,lam,cr,Bs,γ,c₅,speed,CT,c,Nw,hL,havg,hRun,⟨hq,href⟩,hγ,_,conditions,root⟩ :=
    head L ho hL₀
  subst L
  let L := (T.stepParameters y).side
  let p := T.stepParameters y
  have hadm : Conventions.IsAdmissibleBlockingFactor p.side :=
    ⟨hRun.adm.L_odd, (by have := hRun.adm.L_ge; change 13 ≤ T.side; omega)⟩
  let s := CouplingFlow.slopeConst L
  have hs : 0 < s := by
    have hh : 1 < L := by change 1 < p.side; have := hadm.2; omega
    have hl := Real.log_pos (show 1 < (L:ℝ) by exact_mod_cast hh)
    dsimp only [s,CouplingFlow.slopeConst]; positivity
  obtain ⟨X,hrec⟩ := uniform_record_gap hs havg hRun href
  let H := max X (Bs + (γ⁻¹)^2 + 1)
  obtain ⟨M,δ,hM,hδ,hroots⟩ := root H
  refine ⟨T,y,Kr,lam,cr,rfl,hRun,hq,M,δ,hM,hδ,hroots.mono (fun _ hj g₀ hg₀ => (hj g₀ hg₀).1),fun hcold g₀ hg₀ => ?_⟩
  obtain ⟨w,hw,hboth⟩ := extraction_of_frequently_atTop
    ((hrec.and_eventually hroots).and_eventually (eventually_ge_atTop 1))
  let K (j : ℕ) : ℕ+ := ⟨w j, (hboth j).2⟩
  let g (j : ℕ) := renormalizedBareCoupling L M (K j) g₀
  let b (j : ℕ) := (g j ^ 2)⁻¹
  let P (j : ℕ) := TotalDensityFlow.coupling p (b j) (K j)
  have hdata j : IsLeast {t : ℝ | 0<t ∧ referenceResponse L M (K j) (t^2)⁻¹ = fixedPhysicalLevel g₀} (g j) ∧
      b j ∈ runDomain T y (K j) ∧ IsTunedAt T y (P j) (K j) (b j) ∧ H ≤ P j :=
    (hboth j).1.2 g₀ hg₀
  have hβ j : 0 < b j := inv_pos.mpr (sq_pos_of_pos (hdata j).1.1.1)
  let f (j : ℕ) := referenceResponse L M (K j) (b j)
  have heq j : f j = fixedPhysicalLevel g₀ := (hdata j).1.1.2
  have hpos := fixedPhysicalLevel_pos hg₀.1
  have hc (e : ℕ → ℕ) (he : StrictMono e) (hesc : Tendsto (P ∘ e) atTop atTop) :
      Tendsto (f ∘ e) atTop (𝓝 0) :=
    (hcold _ hpos (w ∘ e) (b ∘ e) (hw.comp he) (fun i => hβ (e i))
      (fun i => (hdata (e i)).2.1) (fun i => (hdata (e i)).2.2.1) (fun i => heq (e i)) hesc).elim
  obtain ⟨W,hW,hwin⟩ := ReferenceCalibration.fixed_window_of_positive_reference P f hpos
    (show 0 < s/4 by positivity) (fun j => (hdata j).2.2.2) heq hc
  have hWX : Bs + (γ⁻¹)^2 + 1 ≤ W := (le_max_right ..).trans hW
  have hdiff : 0 < W-Bs := by linarith [sq_nonneg γ⁻¹]
  let G := (Real.sqrt (W-Bs))⁻¹
  have hG : G ∈ Ioc (0:ℝ) γ := by
    have hz : γ⁻¹ ≤ Real.sqrt (W-Bs) := (Real.le_sqrt (inv_pos.mpr hγ).le hdiff.le).2 (by linarith)
    exact ⟨inv_pos.mpr (Real.sqrt_pos.mpr hdiff), by simpa [G] using inv_anti₀ (inv_pos.mpr hγ) hz⟩
  have hth : SequencePassage.passageThreshold Bs G = W := by
    dsimp [SequencePassage.passageThreshold,G]
    rw [inv_zpow',neg_neg,zpow_two,Real.mul_self_sqrt hdiff.le]
    ring
  have hp : ∃ᶠ j in atTop, TotalDensitySystem.IsFirstPassagePair p Bs G (K j) (b j) := by
    refine hwin.mono fun j hj => ?_
    have hd := (hdata j).2.2.1
    have hdef := (total_flow_of_above_total expansion_gives_total_flow total_density_flow_unique hRun hd.1).1
    have hgap := (hboth j).1.1 (b j) (P j) ((le_max_left ..).trans (hdata j).2.2.2) hd
    have hprior (i : ℕ) (hi : i < K j) : W < TotalDensityFlow.coupling p (b j) i := hj.2.trans_le (hgap i hi)
    change TotalDensityFlow.IsDefinedUpTo p (b j) (K j) ∧
      SequencePassage.passageThreshold Bs G ≤ b j ∧ P j ≤ SequencePassage.passageThreshold Bs G ∧
        ∀ i < (K j:ℕ), SequencePassage.passageThreshold Bs G < TotalDensityFlow.coupling p (b j) i
    rw [hth]
    exact ⟨hdef,(hprior 0 (K j).pos).le,hj.1,hprior⟩
  obtain ⟨φ,m,ν,S,X₂,X₄,hφ,_,hν,hm,hslope,htail⟩ :=
    su2_continuum_limit_of_frequent_passage hP hadm (conditions G hG) K b hw.tendsto_atTop hβ hp
  have hKs : StrictMono K := fun i j hij => show w i < w j from hw hij
  refine ⟨K ∘ φ,m,ν,S,X₂,X₄,hKs.comp hφ,fun j => (hdata (φ j)).1,?_,hν,hm,hslope,htail⟩
  have h := hslope.inv₀ (by positivity)
  rw [show (11 / (3 * Real.pi^2) : ℝ)⁻¹ = 3*Real.pi^2/11 by rw [inv_div]] at h
  apply h.congr'
  filter_upwards with j
  change (((g (φ j) ^ 2)⁻¹ / ((K (φ j):ℝ) * Real.log L))⁻¹) = (g (φ j) ^ 2) * (K (φ j):ℝ) * Real.log L
  rw [inv_div,div_eq_mul_inv,inv_inv]
  ring

end BranchHot

/-- Fixed-observable extraction with any property proved for the component representatives. -/
theorem fixed_observable_continuum_of_components
    {P : SystemsWithFiveBounds.LimitConstants → FlatSequence → Prop} (hP : HoldsForComponents P) :
    FixedObservableLimit (FixedObservableContinuumWith P) := by
  obtain ⟨L₀, h⟩ := BranchHot.fixed_observable_continuum_of_no_escape hP (BranchHot.noEscapingTables_of_stageDecay Formulation.stopped_covariance_vanishes)
  refine ⟨L₀, fun L hodd hL => ?_⟩
  obtain ⟨T,y,KrRun,lam,cr,hside,hRun,hTable,M,δ,hM,hδ,hall,hlim⟩ := h L hodd hL
  have hNo := hTable KrRun lam cr hRun M
  change T.side = L at hside
  rw [hside] at hNo
  exact ⟨M,δ,hM,hδ,hall,hlim hNo⟩

/-- The infinite-volume SU(2) continuum limit at the least positive bare coupling
selected by the fixed two-point observable, with OS axioms on every component. -/
theorem su2_fixed_observable_continuum_limit : FixedObservableLimit FixedObservableContinuum :=
  fixed_observable_continuum_of_components os_axioms_for_components

end YangMills
end
