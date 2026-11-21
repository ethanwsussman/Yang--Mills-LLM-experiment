import YangMills.Construction.RunningCouplingSlope.TotalAtTheLeastFieldProof
import YangMills.Construction.ClusterExpansionOfAStep.HaarOfFieldsIsKept
import YangMills.Construction.ClusterExpansionOfAStep.IsometriesCarryTheKernel
import YangMills.Construction.ColdStepAtMirrorFrames.ZeroFamilyIsAnExpansionProof
import YangMills.Construction.RunningCouplingSlope.HessianOfAStepIsPositiveProof
import YangMills.Construction.SummableBoundsOfTheFlow.DisplayAtTheLeastField
import YangMills.Construction.SummableBoundsOfTheFlow.ParityOfTheScaledMeans
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreMeansAtAScale
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreNearTheirLimitsProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAtTheScaleZero
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensityOfTheStepIsCarried
import YangMills.Construction.SummableBoundsOfTheFlow.TheLeastFieldHasNoExcess
import YangMills.Construction.SummableBoundsOfTheFlow.TheMeansMoveWithTheirWeight
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledPartsAreSmooth
import YangMills.Construction.SummableBoundsOfTheFlow.TheStepIsRegularAtTheLeastField
import YangMills.Construction.SummableBoundsOfTheFlow.TheStepOverColdFieldsIsNearItsCut
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation FamilyNorms TorusFields TorusLumps ScaledVariables
  StepCosts FieldHaar StepDensities MeasureTheory
namespace ReferenceDensity
section
variable {n : ℕ}
private theorem norm_coe_sub_one_sq (g : UnitQuaternion) :
    ‖((g : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 = 2 * (1 - ((g : UnitQuaternion) : ℍ[ℝ]).re) := by apply _root_.YangMills.Construction.TorusFields.sq_norm_unitQuaternion_sub_one <;> assumption
private theorem curvature_eq_sqrt (U : TorusField n) (x : TorusSite n) (μ ν : Fin 4) :
    curvature U x μ ν = Real.sqrt (2 * plaquetteEnergy U x μ ν) := by
  unfold curvature plaquetteEnergy
  rw [← norm_coe_sub_one_sq, Real.sqrt_sq (norm_nonneg _)]
private theorem curvature_symm (U : TorusField n) (x : TorusSite n) (μ ν : Fin 4) :
    curvature U x μ ν = curvature U x ν μ := by
  rw [curvature_eq_sqrt, curvature_eq_sqrt, plaquetteEnergy_symm]
private theorem curvature_of_transports {g : TorusIsometry} {U U' : TorusField n} (h : g.Transports U U')
    (x : TorusSite n) (μ ν : Fin 4) :
    curvature U x μ ν = curvature U' (g.imageCorner x μ ν) (g.imageAxis μ) (g.imageAxis ν) := by
  rw [curvature_eq_sqrt, curvature_eq_sqrt, plaquetteEnergy_of_transports h]
private theorem isCold_of_transports_image {g : TorusIsometry} {s : ℝ} {U U' : TorusField n}
    (h : g.Transports U U') (hU' : IsCold s U') : IsCold s U := by
  intro x μ ν hμν
  rw [curvature_of_transports h]
  have hne : g.imageAxis μ ≠ g.imageAxis ν := fun e => hμν.ne (g.axisPerm.symm.injective e)
  rcases lt_or_gt_of_ne hne with h1 | h1
  · exact hU' _ _ _ h1
  · rw [curvature_symm]
    exact hU' _ _ _ h1
private theorem isCold_image_of_transports [NeZero n] {g : TorusIsometry} {s : ℝ} {U U' : TorusField n}
    (h : g.Transports U U') (hU : IsCold s U) : IsCold s U' := by
  intro y a b hab
  have hbij : Function.Bijective (g.mapSite (n := n)) :=
    Finite.injective_iff_bijective.mp (mapSite_injective g)
  have da : g.imageAxis (g.axisPerm a) = a := by simp [TorusIsometry.imageAxis]
  have db : g.imageAxis (g.axisPerm b) = b := by simp [TorusIsometry.imageAxis]
  obtain ⟨x, hx⟩ := hbij.2
    (y + (if g.axisSign a = 1 then 0 else TorusFields.unitStep n a) +
      (if g.axisSign b = 1 then 0 else TorusFields.unitStep n b))
  have hb : g.imageCorner x (g.axisPerm a) (g.axisPerm b) = y := by
    simp only [TorusIsometry.imageCorner, hx, da, db]
    abel
  have e := curvature_of_transports h x (g.axisPerm a) (g.axisPerm b)
  rw [hb, da, db] at e
  rw [← e]
  have hne : g.axisPerm a ≠ g.axisPerm b := fun e' => hab.ne (g.axisPerm.injective e')
  rcases lt_or_gt_of_ne hne with h1 | h1
  · exact hU _ _ _ h1
  · rw [curvature_symm]
    exact hU _ _ _ h1
end
section
variable {L t N : ℕ}
private theorem torusFrame_period (i : Fin 4) :
    (torusFrame L t N).period (torusFrame L t N).top i = N := TopLevelSites.period_top i
private theorem toTorusSite_actSite [NeZero N] (g : TorusIsometry) (x : (torusFrame L t N).Cell) :
    toTorusSite N (CubicSymmetry.actSite ⟨g.axisPerm, g.axisSign, g.offset⟩ (torusFrame L t N).top x) =
      g.mapSite (toTorusSite N x) := by apply _root_.YangMills.DeltaSharedProofs.p501220 <;> assumption
private theorem actSite_torusSiteInFrame [NeZero N] (g : TorusIsometry) (y : TorusSite N) :
    CubicSymmetry.actSite ⟨g.axisPerm, g.axisSign, g.offset⟩ (torusFrame L t N).top
        (torusSiteInFrame (torusFrame L t N) (torusFrame L t N).top y) =
      torusSiteInFrame (torusFrame L t N) (torusFrame L t N).top (g.mapSite y) := by
  apply TopLevelSites.toTorusSite_injective torusFrame_period
  rw [toTorusSite_actSite, TopLevelSites.toTorusSite_torusSiteInFrame torusFrame_period,
    TopLevelSites.toTorusSite_torusSiteInFrame torusFrame_period]
abbrev _root_.YangMills.SharedProofs.p75600 := @actSite_torusSiteInFrame
private theorem cubicSymmetry_transportsField [NeZero N] (g : TorusIsometry) {U U' : TorusField N}
    (h : g.Transports U U') :
    CubicSymmetry.TransportsField (F := torusFrame L t N) ⟨g.axisPerm, g.axisSign, g.offset⟩
      (readAtLevel (torusFrame L t N) (torusFrame L t N).top U)
      (readAtLevel (torusFrame L t N) (torusFrame L t N).top U') := by apply _root_.YangMills.DeltaSharedProofs.p501285 <;> assumption
abbrev _root_.YangMills.SharedProofs.p26341 := @cubicSymmetry_transportsField
private theorem isSmallCurvature_readAtLevel [NeZero N] {s : ℝ} {V : TorusField N} (hV : IsCold s V) :
    IsSmallCurvature s (readAtLevel (torusFrame L t N) (torusFrame L t N).top V) := by apply _root_.YangMills.SharedProofs.p2155 <;> assumption
private theorem mem_finiteCells_torusFrame (hN : 2 ≤ N) (z : (torusFrame L t N).Cell) :
    z ∈ finiteCells (torusFrame L t N) :=
  TopLevelSites.mem_finiteCells (fun _ => by show 0 < N; omega) z
private theorem sum_finiteCells_eq_sum_torusSite [NeZero N] (hN : 2 ≤ N) (f : (torusFrame L t N).Cell → ℝ) :
    ∑ Y ∈ finiteCells (torusFrame L t N), f Y =
      ∑ z : TorusSite N, f (torusSiteInFrame (torusFrame L t N) (torusFrame L t N).top z) := by
  symm
  refine Finset.sum_bij (fun z _ => torusSiteInFrame (torusFrame L t N) (torusFrame L t N).top z)
    (fun z _ => mem_finiteCells_torusFrame hN _) ?_ ?_ (fun _ _ => rfl)
  · intro z _ z' _ h
    have := congrArg (toTorusSite N) h
    rwa [TopLevelSites.toTorusSite_torusSiteInFrame torusFrame_period,
      TopLevelSites.toTorusSite_torusSiteInFrame torusFrame_period] at this
  · intro w _
    exact ⟨toTorusSite N w, Finset.mem_univ _, TopLevelSites.torusSiteInFrame_toTorusSite torusFrame_period w⟩
private theorem minimalAction_of_transports (hS : sumCellSharesEqAction) {a : ℝ} {c : ColdChainParameters}
    (hc : c.Admissible a L) (ha : 0 ≤ a) (hL : Odd L) {s : ℝ} (hs : 0 < s) (hsA : s ≤ c.σA) [NeZero N]
    (hN : 64 ≤ N) (g : TorusIsometry) {U U' : TorusField N} (hU : IsCold s U) (hT : g.Transports U U') :
    minimalAction a (finiteCells (torusFrame L t N)) (torusFrame L t N).top
        (readAtLevel (torusFrame L t N) (torusFrame L t N).top U') =
      minimalAction a (finiteCells (torusFrame L t N)) (torusFrame L t N).top
        (readAtLevel (torusFrame L t N) (torusFrame L t N).top U) := by
  have hN2 : 2 ≤ N := by omega
  have e : ∀ V : TorusField N, minimalAction a (finiteCells (torusFrame L t N)) (torusFrame L t N).top
      (readAtLevel (torusFrame L t N) (torusFrame L t N).top V) =
      ∑ z : TorusSite N, minimalCellShare a (finiteCells (torusFrame L t N))
        (torusSiteInFrame (torusFrame L t N) (torusFrame L t N).top z)
        (readAtLevel (torusFrame L t N) (torusFrame L t N).top V) := by
    intro V
    rw [← sum_finiteCells_eq_sum_torusSite hN2 fun Y => minimalCellShare a (finiteCells (torusFrame L t N)) Y
      (readAtLevel (torusFrame L t N) (torusFrame L t N).top V)]
    exact ((hS (torusFrame L t N) a (fun _ _ => 0) (readAtLevel (torusFrame L t N) (torusFrame L t N).top V) ha hL
      fun _ => hN2).1).symm
  have hcl := hc.estimates (torusFrame L t N) s (readAtLevel (torusFrame L t N) (torusFrame L t N).top U)
    ⟨rfl, N, hN, fun _ => rfl⟩ hs hsA (isSmallCurvature_readAtLevel hU)
  obtain ⟨-, -, -, -, hIso, -⟩ := hcl.cellShares
  rw [e, e]
  have hbij : Function.Bijective (g.mapSite (n := N)) :=
    Finite.injective_iff_bijective.mp (mapSite_injective g)
  rw [← (Equiv.ofBijective _ hbij).sum_comp (fun z => minimalCellShare a (finiteCells (torusFrame L t N))
    (torusSiteInFrame (torusFrame L t N) (torusFrame L t N).top z)
    (readAtLevel (torusFrame L t N) (torusFrame L t N).top U'))]
  refine Finset.sum_congr rfl fun z _ => ?_
  have h1 := hIso ⟨g.axisPerm, g.axisSign, g.offset⟩ (finiteCells (torusFrame L t N))
    (readAtLevel (torusFrame L t N) (torusFrame L t N).top U') ⟨g.axisSign_unit, fun _ _ => rfl⟩
    (fun _ => ⟨fun _ => mem_finiteCells_torusFrame hN2 _, fun _ => mem_finiteCells_torusFrame hN2 _⟩)
    (cubicSymmetry_transportsField g hT)
    (torusSiteInFrame (torusFrame L t N) (torusFrame L t N).top z)
  rw [actSite_torusSiteInFrame] at h1
  exact h1
private theorem actionAtLevel_of_transports (hS : sumCellSharesEqAction) {a : ℝ} {c : ColdChainParameters}
    (hc : c.Admissible a L) (ha : 0 ≤ a) (hL : Odd L) {s : ℝ} (hs : 0 < s) (hsA : s ≤ c.σA) (t : ℕ)
    [NeZero N] (hN : 64 ≤ N) (g : TorusIsometry) {U U' : TorusField N} (hU : IsCold s U)
    (hT : g.Transports U U') :
    actionAtLevel a L t Finset.univ U' = actionAtLevel a L t Finset.univ U := by
  cases t with
  | zero => exact wilsonAction_of_transports hT
  | succ t =>
    have hw : cellsOfSites (torusFrame L t N) (Finset.univ : Finset (TorusSite N)) =
        finiteCells (torusFrame L t N) := by
      ext z
      refine ⟨fun _ => mem_finiteCells_torusFrame (by omega) z, fun _ => ?_⟩
      unfold cellsOfSites
      exact Finset.mem_image.mpr ⟨toTorusSite N z, Finset.mem_univ _,
        TopLevelSites.torusSiteInFrame_toTorusSite torusFrame_period z⟩
    show minimalAction a (cellsOfSites (torusFrame L t N) Finset.univ) (t + 1)
        (readAtLevel (torusFrame L t N) (t + 1) U') =
      minimalAction a (cellsOfSites (torusFrame L t N) Finset.univ) (t + 1)
        (readAtLevel (torusFrame L t N) (t + 1) U)
    rw [hw]
    exact minimalAction_of_transports hS hc ha hL hs hsA hN g hU hT
end
section
private theorem standardBorelSpace_unitQuaternion : StandardBorelSpace UnitQuaternion := by
  have : BorelSpace UnitQuaternion := ⟨rfl⟩
  infer_instance
private theorem coldStepIntegral_of_transports (hH : HaarInvariantUnderSymmetries)
    (hK : IsometriesPreserveAveragedKernel) (ℓ : TorusLumps.StepParameters) (hF : ℓ.Admissible) (t : ℕ)
    (x : ℝ) (n : ℕ) [NeZero n] (hn : ℓ.n₀ ≤ n)
    (hAct : ∀ (g : TorusIsometry) (U U' : TorusField (n * ℓ.side)), IsCold ℓ.threshold U → g.Transports U U' →
      actionAtLevel ℓ.coupling ℓ.side t Finset.univ U' = actionAtLevel ℓ.coupling ℓ.side t Finset.univ U)
    (g : TorusIsometry) {V V' : TorusField n} (hT : g.Transports V V') :
    coldStepIntegral ℓ t x n V' = coldStepIntegral ℓ t x n V := by
  obtain ⟨Ψ, hΨ, hcar⟩ := (hH (n * ℓ.side)).2 (g.scaledLift ℓ.side)
  have hinj : Function.Injective Ψ := by
    intro U₁ U₂ he
    funext y k
    have h1 := hcar U₁ y k
    have h2 := hcar U₂ y k
    rw [he] at h1
    by_cases hs : (g.scaledLift ℓ.side).axisSign ((g.scaledLift ℓ.side).axisPerm.symm k) = 1
    · rw [if_pos hs] at h1 h2
      exact h1.symm.trans h2
    · rw [if_neg hs] at h1 h2
      exact h1.symm.trans h2
  have : StandardBorelSpace UnitQuaternion := standardBorelSpace_unitQuaternion
  have hemb : MeasurableEmbedding Ψ := hΨ.measurable.measurableEmbedding hinj
  unfold coldStepIntegral
  rw [← hΨ.integral_comp hemb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  show Set.indicator _ _ (Ψ U) = Set.indicator _ _ U
  by_cases hcold : IsCold ℓ.threshold U
  · have c' := isCold_image_of_transports (hcar U) hcold
    rw [Set.indicator_of_mem (show Ψ U ∈ {U' : TorusField (n * ℓ.side) | IsCold ℓ.threshold U'} from c'),
      Set.indicator_of_mem (show U ∈ {U' : TorusField (n * ℓ.side) | IsCold ℓ.threshold U'} from hcold)]
    have ka := hK ℓ hF x n hn g U (Ψ U) V V' (hcar U) hT
    have aw : coldActionWeight ℓ.coupling ℓ.side t x (n * ℓ.side) (Ψ U) =
        coldActionWeight ℓ.coupling ℓ.side t x (n * ℓ.side) U := by
      unfold coldActionWeight
      rw [dif_neg (NeZero.ne _), dif_neg (NeZero.ne _), hAct _ U _ hcold (hcar U)]
    rw [aw]
    exact congrArg _ ka
  · have c' : ¬ IsCold ℓ.threshold (Ψ U) := fun h => hcold (isCold_of_transports_image (hcar U) h)
    rw [Set.indicator_of_notMem (show Ψ U ∉ {U' : TorusField (n * ℓ.side) | IsCold ℓ.threshold U'} from c'),
      Set.indicator_of_notMem (show U ∉ {U' : TorusField (n * ℓ.side) | IsCold ℓ.threshold U'} from hcold)]
end
section
private theorem bondDeriv_zero_density {F : BlockFrame} {j k : ℕ} (W : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv (fun _ : F.GaugeField j => (0 : ℝ)) W c X = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ZeroFamilyRegular.bondDeriv_zero <;> assumption
private theorem subtractTrivial_zero (F : BlockFrame) (y : F.Site F.depth) :
    subtractTrivial (localFamilyOfDensity 0) F y = fun _ => (0 : ℝ) := by
  funext W
  exact sub_self _
private theorem isNormBoundedLocalFamily_zero (L t n₀ : ℕ) (σ δ ε ε₃ : ℝ) (hw : ∀ x, 0 ≤ torusDecayFactor L δ x)
    (h : 0 ≤ ε) (h₃ : 0 ≤ ε₃) :
    IsNormBoundedLocalFamily L t n₀ σ δ ε ε₃ (localFamilyOfDensity 0) where
  smooth := fun _ _ _ _ _ _ _ _ => contDiffAt_const
  gauge_invariant := fun _ _ _ _ _ _ => rfl
  translation_invariant := fun _ _ _ _ _ _ => rfl
  decay := by
    intro F _ y W k c X _ _ _ _
    have e : bondDeriv (localFamilyOfDensity (0 : LocalDensity) F y) W c X = 0 := bondDeriv_zero_density W c X
    rw [e, abs_zero]
    refine div_nonneg ?_ (hw _)
    split_ifs
    · exact h₃
    · exact h
  locality := by
    intro F F' _ _ y y' W W' r k b X _ _ _ _ _ _
    rw [subtractTrivial_zero, subtractTrivial_zero, bondDeriv_zero_density, bondDeriv_zero_density, sub_zero,
      abs_zero]
    exact div_nonneg h (hw _)
private theorem isRegularFamily_zero (L t n₀ : ℕ) (σ δ ε ε₃ : ℝ) (hw : ∀ x, 0 ≤ torusDecayFactor L δ x)
    (h : 0 ≤ ε) (h₃ : 0 ≤ ε₃) :
    IsRegularFamily L t n₀ σ δ ε ε₃ (localFamilyOfDensity 0) := by
  have hb := isNormBoundedLocalFamily_zero L t n₀ σ δ ε ε₃ hw h h₃
  refine ⟨hb.smooth, hb.gauge_invariant, hb.translation_invariant, hb.decay, hb.locality, fun _ _ _ _ => 0, ?_, ?_⟩
  · intro b b' X X'
    refine tendsto_const_nhds.congr fun n => ?_
    exact (bondDeriv_zero_density _ _ _).symm
  · intro _ _ _ _ _ _ _ _
    exact hasSum_zero
private theorem isBoundedFamilyOrderSix_zero (T : ColdStepAtMirrorFrames.StepParameters) (hT : T.IsOrdered)
    (hw : ∀ x, 0 ≤ torusDecayFactor T.L T.decayRate x) (t : ℕ) :
    T.IsBoundedFamilyOrderSix (fun _ => 0) t (localFamilyOfDensity 0) := by
  have hE : 0 ≤ T.E := by linarith [hT.one_le_E]
  have hE₃ : 0 ≤ T.energyRatio := div_nonneg hE hT.η₃_pos.le
  refine ⟨isNormBoundedLocalFamily_zero _ _ _ _ _ _ _ hw hE hE₃, fun _ _ _ _ _ _ _ _ => contDiffAt_const,
    fun _ _ _ _ _ _ => rfl, ?_⟩
  intro F _ y W j c X _ _ _ _
  have e : bondDeriv (localFamilyOfDensity (0 : LocalDensity) F y) W c X = 0 := bondDeriv_zero_density W c X
  rw [e, abs_zero, zero_div]
private theorem expansionDensity_zero {F : BlockFrame} (a ρA x : ℝ) (m : ℕ) (ρ : ℝ) (p : ℝ → ℝ) (Y : F.Cell)
    (V : F.GaugeField F.top) :
    expansionDensity true a ρA ρ x m p (localFamilyOfDensity 0) Y V = 0 := by
  have hb : ∀ η, cellCentredExpansion true a ρA m (localFamilyOfDensity 0) Y η V = 0 := by
    intro η
    unfold cellCentredExpansion centredExpansion
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [subtractTrivial_zero]
  unfold expansionDensity cutoffMean
  simp [hb]
end
section
private theorem bondDeriv_fin_zero {F : BlockFrame} (G : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G V c X = G V := by apply _root_.YangMills.SharedProofs.p1654 <;> assumption
private theorem tendsto_interactionDensity_stepDensity (hP : scaledMeanParity)
    (hS : rescaledPartsSmoothStatement) (hW : meansDifferentiableInWeightStatement)
    (hZ : DensitiesAtScaleZero) (hE : DensitiesAreRescaledMeans) :
    EventuallyOrdered fun T => ∀ (t : ℕ) (F : BlockFrame) (Y : F.Cell) (V : F.GaugeField F.top),
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V →
      Filter.Tendsto (fun x => interactionDensity true T.a T.ρA T.ballRadius T.lam x 0 T.p
          (localFamilyOfDensity 0) Y V) Filter.atTop
        (𝓝 (stepDensity T.a T.ρA T.lam Y V)) := by
  refine EventuallyOrdered.mono ((((hP.and hS).and hW).and hZ).and hE) ?_
  rintro T hT hn ⟨⟨⟨⟨cP, cS⟩, cW⟩, cZ⟩, cE⟩ t F Y V hF hV
  have hw : ∀ x, 0 ≤ torusDecayFactor T.L T.decayRate x := fun x => by
    unfold torusDecayFactor
    positivity
  set f : LocalFamily := localFamilyOfDensity 0 with hf
  have he : T.IsBoundedFamilyOrderSix (fun _ => 0) t f := isBoundedFamilyOrderSix_zero T hT hw t
  obtain ⟨l₁, C₁, hl₁, hC₁, gP⟩ := cP fun _ => 0
  obtain ⟨l₂, K, hl₂, hK, gS⟩ := cS fun _ => 0
  obtain ⟨l₃, hl₃, gW⟩ := cW fun _ => 0
  obtain ⟨l₄, hl₄, gE⟩ := cE
  set l₀ : ℝ := min (min l₁ (l₂ / 2)) (min l₃ l₄) with hl₀def
  have hl₀ : 0 < l₀ := lt_min (lt_min hl₁ (half_pos hl₂)) (lt_min hl₃ hl₄)
  have hle₁ : l₀ ≤ l₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hle₂' : l₀ ≤ l₂ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hle₂ : l₀ ≤ l₂ := by linarith
  have hdbl : 2 * l₀ ≤ l₂ := by linarith
  have hdbl₀ : 0 < 2 * l₀ := by positivity
  have hle₃ : l₀ ≤ l₃ := (min_le_right _ _).trans (min_le_left _ _)
  have hle₄ : l₀ ≤ l₄ := (min_le_right _ _).trans (min_le_right _ _)
  set O₁ : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
    fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ with hO₁
  have hs₁ : IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius l₀ K Y O₁ :=
    fun V' hV' => (gS l₀ hl₀ hle₂ t f F V' Y he hF hV').1
  have hd₁ : IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius (2 * l₀) K Y O₁ :=
    fun V' hV' => (gS (2 * l₀) hdbl₀ hdbl t f F V' Y he hF hV').1
  have hX₀ : AreUnitVectors (Fin.elim0 : Fin 0 → imaginaryQuaternions) := fun l => l.elim0
  obtain ⟨v₁l, v₁z⟩ := (gW l₀ hl₀ hle₃ t f F V Y StepLaw.interpolated K O₁ 0 Fin.elim0 Fin.elim0 he hF hV
    (Or.inr rfl) hK hs₁ hX₀).1 (by norm_num)
  set B : ℝ := C₁ * K * Real.exp (-(T.κ / 2 ^ 6 *
    bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4))) with hB
  have hbound : ∀ x, l₀⁻¹ ^ 2 ≤ x →
      |interactionDensity true T.a T.ρA T.ballRadius T.lam x 0 T.p f Y V - stepDensity T.a T.ρA T.lam Y V| ≤
        B * x⁻¹ := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
    obtain ⟨l, hl, hll, hxl, hl2⟩ : ∃ l : ℝ, 0 < l ∧ l ≤ l₀ ∧ l⁻¹ ^ 2 = x ∧ l ^ 2 = x⁻¹ := by
      have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
      refine ⟨(Real.sqrt x)⁻¹, inv_pos.mpr hsq, ?_, ?_, ?_⟩
      · have h1 : l₀⁻¹ ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hx
        exact inv_le_of_inv_le₀ hl₀ h1
      · rw [inv_inv, Real.sq_sqrt hx0.le]
      · rw [inv_pow, Real.sq_sqrt hx0.le]
    subst hxl
    have hz : stepDensity T.a T.ρA T.lam Y V =
        -∫ θ in (0 : ℝ)..1, observableGaussianMean T.a T.ρA T.lam f (.interpolated θ) O₁ V :=
      (cZ t f F V Y hF hV).1.symm
    obtain ⟨-, -, u₁, -⟩ := gE t F V f l Y hF hV hl (hll.trans hle₄)
    have hu : interactionDensity true T.a T.ρA T.ballRadius T.lam (l⁻¹ ^ 2) 0 T.p f Y V =
        -∫ θ in (0 : ℝ)..1, observableMean T.a T.ρA T.ballRadius T.lam T.p f (.interpolated θ) O₁ l V := u₁
    have par : ∀ θ ∈ Set.uIoc (0 : ℝ) 1,
        ‖observableMean T.a T.ρA T.ballRadius T.lam T.p f (.interpolated θ) O₁ l V -
          observableGaussianMean T.a T.ρA T.lam f (.interpolated θ) O₁ V‖ ≤ B * l ^ 2 := by
      intro θ hθ
      rw [Set.uIoc_of_le zero_le_one] at hθ
      have h := (gP l₀ hl₀ hle₁ t f F V Y (.interpolated θ) K O₁ 0 Fin.elim0 Fin.elim0 he hF hV
        ⟨hθ.1.le, hθ.2⟩ hK hd₁ hX₀).sub_gaussianMean_le (by norm_num) l hl hll
      rw [bondDeriv_fin_zero, bondDeriv_fin_zero] at h
      rw [Real.norm_eq_abs]
      refine h.trans (le_of_eq ?_)
      rw [hB]
      ring
    have iS : IntervalIntegrable
        (fun θ => observableMean T.a T.ρA T.ballRadius T.lam T.p f (.interpolated θ) O₁ l V) volume 0 1 := by
      have h := (v₁l l hl hll).integrable
      simpa only [bondDeriv_fin_zero] using h
    have iZ : IntervalIntegrable
        (fun θ => observableGaussianMean T.a T.ρA T.lam f (.interpolated θ) O₁ V) volume 0 1 := by
      have h := v₁z.integrable
      simpa only [bondDeriv_fin_zero] using h
    have i₁ := intervalIntegral.norm_integral_le_of_norm_le_const par
    rw [intervalIntegral.integral_sub iS iZ] at i₁
    simp only [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at i₁
    rw [hu, hz, ← hl2]
    have e : ∀ u v : ℝ, -u - -v = -(u - v) := fun u v => by ring
    rw [e, abs_neg]
    exact i₁
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ (g := fun x => B * x⁻¹) ?_
  · filter_upwards [Filter.eventually_ge_atTop (l₀⁻¹ ^ 2)] with x hx
    rw [Real.norm_eq_abs]
    exact hbound x hx
  · simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul B
end
private theorem eventually_threshold_le_chain : EventuallyInParameters fun T => T.σ ≤ T.chainParams.σA := by
  intro a _
  refine ⟨0, fun L _ _ c hc => ?_⟩
  exact ⟨0, fun Ct _ => ⟨1, one_pos, fun κ _ _ => ⟨1, one_pos, fun η₃ _ _ _ => ⟨0, fun nss _ =>
    ⟨c.σA, hc.positivity.2.2.2.1, fun σ _ hσ p _ => ⟨0, fun Cs _ E _ => ⟨0, fun n₀ _ => ⟨0, fun CE _ =>
      ⟨0, fun y₁ _ => hσ⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem stepDensitySumInvariant_holds (hC : ColdStepLaplaceAsymptotics)
    (hD : logIntegralAtMinimizerStatement) (hX : minimizerExcessSumZero)
    (hR : regularStepAtMinimizerStatement) (hK : IsometriesPreserveAveragedKernel)
    (hH : HaarInvariantUnderSymmetries) (hSh : sumCellSharesEqAction)
    (hP : scaledMeanParity) (hS : rescaledPartsSmoothStatement)
    (hW : meansDifferentiableInWeightStatement) (hZ : DensitiesAtScaleZero)
    (hE : DensitiesAreRescaledMeans) : StepDensitySumInvariant := by
  have hB := tendsto_interactionDensity_stepDensity hP hS hW hZ hE
  have hG : EventuallyOrdered fun T => T.σ ≤ T.chainParams.σA :=
    EventuallyInParameters.mono eventually_threshold_le_chain fun _ h _ _ => h
  have hR' : EventuallyOrdered IsRegularAtMinimizer := EventuallyInParameters.mono hR fun _ h _ _ => h
  refine EventuallyOrdered.mono (((hC.and hB).and hG).and hR') ?_
  rintro T hT hn₁ ⟨⟨⟨cC, cB⟩, cG⟩, cR⟩ ℓ hm hF t n _ hnn g W W' hW₀ hW₀' hCar
  have hσ₀ := hT.σ_pos
  have ha : 0 ≤ T.a := by linarith [hT.one_le_a]
  have hodd := hT.odd_L
  have hnT : T.n₀ ≤ n := hm.n₀_eq ▸ hnn
  have hn4 : 4096 ≤ n := hF.n₀_ge.trans hnn
  have hWc : IsCold T.σ W := hm.threshold_eq ▸ hW₀
  have hWc' : IsCold T.σ W' := hm.threshold_eq ▸ hW₀'
  have hLpos : 0 < ℓ.side := lt_of_lt_of_le (by norm_num) hF.L_ge
  obtain ⟨c, hc⟩ := cC ℓ hm hF t n hnT
  have t₁ := hc W hW₀
  have t₂ := hc W' hW₀'
  have hstep : ∀ x, coldStepIntegral ℓ t x n W' = coldStepIntegral ℓ t x n W := by
    intro x
    refine coldStepIntegral_of_transports hH hK ℓ hF t x n hnn ?_ g hCar
    intro g' U U' hU hU'
    have hUc : IsCold T.σ U := hm.threshold_eq ▸ hU
    have key : ∀ (a : ℝ) (L : ℕ), a = T.a → L = T.L →
        actionAtLevel a L t Finset.univ U' = actionAtLevel a L t Finset.univ U := by
      rintro a L rfl rfl
      have h64 : 64 ≤ n * ℓ.side := by
        have : n ≤ n * ℓ.side := Nat.le_mul_of_pos_right _ hLpos
        omega
      exact actionAtLevel_of_transports hSh hT.chain_admissible ha hodd hσ₀ cG t h64 g' hUc hU'
    exact key _ _ hm.coupling_eq hm.side_eq
  set F := torusFrame T.L t n with hFdef
  have hside : ∀ i, 2 ≤ F.extent i := fun _ => by
    show 2 ≤ n
    omega
  have htop : IsCubicTopTorus T.L t T.n₀ F := ⟨rfl, rfl, n, fun _ => rfl, hnT⟩
  have hw : ∀ x, 0 ≤ torusDecayFactor T.L T.decayRate x := fun x => by
    unfold torusDecayFactor
    positivity
  have hE0 : 0 ≤ T.E := by linarith [hT.one_le_E]
  have hη := hT.η₃_pos
  set Kc : ℝ → ℝ := fun x => (∑ _c ∈ innerBonds (finiteCells F) F.top, haarGap (T.a * x)) +
    (∑ _b : ↥(chordBonds (finiteCells F)), Real.log (haarRadialDensity 0)) +
    Real.log (gaussianMass T.ballRadius T.lam x T.p F) with hKc
  set U : TorusField n → ℝ → ℝ := fun V x => ∑ Y ∈ finiteCells F,
    interactionDensity true T.a T.ρA T.ballRadius T.lam x 0 T.p (localFamilyOfDensity 0) Y
      (readAtLevel F F.top V) with hU
  have hdisp : ∀ V : TorusField n, IsCold T.σ V → ∀ x, T.coupling ≤ x →
      Real.log (interpolatedStepIntegral 0 T.a T.ρA T.ballRadius x 0 T.p (localFamilyOfDensity 0)
          (readAtLevel F F.top V)) =
        Kc x - x * minimalAction T.a (finiteCells F) F.top (readAtLevel F F.top V) + U V x := by
    intro V hV x hx
    have hcold : IsSmallCurvature (9 / 8 * T.σ) (readAtLevel F F.top V) :=
      isSmallCurvature_readAtLevel fun y μ ν h => lt_of_lt_of_le (hV y μ ν h) (by linarith)
    have hfam : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E (T.E / T.η₃)
        (localFamilyOfDensity 0 + θ • localFamilyOfDensity 0) := by
      intro θ _ _
      have e : (localFamilyOfDensity 0 + θ • localFamilyOfDensity 0 : LocalFamily) = localFamilyOfDensity 0 := by
        funext F' y W''
        show (0 : ℝ) + θ • (0 : ℝ) = 0
        simp
      rw [e]
      exact isNormBoundedLocalFamily_zero _ _ _ _ _ _ _ hw hE0 (div_nonneg hE0 hη.le)
    obtain ⟨hfr, ⟨w, hw'⟩, ⟨M, hM⟩, -⟩ := cR t x (localFamilyOfDensity 0) (localFamilyOfDensity 0) 1 hx one_pos
      hfam (isRegularFamily_zero _ _ _ _ _ _ _ hw zero_le_one (div_nonneg zero_le_one hη.le)) F htop _ hcold
    have hm₁ : ¬ ∀ i, 4 * n + 5 < F.extent i := by
      intro h
      have h0 : 4 * n + 5 < n := h 0
      omega
    have d := hD F T.a T.ρA T.ballRadius T.lam x M 0 0 n T.p (localFamilyOfDensity 0) (readAtLevel F F.top V)
      ha hodd hside hm₁ hfr (hM n hm₁)
    have hx0 := hX F T.a T.ρA x 0 (readAtLevel F F.top V) ha hodd hside ⟨w, hw'⟩
    rw [d, Finset.sum_add_distrib, Finset.sum_add_distrib, hx0]
    simp only [expansionDensity_zero, Finset.sum_const_zero, add_zero]
    rfl
  have hA := minimalAction_of_transports (t := t) hSh hT.chain_admissible ha hodd hσ₀ cG (by omega) g hWc hCar
  have tU : ∀ V : TorusField n, IsCold T.σ V → Filter.Tendsto (U V) Filter.atTop
      (𝓝 (∑ Y ∈ finiteCells F, stepDensity T.a T.ρA T.lam Y (readAtLevel F F.top V))) := fun V hV =>
    tendsto_finsetSum _ fun Y _ => cB t F Y _ htop
      (isSmallCurvature_readAtLevel fun y μ ν h => lt_of_lt_of_le (hV y μ ν h) (by linarith))
  have hd : Filter.Tendsto (fun x => U W' x - U W x) Filter.atTop (𝓝 0) := by
    have h := t₁.sub t₂
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop T.coupling] with x hx
    rw [hstep x, hdisp W hWc x hx, hdisp W' hWc' x hx, hA]
    ring
  have e := tendsto_nhds_unique ((tU W' hWc').sub (tU W hWc)) hd
  have hg : ∀ V : TorusField n, ∑ y, T.stepDensity t n y V =
      ∑ Y ∈ finiteCells F, stepDensity T.a T.ρA T.lam Y (readAtLevel F F.top V) := fun V => by
    rw [sum_finiteCells_eq_sum_torusSite (L := T.L) (t := t) (N := n) (by omega)
      fun Y => stepDensity T.a T.ρA T.lam Y (readAtLevel F F.top V)]
    rfl
  simp only [centered, Finset.sum_sub_distrib]
  rw [hg W', hg W]
  linarith
end ReferenceDensity
end YangMills.Construction
end
