import YangMills.Construction.ColdStepAtMirrorFrames.ColdExpansionIsAnExpansionBelowProof
import YangMills.Construction.ClusterExpansionOfAStep.MovesAlongLinearDirections
import YangMills.Construction.RunningCouplingSlope.TotalOfAStepReadsNoBoundProof
import YangMills.Construction.SummableBoundsOfTheFlow.EnergyUnderAnIsometry
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensityOfTheStepIsCarriedProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheFamilyAtTheLeastFieldIsCarried
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceIsAFamilyBelowProof
import YangMills.Construction.SummableBoundsOfTheFlow.ValuesAboveTheLeastField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps StepCosts EnergySymmetry StepDensities
namespace ReferenceDensity
namespace TorusTransfer
section Casts
variable {a b : ℕ}
private theorem intCast_cast_add (h : a = b) (u v : ZMod a) :
    (((u + v).cast : ℤ) : ZMod b) = ((u.cast : ℤ) : ZMod b) + ((v.cast : ℤ) : ZMod b) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_add <;> assumption
private theorem intCast_cast_intCast_cast (h : a = b) (u : ZMod b) :
    (((((u.cast : ℤ) : ZMod a)).cast : ℤ) : ZMod b) = u := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_roundTrip <;> assumption
end Casts
section Sites
variable {F : BlockFrame} {m : ℕ}
private def frameSiteOf (x : TorusSite m) : F.Site F.depth := siteOfCoords F.depth fun k => ((x k).cast : ℤ)
private theorem toTorusSite_frameSiteOf (hp : ∀ i, F.period F.depth i = m) (x : TorusSite m) :
    toTorusSite m (frameSiteOf (F := F) x) = x :=
  funext fun k => intCast_cast_intCast_cast (hp k) (x k)
private theorem frameSiteOf_toTorusSite (hp : ∀ i, F.period F.depth i = m) (y : F.Site F.depth) :
    frameSiteOf (toTorusSite m y) = y :=
  funext fun k => intCast_cast_intCast_cast (hp k).symm (y k)
private theorem toTorusSite_add_of_period (hp : ∀ i, F.period F.depth i = m) (x y : F.Site F.depth) :
    toTorusSite m (x + y) = toTorusSite m x + toTorusSite m y :=
  funext fun k => intCast_cast_add (hp k) (x k) (y k)
private theorem toTorusSite_sub_of_period (hp : ∀ i, F.period F.depth i = m) (x y : F.Site F.depth) :
    toTorusSite m (x - y) = toTorusSite m x - toTorusSite m y := by apply _root_.YangMills.Construction.FrameTorus.toTorusSite_sub <;> assumption
private theorem toTorusSite_siteOfCoords_of_period (hp : ∀ i, F.period F.depth i = m) (z : Fin 4 → ℤ) :
    toTorusSite m (siteOfCoords (F := F) F.depth z) = siteOfInt z := by apply _root_.YangMills.Construction.FrameTorus.toTorusSite_siteOfCoords <;> assumption
private theorem siteOfInt_single_one (i : Fin 4) :
    (siteOfInt (Pi.single i 1) : TorusSite m) = TorusFields.unitStep m i := by apply _root_.YangMills.Construction.FrameTorusAction.siteOfInt_single <;> assumption
private theorem toTorusSite_unitStep_of_period (hp : ∀ i, F.period F.depth i = m) (i : Fin 4) :
    toTorusSite m (BlockAverages.unitStep (F := F) F.depth i) = TorusFields.unitStep m i := by
  rw [BlockAverages.unitStep, toTorusSite_siteOfCoords_of_period hp, siteOfInt_single_one]
private theorem toTorusSite_injective (hp : ∀ i, F.period F.depth i = m) :
    Function.Injective (toTorusSite m : F.Site F.depth → TorusSite m) := fun x y h => by
  rw [← frameSiteOf_toTorusSite hp x, h, frameSiteOf_toTorusSite hp y]
private theorem restrictToTorus_apply (hp : ∀ i, F.period F.depth i = m) (W : F.GaugeField F.depth)
    (y : F.Site F.depth) (i : Fin 4) :
    restrictToTorus m W (toTorusSite m y) i = W y i := by apply _root_.YangMills.Construction.FrameTorus.restrictToTorus_apply <;> assumption
private theorem isCold_restrictToTorus (hp : ∀ i, F.period F.depth i = m) {s : ℝ} {W : F.GaugeField F.depth}
    (h : IsSmallCurvature s W) : IsCold s (restrictToTorus m W) := by apply _root_.YangMills.Construction.FrameTorus.isCold_restrictToTorus <;> assumption
private theorem restrictToTorus_gaugeTransform (hp : ∀ i, F.period F.depth i = m)
    (γ : F.Site F.depth → UnitQuaternion) (W : F.GaugeField F.depth) :
    restrictToTorus m (BlockAverages.gaugeTransform γ W) =
      TorusFields.gaugeTransform (fun x => γ (frameSiteOf x)) (restrictToTorus m W) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TorusCoordinates.restrictToTorus_gaugeTransform <;> assumption
end Sites
private theorem period_eq_of_isCubicTorusAbove {L t n₀ : ℕ} {F : BlockFrame} (h : IsCubicTorusAbove L t n₀ F) :
    (∀ i, F.period F.depth i = F.period F.depth 0) ∧ n₀ ≤ F.period F.depth 0 := by apply _root_.YangMills.Construction.FrameTorus.period_eq_of_isCubicTorusAbove <;> assumption
end TorusTransfer
namespace MinimizerTransport
open TorusTransfer
section Frames
variable {F : BlockFrame}
private theorem fieldAboveFrame_zero (a ρ : ℝ) (V : F.GaugeField F.top) :
    fieldAboveFrame true a ρ 0 V 0 = chartedField (minimizingCoordinates a (finiteCells F) V ρ) V := by apply _root_.YangMills.SharedProofs.p22006 <;> assumption
private theorem blockEnergy_fieldAboveFrame_le {a ρ N₀ s : ℝ} {V : F.GaugeField F.top}
    (h : HasColdMinimizer a ρ N₀ s (finiteCells F) V) (W' : F.GaugeField F.depth) :
    blockEnergy a (finiteCells F) F.depth (fieldAboveFrame true a ρ 0 V 0) V ≤
      blockEnergy a (finiteCells F) F.depth W' V := by
  obtain ⟨w, hw, -, -⟩ := h
  have hex : ∃ w, IsMinimizingChart a (finiteCells F) V ρ w :=
    ⟨w, hw.1, fun b hb => (hw.2.1 b hb).trans (min_le_left _ _), hw.2.2⟩
  have hl : IsMinimizingChart a (finiteCells F) V ρ (minimizingCoordinates a (finiteCells F) V ρ) := by
    unfold minimizingCoordinates
    rw [dif_pos hex]
    exact hex.choose_spec
  rw [fieldAboveFrame_zero]
  exact hl.2.2 W'
private theorem exists_gauge_of_minimizers (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {a ρ N₀ s : ℝ}
    {V : F.GaugeField F.top} (h : HasColdMinimizer a ρ N₀ s (finiteCells F) V) {W₁ W₂ : F.GaugeField F.depth}
    (h₁ : ∀ W' : F.GaugeField F.depth, blockEnergy a (finiteCells F) F.depth W₁ V ≤ blockEnergy a (finiteCells F) F.depth W' V)
    (h₂ : ∀ W' : F.GaugeField F.depth, blockEnergy a (finiteCells F) F.depth W₂ V ≤ blockEnergy a (finiteCells F) F.depth W' V) :
    ∃ γ : F.Site F.depth → UnitQuaternion, W₁ = BlockAverages.gaugeTransform γ W₂ := by
  obtain ⟨w, -, -, hg⟩ := h
  obtain ⟨γ₁, -, e₁⟩ := hg W₁ h₁
  obtain ⟨γ₂, -, e₂⟩ := hg W₂ h₂
  have hb : ∀ (x : F.Site F.depth) (i : Fin 4), (x, i) ∈ innerBonds (finiteCells F) F.depth := by
    intro x i
    unfold innerBonds
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨LinearDirections.mem_sitesOfCells_finiteCells hL hs x,
      Finset.mem_univ _⟩, LinearDirections.mem_sitesOfCells_finiteCells hL hs _⟩
  refine ⟨fun x => γ₁ x * (γ₂ x)⁻¹, ?_⟩
  funext x i
  have a₁ := e₁ (x, i) (hb x i)
  have a₂ := e₂ (x, i) (hb x i)
  simp only [BlockAverages.gaugeTransform] at a₁ a₂ ⊢
  rw [a₁, a₂]
  group
private theorem sum_centredExpansion_eq_sum_centered (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [NeZero (F.period F.depth 0)] (hp : ∀ i, F.period F.depth i = F.period F.depth 0) (a ρ : ℝ) (f : LocalDensity)
    (V : F.GaugeField F.top) :
    ∑ y' ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion true a ρ 0 (localFamilyOfDensity f) y' 0 V =
      ∑ z : TorusSite (F.period F.depth 0), centered f _ z (restrictToTorus _ (fieldAboveFrame true a ρ 0 V 0)) := by
  refine Finset.sum_bij (fun y' _ => toTorusSite (F.period F.depth 0) y') (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro x _ y _ h
    exact toTorusSite_injective hp h
  · intro z _
    exact ⟨frameSiteOf z, LinearDirections.mem_sitesOfCells_finiteCells hL hs _, toTorusSite_frameSiteOf hp z⟩
  · intro y' _
    rfl
end Frames
section Top
variable {L t n : ℕ}
private theorem period_torusFrame (i : Fin 4) : (torusFrame L t n).period (torusFrame L t n).top i = n := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.torusFrame_period_top <;> assumption
private theorem mem_finiteCells_torusFrame [NeZero n] (z : (torusFrame L t n).Cell) : z ∈ finiteCells (torusFrame L t n) :=
  TopLevelSites.mem_finiteCells (fun _ => Nat.pos_of_ne_zero (NeZero.ne n)) z
private theorem isSmallCurvature_readAtLevel [NeZero n] {s : ℝ} {V : TorusField n} (hV : IsCold s V) :
    IsSmallCurvature (F := torusFrame L t n) s (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by apply _root_.YangMills.SharedProofs.p2155 <;> assumption
private theorem transportsField_readAtLevel [NeZero n] (g : TorusIsometry) {W W' : TorusField n}
    (h : g.Transports W W') :
    CubicSymmetry.TransportsField (F := torusFrame L t n) ⟨g.axisPerm, g.axisSign, g.offset⟩
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top W') := by apply _root_.YangMills.SharedProofs.p26341 <;> assumption
private theorem sum_familyAtMinimizer_eq [NeZero n] (hL : Odd L) (h2 : 2 ≤ n) (a ρ : ℝ) (f : LocalDensity)
    [NeZero ((torusFrame L t n).period (torusFrame L t n).depth 0)]
    (hp : ∀ i, (torusFrame L t n).period (torusFrame L t n).depth i =
      (torusFrame L t n).period (torusFrame L t n).depth 0) (V : TorusField n) :
    ∑ y, familyAtMinimizer a ρ L t f n y V =
      ∑ z : TorusSite ((torusFrame L t n).period (torusFrame L t n).depth 0), centered f _ z (restrictToTorus _
        (fieldAboveFrame true a ρ 0 (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) 0)) := by
  classical
  have hs : ∀ i, 2 ≤ (torusFrame L t n).extent i := fun _ => h2
  rw [← sum_centredExpansion_eq_sum_centered (F := torusFrame L t n) hL hs hp a ρ f]
  have hcell : ∀ y' ∈ sitesOfCells (finiteCells (torusFrame L t n)) (torusFrame L t n).depth,
      enclosingCell y' ∈ finiteCells (torusFrame L t n) := fun _ _ => mem_finiteCells_torusFrame _
  rw [← Finset.sum_fiberwise_of_maps_to hcell]
  refine Finset.sum_bij (fun z _ => torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top z)
    (fun z _ => mem_finiteCells_torusFrame _) ?_ ?_ ?_
  · intro z _ z' _ h
    have := congrArg (toTorusSite n) h
    rwa [TopLevelSites.toTorusSite_torusSiteInFrame period_torusFrame,
      TopLevelSites.toTorusSite_torusSiteInFrame period_torusFrame] at this
  · intro w _
    exact ⟨toTorusSite n w, Finset.mem_univ _, TopLevelSites.torusSiteInFrame_toTorusSite period_torusFrame w⟩
  · intro z _
    show cellCentredExpansion true a ρ 0 (localFamilyOfDensity f) _ 0 _ = _
    unfold cellCentredExpansion
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext y'
    simp only [Finset.mem_filter]
    exact Iff.rfl
private theorem toTorusSite_actSite_scaledLift {m : ℕ} [NeZero m] (g : TorusIsometry)
    (hp : ∀ i, (torusFrame L t n).period (torusFrame L t n).depth i = m)
    (x : (torusFrame L t n).Site (torusFrame L t n).depth) :
    toTorusSite m (CubicSymmetry.actSite ⟨g.axisPerm, g.axisSign, g.offset⟩ (torusFrame L t n).depth x) =
      (g.scaledLift L).mapSite (toTorusSite m x) := by
  have hpow : (((torusFrame L t n).blockSide : ℕ) : ℤ) ^ ((torusFrame L t n).top - (torusFrame L t n).depth) =
      (L : ℤ) := by
    rw [TopLevelSites.top_sub_depth]
    simp [torusFrame]
  unfold CubicSymmetry.actSite
  rw [TopLevelSites.toTorusSite_siteOfCoords hp, hpow]
  funext i
  simp [siteOfInt, TorusIsometry.mapSite, TorusIsometry.scaledLift, toTorusSite]
private theorem transports_restrictToTorus {m : ℕ} [NeZero m] (g : TorusIsometry)
    (hp : ∀ i, (torusFrame L t n).period (torusFrame L t n).depth i = m)
    (Wl Wi : (torusFrame L t n).GaugeField (torusFrame L t n).depth)
    (hst : ∀ (x : (torusFrame L t n).Site (torusFrame L t n).depth) (k : Fin 4),
      linkValue Wi (CubicSymmetry.actSite ⟨g.axisPerm, g.axisSign, g.offset⟩ (torusFrame L t n).depth x)
        (CubicSymmetry.actStep ⟨g.axisPerm, g.axisSign, g.offset⟩ k) = Wl x k) :
    (g.scaledLift L).Transports (restrictToTorus m Wl) (restrictToTorus m Wi) := by
  intro x k
  have hc := hst (frameSiteOf x) k
  have hs := toTorusSite_actSite_scaledLift g hp (frameSiteOf x)
  rw [toTorusSite_frameSiteOf hp] at hs
  have hv : restrictToTorus m Wl x k = Wl (frameSiteOf x) k := rfl
  unfold linkValue CubicSymmetry.actStep at hc
  show if g.axisSign (g.axisPerm.symm k) = 1 then
      restrictToTorus m Wi ((g.scaledLift L).mapSite x) (g.axisPerm.symm k) = restrictToTorus m Wl x k
    else (restrictToTorus m Wi ((g.scaledLift L).mapSite x - TorusFields.unitStep m (g.axisPerm.symm k))
      (g.axisPerm.symm k))⁻¹ = restrictToTorus m Wl x k
  by_cases hg : g.axisSign (g.axisPerm.symm k) = 1
  · simp only [hg, decide_true, if_true] at hc ⊢
    rw [← hs, restrictToTorus_apply hp, hv]
    exact hc
  · simp only [hg, decide_false, if_false, Bool.false_eq_true] at hc ⊢
    have e : (g.scaledLift L).mapSite x - TorusFields.unitStep m (g.axisPerm.symm k) =
        toTorusSite m (CubicSymmetry.actSite ⟨g.axisPerm, g.axisSign, g.offset⟩ (torusFrame L t n).depth (frameSiteOf x) -
          BlockAverages.unitStep (torusFrame L t n).depth (g.axisPerm.symm k)) := by
      rw [toTorusSite_sub_of_period hp, toTorusSite_unitStep_of_period hp, hs]
    rw [e, restrictToTorus_apply hp, hv]
    exact hc
end Top
private theorem sum_centered_invariant (hEn : BlockEnergySymmetric) (T : ColdStepAtMirrorFrames.StepParameters)
    (hdr : T.IsOrdered) (hσA : 5 / 4 * T.σ ≤ T.chainParams.σA) (h64 : 64 ≤ T.n₀)
    (hvals : ∀ (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)),
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → (∀ b, ‖η b‖ ≤ T.ballRadius) →
      IsSmallCurvature T.σ (fieldAboveFrame true T.a T.ρA 0 V η))
    (ℓ : TorusLumps.StepParameters) (hm : T.Compatible ℓ) (t : ℕ) (f : LocalDensity)
    (hpl : IsAdmissibleDensity ℓ f) (hcar : SumInvariantUnderIsometries ℓ f) (n : ℕ) [NeZero n] (hnn : T.n₀ ≤ n)
    (g : TorusIsometry) (W W' : TorusField n) (hW : IsCold T.σ W) (hW' : IsCold T.σ W') (hC : g.Transports W W') :
    ∑ y, centered (familyAtMinimizer T.a T.ρA T.L t f) n y W' =
      ∑ y, centered (familyAtMinimizer T.a T.ρA T.L t f) n y W := by
  have hσ := hdr.σ_pos
  have e : ∀ V : TorusField n, ∑ y, centered (familyAtMinimizer T.a T.ρA T.L t f) n y V =
      ∑ y, familyAtMinimizer T.a T.ρA T.L t f n y V - ∑ y, familyAtMinimizer T.a T.ρA T.L t f n y (trivialField n) :=
    fun V => Finset.sum_sub_distrib _ _
  suffices h : ∑ y, familyAtMinimizer T.a T.ρA T.L t f n y W' = ∑ y, familyAtMinimizer T.a T.ρA T.L t f n y W by
    rw [e, e, h]
  have hLpos : 1 ≤ T.L := hdr.odd_L.pos
  have hlow : IsCubicTorusAbove T.L t T.n₀ (torusFrame T.L t n) :=
    ⟨rfl, rfl, n, fun _ => rfl, hnn.trans (Nat.le_mul_of_pos_right _ hLpos)⟩
  obtain ⟨hp, hmm⟩ := period_eq_of_isCubicTorusAbove hlow
  have : NeZero ((torusFrame T.L t n).period (torusFrame T.L t n).depth 0) := ⟨by omega⟩
  have h2 : 2 ≤ n := by omega
  rw [sum_familyAtMinimizer_eq hdr.odd_L h2 T.a T.ρA f hp W', sum_familyAtMinimizer_eq hdr.odd_L h2 T.a T.ρA f hp W]
  have hA : CubicSymmetry.IsSymmetry ⟨g.axisPerm, g.axisSign, g.offset⟩ (torusFrame T.L t n) :=
    ⟨g.axisSign_unit, fun _ _ => rfl⟩
  obtain ⟨he, hon, hst⟩ := hEn (torusFrame T.L t n) T.a _ _ _ _ ⟨g.axisPerm, g.axisSign, g.offset⟩ hdr.odd_L hA
    (fun _ => ⟨fun _ => mem_finiteCells_torusFrame _, fun _ => mem_finiteCells_torusFrame _⟩)
    (transportsField_readAtLevel g hC)
  have cl : ∀ V : TorusField n, IsCold T.σ V →
      HasColdMinimizer T.a T.chainParams.ρA (T.chainParams.N 0) T.σ (finiteCells (torusFrame T.L t n))
        (readAtLevel (torusFrame T.L t n) (torusFrame T.L t n).top V) := fun V hV =>
    (hdr.chain_admissible.estimates _ T.σ _ ⟨rfl, n, by omega, fun _ => rfl⟩ hσ (by linarith)
      (isSmallCurvature_readAtLevel hV)).minimizer
  have hWi : ∀ W'' : (torusFrame T.L t n).GaugeField (torusFrame T.L t n).depth,
      blockEnergy T.a (finiteCells (torusFrame T.L t n)) (torusFrame T.L t n).depth
        (transportField ⟨g.axisPerm, g.axisSign, g.offset⟩
          (fieldAboveFrame true T.a T.chainParams.ρA 0 (readAtLevel (torusFrame T.L t n) (torusFrame T.L t n).top W) 0))
        (readAtLevel (torusFrame T.L t n) (torusFrame T.L t n).top W') ≤
      blockEnergy T.a (finiteCells (torusFrame T.L t n)) (torusFrame T.L t n).depth W''
        (readAtLevel (torusFrame T.L t n) (torusFrame T.L t n).top W') := by
    intro W''
    obtain ⟨X, rfl⟩ := hon W''
    rw [he, he]
    exact blockEnergy_fieldAboveFrame_le (cl W hW) X
  obtain ⟨γ, hγ⟩ := exists_gauge_of_minimizers (F := torusFrame T.L t n) hdr.odd_L (fun _ => h2) (cl W' hW') hWi
    (blockEnergy_fieldAboveFrame_le (cl W' hW'))
  have hρ : ∀ (b : ↥(chordBonds (finiteCells (torusFrame T.L t n)))),
      ‖(0 : StepVariable (finiteCells (torusFrame T.L t n))) b‖ ≤ T.ballRadius := fun b => by
    simpa using (show (0 : ℝ) ≤ T.ballRadius by
      unfold ColdStepAtMirrorFrames.StepParameters.ballRadius; positivity)
  have hTop : IsCubicTopTorus T.L t T.n₀ (torusFrame T.L t n) := ⟨rfl, rfl, n, fun _ => rfl, hnn⟩
  have hcold : ∀ V : TorusField n, IsCold T.σ V →
      IsCold ℓ.threshold (restrictToTorus ((torusFrame T.L t n).period (torusFrame T.L t n).depth 0)
        (fieldAboveFrame true T.a T.chainParams.ρA 0 (readAtLevel (torusFrame T.L t n) (torusFrame T.L t n).top V) 0)) := by
    intro V hV
    rw [hm.threshold_eq]
    exact isCold_restrictToTorus hp (hvals t _ _ 0 hTop
      (isSmallCurvature_readAtLevel fun x μ ν h => lt_of_lt_of_le (hV x μ ν h) (by linarith)) hρ)
  have hUU := congrArg (restrictToTorus ((torusFrame T.L t n).period (torusFrame T.L t n).depth 0)) hγ
  rw [restrictToTorus_gaugeTransform hp] at hUU
  have hcU'' : IsCold ℓ.threshold (restrictToTorus ((torusFrame T.L t n).period (torusFrame T.L t n).depth 0)
      (transportField ⟨g.axisPerm, g.axisSign, g.offset⟩
        (fieldAboveFrame true T.a T.chainParams.ρA 0 (readAtLevel (torusFrame T.L t n) (torusFrame T.L t n).top W) 0))) := by
    rw [hUU]
    intro x μ ν h
    rw [curvature_gaugeTransform]
    exact hcold W' hW' x μ ν h
  have hCar := transports_restrictToTorus g hp _ _
    (hst (fieldAboveFrame true T.a T.chainParams.ρA 0 (readAtLevel (torusFrame T.L t n) (torusFrame T.L t n).top W) 0))
  have hmm' : ℓ.n₀ ≤ (torusFrame T.L t n).period (torusFrame T.L t n).depth 0 := by
    rw [hm.n₀_eq]
    exact hmm
  have h1 := hcar _ hmm' (g.scaledLift T.L) _ _ (hcold W hW) hcU'' hCar
  rw [hUU] at h1
  have h3 : ∑ z, centered f ((torusFrame T.L t n).period (torusFrame T.L t n).depth 0) z
      (TorusFields.gaugeTransform (fun x => γ (frameSiteOf x)) (restrictToTorus _
        (fieldAboveFrame true T.a T.chainParams.ρA 0 (readAtLevel (torusFrame T.L t n) (torusFrame T.L t n).top W') 0))) =
      ∑ z, centered f _ z (restrictToTorus _
        (fieldAboveFrame true T.a T.chainParams.ρA 0 (readAtLevel (torusFrame T.L t n) (torusFrame T.L t n).top W') 0)) :=
    Finset.sum_congr rfl fun z _ => by
      unfold centered
      rw [hpl.gauge _ hmm' z _ _ (hcold W' hW')]
  exact h3.symm.trans h1
end MinimizerTransport
open MinimizerTransport in
theorem familyAtMinimizerInvariant (hFr : FrameBoundsEventually)
    (hVal : valuesAboveFrameBoundedStatement) (hEn : BlockEnergySymmetric) :
    FamilyAtMinimizerInvariant := by
  have hVal' : EventuallyOrdered _ := hVal
  have hFr' : EventuallyInParameters FrameBoundsForParameters := hFr
  unfold FamilyAtMinimizerInvariant EventuallyOrdered
  refine EventuallyInParameters.mono (EventuallyInParameters.and hFr' hVal') ?_
  rintro T ⟨hF, hV⟩ hdr hn ℓ hm hfits t f hpl hcar n _ hnn g W W' hW hW' hC
  obtain ⟨R₀, -, hvals⟩ := hV hdr hn
  obtain ⟨Cf, C, -, -, -, -, -, h64, -, -, -, -, hσA, -, -, -⟩ := hF
  rw [hm.n₀_eq] at hnn
  rw [hm.threshold_eq] at hW hW'
  exact sum_centered_invariant hEn T hdr hσA h64 (fun t F V η hF hV hη => (hvals t F V η hF hV hη).1) ℓ hm t f hpl
    hcar n hnn g W W' hW hW' hC
end ReferenceDensity
end YangMills.Construction
end
