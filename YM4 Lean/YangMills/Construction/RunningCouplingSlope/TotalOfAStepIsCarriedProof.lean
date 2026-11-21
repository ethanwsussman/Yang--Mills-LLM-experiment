import YangMills.Construction.RunningCouplingSlope.ValueOfTheDensityOfTheStepOnTwoToriAtParametersProof
import YangMills.Construction.ClusterExpansionOfAStep.BondInCoordinates
import YangMills.Construction.ClusterExpansionOfAStep.SitesOfTheTopOfAStep
import YangMills.Construction.RunningCouplingSlope.AmplitudeUnderAnIsometry
import YangMills.Construction.RunningCouplingSlope.LeastFieldNearTheFlatField
import YangMills.Construction.RunningCouplingSlope.LengthsOfTheMeansUnderAnIsometry
import YangMills.Construction.RunningCouplingSlope.TotalOfAStepIsCarried
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open Filter
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps EnergySymmetry SlopeCoefficient
  ReferenceDensity BondCoordinates TopLevelSites
namespace RunningCouplingSlope.StepGaugeTotalIsometryInvariant
section OnAFrame
variable {F : BlockFrame}
private theorem coordsAboveFrame_zero (a ρ : ℝ) (V : F.GaugeField F.top) :
    coordsAboveFrame true a ρ 0 V 0 = minimizingCoordinates a (finiteCells F) V ρ := by apply _root_.YangMills.DeltaSharedProofs.p501121 <;> assumption
private theorem isMinimizingChart_coordsAboveFrame {a ρ : ℝ} {V : F.GaugeField F.top}
    (h : ∃ w, IsMinimizingChart a (finiteCells F) V ρ w) :
    IsMinimizingChart a (finiteCells F) V ρ (coordsAboveFrame true a ρ 0 V 0) := by
  rw [coordsAboveFrame_zero]
  unfold minimizingCoordinates
  rw [dif_pos h]
  exact h.choose_spec
private theorem stepLogAmplitude_eq (hE : BlockEnergySymmetric) (hA : stepAmplitudeSymmetryStatement)
    (hM : LogContourLengthsSymmetric) {a ρ : ℝ} (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    {g : CubicSymmetry} (hg : g.IsSymmetry F) (h0 : 0 < ρ) (h1 : ρ ≤ 1) {V V' : F.GaugeField F.top}
    (hC : g.TransportsField V V')
    (hw : ∃ w, IsMinimizingChart a (finiteCells F) V ρ w) (hw' : ∃ w, IsMinimizingChart a (finiteCells F) V' ρ w)
    (hu : ∀ W' : F.GaugeField F.depth,
      (∀ W'', blockEnergy a (finiteCells F) F.depth W' V' ≤ blockEnergy a (finiteCells F) F.depth W'' V') →
      ∃ γ : F.Site F.depth → UnitQuaternion, (∀ z : F.Cell, γ (cellCentre _ z) = 1) ∧
        W' = BlockAverages.gaugeTransform γ (fieldAboveFrame true a ρ 0 V' 0))
    (hp : (chartedHessian a ρ V 0).PosDef) (hp' : (chartedHessian a ρ V' 0).PosDef) :
    stepLogAmplitude a ρ V' = stepLogAmplitude a ρ V := by
  have hall : ∀ z : F.Cell, z ∈ finiteCells F := BlockOffsets.mem_finiteCells hs
  have hl := isMinimizingChart_coordsAboveFrame hw
  have hl' := isMinimizingChart_coordsAboveFrame hw'
  obtain ⟨e1, e2, -⟩ := hE F a (finiteCells F) (finiteCells F) V V' g hodd hg
    (fun z => ⟨fun _ => hall _, fun _ => hall _⟩) hC
  have hmin : ∀ W'', blockEnergy a (finiteCells F) F.depth (transportField g (fieldAboveFrame true a ρ 0 V 0)) V' ≤
      blockEnergy a (finiteCells F) F.depth W'' V' := by
    intro W''
    obtain ⟨W, rfl⟩ := e2 W''
    rw [e1, e1]
    exact hl.2.2 W
  obtain ⟨γ, hγ, hi⟩ := hu _ hmin
  have ha := hA F a ρ V V' g γ hodd hs hg h0 h1 hC hl hl' hγ hi hp hp'
  have hm := hM F _ _ g γ hodd hs hg hγ hi
  unfold stepLogAmplitude
  rw [ha, hm]
end OnAFrame
variable {n : ℕ}
private def preimageSite (g : TorusIsometry) (y : TorusSite n) : TorusSite n :=
  fun k => (g.axisSign (g.axisPerm.symm k) : ZMod n) *
    (y (g.axisPerm.symm k) - (g.offset (g.axisPerm.symm k) : ZMod n))
private theorem mapSite_preimageSite (g : TorusIsometry) (y : TorusSite n) : g.mapSite (preimageSite g y) = y := by
  funext i
  have hs : ((g.axisSign i : ℤ) : ZMod n) * (g.axisSign i : ZMod n) = 1 := by
    rcases g.axisSign_unit i with h | h <;> rw [h] <;> simp
  simp only [TorusIsometry.mapSite, preimageSite, Equiv.symm_apply_apply]
  linear_combination (y i - (g.offset i : ZMod n)) * hs
private def pushField (g : TorusIsometry) (V : TorusField n) : TorusField n := fun y i =>
  if g.axisSign i = 1 then V (preimageSite g y) (g.axisPerm i)
  else (V (preimageSite g (y + TorusFields.unitStep n i)) (g.axisPerm i))⁻¹
private theorem eq_pushField {g : TorusIsometry} {V V' : TorusField n} (h : g.Transports V V') :
    V' = pushField g V := by
  funext y i
  have hp : g.axisPerm.symm (g.axisPerm i) = i := by simp
  unfold pushField
  by_cases hs : g.axisSign i = 1
  · have := h (preimageSite g y) (g.axisPerm i)
    rw [hp, if_pos hs, mapSite_preimageSite] at this
    rw [if_pos hs]
    exact this.trans rfl
  · have := h (preimageSite g (y + TorusFields.unitStep n i)) (g.axisPerm i)
    rw [hp, if_neg hs, mapSite_preimageSite, add_sub_cancel_right] at this
    rw [if_neg hs, ← this, inv_inv]
private theorem continuous_pushField (g : TorusIsometry) : Continuous (pushField (n := n) g) := by
  refine continuous_pi fun y => continuous_pi fun i => ?_
  unfold pushField
  by_cases hs : g.axisSign i = 1
  · simp only [if_pos hs]
    exact continuous_apply_apply _ _
  · simp only [if_neg hs]
    exact (continuous_apply_apply _ _).inv
private theorem pushField_trivialField (g : TorusIsometry) : pushField g (trivialField n) = trivialField n := by
  funext y i
  unfold pushField trivialField
  split_ifs <;> simp
private theorem toTorusSite_actSite {L t : ℕ} [NeZero n] (g : TorusIsometry) (x : (torusFrame L t n).Cell) :
    toTorusSite n (CubicSymmetry.actSite ⟨g.axisPerm, g.axisSign, g.offset⟩ (torusFrame L t n).top x) =
      g.mapSite (toTorusSite n x) := by
  unfold CubicSymmetry.actSite
  rw [toTorusSite_siteOfCoords (fun i => TopLevelSites.period_top i)]
  funext i
  simp [siteOfInt, TorusIsometry.mapSite, toTorusSite]
private theorem transportsField_readAtLevel {L t : ℕ} [NeZero n] (g : TorusIsometry) {W W' : TorusField n}
    (h : g.Transports W W') :
    CubicSymmetry.TransportsField (F := torusFrame L t n) ⟨g.axisPerm, g.axisSign, g.offset⟩
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top W') := by
  intro x k
  have per_eq : ∀ i : Fin 4, (torusFrame L t n).period (torusFrame L t n).top i = n :=
    fun i => TopLevelSites.period_top i
  have hc := h (toTorusSite n x) k
  have hr : ∀ (V : TorusField n) (z : (torusFrame L t n).Cell) (i : Fin 4),
      readAtLevel (torusFrame L t n) (torusFrame L t n).top V z i = V (toTorusSite n z) i := fun _ _ _ => rfl
  unfold linkValue CubicSymmetry.actStep
  by_cases hs : g.axisSign (g.axisPerm.symm k) = 1
  · simp only [hs, decide_true, if_true] at hc ⊢
    rw [hr, hr, toTorusSite_actSite]
    exact hc
  · simp only [hs, decide_false, if_false, Bool.false_eq_true] at hc ⊢
    rw [hr, hr, sub_eq_add_neg, toTorusSite_add per_eq, toTorusSite_neg per_eq, toTorusSite_unitStep per_eq,
      toTorusSite_actSite, ← sub_eq_add_neg]
    exact hc
theorem of_components (hLF : MinimizerNearTrivialField) (hE : BlockEnergySymmetric)
    (hA : stepAmplitudeSymmetryStatement) (hM : LogContourLengthsSymmetric) :
    StepGaugeTotalIsometryInvariant := by
  intro a ha L hL t ρ h0 hρ
  filter_upwards [eventually_ge_atTop (2 * L)] with n hn g
  have hL13 := hL.2
  have : NeZero n := ⟨by omega⟩
  have hs : ∀ i, 2 ≤ (torusFrame L t n).extent i := fun _ => by
    show 2 ≤ n
    omega
  have hodd : Odd (torusFrame L t n).blockSide := hL.1
  have hg : CubicSymmetry.IsSymmetry ⟨g.axisPerm, g.axisSign, g.offset⟩ (torusFrame L t n) :=
    ⟨g.axisSign_unit, fun _ _ => rfl⟩
  have hG := (hLF a ha L hL t n ρ hn h0 hρ).2
  have hq : Tendsto (pushField g) (𝓝 (trivialField n)) (𝓝 (trivialField n)) := by
    have := (continuous_pushField (n := n) g).tendsto (trivialField n)
    rwa [pushField_trivialField] at this
  filter_upwards [hG, hq.eventually hG] with V hV hV' V' hC
  obtain rfl : V' = pushField g V := eq_pushField hC
  obtain ⟨hw, -, hp, -, -⟩ := hV
  obtain ⟨hw', hu', hp', -, -⟩ := hV'
  unfold stepGaugeTotal
  rw [stepLogAmplitude_eq hE hA hM hodd hs hg h0 hρ (transportsField_readAtLevel g hC) hw hw' hu' hp hp']
end RunningCouplingSlope.StepGaugeTotalIsometryInvariant
end YangMills.Construction
end
