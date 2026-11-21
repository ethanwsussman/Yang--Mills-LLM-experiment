import YangMills.Construction.ClusterExpansionOfAStep.ChartsOverTheTopOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TopLevelSites TorusFields TorusLumps StepSettings StepCosts
namespace TorusCharts
variable {n : ℕ} [NeZero n]
def IsBlockEndBond (L : ℕ) {m : ℕ} (x : TorusSite m) (i : Fin 4) : Prop :=
  offsetFromCentre L ((x i).cast : ℤ) = halfWidth L
def IsBlockTreeBond (L : ℕ) {m : ℕ} (x : TorusSite m) (i : Fin 4) : Prop :=
  IsTreeOffset L ((fun l => offsetFromCentre L ((x l).cast : ℤ)), i)
open Classical in
def torusChart (L : ℕ) (w : TorusBond (n * L) → imaginaryQuaternions) (V : TorusField n) :
    TorusField (n * L) := fun x i =>
  if IsBlockEndBond L x i then expUnit (w (x, i)) * V (parentBlock L x) i
  else if IsBlockTreeBond L x i then 1 else expUnit (w (x, i))
theorem torusChart_congr {L : ℕ} {w w' : TorusBond (n * L) → imaginaryQuaternions} (V : TorusField n)
    {x : TorusSite (n * L)} {i : Fin 4}
    (h : w (x, i) = w' (x, i)) : torusChart L w V x i = torusChart L w' V x i := by
  unfold torusChart
  rw [h]
variable {F : BlockFrame}
theorem chartedField_readAtLevel (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide) (h2 : 2 ≤ n)
    [NeZero (n * F.blockSide)]
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : TorusField n) (x : TorusSite (n * F.blockSide))
    (i : Fin 4) :
    chartedField w (readAtLevel F F.top V) (torusSiteInFrame F F.depth x) i =
      torusChart F.blockSide (fun b => w (torusSiteInFrame F F.depth b.1) b.2) V x i := by
  unfold chartedField torusChart
  by_cases h1 : IsCrossingBond (torusSiteInFrame F F.depth x, i)
  · have h1' : IsBlockEndBond F.blockSide x i := (isCrossingBond_torusSiteInFrame_iff hn hL h2 x i).mp h1
    rw [if_pos h1, if_pos h1', enclosingCell_torusSiteInFrame hn,
      readAtLevel_torusSiteInFrame (period_top_of_extent hn)]
  · have h1' : ¬ IsBlockEndBond F.blockSide x i :=
      fun h => h1 ((isCrossingBond_torusSiteInFrame_iff hn hL h2 x i).mpr h)
    rw [if_neg h1, if_neg h1']
    by_cases h3 : IsAxialTreeBond (torusSiteInFrame F F.depth x, i)
    · have h3' : IsBlockTreeBond F.blockSide x i := (isAxialTreeBond_torusSiteInFrame_iff hn hL h2 x i).mp h3
      rw [if_pos h3, if_pos h3']
    · have h3' : ¬ IsBlockTreeBond F.blockSide x i :=
        fun h => h3 ((isAxialTreeBond_torusSiteInFrame_iff hn hL h2 x i).mpr h)
      rw [if_neg h3, if_neg h3']
variable {R : StepSetup}
theorem stepBlockFrame_extent (L n : ℕ) (i : Fin 4) : (stepBlockFrame L n).extent i = n := rfl
theorem gaugeTransform_axialGauge_eq_torusChart (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide) (h2 : 2 ≤ n)
    [NeZero (n * F.blockSide)] (W : TorusField (n * F.blockSide)) (V : TorusField n) :
    TorusFields.gaugeTransform (fun x => axialGauge 1 (readAtLevel F F.depth W) (torusSiteInFrame F F.depth x)) W =
      torusChart F.blockSide
        (fun b => bondCoordinate 1 (readAtLevel F F.top V) (readAtLevel F F.depth W) (torusSiteInFrame F F.depth b.1, b.2))
        V := by
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hn]; exact h2
  funext x i
  have h := axialGauge_eq_chartedField hL hs (readAtLevel F F.top V) (readAtLevel F F.depth W)
    (torusSiteInFrame F F.depth x) i
  have e := chartedField_readAtLevel hn hL h2
    (fun x i => bondCoordinate 1 (readAtLevel F F.top V) (readAtLevel F F.depth W) (x, i)) V x i
  have hnext : torusSiteInFrame F F.depth x + BlockAverages.unitStep F.depth i =
      torusSiteInFrame F F.depth (x + TorusFields.unitStep (n * F.blockSide) i) := by
    apply toTorusSite_injective (period_depth_of_extent hn)
    rw [toTorusSite_torusSiteInFrame (period_depth_of_extent hn), toTorusSite_add (period_depth_of_extent hn),
      toTorusSite_torusSiteInFrame (period_depth_of_extent hn), toTorusSite_unitStep (period_depth_of_extent hn)]
  have hread : readAtLevel F F.depth W (torusSiteInFrame F F.depth x) i = W x i :=
    readAtLevel_torusSiteInFrame (period_depth_of_extent hn) W x i
  unfold BlockAverages.gaugeTransform at h
  rw [hread, hnext] at h
  exact h.trans e
theorem gaugeTransform_gaugeAt_eq_torusChart (hL : Odd R.params.side) (h2 : 2 ≤ n)
    [NeZero (n * R.params.side)] (W : TorusField (n * R.params.side)) (V : TorusField n) :
    TorusFields.gaugeTransform (gaugeAt (R := R) W) W = torusChart R.params.side (chartCoord R.params V W) V := by
  haveI : NeZero (n * (stepBlockFrame R.params.side n).blockSide) := inferInstanceAs (NeZero (n * R.params.side))
  exact gaugeTransform_axialGauge_eq_torusChart (F := stepBlockFrame R.params.side n)
    (stepBlockFrame_extent R.params.side n) hL h2 W V
end TorusCharts
namespace StepSettings.ChartSetting
open TorusCharts
variable {R : StepSetup} {n : ℕ} [NeZero n]
def coordinates (s : ChartSetting R n) (η : FreeCoords s.free) (b : TorusBond (n * R.params.side)) :
    imaginaryQuaternions :=
  open Classical in
  if h : b ∈ s.free then s.frame b + toImaginary (η ⟨b, h⟩) else chartCoord R.params s.coarse s.fine b
theorem gaugeTransform_field_eq_torusChart [NeZero (n * R.params.side)] (hL : Odd R.params.side) (h2 : 2 ≤ n)
    (s : ChartSetting R n) (hs : s.free ⊆ chartBonds R.params.side n) (η : FreeCoords s.free) :
    TorusFields.gaugeTransform (gaugeAt (R := R) s.fine) (s.field η) =
      torusChart R.params.side (s.coordinates η) s.coarse := by
  classical
  have hn := stepBlockFrame_extent R.params.side n
  haveI : NeZero (n * (stepBlockFrame R.params.side n).blockSide) := inferInstanceAs (NeZero (n * R.params.side))
  funext x i
  by_cases hf : (x, i) ∈ s.free
  · have hnt : ¬ IsAxialTreeBond (F := stepBlockFrame R.params.side n)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i) := by
      have := hs hf
      exact (Finset.mem_filter.mp this).2
    have hnt' : ¬ IsBlockTreeBond R.params.side x i :=
      fun h => hnt ((isAxialTreeBond_torusSiteInFrame_iff hn hL h2 x i).mpr h)
    have hv : s.coordinates η (x, i) = s.frame (x, i) + toImaginary (η ⟨(x, i), hf⟩) := by
      unfold ChartSetting.coordinates
      rw [dif_pos hf]
    unfold TorusFields.gaugeTransform ChartSetting.field torusChart
    rw [dif_pos hf, hv]
    unfold chartLink
    by_cases hc : IsCrossingBond (F := stepBlockFrame R.params.side n)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i)
    · have hc' : IsBlockEndBond R.params.side x i := (isCrossingBond_torusSiteInFrame_iff hn hL h2 x i).mp hc
      rw [if_pos hc, if_pos hc']
      group
    · have hc' : ¬ IsBlockEndBond R.params.side x i :=
        fun h => hc ((isCrossingBond_torusSiteInFrame_iff hn hL h2 x i).mpr h)
      rw [if_neg hc, if_neg hc', if_neg hnt']
      group
  · have hb := congrFun (congrFun (gaugeTransform_gaugeAt_eq_torusChart (R := R) hL h2 s.fine s.coarse) x) i
    have hv : s.coordinates η (x, i) = chartCoord R.params s.coarse s.fine (x, i) := by
      unfold ChartSetting.coordinates
      rw [dif_neg hf]
    have hfield : s.field η x i = s.fine x i := by
      unfold ChartSetting.field
      rw [dif_neg hf]
    rw [torusChart_congr s.coarse hv, ← hb]
    unfold TorusFields.gaugeTransform
    rw [hfield]
end StepSettings.ChartSetting
end YangMills.Construction
end
