import YangMills.Construction.ClusterExpansionOfAStep.EvaluationsOfAStateAreBorel
import YangMills.Construction.ClusterExpansionOfAStep.FrameIsContinuousWhereItIsReadProof
import YangMills.Construction.ClusterExpansionOfAStep.PriceOfTheHotLumps
import YangMills.Construction.ClusterExpansionOfAStep.ShareOfTheFieldAboveIsBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours TopLevelSites TorusFields TorusLumps StepCosts HoledShares
  StateMeasurability
namespace ShareMeasurability
variable {F : BlockFrame}
theorem continuousAt_of_isBondAnalyticAt [Finite F.Cell] {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {G : F.GaugeField F.top → E} {V : F.GaugeField F.top}
    (hG : IsBondAnalyticAt G V) : ContinuousAt G V := by apply _root_.YangMills.Construction.StepFrames.continuousAt_of_isBondAnalyticAt <;> assumption
theorem continuous_readAtLevel' {m : ℕ} (j : ℕ) : Continuous (readAtLevel (n := m) F j) := by apply _root_.YangMills.Construction.StepCosts.continuous_readAtLevel <;> assumption
end ShareMeasurability
open ShareMeasurability in
theorem ShareMeasurability.levelShareOffHotMeasurable
    (hc : ComplementOfThickenedLumpsRegular) : LevelShareOffHotMeasurable := by
  intro ℓ δ lam ρA σA cg N hadm hch hσ t n _ hB Y
  classical
  obtain ⟨_, _, _, _, _, _, _, _, hbody⟩ := hch
  have hLn : ℓ.side ∣ n := hB.1
  have hLpos : 0 < ℓ.side := hadm.L_odd.pos
  have hσpos := hadm.σ_pos
  have hn64 : 64 ≤ n := by
    have h1 : ℓ.side * ℓ.n₀ ≤ n := hB.2
    have h2 : 4096 ≤ ℓ.n₀ := hadm.n₀_ge
    have h3 : ℓ.n₀ ≤ ℓ.side * ℓ.n₀ := Nat.le_mul_of_pos_left _ hLpos
    omega
  have hn : ∀ i, (torusFrame ℓ.side t n).extent i = n := fun _ => rfl
  have hamb : IsAdmissibleAmbient (torusFrame ℓ.side t n) := Or.inr fun i => by rw [hn]; omega
  have hpos : ∀ i, 0 < (torusFrame ℓ.side t n).extent i := fun i => by rw [hn]; omega
  have : Finite (torusFrame ℓ.side t n).Cell := finite_cell hpos
  refine measurable_of_countable_cover (ι := Finset (Finset (TorusSite n)))
    (fun H => {V | torusHotLumps ℓ V = H})
    (fun H => measurableSet_torusHotLumps_eq hadm hLn H) (fun V => ⟨torusHotLumps ℓ V, rfl⟩)
    fun H => ?_
  rcases isEmpty_or_nonempty {V : TorusField n | torusHotLumps ℓ V = H} with he | ⟨⟨V₀, h₀⟩⟩
  · exact measurable_of_empty _
  let S : Finset (torusFrame ℓ.side t n).Cell :=
    cellsOfSites (torusFrame ℓ.side t n) (coldRegion ℓ V₀)
  let G : (torusFrame ℓ.side t n).GaugeField (torusFrame ℓ.side t n).top → ℝ :=
    minimalCellShare ℓ.coupling S (torusSiteInFrame (torusFrame ℓ.side t n) (t + 1) Y)
  have hcold' : ∀ x : {V : TorusField n | torusHotLumps ℓ V = H},
      coldRegion ℓ x.1 = coldRegion ℓ V₀ := by
    intro x
    have e : torusHotLumps ℓ x.1 = torusHotLumps ℓ V₀ := x.2.trans h₀.symm
    simp only [coldRegion, torusHotSites, e]
  have hval : (fun x : {V : TorusField n | torusHotLumps ℓ V = H} =>
        levelShare ℓ.coupling ℓ.side (t + 1) (coldRegion ℓ x.1) Y x.1) =
      fun x => G (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top x.1) := by
    funext x
    rw [hcold' x]
    rfl
  show Measurable fun x : {V : TorusField n | torusHotLumps ℓ V = H} =>
    levelShare ℓ.coupling ℓ.side (t + 1) (coldRegion ℓ x.1) Y x.1
  rw [hval]
  refine Continuous.measurable (continuous_iff_continuousAt.mpr fun x => ?_)
  have hS : S = cellsOfSites (torusFrame ℓ.side t n)
      (Finset.univ \ thickening lumpRange (torusHotSites ℓ x.1)) := by
    show cellsOfSites (torusFrame ℓ.side t n) (coldRegion ℓ V₀) = _
    rw [← hcold' x]
    rfl
  have hreg : IsOrthantRegular S 2047 := by
    rw [hS]
    exact isOrthantRegular_cellsOfSites_compl_thickening hc hadm hLn hn x.1
  have hcold : IsCold S (torusFrame ℓ.side t n).top ℓ.threshold
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top x.1) := by
    rw [hS]
    exact isCold_cellsOfSites_compl_thickening hadm hLn hn x.1
  obtain ⟨_, _, hsh, _⟩ :=
    hbody (torusFrame ℓ.side t n) 2047 S rfl hamb (by norm_num) hreg ℓ.threshold _ hσpos hσ hcold
  have hG : ContinuousAt G
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top x.1) :=
    continuousAt_of_isBondAnalyticAt (hsh.2.1 _)
  have hr : Continuous fun x : {V : TorusField n | torusHotLumps ℓ V = H} =>
      readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top x.1 :=
    (continuous_readAtLevel' _).comp continuous_subtype_val
  exact ContinuousAt.comp (f := fun x : {V : TorusField n | torusHotLumps ℓ V = H} =>
    readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top x.1) hG hr.continuousAt
end YangMills.Construction
end
