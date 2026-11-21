import YangMills.Construction.ClusterExpansionOfAStep.UnitQuaternionsAsSpecialUnitaryMatrices
import YangMills.Construction.ResponseInTheExpansion.WeightsOfAnExpansion
import YangMills.Construction.RunningCouplingSlope.LeastPointsOverAFieldAreOneOrbitProof
import YangMills.Construction.RunningCouplingSlope.LengthsOfAChainAreThoseOfItsSteps
import YangMills.Construction.RunningCouplingSlope.LevelOfAChainReadsTheFieldOfItsStep
import YangMills.Construction.RunningCouplingSlope.PositiveBondsOfALevelAreThoseOfAFrame
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower BlockAverages ColdStepAtMirrorFrames
open TorusFields (TorusField TorusSite readAtLevel torusFrame)
namespace ChainLogRadii
private abbrev quatMat (q : ℍ[ℝ]) : Matrices.ComplexMatrix2 := SoftAverages.quaternionToMatrix q
private theorem sqrt_det_quatMat (q : ℍ[ℝ]) : (Matrix.det (quatMat q)) ^ (1 / 2 : ℂ) = ((‖q‖ : ℝ) : ℂ) := by apply _root_.YangMills.DeltaSharedProofs.p501669 <;> assumption
private theorem finset_sum_eq_finsum {α β : Type*} (s : Finset α) (f : α → ℝ) (g : β → ℝ) (e : ↥s → β)
    (he : Function.Bijective e) (hfg : ∀ a : ↥s, f a = g (e a)) :
    ∑ a ∈ s, f a = ∑ᶠ b, g b := by apply _root_.YangMills.SharedProofs.p64412 <;> assumption
private theorem torusSideBelow_eq (L : ℕ) : ∀ s N : ℕ, torusSideBelow L s N = N * L ^ s := by
  intro s
  induction s with
  | zero => intro N; simp [torusSideBelow]
  | succ s ih =>
    intro N
    show torusSideBelow L s (N * L) = _
    rw [ih, pow_succ]
    ring
abbrev _root_.YangMills.SharedProofs.p41915 := @torusSideBelow_eq
private theorem zmod_cast_cast {P m : ℕ} (h : P = m) (x : ZMod P) :
    ((((x.cast : ℤ) : ZMod m)).cast : ℤ) = x.cast := by apply _root_.YangMills.Construction.FrameTorusAction.cast_intCast_cast <;> assumption
private theorem siteOfCoords_coords {F : BlockFrame} {l : ℕ} (x : F.Site l) : siteOfCoords l (siteCoords x) = x := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords <;> assumption
variable {L n k : ℕ}
private theorem sideAtStep_eq (j : ℕ) :
    sideAtStep L n k j = 2 * L ^ (n + (k - (j + 1))) := by
  rw [sideAtStep, torusSideBelow_eq, pow_add]
  ring
private theorem sideAtStep_mul {j : ℕ} (hj : j < k) :
    sideAtStep L n k j * L = 2 * L ^ (n + (k - j)) := by
  have hexp : n + (k - j) = n + (k - (j + 1)) + 1 := by omega
  rw [sideAtStep_eq, hexp, pow_succ]
  ring
private theorem period_at_level (j : ℕ) (i : Fin 4) :
    (frameAtStep L n k j).period j i = sideAtStep L n k j * L := by
  simp [BlockFrame.period, frameAtStep, torusFrame, BlockFrame.top]
private theorem period_above_level (j : ℕ) (i : Fin 4) :
    (frameAtStep L n k j).period (j + 1) i = sideAtStep L n k j := by
  simp [BlockFrame.period, frameAtStep, torusFrame, BlockFrame.top]
private def minimizerOnTorus (a ρ : ℝ) (L n k j : ℕ) (V : TorusField (2 * L ^ n)) :
    TorusField (sideAtStep L n k j * L) :=
  fun z i => fieldAboveFrame (F := frameAtStep L n k j) true a ρ 0 (topFieldAtStep a ρ L n k j V) 0
    (siteOfCoords (F := frameAtStep L n k j) j fun c => ((z c).cast : ℤ)) i
private theorem siteCoords_of_cast (j : ℕ) (z : TorusSite (sideAtStep L n k j * L)) :
    siteCoords (siteOfCoords (F := frameAtStep L n k j) j fun c => ((z c).cast : ℤ)) =
      fun c => ((z c).cast : ℤ) := by
  funext c
  exact zmod_cast_cast (period_at_level j c).symm (z c)
private theorem represents_minimizer (hW : ChainLevelIsStepMinimizer) {a ρ : ℝ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {V : TorusField (2 * L ^ n)}
    {X : ChainPoint L n k} (hR : RepresentsMinimizerChain a ρ V X) {j : ℕ} (hj : j < k) :
    RepresentsAtLevel j (levelField X j) (minimizerOnTorus a ρ L n k j V) := by
  refine ⟨(hR j hj.le).1, fun z μ => ?_⟩
  have h := hW a ρ L hL k n hn V X hR j hj
    ((siteOfCoords (F := frameAtStep L n k j) j fun c => ((z c).cast : ℤ)), μ)
  have hedge : (edgeOfCoords (L := L) (n := n) (k := k) j
      (F := frameAtStep L n k j) (l := j)
      ((siteOfCoords (F := frameAtStep L n k j) j fun c => ((z c).cast : ℤ)), μ)) =
      PeriodicLattice.Bond.forwardFrom (levelVertexOfTorusSite j z) μ := by
    simp only [edgeOfCoords, levelVertexOfTorusSite]
    rw [siteCoords_of_cast]
  exact (congrArg (levelField X j) hedge).symm.trans h
private theorem readAtLevel_minimizer (a ρ : ℝ) (j : ℕ) (V : TorusField (2 * L ^ n)) :
    readAtLevel (frameAtStep L n k j) j (minimizerOnTorus a ρ L n k j V) =
      fieldAboveFrame (F := frameAtStep L n k j) true a ρ 0 (topFieldAtStep a ρ L n k j V) 0 := by
  funext x i
  show fieldAboveFrame (F := frameAtStep L n k j) true a ρ 0 (topFieldAtStep a ρ L n k j V) 0 _ i = _
  congr 1
  funext c
  have hc := zmod_cast_cast (period_at_level (L := L) (n := n) (k := k) j c) (x c)
  exact (congrArg (fun w : ℤ => (w : ZMod ((frameAtStep L n k j).period j c))) hc).trans
    (ZMod.intCast_zmod_cast (x c))
private theorem contourMean_eq (hP : ContourMeanMatchesFrame)
    (hW : ChainLevelIsStepMinimizer) {a ρ : ℝ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {V : TorusField (2 * L ^ n)}
    {X : ChainPoint L n k} (hR : RepresentsMinimizerChain a ρ V X) {j : ℕ} (hj : j < k)
    (b : (frameAtStep L n k j).Site (frameAtStep L n k j).top × Fin 4) :
    contourMean (levelField X j) (edgeOfCoords (j + 1) b) =
      quatMat (BlockAverages.contourAverage (fieldAboveFrame true a ρ 0 (topFieldAtStep a ρ L n k j V) 0) b) := by
  obtain ⟨x, μ⟩ := b
  have h := hP L hL n k j (sideAtStep L n k j) hn hj (sideAtStep_mul hj) (frameAtStep L n k j) rfl
    (period_at_level j) (period_above_level j) (minimizerOnTorus a ρ L n k j V) (levelField X j)
    (represents_minimizer hW hL hn hR hj) (siteCoords x) μ
  rw [readAtLevel_minimizer] at h
  have hx : siteOfCoords (F := frameAtStep L n k j) (j + 1) (siteCoords x) = x := siteOfCoords_coords x
  rw [hx] at h
  exact h
private theorem mem_innerBonds (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    (b : (frameAtStep L n k j).Site (frameAtStep L n k j).top × Fin 4) :
    b ∈ innerBonds (finiteCells (frameAtStep L n k j)) (frameAtStep L n k j).top := by
  have hL0 : 0 < L := hL.1.pos
  have hodd : Odd (frameAtStep L n k j).blockSide := hL.1
  have hext : ∀ i, 0 < (frameAtStep L n k j).extent i := fun i => by
    show 0 < sideAtStep L n k j
    rw [sideAtStep_eq]
    positivity
  have hs := fun x : (frameAtStep L n k j).Site (frameAtStep L n k j).top =>
    mem_allSites hodd hext le_rfl x
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨hs _, hs _⟩
private theorem logRadii_at_step (hP : ContourMeanMatchesFrame)
    (hW : ChainLevelIsStepMinimizer)
    (hB : FramePositiveEdgesBijective) {a ρ : ℝ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {V : TorusField (2 * L ^ n)}
    {X : ChainPoint L n k} (hR : RepresentsMinimizerChain a ρ V X) {j : ℕ} (hj : j < k) :
    ∑ᶠ c : PositiveEdge L n k (j + 1), Real.log (meanRadius (levelField X j) c.1).re =
      ∑ c ∈ innerBonds (finiteCells (frameAtStep L n k j)) (frameAtStep L n k j).top,
        Real.log ‖BlockAverages.contourAverage (fieldAboveFrame true a ρ 0 (topFieldAtStep a ρ L n k j V) 0) c‖ := by
  have hper : ∀ i, (frameAtStep L n k j).period (frameAtStep L n k j).top i =
      2 * L ^ (n + (k - (j + 1))) := fun i => (period_above_level j i).trans (sideAtStep_eq j)
  obtain ⟨hpos, hinj, hsurj⟩ := hB L hL n k (j + 1) hn hj (frameAtStep L n k j) _ hper
  symm
  refine finset_sum_eq_finsum _ _ _ (fun p => ⟨edgeOfCoords (j + 1) p.1, hpos p.1⟩) ⟨?_, ?_⟩ ?_
  · rintro ⟨b, hb⟩ ⟨b', hb'⟩ h
    exact Subtype.ext (hinj (congrArg Subtype.val h))
  · rintro ⟨c, hc⟩
    obtain ⟨b, rfl⟩ := hsurj c hc
    exact ⟨⟨b, mem_innerBonds hL hn hj b⟩, rfl⟩
  · rintro ⟨b, hb⟩
    show _ = Real.log (meanRadius (levelField X j) (edgeOfCoords (j + 1) b)).re
    rw [meanRadius, contourMean_eq hP hW hL hn hR hj b, sqrt_det_quatMat]
    simp
end ChainLogRadii
open ChainLogRadii in
theorem chainLogRadiiAreStepLogRadii (hP : ContourMeanMatchesFrame)
    (hW : ChainLevelIsStepMinimizer)
    (hB : FramePositiveEdgesBijective) :
    ChainLogRadiiAreStepLogRadii := by
  intro a ρ L hL k n hn V X hR
  unfold logRadiusSum
  exact Finset.sum_congr rfl fun j _ => logRadii_at_step hP hW hB hL hn hR j.2
end YangMills.Construction.RunningCouplingSlope
end
