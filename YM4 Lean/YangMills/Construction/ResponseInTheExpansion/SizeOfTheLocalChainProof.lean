import YangMills.Construction.ClusterExpansionOfAStep.CountsOnATorus
import YangMills.Construction.ResponseInTheExpansion.AxialGaugeOnABox
import YangMills.Construction.ResponseInTheExpansion.CurvatureOfAStepFallsByHalf
import YangMills.Construction.ResponseInTheExpansion.FloorsOfTheLocalChain
import YangMills.Construction.ResponseInTheExpansion.MomentsOfAStepOfTheCurvatureProof
import YangMills.Construction.ResponseInTheExpansion.MomentsOfTheFluctuationsOfAStep
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAScoredTowerOnColdMirrorsProof
import YangMills.Construction.ResponseInTheExpansion.SizeOfTheLocalChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.StepCosts
open YangMills.Construction.StepMarks YangMills.Construction.MarkedIntegrals YangMills.Construction.BlockTrees
open YangMills.Construction.WeightedResponses YangMills.Construction.RenormalizationStepParameters
namespace LocalChainSize
section Bonds
variable {L n : ℕ}
private theorem frameOne_unitStep [NeZero n] (i : Fin 4) :
    torusSiteInFrame (stepBlockFrame L n) 1 (TorusFields.unitStep n i) =
      BlockAverages.unitStep (F := stepBlockFrame L n) 1 i := by
  funext k
  have e : (TorusFields.unitStep n i) k = (((Pi.single i 1 : Fin 4 → ℤ) k : ℤ) : ZMod n) := by
    by_cases hk : k = i
    · subst hk
      simp [TorusFields.unitStep]
    · simp [TorusFields.unitStep, Pi.single_eq_of_ne hk]
  show ((ZMod.cast (TorusFields.unitStep n i k) : ℤ) : ZMod ((stepBlockFrame L n).period 1 k)) = _
  rw [e]
  exact intCast_cast_intCast (_root_.YangMills.Construction.BlockTrees.stepBlockFrame_period_one k) _
abbrev _root_.YangMills.SharedProofs.p8913 := @frameOne_unitStep
private theorem frameOne_add [NeZero n] (x y : TorusSite n) :
    torusSiteInFrame (stepBlockFrame L n) 1 (x + y) =
      torusSiteInFrame (stepBlockFrame L n) 1 x + torusSiteInFrame (stepBlockFrame L n) 1 y := by
  funext i
  exact intCast_cast_add (_root_.YangMills.Construction.BlockTrees.stepBlockFrame_period_one i) (x i) (y i)
variable [NeZero L] [NeZero n]
private theorem parentBlock_add_of_crossing (hL : Odd L) (hn : 2 ≤ n) (x : TorusSite (n * L)) (i : Fin 4)
    (hc : IsCrossingBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 x, i)) :
    parentBlock L (x + TorusFields.unitStep (n * L) i) = parentBlock L x + TorusFields.unitStep n i := by
  apply torusSiteInFrame_injective (stepBlockFrame L n) 1 _root_.YangMills.Construction.BlockTrees.stepBlockFrame_period_one
  rw [frameOne_add, frameOne_unitStep, ← enclosingCell_torusSiteInFrame, ← enclosingCell_torusSiteInFrame,
    torusSiteInFrame_add, torusSiteInFrame_unitStep]
  exact TopLevelSites.enclosingCell_add_unitStep (F := stepBlockFrame L n) hL (fun _ => hn) _ i hc
private theorem parentBlock_add_of_not_crossing (x : TorusSite (n * L)) (i : Fin 4)
    (hc : ¬ IsCrossingBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 x, i)) :
    parentBlock L (x + TorusFields.unitStep (n * L) i) = parentBlock L x := by
  have h1 : enclosingCell (torusSiteInFrame (stepBlockFrame L n) 0 x + BlockAverages.unitStep (F := stepBlockFrame L n) 0 i) =
      enclosingCell (torusSiteInFrame (stepBlockFrame L n) 0 x) := not_not.mp hc
  rw [← torusSiteInFrame_unitStep, ← torusSiteInFrame_add] at h1
  exact torusSiteInFrame_injective (stepBlockFrame L n) 1 _root_.YangMills.Construction.BlockTrees.stepBlockFrame_period_one
    ((enclosingCell_torusSiteInFrame _).symm.trans (h1.trans (enclosingCell_torusSiteInFrame x)))
end Bonds
private theorem norm_expUnit_sub_one (w : imaginaryQuaternions) :
    ‖((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(w : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.SmallCellTerms.norm_coe_expUnit_sub_one_le <;> assumption
private theorem defect_down (ℓ : TorusLumps.StepParameters) (hL : Odd ℓ.side) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (g : TorusSite n → UnitQuaternion) (V : TorusField n)
    (W : TorusField (n * ℓ.side)) (b : TorusBond (n * ℓ.side)) {a e : ℝ} (ha0 : 0 ≤ a) (he0 : 0 ≤ e)
    (ha : ‖((ResponseInTheExpansion.gaugeTransform g V (parentBlock ℓ.side b.1, b.2) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ a)
    (he : b ∈ chartBonds ℓ.side n → ‖((chartCoord ℓ V W b : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ e) :
    ‖((ResponseInTheExpansion.gaugeTransform (fun x => g (parentBlock ℓ.side x) * blockTreeGauge ℓ W x) W b : UnitQuaternion) : ℍ[ℝ]) - 1‖
      ≤ a + e := by
  classical
  obtain ⟨x, i⟩ := b
  have hform : ResponseInTheExpansion.gaugeTransform (fun x => g (parentBlock ℓ.side x) * blockTreeGauge ℓ W x) W (x, i) =
      g (parentBlock ℓ.side x) * (blockGauge ℓ.side W x * W x i *
        (blockGauge ℓ.side W (x + TorusFields.unitStep (n * ℓ.side) i))⁻¹) *
        (g (parentBlock ℓ.side (x + TorusFields.unitStep (n * ℓ.side) i)))⁻¹ := by
    show g (parentBlock ℓ.side x) * blockGauge ℓ.side W x * W x i *
      (g (parentBlock ℓ.side (x + TorusFields.unitStep (n * ℓ.side) i)) *
        blockGauge ℓ.side W (x + TorusFields.unitStep (n * ℓ.side) i))⁻¹ = _
    group
  rw [hform]
  by_cases ht : IsAxialTreeBond (F := stepBlockFrame ℓ.side n) (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 x, i)
  · have hs := blockGauge_add_unitStep hL hn W x i ht
    have hb := parentBlock_add_of_not_crossing x i ht.1
    rw [hs, hb]
    have : g (parentBlock ℓ.side x) * (blockGauge ℓ.side W x * W x i * (blockGauge ℓ.side W x * W x i)⁻¹) *
        (g (parentBlock ℓ.side x))⁻¹ = 1 := by
      group
    rw [this]
    simpa using add_nonneg ha0 he0
  · have hmem : (x, i) ∈ chartBonds ℓ.side n := by
      simp only [chartBonds, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ht
    have hco := he hmem
    set co := chartCoord ℓ V W (x, i) with hcodef
    have hf := chartCoord_eq ℓ V W (x, i)
    by_cases hc : IsCrossingBond (F := stepBlockFrame ℓ.side n) (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 x, i)
    · rw [if_pos hc] at hf
      have hexp : expUnit co = blockGauge ℓ.side W x * W x i *
          (blockGauge ℓ.side W (x + TorusFields.unitStep (n * ℓ.side) i))⁻¹ * (V (parentBlock ℓ.side x) i)⁻¹ := by
        rw [hcodef, hf]
        exact TopLevelSites.expUnit_minimalLog _
      have hQ : blockGauge ℓ.side W x * W x i * (blockGauge ℓ.side W (x + TorusFields.unitStep (n * ℓ.side) i))⁻¹ =
          expUnit co * V (parentBlock ℓ.side x) i := by
        rw [hexp]
        group
      rw [hQ, parentBlock_add_of_crossing hL hn x i hc]
      have hsplit : g (parentBlock ℓ.side x) * (expUnit co * V (parentBlock ℓ.side x) i) *
          (g (parentBlock ℓ.side x + TorusFields.unitStep n i))⁻¹ =
          (g (parentBlock ℓ.side x) * expUnit co * (g (parentBlock ℓ.side x))⁻¹) *
            ResponseInTheExpansion.gaugeTransform g V (parentBlock ℓ.side x, i) := by
        show _ = _ * (g (parentBlock ℓ.side x) * V (parentBlock ℓ.side x) i *
          (g (parentBlock ℓ.side x + TorusFields.unitStep n i))⁻¹)
        group
      rw [hsplit]
      refine (GaugeFixing.norm_mul_sub_one_le _ _).trans ?_
      rw [GaugeFixing.norm_conj_sub_one]
      have := norm_expUnit_sub_one co
      linarith
    · rw [if_neg hc] at hf
      have hexp : expUnit co = blockGauge ℓ.side W x * W x i *
          (blockGauge ℓ.side W (x + TorusFields.unitStep (n * ℓ.side) i))⁻¹ := by
        rw [hcodef, hf]
        exact TopLevelSites.expUnit_minimalLog _
      rw [← hexp, parentBlock_add_of_not_crossing x i hc, GaugeFixing.norm_conj_sub_one]
      have := norm_expUnit_sub_one co
      linarith
section Sizes
variable {ℓ : TorusLumps.StepParameters}
private theorem le_finsetSup {α : Type} {S : Finset α} {f : α → ℝ} {b : α} (hb : b ∈ S) : f b ≤ finsetSupNonneg S f :=
  (Finset.le_fold_max _).2 (Or.inr ⟨b, hb, le_refl _⟩)
private theorem finsetSup_nonneg {α : Type} (S : Finset α) (f : α → ℝ) : 0 ≤ finsetSupNonneg S f :=
  (Finset.le_fold_max _).2 (Or.inl le_rfl)
private theorem finsetSup_le {α : Type} {S : Finset α} {f : α → ℝ} {c : ℝ} (h0 : 0 ≤ c) (h : ∀ b ∈ S, f b ≤ c) :
    finsetSupNonneg S f ≤ c :=
  (Finset.fold_max_le _).2 ⟨h0, h⟩
private theorem finsetSup_mono {α : Type} {S S' : Finset α} (h : S ⊆ S') (f : α → ℝ) :
    finsetSupNonneg S f ≤ finsetSupNonneg S' f :=
  finsetSup_le (finsetSup_nonneg _ _) fun _ hb => le_finsetSup (h hb)
private theorem mem_supBall_iff {n : ℕ} [NeZero n] {o z : TorusSite n} {r : ℝ} :
    z ∈ supBall o r ↔ (_root_.YangMills.Construction.TorusFields.supDist z o : ℝ) ≤ r := by
  simp [supBall]
private theorem supBall_mono {n : ℕ} [NeZero n] (o : TorusSite n) {r r' : ℝ} (h : r ≤ r') : supBall o r ⊆ supBall o r' :=
  fun _ hz => mem_supBall_iff.2 ((mem_supBall_iff.1 hz).trans h)
private theorem plaquettesIn_mono {n : ℕ} [NeZero n] {S S' : Finset (TorusSite n)} (h : S ⊆ S') :
    plaquettesIn S ⊆ plaquettesIn S' := by
  intro p hp
  simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact ⟨hp.1, fun z hz => h (hp.2 z hz)⟩
private theorem maxCurv_mono {n : ℕ} [NeZero n] (W : TorusField n) (o : TorusSite n) {r r' : ℝ} (h : r ≤ r') :
    maxCurvatureOnBall W o r ≤ maxCurvatureOnBall W o r' :=
  finsetSup_mono (plaquettesIn_mono (supBall_mono o h)) _
private theorem maxCurv_nonneg {n : ℕ} [NeZero n] (W : TorusField n) (o : TorusSite n) (r : ℝ) :
    0 ≤ maxCurvatureOnBall W o r :=
  finsetSup_nonneg _ _
private theorem maxDev_nonneg (T : StageTower ℓ) (t : ℕ) {n : ℕ} [NeZero n] (V : TorusField n)
    (W : TorusField (n * ℓ.side)) (o : TorusSite n) (r : ℝ) : 0 ≤ maxDeviationOnBall T t V W o r :=
  finsetSup_nonneg _ _
private theorem curvature_le_maxCurv {n : ℕ} [NeZero n] (W : TorusField n) (o : TorusSite n) (r : ℝ)
    {p : TorusPlaquette n} (hp : p ∈ plaquettesIn (supBall o r)) :
    curvature W p.1 p.2.1 p.2.2 ≤ maxCurvatureOnBall W o r := by
  unfold maxCurvatureOnBall
  exact le_finsetSup (f := fun p : TorusPlaquette n => curvature W p.1 p.2.1 p.2.2) hp
private theorem unitStep_eq_ofInt {n : ℕ} (i : Fin 4) : TorusFields.unitStep n i = siteOfInt (Pi.single i 1) := by apply _root_.YangMills.Construction.BlockOffsets.unitStep_eq_siteOfInt <;> assumption
private theorem curvature_diag {n : ℕ} (W : TorusField n) (z : TorusSite n) (μ : Fin 4) : curvature W z μ μ = 0 := by
  simp [curvature, holonomy]
private theorem curvature_swap {n : ℕ} (W : TorusField n) (z : TorusSite n) (μ ν : Fin 4) :
    curvature W z ν μ = curvature W z μ ν := by
  have e : holonomy W z ν μ = (holonomy W z μ ν)⁻¹ := by
    simp only [holonomy]
    group
  simp only [curvature]
  rw [e, GaugeFixing.norm_inv_sub_one]
abbrev _root_.YangMills.SharedProofs.p108355 := @curvature_swap
private theorem curvature_le_maxCurv_wide {n : ℕ} [NeZero n] (W : TorusField n) (o z : TorusSite n) {r : ℝ}
    (hz : z ∈ supBall o r) (μ ν : Fin 4) :
    curvature W z μ ν ≤ maxCurvatureOnBall W o (r + 1) := by
  have key : ∀ μ ν : Fin 4, μ < ν → curvature W z μ ν ≤ maxCurvatureOnBall W o (r + 1) := by
    intro μ ν hμν
    have hmem : (z, μ, ν) ∈ plaquettesIn (supBall o (r + 1)) := by
      simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hμν, fun c hc => ?_⟩
      have hz' := mem_supBall_iff.1 hz
      have hne : μ ≠ ν := hμν.ne
      have hd : _root_.YangMills.Construction.TorusFields.supDist c z ≤ 1 := by
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
        simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl
        · simp [_root_.YangMills.Construction.TorusFields.supDist_self]
        · rw [unitStep_eq_ofInt]
          refine supDist_add_siteOfInt_le _ _ _ fun i => ?_
          by_cases hi : i = μ
          · subst hi; simp
          · simp [Pi.single_eq_of_ne hi]
        · rw [unitStep_eq_ofInt]
          refine supDist_add_siteOfInt_le _ _ _ fun i => ?_
          by_cases hi : i = ν
          · subst hi; simp
          · simp [Pi.single_eq_of_ne hi]
        · rw [unitStep_eq_ofInt, unitStep_eq_ofInt, add_assoc, ← siteOfInt_add]
          refine supDist_add_siteOfInt_le _ _ _ fun i => ?_
          by_cases hi : i = μ
          · subst hi
            simp [Pi.single_eq_of_ne hne]
          · by_cases hj : i = ν
            · subst hj
              simp [Pi.single_eq_of_ne hi]
            · simp [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hj]
      have ht := _root_.YangMills.Construction.TorusFields.supDist_triangle c z o
      have : (_root_.YangMills.Construction.TorusFields.supDist c o : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist c z : ℝ) + _root_.YangMills.Construction.TorusFields.supDist z o := by exact_mod_cast ht
      have hd' : (_root_.YangMills.Construction.TorusFields.supDist c z : ℝ) ≤ 1 := by exact_mod_cast hd
      exact mem_supBall_iff.2 (by linarith)
    exact curvature_le_maxCurv W o (r + 1) (p := (z, μ, ν)) hmem
  rcases lt_trichotomy μ ν with h | h | h
  · exact key μ ν h
  · subst h
    rw [curvature_diag]
    exact maxCurv_nonneg _ _ _
  · rw [← curvature_swap]
    exact key ν μ h
private def GoodAlong (T : StageTower ℓ) (s : ℕ) (m : ℝ) :
    (D n : ℕ) → [NeZero n] → MarkedSample ℓ (s + D) n → TorusSite (fineSide ℓ.side D n) → Prop
  | 0, _, _, _, _ => True
  | D + 1, n, _, u, o =>
    IsColdOnBall ℓ.threshold u.2.2.1 (siteAbove ℓ.side (D + 1) n o) m ∧
      (∀ b ∈ chartBondsInBlocks ℓ.side (supBall (siteAbove ℓ.side (D + 1) n o) m),
        ‖(stepDeviation T (s + D) u.2.2.1 (topField ℓ (s + D) (n * ℓ.side) u.1) b : ℍ[ℝ])‖ < ℓ.threshold / 64) ∧
      GoodAlong T s m D (n * ℓ.side) u.1 o
private def devSum (T : StageTower ℓ) (s : ℕ) (nn ρ₀ : ℝ) (w : ℕ → ℝ) :
    (D n : ℕ) → [NeZero n] → MarkedSample ℓ (s + D) n → TorusSite (fineSide ℓ.side D n) → ℝ
  | 0, _, _, _, _ => 0
  | D + 1, n, _, u, o =>
    devSum T s nn ρ₀ w D (n * ℓ.side) u.1 o +
      w D * maxDeviationOnBall T (s + D) u.2.2.1 (topField ℓ (s + D) (n * ℓ.side) u.1) (siteAbove ℓ.side (D + 1) n o)
        ((ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2)
private theorem devSum_nonneg (T : StageTower ℓ) (s : ℕ) (nn ρ₀ : ℝ) {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) :
    ∀ (D n : ℕ) [NeZero n] (u : MarkedSample ℓ (s + D) n) (o : TorusSite (fineSide ℓ.side D n)),
      0 ≤ devSum T s nn ρ₀ w D n u o := by
  intro D
  induction D with
  | zero => intro n _ u o; exact le_rfl
  | succ D ih =>
    intro n _ u o
    exact add_nonneg (ih (n * ℓ.side) u.1 o) (mul_nonneg (hw D) (maxDev_nonneg _ _ _ _ _ _))
private theorem stageSum_nonneg (T : StageTower ℓ) (s : ℕ) (nn ρ₀ : ℝ) :
    ∀ (D n : ℕ) [NeZero n] (u : MarkedSample ℓ (s + D) n) (o : TorusSite (fineSide ℓ.side D n)),
      0 ≤ widenedStageSum T s nn ρ₀ D n u o := by
  intro D
  induction D with
  | zero => intro n _ u o; exact le_rfl
  | succ D ih =>
    intro n _ u o
    exact add_nonneg (add_nonneg (maxCurv_nonneg _ _ _) (maxDev_nonneg _ _ _ _ _ _)) (ih (n * ℓ.side) u.1 o)
abbrev _root_.YangMills.SharedProofs.p61945 := @stageSum_nonneg
private structure StepsHalve (T : StageTower ℓ) (s : ℕ) (nn ρ₀ m e N₀ side : ℝ) (A : ℕ) : Prop where
  frame : ∀ D, D < A → ∀ (n : ℕ) [NeZero n], side ≤ n → ∀ (o : TorusSite n) (V : TorusField n),
    IsColdOnBall ℓ.threshold V o m →
    ∀ b ∈ chartBonds ℓ.side n, supBall (parentBlock ℓ.side b.1) ρ₀ ⊆ supBall o (ballRadius ℓ.side nn ρ₀ (D + 1)) →
      ‖(frameCoord ℓ (T.stage (s + D)).anchorRadius (s + D) (T.stage (s + D)).toStepSetup.frameReach V b : ℍ[ℝ])‖ ≤
        N₀ * maxCurvatureOnBall V o (ballRadius ℓ.side nn ρ₀ (D + 1)) + e
  falls : ∀ D, D < A → ∀ (n : ℕ) [NeZero n], side ≤ n → ∀ (o : TorusSite n) (V : TorusField n),
    IsColdOnBall ℓ.threshold V o m →
    ∀ (W : TorusField (n * ℓ.side)) (o' : TorusSite (n * ℓ.side)), parentBlock ℓ.side o' = o →
      (∀ b ∈ chartBondsInBlocks ℓ.side (supBall o m), ‖(stepDeviation T (s + D) V W b : ℍ[ℝ])‖ < ℓ.threshold / 64) →
      maxCurvatureOnBall W o' (ballRadius ℓ.side nn ρ₀ D + 1) ≤
        (1 / 2) * maxCurvatureOnBall V o (ballRadius ℓ.side nn ρ₀ (D + 1) + 1) +
          4 * maxDeviationOnBall T (s + D) V W o ((ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2) + e
private theorem side_le_mul {side : ℝ} {n : ℕ} (h0 : 0 ≤ side) (h : side ≤ n) : side ≤ ((n * ℓ.side : ℕ) : ℝ) := by apply _root_.YangMills.SharedProofs.p36346 <;> assumption
variable {T : StageTower ℓ} {s : ℕ} {nn ρ₀ m e N₀ side : ℝ} {A : ℕ}
private theorem curvature_descends (H : StepsHalve T s nn ρ₀ m e N₀ side A) (hs : 0 ≤ side) :
    ∀ D, D ≤ A → ∀ (n : ℕ) [NeZero n], side ≤ n → ∀ (u : MarkedSample ℓ (s + D) n) (o : TorusSite (fineSide ℓ.side D n)),
      GoodAlong T s m D n u o →
      maxCurvatureOnBall (topField ℓ s _ (sampleBelow ℓ s D n u)) o (ballRadius ℓ.side nn ρ₀ 0 + 1) ≤
        (1 / 2) ^ D * maxCurvatureOnBall (topField ℓ (s + D) n u) (siteAbove ℓ.side D n o) (ballRadius ℓ.side nn ρ₀ D + 1) +
          devSum T s nn ρ₀ (fun i => (1 / 2) ^ i * 4) D n u o + (2 - 2 * (1 / 2) ^ D) * e := by
  intro D
  induction D with
  | zero =>
    intro _ n _ _ u o _
    show maxCurvatureOnBall (topField ℓ s n u) o (ballRadius ℓ.side nn ρ₀ 0 + 1) ≤
      (1 / 2) ^ 0 * maxCurvatureOnBall (topField ℓ s n u) o (ballRadius ℓ.side nn ρ₀ 0 + 1) + 0 + (2 - 2 * (1 / 2) ^ 0) * e
    simp
  | succ D ih =>
    intro hD n _ hn u o hg
    obtain ⟨hc, hη, hg'⟩ := hg
    have h1 := ih (by omega) (n * ℓ.side) (side_le_mul hs hn) u.1 o hg'
    have h2 := H.falls D (by omega) n hn (siteAbove ℓ.side (D + 1) n o) u.2.2.1 hc
      (topField ℓ (s + D) (n * ℓ.side) u.1) (siteAbove ℓ.side D (n * ℓ.side) o) rfl hη
    have hp : (0 : ℝ) ≤ (1 / 2) ^ D := by positivity
    have h3 := mul_le_mul_of_nonneg_left h2 hp
    refine h1.trans ?_
    show _ ≤ (1 / 2) ^ (D + 1) * maxCurvatureOnBall u.2.2.1 (siteAbove ℓ.side (D + 1) n o)
        (ballRadius ℓ.side nn ρ₀ (D + 1) + 1) +
      (devSum T s nn ρ₀ (fun i => (1 / 2) ^ i * 4) D (n * ℓ.side) u.1 o +
        ((1 / 2) ^ D * 4) * maxDeviationOnBall T (s + D) u.2.2.1 (topField ℓ (s + D) (n * ℓ.side) u.1)
          (siteAbove ℓ.side (D + 1) n o) ((ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2)) +
      (2 - 2 * (1 / 2) ^ (D + 1)) * e
    rw [pow_succ]
    linarith
private theorem stageSum_descends (H : StepsHalve T s nn ρ₀ m e N₀ side A) (hs : 0 ≤ side) :
    ∀ D, D ≤ A → ∀ (n : ℕ) [NeZero n], side ≤ n → ∀ (u : MarkedSample ℓ (s + D) n) (o : TorusSite (fineSide ℓ.side D n)),
      GoodAlong T s m D n u o →
      widenedStageSum T s nn ρ₀ D n u o ≤
        2 * maxCurvatureOnBall (topField ℓ (s + D) n u) (siteAbove ℓ.side D n o) (ballRadius ℓ.side nn ρ₀ D + 1) +
          9 * devSum T s nn ρ₀ (fun _ => 1) D n u o + 2 * D * e := by
  intro D
  induction D with
  | zero =>
    intro _ n _ _ u o _
    have h0 := maxCurv_nonneg (topField ℓ s n u) o (ballRadius ℓ.side nn ρ₀ 0 + 1)
    show (0 : ℝ) ≤ 2 * maxCurvatureOnBall (topField ℓ s n u) o (ballRadius ℓ.side nn ρ₀ 0 + 1) + 9 * 0 +
      2 * ((0 : ℕ) : ℝ) * e
    have : (2 : ℝ) * ((0 : ℕ) : ℝ) * e = 0 := by simp
    linarith
  | succ D ih =>
    intro hD n _ hn u o hg
    obtain ⟨hc, hη, hg'⟩ := hg
    have h1 := ih (by omega) (n * ℓ.side) (side_le_mul hs hn) u.1 o hg'
    have h2 := H.falls D (by omega) n hn (siteAbove ℓ.side (D + 1) n o) u.2.2.1 hc
      (topField ℓ (s + D) (n * ℓ.side) u.1) (siteAbove ℓ.side D (n * ℓ.side) o) rfl hη
    show maxCurvatureOnBall u.2.2.1 (siteAbove ℓ.side (D + 1) n o) (ballRadius ℓ.side nn ρ₀ (D + 1) + 1) +
        maxDeviationOnBall T (s + D) u.2.2.1 (topField ℓ (s + D) (n * ℓ.side) u.1) (siteAbove ℓ.side (D + 1) n o)
          ((ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2) + widenedStageSum T s nn ρ₀ D (n * ℓ.side) u.1 o ≤
      2 * maxCurvatureOnBall u.2.2.1 (siteAbove ℓ.side (D + 1) n o) (ballRadius ℓ.side nn ρ₀ (D + 1) + 1) +
        9 * (devSum T s nn ρ₀ (fun _ => 1) D (n * ℓ.side) u.1 o +
          1 * maxDeviationOnBall T (s + D) u.2.2.1 (topField ℓ (s + D) (n * ℓ.side) u.1) (siteAbove ℓ.side (D + 1) n o)
            ((ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2)) + 2 * ((D + 1 : ℕ) : ℝ) * e
    push_cast
    linarith
private theorem stageMax_descends (H : StepsHalve T s nn ρ₀ m e N₀ side A) (hs : 0 ≤ side) (he : 0 ≤ e) :
    ∀ D, D ≤ A → ∀ (n : ℕ) [NeZero n], side ≤ n → ∀ (u : MarkedSample ℓ (s + D) n) (o : TorusSite (fineSide ℓ.side D n)),
      GoodAlong T s m D n u o →
      widenedStageMax s nn ρ₀ D n u o ≤
        maxCurvatureOnBall (topField ℓ (s + D) n u) (siteAbove ℓ.side D n o) (ballRadius ℓ.side nn ρ₀ D + 1) +
          4 * devSum T s nn ρ₀ (fun _ => 1) D n u o + D * e := by
  intro D
  induction D with
  | zero =>
    intro _ n _ _ u o _
    show maxCurvatureOnBall (topField ℓ s n u) o (ballRadius ℓ.side nn ρ₀ 0 + 1) ≤
      maxCurvatureOnBall (topField ℓ s n u) o (ballRadius ℓ.side nn ρ₀ 0 + 1) + 4 * 0 + ((0 : ℕ) : ℝ) * e
    simp
  | succ D ih =>
    intro hD n _ hn u o hg
    obtain ⟨hc, hη, hg'⟩ := hg
    have h1 := ih (by omega) (n * ℓ.side) (side_le_mul hs hn) u.1 o hg'
    have h2 := H.falls D (by omega) n hn (siteAbove ℓ.side (D + 1) n o) u.2.2.1 hc
      (topField ℓ (s + D) (n * ℓ.side) u.1) (siteAbove ℓ.side D (n * ℓ.side) o) rfl hη
    have hS := devSum_nonneg T s nn ρ₀ (w := fun _ => 1) (fun _ => zero_le_one) D (n * ℓ.side) u.1 o
    have hm := maxDev_nonneg T (s + D) u.2.2.1 (topField ℓ (s + D) (n * ℓ.side) u.1) (siteAbove ℓ.side (D + 1) n o)
      ((ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2)
    have hc0 := maxCurv_nonneg u.2.2.1 (siteAbove ℓ.side (D + 1) n o) (ballRadius ℓ.side nn ρ₀ (D + 1) + 1)
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    have hDe : 0 ≤ (D : ℝ) * e := mul_nonneg hD0 he
    show max (maxCurvatureOnBall u.2.2.1 (siteAbove ℓ.side (D + 1) n o) (ballRadius ℓ.side nn ρ₀ (D + 1) + 1))
        (widenedStageMax s nn ρ₀ D (n * ℓ.side) u.1 o) ≤
      maxCurvatureOnBall u.2.2.1 (siteAbove ℓ.side (D + 1) n o) (ballRadius ℓ.side nn ρ₀ (D + 1) + 1) +
        4 * (devSum T s nn ρ₀ (fun _ => 1) D (n * ℓ.side) u.1 o +
          1 * maxDeviationOnBall T (s + D) u.2.2.1 (topField ℓ (s + D) (n * ℓ.side) u.1) (siteAbove ℓ.side (D + 1) n o)
            ((ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2)) + ((D + 1 : ℕ) : ℝ) * e
    push_cast
    refine max_le (by nlinarith) ?_
    linarith
end Sizes
section Logs
variable {ℓ : TorusLumps.StepParameters}
private theorem frameOne_siteOfInt {L n : ℕ} [NeZero n] (e : Fin 4 → ℤ) :
    torusSiteInFrame (stepBlockFrame L n) 1 (siteOfInt e : TorusSite n) = siteOfCoords (F := stepBlockFrame L n) 1 e := by
  funext k
  exact intCast_cast_intCast (_root_.YangMills.Construction.BlockTrees.stepBlockFrame_period_one k) (e k)
private theorem toTorusSite_frameOne {L n : ℕ} [NeZero n] (z : TorusSite n) :
    toTorusSite n (torusSiteInFrame (stepBlockFrame L n) 1 z) = z := by
  funext k
  exact intCast_cast_intCast_cast (_root_.YangMills.Construction.BlockTrees.stepBlockFrame_period_one k).symm (z k)
private theorem axial_defect_le (hAx : axialGaugeNearOneStatement) (ℓ : TorusLumps.StepParameters) {n : ℕ} [NeZero n]
    (V : TorusField n) (o : TorusSite n)
    (R : ℕ) (hR : 2 * (R + 1) + 2 < n) {c : ℝ} (hc0 : 0 ≤ c)
    (hcold : ∀ p ∈ plaquettesIn (supBall o ((R : ℝ) + 1)), curvature V p.1 p.2.1 p.2.2 ≤ c) (b : TorusBond n)
    (hb : _root_.YangMills.Construction.TorusFields.supDist o b.1 ≤ R) :
    ‖((ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ V o) V b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 3 * ((R : ℝ) + 1) * c := by
  obtain ⟨x, i⟩ := b
  obtain ⟨e, he, hbd⟩ := exists_offset_of_supDist o x
  simp only at hb
  have hin : ∀ k, |e k| ≤ ((R + 1 : ℕ) : ℤ) := fun k => by
    have := (hbd k).trans hb
    push_cast
    rw [abs_le]
    omega
  have hbond : BlockAverages.BondWithinRadius (R + 1) (e, i) := by
    refine ⟨hin, fun k => ?_⟩
    have := (hbd k).trans hb
    by_cases hk : k = i
    · subst hk
      simp only [Pi.add_apply, Pi.single_eq_same]
      push_cast
      rw [abs_le]
      omega
    · simp only [Pi.add_apply, Pi.single_eq_of_ne hk, add_zero]
      exact hin k
  have hmain := hAx (stepBlockFrame ℓ.side n) (readAtLevel (stepBlockFrame ℓ.side n) 1 V)
    (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 o) c (R + 1) (fun _ => hR) hc0 ?_ (e, i) hbond
  · have hx : torusSiteInFrame (stepBlockFrame ℓ.side n) 1 o + siteOfCoords (F := stepBlockFrame ℓ.side n) 1 e =
        torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x := by
      rw [he, frameOne_add, frameOne_siteOfInt]
    have hval : BlockAverages.gaugeTransform
        (axialGaugeHolonomy (readAtLevel (stepBlockFrame ℓ.side n) 1 V) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 o))
        (readAtLevel (stepBlockFrame ℓ.side n) 1 V)
        (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 o + siteOfCoords (F := stepBlockFrame ℓ.side n) 1 e) i =
        ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ V o) V (x, i) := by
      rw [hx]
      show _ * readAtLevel (stepBlockFrame ℓ.side n) 1 V (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x) i *
        (axialGaugeHolonomy (readAtLevel (stepBlockFrame ℓ.side n) 1 V) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 o)
          (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x +
            BlockAverages.unitStep (F := stepBlockFrame ℓ.side n) 1 i))⁻¹ = _
      rw [readAtLevel_torusSiteInFrame _ 1 _root_.YangMills.Construction.BlockTrees.stepBlockFrame_period_one V x i, ← frameOne_unitStep, ← frameOne_add]
      rfl
    have h2 : ‖((ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ V o) V (x, i) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        3 * ((R + 1 : ℕ) : ℝ) * c := by
      rw [← hval]
      exact hmain
    push_cast at h2
    exact h2
  · intro a k l hkl h1 h2 h3 h4
    have hz : torusSiteInFrame (stepBlockFrame ℓ.side n) 1 o + siteOfCoords (F := stepBlockFrame ℓ.side n) 1 a =
        torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (o + siteOfInt a) := by
      rw [frameOne_add, frameOne_siteOfInt]
    show plaquetteDefect (readAtLevel (stepBlockFrame ℓ.side n) 1 V)
      (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 o + siteOfCoords (F := stepBlockFrame ℓ.side n) 1 a, k, l) ≤ c
    rw [hz, TopLevelSites.plaquetteDefect_readAtLevel_eq _root_.YangMills.Construction.BlockTrees.stepBlockFrame_period_one, toTorusSite_frameOne]
    have hcorner : ∀ q : Fin 4 → ℤ, BlockAverages.WithinRadius (R + 1) q →
        o + siteOfInt q ∈ supBall o ((R : ℝ) + 1) := fun q hq => by
      refine mem_supBall_iff.2 ?_
      have h5 := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le o q (R + 1) fun j => by
        have := hq j
        rw [abs_le] at this
        push_cast at this
        omega
      rw [supDist_comm]
      have : (_root_.YangMills.Construction.TorusFields.supDist o (o + siteOfInt q) : ℝ) ≤ ((R + 1 : ℕ) : ℝ) := by exact_mod_cast h5
      push_cast at this
      exact this
    refine hcold (o + siteOfInt a, k, l) ?_
    simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hkl, fun z hz' => ?_⟩
    simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz'
    rcases hz' with rfl | rfl | rfl | rfl
    · exact hcorner a h1
    · rw [unitStep_eq_ofInt, add_assoc, ← siteOfInt_add]
      exact hcorner _ h2
    · rw [unitStep_eq_ofInt, add_assoc, ← siteOfInt_add]
      exact hcorner _ h3
    · rw [unitStep_eq_ofInt, unitStep_eq_ofInt, add_assoc, add_assoc, ← siteOfInt_add, ← siteOfInt_add, ← add_assoc]
      exact hcorner _ h4
private theorem ballRadius_succ (L : ℕ) (hL : 0 < L) (nn ρ₀ : ℝ) (D : ℕ) :
    ballRadius L nn ρ₀ D / (L : ℝ) + (4 * ρ₀ - 4 * ρ₀ / (L : ℝ)) = ballRadius L nn ρ₀ (D + 1) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  unfold ballRadius
  rw [pow_succ]
  field_simp
  ring
private theorem parentBlock_near {L n : ℕ} [NeZero n] [NeZero L] (o' x : TorusSite (n * L)) {r : ℝ}
    (hx : x ∈ supBall o' r) :
    (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L x) (parentBlock L o') : ℝ) ≤ r / (L : ℝ) + 1 := by
  have h := TorusBalls.supDist_parentBlock_le_div_add_one L x o'
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have h1 : ((_root_.YangMills.Construction.TorusFields.supDist x o' / L : ℕ) : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist x o' : ℝ) / L := Nat.cast_div_le
  have h2 : (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L x) (parentBlock L o') : ℝ) ≤ ((_root_.YangMills.Construction.TorusFields.supDist x o' / L : ℕ) : ℝ) + 1 := by
    exact_mod_cast h
  have h3 : (_root_.YangMills.Construction.TorusFields.supDist x o' : ℝ) / L ≤ r / L := div_le_div_of_nonneg_right (mem_supBall_iff.1 hx) hL.le
  linarith
variable {T : StageTower ℓ} {s : ℕ} {nn ρ₀ m e N₀ side : ℝ} {A : ℕ}
private theorem gaugeSmall_along (H : StepsHalve T s nn ρ₀ m e N₀ side A) (hs2 : 2 ≤ side) (he : 0 ≤ e) (hN₀ : 0 ≤ N₀)
    (hρ0 : 0 ≤ ρ₀) (hodd : Odd ℓ.side) (hslack : 1 + ρ₀ ≤ 4 * ρ₀ - 4 * ρ₀ / (ℓ.side : ℝ)) {Nb sz : ℝ} (hNb : N₀ ≤ Nb)
    (hNb1 : 1 ≤ Nb) :
    ∀ D, D ≤ A → ∀ (n : ℕ) [NeZero n], side ≤ n → ∀ (u : MarkedSample ℓ (s + D) n) (o : TorusSite (fineSide ℓ.side D n))
      (g : TorusSite n → UnitQuaternion) (a : ℝ), 0 ≤ a → GoodAlong T s m D n u o →
      (∀ b : TorusBond n, b.1 ∈ supBall (siteAbove ℓ.side D n o) (ballRadius ℓ.side nn ρ₀ D) →
        ‖((ResponseInTheExpansion.gaugeTransform g (topField ℓ (s + D) n u) b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ a) →
      2 * (a + Nb * widenedStageSum T s nn ρ₀ D n u o + D * e) ≤ sz →
      widenedStageMax s nn ρ₀ D n u o ≤ sz →
      IsGaugeSmallAlong T s nn ρ₀ sz D n u o g := by
  have hLpos : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne ℓ.side)
  intro D
  induction D with
  | zero =>
    intro _ n _ _ u o g a ha _ hch hsum _ b hb
    have h1 := hch b hb
    have h2 := GaugeFixing.norm_minimalLog_le (ResponseInTheExpansion.gaugeTransform g (topField ℓ (s + 0) n u) b)
    have hz := stageSum_nonneg T s nn ρ₀ 0 n u o
    have : Nb * widenedStageSum T s nn ρ₀ 0 n u o = 0 := by simp [widenedStageSum]
    simp only [Nat.cast_zero, zero_mul, add_zero] at hsum
    rw [this] at hsum
    refine h2.trans ?_
    linarith
  | succ D ih =>
    intro hD n _ hn u o g a ha hg hch hsum hmax
    obtain ⟨hc, hη, hg'⟩ := hg
    set V : TorusField n := u.2.2.1 with hV
    set W : TorusField (n * ℓ.side) := topField ℓ (s + D) (n * ℓ.side) u.1 with hW
    set oV : TorusSite n := siteAbove ℓ.side (D + 1) n o with hoV
    set oW : TorusSite (n * ℓ.side) := siteAbove ℓ.side D (n * ℓ.side) o with hoW
    have hblock : parentBlock ℓ.side oW = oV := rfl
    set cN := maxCurvatureOnBall V oV (ballRadius ℓ.side nn ρ₀ (D + 1) + 1) with hcN
    set mx := maxDeviationOnBall T (s + D) V W oV ((ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2) with hmx
    have hcN0 : 0 ≤ cN := maxCurv_nonneg _ _ _
    have hmx0 : 0 ≤ mx := maxDev_nonneg _ _ _ _ _ _
    have hS : widenedStageSum T s nn ρ₀ (D + 1) n u o = cN + mx + widenedStageSum T s nn ρ₀ D (n * ℓ.side) u.1 o := rfl
    have hS0 := stageSum_nonneg T s nn ρ₀ D (n * ℓ.side) u.1 o
    have hMax : widenedStageMax s nn ρ₀ (D + 1) n u o = max cN (widenedStageMax s nn ρ₀ D (n * ℓ.side) u.1 o) := rfl
    rw [hS] at hsum
    rw [hMax] at hmax
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    have hDe : 0 ≤ (D : ℝ) * e := mul_nonneg hD0 he
    push_cast at hsum
    have hNbS : 0 ≤ Nb * widenedStageSum T s nn ρ₀ D (n * ℓ.side) u.1 o := mul_nonneg (by linarith) hS0
    have hNc : N₀ * cN ≤ Nb * cN := mul_le_mul_of_nonneg_right hNb hcN0
    have hNm : mx ≤ Nb * mx := by nlinarith
    have hn2 : 2 ≤ n := by
      have : (2 : ℝ) ≤ n := hs2.trans hn
      exact_mod_cast this
    refine ⟨fun b hb => ?_, fun z hz μ ν => ?_, ?_⟩
    · have h1 : ‖((ResponseInTheExpansion.gaugeTransform g V b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ a := hch b hb
      have h2 := GaugeFixing.norm_minimalLog_le (ResponseInTheExpansion.gaugeTransform g V b)
      refine h2.trans ?_
      nlinarith
    · refine (curvature_le_maxCurv_wide V oV z hz μ ν).trans (le_trans (le_max_left _ _) hmax)
    · have hbound : ∀ b : TorusBond (n * ℓ.side), b.1 ∈ supBall oW (ballRadius ℓ.side nn ρ₀ D) →
          ‖((ResponseInTheExpansion.gaugeTransform (fun x => g (parentBlock ℓ.side x) * blockTreeGauge ℓ W x) W b :
            UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ a + (N₀ * cN + e + mx) := by
        intro b hb
        have hnear := parentBlock_near oW b.1 hb
        rw [hblock] at hnear
        have hstep := ballRadius_succ ℓ.side hLpos nn ρ₀ D
        have hin1 : parentBlock ℓ.side b.1 ∈ supBall oV (ballRadius ℓ.side nn ρ₀ (D + 1)) :=
          mem_supBall_iff.2 (by linarith)
        refine defect_down ℓ hodd hn2 g V W b ha (by positivity) (hch _ hin1) fun hb' => ?_
        have hsub : supBall (parentBlock ℓ.side b.1) ρ₀ ⊆ supBall oV (ballRadius ℓ.side nn ρ₀ (D + 1)) := by
          intro z hz
          have h1 := mem_supBall_iff.1 hz
          have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle z (parentBlock ℓ.side b.1) oV
          have h3 : (_root_.YangMills.Construction.TorusFields.supDist z oV : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist z (parentBlock ℓ.side b.1) : ℝ) + _root_.YangMills.Construction.TorusFields.supDist (parentBlock ℓ.side b.1) oV := by
            exact_mod_cast h2
          exact mem_supBall_iff.2 (by linarith)
        have hf := H.frame D (by omega) n hn oV V hc b hb' hsub
        have hwide := maxCurv_mono V oV (r := ballRadius ℓ.side nn ρ₀ (D + 1))
          (r' := ballRadius ℓ.side nn ρ₀ (D + 1) + 1) (by linarith)
        have hLr : (0 : ℝ) < ℓ.side := by exact_mod_cast hLpos
        have hmem : b ∈ chartBondsInBlocks ℓ.side (supBall oV ((ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2)) := by
          simp only [chartBondsInBlocks, Finset.mem_filter]
          refine ⟨hb', mem_supBall_iff.2 ?_⟩
          have : ballRadius ℓ.side nn ρ₀ D / (ℓ.side : ℝ) ≤ (ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) :=
            div_le_div_of_nonneg_right (by linarith) hLr.le
          linarith
        have hη' : ‖(stepDeviation T (s + D) V W b : ℍ[ℝ])‖ ≤ mx :=
          le_finsetSup (f := fun b => ‖(stepDeviation T (s + D) V W b : ℍ[ℝ])‖) hmem
        have hsplit : ((chartCoord ℓ V W b : imaginaryQuaternions) : ℍ[ℝ]) = (stepDeviation T (s + D) V W b : ℍ[ℝ]) +
            (frameCoord ℓ (T.stage (s + D)).anchorRadius (s + D) (T.stage (s + D)).toStepSetup.frameReach V b : ℍ[ℝ]) := by
          simp [stepDeviation, _root_.YangMills.Construction.StepMarks.frameDeviation]
        rw [hsplit]
        refine (norm_add_le _ _).trans ?_
        nlinarith
      refine ih (by omega) (n * ℓ.side) (side_le_mul (by linarith) hn) u.1 o _ (a + (N₀ * cN + e + mx)) (by positivity)
        hg' hbound ?_ (le_trans (le_max_right _ _) hmax)
      push_cast
      nlinarith
end Logs
section Norms
open scoped ENNReal
variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
private def InLp (μ : Measure Ω) (p : ℝ≥0∞) (f : Ω → ℝ) (a : ℝ) : Prop :=
  MemLp f p μ ∧ eLpNorm f p μ ≤ ENNReal.ofReal a
private theorem InLp.add {p : ℝ≥0∞} (hp : 1 ≤ p) {f g : Ω → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hf : InLp μ p f a)
    (hg : InLp μ p g b) : InLp μ p (fun x => f x + g x) (a + b) := by
  refine ⟨hf.1.add hg.1, (eLpNorm_add_le hf.1.1 hg.1.1 hp).trans ?_⟩
  rw [ENNReal.ofReal_add ha hb]
  exact add_le_add hf.2 hg.2
private theorem InLp.smul {p : ℝ≥0∞} {f : Ω → ℝ} {a c : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hf : InLp μ p f a) :
    InLp μ p (fun x => c * f x) (c * a) := by
  refine ⟨hf.1.const_mul c, ?_⟩
  have e : (fun x => c * f x) = c • f := by
    funext x
    simp
  rw [e, eLpNorm_const_smul, ENNReal.ofReal_mul hc]
  have hn : ‖c‖ₑ = ENNReal.ofReal c := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hc]
  rw [hn]
  exact mul_le_mul_right hf.2 _
private theorem InLp.mono {p : ℝ≥0∞} {f g : Ω → ℝ} {a : ℝ} (hf : InLp μ p f a) (hg : AEStronglyMeasurable g μ)
    (h : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖f x‖) : InLp μ p g a :=
  ⟨hf.1.mono hg h, (eLpNorm_mono_ae h).trans hf.2⟩
private theorem InLp.const [IsProbabilityMeasure μ] {p : ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c) : InLp μ p (fun _ => c) c := by
  refine ⟨memLp_const c, ?_⟩
  have h := eLpNorm_le_of_ae_bound (μ := μ) (p := p) (f := fun _ : Ω => c) (C := c)
    (Filter.Eventually.of_forall fun x => by simp [abs_of_nonneg hc])
  simpa using h
private theorem InLp.comp {Ω' : Type} {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'} {p : ℝ≥0∞} {f : Ω' → ℝ} {a : ℝ}
    {φ : Ω → Ω'} (hφ : MeasurePreserving φ μ ν) (hf : InLp ν p f a) : InLp μ p (fun x => f (φ x)) a :=
  ⟨hf.1.comp_measurePreserving hφ, by
    have := eLpNorm_comp_measurePreserving (p := p) hf.1.1 hφ
    exact (le_of_eq this).trans hf.2⟩
private theorem InLp.le {p : ℝ≥0∞} {f : Ω → ℝ} {a b : ℝ} (hf : InLp μ p f a) (h : a ≤ b) : InLp μ p f b :=
  ⟨hf.1, hf.2.trans (ENNReal.ofReal_le_ofReal h)⟩
private theorem inLp_of_moment {f : Ω → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hm : AEStronglyMeasurable f μ) {q : ℕ} (hq : 1 ≤ q)
    (hI : Integrable (fun x => f x ^ q) μ) {B : ℝ} (hB : 0 ≤ B) (h : ∫ x, f x ^ q ∂μ ≤ B ^ q) : InLp μ q f B := by
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hqt : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top q
  have htr : ((q : ℝ≥0∞)).toReal = q := by simp
  have e : (fun x => ‖f x‖ ^ ((q : ℝ≥0∞)).toReal) = fun x => f x ^ q := by
    funext x
    rw [htr, Real.rpow_natCast, Real.norm_of_nonneg (hf0 x)]
  have hmem : MemLp f q μ := (integrable_norm_rpow_iff hm hq0 hqt).1 (by rw [e]; exact hI)
  refine ⟨hmem, ?_⟩
  rw [hmem.eLpNorm_eq_integral_rpow_norm hq0 hqt, e, htr]
  refine ENNReal.ofReal_le_ofReal ?_
  have hq' : q ≠ 0 := by omega
  calc (∫ x, f x ^ q ∂μ) ^ ((q : ℝ)⁻¹)
      ≤ (B ^ q) ^ ((q : ℝ)⁻¹) :=
        Real.rpow_le_rpow (integral_nonneg fun x => pow_nonneg (hf0 x) q) h (by positivity)
    _ = B := Real.pow_rpow_inv_natCast hB hq'
private theorem moment_of_inLp {f : Ω → ℝ} (hf0 : ∀ x, 0 ≤ f x) {q : ℕ} (hq : 1 ≤ q) {B : ℝ} (hB : 0 ≤ B)
    (h : InLp μ q f B) : Integrable (fun x => f x ^ q) μ ∧ ∫ x, f x ^ q ∂μ ≤ B ^ q := by
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hqt : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top q
  have htr : ((q : ℝ≥0∞)).toReal = q := by simp
  have e : (fun x => ‖f x‖ ^ ((q : ℝ≥0∞)).toReal) = fun x => f x ^ q := by
    funext x
    rw [htr, Real.rpow_natCast, Real.norm_of_nonneg (hf0 x)]
  have hI : Integrable (fun x => f x ^ q) μ := by
    rw [← e]
    exact (integrable_norm_rpow_iff h.1.1 hq0 hqt).2 h.1
  refine ⟨hI, ?_⟩
  have h2 := h.2
  rw [h.1.eLpNorm_eq_integral_rpow_norm hq0 hqt, e, htr, ENNReal.ofReal_le_ofReal_iff hB] at h2
  have hq' : q ≠ 0 := by omega
  have hnn : 0 ≤ ∫ x, f x ^ q ∂μ := integral_nonneg fun x => pow_nonneg (hf0 x) q
  calc ∫ x, f x ^ q ∂μ = ((∫ x, f x ^ q ∂μ) ^ ((q : ℝ)⁻¹)) ^ q := (Real.rpow_inv_natCast_pow hnn hq').symm
    _ ≤ B ^ q := pow_le_pow_left₀ (Real.rpow_nonneg hnn _) h2 q
private theorem integral_le_of_condExp [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {D : Set Ω}
    (hD : MeasurableSet[m] D) {f : Ω → ℝ} (hf : Integrable f μ) (hsupp : ∀ x, x ∉ D → f x = 0) {c : ℝ} (hc : 0 ≤ c)
    (hbd : ∀ᵐ x ∂μ, x ∈ D → (μ[f | m]) x ≤ c) : ∫ x, f x ∂μ ≤ c := by
  have h1 : ∫ x in D, f x ∂μ = ∫ x, f x ∂μ := setIntegral_eq_integral_of_forall_compl_eq_zero hsupp
  rw [← h1, ← setIntegral_condExp hm hf hD]
  have hD' := hm D hD
  have h2 : ∫ x in D, (μ[f | m]) x ∂μ ≤ ∫ x in D, c ∂μ := by
    refine setIntegral_mono_on_ae integrable_condExp.integrableOn (integrableOn_const (by simp)) hD' ?_
    filter_upwards [hbd] with x hx hxD using hx hxD
  refine h2.trans ?_
  rw [setIntegral_const]
  simp only [smul_eq_mul]
  have : μ.real D ≤ 1 := measureReal_le_one
  nlinarith
end Norms
section Scene
open scoped ENNReal
variable {ℓ : TorusLumps.StepParameters}
private theorem measurable_lower (ℓ : TorusLumps.StepParameters) (h n : ℕ) :
    Measurable fun u : MarkedSample ℓ (h + 1) n => u.1 := by apply _root_.YangMills.SharedProofs.p1941 <;> assumption
private theorem measurable_sampleBelow (ℓ : TorusLumps.StepParameters) (s : ℕ) :
    ∀ (D n : ℕ), Measurable (sampleBelow ℓ s D n) := by apply _root_.YangMills.SharedProofs.p11381 <;> assumption
private theorem measurable_topField' (ℓ : TorusLumps.StepParameters) : ∀ (s n : ℕ), Measurable (topField ℓ s n)
  | 0, _ => measurable_id
  | s + 1, n => by
    let _ := markedSampleMeasurableSpace ℓ s (n * ℓ.side)
    exact (measurable_fst.comp (measurable_snd.comp measurable_snd) :
      Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => u.2.2.1)
private theorem measurable_finsetSup {X α : Type} [MeasurableSpace X] (S : Finset α) {f : X → α → ℝ}
    (hf : ∀ a ∈ S, Measurable fun x => f x a) : Measurable fun x => finsetSupNonneg S (f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa [finsetSupNonneg] using measurable_const
  | insert a S ha ih =>
    have e : (fun x => finsetSupNonneg (insert a S) (f x)) = fun x => max (f x a) (finsetSupNonneg S (f x)) := by
      funext x
      simp [finsetSupNonneg, Finset.fold_insert ha]
    rw [e]
    exact (hf a (Finset.mem_insert_self _ _)).max (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))
private theorem measurable_maxCurv {n : ℕ} [NeZero n] (o : TorusSite n) (r : ℝ) :
    Measurable fun W : TorusField n => maxCurvatureOnBall W o r := by
  refine measurable_finsetSup _ fun p _ => ?_
  have h : Measurable fun W : TorusField n => holonomy W p.1 p.2.1 p.2.2 := by
    have e : ∀ x i, Measurable fun W : TorusField n => W x i := fun x i =>
      (measurable_pi_apply i).comp (measurable_pi_apply x)
    unfold holonomy
    exact (((e _ _).mul (e _ _)).mul (e _ _).inv).mul (e _ _).inv
  have hc : Continuous fun g : UnitQuaternion => ‖(g : ℍ[ℝ]) - 1‖ := (continuous_subtype_val.sub continuous_const).norm
  exact hc.measurable.comp h
private def TopClear (T : StageTower ℓ) (h : ℕ) (m : ℝ) {n : ℕ} [NeZero n] (o : TorusSite n) :
    Set (MarkedSample ℓ (h + 1) n) :=
  {u | Disjoint (stageState T (h + 1) n u).2.1 (supBall o m) ∧ StepAvoids T h m o u}
private def Clear (T : StageTower ℓ) (s : ℕ) (m : ℝ) (D n : ℕ) [NeZero n] (u : MarkedSample ℓ (s + D) n)
    (o : TorusSite (fineSide ℓ.side D n)) : Prop :=
  Disjoint (stageState T (s + D) n u).2.1 (supBall (siteAbove ℓ.side D n o) m) ∧ StepsAvoidOrigin T s m D n u o
private structure ChainScene (T : StageTower ℓ) (β : ℝ) (k H : ℕ) (m side Rm B : ℝ) (q : ℕ) : Prop where
  q_pos : 1 ≤ q
  B_nonneg : 0 ≤ B
  side_nonneg : 0 ≤ side
  prob : ∀ (h n : ℕ) [NeZero n], IsProbabilityMeasure (markedSampleLaw T β h n)
  below : ∀ (s D n : ℕ) [NeZero n],
    Measure.map (sampleBelow ℓ s D n) (markedSampleLaw T β (s + D) n) = markedSampleLaw T β s (fineSide ℓ.side D n)
  state : ∀ (h n : ℕ) [NeZero n] (S : Finset (TorusSite n)), MeasurableSet {u | Disjoint (stageState T h n u).2.1 S}
  down : ∀ h, k ≤ h → h < H → ∀ (n : ℕ) [NeZero n], side ≤ n → ℓ.side ∣ n → ∀ o : TorusSite n,
    ∀ᵐ u ∂(markedSampleLaw T β (h + 1) n), Disjoint (stageState T (h + 1) n u).2.1 (supBall o m) →
      IsColdOnBall ℓ.threshold u.2.2.1 o m ∧
      (StepAvoids T h m o u →
        (∀ o' : TorusSite (n * ℓ.side), parentBlock ℓ.side o' = o →
          Disjoint (stageState T h (n * ℓ.side) u.1).2.1 (supBall o' m)) ∧
        ∀ b ∈ chartBondsInBlocks ℓ.side (supBall o m),
          ‖(stepDeviation T h u.2.2.1 (topField ℓ h (n * ℓ.side) u.1) b : ℍ[ℝ])‖ < ℓ.threshold / 64)
  event : ∀ h, k ≤ h → h < H → ∀ (n : ℕ) [NeZero n], side ≤ n → ℓ.side ∣ n → ∀ o : TorusSite n,
    NullMeasurableSet (TopClear T h m o) (markedSampleLaw T β (h + 1) n)
  moment : ∀ h, k ≤ h → h < H → ∀ (n : ℕ) [NeZero n], side ≤ n → ℓ.side ∣ n → ∀ (o : TorusSite n) (R : ℝ), R ≤ Rm →
    InLp (markedSampleLaw T β (h + 1) n) q
      ((TopClear T h m o).indicator fun u => maxDeviationOnBall T h u.2.2.1 (topField ℓ h (n * ℓ.side) u.1) o R) B
variable {T : StageTower ℓ} {β : ℝ} {k H s q : ℕ} {nn ρ₀ m side Rm B : ℝ}
private theorem ChainScene.fst (S : ChainScene T β k H m side Rm B q) (h n : ℕ) [NeZero n] :
    MeasurePreserving (fun u : MarkedSample ℓ (h + 1) n => u.1) (markedSampleLaw T β (h + 1) n)
      (markedSampleLaw T β h (n * ℓ.side)) :=
  ⟨measurable_lower ℓ h n, S.below h 1 n⟩
private theorem side_dvd_mul {n : ℕ} : ℓ.side ∣ n * ℓ.side := Dvd.intro_left n rfl
private theorem clear_succ (S : ChainScene T β k H m side Rm B q) (hs : k ≤ s) {D : ℕ} (hD : s + D < H) {n : ℕ}
    [NeZero n] (hn : side ≤ n) (hLn : ℓ.side ∣ n) (o : TorusSite (fineSide ℓ.side (D + 1) n)) :
    ∀ᵐ u ∂(markedSampleLaw T β (s + (D + 1)) n), (Clear T s m (D + 1) n u o ↔
      u ∈ TopClear T (s + D) m (siteAbove ℓ.side (D + 1) n o) ∧ Clear T s m D (n * ℓ.side) u.1 o) := by
  have hdn := S.down (s + D) (by omega) hD n hn hLn (siteAbove ℓ.side (D + 1) n o)
  refine hdn.mono fun u hu => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hdis, hsm, hfc⟩ := h
    have h2 := (hu hdis).2 hfc
    exact ⟨⟨hdis, hfc⟩, h2.1 (siteAbove ℓ.side D (n * ℓ.side) o) rfl, hsm⟩
  · obtain ⟨⟨hd, hm⟩, _, hsm⟩ := h
    exact ⟨hd, hsm, hm⟩
private theorem good_ae (S : ChainScene T β k H m side Rm B q) (hs : k ≤ s) :
    ∀ D, s + D ≤ H → ∀ (n : ℕ) [NeZero n], side ≤ n → ℓ.side ∣ n → ∀ o : TorusSite (fineSide ℓ.side D n),
      ∀ᵐ u ∂(markedSampleLaw T β (s + D) n), Clear T s m D n u o →
        GoodAlong T s m D n u o ∧ Disjoint (stageState T s _ (sampleBelow ℓ s D n u)).2.1 (supBall o m) := by
  intro D
  induction D with
  | zero =>
    intro _ n _ _ _ o
    exact Filter.Eventually.of_forall fun u h => ⟨trivial, h.1⟩
  | succ D ih =>
    intro hD n _ hn hLn o
    have hih := ih (by omega) (n * ℓ.side) (side_le_mul S.side_nonneg hn) side_dvd_mul o
    have hlift : ∀ᵐ u ∂(markedSampleLaw T β (s + (D + 1)) n), Clear T s m D (n * ℓ.side) u.1 o →
        GoodAlong T s m D (n * ℓ.side) u.1 o ∧
          Disjoint (stageState T s _ (sampleBelow ℓ s D (n * ℓ.side) u.1)).2.1 (supBall o m) :=
      (S.fst (s + D) n).quasiMeasurePreserving.ae hih
    have hdn := S.down (s + D) (by omega) (by omega) n hn hLn (siteAbove ℓ.side (D + 1) n o)
    filter_upwards [hlift, hdn, clear_succ S hs (by omega) hn hLn o] with u h1 h2 h3 hEv
    obtain ⟨htop, hlow⟩ := h3.1 hEv
    have hg := h1 hlow
    have hd := h2 htop.1
    exact ⟨⟨hd.1, (hd.2 htop.2).2, hg.1⟩, hg.2⟩
private theorem clear_null (S : ChainScene T β k H m side Rm B q) (hs : k ≤ s) :
    ∀ D, s + D ≤ H → ∀ (n : ℕ) [NeZero n], side ≤ n → ℓ.side ∣ n → ∀ o : TorusSite (fineSide ℓ.side D n),
      NullMeasurableSet {u | Clear T s m D n u o} (markedSampleLaw T β (s + D) n) := by
  intro D
  induction D with
  | zero =>
    intro _ n _ _ _ o
    have h := S.state (s + 0) n (supBall o m)
    have e : {u | Clear T s m 0 n u o} = {u | Disjoint (stageState T (s + 0) n u).2.1 (supBall o m)} := by
      ext u
      exact ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩
    rw [e]
    exact h.nullMeasurableSet
  | succ D ih =>
    intro hD n _ hn hLn o
    have h1 := (S.event (s + D) (by omega) (by omega) n hn hLn (siteAbove ℓ.side (D + 1) n o)).inter
      ((ih (by omega) (n * ℓ.side) (side_le_mul S.side_nonneg hn) side_dvd_mul o).preimage
        (S.fst (s + D) n).quasiMeasurePreserving)
    refine NullMeasurableSet.congr h1 ?_
    filter_upwards [clear_succ S hs (by omega) hn hLn o] with u hu
    exact propext hu.symm
private theorem devSum_inLp (S : ChainScene T β k H m side Rm B q) (hs : k ≤ s) {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hrad : ∀ D, (ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2 ≤ Rm) :
    ∀ D, s + D ≤ H → ∀ (n : ℕ) [NeZero n], side ≤ n → ℓ.side ∣ n → ∀ o : TorusSite (fineSide ℓ.side D n),
      InLp (markedSampleLaw T β (s + D) n) q ({u | Clear T s m D n u o}.indicator fun u => devSum T s nn ρ₀ w D n u o)
        ((∑ i ∈ Finset.range D, w i) * B) := by
  have hp : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast S.q_pos
  intro D
  induction D with
  | zero =>
    intro _ n _ _ _ o
    have e : ({u | Clear T s m 0 n u o}.indicator fun u => devSum T s nn ρ₀ w 0 n u o) = fun _ => 0 := by
      funext u
      simp [devSum]
    rw [e]
    simp only [Finset.range_zero, Finset.sum_empty, zero_mul]
    exact ⟨MemLp.zero', by simp⟩
  | succ D ih =>
    intro hD n _ hn hLn o
    haveI := S.prob (s + (D + 1)) n
    set oV := siteAbove ℓ.side (D + 1) n o with hoV
    set R := (ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2 with hR
    have hg := ih (by omega) (n * ℓ.side) (side_le_mul S.side_nonneg hn) side_dvd_mul o
    have hK := S.moment (s + D) (by omega) (by omega) n hn hLn oV R (hrad D)
    have hG := hg.comp (S.fst (s + D) n)
    have hsum0 : 0 ≤ ∑ i ∈ Finset.range D, w i := Finset.sum_nonneg fun i _ => hw i
    have hR0 := InLp.add hp (mul_nonneg hsum0 S.B_nonneg) (mul_nonneg (hw D) S.B_nonneg) hG
      (InLp.smul (hw D) S.B_nonneg hK)
    have hA := clear_null S hs (D + 1) hD n hn hLn o
    have heq : ∀ᵐ u ∂(markedSampleLaw T β (s + (D + 1)) n),
        ({u | Clear T s m (D + 1) n u o}.indicator fun u => devSum T s nn ρ₀ w (D + 1) n u o) u =
        ({u | Clear T s m (D + 1) n u o}.indicator fun u =>
          ({u | Clear T s m D (n * ℓ.side) u o}.indicator fun u => devSum T s nn ρ₀ w D (n * ℓ.side) u o) u.1 +
            w D * (TopClear T (s + D) m oV).indicator
              (fun u => maxDeviationOnBall T (s + D) u.2.2.1 (topField ℓ (s + D) (n * ℓ.side) u.1) oV R) u) u := by
      filter_upwards [clear_succ S hs (by omega) hn hLn o] with u hu
      by_cases huA : u ∈ {u | Clear T s m (D + 1) n u o}
      · obtain ⟨htop, hlow⟩ := hu.1 huA
        rw [Set.indicator_of_mem huA, Set.indicator_of_mem huA,
          Set.indicator_of_mem (show u.1 ∈ {v | Clear T s m D (n * ℓ.side) v o} from hlow),
          Set.indicator_of_mem htop]
        rfl
      · rw [Set.indicator_of_notMem huA, Set.indicator_of_notMem huA]
    have hI := (hR0.1.1.indicator₀ hA).congr (Filter.EventuallyEq.symm heq)
    have hfin := hR0.mono hI (by
      filter_upwards [heq] with u hu
      rw [hu]
      exact norm_indicator_le_norm_self _ _)
    refine hfin.le (le_of_eq ?_)
    rw [Finset.sum_range_succ]
    ring
end Scene
section Bounds
open scoped ENNReal
variable {ℓ : TorusLumps.StepParameters}
private theorem stageMax_nonneg (s : ℕ) (nn ρ₀ : ℝ) :
    ∀ (D n : ℕ) [NeZero n] (u : MarkedSample ℓ (s + D) n) (o : TorusSite (fineSide ℓ.side D n)),
      0 ≤ widenedStageMax s nn ρ₀ D n u o := by
  intro D n _ u o
  cases D with
  | zero => exact maxCurv_nonneg _ _ _
  | succ D => exact le_max_of_le_left (maxCurv_nonneg _ _ _)
abbrev _root_.YangMills.SharedProofs.p78364 := @stageMax_nonneg
variable {T : StageTower ℓ} {β : ℝ} {k H s q : ℕ} {nn ρ₀ m side Rm B : ℝ}
private theorem stageSum_aesm (S : ChainScene T β k H m side Rm B q) (hs : k ≤ s)
    (hrad : ∀ D, (ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2 ≤ Rm) :
    ∀ D, s + D ≤ H → ∀ (n : ℕ) [NeZero n], side ≤ n → ℓ.side ∣ n → ∀ o : TorusSite (fineSide ℓ.side D n),
      AEStronglyMeasurable ({u | Clear T s m D n u o}.indicator fun u => widenedStageSum T s nn ρ₀ D n u o)
        (markedSampleLaw T β (s + D) n) := by
  intro D
  induction D with
  | zero =>
    intro _ n _ _ _ o
    have e : ({u | Clear T s m 0 n u o}.indicator fun u => widenedStageSum T s nn ρ₀ 0 n u o) = fun _ => 0 := by
      funext u
      simp [widenedStageSum]
    rw [e]
    exact aestronglyMeasurable_const
  | succ D ih =>
    intro hD n _ hn hLn o
    set oV := siteAbove ℓ.side (D + 1) n o with hoV
    set R := (ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2 with hR
    have hg := (ih (by omega) (n * ℓ.side) (side_le_mul S.side_nonneg hn) side_dvd_mul o).comp_measurePreserving
      (S.fst (s + D) n)
    have hK := (S.moment (s + D) (by omega) (by omega) n hn hLn oV R (hrad D)).1.1
    have hc : AEStronglyMeasurable (fun u : MarkedSample ℓ (s + (D + 1)) n =>
        maxCurvatureOnBall (topField ℓ (s + (D + 1)) n u) oV (ballRadius ℓ.side nn ρ₀ (D + 1) + 1))
        (markedSampleLaw T β (s + (D + 1)) n) :=
      ((measurable_maxCurv oV _).comp (measurable_topField' ℓ _ n)).aestronglyMeasurable
    have hA := clear_null S hs (D + 1) hD n hn hLn o
    have hR0 := (hc.add hK).add hg
    have heq : ∀ᵐ u ∂(markedSampleLaw T β (s + (D + 1)) n),
        ({u | Clear T s m (D + 1) n u o}.indicator fun u => widenedStageSum T s nn ρ₀ (D + 1) n u o) u =
        ({u | Clear T s m (D + 1) n u o}.indicator
          ((((fun u : MarkedSample ℓ (s + (D + 1)) n =>
            maxCurvatureOnBall (topField ℓ (s + (D + 1)) n u) oV (ballRadius ℓ.side nn ρ₀ (D + 1) + 1)) +
            (TopClear T (s + D) m oV).indicator
              (fun u => maxDeviationOnBall T (s + D) u.2.2.1 (topField ℓ (s + D) (n * ℓ.side) u.1) oV R)) +
            (({u | Clear T s m D (n * ℓ.side) u o}.indicator fun u => widenedStageSum T s nn ρ₀ D (n * ℓ.side) u o) ∘
              fun u : MarkedSample ℓ (s + D + 1) n => u.1)))) u := by
      filter_upwards [clear_succ S hs (by omega) hn hLn o] with u hu
      by_cases huA : u ∈ {u | Clear T s m (D + 1) n u o}
      · obtain ⟨htop, hlow⟩ := hu.1 huA
        rw [Set.indicator_of_mem huA, Set.indicator_of_mem huA]
        simp only [Pi.add_apply, Function.comp]
        rw [Set.indicator_of_mem (show u.1 ∈ {v | Clear T s m D (n * ℓ.side) v o} from hlow), Set.indicator_of_mem htop]
        rfl
      · rw [Set.indicator_of_notMem huA, Set.indicator_of_notMem huA]
    exact (hR0.indicator₀ hA).congr (Filter.EventuallyEq.symm heq)
private theorem stageMax_aesm (S : ChainScene T β k H m side Rm B q) (hs : k ≤ s) :
    ∀ D, s + D ≤ H → ∀ (n : ℕ) [NeZero n], side ≤ n → ℓ.side ∣ n → ∀ o : TorusSite (fineSide ℓ.side D n),
      AEStronglyMeasurable ({u | Clear T s m D n u o}.indicator fun u => widenedStageMax s nn ρ₀ D n u o)
        (markedSampleLaw T β (s + D) n) := by
  intro D
  induction D with
  | zero =>
    intro _ n _ hn hLn o
    have hc : AEStronglyMeasurable (fun u : MarkedSample ℓ (s + 0) n => widenedStageMax s nn ρ₀ 0 n u o)
        (markedSampleLaw T β (s + 0) n) :=
      ((measurable_maxCurv o _).comp (measurable_topField' ℓ s n)).aestronglyMeasurable
    exact hc.indicator₀ (clear_null S hs 0 (by omega) n hn hLn o)
  | succ D ih =>
    intro hD n _ hn hLn o
    set oV := siteAbove ℓ.side (D + 1) n o with hoV
    have hg := (ih (by omega) (n * ℓ.side) (side_le_mul S.side_nonneg hn) side_dvd_mul o).comp_measurePreserving
      (S.fst (s + D) n)
    have hc : AEMeasurable (fun u : MarkedSample ℓ (s + (D + 1)) n =>
        maxCurvatureOnBall (topField ℓ (s + (D + 1)) n u) oV (ballRadius ℓ.side nn ρ₀ (D + 1) + 1))
        (markedSampleLaw T β (s + (D + 1)) n) :=
      ((measurable_maxCurv oV _).comp (measurable_topField' ℓ _ n)).aemeasurable
    have hA := clear_null S hs (D + 1) hD n hn hLn o
    have hR0 := (hc.max hg.aemeasurable).aestronglyMeasurable
    have heq : ∀ᵐ u ∂(markedSampleLaw T β (s + (D + 1)) n),
        ({u | Clear T s m (D + 1) n u o}.indicator fun u => widenedStageMax s nn ρ₀ (D + 1) n u o) u =
        ({u | Clear T s m (D + 1) n u o}.indicator fun u =>
          max (maxCurvatureOnBall (topField ℓ (s + (D + 1)) n u) oV (ballRadius ℓ.side nn ρ₀ (D + 1) + 1))
            (({u | Clear T s m D (n * ℓ.side) u o}.indicator fun u => widenedStageMax s nn ρ₀ D (n * ℓ.side) u o) u.1)) u := by
      filter_upwards [clear_succ S hs (by omega) hn hLn o] with u hu
      by_cases huA : u ∈ {u | Clear T s m (D + 1) n u o}
      · obtain ⟨htop, hlow⟩ := hu.1 huA
        rw [Set.indicator_of_mem huA, Set.indicator_of_mem huA,
          Set.indicator_of_mem (show u.1 ∈ {v | Clear T s m D (n * ℓ.side) v o} from hlow)]
        rfl
      · rw [Set.indicator_of_notMem huA, Set.indicator_of_notMem huA]
    exact (hR0.indicator₀ hA).congr (Filter.EventuallyEq.symm heq)
private theorem chainSize_aesm (S : ChainScene T β k H m side Rm B q) (hs : k ≤ s) (C₁ c : ℝ) (M : ℕ)
    (hrad : ∀ D, (ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2 ≤ Rm)
    (D : ℕ) (hD : s + D ≤ H) (n : ℕ) [NeZero n] (hn : side ≤ n) (hLn : ℓ.side ∣ n) (o : TorusSite (fineSide ℓ.side D n)) :
    AEStronglyMeasurable ({u | Clear T s m D n u o}.indicator fun u => widenedChainSize T C₁ c M s nn ρ₀ D n u o)
      (markedSampleLaw T β (s + D) n) := by
  have hL := (stageSum_aesm (nn := nn) (ρ₀ := ρ₀) S hs hrad D hD n hn hLn o).aemeasurable
  have hM := (stageMax_aesm (nn := nn) (ρ₀ := ρ₀) S hs D hD n hn hLn o).aemeasurable
  have hc : AEMeasurable (fun u : MarkedSample ℓ (s + D) n =>
      maxCurvatureOnBall (topField ℓ (s + D) n u) (siteAbove ℓ.side D n o) (ballRadius ℓ.side nn ρ₀ D + 1))
      (markedSampleLaw T β (s + D) n) :=
    ((measurable_maxCurv _ _).comp (measurable_topField' ℓ _ n)).aemeasurable
  have hR0 : AEMeasurable (fun u : MarkedSample ℓ (s + D) n => min 1 (C₁ * (ρ₀ *
      maxCurvatureOnBall (topField ℓ (s + D) n u) (siteAbove ℓ.side D n o) (ballRadius ℓ.side nn ρ₀ D + 1) +
      ({u | Clear T s m D n u o}.indicator fun u => widenedStageSum T s nn ρ₀ D n u o) u +
      ({u | Clear T s m D n u o}.indicator fun u => widenedStageMax s nn ρ₀ D n u o) u +
      (M : ℝ) * Real.exp (-(c * ρ₀)))))
      (markedSampleLaw T β (s + D) n) :=
    aemeasurable_const.min ((((hc.const_mul ρ₀).add hL).add hM).add_const _ |>.const_mul C₁)
  refine (hR0.aestronglyMeasurable.indicator₀ (clear_null S hs D hD n hn hLn o)).congr
    (Filter.Eventually.of_forall fun u => ?_)
  by_cases hu : u ∈ {u | Clear T s m D n u o}
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
    simp only [Set.indicator_of_mem hu]
    rfl
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
private theorem sum_geom_half (D : ℕ) : ∑ i ∈ Finset.range D, ((1 : ℝ) / 2) ^ i * 4 ≤ 8 := by
  have h : ∀ D : ℕ, ∑ i ∈ Finset.range D, ((1 : ℝ) / 2) ^ i * 4 = 8 - 8 * (1 / 2) ^ D := by
    intro D
    induction D with
    | zero => simp
    | succ D ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring
  rw [h]
  have : (0 : ℝ) ≤ (1 / 2) ^ D := by positivity
  linarith
abbrev _root_.YangMills.SharedProofs.p85945 := @sum_geom_half
private theorem top_maxCurv_le {T : StageTower ℓ} {s D n : ℕ} [NeZero n] {m σ' r : ℝ} {u : MarkedSample ℓ (s + D) n}
    {o : TorusSite (fineSide ℓ.side D n)} (hD : 1 ≤ D) (hσ : 0 ≤ σ') (hσ' : ℓ.threshold ≤ σ') (hr : r ≤ m)
    (hg : GoodAlong T s m D n u o) :
    maxCurvatureOnBall (topField ℓ (s + D) n u) (siteAbove ℓ.side D n o) r ≤ σ' := by
  cases D with
  | zero => omega
  | succ D =>
    refine finsetSup_le hσ fun p hp => ?_
    exact (hg.1 p (plaquettesIn_mono (supBall_mono _ hr) hp)).le.trans hσ'
variable {t d d' N : ℕ} {nn₁ e N₀ C₁ c : ℝ}
private theorem local_ae (S : ChainScene T β k H m side Rm B q) (ht : k ≤ t) (hH : t + d + d' ≤ H) [NeZero N]
    (hN : side ≤ N) (hLN : ℓ.side ∣ N) (hLd : ℓ.side ∣ fineSide ℓ.side d' N) (hbs : side ≤ fineSide ℓ.side d' N)
    (o : TorusSite (fineSide ℓ.side d (fineSide ℓ.side d' N))) :
    ∀ᵐ u ∂(markedSampleLaw T β (t + d + d') N),
      (IsLocalEventFrom T t d d' m N u o ↔
        Clear T (t + d) m d' N u (siteAbove ℓ.side d (fineSide ℓ.side d' N) o) ∧
          Clear T t m d (fineSide ℓ.side d' N) (sampleBelow ℓ (t + d) d' N u) o) ∧
      (Clear T (t + d) m d' N u (siteAbove ℓ.side d (fineSide ℓ.side d' N) o) →
        GoodAlong T (t + d) m d' N u (siteAbove ℓ.side d (fineSide ℓ.side d' N) o)) ∧
      (Clear T t m d (fineSide ℓ.side d' N) (sampleBelow ℓ (t + d) d' N u) o →
        GoodAlong T t m d (fineSide ℓ.side d' N) (sampleBelow ℓ (t + d) d' N u) o) := by
  have h1 := good_ae S (s := t + d) (by omega) d' hH N hN hLN (siteAbove ℓ.side d (fineSide ℓ.side d' N) o)
  have hmp : MeasurePreserving (sampleBelow ℓ (t + d) d' N) (markedSampleLaw T β (t + d + d') N)
      (markedSampleLaw T β (t + d) (fineSide ℓ.side d' N)) := ⟨measurable_sampleBelow ℓ _ d' N, S.below _ d' N⟩
  have h2 := hmp.quasiMeasurePreserving.ae (good_ae S (s := t) ht d (by omega) (fineSide ℓ.side d' N) hbs hLd o)
  filter_upwards [h1, h2] with u a1 a2
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => (a1 h).1, fun h => (a2 h).1⟩
  · obtain ⟨hd, hs1, hs2⟩ := h
    exact ⟨⟨hd, hs1⟩, (a1 ⟨hd, hs1⟩).2, hs2⟩
  · exact ⟨h.1.1, h.1.2, h.2.2⟩
private theorem local_null (S : ChainScene T β k H m side Rm B q) (ht : k ≤ t) (hH : t + d + d' ≤ H) [NeZero N]
    (hN : side ≤ N) (hLN : ℓ.side ∣ N) (hLd : ℓ.side ∣ fineSide ℓ.side d' N) (hbs : side ≤ fineSide ℓ.side d' N)
    (o : TorusSite (fineSide ℓ.side d (fineSide ℓ.side d' N))) :
    NullMeasurableSet {u | IsLocalEventFrom T t d d' m N u o} (markedSampleLaw T β (t + d + d') N) := by
  have hmp : MeasurePreserving (sampleBelow ℓ (t + d) d' N) (markedSampleLaw T β (t + d + d') N)
      (markedSampleLaw T β (t + d) (fineSide ℓ.side d' N)) := ⟨measurable_sampleBelow ℓ _ d' N, S.below _ d' N⟩
  have h1 := (clear_null S (s := t + d) (by omega) d' hH N hN hLN (siteAbove ℓ.side d (fineSide ℓ.side d' N) o)).inter
    ((clear_null S (s := t) ht d (by omega) (fineSide ℓ.side d' N) hbs hLd o).preimage hmp.quasiMeasurePreserving)
  refine NullMeasurableSet.congr h1 ?_
  filter_upwards [local_ae S ht hH hN hLN hLd hbs o] with u hu
  exact propext hu.1.symm
private theorem local_moments (S : ChainScene T β k H m side Rm B q) (ht : k ≤ t) (hH : t + d + d' ≤ H) [NeZero N]
    (hN : side ≤ N) (hLN : ℓ.side ∣ N) (hLd : ℓ.side ∣ fineSide ℓ.side d' N) (hbs : side ≤ fineSide ℓ.side d' N)
    (o : TorusSite (fineSide ℓ.side d (fineSide ℓ.side d' N)))
    (H₁ : StepsHalve T (t + d) nn₁ ρ₀ m e N₀ side d') (H₂ : StepsHalve T t nn ρ₀ m e N₀ side d)
    (hr : ballRadius ℓ.side nn₁ ρ₀ 0 = ballRadius ℓ.side nn ρ₀ d)
    (hrad₁ : ∀ D, (ballRadius ℓ.side nn₁ ρ₀ D + 1) / (ℓ.side : ℝ) + 2 ≤ Rm)
    (hrad₂ : ∀ D, (ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2 ≤ Rm)
    (he : 0 ≤ e) (hρ : 0 ≤ ρ₀) (hC₁ : 0 ≤ C₁) (M : ℕ) (hd' : 1 ≤ d') {σ' : ℝ} (hσ : 0 ≤ σ')
    (hσ' : ℓ.threshold ≤ σ') (hm : ballRadius ℓ.side nn₁ ρ₀ d' + 1 ≤ m) :
    InLp (markedSampleLaw T β (t + d + d') N) q ({u | IsLocalEventFrom T t d d' m N u o}.indicator fun u =>
        widenedChainSize T C₁ c M t nn ρ₀ d (fineSide ℓ.side d' N) (sampleBelow ℓ (t + d) d' N u) o)
      (C₁ * ((ρ₀ + 3) * ((1 / 2) ^ d' * σ' + 2 * e + 8 * B) + 13 * (d * B) + 3 * (d * e) +
        M * Real.exp (-(c * ρ₀)))) ∧
    InLp (markedSampleLaw T β (t + d + d') N) q ({u | IsLocalEventFrom T t d d' m N u o}.indicator fun u =>
        maxCurvatureOnBall (topField ℓ t _ (sampleBelow ℓ t d _ (sampleBelow ℓ (t + d) d' N u))) o
          (ballRadius ℓ.side nn ρ₀ 0))
      ((1 / 2) ^ d' * σ' + 2 * e + 8 * B + 8 * B + 2 * e) := by
  have hp : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast S.q_pos
  haveI := S.prob (t + d + d') N
  have hB0 := S.B_nonneg
  have hmp : MeasurePreserving (sampleBelow ℓ (t + d) d' N) (markedSampleLaw T β (t + d + d') N)
      (markedSampleLaw T β (t + d) (fineSide ℓ.side d' N)) := ⟨measurable_sampleBelow ℓ _ d' N, S.below _ d' N⟩
  have hG1 := (devSum_inLp S (s := t + d) (by omega) (w := fun i => (1 / 2) ^ i * 4) (fun i => by positivity) hrad₁ d'
    hH N hN hLN (siteAbove ℓ.side d (fineSide ℓ.side d' N) o)).le (mul_le_mul_of_nonneg_right (sum_geom_half d') hB0)
  have hG2 := ((devSum_inLp S (s := t) ht (w := fun i => (1 / 2) ^ i * 4) (fun i => by positivity) hrad₂ d (by omega)
    (fineSide ℓ.side d' N) hbs hLd o).le (mul_le_mul_of_nonneg_right (sum_geom_half d) hB0)).comp hmp
  have hP := (devSum_inLp S (s := t) ht (w := fun _ => 1) (fun _ => zero_le_one) hrad₂ d (by omega)
    (fineSide ℓ.side d' N) hbs hLd o).comp hmp
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hP
  have hχ := local_null S ht hH hN hLN hLd hbs o (m := m)
  set κ : ℝ := (1 / 2) ^ d' * σ' + 2 * e with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set G1 : MarkedSample ℓ (t + d + d') N → ℝ :=
    {u | Clear T (t + d) m d' N u (siteAbove ℓ.side d (fineSide ℓ.side d' N) o)}.indicator
      (fun u => devSum T (t + d) nn₁ ρ₀ (fun i => (1 / 2) ^ i * 4) d' N u
        (siteAbove ℓ.side d (fineSide ℓ.side d' N) o)) with hG1d
  set G2 : MarkedSample ℓ (t + d + d') N → ℝ := fun u =>
    ({v | Clear T t m d (fineSide ℓ.side d' N) v o}.indicator
      (fun v => devSum T t nn ρ₀ (fun i => (1 / 2) ^ i * 4) d (fineSide ℓ.side d' N) v o))
        (sampleBelow ℓ (t + d) d' N u) with hG2d
  set P : MarkedSample ℓ (t + d + d') N → ℝ := fun u =>
    ({v | Clear T t m d (fineSide ℓ.side d' N) v o}.indicator
      (fun v => devSum T t nn ρ₀ (fun _ => 1) d (fineSide ℓ.side d' N) v o)) (sampleBelow ℓ (t + d) d' N u) with hPd
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h8 : 0 ≤ 8 * B := by positivity
  have hdB : 0 ≤ (d : ℝ) * B := mul_nonneg hd0 hB0
  have hA : InLp (markedSampleLaw T β (t + d + d') N) q (fun u => κ + G1 u) (κ + 8 * B) :=
    InLp.add hp hκ0 h8 (InLp.const hκ0) hG1
  have hcore : ∀ᵐ u ∂(markedSampleLaw T β (t + d + d') N), IsLocalEventFrom T t d d' m N u o →
      maxCurvatureOnBall (topField ℓ (t + d) _ (sampleBelow ℓ (t + d) d' N u)) (siteAbove ℓ.side d (fineSide ℓ.side d' N) o)
          (ballRadius ℓ.side nn ρ₀ d + 1) ≤ κ + G1 u ∧
        GoodAlong T t m d (fineSide ℓ.side d' N) (sampleBelow ℓ (t + d) d' N u) o ∧
        sampleBelow ℓ (t + d) d' N u ∈ {v | Clear T t m d (fineSide ℓ.side d' N) v o} := by
    filter_upwards [local_ae S ht hH hN hLN hLd hbs o (m := m)] with u hu hloc
    obtain ⟨ev1, ev2⟩ := hu.1.1 hloc
    have g1 := hu.2.1 ev1
    have h1 := curvature_descends H₁ S.side_nonneg d' le_rfl N hN u (siteAbove ℓ.side d (fineSide ℓ.side d' N) o) g1
    rw [hr] at h1
    have htop := top_maxCurv_le hd' hσ hσ' hm g1
    have hG : G1 u = devSum T (t + d) nn₁ ρ₀ (fun i => (1 / 2) ^ i * 4) d' N u
        (siteAbove ℓ.side d (fineSide ℓ.side d' N) o) :=
      Set.indicator_of_mem
        (show u ∈ {u | Clear T (t + d) m d' N u (siteAbove ℓ.side d (fineSide ℓ.side d' N) o)} from ev1) _
    refine ⟨?_, hu.2.2 ev2, ev2⟩
    have hp0 : (0 : ℝ) ≤ (1 / 2) ^ d' := by positivity
    have := mul_le_mul_of_nonneg_left htop hp0
    have h3 : (2 - 2 * (1 / 2) ^ d') * e ≤ 2 * e := by nlinarith
    rw [hG, hκ]
    exact h1.trans (by linarith)
  constructor
  · have hR : InLp (markedSampleLaw T β (t + d + d') N) q
        (fun u => C₁ * ((ρ₀ + 3) * (κ + G1 u) + 13 * P u + (3 * (d * e) + M * Real.exp (-(c * ρ₀)))))
        (C₁ * ((ρ₀ + 3) * (κ + 8 * B) + 13 * (d * B) + (3 * (d * e) + M * Real.exp (-(c * ρ₀))))) := by
      have hc3 : 0 ≤ 3 * ((d : ℝ) * e) + M * Real.exp (-(c * ρ₀)) := by positivity
      exact InLp.smul hC₁ (by positivity)
        (InLp.add hp (by positivity) hc3 (InLp.add hp (by positivity) (by positivity)
          (InLp.smul (by positivity) (by positivity) hA) (InLp.smul (by norm_num) hdB hP)) (InLp.const hc3))
    have hI : AEStronglyMeasurable ({u | IsLocalEventFrom T t d d' m N u o}.indicator fun u =>
        widenedChainSize T C₁ c M t nn ρ₀ d (fineSide ℓ.side d' N) (sampleBelow ℓ (t + d) d' N u) o)
        (markedSampleLaw T β (t + d + d') N) := by
      have h0 := (chainSize_aesm (nn := nn) (ρ₀ := ρ₀) S ht C₁ c M hrad₂ d (by omega) (fineSide ℓ.side d' N) hbs hLd
        o).comp_measurePreserving hmp
      refine (h0.indicator₀ hχ).congr ?_
      filter_upwards [hcore] with u hu
      by_cases hl : u ∈ {u | IsLocalEventFrom T t d d' m N u o}
      · rw [Set.indicator_of_mem hl, Set.indicator_of_mem hl]
        exact Set.indicator_of_mem (s := {v | Clear T t m d (fineSide ℓ.side d' N) v o}) (hu hl).2.2 _
      · exact (Set.indicator_of_notMem hl _).trans (Set.indicator_of_notMem hl _).symm
    refine (hR.mono hI ?_).le (le_of_eq (by ring))
    filter_upwards [hcore] with u hu
    by_cases hl : u ∈ {u | IsLocalEventFrom T t d d' m N u o}
    · rw [Set.indicator_of_mem hl]
      obtain ⟨a1, a2, a3⟩ := hu hl
      have hs1 := stageSum_descends H₂ S.side_nonneg d le_rfl (fineSide ℓ.side d' N) hbs
        (sampleBelow ℓ (t + d) d' N u) o a2
      have hs2 := stageMax_descends H₂ S.side_nonneg he d le_rfl (fineSide ℓ.side d' N) hbs
        (sampleBelow ℓ (t + d) d' N u) o a2
      have hPu : P u = devSum T t nn ρ₀ (fun _ => 1) d (fineSide ℓ.side d' N) (sampleBelow ℓ (t + d) d' N u) o :=
        Set.indicator_of_mem (s := {v | Clear T t m d (fineSide ℓ.side d' N) v o}) a3 _
      have hcn := maxCurv_nonneg (topField ℓ (t + d) _ (sampleBelow ℓ (t + d) d' N u))
        (siteAbove ℓ.side d (fineSide ℓ.side d' N) o) (ballRadius ℓ.side nn ρ₀ d + 1)
      have hsz0 : 0 ≤ widenedChainSize T C₁ c M t nn ρ₀ d (fineSide ℓ.side d' N) (sampleBelow ℓ (t + d) d' N u) o := by
        refine le_min zero_le_one (mul_nonneg hC₁ ?_)
        have := stageSum_nonneg T t nn ρ₀ d (fineSide ℓ.side d' N) (sampleBelow ℓ (t + d) d' N u) o
        have := stageMax_nonneg t nn ρ₀ d (fineSide ℓ.side d' N) (sampleBelow ℓ (t + d) d' N u) o
        positivity
      rw [Real.norm_of_nonneg hsz0]
      refine le_trans ?_ (le_abs_self _)
      refine (min_le_right _ _).trans (mul_le_mul_of_nonneg_left ?_ hC₁)
      rw [← hPu] at hs1 hs2
      have hρc := mul_le_mul_of_nonneg_left a1 hρ
      nlinarith
    · rw [Set.indicator_of_notMem hl, norm_zero]
      exact norm_nonneg _
  · have hR := InLp.add hp (by positivity) (by positivity) (InLp.add hp (by positivity) h8 hA hG2)
      (InLp.const (c := 2 * e) (by positivity))
    have hI : AEStronglyMeasurable ({u | IsLocalEventFrom T t d d' m N u o}.indicator fun u =>
        maxCurvatureOnBall (topField ℓ t _ (sampleBelow ℓ t d _ (sampleBelow ℓ (t + d) d' N u))) o
          (ballRadius ℓ.side nn ρ₀ 0))
        (markedSampleLaw T β (t + d + d') N) := by
      have h0 : Measurable fun u : MarkedSample ℓ (t + d + d') N =>
          maxCurvatureOnBall (topField ℓ t _ (sampleBelow ℓ t d _ (sampleBelow ℓ (t + d) d' N u))) o
            (ballRadius ℓ.side nn ρ₀ 0) :=
        (measurable_maxCurv o _).comp ((measurable_topField' ℓ t _).comp
          ((measurable_sampleBelow ℓ t d _).comp (measurable_sampleBelow ℓ (t + d) d' N)))
      exact h0.aestronglyMeasurable.indicator₀ hχ
    refine hR.mono hI ?_
    filter_upwards [hcore] with u hu
    by_cases hl : u ∈ {u | IsLocalEventFrom T t d d' m N u o}
    · rw [Set.indicator_of_mem hl]
      obtain ⟨a1, a2, a3⟩ := hu hl
      have h1 := curvature_descends H₂ S.side_nonneg d le_rfl (fineSide ℓ.side d' N) hbs
        (sampleBelow ℓ (t + d) d' N u) o a2
      have hGu : G2 u = devSum T t nn ρ₀ (fun i => (1 / 2) ^ i * 4) d (fineSide ℓ.side d' N)
          (sampleBelow ℓ (t + d) d' N u) o :=
        Set.indicator_of_mem (s := {v | Clear T t m d (fineSide ℓ.side d' N) v o}) a3 _
      have hw := maxCurv_mono (topField ℓ t _ (sampleBelow ℓ t d _ (sampleBelow ℓ (t + d) d' N u))) o
        (r := ballRadius ℓ.side nn ρ₀ 0) (r' := ballRadius ℓ.side nn ρ₀ 0 + 1) (by linarith)
      rw [Real.norm_of_nonneg (maxCurv_nonneg _ _ _)]
      refine le_trans ?_ (le_abs_self _)
      refine hw.trans (h1.trans ?_)
      rw [← hGu]
      have hp0 : (0 : ℝ) ≤ (1 / 2) ^ d := by positivity
      have hp1 : ((1 : ℝ) / 2) ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hcn := maxCurv_nonneg (topField ℓ (t + d) _ (sampleBelow ℓ (t + d) d' N u))
        (siteAbove ℓ.side d (fineSide ℓ.side d' N) o) (ballRadius ℓ.side nn ρ₀ d + 1)
      have h5 : ((1 : ℝ) / 2) ^ d * maxCurvatureOnBall (topField ℓ (t + d) _ (sampleBelow ℓ (t + d) d' N u))
          (siteAbove ℓ.side d (fineSide ℓ.side d' N) o) (ballRadius ℓ.side nn ρ₀ d + 1) ≤ κ + G1 u := by
        refine le_trans ?_ a1
        nlinarith
      have h6 : (2 - 2 * ((1 : ℝ) / 2) ^ d) * e ≤ 2 * e := by nlinarith
      linarith
    · rw [Set.indicator_of_notMem hl, norm_zero]
      exact norm_nonneg _
end Bounds
section Table
open scoped ENNReal
private theorem measurableSet_sigma_fst {ι : Type} {X : ι → Type} [∀ i, MeasurableSpace (X i)] (P : ι → Prop) :
    MeasurableSet {p : Σ i, X i | P p.1} := by
  classical
  show MeasurableSet[⨅ a, (inferInstance : MeasurableSpace (X a)).map (Sigma.mk a)] _
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  show MeasurableSet (Sigma.mk a ⁻¹' _)
  by_cases h : P a
  · have : (Sigma.mk a ⁻¹' {p : Σ i, X i | P p.1}) = Set.univ := by
      ext v
      simpa using h
    rw [this]
    exact MeasurableSet.univ
  · have : (Sigma.mk a ⁻¹' {p : Σ i, X i | P p.1}) = ∅ := by
      ext v
      simpa using h
    rw [this]
    exact MeasurableSet.empty
private theorem card_chartBondsInBlocks {L n : ℕ} [NeZero L] [NeZero n] (o : TorusSite n) {R : ℝ} (hR : 0 ≤ R) :
    ((chartBondsInBlocks L (supBall o R)).card : ℝ) ≤ 4 * (2 * R + 1) ^ 4 * (2 * (L : ℝ) + 1) ^ 4 := by
  classical
  set r := ⌊R⌋₊ with hr
  have hbox : (supBall o R).card ≤ (2 * r + 1) ^ 4 := by
    refine (Finset.card_le_card ?_).trans (TorusCounting.card_thickening_singleton_le r o)
    intro z hz
    refine (mem_thickening _ _ _).2 ⟨o, by simp, ?_⟩
    exact Nat.le_floor (mem_supBall_iff.1 hz)
  have hblocks : (sitesInBlocks L (supBall o R)).card ≤ (supBall o R).card * (2 * L + 1) ^ 4 := by
    have hsub : sitesInBlocks L (supBall o R) ⊆ (supBall o R).biUnion fun Y => sitesInBlocks L {Y} := by
      intro x hx
      have : parentBlock L x ∈ supBall o R := by simpa [sitesInBlocks] using hx
      exact Finset.mem_biUnion.mpr ⟨_, this, by simp [sitesInBlocks]⟩
    exact (Finset.card_le_card hsub).trans
      (Finset.card_biUnion_le_card_mul _ _ _ fun Y _ => TorusCounting.card_sitesInBlocks_singleton_le Y)
  have hbonds : (chartBondsInBlocks L (supBall o R)).card ≤ (sitesInBlocks L (supBall o R)).card * 4 := by
    have hsub : chartBondsInBlocks L (supBall o R) ⊆
        (sitesInBlocks L (supBall o R)) ×ˢ (Finset.univ : Finset (Fin 4)) := by
      intro b hb
      simp only [chartBondsInBlocks, Finset.mem_filter] at hb
      exact Finset.mem_product.mpr ⟨by simpa [sitesInBlocks] using hb.2, Finset.mem_univ _⟩
    refine (Finset.card_le_card hsub).trans ?_
    simp
  have hfin : (chartBondsInBlocks L (supBall o R)).card ≤ (2 * r + 1) ^ 4 * (2 * L + 1) ^ 4 * 4 :=
    hbonds.trans (Nat.mul_le_mul_right _ (hblocks.trans (Nat.mul_le_mul_right _ hbox)))
  have hcast : ((chartBondsInBlocks L (supBall o R)).card : ℝ) ≤
      (2 * (r : ℝ) + 1) ^ 4 * (2 * (L : ℝ) + 1) ^ 4 * 4 := by
    exact_mod_cast hfin
  have hr' : (r : ℝ) ≤ R := Nat.floor_le hR
  have h1 : (2 * (r : ℝ) + 1) ^ 4 ≤ (2 * R + 1) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 4
  have h2 : (0 : ℝ) ≤ (2 * (L : ℝ) + 1) ^ 4 := by positivity
  nlinarith
abbrev _root_.YangMills.SharedProofs.p5403 := @card_chartBondsInBlocks
private theorem ballRadius_shift (L : ℕ) (hL : 0 < L) (nn ρ₀ : ℝ) (a D : ℕ) :
    ballRadius L (nn / (L : ℝ) ^ a) ρ₀ D = ballRadius L nn ρ₀ (a + D) := by
  unfold ballRadius
  rw [pow_add]
  field_simp
abbrev _root_.YangMills.SharedProofs.p21218 := @ballRadius_shift
private theorem ballRadius_le (L : ℕ) (hL : 0 < L) {nn ρ₀ : ℝ} (hnn : 0 ≤ nn) (D : ℕ) :
    ballRadius L nn ρ₀ D ≤ 20 * nn + 4 * ρ₀ := by
  have h1 : (1 : ℝ) ≤ (L : ℝ) ^ D := one_le_pow₀ (by exact_mod_cast hL)
  have : 20 * nn / (L : ℝ) ^ D ≤ 20 * nn := div_le_self (by positivity) h1
  unfold ballRadius
  linarith
abbrev _root_.YangMills.SharedProofs.p10514 := @ballRadius_le
private theorem holdsOnParameters_and3 {P₁ P₂ P₃ Q : ParameterAssignment → ℝ → Prop} (h₁ : HoldsOnParameterFamilies P₁)
    (h₂ : HoldsOnParameterFamilies P₂) (h₃ : HoldsOnParameterFamilies P₃)
    (hQ : ∀ Tb y, Tb.Admissible → Tb.floorMin ≤ y → P₁ Tb y → P₂ Tb y → P₃ Tb y → Q Tb y) :
    HoldsOnParameterFamilies Q := by
  intro a ha
  obtain ⟨L₁, r₁, c₁, hr₁, h₁⟩ := h₁ a ha
  obtain ⟨L₂, r₂, c₂, hr₂, h₂⟩ := h₂ a ha
  obtain ⟨L₃, r₃, c₃, hr₃, h₃⟩ := h₃ a ha
  refine ⟨max L₁ (max L₂ L₃), fun c => min (r₁ c) (min (r₂ c) (r₃ c)), max c₁ (max c₂ c₃),
    fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (hr₃ c)), fun L hodd hL T hTa hTL hD hS hH hrt hC => ?_⟩
  obtain ⟨y₁, p₁⟩ := h₁ L hodd ((le_max_left _ _).trans hL) T hTa hTL hD hS hH (hrt.trans (min_le_left _ _))
    ((le_max_left _ _).trans hC)
  obtain ⟨y₂, p₂⟩ := h₂ L hodd (((le_max_left _ _).trans (le_max_right _ _)).trans hL) T hTa hTL hD hS hH
    (hrt.trans ((min_le_right _ _).trans (min_le_left _ _))) (((le_max_left _ _).trans (le_max_right _ _)).trans hC)
  obtain ⟨y₃, p₃⟩ := h₃ L hodd (((le_max_right _ _).trans (le_max_right _ _)).trans hL) T hTa hTL hD hS hH
    (hrt.trans ((min_le_right _ _).trans (min_le_right _ _))) (((le_max_right _ _).trans (le_max_right _ _)).trans hC)
  refine ⟨max T.floorMin (max y₁ (max y₂ y₃)), fun y hy hRow hW => ?_⟩
  have e₀ : T.floorMin ≤ y := (le_max_left _ _).trans hy
  have e₁ : y₁ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have e₂ : y₂ ≤ y := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have e₃ : y₃ ≤ y := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  exact hQ T y hD e₀ (p₁ y e₁ hRow fun β hβ => hW β hβ) (p₂ y e₂ hRow fun β hβ => hW β hβ)
    (p₃ y e₃ hRow fun β hβ => hW β hβ)
abbrev _root_.YangMills.SharedProofs.p71980 := @holdsOnParameters_and3
variable {Tb : ParameterAssignment} {y : ℝ}
private theorem localChain_at {T : StageTower (Tb.stepParameters y)} {β : ℝ} {k N n : ℕ} {nn x₀ x₁ : ℝ}
    (h : IsLocalChainAbove Tb y T β k N nn x₀) (hx : x₁ ≤ x₀)
    (hn : 2 ^ 10 * localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1 ≤ (n : ℝ)) :
    IsLocalChainAbove Tb y T β k n nn x₁ :=
  ⟨hx.trans h.floor_le, h.coupling_ge, h.onFamily, h.cutoff, h.measurable, hn, h.one_le, h.le_rpow⟩
private theorem scene_exists (hfit : (Tb.stepParameters y).Admissible)
    (hLgt : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side)
    (hDraw : BoxMarks.lowerMarginalStatement) (hTP : TwoPointByTotalCovarianceStatement)
    (hM : stepDeviationMomentsAt Tb y) (hO : descentKeepsBallClearAt Tb y) {q : ℕ} (hq1 : 1 ≤ q) :
    ∃ Cb xs : ℝ, 0 ≤ Cb ∧ ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k N : ℕ) [NeZero N] (nn : ℝ),
      IsLocalChainAbove Tb y T β k N nn xs → 0 ≤ flowCouplings (Tb.stepParameters y) β k →
      4 * (2 * ((localBlockSide (Tb.stepParameters y) β k : ℝ) / 8) + 1) ^ 4 *
          (2 * ((Tb.stepParameters y).side : ℝ) + 1) ^ 4 ≤
        flowCouplings (Tb.stepParameters y) β k →
      ChainScene T β k (k + 2 * localChainDepth (Tb.stepParameters y) β k) (localBlockSide (Tb.stepParameters y) β k)
        (2 ^ 10 * (localBlockSide (Tb.stepParameters y) β k : ℝ)) ((localBlockSide (Tb.stepParameters y) β k : ℝ) / 8)
        (Cb * flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ) + 1 / 1000)) q := by
  obtain ⟨Cq, xq, hq⟩ := hM q
  obtain ⟨C1, x1, h1⟩ := hM 1
  obtain ⟨C0, x0, h0⟩ := hM 0
  obtain ⟨xd, hdn⟩ := hO
  refine ⟨|Cq|, max xq (max x1 (max x0 xd)), abs_nonneg _, fun T β k N _ nn hloc hx0 hcard => ?_⟩
  have hcut := hloc.cutoff
  have hcoin := hloc.measurable
  have hlaw := fun (h n : ℕ) [NeZero n] => hTP (Tb.stepParameters y) hfit hLgt T hcut hcoin β (fun _ => 0) h n
  set x := flowCouplings (Tb.stepParameters y) β k with hx
  set m : ℝ := (localBlockSide (Tb.stepParameters y) β k : ℝ) with hm
  have hX : 0 ≤ x ^ (-(1 / 2 : ℝ) + 1 / 1000) := Real.rpow_nonneg hx0 _
  have hlq : xq ≤ max xq (max x1 (max x0 xd)) := le_max_left _ _
  have hl1 : x1 ≤ max xq (max x1 (max x0 xd)) := (le_max_left _ _).trans (le_max_right _ _)
  have hl0 : x0 ≤ max xq (max x1 (max x0 xd)) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hld : xd ≤ max xq (max x1 (max x0 xd)) :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  refine ⟨hq1, mul_nonneg (abs_nonneg _) hX, by positivity, fun h n _ => (hlaw h n).1,
    fun s D n _ => hDraw (Tb.stepParameters y) hfit hLgt T hcut hcoin β s D n, ?_, ?_, ?_, ?_⟩
  · intro h n _ S
    refine (hlaw h n).2.1 _ ⟨{st | Disjoint st.2.1 S}, ?_, rfl⟩
    exact measurable_snd (measurableSet_sigma_fst fun Y : Finset (TorusSite n) => Disjoint Y S)
  · intro h hk hH n _ hn hLn o
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    refine (hdn T β k n nn j o (localChain_at hloc hld hn) hLn (by omega)).mono fun u hu hdis => ?_
    refine ⟨(hu hdis).1, fun hs => ⟨((hu hdis).2 hs).1, fun b hb => (((hu hdis).2 hs).2 b hb).2⟩⟩
  · intro h hk hH n _ hn hLn o
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    have h2 := (h0 T β k n nn j o ∅ (localChain_at hloc hl0 hn) hLn (by omega) (by simp) (by simpa using hx0)).2.1
    have h3 : AEMeasurable ((TopClear T (k + j) m o).indicator fun _ => (1 : ℝ)) (markedSampleLaw T β (k + j + 1) n) := by
      have h4 := h2.aestronglyMeasurable.aemeasurable
      simp only [pow_zero] at h4
      exact h4
    exact (aemeasurable_indicator_const_iff 1).1 h3
  · intro h hk hH n _ hn hLn o R hR
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hsub : chartBondsInBlocks (Tb.stepParameters y).side (supBall o R) ⊆
        chartBondsInBlocks (Tb.stepParameters y).side (supBall o (m / 8)) := by
      intro b hb
      simp only [chartBondsInBlocks, Finset.mem_filter] at hb ⊢
      exact ⟨hb.1, supBall_mono o hR hb.2⟩
    have hcardZ : ((chartBondsInBlocks (Tb.stepParameters y).side (supBall o R)).card : ℝ) ≤ x := by
      have h4 : ((chartBondsInBlocks (Tb.stepParameters y).side (supBall o R)).card : ℝ) ≤
          ((chartBondsInBlocks (Tb.stepParameters y).side (supBall o (m / 8))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      exact h4.trans ((card_chartBondsInBlocks o (by positivity)).trans hcard)
    have A1 := h1 T β k n nn j o _ (localChain_at hloc hl1 hn) hLn (by omega) hsub hcardZ
    have Aq := hq T β k n nn j o _ (localChain_at hloc hlq hn) hLn (by omega) hsub hcardZ
    have hmeas : AEStronglyMeasurable ((TopClear T (k + j) m o).indicator fun u =>
        maxDeviationOnBall T (k + j) u.2.2.1
          (topField (Tb.stepParameters y) (k + j) (n * (Tb.stepParameters y).side) u.1) o R)
        (markedSampleLaw T β (k + j + 1) n) := by
      have h4 := A1.2.1.aestronglyMeasurable
      simp only [pow_one] at h4
      exact h4
    have hint : Integrable ((TopClear T (k + j) m o).indicator fun u =>
        maxDeviationOnBall T (k + j) u.2.2.1
          (topField (Tb.stepParameters y) (k + j) (n * (Tb.stepParameters y).side) u.1) o R ^ q)
        (markedSampleLaw T β (k + j + 1) n) := Aq.2.1
    have hpow : (fun u => ((TopClear T (k + j) m o).indicator (fun u =>
        maxDeviationOnBall T (k + j) u.2.2.1
          (topField (Tb.stepParameters y) (k + j) (n * (Tb.stepParameters y).side) u.1) o R) u) ^ q) =
        (TopClear T (k + j) m o).indicator fun u =>
          maxDeviationOnBall T (k + j) u.2.2.1
            (topField (Tb.stepParameters y) (k + j) (n * (Tb.stepParameters y).side) u.1) o R ^ q := by
      funext u
      by_cases hu : u ∈ TopClear T (k + j) m o
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
        exact zero_pow (by omega)
    haveI := (hlaw (k + j + 1) n).1
    refine inLp_of_moment (fun u => Set.indicator_nonneg (fun _ _ => maxDev_nonneg _ _ _ _ _ _) u) hmeas hq1
      (by rw [hpow]; exact hint) (mul_nonneg (abs_nonneg _) hX) ?_
    rw [hpow]
    refine integral_le_of_condExp (hlaw (k + j + 1) n).2.1
      (D := {u | Disjoint (stageState T (k + j + 1) n u).2.1 (supBall o m)}) ?_ hint ?_ (by positivity) ?_
    · exact ⟨{st | Disjoint st.2.1 (supBall o m)}, measurable_snd (measurableSet_sigma_fst
        fun Y : Finset (TorusSite n) => Disjoint Y (supBall o m)), rfl⟩
    · intro u hu
      exact Set.indicator_of_notMem (fun h => hu h.1) _
    · filter_upwards [Aq.2.2] with u hu hD
      refine (hu hD).2.trans ?_
      refine (le_abs_self _).trans (le_of_eq ?_)
      rw [abs_pow, abs_mul, abs_of_nonneg hX]
end Table
section Main
open scoped ENNReal
variable {Tb : ParameterAssignment} {y : ℝ}
private theorem chainSize_nonneg {ℓ : TorusLumps.StepParameters} (T : StageTower ℓ) {C₁ ρ₀ : ℝ} (hC₁ : 0 ≤ C₁)
    (hρ : 0 ≤ ρ₀) (c : ℝ) (M t : ℕ) (nn : ℝ)
    (d n : ℕ) [NeZero n] (u : MarkedSample ℓ (t + d) n) (o : TorusSite (fineSide ℓ.side d n)) :
    0 ≤ widenedChainSize T C₁ c M t nn ρ₀ d n u o := by
  refine le_min zero_le_one (mul_nonneg hC₁ ?_)
  have h1 := stageSum_nonneg T t nn ρ₀ d n u o
  have h2 := stageMax_nonneg t nn ρ₀ d n u o
  have h3 := maxCurv_nonneg (topField ℓ (t + d) n u) (siteAbove ℓ.side d n o) (ballRadius ℓ.side nn ρ₀ d + 1)
  positivity
private theorem indicator_moment {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {A : Set Ω} {f : Ω → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) {q : ℕ} (hq : 1 ≤ q) {B : ℝ} (hB : 0 ≤ B) (h : InLp μ q (A.indicator f) B) :
    Integrable (A.indicator fun x => f x ^ q) μ ∧ ∫ x, A.indicator (fun x => f x ^ q) x ∂μ ≤ B ^ q := by
  have hpow : (fun x => (A.indicator f x) ^ q) = A.indicator fun x => f x ^ q := by
    funext u
    by_cases hu : u ∈ A
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
      exact zero_pow (by omega)
  have := moment_of_inLp (fun x => Set.indicator_nonneg (fun x _ => hf0 x) x) hq hB h
  rwa [hpow] at this
set_option maxHeartbeats 1600000 in
private theorem bounds_at (hAx : axialGaugeNearOneStatement) (hFl : localChainFloorsStatement)
    (hDraw : BoxMarks.lowerMarginalStatement) (hTP : TwoPointByTotalCovarianceStatement)
    (hD : Tb.Admissible) (hy : Tb.floorMin ≤ y) (hC : curvatureHalvesAt Tb y) (hM : stepDeviationMomentsAt Tb y)
    (hO : descentKeepsBallClearAt Tb y) :
    ∃ C₁ c : ℝ, 0 < C₁ ∧ 0 < c ∧ ∀ q : ℕ, 1 ≤ q → ∃ Cq x₀ : ℝ, 0 ≤ Cq ∧
      ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k N : ℕ) [NeZero N] (nn : ℝ) (t d : ℕ)
        (o : TorusSite (fineSide (Tb.stepParameters y).side d
          (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N))),
        IsLocalChainAbove Tb y T β k N nn x₀ → (Tb.stepParameters y).side ∣ N → k ≤ t →
        t + d = k + localChainDepth (Tb.stepParameters y) β k →
        0 ≤ flowCouplings (Tb.stepParameters y) β k ∧
        (∀ s : ℝ, s < 1 → ∀ᵐ u ∂(markedSampleLaw T β (t + d + localChainDepth (Tb.stepParameters y) β k) N),
          IsLocalEventFrom T t d (localChainDepth (Tb.stepParameters y) β k) (localBlockSide (Tb.stepParameters y) β k)
            N u o →
          widenedChainSize T C₁ c (localChainDepth (Tb.stepParameters y) β k) t
              (nn / ((Tb.stepParameters y).side : ℝ) ^ (t - k))
              (localLogScale (Tb.stepParameters y) β k) d
              (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)
              (sampleBelow (Tb.stepParameters y) (t + d) (localChainDepth (Tb.stepParameters y) β k) N u) o ≤ s →
          IsGaugeSmallAlong T t (nn / ((Tb.stepParameters y).side : ℝ) ^ (t - k)) (localLogScale (Tb.stepParameters y) β k)
            s d
            (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)
            (sampleBelow (Tb.stepParameters y) (t + d) (localChainDepth (Tb.stepParameters y) β k) N u) o
            (axialGaugeAt (Tb.stepParameters y) (topField (Tb.stepParameters y) (t + d)
                (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)
                (sampleBelow (Tb.stepParameters y) (t + d) (localChainDepth (Tb.stepParameters y) β k) N u))
              (siteAbove (Tb.stepParameters y).side d
                (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) o))) ∧
        NullMeasurableSet {u | IsLocalEventFrom T t d (localChainDepth (Tb.stepParameters y) β k)
            (localBlockSide (Tb.stepParameters y) β k) N u o}
          (markedSampleLaw T β (t + d + localChainDepth (Tb.stepParameters y) β k) N) ∧
        IsProbabilityMeasure (markedSampleLaw T β (t + d + localChainDepth (Tb.stepParameters y) β k) N) ∧
        InLp (markedSampleLaw T β (t + d + localChainDepth (Tb.stepParameters y) β k) N) q
          ({u | IsLocalEventFrom T t d (localChainDepth (Tb.stepParameters y) β k)
              (localBlockSide (Tb.stepParameters y) β k) N u o}.indicator fun u =>
            widenedChainSize T C₁ c (localChainDepth (Tb.stepParameters y) β k) t
              (nn / ((Tb.stepParameters y).side : ℝ) ^ (t - k))
              (localLogScale (Tb.stepParameters y) β k) d
              (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)
              (sampleBelow (Tb.stepParameters y) (t + d) (localChainDepth (Tb.stepParameters y) β k) N u) o)
          (Cq * flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ) + 2 / 1000)) ∧
        InLp (markedSampleLaw T β (t + d + localChainDepth (Tb.stepParameters y) β k) N) q
          ({u | IsLocalEventFrom T t d (localChainDepth (Tb.stepParameters y) β k)
              (localBlockSide (Tb.stepParameters y) β k) N u o}.indicator fun u =>
            maxCurvatureOnBall (topField (Tb.stepParameters y) t _ (sampleBelow (Tb.stepParameters y) t d _
              (sampleBelow (Tb.stepParameters y) (t + d) (localChainDepth (Tb.stepParameters y) β k) N u))) o
              (ballRadius (Tb.stepParameters y).side (nn / ((Tb.stepParameters y).side : ℝ) ^ (t - k))
                (localLogScale (Tb.stepParameters y) β k) 0))
          (Cq * flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ) + 1 / 1000)) := by
  obtain ⟨C, N₀, c, xc, hc, hcurv⟩ := hC
  have hfit := hD.fits y hy
  have hLgt : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side := hD.L_gt
  have hodd : Odd (Tb.stepParameters y).side := hD.L_odd
  have hσ : 0 < (Tb.stepParameters y).threshold := hD.σ_pos
  have hLbig : 2 ^ 40 ≤ (Tb.stepParameters y).side := hD.L_ge
  have hLpos : 0 < (Tb.stepParameters y).side := by omega
  have hL2 : (2 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) := by
    have : 2 ≤ (Tb.stepParameters y).side := by omega
    exact_mod_cast this
  have hNb1 : 1 ≤ max N₀ 1 := le_max_right _ _
  have hCe1 : 1 ≤ max C 1 := le_max_right _ _
  have hC₁ : 0 < 36 + 2 * max N₀ 1 + 2 * max C 1 := by positivity
  refine ⟨36 + 2 * max N₀ 1 + 2 * max C 1, c, hC₁, hc, fun q hq => ?_⟩
  obtain ⟨Cb, xs, hCb, hsc⟩ := scene_exists hfit hLgt hDraw hTP hM hO hq
  have hKnn : 0 ≤ (Tb.stepParameters y).threshold + 5 * max C 1 + 1 +
      4 * (2 * ((Tb.stepParameters y).side : ℝ) + 1) ^ 4 := by positivity
  obtain ⟨X₀, hX⟩ := Filter.eventually_atTop.1 (hFl _ c hKnn hc)
  refine ⟨(36 + 2 * max N₀ 1 + 2 * max C 1) * (1 + 21 * Cb) + 2 + 16 * Cb, max (max X₀ xs) xc, by positivity,
    fun T β k N _ nn t d o hloc hLN hkt htd => ?_⟩
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hkt
  simp only [Nat.add_sub_cancel_left]
  have hfl : max (max X₀ xs) xc ≤ flowCouplings (Tb.stepParameters y) β k := hloc.floor_le
  have hX₀x : X₀ ≤ flowCouplings (Tb.stepParameters y) β k := ((le_max_left _ _).trans (le_max_left _ _)).trans hfl
  have hxsx : xs ≤ max (max X₀ xs) xc := (le_max_right _ _).trans (le_max_left _ _)
  have hxcx : xc ≤ max (max X₀ xs) xc := le_max_right _ _
  have F := hX _ hX₀x
  set x := flowCouplings (Tb.stepParameters y) β k with hxdef
  set ρ₀ := localLogScale (Tb.stepParameters y) β k with hρdef
  set m : ℝ := (localBlockSide (Tb.stepParameters y) β k : ℝ) with hmdef
  set L : ℝ := ((Tb.stepParameters y).side : ℝ) with hLdef
  set Nb := max N₀ 1 with hNbdef
  set Ce := max C 1 with hCedef
  set C₁ := 36 + 2 * Nb + 2 * Ce with hC₁def
  have hx1 : 1 ≤ x := F.one_le
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hρ1 : 1 ≤ ρ₀ := F.one_le_scale
  have hρ0 : 0 ≤ ρ₀ := by linarith
  have hM1 : 1 ≤ (localChainDepth (Tb.stepParameters y) β k) := F.one_le_depth
  have hrad0 : 20 * x ^ ((1 : ℝ) / 90) + 4 * ρ₀ + 4 ≤ m / 8 := F.radii_le
  have hnn1 : 1 ≤ nn := hloc.one_le
  have hnnx : nn ≤ x ^ ((1 : ℝ) / 90) := hloc.le_rpow
  have hp90 : 0 ≤ x ^ ((1 : ℝ) / 90) := Real.rpow_nonneg hx0 _
  have hm32 : 32 ≤ m := by linarith
  have hmx : m ≤ x ^ ((1 : ℝ) / 20) := Nat.floor_le (Real.rpow_nonneg hx0 _)
  have hside : 2 ^ 10 * m ≤ (N : ℝ) := hloc.side_ge
  have hcardF : 4 * (2 * (m / 8) + 1) ^ 4 * (2 * L + 1) ^ 4 ≤ x := by
    have h1 : 2 * (m / 8) + 1 ≤ x ^ ((1 : ℝ) / 20) := by linarith
    have h2 : (2 * (m / 8) + 1) ^ 4 ≤ x ^ ((1 : ℝ) / 5) := by
      have h3 := pow_le_pow_left₀ (by positivity) h1 4
      refine h3.trans (le_of_eq ?_)
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
      norm_num
    have h4 : 0 ≤ (2 * L + 1) ^ 4 := by positivity
    have hp5 : 0 ≤ x ^ ((1 : ℝ) / 5) := Real.rpow_nonneg hx0 _
    have h5 := F.card_le
    have hσC : 0 ≤ (Tb.stepParameters y).threshold + 5 * Ce + 1 := by positivity
    have h6 : 4 * (2 * L + 1) ^ 4 * x ^ ((1 : ℝ) / 5) ≤
        ((Tb.stepParameters y).threshold + 5 * Ce + 1 + 4 * (2 * L + 1) ^ 4) * x ^ ((1 : ℝ) / 5) :=
      mul_le_mul_of_nonneg_right (by linarith) hp5
    have h7 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 4 * (2 * L + 1) ^ 4)
    have h8 : 4 * (2 * (m / 8) + 1) ^ 4 * (2 * L + 1) ^ 4 = 4 * (2 * L + 1) ^ 4 * (2 * (m / 8) + 1) ^ 4 := by ring
    linarith
  have S := hsc T β k N nn (localChain_at hloc hxsx hloc.side_ge) hx0 hcardF
  set E := Real.exp (-(c * ρ₀)) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set e := Ce * E with hedef
  have he0 : 0 ≤ e := by positivity
  have hF : ∀ a' A : ℕ, a' + A ≤ 2 * (localChainDepth (Tb.stepParameters y) β k) →
      StepsHalve T (k + a') (nn / L ^ a') ρ₀ m e Nb (2 ^ 10 * m) A := by
    intro a' A hA
    refine ⟨fun D hD n _ hn o' V hcold b hb hsub => ?_, fun D hD n _ hn o' V hcold W o'' ho hη => ?_⟩
    · have hch := (hcurv T β k n nn (a' + D) o' V (localChain_at hloc hxcx hn) (by omega) hcold).1 b hb
        (by rw [hLdef, ballRadius_shift _ hLpos] at hsub; exact hsub)
      rw [hLdef, ballRadius_shift _ hLpos, Nat.add_assoc k a' D]
      exact hch.trans (add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (maxCurv_nonneg _ _ _))
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hE0))
    · rw [Nat.add_assoc k a' D] at hη
      have hch := (hcurv T β k n nn (a' + D) o' V (localChain_at hloc hxcx hn) (by omega) hcold).2 W o'' ho hη 1
        zero_le_one le_rfl
      rw [hLdef, ballRadius_shift _ hLpos, ballRadius_shift _ hLpos, Nat.add_assoc k a' D]
      exact hch.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_max_left _ _) hE0))
  have hbsN : (N : ℝ) ≤ (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N : ℝ) := by
    rw [fineSide_eq]
    push_cast
    have h1 : (1 : ℝ) ≤ L ^ (localChainDepth (Tb.stepParameters y) β k) := one_le_pow₀ (by linarith)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    exact le_mul_of_one_le_right hN0 h1
  have hbs : 2 ^ 10 * m ≤ (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N : ℝ) :=
    hside.trans hbsN
  have hLd : (Tb.stepParameters y).side ∣
      fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N := by
    rw [fineSide_eq]
    exact Dvd.dvd.mul_right hLN _
  have hadM : a + d = (localChainDepth (Tb.stepParameters y) β k) := by omega
  have hkt' : k ≤ k + a := by omega
  have hH : k + a + d + (localChainDepth (Tb.stepParameters y) β k) ≤
      k + 2 * (localChainDepth (Tb.stepParameters y) β k) := by omega
  have hradall : ∀ a' D : ℕ, (ballRadius (Tb.stepParameters y).side (nn / L ^ a') ρ₀ D + 1) / L + 2 ≤ m / 8 := by
    intro a' D
    rw [hLdef, ballRadius_shift _ hLpos]
    have h1 := ballRadius_le (Tb.stepParameters y).side hLpos (nn := nn) (ρ₀ := ρ₀) (by linarith) (a' + D)
    have h2 : 0 ≤ ballRadius (Tb.stepParameters y).side nn ρ₀ (a' + D) := by
      unfold ballRadius
      positivity
    have h3 : (ballRadius (Tb.stepParameters y).side nn ρ₀ (a' + D) + 1) / ((Tb.stepParameters y).side : ℝ) ≤
        ballRadius (Tb.stepParameters y).side nn ρ₀ (a' + D) + 1 := div_le_self (by linarith) (by linarith)
    linarith
  have H₂ := hF a d (by omega)
  have H₁ : StepsHalve T (k + a + d) (nn / L ^ (a + d)) ρ₀ m e Nb (2 ^ 10 * m)
      (localChainDepth (Tb.stepParameters y) β k) := by
    have := hF (a + d) (localChainDepth (Tb.stepParameters y) β k) (by omega)
    rwa [← Nat.add_assoc k a d] at this
  have hr : ballRadius (Tb.stepParameters y).side (nn / L ^ (a + d)) ρ₀ 0 =
      ballRadius (Tb.stepParameters y).side (nn / L ^ a) ρ₀ d := by
    rw [hLdef, ballRadius_shift _ hLpos, ballRadius_shift _ hLpos]
    rfl
  have hmtop : ballRadius (Tb.stepParameters y).side (nn / L ^ (a + d)) ρ₀ (localChainDepth (Tb.stepParameters y) β k) + 1
      ≤ m := by
    rw [hLdef, ballRadius_shift _ hLpos]
    have h1 := ballRadius_le (Tb.stepParameters y).side hLpos (nn := nn) (ρ₀ := ρ₀) (by linarith)
      (a + d + (localChainDepth (Tb.stepParameters y) β k))
    linarith
  have hmain := local_moments (t := k + a) (d := d) (d' := (localChainDepth (Tb.stepParameters y) β k)) (N := N)
    (nn := nn / L ^ a) (nn₁ := nn / L ^ (a + d))
    (e := e) (N₀ := Nb) (C₁ := C₁) (c := c) S hkt' hH hside hLN hLd hbs o H₁ H₂ hr (hradall _) (hradall _) he0 hρ0
    hC₁.le (localChainDepth (Tb.stepParameters y) β k) hM1 hσ.le le_rfl hmtop
  have hX1 : 0 ≤ x ^ (-(1 / 2 : ℝ) + 1 / 1000) := Real.rpow_nonneg hx0 _
  have hX2 : 0 ≤ x ^ (-(1 / 2 : ℝ) + 2 / 1000) := Real.rpow_nonneg hx0 _
  have hXX : x ^ (-(1 / 2 : ℝ) + 2 / 1000) = x ^ ((1 : ℝ) / 1000) * x ^ (-(1 / 2 : ℝ) + 1 / 1000) := by
    rw [← Real.rpow_add hxpos]
    norm_num
  have hxm1 : 0 ≤ x ^ (-1 : ℝ) := Real.rpow_nonneg hx0 _
  have hxm2 : x ^ (-2 : ℝ) ≤ x ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hhalf : ((1 : ℝ) / 2) ^ (localChainDepth (Tb.stepParameters y) β k) ≤ x ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one, one_div, inv_pow]
    exact inv_anti₀ hxpos F.le_two_pow_depth
  have hEx : E ≤ x ^ (-2 : ℝ) := F.exp_le
  have hκ : ((1 : ℝ) / 2) ^ (localChainDepth (Tb.stepParameters y) β k) * (Tb.stepParameters y).threshold + 2 * e ≤
      x ^ (-(1 / 2 : ℝ) + 1 / 1000) := by
    have h1 := mul_le_mul_of_nonneg_right hhalf hσ.le
    have h2 : e ≤ Ce * x ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left (hEx.trans hxm2) (by positivity)
    have h3 := F.inv_le
    have h4 : ((Tb.stepParameters y).threshold + 2 * Ce) * x ^ (-1 : ℝ) ≤
        ((Tb.stepParameters y).threshold + 5 * Ce + 1 + 4 * (2 * L + 1) ^ 4) * x ^ (-1 : ℝ) :=
      mul_le_mul_of_nonneg_right (by
        have : 0 ≤ 4 * (2 * L + 1) ^ 4 := by positivity
        linarith) hxm1
    have h5 : x ^ (-1 : ℝ) * (Tb.stepParameters y).threshold + 2 * (Ce * x ^ (-1 : ℝ)) =
        ((Tb.stepParameters y).threshold + 2 * Ce) * x ^ (-1 : ℝ) := by
      ring
    linarith
  have hdM : (d : ℝ) ≤ (localChainDepth (Tb.stepParameters y) β k) := by
    have : d ≤ (localChainDepth (Tb.stepParameters y) β k) := by omega
    exact_mod_cast this
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ (localChainDepth (Tb.stepParameters y) β k) := Nat.cast_nonneg _
  have hc3 : 3 * ((d : ℝ) * e) + (localChainDepth (Tb.stepParameters y) β k) * E ≤ x ^ (-(1 / 2 : ℝ) + 1 / 1000) := by
    have h1 : (d : ℝ) * e ≤ (localChainDepth (Tb.stepParameters y) β k) * e := mul_le_mul_of_nonneg_right hdM he0
    have h2 : 3 * (((localChainDepth (Tb.stepParameters y) β k) : ℝ) * e) + (localChainDepth (Tb.stepParameters y) β k) * E =
        (3 * Ce + 1) * (localChainDepth (Tb.stepParameters y) β k) * E := by
      rw [hedef]
      ring
    have h3 : (3 * Ce + 1) * (localChainDepth (Tb.stepParameters y) β k) * E ≤
        (3 * Ce + 1) * (localChainDepth (Tb.stepParameters y) β k) * x ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_left hEx (by positivity)
    have hxm2' : 0 ≤ x ^ (-2 : ℝ) := Real.rpow_nonneg hx0 _
    have h4 : (3 * Ce + 1) * (localChainDepth (Tb.stepParameters y) β k) * x ^ (-2 : ℝ) ≤
        ((Tb.stepParameters y).threshold + 5 * Ce + 1 + 4 * (2 * L + 1) ^ 4) * (localChainDepth (Tb.stepParameters y) β k) *
          x ^ (-2 : ℝ) := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hM0) hxm2'
      have : 0 ≤ 4 * (2 * L + 1) ^ 4 := by positivity
      linarith
    have h5 : ((Tb.stepParameters y).threshold + 5 * Ce + 1 + 4 * (2 * L + 1) ^ 4) *
        ((localChainDepth (Tb.stepParameters y) β k) : ℝ) * x ^ (-2 : ℝ) ≤
        x ^ (-(1 / 2 : ℝ) + 1 / 1000) := F.depth_inv_sq_le
    linarith
  have hlogs : ρ₀ + (localChainDepth (Tb.stepParameters y) β k) + 4 ≤ x ^ ((1 : ℝ) / 1000) := F.logs_le
  have hCbX : 0 ≤ Cb * x ^ (-(1 / 2 : ℝ) + 1 / 1000) := mul_nonneg hCb hX1
  refine ⟨hx0, ?_, local_null S hkt' hH hside hLN hLd hbs o, S.prob _ _, hmain.1.le ?_, hmain.2.le ?_⟩
  · intro s hs
    filter_upwards [local_ae S hkt' hH hside hLN hLd hbs o] with u hu hlocal hsz
    obtain ⟨ev1, ev2⟩ := hu.1.1 hlocal
    have g2 := hu.2.2 ev2
    set db := sampleBelow (Tb.stepParameters y) (k + a + d) (localChainDepth (Tb.stepParameters y) β k) N u with hdb
    set V := topField (Tb.stepParameters y) (k + a + d)
      (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db with hV
    set o₁ := siteAbove (Tb.stepParameters y).side d
      (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) o with ho₁
    set rd := ballRadius (Tb.stepParameters y).side (nn / L ^ a) ρ₀ d with hrd
    set cc := maxCurvatureOnBall V o₁ (rd + 1) with hcc
    have hcc0 : 0 ≤ cc := maxCurv_nonneg _ _ _
    have hrd5 : rd ≤ 5 * ρ₀ := by
      rw [hrd, hLdef, ballRadius_shift _ hLpos, hadM]
      unfold ballRadius
      have hLM : x ≤ ((Tb.stepParameters y).side : ℝ) ^ (localChainDepth (Tb.stepParameters y) β k) :=
        F.le_two_pow_depth.trans (pow_le_pow_left₀ (by norm_num) hL2 (localChainDepth (Tb.stepParameters y) β k))
      have h20 : 20 * nn ≤ x := by
        have := F.rpow_le_self
        linarith
      have hLMpos : 0 < ((Tb.stepParameters y).side : ℝ) ^ (localChainDepth (Tb.stepParameters y) β k) := by linarith
      have : 20 * nn / ((Tb.stepParameters y).side : ℝ) ^ (localChainDepth (Tb.stepParameters y) β k) ≤ 1 :=
        (div_le_one hLMpos).2 (h20.trans hLM)
      linarith
    have hrd0 : 0 ≤ rd := by
      rw [hrd]
      unfold ballRadius
      have : 0 ≤ L := by linarith
      positivity
    set R := ⌊rd⌋₊ with hR
    have hRr : (R : ℝ) ≤ rd := Nat.floor_le hrd0
    have hRside : 2 * (R + 1) + 2 < (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) := by
      have h1 : (2 * ((R : ℝ) + 1) + 2) <
          ((fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) : ℝ) := by
        have : 2 ^ 10 * m ≤ ((fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) : ℝ) := hbs
        linarith
      exact_mod_cast h1
    have hcold : ∀ p ∈ plaquettesIn (supBall o₁ ((R : ℝ) + 1)), curvature V p.1 p.2.1 p.2.2 ≤ cc := fun p hp =>
      curvature_le_maxCurv V o₁ (rd + 1) (plaquettesIn_mono (supBall_mono o₁ (by linarith)) hp)
    have hch : ∀ b : TorusBond (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N),
        b.1 ∈ supBall o₁ rd →
        ‖((ResponseInTheExpansion.gaugeTransform (axialGaugeAt (Tb.stepParameters y) V o₁) V b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
          3 * ((R : ℝ) + 1) * cc := by
      intro b hb
      refine axial_defect_le hAx (Tb.stepParameters y) V o₁ R hRside hcc0 hcold b ?_
      rw [supDist_comm]
      exact Nat.le_floor (mem_supBall_iff.1 hb)
    have hZ : C₁ * (ρ₀ * cc + widenedStageSum T (k + a) (nn / L ^ a) ρ₀ d
          (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db o +
        widenedStageMax (k + a) (nn / L ^ a) ρ₀ d
          (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db o +
        ((localChainDepth (Tb.stepParameters y) β k) : ℝ) * E) ≤ s :=
      (min_le_iff.1 hsz).resolve_left (not_le.2 hs)
    have hL0 := stageSum_nonneg T (k + a) (nn / L ^ a) ρ₀ d
      (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db o
    have hMx0 := stageMax_nonneg (k + a) (nn / L ^ a) ρ₀ d
      (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db o
    set Ls := widenedStageSum T (k + a) (nn / L ^ a) ρ₀ d
      (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db o with hLs
    set Mx := widenedStageMax (k + a) (nn / L ^ a) ρ₀ d
      (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db o with hMx
    have hw1 : 0 ≤ ρ₀ * cc := mul_nonneg hρ0 hcc0
    have hw4 : 0 ≤ ((localChainDepth (Tb.stepParameters y) β k) : ℝ) * E := mul_nonneg hM0 hE0
    have hNb0 : 0 ≤ Nb := by linarith
    have hCe0 : 0 ≤ Ce := by linarith
    have ht1 := mul_nonneg hNb0 hw1
    have ht2 := mul_nonneg hNb0 hMx0
    have ht3 := mul_nonneg hNb0 hw4
    have ht4 := mul_nonneg hCe0 hw1
    have ht5 := mul_nonneg hCe0 hL0
    have ht6 := mul_nonneg hCe0 hMx0
    have ht7 := mul_nonneg hNb0 hL0
    have ht8 := mul_nonneg hCe0 hw4
    have hexp : C₁ * (ρ₀ * cc + Ls + Mx + ((localChainDepth (Tb.stepParameters y) β k) : ℝ) * E) =
        36 * (ρ₀ * cc) + 36 * Ls + 36 * Mx + 36 * (((localChainDepth (Tb.stepParameters y) β k) : ℝ) * E) +
          2 * (Nb * (ρ₀ * cc)) + 2 * (Nb * Ls) + 2 * (Nb * Mx) +
          2 * (Nb * (((localChainDepth (Tb.stepParameters y) β k) : ℝ) * E)) + 2 * (Ce * (ρ₀ * cc)) + 2 * (Ce * Ls) +
          2 * (Ce * Mx) + 2 * (Ce * (((localChainDepth (Tb.stepParameters y) β k) : ℝ) * E)) := by
      rw [hC₁def]
      ring
    rw [hexp] at hZ
    have ha₀ : 3 * ((R : ℝ) + 1) * cc ≤ 18 * (ρ₀ * cc) := by
      have h3 : 3 * ((R : ℝ) + 1) ≤ 18 * ρ₀ := by linarith
      have h4 := mul_le_mul_of_nonneg_right h3 hcc0
      linarith
    have hde : (d : ℝ) * e ≤ Ce * (((localChainDepth (Tb.stepParameters y) β k) : ℝ) * E) := by
      have h1 : (d : ℝ) * e ≤ (localChainDepth (Tb.stepParameters y) β k) * e := mul_le_mul_of_nonneg_right hdM he0
      have h2 : ((localChainDepth (Tb.stepParameters y) β k) : ℝ) * e =
          Ce * (((localChainDepth (Tb.stepParameters y) β k) : ℝ) * E) := by
        rw [hedef]
        ring
      linarith
    have hslack : 1 + ρ₀ ≤ 4 * ρ₀ - 4 * ρ₀ / L := by
      have : 4 * ρ₀ / L ≤ 2 * ρ₀ := by
        rw [div_le_iff₀ (by linarith)]
        have := mul_le_mul_of_nonneg_left hL2 hρ0
        linarith
      linarith
    have hsum : 2 * (3 * ((R : ℝ) + 1) * cc + Nb * Ls + (d : ℝ) * e) ≤ s := by linarith
    have hmaxs : Mx ≤ s := by linarith
    exact gaugeSmall_along (Nb := Nb) (sz := s) H₂ (by linarith) he0 hNb0 hρ0 hodd hslack le_rfl hNb1 d le_rfl
      (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) hbs db o
      (axialGaugeAt (Tb.stepParameters y) V o₁) (3 * ((R : ℝ) + 1) * cc) (by positivity) g2 hch hsum hmaxs
  · have h1 : ((1 : ℝ) / 2) ^ (localChainDepth (Tb.stepParameters y) β k) * (Tb.stepParameters y).threshold + 2 * e +
        8 * (Cb * x ^ (-(1 / 2 : ℝ) + 1 / 1000)) ≤
        (1 + 8 * Cb) * x ^ (-(1 / 2 : ℝ) + 1 / 1000) := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ ρ₀ + 3)
    have h3 : 13 * ((d : ℝ) * (Cb * x ^ (-(1 / 2 : ℝ) + 1 / 1000))) ≤
        13 * (((localChainDepth (Tb.stepParameters y) β k) : ℝ) * (Cb * x ^ (-(1 / 2 : ℝ) + 1 / 1000))) := by
      have := mul_le_mul_of_nonneg_right hdM hCbX
      linarith
    have h4 : (ρ₀ + 3) * ((1 + 8 * Cb) * x ^ (-(1 / 2 : ℝ) + 1 / 1000)) +
        13 * (((localChainDepth (Tb.stepParameters y) β k) : ℝ) * (Cb * x ^ (-(1 / 2 : ℝ) + 1 / 1000))) +
          x ^ (-(1 / 2 : ℝ) + 1 / 1000) ≤
        ((1 + 21 * Cb) * (ρ₀ + (localChainDepth (Tb.stepParameters y) β k) + 4)) * x ^ (-(1 / 2 : ℝ) + 1 / 1000) := by
      have hp : (ρ₀ + 3) * (1 + 8 * Cb) + 13 * (((localChainDepth (Tb.stepParameters y) β k) : ℝ) * Cb) + 1 ≤
          (1 + 21 * Cb) * (ρ₀ + (localChainDepth (Tb.stepParameters y) β k) + 4) := by
        have a1 := mul_nonneg hCb hρ0
        have a2 := mul_nonneg hCb hM0
        linarith
      have a3 := mul_le_mul_of_nonneg_right hp hX1
      linarith
    have h5 : ((1 + 21 * Cb) * (ρ₀ + (localChainDepth (Tb.stepParameters y) β k) + 4)) * x ^ (-(1 / 2 : ℝ) + 1 / 1000) ≤
        (1 + 21 * Cb) * x ^ (-(1 / 2 : ℝ) + 2 / 1000) := by
      rw [hXX, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogs (by positivity)) hX1
    have h6 : (ρ₀ + 3) * (((1 : ℝ) / 2) ^ (localChainDepth (Tb.stepParameters y) β k) * (Tb.stepParameters y).threshold +
        2 * e + 8 * (Cb * x ^ (-(1 / 2 : ℝ) + 1 / 1000))) +
        13 * ((d : ℝ) * (Cb * x ^ (-(1 / 2 : ℝ) + 1 / 1000))) + 3 * ((d : ℝ) * e) +
          (localChainDepth (Tb.stepParameters y) β k) * E ≤
        (1 + 21 * Cb) * x ^ (-(1 / 2 : ℝ) + 2 / 1000) := by linarith
    have h7 := mul_le_mul_of_nonneg_left h6 hC₁.le
    refine h7.trans ?_
    have h8 : 0 ≤ (2 + 16 * Cb) * x ^ (-(1 / 2 : ℝ) + 2 / 1000) := by positivity
    linarith
  · have hfirst : 0 ≤ ((1 : ℝ) / 2) ^ (localChainDepth (Tb.stepParameters y) β k) * (Tb.stepParameters y).threshold := by
      positivity
    have h1 : ((1 : ℝ) / 2) ^ (localChainDepth (Tb.stepParameters y) β k) * (Tb.stepParameters y).threshold + 2 * e +
        8 * (Cb * x ^ (-(1 / 2 : ℝ) + 1 / 1000)) +
        8 * (Cb * x ^ (-(1 / 2 : ℝ) + 1 / 1000)) + 2 * e ≤ (2 + 16 * Cb) * x ^ (-(1 / 2 : ℝ) + 1 / 1000) := by
      linarith
    refine h1.trans ?_
    have h8 : 0 ≤ (C₁ * (1 + 21 * Cb)) * x ^ (-(1 / 2 : ℝ) + 1 / 1000) := by positivity
    linarith
end Main
end LocalChainSize
open LocalChainSize
theorem localChainSizeStatement_holds (hCurv : curvatureHalvesStatement)
    (hMom : stepDeviationMomentsStatement) (hDown : descentKeepsBallClearStatement)
    (hAx : axialGaugeNearOneStatement) (hFl : localChainFloorsStatement)
    (hDraw : BoxMarks.lowerMarginalStatement) (hTP : TwoPointByTotalCovarianceStatement) :
    localChainSizeStatement := by
  refine holdsOnParameters_and3 hCurv hMom hDown ?_
  intro Tb y hD hy hC hM hO
  obtain ⟨C₁, c, hC₁, hc, hmain⟩ := bounds_at hAx hFl hDraw hTP hD hy hC hM hO
  refine ⟨C₁, c, hC₁, hc, fun q => ?_⟩
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · obtain ⟨Cq, x₀, -, h⟩ := hmain 1 le_rfl
    refine ⟨1, x₀, fun T β k N _ nn t d d' o hloc hLN hkt htd hd' => ?_⟩
    subst hd'
    obtain ⟨-, hP1, hnull, hprob, -, -⟩ := h T β k N nn t d o hloc hLN hkt htd
    have hI : Integrable ({u | IsLocalEventFrom T t d (localChainDepth (Tb.stepParameters y) β k)
        (localBlockSide (Tb.stepParameters y) β k) N u o}.indicator
        fun _ => (1 : ℝ)) (markedSampleLaw T β (t + d + localChainDepth (Tb.stepParameters y) β k) N) := by
      refine Integrable.of_bound (aestronglyMeasurable_const.indicator₀ hnull) 1 (Filter.Eventually.of_forall fun u => ?_)
      by_cases hu : u ∈ {u | IsLocalEventFrom T t d (localChainDepth (Tb.stepParameters y) β k)
          (localBlockSide (Tb.stepParameters y) β k) N u o}
      · simp [Set.indicator_of_mem hu]
      · simp [Set.indicator_of_notMem hu]
    have hle : ∫ u, ({u | IsLocalEventFrom T t d (localChainDepth (Tb.stepParameters y) β k)
        (localBlockSide (Tb.stepParameters y) β k) N u o}.indicator
        fun _ => (1 : ℝ)) u ∂(markedSampleLaw T β (t + d + localChainDepth (Tb.stepParameters y) β k) N) ≤ 1 := by
      have h1 : ∀ u, ({u | IsLocalEventFrom T t d (localChainDepth (Tb.stepParameters y) β k)
          (localBlockSide (Tb.stepParameters y) β k) N u o}.indicator
          fun _ => (1 : ℝ)) u ≤ 1 := fun u => Set.indicator_le_self' (fun _ _ => zero_le_one) u
      have h2 := integral_mono hI (integrable_const (1 : ℝ)) h1
      simpa using h2
    simp only [pow_zero]
    exact ⟨hP1, ⟨hI, hle⟩, hI, hle⟩
  · obtain ⟨Cq, x₀, hCq, h⟩ := hmain q hq
    refine ⟨Cq, x₀, fun T β k N _ nn t d d' o hloc hLN hkt htd hd' => ?_⟩
    subst hd'
    obtain ⟨hx, hP1, hnull, hprob, hL1, hL2⟩ := h T β k N nn t d o hloc hLN hkt htd
    have hX₁ := Real.rpow_nonneg hx (-(1 / 2 : ℝ) + 1 / 1000)
    have hX₂ := Real.rpow_nonneg hx (-(1 / 2 : ℝ) + 2 / 1000)
    have hs0 : 0 ≤ localLogScale (Tb.stepParameters y) β k := Nat.cast_nonneg _
    have m1 := indicator_moment (fun u => chainSize_nonneg T hC₁.le hs0 c _ t _ d _ _ o) hq (mul_nonneg hCq hX₂) hL1
    have m2 := indicator_moment (fun u => maxCurv_nonneg _ _ _) hq (mul_nonneg hCq hX₁) hL2
    exact ⟨hP1, m1, m2⟩
end YangMills.Construction.ResponseInTheExpansion
end
