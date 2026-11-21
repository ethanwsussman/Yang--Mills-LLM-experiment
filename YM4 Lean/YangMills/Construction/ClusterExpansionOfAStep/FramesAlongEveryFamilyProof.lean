import YangMills.Construction.ClusterExpansionOfAStep.ChainOnATorus
import YangMills.Construction.ClusterExpansionOfAStep.FramesAlongEveryFamily
import YangMills.Construction.ClusterExpansionOfAStep.MovesAlongLinearDirections
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorImagesOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.FrameAnalyticity
theorem frameAnalyticAlongFamilies_of_reflections
    (hmove : ColdStepAtMirrorFrames.ReflectedFieldOfTranslatedTop)
    (himg : ColdStepAtMirrorFrames.reflectedImagesOfBond) :
    FrameAnalyticity.FrameAnalyticAlongFamilies := by
  intro T hT
  obtain ⟨_, _, _, _, _, _, _, _, hbody⟩ := hT.chain
  refine ⟨(2 : ℝ) ^ 1600, ?_⟩
  intro x y hx t n _ hn₀ V hcold b hb j c X
  have hthr := hT.σ_pos
  have hs0 : 0 < 5 / 4 * T.threshold := by positivity
  have hsA : 5 / 4 * T.threshold ≤ T.σA := by linarith [hT.σ_le]
  have hn4 : 4096 ≤ n := hT.n₀_ge.trans hn₀
  have hm16 : 16 ≤ RenormalizationStepParameters.boxRadius x := LinearDirections.sixteen_le_boxRadius hx
  set m := RenormalizationStepParameters.boxRadius x with hm
  have hLodd : Odd T.side := hT.L_odd
  have hLpos : 0 < T.side := hLodd.pos
  set F := TorusFields.torusFrame T.side t n with hF
  have hn : ∀ i, F.extent i = n := fun _ => rfl
  have hodd : Odd F.blockSide := hLodd
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hn]; omega
  have h2 : 2 ≤ n := by omega
  haveI hne0 : NeZero (n * T.side) := ⟨(Nat.mul_pos (by omega) hLpos).ne'⟩
  haveI : NeZero (n * F.blockSide) := hne0
  haveI : NeZero (n * (TorusLumps.stepBlockFrame T.side n).blockSide) := hne0
  haveI hper : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by rw [TopLevelSites.period_top_of_extent hn]; omega⟩
  have hp : ∀ i, F.period F.top i = n := TopLevelSites.period_top_of_extent hn
  have hamb : BlockAverages.IsAdmissibleAmbient F := Or.inr fun i => by rw [hn]; omega
  have hnt : ¬ BlockAverages.IsAxialTreeBond (F := F) (StepCosts.torusSiteInFrame F F.depth b.1, b.2) := by
    intro ht
    have h0 : ¬ BlockAverages.IsAxialTreeBond (F := TorusLumps.stepBlockFrame T.side n)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame T.side n) 0 b.1, b.2) := by
      classical
      exact (Finset.mem_filter.mp hb).2
    apply h0
    have e1 := (TopLevelSites.isAxialTreeBond_torusSiteInFrame_iff (F := F) hn hodd h2 b.1 b.2).mp ht
    exact (TopLevelSites.isAxialTreeBond_torusSiteInFrame_iff (F := TorusLumps.stepBlockFrame T.side n)
      (fun _ => rfl) hLodd h2 b.1 b.2).mpr e1
  have hcell : BlockAverages.enclosingCell (StepCosts.torusSiteInFrame F F.depth b.1) =
      StepCosts.torusSiteInFrame F F.top (TorusLumps.parentBlock T.side b.1) :=
    TopLevelSites.enclosingCell_torusSiteInFrame hn b.1
  by_cases hbig : 4 * m + 5 < n
  · have hsides : ∀ i, 4 * m + 5 < F.extent i := fun i => by rw [hn]; exact hbig
    set Y₁ := StepCosts.torusSiteInFrame F F.top (TorusLumps.parentBlock T.side b.1) with hY₁
    set M := ColdStepAtMirrorFrames.reflectedFrame F m with hM
    set G : M.GaugeField M.top → BlockAverages.imaginaryQuaternions :=
      BlockAverages.minimizingBondCoordinate T.coupling T.ρA (ColdStepAtMirrorFrames.finiteCells M)
        (ColdStepAtMirrorFrames.reflectedBond (F := F) m (StepCosts.torusSiteInFrame F F.depth b.1, b.2)) with hG
    have hframe : ∀ V' : TorusFields.TorusField n, StepCosts.frameCoord (T.stepParameters y) T.ρA t m V' b =
        G (ColdStepAtMirrorFrames.reflectedField m Y₁ (TorusFields.readAtLevel F F.top V')) := by
      intro V'
      have : (∀ i, 4 * m + 5 < (TorusFields.torusFrame (T.stepParameters y).side t n).extent i) := hsides
      unfold StepCosts.frameCoord ColdStepAtMirrorFrames.bondFrameCoord
      rw [if_pos this]
      unfold ColdStepAtMirrorFrames.reflectedBondCoord
      simp only
      exact congrArg (fun Z => BlockAverages.minimizingBondCoordinate T.coupling T.ρA
        (ColdStepAtMirrorFrames.finiteCells M)
        (ColdStepAtMirrorFrames.reflectedBond (F := F) m (StepCosts.torusSiteInFrame F F.depth b.1, b.2))
        (ColdStepAtMirrorFrames.reflectedField m Z (TorusFields.readAtLevel F F.top V'))) hcell
    set V₁ := TorusFields.readAtLevel F F.top V with hV₁
    set U := ColdStepAtMirrorFrames.reflectedField m Y₁ V₁ with hU
    set c₁ : Fin j → F.Cell × Fin 4 := fun l => (StepCosts.torusSiteInFrame F F.top (c l).1, (c l).2) with hc₁
    set Yd : Fin j → M.Cell → Fin 4 → BlockAverages.imaginaryQuaternions :=
      fun l => ColdStepAtMirrorFrames.reflectedDirection m Y₁ V₁ (c₁ l) (X l) with hYd
    have hmoved : ∀ τ : Fin j → ℝ, ColdStepAtMirrorFrames.reflectedField m Y₁
        (TorusFields.readAtLevel F F.top (TorusFields.perturb c X τ V)) =
        BlockAverages.rotatedField (fun z i => ∑ l, τ l • Yd l z i) U := by
      intro τ
      rw [TorusChain.readAtLevel_perturb hp]
      exact hmove F m Y₁ V₁ j c₁ X τ (by omega)
    have hJ := fun l => himg F m Y₁ (c₁ l) (by omega) (fun i => by have := hsides i; omega)
    choose J _ hJ0 _ _ _ using hJ
    have hs' : ∀ i, 2 ≤ M.extent i := fun i => by
      change 2 ≤ 4 * m
      omega
    have hamb' : BlockAverages.IsAdmissibleAmbient M := Or.inr fun i => by
      change 64 ≤ 4 * m
      omega
    have hreg' := TopLevelSites.isOrthantRegular_finiteCells (F := M) (fun i => by have := hs' i; omega) 1024
    have hcoldU : BlockAverages.IsCold (ColdStepAtMirrorFrames.finiteCells M) M.top (5 / 4 * T.threshold) U :=
      TopLevelSites.isCold_reflectedField (F := F) hn (m := m) (by omega) hs0 V (TorusLumps.parentBlock T.side b.1)
        (fun a μ ν hμν _ => hcold _ _ _ hμν)
    have hcoord := (hbody M 1024 _ rfl hamb' le_rfl hreg' _ U hs0 hsA hcoldU).2.2.2.1
    obtain ⟨han, _⟩ := hcoord _ (LinearDirections.reflectedBond_mem_chordBonds hodd hs2 (by omega) _ _ hnt)
    have hfun : (fun τ : Fin j → ℝ =>
        StepCosts.frameCoord (T.stepParameters y) T.ρA t m (TorusFields.perturb c X τ V) b) =
        fun τ => G (BlockAverages.rotatedField (fun z i => ∑ l, τ l • Yd l z i) U) := by
      funext τ
      rw [hframe, hmoved]
    rw [hfun]
    exact (LinearDirections.analyticAt_and_iteratedFDeriv_linearMove (F := M) G U han Yd J
      (fun l z i h => hJ0 l V₁ (X l) z i h)).1
  · have hnotall : ¬ ∀ i, 4 * m + 5 < (TorusFields.torusFrame (T.stepParameters y).side t n).extent i :=
      fun h => hbig (h 0)
    set G : F.GaugeField F.top → BlockAverages.imaginaryQuaternions :=
      BlockAverages.minimizingBondCoordinate T.coupling T.ρA (ColdStepAtMirrorFrames.finiteCells F)
        (StepCosts.torusSiteInFrame F F.depth b.1, b.2) with hG
    have hframe : ∀ V' : TorusFields.TorusField n, StepCosts.frameCoord (T.stepParameters y) T.ρA t m V' b =
        G (TorusFields.readAtLevel F F.top V') := by
      intro V'
      unfold StepCosts.frameCoord ColdStepAtMirrorFrames.bondFrameCoord
      rw [if_neg hnotall]
      rfl
    have hreg := TopLevelSites.isOrthantRegular_finiteCells (F := F) (fun i => by have := hs2 i; omega) 1024
    have hcoldV : BlockAverages.IsCold (ColdStepAtMirrorFrames.finiteCells F) F.top (5 / 4 * T.threshold)
        (TorusFields.readAtLevel F F.top V) := TopLevelSites.isCold_readAtLevel hn hcold
    have hcoord := (hbody F 1024 _ rfl hamb le_rfl hreg _ _ hs0 hsA hcoldV).2.2.2.1
    obtain ⟨han, _⟩ := hcoord _ (LinearDirections.mem_chordBonds_finiteCells hodd hs2 _ _ hnt)
    set c₁ : Fin j → F.Cell × Fin 4 := fun l => (StepCosts.torusSiteInFrame F F.top (c l).1, (c l).2) with hc₁
    have hfun : (fun τ : Fin j → ℝ =>
        StepCosts.frameCoord (T.stepParameters y) T.ρA t m (TorusFields.perturb c X τ V) b) =
        fun τ => G (BlockAverages.rotatedField (BlockAverages.bondSpread c₁ X τ) (TorusFields.readAtLevel F F.top V)) := by
      funext τ
      rw [hframe, TorusChain.readAtLevel_perturb hp]
    rw [hfun]
    exact han j c₁ X
end YangMills.Construction.FrameAnalyticity
end
