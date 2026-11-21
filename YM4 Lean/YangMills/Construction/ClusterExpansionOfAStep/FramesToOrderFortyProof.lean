import YangMills.Construction.ClusterExpansionOfAStep.ChainOnATorus
import YangMills.Construction.ClusterExpansionOfAStep.FramesToOrderForty
import YangMills.Construction.ClusterExpansionOfAStep.MovesAlongLinearDirections
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorImagesOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames TopLevelSites TorusFields TorusLumps TorusChain StepCosts
  RenormalizationStepParameters
open LinearDirections in
theorem frameDerivativesBounded_of_reflection (hmove : ReflectedFieldOfTranslatedTop)
    (himg : reflectedImagesOfBond) : FrameDerivativesBounded := by
  intro T hT
  obtain ⟨δpos, _, _, _, ρle, _, _, Npos, hbody⟩ := hT.chain
  refine ⟨T.N, (2 : ℝ) ^ 1600, Npos, ?_⟩
  intro x y hx t n _ hn₀ V hcold b hb j c X hj1 _ hX
  have hσ := hT.σ_pos
  have hs0 : 0 < 5 / 4 * T.threshold := by positivity
  have hsA : 5 / 4 * T.threshold ≤ T.σA := by linarith [hT.σ_le]
  have hn4 : 4096 ≤ n := hT.n₀_ge.trans hn₀
  have hm16 : 16 ≤ boxRadius x := sixteen_le_boxRadius hx
  set m := boxRadius x with hm
  have hLodd : Odd T.side := hT.L_odd
  have hLpos : 0 < T.side := hLodd.pos
  set F := torusFrame T.side t n with hF
  have hn : ∀ i, F.extent i = n := fun _ => rfl
  have hodd : Odd F.blockSide := hLodd
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hn]; omega
  have h2 : 2 ≤ n := by omega
  have hne0 : NeZero (n * T.side) := ⟨(Nat.mul_pos (by omega) hLpos).ne'⟩
  have : NeZero (n * F.blockSide) := hne0
  have : NeZero (n * (stepBlockFrame T.side n).blockSide) := hne0
  have hper : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by rw [period_top_of_extent hn]; omega⟩
  have hp : ∀ i, F.period F.top i = n := period_top_of_extent hn
  have hamb : IsAdmissibleAmbient F := Or.inr fun i => by rw [hn]; omega
  have hnt : ¬ IsAxialTreeBond (F := F) (torusSiteInFrame F F.depth b.1, b.2) := by
    intro ht
    have h0 : ¬ IsAxialTreeBond (F := stepBlockFrame T.side n)
        (torusSiteInFrame (stepBlockFrame T.side n) 0 b.1, b.2) := by
      classical
      exact (Finset.mem_filter.mp hb).2
    apply h0
    have e1 := (isAxialTreeBond_torusSiteInFrame_iff (F := F) hn hodd h2 b.1 b.2).mp ht
    exact (isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame T.side n) (fun _ => rfl) hLodd h2 b.1 b.2).mpr e1
  have hcell : enclosingCell (torusSiteInFrame F F.depth b.1) =
      torusSiteInFrame F F.top (parentBlock T.side b.1) := enclosingCell_torusSiteInFrame hn b.1
  by_cases hbig : 4 * m + 5 < n
  · have hsides : ∀ i, 4 * m + 5 < F.extent i := fun i => by rw [hn]; exact hbig
    set Y₁ := torusSiteInFrame F F.top (parentBlock T.side b.1) with hY₁
    set M := reflectedFrame F m with hM
    set G : M.GaugeField M.top → imaginaryQuaternions := minimizingBondCoordinate T.coupling T.ρA (finiteCells M)
      (reflectedBond (F := F) m (torusSiteInFrame F F.depth b.1, b.2)) with hG
    have hframe : ∀ V' : TorusField n, frameCoord (T.stepParameters y) T.ρA t m V' b =
        G (reflectedField m Y₁ (readAtLevel F F.top V')) := by
      intro V'
      have : (∀ i, 4 * m + 5 < (torusFrame (T.stepParameters y).side t n).extent i) := hsides
      unfold frameCoord bondFrameCoord
      rw [if_pos this]
      unfold reflectedBondCoord
      simp only
      exact congrArg (fun Z => minimizingBondCoordinate T.coupling T.ρA (finiteCells M)
        (reflectedBond (F := F) m (torusSiteInFrame F F.depth b.1, b.2))
          (reflectedField m Z (readAtLevel F F.top V'))) hcell
    set V₁ := readAtLevel F F.top V with hV₁
    set U := reflectedField m Y₁ V₁ with hU
    set c₁ : Fin j → F.Cell × Fin 4 := fun l => (torusSiteInFrame F F.top (c l).1, (c l).2) with hc₁
    set Yd : Fin j → M.Cell → Fin 4 → imaginaryQuaternions :=
      fun l => reflectedDirection m Y₁ V₁ (c₁ l) (X l) with hYd
    have hmoved : ∀ τ : Fin j → ℝ, reflectedField m Y₁ (readAtLevel F F.top (perturb c X τ V)) =
        rotatedField (fun z i => ∑ l, τ l • Yd l z i) U := by
      intro τ
      rw [readAtLevel_perturb hp]
      exact hmove F m Y₁ V₁ j c₁ X τ (by omega)
    have hJ := fun l => himg F m Y₁ (c₁ l) (by omega) (fun i => by have := hsides i; omega)
    choose J hJcard hJ0 hJnorm _ hJoff using hJ
    have hs' : ∀ i, 2 ≤ M.extent i := fun i => by
      change 2 ≤ 4 * m
      omega
    have hamb' : IsAdmissibleAmbient M := Or.inr fun i => by
      change 64 ≤ 4 * m
      omega
    have hreg' := isOrthantRegular_finiteCells (F := M) (fun i => by have := hs' i; omega) 1024
    have hcoldU : IsCold (finiteCells M) M.top (5 / 4 * T.threshold) U :=
      isCold_reflectedField (F := F) hn (m := m) (by omega) hs0 V (parentBlock T.side b.1)
        (fun a μ ν hμν _ => hcold _ _ _ hμν)
    have hcoord := (hbody M 1024 _ rfl hamb' le_rfl hreg' _ U hs0 hsA hcoldU).2.2.2.1
    have hch := hcoord _ (reflectedBond_mem_chordBonds hodd hs2 (by omega) _ _ hnt)
    obtain ⟨han, hder⟩ := hch
    obtain ⟨hAn, hExp⟩ :=
      analyticAt_and_iteratedFDeriv_linearMove (F := M) G U han Yd J (fun l z i h => hJ0 l V₁ (X l) z i h)
    have hfun : (fun τ : Fin j → ℝ => frameCoord (T.stepParameters y) T.ρA t m (perturb c X τ V) b) =
        fun τ => G (rotatedField (fun z i => ∑ l, τ l • Yd l z i) U) := by
      funext τ
      rw [hframe, hmoved]
    have hd : mixedDeriv (fun V' : TorusField n => frameCoord (T.stepParameters y) T.ρA t m V' b) V c X =
        ∑ r ∈ Fintype.piFinset J, mixedBondDerivative G U r (fun l => Yd l (r l).1 (r l).2) := by
      unfold mixedDeriv
      rw [hfun]
      exact hExp
    refine ⟨?_, ?_, ?_⟩
    · rw [hfun]
      exact hAn.contDiffAt
    · rw [hd]
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ r ∈ Fintype.piFinset J,
          ‖mixedBondDerivative G U r (fun l => Yd l (r l).1 (r l).2)‖ ≤ T.N j := by
        intro r hr
        have hr' := Fintype.mem_piFinset.mp hr
        have hu : AreUnitVectors (fun l => Yd l (r l).1 (r l).2) := fun l => by
          rw [← hX l]
          exact hJnorm l V₁ (X l) (r l) (hr' l)
        refine (hder j r _ hj1 hu).trans ?_
        exact mul_le_of_le_one_right (Npos j).le (Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _)))
      refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
      rw [nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Npos j).le
      rw [Fintype.card_piFinset]
      have : ∏ l, (J l).card ≤ 16 ^ j := by
        calc ∏ l, (J l).card ≤ ∏ _l : Fin j, 16 := Finset.prod_le_prod' fun l _ => hJcard l
          _ = 16 ^ j := by simp
      exact_mod_cast this
    · intro _ ⟨l, hl⟩
      have hoff : ∀ u : (Fin 4 → ℤ) × Fin 4, BlockAverages.BondWithinRadius m u →
          c₁ l ≠ (Y₁ + siteOfCoords F.top u.1, u.2) := by
        intro u hu he
        apply hl u hu
        have h1 : torusSiteInFrame F F.top (c l).1 = Y₁ + siteOfCoords F.top u.1 := congrArg Prod.fst he
        have h2' : (c l).2 = u.2 := congrArg Prod.snd he
        refine Prod.ext ?_ h2'
        have h3 : torusSiteInFrame F F.top (c l).1 =
            torusSiteInFrame F F.top (parentBlock T.side b.1 + siteOfInt u.1) := by
          rw [h1, TopLevelSites.torusSiteInFrame_add hp,
            TopLevelSites.torusSiteInFrame_siteOfInt hp]
        have h4 := congrArg (toTorusSite n) h3
        rwa [TopLevelSites.toTorusSite_torusSiteInFrame hp,
          TopLevelSites.toTorusSite_torusSiteInFrame hp] at h4
      have hempty : J l = ∅ := (hJoff l hoff).1
      rw [hd]
      have : Fintype.piFinset J = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro r hr
        have := Fintype.mem_piFinset.mp hr l
        rw [hempty] at this
        exact absurd this (Finset.notMem_empty _)
      rw [this, Finset.sum_empty]
  · have hnotall : ¬ ∀ i, 4 * m + 5 < (torusFrame (T.stepParameters y).side t n).extent i :=
      fun h => hbig (h 0)
    set G : F.GaugeField F.top → imaginaryQuaternions :=
      minimizingBondCoordinate T.coupling T.ρA (finiteCells F) (torusSiteInFrame F F.depth b.1, b.2) with hG
    have hframe : ∀ V' : TorusField n, frameCoord (T.stepParameters y) T.ρA t m V' b =
        G (readAtLevel F F.top V') := by
      intro V'
      unfold frameCoord bondFrameCoord
      rw [if_neg hnotall]
      rfl
    have hreg := isOrthantRegular_finiteCells (F := F) (fun i => by have := hs2 i; omega) 1024
    have hcoldV : IsCold (finiteCells F) F.top (5 / 4 * T.threshold) (readAtLevel F F.top V) :=
      isCold_readAtLevel hn hcold
    have hcoord := (hbody F 1024 _ rfl hamb le_rfl hreg _ _ hs0 hsA hcoldV).2.2.2.1
    obtain ⟨han, hder⟩ := hcoord _ (mem_chordBonds_finiteCells hodd hs2 _ _ hnt)
    set c₁ : Fin j → F.Cell × Fin 4 := fun l => (torusSiteInFrame F F.top (c l).1, (c l).2) with hc₁
    have hfun : (fun τ : Fin j → ℝ => frameCoord (T.stepParameters y) T.ρA t m (perturb c X τ V) b) =
        fun τ => G (rotatedField (BlockAverages.bondSpread c₁ X τ) (readAtLevel F F.top V)) := by
      funext τ
      rw [hframe, readAtLevel_perturb hp]
    have hd : mixedDeriv (fun V' : TorusField n => frameCoord (T.stepParameters y) T.ρA t m V' b) V c X =
        mixedBondDerivative G (readAtLevel F F.top V) c₁ X := by
      unfold mixedDeriv mixedBondDerivative
      rw [hfun]
    refine ⟨?_, ?_, fun h => absurd h hbig⟩
    · rw [hfun]
      exact (han j c₁ X).contDiffAt
    · rw [hd]
      refine (hder j c₁ X hj1 hX).trans ?_
      have h1 : Real.exp (-T.δ₁ *
          (bondListDistance (enclosingCell (torusSiteInFrame F F.depth b.1, b.2).1) c₁ : ℝ)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ T.δ₁ *
            (bondListDistance (enclosingCell (torusSiteInFrame F F.depth b.1, b.2).1) c₁ : ℝ) := by positivity
        linarith
      have h3 : T.N j * 1 ≤ 16 ^ j * T.N j := by
        have : (1 : ℝ) ≤ 16 ^ j := one_le_pow₀ (by norm_num)
        nlinarith [Npos j]
      exact (mul_le_mul_of_nonneg_left h1 (Npos j).le).trans h3
end YangMills.Construction.ClusterExpansionOfAStep
end
