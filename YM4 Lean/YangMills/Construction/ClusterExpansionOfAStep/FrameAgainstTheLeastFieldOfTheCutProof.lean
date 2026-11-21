import YangMills.Construction.ClusterExpansionOfAStep.ChartsOverTheTopOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.FrameAgainstTheLeastFieldOfTheCut
import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TopLevelSites TorusFields TorusLumps TorusMirror
  StepMarks StepCosts StepFrames
namespace StepFrames
theorem frameGap_isRangeSuppressed {N₀ δ σ : ℝ} (hN : 0 < N₀) (hδ : 0 < δ) (hσ : 0 < σ) :
    IsRangeSuppressed (frameGap N₀ δ σ) := by
  refine ⟨N₀ * (2 * σ) * Real.exp δ, 0, δ / 2 ^ 11, by positivity, fun x _ => ?_⟩
  have hpos : 0 ≤ frameGap N₀ δ σ x := by
    unfold frameGap
    positivity
  rw [abs_of_nonneg hpos, Real.rpow_zero, mul_one]
  unfold frameGap
  rw [mul_assoc (N₀ * (2 * σ))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  set r := clusterRange x
  have h1 : (r : ℝ) / 2 ^ 11 - 1 ≤ ((r / 2 ^ 11 : ℕ) : ℝ) := by
    have e : r < (r / 2 ^ 11 + 1) * 2 ^ 11 := by omega
    have e' : (r : ℝ) < (((r / 2 ^ 11 : ℕ) : ℝ) + 1) * 2 ^ 11 := by exact_mod_cast e
    have : (r : ℝ) / 2 ^ 11 < ((r / 2 ^ 11 : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ (by norm_num)]
      exact e'
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hδ.le
  have e : δ * ((r : ℝ) / 2 ^ 11 - 1) = δ / 2 ^ 11 * r - δ := by ring
  linarith
theorem frameNearMinimizer_holds (hc : ComplementOfThickenedLumpsRegular) :
    FrameNearMinimizer := by
  intro ℓ δ lam ρA σA cg N hfit hch hσ
  obtain ⟨δpos, _, _, _, ρle, _, _, Npos, hbody⟩ := hch
  have hπ : ρA < Real.pi := lt_of_le_of_lt ρle (by linarith [Real.pi_gt_three])
  refine ⟨frameGap_isRangeSuppressed (Npos 0) δpos hfit.σ_pos, ?_⟩
  intro t r r' n _ V S C s hr hsit b hb hy
  obtain ⟨spos, sle, n4096, hF⟩ := stepSituation_regular_and_cold hc hfit hsit
  have hn : ∀ i, (torusFrame ℓ.side t n).extent i = n := fun _ => rfl
  obtain ⟨hreg, hcold⟩ := hF (torusFrame ℓ.side t n) hn
  have hodd : Odd (torusFrame ℓ.side t n).blockSide := hfit.L_odd
  have hs2 : ∀ i, 2 ≤ (torusFrame ℓ.side t n).extent i := fun i => by rw [hn]; omega
  have h2 : 2 ≤ n := by omega
  have hLpos : 0 < ℓ.side := hfit.L_odd.pos
  have hne0 : NeZero (n * ℓ.side) := ⟨(Nat.mul_pos (by omega) hLpos).ne'⟩
  have : NeZero (n * (torusFrame ℓ.side t n).blockSide) := hne0
  have : NeZero (n * (stepBlockFrame ℓ.side n).blockSide) := hne0
  have hamb : IsAdmissibleAmbient (torusFrame ℓ.side t n) := Or.inr fun i => by rw [hn]; omega
  have hcell : enclosingCell (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1) =
      torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (parentBlock ℓ.side b.1) :=
    enclosingCell_torusSiteInFrame hn b.1
  have hb0 := hbody (torusFrame ℓ.side t n) 2047 (cellsOfSites (torusFrame ℓ.side t n) S) rfl hamb (by norm_num)
    hreg s (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) spos (sle.trans hσ) hcold
  obtain ⟨one, _, _, _, _, two⟩ := hb0
  have hnt : ¬ IsAxialTreeBond (F := torusFrame ℓ.side t n)
      (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1, b.2) := by
    intro ht
    have h0 : ¬ IsAxialTreeBond (F := stepBlockFrame ℓ.side n)
        (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 b.1, b.2) := by
      classical
      exact (Finset.mem_filter.mp hb).2
    apply h0
    have e1 := (isAxialTreeBond_torusSiteInFrame_iff (F := torusFrame ℓ.side t n) hn hodd h2 b.1 b.2).mp ht
    exact (isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame ℓ.side n) (fun _ => rfl) hfit.L_odd h2
      b.1 b.2).mpr e1
  set m := r / 2 ^ 11 with hm
  have hm16 : 16 ≤ m := hr.frame_radius
  by_cases hbig : 4 * m + 5 < n
  · obtain ⟨hbox, hboxcold⟩ := stepSituation_box_of_not_mem hfit hr hsit hy
    have hsides : ∀ i, 4 * m + 5 < (torusFrame ℓ.side t n).extent i := fun i => by rw [hn]; exact hbig
    have hagree := agreeOnBall_reflectedField (F := torusFrame ℓ.side t n) hn (m := m) (by omega) (by omega)
      (S := S) V (parentBlock ℓ.side b.1) (fun h hh => hbox h fun i => (hh i).trans (by push_cast; omega))
    have hcold' := isCold_reflectedField (F := torusFrame ℓ.side t n) hn (m := m) (by omega) spos V
      (parentBlock ℓ.side b.1) hboxcold
    have hs' : ∀ i, 2 ≤ (reflectedFrame (torusFrame ℓ.side t n) m).extent i := fun i => by
      change 2 ≤ 4 * m
      omega
    have hamb' : IsAdmissibleAmbient (reflectedFrame (torusFrame ℓ.side t n) m) := Or.inr fun i => by
      change 64 ≤ 4 * m
      omega
    have hreg' := isOrthantRegular_finiteCells (F := reflectedFrame (torusFrame ℓ.side t n) m)
      (fun i => by have := hs' i; omega) 2047
    have hloc := (two (reflectedFrame (torusFrame ℓ.side t n) m) _ _ _ 0 m rfl rfl hamb' hreg' hcold'
      hagree).2
    have one' := (hbody (reflectedFrame (torusFrame ℓ.side t n) m) 2047 _ rfl hamb' (by norm_num) hreg' s _
      spos (sle.trans hσ) hcold').1
    obtain ⟨w, hw, _, hlc⟩ := minimizingCoordinates_eq (ρ := ρA) hfit.L_odd hs' hπ le_rfl one'
    have hframe : frameCoord ℓ ρA t m V b = w (reflectedBond (F := torusFrame ℓ.side t n) m
        (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1, b.2)).1 b.2 := by
      unfold frameCoord bondFrameCoord
      rw [if_pos hsides]
      unfold reflectedBondCoord minimizingBondCoordinate
      simp only
      rw [hcell, hlc]
      rfl
    have hfr : frameCoord ℓ ρA t m V b = minimizingBondCoordinate ℓ.coupling ρA
        (finiteCells (reflectedFrame (torusFrame ℓ.side t n) m))
        (reflectedBond (F := torusFrame ℓ.side t n) m
          (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1, b.2))
        (reflectedField m
          (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (parentBlock ℓ.side b.1))
          (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)) := by
      unfold frameCoord bondFrameCoord
      rw [if_pos hsides]
      unfold reflectedBondCoord
      simp only
      rw [hcell]
    refine ⟨⟨fun _ => ⟨w, ?_, hframe⟩, fun h => absurd hbig h⟩, ?_⟩
    · simpa only [hcell] using hw
    · have hy0 : parentBlock ℓ.side b.1 ∈ S := by
        have h0 := hbox 0 fun i => by
          simp only [Pi.zero_apply, abs_zero]
          positivity
        have e0 : (siteOfInt 0 : TorusSite n) = 0 := by
          funext i
          simp [siteOfInt]
        rwa [e0, add_zero] at h0
      have hy1 : parentBlock ℓ.side (b.1 + TorusFields.unitStep (n * ℓ.side) b.2) ∈ S := by
        rcases parentBlock_add_unitStep (F := torusFrame ℓ.side t n) hn hodd h2 b.1 b.2 with e | e
        · have e' : parentBlock ℓ.side (b.1 + TorusFields.unitStep (n * ℓ.side) b.2) = parentBlock ℓ.side b.1 := e
          rw [e']
          exact hy0
        · have e' : parentBlock ℓ.side (b.1 + TorusFields.unitStep (n * ℓ.side) b.2) =
              parentBlock ℓ.side b.1 + TorusFields.unitStep n b.2 := e
          rw [e']
          have := hbox (Pi.single b.2 1) fun i => by
            by_cases hi : i = b.2
            · subst hi
              simp only [Pi.single_eq_same, abs_one]
              push_cast
              omega
            · simp only [Pi.single_eq_of_ne hi, abs_zero]
              positivity
          have e2 : (siteOfInt (Pi.single b.2 1) : TorusSite n) = TorusFields.unitStep n b.2 :=
            unitStep_eq_siteOfInt _ |>.symm
          rwa [e2] at this
      have hmem := mem_chordBonds_of_parentBlock (F := torusFrame ℓ.side t n) hn hodd h2 (S := S) b.1 b.2 hnt
        hy0 hy1
      obtain ⟨hc', he⟩ := centre_cellOffset hfit.L_odd hs2
        (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1)
      have hlow : fineBondAt
          (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (parentBlock ℓ.side b.1)) 0
          (cellOffset (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1)) b.2 =
          (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1, b.2) := by
        rw [← hcell]
        exact fineBondAt_enclosingCell_cellOffset hfit.L_odd hs2 _ _
      have hne' : ∀ i, NeZero ((reflectedFrame (torusFrame ℓ.side t n) m).period
          (reflectedFrame (torusFrame ℓ.side t n) m).top i) :=
        fun i => ⟨by rw [period_top]; have := hs' i; omega⟩
      have hlow0 := fineBondAt_zero (F' := reflectedFrame (torusFrame ℓ.side t n) m) hne'
        (cellOffset (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1)) b.2
      have hl := hloc 0
        (cellOffset (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1)) b.2 hc'
        (by rw [hlow]; exact hmem) (fun i => by simp)
        (by
          rw [hlow]
          simp only
          rw [← hcell]
          exact (cellSupDist_enclosingCell_step_le hfit.L_odd hs2 _ _).trans (by omega))
      have hd : cellSupDist
          (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (parentBlock ℓ.side b.1))
          (enclosingCell (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1)) = 0 := by
        rw [hcell, cellSupDist_self]
      rw [hlow, hlow0] at hl
      have hl1 := hl.1
      simp only [hd] at hl1
      rw [hfr, norm_sub_rev]
      have e3 : -δ * ((m : ℝ) - ((0 : ℕ) : ℝ)) = -(δ * (m : ℝ)) := by push_cast; ring
      rw [e3] at hl1
      exact hl1
  · have hS := stepSituation_eq_univ_of_small hfit hr hsit hy hbig
    subst hS
    rw [cellsOfSites_univ hn] at one
    obtain ⟨w, hw, _, hlc⟩ := minimizingCoordinates_eq (ρ := ρA) hfit.L_odd hs2 hπ le_rfl one
    have hframe : frameCoord ℓ ρA t m V b =
        w (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1) b.2 := by
      unfold frameCoord bondFrameCoord
      rw [if_neg (fun h => hbig (h 0))]
      unfold minimizingBondCoordinate
      simp only
      rw [hlc]
    have hle : minimizerCoord ℓ.coupling ρA ℓ.side t Finset.univ V b =
        w (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1) b.2 := by
      unfold minimizerCoord minimizingBondCoordinate
      simp only
      rw [cellsOfSites_univ hn, hlc]
    refine ⟨⟨fun h => absurd h hbig, fun _ => ⟨w, hw, hframe⟩⟩, ?_⟩
    rw [hframe, hle, sub_self, norm_zero]
    have := Npos 0
    positivity
end StepFrames
end YangMills.Construction
end
