import YangMills.Construction.LawByMomentsOfTheFlow.CurvatureUnderTheFluctuationsOfTheChain
import YangMills.Construction.LawByMomentsOfTheFlow.FluctuationsOfAStepInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.HullsClearOfThePointInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.SitesOfAStepInALimitField
import YangMills.Construction.LawByMomentsOfTheFlow.TheLocalChainIsSmallUnderItsFluctuations
import YangMills.Construction.ResponseInTheExpansion.TheLocalEventIsLikelyProof
import YangMills.Construction.ResponseInTheExpansion.TheStepsOfTheLocalChainFormStates
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps StepSettings RenormalizationStepParameters WeightedResponses ResponseInTheExpansion MomentMethod LevelTestFunctions HullTrees ChainNoise TorusBlocks BlockOffsets TorusBalls BlockPlaces KeptRegion MarkedIntegrals TorusCounting FreeEnergies
section
variable {ℓ : StepParameters}
private theorem sample_fst_cast {a b n : ℕ} (h : a = b) (h' : a + 1 = b + 1) (w : MarkedSample ℓ (a + 1) n) :
    (h' ▸ w : MarkedSample ℓ (b + 1) n).1 = (h ▸ w.1 : MarkedSample ℓ b (n * ℓ.side)) := by
  subst h
  rfl
private theorem sampleBelow_fst_heq (a : ℕ) : ∀ (d n : ℕ) (e : a + 1 + d = a + (d + 1)) (w : MarkedSample ℓ (a + 1 + d) n),
    HEq (sampleBelow ℓ (a + 1) d n w).1 (sampleBelow ℓ a (d + 1) n (e ▸ w)) := by
  intro d
  induction d with
  | zero =>
    intro n e w
    rfl
  | succ d ih =>
    intro n e w
    have e' : a + 1 + d = a + (d + 1) := by omega
    have h1 := ih (n * ℓ.side) e' w.1
    have h2 : (e ▸ w : MarkedSample ℓ (a + (d + 1 + 1)) n).1 = (e' ▸ w.1 : MarkedSample ℓ (a + (d + 1)) (n * ℓ.side)) :=
      sample_fst_cast (a := a + 1 + d) (b := a + (d + 1)) e' e w
    show HEq (sampleBelow ℓ (a + 1) d (n * ℓ.side) w.1).1 (sampleBelow ℓ a (d + 1) (n * ℓ.side) (e ▸ w : MarkedSample ℓ (a + (d + 1 + 1)) n).1)
    rw [h2]
    exact h1
private theorem sampleBelow_heq_of_eq (a K n d d' : ℕ) (e₁ : K = a + 1 + d) (e₂ : K = a + d') (hd : d' = d + 1) (w : MarkedSample ℓ K n) :
    HEq (sampleBelow ℓ (a + 1) d n (e₁ ▸ w)).1 (sampleBelow ℓ a d' n (e₂ ▸ w)) := by
  subst hd
  subst e₁
  exact sampleBelow_fst_heq a d n e₂ w
end
section
variable {Λ : MomentParameters}
private theorem sideAtLevel_succ_mul (S : MomentPoint Λ) {a : ℕ} (h : a + 1 ≤ S.data.windowLevel) :
    S.sideAtLevel (a + 1) * Λ.stepParams.side = S.sideAtLevel a := by
  have e : S.data.windowLevel - a = S.data.windowLevel - (a + 1) + 1 := by omega
  show fineSide Λ.stepParams.side (S.data.windowLevel - (a + 1)) (S.data.period Λ.stepParams.side) * Λ.stepParams.side =
    fineSide Λ.stepParams.side (S.data.windowLevel - a) (S.data.period Λ.stepParams.side)
  rw [fineSide_eq, fineSide_eq, e, pow_succ]
  ring
private theorem sampleAtLevel_fst_heq (S : MomentPoint Λ) {a : ℕ} (h : a + 1 ≤ S.data.windowLevel) (h' : a ≤ S.data.windowLevel)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    HEq (S.sampleAtLevel (a + 1) h w).1 (S.sampleAtLevel a h' w) :=
  sampleBelow_heq_of_eq a S.data.windowLevel (S.data.period Λ.stepParams.side) (S.data.windowLevel - (a + 1)) (S.data.windowLevel - a) _ _ (by omega) w
private theorem sampleBelow_heq_sampleAtLevel (S : MomentPoint Λ) (a : ℕ) (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side))
    (ha : a ≤ S.data.windowLevel) :
    ∀ (d n : ℕ) (hd : a + d ≤ S.data.windowLevel) (x : MarkedSample Λ.stepParams (a + d) n), n = S.sideAtLevel (a + d) →
      HEq x (S.sampleAtLevel (a + d) hd w) → HEq (sampleBelow Λ.stepParams a d n x) (S.sampleAtLevel a ha w) := by
  intro d
  induction d with
  | zero =>
    intro n hd x hn hx
    exact hx
  | succ d ih =>
    intro n hd x hn hx
    have hd' : a + d + 1 ≤ S.data.windowLevel := hd
    subst hn
    obtain rfl := eq_of_heq hx
    exact ih (S.sideAtLevel (a + (d + 1)) * Λ.stepParams.side) (Nat.le_of_succ_le hd') _ (sideAtLevel_succ_mul S hd)
      (sampleAtLevel_fst_heq S hd (Nat.le_of_succ_le hd') w)
private theorem fineSide_sideAtLevel (S : MomentPoint Λ) (a d : ℕ) (hd : a + d ≤ S.data.windowLevel) :
    fineSide Λ.stepParams.side d (S.sideAtLevel (a + d)) = S.sideAtLevel a := by
  induction d with
  | zero => rfl
  | succ d ih =>
    show fineSide Λ.stepParams.side d (S.sideAtLevel (a + d + 1) * Λ.stepParams.side) = _
    rw [sideAtLevel_succ_mul S (by omega)]
    exact ih (by omega)
end
section
variable {ℓ : StepParameters}
private def levelSum (s : ℕ) (term : ∀ (i n : ℕ) [NeZero n], MarkedSample ℓ (s + i + 1) n → TorusSite (fineSide ℓ.side (i + 1) n) → ℝ) :
    (D n : ℕ) → [NeZero n] → MarkedSample ℓ (s + D) n → TorusSite (fineSide ℓ.side D n) → ℝ
  | 0, _, _, _, _ => 0
  | D + 1, n, _, x, o => levelSum s term D (n * ℓ.side) x.1 o + term D n x o
private theorem levelSum_nonneg (s : ℕ) {term : ∀ (i n : ℕ) [NeZero n], MarkedSample ℓ (s + i + 1) n → TorusSite (fineSide ℓ.side (i + 1) n) → ℝ}
    (h : ∀ (i n : ℕ) [NeZero n] x o, 0 ≤ term i n x o) :
    ∀ (D n : ℕ) [NeZero n] (x : MarkedSample ℓ (s + D) n) (o : TorusSite (fineSide ℓ.side D n)), 0 ≤ levelSum s term D n x o := by
  intro D
  induction D with
  | zero => intro n _ x o; exact le_rfl
  | succ D ih =>
    intro n _ x o
    exact add_nonneg (ih _ _ _) (h _ _ _ _)
end
section
variable {Λ : MomentParameters}
private theorem levelSum_congr (s : ℕ)
    (term : ∀ (i n : ℕ) [NeZero n], MarkedSample Λ.stepParams (s + i + 1) n → TorusSite (fineSide Λ.stepParams.side (i + 1) n) → ℝ)
    (oF : ∀ (D n : ℕ) [NeZero n], TorusSite (fineSide Λ.stepParams.side D n)) (D : ℕ) {n n' : ℕ} [NeZero n] [NeZero n'] (h : n = n')
    {x : MarkedSample Λ.stepParams (s + D) n} {x' : MarkedSample Λ.stepParams (s + D) n'} (hx : HEq x x') :
    levelSum s term D n x (oF D n) = levelSum s term D n' x' (oF D n') := by
  subst h
  obtain rfl := eq_of_heq hx
  rfl
private theorem levelSum_eq_sum (S : MomentPoint Λ) (s : ℕ)
    (term : ∀ (i n : ℕ) [NeZero n], MarkedSample Λ.stepParams (s + i + 1) n → TorusSite (fineSide Λ.stepParams.side (i + 1) n) → ℝ)
    (oF : ∀ (D n : ℕ) [NeZero n], TorusSite (fineSide Λ.stepParams.side D n))
    (hO : ∀ (D n : ℕ) [NeZero n], oF (D + 1) n = oF D (n * Λ.stepParams.side))
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    ∀ (D : ℕ) (hD : s + D ≤ S.data.windowLevel), levelSum s term D (S.sideAtLevel (s + D)) (S.sampleAtLevel (s + D) hD w) (oF D _) =
      ∑ i ∈ Finset.range D, if h : s + i + 1 ≤ S.data.windowLevel then
        term i (S.sideAtLevel (s + i + 1)) (S.sampleAtLevel (s + i + 1) h w) (oF (i + 1) _) else 0 := by
  intro D
  induction D with
  | zero =>
    intro hD
    simp [levelSum]
  | succ D ih =>
    intro hD
    have hD' : s + D + 1 ≤ S.data.windowLevel := hD
    rw [Finset.sum_range_succ, dif_pos hD', ← ih (by omega)]
    have e1 : levelSum s term D (S.sideAtLevel (s + D + 1) * Λ.stepParams.side) (S.sampleAtLevel (s + D + 1) hD' w).1
        (oF (D + 1) (S.sideAtLevel (s + D + 1))) =
        levelSum s term D (S.sideAtLevel (s + D)) (S.sampleAtLevel (s + D) (by omega) w) (oF D (S.sideAtLevel (s + D))) :=
      (congrArg (levelSum s term D (S.sideAtLevel (s + D + 1) * Λ.stepParams.side) (S.sampleAtLevel (s + D + 1) hD' w).1)
        (hO D (S.sideAtLevel (s + D + 1)))).trans
        (levelSum_congr s term oF D (sideAtLevel_succ_mul S hD') (sampleAtLevel_fst_heq S hD' (by omega) w))
    show levelSum s term D (S.sideAtLevel (s + D + 1) * Λ.stepParams.side) (S.sampleAtLevel (s + D + 1) hD' w).1
      (oF (D + 1) (S.sideAtLevel (s + D + 1))) + _ = _
    rw [e1]
    rfl
end
section
variable {ℓ : StepParameters}
private theorem finsetSupNonneg_le {α : Type} {S : Finset α} {f : α → ℝ} {c : ℝ} (h0 : 0 ≤ c) (h : ∀ b ∈ S, f b ≤ c) :
    finsetSupNonneg S f ≤ c :=
  (Finset.fold_max_le _).2 ⟨h0, h⟩
open Classical in
private def coldDeviation (T : StageTower ℓ) (j : ℕ) {n : ℕ} [NeZero n] (V : TorusField n) (W : TorusField (n * ℓ.side))
    (c : TorusSite n) (m : ℝ) (b : TorusBond (n * ℓ.side)) : ℍ[ℝ] :=
  if IsColdOnBall ℓ.threshold V c m then (stepDeviation T j V W b : ℍ[ℝ]) else 0
private def truncPowerTerm (T : StageTower ℓ) (s : ℕ) (m : ℝ) (q : ℕ) (nn ρ₀ : ℝ) (i n : ℕ) [NeZero n]
    (x : MarkedSample ℓ (s + i + 1) n) (o : TorusSite (fineSide ℓ.side (i + 1) n)) : ℝ :=
  ∑ b ∈ chartBondsInBlocks ℓ.side (supBall (siteAbove ℓ.side (i + 1) n o) ((ballRadius ℓ.side nn ρ₀ i + 1) / (ℓ.side : ℝ) + 2)),
    (1 : ℝ) * min ‖coldDeviation T (s + i) x.2.2.1 (topField ℓ (s + i) (n * ℓ.side) x.1) (siteAbove ℓ.side (i + 1) n o) m b‖ 1 ^ (2 * q)
private theorem truncPowerTerm_nonneg (T : StageTower ℓ) (s : ℕ) (m : ℝ) (q : ℕ) (nn ρ₀ : ℝ) (i n : ℕ) [NeZero n]
    (x : MarkedSample ℓ (s + i + 1) n) (o : TorusSite (fineSide ℓ.side (i + 1) n)) : 0 ≤ truncPowerTerm T s m q nn ρ₀ i n x o :=
  Finset.sum_nonneg fun _ _ => mul_nonneg zero_le_one (pow_nonneg (le_min (norm_nonneg _) zero_le_one) _)
private def coldFailureTerm (T : StageTower ℓ) (s : ℕ) (m : ℝ) (i n : ℕ) [NeZero n] (x : MarkedSample ℓ (s + i + 1) n)
    (o : TorusSite (fineSide ℓ.side (i + 1) n)) : ℝ :=
  open Classical in
  if IsColdOnBall ℓ.threshold x.2.2.1 (siteAbove ℓ.side (i + 1) n o) m ∧
      ∀ b ∈ chartBondsInBlocks ℓ.side (supBall (siteAbove ℓ.side (i + 1) n o) m),
        ‖(stepDeviation T (s + i) x.2.2.1 (topField ℓ (s + i) (n * ℓ.side) x.1) b : ℍ[ℝ])‖ < ℓ.threshold / 64 then 0 else 1
private theorem coldFailureTerm_nonneg (T : StageTower ℓ) (s : ℕ) (m : ℝ) (i n : ℕ) [NeZero n] (x : MarkedSample ℓ (s + i + 1) n)
    (o : TorusSite (fineSide ℓ.side (i + 1) n)) : 0 ≤ coldFailureTerm T s m i n x o := by
  unfold coldFailureTerm
  split_ifs <;> norm_num
private theorem levelSum_coldFailure_eq_zero (T : StageTower ℓ) (s : ℕ) (m : ℝ) :
    ∀ (D n : ℕ) [NeZero n] (x : MarkedSample ℓ (s + D) n) (o : TorusSite (fineSide ℓ.side D n)), coldAlongSteps T s m D n x o →
      levelSum s (fun i n _ x o => coldFailureTerm T s m i n x o) D n x o = 0 := by
  intro D
  induction D with
  | zero => intro n _ x o _; rfl
  | succ D ih =>
    intro n _ x o h
    obtain ⟨h1, h2, h3⟩ := h
    show levelSum s _ D (n * ℓ.side) x.1 o + coldFailureTerm T s m D n x o = 0
    rw [ih _ _ _ h3]
    unfold coldFailureTerm
    rw [if_pos ⟨h1, h2⟩, add_zero]
private theorem deviationsBoundedAlong_of_levelSum (T : StageTower ℓ) (s : ℕ) (m : ℝ) (q : ℕ) (hq : 1 ≤ q) (nn ρ₀ τ : ℝ)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    ∀ (D n : ℕ) [NeZero n] (x : MarkedSample ℓ (s + D) n) (o : TorusSite (fineSide ℓ.side D n)), coldAlongSteps T s m D n x o →
      levelSum s (fun i n _ x o => truncPowerTerm T s m q nn ρ₀ i n x o) D n x o < τ ^ (2 * q) →
        deviationsBoundedAlong T s nn ρ₀ τ D n x o := by
  intro D
  induction D with
  | zero => intro n _ x o _ _; trivial
  | succ D ih =>
    intro n _ x o h hs
    obtain ⟨h1, h2, h3⟩ := h
    have hs' : levelSum s (fun i n _ x o => truncPowerTerm T s m q nn ρ₀ i n x o) D (n * ℓ.side) x.1 o +
        truncPowerTerm T s m q nn ρ₀ D n x o < τ ^ (2 * q) := hs
    have p1 := levelSum_nonneg s (term := fun i n _ x o => truncPowerTerm T s m q nn ρ₀ i n x o)
      (fun i n _ x o => truncPowerTerm_nonneg T s m q nn ρ₀ i n x o) D (n * ℓ.side) x.1 o
    have p2 := truncPowerTerm_nonneg T s m q nn ρ₀ D n x o
    refine ⟨finsetSupNonneg_le hτ fun b hb => ?_, ih _ _ _ h3 (by linarith)⟩
    by_contra hb'
    push Not at hb'
    have e1 : coldDeviation T (s + D) x.2.2.1 (topField ℓ (s + D) (n * ℓ.side) x.1) (siteAbove ℓ.side (D + 1) n o) m b =
        (stepDeviation T (s + D) x.2.2.1 (topField ℓ (s + D) (n * ℓ.side) x.1) b : ℍ[ℝ]) := if_pos h1
    have h4 : τ ≤ min ‖coldDeviation T (s + D) x.2.2.1 (topField ℓ (s + D) (n * ℓ.side) x.1) (siteAbove ℓ.side (D + 1) n o) m b‖ 1 := by
      rw [e1]
      exact le_min hb'.le hτ1
    have h5 : τ ^ (2 * q) ≤ (1 : ℝ) *
        min ‖coldDeviation T (s + D) x.2.2.1 (topField ℓ (s + D) (n * ℓ.side) x.1) (siteAbove ℓ.side (D + 1) n o) m b‖ 1 ^ (2 * q) := by
      rw [one_mul]
      exact pow_le_pow_left₀ hτ h4 _
    have h6 := Finset.single_le_sum (f := fun b => (1 : ℝ) *
        min ‖coldDeviation T (s + D) x.2.2.1 (topField ℓ (s + D) (n * ℓ.side) x.1) (siteAbove ℓ.side (D + 1) n o) m b‖ 1 ^ (2 * q))
      (fun _ _ => mul_nonneg zero_le_one (pow_nonneg (le_min (norm_nonneg _) zero_le_one) _)) hb
    have h7 : (1 : ℝ) *
        min ‖coldDeviation T (s + D) x.2.2.1 (topField ℓ (s + D) (n * ℓ.side) x.1) (siteAbove ℓ.side (D + 1) n o) m b‖ 1 ^ (2 * q) ≤
        truncPowerTerm T s m q nn ρ₀ D n x o := h6
    linarith
open Classical in
private def siteHitTerm (T : StageTower ℓ) (s : ℕ) (m : ℝ) (i n : ℕ) [NeZero n] (x : MarkedSample ℓ (s + i + 1) n)
    (o : TorusSite (fineSide ℓ.side (i + 1) n)) : ℝ :=
  if (((show Finset (TorusBond (n * ℓ.side)) from x.2.2.2).image Prod.fst ∪ (stageState T (s + i) (n * ℓ.side) x.1).2.1) ∩
      thickening (4 * (T.stage (s + i)).toStepSetup.range)
        (sitesInBlocks ℓ.side (supBall (siteAbove ℓ.side (i + 1) n o) m))).Nonempty then 1 else 0
private theorem siteHitTerm_nonneg (T : StageTower ℓ) (s : ℕ) (m : ℝ) (i n : ℕ) [NeZero n] (x : MarkedSample ℓ (s + i + 1) n)
    (o : TorusSite (fineSide ℓ.side (i + 1) n)) : 0 ≤ siteHitTerm T s m i n x o := by
  classical
  unfold siteHitTerm
  split_ifs <;> norm_num
private theorem freeCoresAvoid_of_not_nonempty (R : StepSetup) {n : ℕ} [NeZero n] (Yt : Finset (TorusSite (n * R.params.side)))
    (bad : Finset (TorusBond (n * R.params.side))) (C Q : Finset (TorusSite n))
    (h : ¬ ((bad.image Prod.fst ∪ Yt) ∩ thickening (4 * R.range) (sitesInBlocks R.params.side Q)).Nonempty) :
    FreeCoresAvoid R Yt bad C Q := by
  classical
  intro X hX hfree
  rw [Finset.disjoint_left]
  intro y hy hyQ
  obtain ⟨s₀, hs₀⟩ := (Finset.mem_filter.mp hy).2
  obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hs₀
  obtain ⟨z, hzX, hd⟩ := (mem_thickening _ _ _).mp h2
  have hzA := subset_of_mem_chainComponents (r := 10 * R.range) hX hzX
  rcases Finset.mem_union.mp hzA with h3 | h3
  · refine h ⟨z, Finset.mem_inter.mpr ⟨h3, (mem_thickening _ _ _).mpr ⟨s₀, ?_, by rw [supDist_comm]; exact hd⟩⟩⟩
    have h4 : parentBlock R.params.side s₀ = y := by simpa using ClusterExpansionOfAStep.mem_sitesInBlocks.mp h1
    exact ClusterExpansionOfAStep.mem_sitesInBlocks.mpr (h4 ▸ hyQ)
  · exact hfree ⟨z, Finset.mem_inter.mpr ⟨hzX, h3⟩⟩
private theorem stepsAvoidOrigin_of_levelSum (T : StageTower ℓ) (s : ℕ) (m : ℝ) :
    ∀ (D n : ℕ) [NeZero n] (x : MarkedSample ℓ (s + D) n) (o : TorusSite (fineSide ℓ.side D n)),
      levelSum s (fun i n _ x o => siteHitTerm T s m i n x o) D n x o < 1 → StepsAvoidOrigin T s m D n x o := by
  classical
  intro D
  induction D with
  | zero => intro n _ x o _; trivial
  | succ D ih =>
    intro n _ x o hs
    have hs' : levelSum s (fun i n _ x o => siteHitTerm T s m i n x o) D (n * ℓ.side) x.1 o + siteHitTerm T s m D n x o < 1 := hs
    have p1 := levelSum_nonneg s (term := fun i n _ x o => siteHitTerm T s m i n x o)
      (fun i n _ x o => siteHitTerm_nonneg T s m i n x o) D (n * ℓ.side) x.1 o
    have p2 := siteHitTerm_nonneg T s m D n x o
    refine ⟨ih _ _ _ (by linarith), freeCoresAvoid_of_not_nonempty _ _ _ _ _ ?_⟩
    intro hne
    have e : siteHitTerm T s m D n x o = 1 := if_pos hne
    linarith
private def transportTerm (T : StageTower ℓ) (k : ℕ) (ρ₀ ρA : ℝ) (μ ν : Fin 4) (i n : ℕ) [NeZero n]
    (x : MarkedSample ℓ (k + i + 1) n) (o : TorusSite (fineSide ℓ.side (i + 1) n)) : ℝ :=
  ∑ b ∈ readBondsAtLevel ℓ 1 ρ₀ i n o,
    |adjointTransport ℓ.coupling ρA ℓ.side k i (n * ℓ.side) (curlFunctional ((o, μ, ν) : TorusPlaquette (fineSide ℓ.side (i + 1) n))) b| *
      ‖(stepDeviation T (k + i) x.2.2.1 (topField ℓ (k + i) (n * ℓ.side) x.1) b : ℍ[ℝ])‖
private def transportPowerTerm (T : StageTower ℓ) (k : ℕ) (m : ℝ) (q : ℕ) (ρ₀ ρA : ℝ) (μ ν : Fin 4) (i n : ℕ) [NeZero n]
    (x : MarkedSample ℓ (k + i + 1) n) (o : TorusSite (fineSide ℓ.side (i + 1) n)) : ℝ :=
  ∑ b ∈ readBondsAtLevel ℓ 1 ρ₀ i n o,
    |adjointTransport ℓ.coupling ρA ℓ.side k i (n * ℓ.side) (curlFunctional ((o, μ, ν) : TorusPlaquette (fineSide ℓ.side (i + 1) n))) b| *
      min ‖coldDeviation T (k + i) x.2.2.1 (topField ℓ (k + i) (n * ℓ.side) x.1) (siteAbove ℓ.side (i + 1) n o) m b‖ 1 ^ (2 * q)
private theorem deviationMass_eq_levelSum (T : StageTower ℓ) (k : ℕ) (ρ₀ ρA : ℝ) (μ ν : Fin 4) :
    ∀ (D n : ℕ) [NeZero n] (x : MarkedSample ℓ (k + D) n) (o : TorusSite (fineSide ℓ.side D n)),
      deviationMass T k 1 ρ₀ ρA D n x o (o, μ, ν) = levelSum k (fun i n _ x o => transportTerm T k ρ₀ ρA μ ν i n x o) D n x o := by
  intro D
  induction D with
  | zero => intro n _ x o; rfl
  | succ D ih =>
    intro n _ x o
    exact congrArg (fun t => t + transportTerm T k ρ₀ ρA μ ν D n x o) (ih (n * ℓ.side) x.1 o)
end
section
private theorem weighted_sum_pow_le {ι : Type} (s : Finset ι) (a t : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (ht : ∀ i ∈ s, 0 ≤ t i)
    (p : ℕ) (hp : 1 ≤ p) :
    (∑ i ∈ s, a i * t i) ^ p ≤ (∑ i ∈ s, a i) ^ (p - 1) * ∑ i ∈ s, a i * t i ^ p := by
  have hW0 : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg ha
  rcases hW0.eq_or_lt with hW | hW
  · have hz : ∀ i ∈ s, a i = 0 := (Finset.sum_eq_zero_iff_of_nonneg ha).1 hW.symm
    have e1 : ∑ i ∈ s, a i * t i = 0 := Finset.sum_eq_zero fun i hi => by rw [hz i hi, zero_mul]
    have e2 : ∑ i ∈ s, a i * t i ^ p = 0 := Finset.sum_eq_zero fun i hi => by rw [hz i hi, zero_mul]
    rw [e1, e2, mul_zero, zero_pow (by omega)]
  · set W := ∑ i ∈ s, a i with hWd
    have h1 := Real.pow_arith_mean_le_arith_mean_pow s (fun i => a i / W) t (fun i hi => div_nonneg (ha i hi) hW.le)
      (by rw [← Finset.sum_div]; exact div_self hW.ne') ht p
    have e1 : ∑ i ∈ s, a i / W * t i = (∑ i ∈ s, a i * t i) / W := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i ∈ s, a i / W * t i ^ p = (∑ i ∈ s, a i * t i ^ p) / W := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2, div_pow, div_le_div_iff₀ (pow_pos hW p) hW] at h1
    have e3 : W ^ p = W ^ (p - 1) * W := by
      rw [← pow_succ]
      congr 1
      omega
    rw [e3, ← mul_assoc] at h1
    refine le_of_mul_le_mul_right ?_ hW
    rw [mul_comm (W ^ (p - 1))]
    exact h1
private theorem geometric_sum_pow_le (M p : ℕ) (hp : 1 ≤ p) (f g : ℕ → ℝ) (hf : ∀ d < M, 0 ≤ f d) (hg : ∀ d < M, 0 ≤ g d)
    (h : ∀ d < M, f d ^ p ≤ (4 * (1 / 2) ^ d) ^ (p - 1) * g d) :
    (∑ d ∈ Finset.range M, f d) ^ p ≤ 8 ^ (p - 1) * ∑ d ∈ Finset.range M, g d := by
  have hw : ∀ d, (0 : ℝ) < (1 / 2) ^ (d + 1) := fun d => by positivity
  have e1 : ∑ d ∈ Finset.range M, f d = ∑ d ∈ Finset.range M, ((1 : ℝ) / 2) ^ (d + 1) * (f d / (1 / 2) ^ (d + 1)) :=
    Finset.sum_congr rfl fun d _ => by field_simp
  have h1 := weighted_sum_pow_le (Finset.range M) (fun d => ((1 : ℝ) / 2) ^ (d + 1)) (fun d => f d / (1 / 2) ^ (d + 1))
    (fun d _ => (hw d).le) (fun d hd => div_nonneg (hf d (Finset.mem_range.mp hd)) (hw d).le) p hp
  have hS : ∑ d ∈ Finset.range M, ((1 : ℝ) / 2) ^ (d + 1) ≤ 1 := by
    have : ∀ D : ℕ, ∑ d ∈ Finset.range D, ((1 : ℝ) / 2) ^ (d + 1) = 1 - (1 / 2) ^ D := by
      intro D
      induction D with
      | zero => simp
      | succ D ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        ring
    rw [this]
    have : (0 : ℝ) ≤ (1 / 2) ^ M := by positivity
    linarith
  have hS0 : 0 ≤ ∑ d ∈ Finset.range M, ((1 : ℝ) / 2) ^ (d + 1) := Finset.sum_nonneg fun d _ => (hw d).le
  have h2 : (∑ d ∈ Finset.range M, ((1 : ℝ) / 2) ^ (d + 1)) ^ (p - 1) ≤ 1 := pow_le_one₀ hS0 hS
  have h3 : ∀ d ∈ Finset.range M, (1 / 2 : ℝ) ^ (d + 1) * (f d / (1 / 2) ^ (d + 1)) ^ p ≤ 8 ^ (p - 1) * g d := by
    intro d hd
    have hdM := Finset.mem_range.mp hd
    have e2 : ((1 / 2 : ℝ) ^ (d + 1)) * (f d / (1 / 2) ^ (d + 1)) ^ p = f d ^ p * (2 ^ (d + 1)) ^ (p - 1) := by
      obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have hh : (2 : ℝ) ^ (d + 1) = ((1 / 2 : ℝ) ^ (d + 1))⁻¹ := by rw [one_div, inv_pow, inv_inv]
      rw [hh]
      have hne := (hw d).ne'
      generalize (1 / 2 : ℝ) ^ (d + 1) = hv at hne
      rw [div_pow, inv_pow, pow_succ hv]
      field_simp
    rw [e2]
    have h4 := mul_le_mul_of_nonneg_right (h d hdM) (by positivity : (0 : ℝ) ≤ (2 ^ (d + 1)) ^ (p - 1))
    refine h4.trans (le_of_eq ?_)
    have e3 : (4 * ((1 : ℝ) / 2) ^ d) * 2 ^ (d + 1) = 8 := by
      have e4 : ((1 : ℝ) / 2) ^ d * 2 ^ d = 1 := by
        rw [← mul_pow]
        norm_num
      rw [pow_succ]
      calc (4 * ((1 : ℝ) / 2) ^ d) * (2 ^ d * 2) = 8 * (((1 : ℝ) / 2) ^ d * 2 ^ d) := by ring
        _ = 8 := by rw [e4, mul_one]
    calc (4 * (1 / 2 : ℝ) ^ d) ^ (p - 1) * g d * (2 ^ (d + 1)) ^ (p - 1)
        = ((4 * (1 / 2 : ℝ) ^ d) ^ (p - 1) * (2 ^ (d + 1)) ^ (p - 1)) * g d := by ring
      _ = ((4 * (1 / 2 : ℝ) ^ d) * 2 ^ (d + 1)) ^ (p - 1) * g d := by rw [← mul_pow]
      _ = 8 ^ (p - 1) * g d := by rw [e3]
  rw [e1]
  have h5 := Finset.sum_le_sum h3
  rw [← Finset.mul_sum] at h5
  have hG : 0 ≤ ∑ d ∈ Finset.range M, ((1 : ℝ) / 2) ^ (d + 1) * (f d / (1 / 2) ^ (d + 1)) ^ p :=
    Finset.sum_nonneg fun d hd => mul_nonneg (hw d).le (pow_nonneg (div_nonneg (hf d (Finset.mem_range.mp hd)) (hw d).le) _)
  calc _ ≤ (∑ d ∈ Finset.range M, ((1 : ℝ) / 2) ^ (d + 1)) ^ (p - 1) *
        ∑ d ∈ Finset.range M, ((1 : ℝ) / 2) ^ (d + 1) * (f d / (1 / 2) ^ (d + 1)) ^ p := h1
    _ ≤ 1 * ∑ d ∈ Finset.range M, ((1 : ℝ) / 2) ^ (d + 1) * (f d / (1 / 2) ^ (d + 1)) ^ p := mul_le_mul_of_nonneg_right h2 hG
    _ ≤ _ := by rw [one_mul]; exact h5
end
section
variable {ℓ : StepParameters}
private theorem transportTerm_pow_le (T : StageTower ℓ) (k : ℕ) (m : ℝ) (q : ℕ) (hq : 1 ≤ q) (ρ₀ ρA : ℝ) (μ ν : Fin 4) (i n : ℕ)
    [NeZero n] (x : MarkedSample ℓ (k + i + 1) n) (o : TorusSite (fineSide ℓ.side (i + 1) n)) (hcold : coldFailureTerm T k m i n x o = 0)
    (hσ : ℓ.threshold / 64 ≤ 1)
    (hsub : readBondsAtLevel ℓ 1 ρ₀ i n o ⊆ chartBondsInBlocks ℓ.side (supBall (siteAbove ℓ.side (i + 1) n o) m)) (A : ℝ)
    (hw : ∑ b ∈ readBondsAtLevel ℓ 1 ρ₀ i n o,
      |adjointTransport ℓ.coupling ρA ℓ.side k i (n * ℓ.side) (curlFunctional ((o, μ, ν) : TorusPlaquette (fineSide ℓ.side (i + 1) n))) b| ≤ A) :
    transportTerm T k ρ₀ ρA μ ν i n x o ^ (2 * q) ≤ A ^ (2 * q - 1) * transportPowerTerm T k m q ρ₀ ρA μ ν i n x o := by
  classical
  have hc : IsColdOnBall ℓ.threshold x.2.2.1 (siteAbove ℓ.side (i + 1) n o) m ∧
      ∀ b ∈ chartBondsInBlocks ℓ.side (supBall (siteAbove ℓ.side (i + 1) n o) m),
        ‖(stepDeviation T (k + i) x.2.2.1 (topField ℓ (k + i) (n * ℓ.side) x.1) b : ℍ[ℝ])‖ < ℓ.threshold / 64 := by
    by_contra h
    unfold coldFailureTerm at hcold
    rw [if_neg h] at hcold
    norm_num at hcold
  have h1 := weighted_sum_pow_le (readBondsAtLevel ℓ 1 ρ₀ i n o)
    (fun b => |adjointTransport ℓ.coupling ρA ℓ.side k i (n * ℓ.side)
      (curlFunctional ((o, μ, ν) : TorusPlaquette (fineSide ℓ.side (i + 1) n))) b|)
    (fun b => ‖(stepDeviation T (k + i) x.2.2.1 (topField ℓ (k + i) (n * ℓ.side) x.1) b : ℍ[ℝ])‖)
    (fun _ _ => abs_nonneg _) (fun _ _ => norm_nonneg _) (2 * q) (by omega)
  have e1 : transportPowerTerm T k m q ρ₀ ρA μ ν i n x o = ∑ b ∈ readBondsAtLevel ℓ 1 ρ₀ i n o,
      |adjointTransport ℓ.coupling ρA ℓ.side k i (n * ℓ.side) (curlFunctional ((o, μ, ν) : TorusPlaquette (fineSide ℓ.side (i + 1) n))) b| *
        ‖(stepDeviation T (k + i) x.2.2.1 (topField ℓ (k + i) (n * ℓ.side) x.1) b : ℍ[ℝ])‖ ^ (2 * q) := by
    refine Finset.sum_congr rfl fun b hb => ?_
    have e2 : coldDeviation T (k + i) x.2.2.1 (topField ℓ (k + i) (n * ℓ.side) x.1) (siteAbove ℓ.side (i + 1) n o) m b =
        (stepDeviation T (k + i) x.2.2.1 (topField ℓ (k + i) (n * ℓ.side) x.1) b : ℍ[ℝ]) := if_pos hc.1
    rw [e2, min_eq_left ((hc.2 b (hsub hb)).le.trans hσ)]
  rw [e1]
  refine h1.trans (mul_le_mul_of_nonneg_right ?_
    (Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (pow_nonneg (norm_nonneg _) _)))
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) hw _
end
section
variable {Λ : MomentParameters}
private def lowerSite (S : MomentPoint Λ) (u : ℕ) (z : Fin 4 → ℤ) (D n : ℕ) [NeZero n] : TorusSite (fineSide Λ.stepParams.side D n) :=
  S.originSite u (fineSide Λ.stepParams.side D n) + siteOfInt z
private def upperSite (S : MomentPoint Λ) (u M : ℕ) (z : Fin 4 → ℤ) (D n : ℕ) [NeZero n] : TorusSite (fineSide Λ.stepParams.side D n) :=
  siteAbove Λ.stepParams.side M (fineSide Λ.stepParams.side D n) (lowerSite S u z M (fineSide Λ.stepParams.side D n))
private def lowerCentre (u : ℕ) (z : Fin 4 → ℤ) (i : ℕ) (S : MomentPoint Λ) : TorusSite (S.sideAtLevel (u + i + 1)) :=
  siteAbove Λ.stepParams.side (i + 1) _ (lowerSite S u z (i + 1) (S.sideAtLevel (u + i + 1)))
private def upperCentre (u M : ℕ) (z : Fin 4 → ℤ) (i : ℕ) (S : MomentPoint Λ) : TorusSite (S.sideAtLevel (u + M + i + 1)) :=
  siteAbove Λ.stepParams.side (i + 1) _ (upperSite S u M z (i + 1) (S.sideAtLevel (u + M + i + 1)))
private def lowerBonds (u : ℕ) (z : Fin 4 → ℤ) (i : ℕ) (S : MomentPoint Λ) :
    Finset (TorusBond (S.sideAtLevel (u + i + 1) * Λ.stepParams.side)) :=
  readBondsAtLevel Λ.stepParams 1 (localLogScale Λ.stepParams S.β u) i _ (lowerSite S u z (i + 1) (S.sideAtLevel (u + i + 1)))
private def lowerWeight (u : ℕ) (z : Fin 4 → ℤ) (μ ν : Fin 4) (i : ℕ) (S : MomentPoint Λ)
    (b : TorusBond (S.sideAtLevel (u + i + 1) * Λ.stepParams.side)) : ℝ :=
  |adjointTransport Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side u i (S.sideAtLevel (u + i + 1) * Λ.stepParams.side)
    (curlFunctional ((lowerSite S u z (i + 1) (S.sideAtLevel (u + i + 1)), μ, ν) :
      TorusPlaquette (fineSide Λ.stepParams.side (i + 1) (S.sideAtLevel (u + i + 1))))) b|
private def lowerMaxBonds (u : ℕ) (z : Fin 4 → ℤ) (i : ℕ) (S : MomentPoint Λ) :
    Finset (TorusBond (S.sideAtLevel (u + i + 1) * Λ.stepParams.side)) :=
  chartBondsInBlocks Λ.stepParams.side (supBall (lowerCentre u z i S)
    ((ballRadius Λ.stepParams.side 1 (localLogScale Λ.stepParams S.β u) i + 1) / (Λ.stepParams.side : ℝ) + 2))
private def upperMaxBonds (u M : ℕ) (z : Fin 4 → ℤ) (i : ℕ) (S : MomentPoint Λ) :
    Finset (TorusBond (S.sideAtLevel (u + M + i + 1) * Λ.stepParams.side)) :=
  chartBondsInBlocks Λ.stepParams.side (supBall (upperCentre u M z i S)
    ((ballRadius Λ.stepParams.side (1 / (Λ.stepParams.side : ℝ) ^ M) (localLogScale Λ.stepParams S.β u) i + 1) /
      (Λ.stepParams.side : ℝ) + 2))
private def lowerSites (u : ℕ) (z : Fin 4 → ℤ) (i : ℕ) (S : MomentPoint Λ) :
    Finset (TorusSite (S.sideAtLevel (u + i + 1) * Λ.stepParams.side)) :=
  thickening (4 * (S.tower.stage (u + i)).toStepSetup.range)
    (sitesInBlocks Λ.stepParams.side (supBall (lowerCentre u z i S) (localBlockSide Λ.stepParams S.β u)))
private def upperSites (u M : ℕ) (z : Fin 4 → ℤ) (i : ℕ) (S : MomentPoint Λ) :
    Finset (TorusSite (S.sideAtLevel (u + M + i + 1) * Λ.stepParams.side)) :=
  thickening (4 * (S.tower.stage (u + M + i)).toStepSetup.range)
    (sitesInBlocks Λ.stepParams.side (supBall (upperCentre u M z i S) (localBlockSide Λ.stepParams S.β u)))
private def transportPowerObs (u : ℕ) (z : Fin 4 → ℤ) (μ ν : Fin 4) (q i : ℕ) : SampleObservable Λ :=
  caseObservable (u + i) (truncatedDeviationCases u (u + i) q (lowerCentre u z i) (lowerBonds u z i) (lowerWeight u z μ ν i))
private def lowerMaxObs (u : ℕ) (z : Fin 4 → ℤ) (q i : ℕ) : SampleObservable Λ :=
  caseObservable (u + i) (truncatedDeviationCases u (u + i) q (lowerCentre u z i) (lowerMaxBonds u z i) (fun _ _ => 1))
private def upperMaxObs (u M : ℕ) (z : Fin 4 → ℤ) (q i : ℕ) : SampleObservable Λ :=
  caseObservable (u + M + i) (truncatedDeviationCases u (u + M + i) q (upperCentre u M z i) (upperMaxBonds u M z i) (fun _ _ => 1))
private def lowerSiteObs (u : ℕ) (z : Fin 4 → ℤ) (i : ℕ) : SampleObservable Λ :=
  caseObservable (u + i) (badOrSupportSiteCase (u + i) (lowerSites u z i))
private def upperSiteObs (u M : ℕ) (z : Fin 4 → ℤ) (i : ℕ) : SampleObservable Λ :=
  caseObservable (u + M + i) (badOrSupportSiteCase (u + M + i) (upperSites u M z i))
variable (S : MomentPoint Λ) (u : ℕ) (z : Fin 4 → ℤ) (μ ν : Fin 4)
  (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side))
private theorem transportPowerObs_eq (q i : ℕ) : transportPowerObs u z μ ν q i S w = if h : u + i + 1 ≤ S.data.windowLevel then
    transportPowerTerm S.tower u (localBlockSide Λ.stepParams S.β u) q (localLogScale Λ.stepParams S.β u) Λ.table.ρA μ ν i
      (S.sideAtLevel (u + i + 1)) (S.sampleAtLevel (u + i + 1) h w) (lowerSite S u z (i + 1) (S.sideAtLevel (u + i + 1))) else 0 := rfl
private theorem lowerMaxObs_eq (q i : ℕ) : lowerMaxObs u z q i S w = if h : u + i + 1 ≤ S.data.windowLevel then
    truncPowerTerm S.tower u (localBlockSide Λ.stepParams S.β u) q 1 (localLogScale Λ.stepParams S.β u) i (S.sideAtLevel (u + i + 1))
      (S.sampleAtLevel (u + i + 1) h w) (lowerSite S u z (i + 1) (S.sideAtLevel (u + i + 1))) else 0 := rfl
private theorem upperMaxObs_eq (M q i : ℕ) : upperMaxObs u M z q i S w = if h : u + M + i + 1 ≤ S.data.windowLevel then
    truncPowerTerm S.tower (u + M) (localBlockSide Λ.stepParams S.β u) q (1 / (Λ.stepParams.side : ℝ) ^ M)
      (localLogScale Λ.stepParams S.β u) i (S.sideAtLevel (u + M + i + 1))
      (S.sampleAtLevel (u + M + i + 1) h w) (upperSite S u M z (i + 1) (S.sideAtLevel (u + M + i + 1))) else 0 := rfl
private theorem lowerSiteObs_eq (i : ℕ) : lowerSiteObs u z i S w = if h : u + i + 1 ≤ S.data.windowLevel then
    siteHitTerm S.tower u (localBlockSide Λ.stepParams S.β u) i (S.sideAtLevel (u + i + 1)) (S.sampleAtLevel (u + i + 1) h w)
      (lowerSite S u z (i + 1) (S.sideAtLevel (u + i + 1))) else 0 := rfl
private theorem upperSiteObs_eq (M i : ℕ) : upperSiteObs u M z i S w = if h : u + M + i + 1 ≤ S.data.windowLevel then
    siteHitTerm S.tower (u + M) (localBlockSide Λ.stepParams S.β u) i (S.sideAtLevel (u + M + i + 1))
      (S.sampleAtLevel (u + M + i + 1) h w) (upperSite S u M z (i + 1) (S.sideAtLevel (u + M + i + 1))) else 0 := rfl
end
section
variable {Λ : MomentParameters}
private theorem supDist_parentBlock_originSite_le_one {Λ : MomentParameters} (S : MomentPoint Λ) (hodd : Odd Λ.stepParams.side)
    (u n : ℕ) [NeZero n] :
    TorusFields.supDist (parentBlock Λ.stepParams.side (S.originSite u (n * Λ.stepParams.side))) (S.originSite (u + 1) n) ≤ 1 := by
  obtain ⟨H, hH⟩ := hodd
  have hLpos : (0 : ℝ) < (Λ.stepParams.side : ℝ) := by
    have : 0 < Λ.stepParams.side := by omega
    exact_mod_cast this
  set z : Fin 4 → ℝ := fun a => S.data.center a * (Λ.stepParams.side : ℝ) ^ S.data.windowLevel / (Λ.stepParams.side : ℝ) ^ u with hz
  obtain ⟨kk, o₁, ho, hdec⟩ := exists_block_offset (L := Λ.stepParams.side) ⟨H, hH⟩ fun a => round (z a)
  have e1 : S.originSite u (n * Λ.stepParams.side) = siteOfInt (blockPoint Λ.stepParams.side kk o₁) := by
    funext a
    have := hdec a
    simp only [MomentPoint.originSite, siteOfInt, blockPoint]
    rw [← this]
  rw [e1, parentBlock_blockPoint ⟨H, hH⟩ kk o₁ ho]
  have e2 : S.originSite (u + 1) n = siteOfInt fun a => round (z a / (Λ.stepParams.side : ℝ)) := by
    funext a
    have e : S.data.center a * (Λ.stepParams.side : ℝ) ^ S.data.windowLevel / (Λ.stepParams.side : ℝ) ^ (u + 1) =
        z a / (Λ.stepParams.side : ℝ) := by
      simp only [hz]
      rw [pow_succ, div_div]
    simp only [MomentPoint.originSite, siteOfInt]
    rw [e]
  rw [e2, supDist_comm]
  have e3 : (siteOfInt kk : TorusSite n) = siteOfInt (fun a => round (z a / (Λ.stepParams.side : ℝ))) +
      siteOfInt (fun a => kk a - round (z a / (Λ.stepParams.side : ℝ))) := by
    funext a
    simp [siteOfInt]
  rw [e3]
  refine supDist_add_siteOfInt_le _ _ 1 fun a => ?_
  have hc := (mem_centredCube_iff o₁).mp ho a
  have hLH : ((Λ.stepParams.side : ℤ) - 1) / 2 = (H : ℤ) := by
    rw [hH]
    push_cast
    omega
  rw [hLH] at hc
  have h1 := abs_sub_round (z a)
  have h2 := abs_sub_round (z a / (Λ.stepParams.side : ℝ))
  have hd := hdec a
  have hd' : ((round (z a) : ℤ) : ℝ) = (Λ.stepParams.side : ℝ) * kk a + o₁ a := by exact_mod_cast hd
  have hLr : (Λ.stepParams.side : ℝ) = 2 * H + 1 := by exact_mod_cast hH
  have hc1 : -(H : ℝ) ≤ o₁ a := by exact_mod_cast hc.1
  have hc2 : (o₁ a : ℝ) ≤ H := by exact_mod_cast hc.2
  rw [hd'] at h1
  have hk : |(kk a : ℝ) - z a / (Λ.stepParams.side : ℝ)| ≤ 1 / 2 := by
    have e : (kk a : ℝ) - z a / (Λ.stepParams.side : ℝ) = ((Λ.stepParams.side : ℝ) * kk a - z a) / (Λ.stepParams.side : ℝ) := by
      field_simp
    rw [e, abs_div, abs_of_pos hLpos, div_le_iff₀ hLpos]
    have a1 := abs_le.1 h1
    rw [abs_le]
    constructor <;> [skip; skip] <;> linarith [a1.1, a1.2]
  have hfin : |(kk a : ℝ) - ((round (z a / (Λ.stepParams.side : ℝ)) : ℤ) : ℝ)| ≤ 1 := by
    have a1 := abs_le.1 hk
    have a2 := abs_le.1 h2
    rw [abs_le]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  have hint : |kk a - round (z a / (Λ.stepParams.side : ℝ))| ≤ 1 := by
    have : ((|kk a - round (z a / (Λ.stepParams.side : ℝ))| : ℤ) : ℝ) ≤ 1 := by
      push_cast
      exact hfin
    exact_mod_cast this
  have := abs_le.1 hint
  omega
abbrev _root_.YangMills.SharedProofs.p63379 := @supDist_parentBlock_originSite_le_one
private theorem supDist_siteAbove_originSite_le (S : MomentPoint Λ) (hodd : Odd Λ.stepParams.side) (hL2 : 2 ≤ Λ.stepParams.side)
    (a : ℕ) (t : ℕ) (ht : 3 ≤ t) :
    ∀ (d n : ℕ) [NeZero n] (y : TorusSite (fineSide Λ.stepParams.side d n)),
      TorusFields.supDist y (S.originSite a (fineSide Λ.stepParams.side d n)) ≤ t →
        TorusFields.supDist (siteAbove Λ.stepParams.side d n y) (S.originSite (a + d) n) ≤ t := by
  intro d
  induction d with
  | zero =>
    intro n _ y h
    exact h
  | succ d ih =>
    intro n _ y h
    have h1 := ih (n * Λ.stepParams.side) y h
    have t1 := supDist_triangle (parentBlock Λ.stepParams.side (siteAbove Λ.stepParams.side d (n * Λ.stepParams.side) y))
      (parentBlock Λ.stepParams.side (S.originSite (a + d) (n * Λ.stepParams.side))) (S.originSite (a + d + 1) n)
    have t2 := supDist_parentBlock_le_div_add_one Λ.stepParams.side (siteAbove Λ.stepParams.side d (n * Λ.stepParams.side) y)
      (S.originSite (a + d) (n * Λ.stepParams.side))
    have t3 := supDist_parentBlock_originSite_le_one S hodd (a + d) n
    have t4 : TorusFields.supDist (siteAbove Λ.stepParams.side d (n * Λ.stepParams.side) y) (S.originSite (a + d) (n * Λ.stepParams.side)) /
        Λ.stepParams.side ≤ t / 2 :=
      (Nat.div_le_div_right h1).trans (Nat.div_le_div_left hL2 (by norm_num))
    show TorusFields.supDist (parentBlock Λ.stepParams.side (siteAbove Λ.stepParams.side d (n * Λ.stepParams.side) y))
      (S.originSite (a + d + 1) n) ≤ t
    omega
private theorem lowerSite_near (S : MomentPoint Λ) (u : ℕ) (z : Fin 4 → ℤ) (t : ℕ) (hz : ∀ a, (z a).natAbs ≤ t) (D n : ℕ) [NeZero n] :
    TorusFields.supDist (lowerSite S u z D n) (S.originSite u (fineSide Λ.stepParams.side D n)) ≤ t := by
  rw [supDist_comm]
  exact supDist_add_siteOfInt_le _ _ _ hz
private theorem upperSite_near (S : MomentPoint Λ) (hodd : Odd Λ.stepParams.side) (hL2 : 2 ≤ Λ.stepParams.side) (u M : ℕ)
    (z : Fin 4 → ℤ) (t : ℕ) (ht : 3 ≤ t) (hz : ∀ a, (z a).natAbs ≤ t) (D n : ℕ) [NeZero n] :
    TorusFields.supDist (upperSite S u M z D n) (S.originSite (u + M) (fineSide Λ.stepParams.side D n)) ≤ t :=
  supDist_siteAbove_originSite_le S hodd hL2 u t ht M _ _ (lowerSite_near S u z t hz M _)
private theorem lowerCentre_near (S : MomentPoint Λ) (hodd : Odd Λ.stepParams.side) (hL2 : 2 ≤ Λ.stepParams.side) (u : ℕ)
    (z : Fin 4 → ℤ) (t : ℕ) (ht : 3 ≤ t) (hz : ∀ a, (z a).natAbs ≤ t) (i : ℕ) :
    TorusFields.supDist (lowerCentre u z i S) (S.originSite (u + i + 1) (S.sideAtLevel (u + i + 1))) ≤ t :=
  supDist_siteAbove_originSite_le S hodd hL2 u t ht (i + 1) _ _ (lowerSite_near S u z t hz (i + 1) _)
private theorem upperCentre_near (S : MomentPoint Λ) (hodd : Odd Λ.stepParams.side) (hL2 : 2 ≤ Λ.stepParams.side) (u M : ℕ)
    (z : Fin 4 → ℤ) (t : ℕ) (ht : 3 ≤ t) (hz : ∀ a, (z a).natAbs ≤ t) (i : ℕ) :
    TorusFields.supDist (upperCentre u M z i S) (S.originSite (u + M + i + 1) (S.sideAtLevel (u + M + i + 1))) ≤ t :=
  supDist_siteAbove_originSite_le S hodd hL2 (u + M) t ht (i + 1) _ _ (upperSite_near S hodd hL2 u M z t ht hz (i + 1) _)
private theorem blockCentreSite_add_siteOfInt {n L : ℕ} [NeZero n] [NeZero L] (Y : TorusSite n) (e : Fin 4 → ℤ) :
    blockCentreSite L (Y + siteOfInt e) = blockCentreSite L Y + siteOfInt fun k => (L : ℤ) * e k := by
  funext k
  simp only [blockCentreSite, siteOfInt, Pi.add_apply]
  rw [← Int.cast_add, ZMod.intCast_eq_intCast_iff_dvd_sub]
  have h1 : (((Y k + ((e k : ℤ) : ZMod n)).cast : ℤ) : ZMod n) = (((Y k).cast + e k : ℤ) : ZMod n) := by
    simp
  obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
  refine ⟨c, ?_⟩
  push_cast
  linear_combination (L : ℤ) * hc
abbrev _root_.YangMills.SharedProofs.p20130 := @blockCentreSite_add_siteOfInt
private theorem supDist_blockCentreSite_le {n L : ℕ} [NeZero n] [NeZero L] (hodd : Odd L) (x : TorusSite (n * L)) (Y : TorusSite n) :
    TorusFields.supDist x (blockCentreSite L Y) ≤ L + L * TorusFields.supDist (parentBlock L x) Y := by
  haveI : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  obtain ⟨e, he, hb⟩ := exists_offset_of_supDist Y (parentBlock L x)
  have h1 : TorusFields.supDist x (blockCentreSite L (parentBlock L x)) ≤ L :=
    supDist_le_of_parentBlock_eq hodd (by rw [parentBlock_blockCentreSite hodd])
  have h2 : TorusFields.supDist (blockCentreSite L Y) (blockCentreSite L (parentBlock L x)) ≤ L * TorusFields.supDist (parentBlock L x) Y := by
    rw [he, blockCentreSite_add_siteOfInt, ← he]
    refine supDist_add_siteOfInt_le _ _ _ fun i => ?_
    rw [Int.natAbs_mul, Int.natAbs_natCast, supDist_comm (parentBlock L x) Y]
    exact Nat.mul_le_mul_left _ (hb i)
  have h3 := supDist_triangle x (blockCentreSite L (parentBlock L x)) (blockCentreSite L Y)
  rw [supDist_comm (blockCentreSite L (parentBlock L x)) (blockCentreSite L Y)] at h3
  omega
private theorem mem_supBall {n : ℕ} [NeZero n] {o x : TorusSite n} {r : ℝ} : x ∈ supBall o r ↔ (TorusFields.supDist x o : ℝ) ≤ r := by
  simp [supBall]
end
section
private theorem measurable_norm_of_measurableQuaternion {Ξ : Type} [MeasurableSpace Ξ] {f : Ξ → ℍ[ℝ]} (hf : MeasurableQuaternion f) :
    Measurable fun ξ => ‖f ξ‖ := by apply _root_.YangMills.SharedProofs.p6605 <;> assumption
private theorem measurable_sample_fst (ℓ : StepParameters) (h n : ℕ) : Measurable fun u : MarkedSample ℓ (h + 1) n => u.1 := by apply _root_.YangMills.SharedProofs.p1941 <;> assumption
private theorem measurable_topField (ℓ : StepParameters) : ∀ (s n : ℕ), Measurable (topField ℓ s n)
  | 0, _ => measurable_id
  | _ + 1, _ => measurable_fst.comp (measurable_snd.comp measurable_snd)
private theorem measurable_of_eq_comp {α β : Type} [MeasurableSpace α] [MeasurableSpace β] {g : β → ℝ} {f : α → β} {h : α → ℝ}
    (hg : Measurable g) (hf : Measurable f) (e : ∀ a, h a = g (f a)) : Measurable h := by
  have e' : h = g ∘ f := funext e
  rw [e']
  exact hg.comp hf
end
section
variable {Λ : MomentParameters}
private theorem markedSampleLaw_cast (T : StageTower Λ.stepParams) (β : ℝ) {K K' : ℕ} (h : K = K') (n : ℕ) [NeZero n] :
    Measurable (fun w : MarkedSample Λ.stepParams K n => (h ▸ w : MarkedSample Λ.stepParams K' n)) ∧
      (markedSampleLaw T β K n).map (fun w : MarkedSample Λ.stepParams K n => (h ▸ w : MarkedSample Λ.stepParams K' n)) =
        markedSampleLaw T β K' n := by apply _root_.YangMills.SharedProofs.p48114 <;> assumption
private structure SampleFacts (S : MomentPoint Λ) : Prop where
  measurable_stageState : ∀ (u n : ℕ) [NeZero n], Measurable (stageState S.tower u n)
  sampleBelow_map : ∀ (s d n : ℕ) [NeZero n], Measurable (sampleBelow Λ.stepParams s d n) ∧
    Measure.map (sampleBelow Λ.stepParams s d n) (markedSampleLaw S.tower S.β (s + d) n) =
      markedSampleLaw S.tower S.β s (fineSide Λ.stepParams.side d n)
  isProbability : ∀ (u n : ℕ) [NeZero n], IsProbabilityMeasure (markedSampleLaw S.tower S.β u n)
private theorem SampleFacts.sampleAtLevel_map {S : MomentPoint Λ} (h : SampleFacts S) (u : ℕ) (hu : u ≤ S.data.windowLevel) :
    Measurable (S.sampleAtLevel u hu) ∧
      (S.law S.data.windowLevel (S.data.period Λ.stepParams.side)).map (S.sampleAtLevel u hu) = S.law u (S.sideAtLevel u) := by
  have hc := markedSampleLaw_cast S.tower S.β (Nat.add_sub_of_le hu).symm (S.data.period Λ.stepParams.side)
  obtain ⟨m1, e1⟩ := h.sampleBelow_map u (S.data.windowLevel - u) (S.data.period Λ.stepParams.side)
  refine ⟨m1.comp hc.1, ?_⟩
  have e2 := Measure.map_map (μ := markedSampleLaw S.tower S.β S.data.windowLevel (S.data.period Λ.stepParams.side)) m1 hc.1
  rw [hc.2, e1] at e2
  exact e2.symm
private theorem SampleFacts.ae_sampleAtLevel {S : MomentPoint Λ} (h : SampleFacts S) (u : ℕ) (hu : u ≤ S.data.windowLevel)
    {p : MarkedSample Λ.stepParams u (S.sideAtLevel u) → Prop}
    (hp : ∀ᵐ x ∂(markedSampleLaw S.tower S.β u (S.sideAtLevel u)), p x) :
    ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)), p (S.sampleAtLevel u hu w) := by
  obtain ⟨m1, e1⟩ := h.sampleAtLevel_map u hu
  have hp' : ∀ᵐ x ∂(S.law u (S.sideAtLevel u)), p x := hp
  rw [← e1] at hp'
  exact ae_of_ae_map m1.aemeasurable hp'
private theorem curvature_le_two {m : ℕ} (W : TorusField m) (z : TorusSite m) (μ ν : Fin 4) : curvature W z μ ν ≤ 2 := by apply _root_.YangMills.SharedProofs.p28884 <;> assumption
private theorem curvature_nonneg {m : ℕ} (W : TorusField m) (z : TorusSite m) (μ ν : Fin 4) : 0 ≤ curvature W z μ ν := norm_nonneg _
private theorem stageState_fst (T : StageTower Λ.stepParams) : ∀ (s n : ℕ) [NeZero n] (u : MarkedSample Λ.stepParams s n),
    (stageState T s n u).1 = topField Λ.stepParams s n u
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem clearCurvaturePower_le (S : MomentPoint Λ) {u : ℕ} (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ) (μ ν : Fin 4) (q : ℕ)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    clearCurvaturePower u z μ ν q S w ≤ curvature (S.stateAtLevel u hu w).1 (S.siteAt u z) μ ν ^ (2 * q) := by
  classical
  unfold clearCurvaturePower
  rw [dif_pos hu]
  split_ifs
  · exact le_rfl
  · exact pow_nonneg (curvature_nonneg _ _ _ _) _
private theorem curvature_congr (S : MomentPoint Λ) (u : ℕ) (z : Fin 4 → ℤ) (μ ν : Fin 4) {n n' : ℕ} [NeZero n] [NeZero n'] (h : n = n')
    {x : MarkedSample Λ.stepParams u n} {x' : MarkedSample Λ.stepParams u n'} (hx : HEq x x') :
    curvature (topField Λ.stepParams u n x) (S.originSite u n + siteOfInt z) μ ν =
      curvature (topField Λ.stepParams u n' x') (S.originSite u n' + siteOfInt z) μ ν := by
  subst h
  obtain rfl := eq_of_heq hx
  rfl
private theorem largeHullIndicator_zero_eq (S : MomentPoint Λ) {u : ℕ} (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    largeHullIndicator u z 0 S w = (open Classical in if S.siteAt u z ∈ (S.stateAtLevel u hu w).2.1 then 1 else 0) := by apply _root_.YangMills.SharedProofs.p14364 <;> assumption
private theorem largeHullIndicator_zero_nonneg (S : MomentPoint Λ) (u : ℕ) (z : Fin 4 → ℤ)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) : 0 ≤ largeHullIndicator u z 0 S w := by apply _root_.YangMills.SharedProofs.p20972 <;> assumption
private theorem one_le_sum_largeHullIndicator (S : MomentPoint Λ) {u R : ℕ} (hu : u ≤ S.data.windowLevel)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side))
    (hC : ¬ Disjoint (S.stateAtLevel u hu w).2.1 (supBall (S.originSite u (S.sideAtLevel u)) (R : ℝ))) :
    1 ≤ ∑ z ∈ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(R : ℤ)) (R : ℤ)), largeHullIndicator u z 0 S w := by apply _root_.YangMills.SharedProofs.p56626 <;> assumption
variable (S : MomentPoint Λ) (u : ℕ)
private theorem lowerLevelSum_eq (z : Fin 4 → ℤ)
    (term : ∀ (i n : ℕ) [NeZero n], MarkedSample Λ.stepParams (u + i + 1) n → TorusSite (fineSide Λ.stepParams.side (i + 1) n) → ℝ)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side))
    (hK : u + (localChainDepth Λ.stepParams S.β u) + (localChainDepth Λ.stepParams S.β u) ≤ S.data.windowLevel) :
    levelSum u term (localChainDepth Λ.stepParams S.β u)
        (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
          (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)))
        (sampleBelow Λ.stepParams (u + (localChainDepth Λ.stepParams S.β u)) (localChainDepth Λ.stepParams S.β u)
          (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))
          (S.sampleAtLevel (u + (localChainDepth Λ.stepParams S.β u) + (localChainDepth Λ.stepParams S.β u)) hK w))
        (lowerSite S u z (localChainDepth Λ.stepParams S.β u) (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
          (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)))) =
      ∑ i ∈ Finset.range (localChainDepth Λ.stepParams S.β u), if h : u + i + 1 ≤ S.data.windowLevel then
        term i (S.sideAtLevel (u + i + 1)) (S.sampleAtLevel (u + i + 1) h w) (lowerSite S u z (i + 1) (S.sideAtLevel (u + i + 1)))
      else 0 := by
  have hd : u + (localChainDepth Λ.stepParams S.β u) ≤ S.data.windowLevel := by omega
  have e1 := levelSum_congr u term (fun D n _ => lowerSite S u z D n) (localChainDepth Λ.stepParams S.β u)
    (fineSide_sideAtLevel S (u + (localChainDepth Λ.stepParams S.β u)) (localChainDepth Λ.stepParams S.β u) hK)
    (sampleBelow_heq_sampleAtLevel S (u + (localChainDepth Λ.stepParams S.β u)) w hd (localChainDepth Λ.stepParams S.β u)
      (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) hK
      (S.sampleAtLevel (u + (localChainDepth Λ.stepParams S.β u) + (localChainDepth Λ.stepParams S.β u)) hK w) rfl HEq.rfl)
  exact e1.trans (levelSum_eq_sum S u term (fun D n _ => lowerSite S u z D n) (fun _ _ _ => rfl) w
    (localChainDepth Λ.stepParams S.β u) hd)
private theorem upperLevelSum_eq (z : Fin 4 → ℤ)
    (term : ∀ (i n : ℕ) [NeZero n], MarkedSample Λ.stepParams (u + (localChainDepth Λ.stepParams S.β u) + i + 1) n →
      TorusSite (fineSide Λ.stepParams.side (i + 1) n) → ℝ)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side))
    (hK : u + (localChainDepth Λ.stepParams S.β u) + (localChainDepth Λ.stepParams S.β u) ≤ S.data.windowLevel) :
    levelSum (u + (localChainDepth Λ.stepParams S.β u)) term (localChainDepth Λ.stepParams S.β u)
        (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))
        (S.sampleAtLevel (u + (localChainDepth Λ.stepParams S.β u) + (localChainDepth Λ.stepParams S.β u)) hK w)
        (upperSite S u (localChainDepth Λ.stepParams S.β u) z (localChainDepth Λ.stepParams S.β u)
          (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) =
      ∑ i ∈ Finset.range (localChainDepth Λ.stepParams S.β u),
        if h : u + (localChainDepth Λ.stepParams S.β u) + i + 1 ≤ S.data.windowLevel then
          term i (S.sideAtLevel (u + (localChainDepth Λ.stepParams S.β u) + i + 1))
            (S.sampleAtLevel (u + (localChainDepth Λ.stepParams S.β u) + i + 1) h w)
            (upperSite S u (localChainDepth Λ.stepParams S.β u) z (i + 1)
              (S.sideAtLevel (u + (localChainDepth Λ.stepParams S.β u) + i + 1)))
        else 0 :=
  levelSum_eq_sum S (u + (localChainDepth Λ.stepParams S.β u)) term
    (fun D n _ => upperSite S u (localChainDepth Λ.stepParams S.β u) z D n) (fun _ _ _ => rfl) w (localChainDepth Λ.stepParams S.β u) hK
set_option maxHeartbeats 2000000 in
private theorem clearCurvaturePower_ae_le (z : Fin 4 → ℤ) (μ ν : Fin 4) (hμν : μ < ν) (q q₂ : ℕ) (hq : 1 ≤ q) (hq₂ : 1 ≤ q₂)
    (hK : u + (localChainDepth Λ.stepParams S.β u) + (localChainDepth Λ.stepParams S.β u) ≤ S.data.windowLevel) (C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (Rt : ℕ) (hσ : Λ.stepParams.threshold / 64 ≤ 1) (hx1 : 1 ≤ flowCouplings Λ.stepParams S.β u)
    (h₁ : ∀ᵐ x ∂(markedSampleLaw S.tower S.β (u + (localChainDepth Λ.stepParams S.β u) + (localChainDepth Λ.stepParams S.β u))
        (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))),
      IsLocalEvent S.tower u (localChainDepth Λ.stepParams S.β u) (localBlockSide Λ.stepParams S.β u)
          (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) x
          (lowerSite S u z (localChainDepth Λ.stepParams S.β u) (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)))) →
      IsGaugeSmallAlong S.tower u 1 (localLogScale Λ.stepParams S.β u) (flowCouplings Λ.stepParams S.β u ^ (-(1 / 4 : ℝ)))
          (localChainDepth Λ.stepParams S.β u)
          (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)))
          (sampleBelow Λ.stepParams (u + (localChainDepth Λ.stepParams S.β u)) (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) x)
          (lowerSite S u z (localChainDepth Λ.stepParams S.β u) (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))))
          (axialGaugeAt Λ.stepParams (topField Λ.stepParams (u + (localChainDepth Λ.stepParams S.β u))
              (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
                (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)))
              (sampleBelow Λ.stepParams (u + (localChainDepth Λ.stepParams S.β u)) (localChainDepth Λ.stepParams S.β u)
                (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) x))
            (siteAbove Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
              (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
                (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)))
              (lowerSite S u z (localChainDepth Λ.stepParams S.β u) (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
                (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)))))) →
      ∀ μ ν : Fin 4, μ < ν →
        curvature (topField Λ.stepParams u _ (sampleBelow Λ.stepParams u (localChainDepth Λ.stepParams S.β u) _
            (sampleBelow Λ.stepParams (u + (localChainDepth Λ.stepParams S.β u)) (localChainDepth Λ.stepParams S.β u)
              (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) x)))
          (lowerSite S u z (localChainDepth Λ.stepParams S.β u) (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)))) μ ν ≤
          deviationMass S.tower u 1 (localLogScale Λ.stepParams S.β u) Λ.table.ρA (localChainDepth Λ.stepParams S.β u)
              (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
                (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)))
              (sampleBelow Λ.stepParams (u + (localChainDepth Λ.stepParams S.β u)) (localChainDepth Λ.stepParams S.β u)
                (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) x)
              (lowerSite S u z (localChainDepth Λ.stepParams S.β u) (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
                (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))))
              (lowerSite S u z (localChainDepth Λ.stepParams S.β u) (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
                (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))), μ, ν) +
            C₁ * flowCouplings Λ.stepParams S.β u ^ (-(1 / 2 : ℝ)))
    (h₂ : ∀ᵐ x ∂(markedSampleLaw S.tower S.β (u + (localChainDepth Λ.stepParams S.β u) + (localChainDepth Λ.stepParams S.β u))
        (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))),
      IsLocalEvent S.tower u (localChainDepth Λ.stepParams S.β u) (localBlockSide Λ.stepParams S.β u)
          (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) x
          (lowerSite S u z (localChainDepth Λ.stepParams S.β u) (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)))) →
      coldAlongSteps S.tower (u + (localChainDepth Λ.stepParams S.β u)) (localBlockSide Λ.stepParams S.β u)
          (localChainDepth Λ.stepParams S.β u)
          (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) x
          (upperSite S u (localChainDepth Λ.stepParams S.β u) z (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) ∧
      coldAlongSteps S.tower u (localBlockSide Λ.stepParams S.β u) (localChainDepth Λ.stepParams S.β u)
          (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)))
          (sampleBelow Λ.stepParams (u + (localChainDepth Λ.stepParams S.β u)) (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) x)
          (lowerSite S u z (localChainDepth Λ.stepParams S.β u) (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)))) ∧
      (deviationsBoundedAlong S.tower (u + (localChainDepth Λ.stepParams S.β u))
          (1 / (Λ.stepParams.side : ℝ) ^ (localChainDepth Λ.stepParams S.β u)) (localLogScale Λ.stepParams S.β u)
          (flowCouplings Λ.stepParams S.β u ^ (-(1 / 3 : ℝ))) (localChainDepth Λ.stepParams S.β u)
          (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) x
          (upperSite S u (localChainDepth Λ.stepParams S.β u) z (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) →
        deviationsBoundedAlong S.tower u 1 (localLogScale Λ.stepParams S.β u) (flowCouplings Λ.stepParams S.β u ^ (-(1 / 3 : ℝ)))
          (localChainDepth Λ.stepParams S.β u)
          (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)))
          (sampleBelow Λ.stepParams (u + (localChainDepth Λ.stepParams S.β u)) (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) x)
          (lowerSite S u z (localChainDepth Λ.stepParams S.β u) (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)))) →
        IsGaugeSmallAlong S.tower u 1 (localLogScale Λ.stepParams S.β u) (flowCouplings Λ.stepParams S.β u ^ (-(1 / 4 : ℝ)))
          (localChainDepth Λ.stepParams S.β u)
          (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)))
          (sampleBelow Λ.stepParams (u + (localChainDepth Λ.stepParams S.β u)) (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) x)
          (lowerSite S u z (localChainDepth Λ.stepParams S.β u) (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))))
          (axialGaugeAt Λ.stepParams (topField Λ.stepParams (u + (localChainDepth Λ.stepParams S.β u))
              (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
                (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)))
              (sampleBelow Λ.stepParams (u + (localChainDepth Λ.stepParams S.β u)) (localChainDepth Λ.stepParams S.β u)
                (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) x))
            (siteAbove Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
              (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
                (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)))
              (lowerSite S u z (localChainDepth Λ.stepParams S.β u) (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
                (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))))))))
    (hrow : ∀ d < (localChainDepth Λ.stepParams S.β u),
      ∑ b ∈ readBondsAtLevel Λ.stepParams 1 (localLogScale Λ.stepParams S.β u) d (S.sideAtLevel (u + d + 1))
          (lowerSite S u z (d + 1) (S.sideAtLevel (u + d + 1))),
        |adjointTransport Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side u d (S.sideAtLevel (u + d + 1) * Λ.stepParams.side)
          (curlFunctional ((lowerSite S u z (d + 1) (S.sideAtLevel (u + d + 1)), μ, ν) :
            TorusPlaquette (fineSide Λ.stepParams.side (d + 1) (S.sideAtLevel (u + d + 1))))) b| ≤ 4 * (1 / 2) ^ d)
    (hsub : ∀ d < (localChainDepth Λ.stepParams S.β u),
      readBondsAtLevel Λ.stepParams 1 (localLogScale Λ.stepParams S.β u) d (S.sideAtLevel (u + d + 1))
          (lowerSite S u z (d + 1) (S.sideAtLevel (u + d + 1))) ⊆
        chartBondsInBlocks Λ.stepParams.side (supBall (lowerCentre u z d S) (localBlockSide Λ.stepParams S.β u)))
    (htop : supBall (siteAbove Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
          (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))
          (upperSite S u (localChainDepth Λ.stepParams S.β u) z (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))))
        (localBlockSide Λ.stepParams S.β u) ⊆
      supBall (S.originSite (u + (localChainDepth Λ.stepParams S.β u) + (localChainDepth Λ.stepParams S.β u))
        (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) (Rt : ℝ))
    (hL : SampleFacts S) :
    ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)), clearCurvaturePower u z μ ν q S w ≤
      16 ^ (2 * q) * ∑ d ∈ Finset.range (localChainDepth Λ.stepParams S.β u), transportPowerObs u z μ ν q d S w +
      (2 * (C₁ * flowCouplings Λ.stepParams S.β u ^ (-(1 / 2 : ℝ)))) ^ (2 * q) +
      4 ^ q * (((flowCouplings Λ.stepParams S.β u ^ (-(1 / 3 : ℝ))) ^ (2 * q₂))⁻¹ *
          ∑ i ∈ Finset.range (localChainDepth Λ.stepParams S.β u), lowerMaxObs u z q₂ i S w +
        ((flowCouplings Λ.stepParams S.β u ^ (-(1 / 3 : ℝ))) ^ (2 * q₂))⁻¹ *
          ∑ i ∈ Finset.range (localChainDepth Λ.stepParams S.β u), upperMaxObs u (localChainDepth Λ.stepParams S.β u) z q₂ i S w +
        ∑ i ∈ Finset.range (localChainDepth Λ.stepParams S.β u), lowerSiteObs u z i S w +
        ∑ i ∈ Finset.range (localChainDepth Λ.stepParams S.β u), upperSiteObs u (localChainDepth Λ.stepParams S.β u) z i S w +
        ∑ z' ∈ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(Rt : ℤ)) (Rt : ℤ)),
          largeHullIndicator (u + (localChainDepth Λ.stepParams S.β u) + (localChainDepth Λ.stepParams S.β u)) z' 0 S w) := by
  classical
  have hu : u ≤ S.data.windowLevel := by omega
  filter_upwards [hL.ae_sampleAtLevel (u + (localChainDepth Λ.stepParams S.β u) + (localChainDepth Λ.stepParams S.β u)) hK h₁,
    hL.ae_sampleAtLevel (u + (localChainDepth Λ.stepParams S.β u) + (localChainDepth Λ.stepParams S.β u)) hK h₂] with w a₁ a₂
  have hx0 : 0 < flowCouplings Λ.stepParams S.β u := by linarith
  set X := S.sampleAtLevel (u + (localChainDepth Λ.stepParams S.β u) + (localChainDepth Λ.stepParams S.β u)) hK w with hX
  set db := sampleBelow Λ.stepParams (u + (localChainDepth Λ.stepParams S.β u)) (localChainDepth Λ.stepParams S.β u)
    (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) X with hdb
  set o := lowerSite S u z (localChainDepth Λ.stepParams S.β u) (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
    (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) with ho
  set m : ℝ := (localBlockSide Λ.stepParams S.β u : ℝ) with hm
  set ρ₀ := localLogScale Λ.stepParams S.β u with hρ
  set τ := flowCouplings Λ.stepParams S.β u ^ (-(1 / 3 : ℝ)) with hτ
  have hτ0 : 0 < τ := Real.rpow_pos_of_pos hx0 _
  have hτ1 : τ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have hτp : 0 < τ ^ (2 * q₂) := pow_pos hτ0 _
  have eSL := lowerLevelSum_eq S u z (fun i n _ x o => siteHitTerm S.tower u m i n x o) w hK
  have eSH := upperLevelSum_eq S u z (fun i n _ x o => siteHitTerm S.tower (u + (localChainDepth Λ.stepParams S.β u)) m i n x o) w hK
  have eQL := lowerLevelSum_eq S u z (fun i n _ x o => truncPowerTerm S.tower u m q₂ 1 ρ₀ i n x o) w hK
  have eQH := upperLevelSum_eq S u z (fun i n _ x o => truncPowerTerm S.tower (u + (localChainDepth Λ.stepParams S.β u)) m q₂
    (1 / (Λ.stepParams.side : ℝ) ^ (localChainDepth Λ.stepParams S.β u)) ρ₀ i n x o) w hK
  have eCL := lowerLevelSum_eq S u z (fun i n _ x o => coldFailureTerm S.tower u m i n x o) w hK
  have eRL := lowerLevelSum_eq S u z (fun i n _ x o => transportTerm S.tower u ρ₀ Λ.table.ρA μ ν i n x o) w hK
  have sSL : ∑ i ∈ Finset.range (localChainDepth Λ.stepParams S.β u), lowerSiteObs u z i S w =
      levelSum u (fun i n _ x o => siteHitTerm S.tower u m i n x o) (localChainDepth Λ.stepParams S.β u)
        (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
          (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) db o := by
    rw [eSL]
    exact Finset.sum_congr rfl fun i _ => lowerSiteObs_eq S u z w i
  have sSH : ∑ i ∈ Finset.range (localChainDepth Λ.stepParams S.β u), upperSiteObs u (localChainDepth Λ.stepParams S.β u) z i S w =
      levelSum (u + (localChainDepth Λ.stepParams S.β u))
        (fun i n _ x o => siteHitTerm S.tower (u + (localChainDepth Λ.stepParams S.β u)) m i n x o) (localChainDepth Λ.stepParams S.β u)
        (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) X
        (upperSite S u (localChainDepth Λ.stepParams S.β u) z (localChainDepth Λ.stepParams S.β u)
          (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) := by
    rw [eSH]
    exact Finset.sum_congr rfl fun i _ => upperSiteObs_eq S u z w (localChainDepth Λ.stepParams S.β u) i
  have sQL : ∑ i ∈ Finset.range (localChainDepth Λ.stepParams S.β u), lowerMaxObs u z q₂ i S w =
      levelSum u (fun i n _ x o => truncPowerTerm S.tower u m q₂ 1 ρ₀ i n x o) (localChainDepth Λ.stepParams S.β u)
        (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
          (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) db o := by
    rw [eQL]
    exact Finset.sum_congr rfl fun i _ => lowerMaxObs_eq S u z w q₂ i
  have sQH : ∑ i ∈ Finset.range (localChainDepth Λ.stepParams S.β u), upperMaxObs u (localChainDepth Λ.stepParams S.β u) z q₂ i S w =
      levelSum (u + (localChainDepth Λ.stepParams S.β u))
        (fun i n _ x o => truncPowerTerm S.tower (u + (localChainDepth Λ.stepParams S.β u)) m q₂
          (1 / (Λ.stepParams.side : ℝ) ^ (localChainDepth Λ.stepParams S.β u)) ρ₀ i n x o) (localChainDepth Λ.stepParams S.β u)
        (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) X
        (upperSite S u (localChainDepth Λ.stepParams S.β u) z (localChainDepth Λ.stepParams S.β u)
          (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) := by
    rw [eQH]
    exact Finset.sum_congr rfl fun i _ => upperMaxObs_eq S u z w (localChainDepth Λ.stepParams S.β u) q₂ i
  have nSL : 0 ≤ levelSum u (fun i n _ x o => siteHitTerm S.tower u m i n x o) (localChainDepth Λ.stepParams S.β u)
      (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
        (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) db o :=
    levelSum_nonneg u (fun i n _ x o => siteHitTerm_nonneg S.tower u m i n x o) _ _ _ _
  have nSH : 0 ≤ levelSum (u + (localChainDepth Λ.stepParams S.β u))
      (fun i n _ x o => siteHitTerm S.tower (u + (localChainDepth Λ.stepParams S.β u)) m i n x o) (localChainDepth Λ.stepParams S.β u)
      (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) X
      (upperSite S u (localChainDepth Λ.stepParams S.β u) z (localChainDepth Λ.stepParams S.β u)
        (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) :=
    levelSum_nonneg _ (fun i n _ x o => siteHitTerm_nonneg S.tower (u + (localChainDepth Λ.stepParams S.β u)) m i n x o) _ _ _ _
  have nQL : 0 ≤ levelSum u (fun i n _ x o => truncPowerTerm S.tower u m q₂ 1 ρ₀ i n x o) (localChainDepth Λ.stepParams S.β u)
      (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
        (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) db o :=
    levelSum_nonneg u (fun i n _ x o => truncPowerTerm_nonneg S.tower u m q₂ 1 ρ₀ i n x o) _ _ _ _
  have nQH : 0 ≤ levelSum (u + (localChainDepth Λ.stepParams S.β u))
      (fun i n _ x o => truncPowerTerm S.tower (u + (localChainDepth Λ.stepParams S.β u)) m q₂
        (1 / (Λ.stepParams.side : ℝ) ^ (localChainDepth Λ.stepParams S.β u)) ρ₀ i n x o) (localChainDepth Λ.stepParams S.β u)
      (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) X
      (upperSite S u (localChainDepth Λ.stepParams S.β u) z (localChainDepth Λ.stepParams S.β u)
        (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) :=
    levelSum_nonneg _ (fun i n _ x o => truncPowerTerm_nonneg S.tower (u + (localChainDepth Λ.stepParams S.β u)) m q₂
      (1 / (Λ.stepParams.side : ℝ) ^ (localChainDepth Λ.stepParams S.β u)) ρ₀ i n x o) _ _ _ _
  have nH : 0 ≤ ∑ z' ∈ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(Rt : ℤ)) (Rt : ℤ)),
      largeHullIndicator (u + (localChainDepth Λ.stepParams S.β u) + (localChainDepth Λ.stepParams S.β u)) z' 0 S w :=
    Finset.sum_nonneg fun z' _ => largeHullIndicator_zero_nonneg S _ _ _
  have nP : 0 ≤ ∑ d ∈ Finset.range (localChainDepth Λ.stepParams S.β u), transportPowerObs u z μ ν q d S w :=
    Finset.sum_nonneg fun d _ => by
      rw [transportPowerObs_eq]
      split_ifs
      · exact Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (pow_nonneg (le_min (norm_nonneg _) zero_le_one) _)
      · exact le_rfl
  have hcinv : 0 ≤ (τ ^ (2 * q₂))⁻¹ := (inv_pos.mpr hτp).le
  have hlast : 0 ≤ (2 * (C₁ * flowCouplings Λ.stepParams S.β u ^ (-(1 / 2 : ℝ)))) ^ (2 * q) :=
    pow_nonneg (mul_nonneg zero_le_two (mul_nonneg hC₁ (Real.rpow_nonneg hx0.le _))) _
  rw [sSL, sSH, sQL, sQH]
  have h4 : (0 : ℝ) < 4 ^ q := by positivity
  have hoff := clearCurvaturePower_le S hu z μ ν q w
  have hcurv2 : curvature (S.stateAtLevel u hu w).1 (S.siteAt u z) μ ν ^ (2 * q) ≤ 4 ^ q := by
    have := pow_le_pow_left₀ (curvature_nonneg _ _ _ _) (curvature_le_two (S.stateAtLevel u hu w).1 (S.siteAt u z) μ ν) (2 * q)
    have e : (2 : ℝ) ^ (2 * q) = 4 ^ q := by
      rw [pow_mul]
      norm_num
    exact this.trans e.le
  have htriv : 1 ≤ (τ ^ (2 * q₂))⁻¹ * levelSum u (fun i n _ x o => truncPowerTerm S.tower u m q₂ 1 ρ₀ i n x o)
          (localChainDepth Λ.stepParams S.β u) (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) db o +
        (τ ^ (2 * q₂))⁻¹ * levelSum (u + (localChainDepth Λ.stepParams S.β u))
          (fun i n _ x o => truncPowerTerm S.tower (u + (localChainDepth Λ.stepParams S.β u)) m q₂
            (1 / (Λ.stepParams.side : ℝ) ^ (localChainDepth Λ.stepParams S.β u)) ρ₀ i n x o) (localChainDepth Λ.stepParams S.β u)
          (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) X
          (upperSite S u (localChainDepth Λ.stepParams S.β u) z (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) +
        levelSum u (fun i n _ x o => siteHitTerm S.tower u m i n x o) (localChainDepth Λ.stepParams S.β u)
          (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) db o +
        levelSum (u + (localChainDepth Λ.stepParams S.β u))
          (fun i n _ x o => siteHitTerm S.tower (u + (localChainDepth Λ.stepParams S.β u)) m i n x o) (localChainDepth Λ.stepParams S.β u)
          (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) X
          (upperSite S u (localChainDepth Λ.stepParams S.β u) z (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) +
        ∑ z' ∈ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(Rt : ℤ)) (Rt : ℤ)),
          largeHullIndicator (u + (localChainDepth Λ.stepParams S.β u) + (localChainDepth Λ.stepParams S.β u)) z' 0 S w →
      clearCurvaturePower u z μ ν q S w ≤
        16 ^ (2 * q) * ∑ d ∈ Finset.range (localChainDepth Λ.stepParams S.β u), transportPowerObs u z μ ν q d S w +
        (2 * (C₁ * flowCouplings Λ.stepParams S.β u ^ (-(1 / 2 : ℝ)))) ^ (2 * q) +
        4 ^ q * ((τ ^ (2 * q₂))⁻¹ * levelSum u (fun i n _ x o => truncPowerTerm S.tower u m q₂ 1 ρ₀ i n x o)
            (localChainDepth Λ.stepParams S.β u) (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
              (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) db o +
          (τ ^ (2 * q₂))⁻¹ * levelSum (u + (localChainDepth Λ.stepParams S.β u))
            (fun i n _ x o => truncPowerTerm S.tower (u + (localChainDepth Λ.stepParams S.β u)) m q₂
              (1 / (Λ.stepParams.side : ℝ) ^ (localChainDepth Λ.stepParams S.β u)) ρ₀ i n x o) (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) X
            (upperSite S u (localChainDepth Λ.stepParams S.β u) z (localChainDepth Λ.stepParams S.β u)
              (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) +
          levelSum u (fun i n _ x o => siteHitTerm S.tower u m i n x o) (localChainDepth Λ.stepParams S.β u)
            (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
              (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) db o +
          levelSum (u + (localChainDepth Λ.stepParams S.β u))
            (fun i n _ x o => siteHitTerm S.tower (u + (localChainDepth Λ.stepParams S.β u)) m i n x o) (localChainDepth Λ.stepParams S.β u)
            (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) X
            (upperSite S u (localChainDepth Λ.stepParams S.β u) z (localChainDepth Λ.stepParams S.β u)
              (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) +
          ∑ z' ∈ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(Rt : ℤ)) (Rt : ℤ)),
            largeHullIndicator (u + (localChainDepth Λ.stepParams S.β u) + (localChainDepth Λ.stepParams S.β u)) z' 0 S w) := by
    intro hone
    have e1 := mul_le_mul_of_nonneg_left hone h4.le
    have e2 : (0 : ℝ) ≤ 16 ^ (2 * q) * ∑ d ∈ Finset.range (localChainDepth Λ.stepParams S.β u), transportPowerObs u z μ ν q d S w :=
      mul_nonneg (by positivity) nP
    linarith
  by_cases hbad : 1 ≤ levelSum u (fun i n _ x o => siteHitTerm S.tower u m i n x o) (localChainDepth Λ.stepParams S.β u)
        (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
          (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) db o ∨
      1 ≤ levelSum (u + (localChainDepth Λ.stepParams S.β u))
        (fun i n _ x o => siteHitTerm S.tower (u + (localChainDepth Λ.stepParams S.β u)) m i n x o) (localChainDepth Λ.stepParams S.β u)
        (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) X
        (upperSite S u (localChainDepth Λ.stepParams S.β u) z (localChainDepth Λ.stepParams S.β u)
          (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) ∨
      1 ≤ ∑ z' ∈ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(Rt : ℤ)) (Rt : ℤ)),
        largeHullIndicator (u + (localChainDepth Λ.stepParams S.β u) + (localChainDepth Λ.stepParams S.β u)) z' 0 S w
  · refine htriv ?_
    have p1 := mul_nonneg hcinv nQL
    have p2 := mul_nonneg hcinv nQH
    rcases hbad with h | h | h <;> linarith
  push Not at hbad
  obtain ⟨b1, b2, b3⟩ := hbad
  have hlocal : IsLocalEvent S.tower u (localChainDepth Λ.stepParams S.β u) (localBlockSide Λ.stepParams S.β u)
      (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) X o := by
    refine ⟨?_, stepsAvoidOrigin_of_levelSum S.tower (u + (localChainDepth Λ.stepParams S.β u)) m (localChainDepth Λ.stepParams S.β u)
      (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) X _ b2,
      stepsAvoidOrigin_of_levelSum S.tower u m (localChainDepth Λ.stepParams S.β u) _ db o b1⟩
    by_contra hc
    have hc' : ¬ Disjoint (S.stateAtLevel (u + (localChainDepth Λ.stepParams S.β u) + (localChainDepth Λ.stepParams S.β u)) hK w).2.1
        (supBall (S.originSite (u + (localChainDepth Λ.stepParams S.β u) + (localChainDepth Λ.stepParams S.β u))
          (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) (Rt : ℝ)) := fun h =>
      hc (Finset.disjoint_of_subset_right htop h)
    have := one_le_sum_largeHullIndicator S hK w hc'
    linarith
  obtain ⟨c1, c2, c3⟩ := a₂ hlocal
  by_cases hmax : τ ^ (2 * q₂) ≤ levelSum u (fun i n _ x o => truncPowerTerm S.tower u m q₂ 1 ρ₀ i n x o)
        (localChainDepth Λ.stepParams S.β u) (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
          (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) db o ∨
      τ ^ (2 * q₂) ≤ levelSum (u + (localChainDepth Λ.stepParams S.β u))
        (fun i n _ x o => truncPowerTerm S.tower (u + (localChainDepth Λ.stepParams S.β u)) m q₂
          (1 / (Λ.stepParams.side : ℝ) ^ (localChainDepth Λ.stepParams S.β u)) ρ₀ i n x o) (localChainDepth Λ.stepParams S.β u)
        (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) X
        (upperSite S u (localChainDepth Λ.stepParams S.β u) z (localChainDepth Λ.stepParams S.β u)
          (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)))
  · refine htriv ?_
    have p1 := mul_nonneg hcinv nQL
    have p2 := mul_nonneg hcinv nQH
    have e1 : (τ ^ (2 * q₂))⁻¹ * τ ^ (2 * q₂) = 1 := inv_mul_cancel₀ hτp.ne'
    rcases hmax with h | h
    · have := mul_le_mul_of_nonneg_left h hcinv
      linarith
    · have := mul_le_mul_of_nonneg_left h hcinv
      linarith
  push Not at hmax
  obtain ⟨d1, d2⟩ := hmax
  have eL := deviationsBoundedAlong_of_levelSum S.tower u m q₂ hq₂ 1 ρ₀ τ hτ0.le hτ1 (localChainDepth Λ.stepParams S.β u) _ db o c2 d1
  have eH := deviationsBoundedAlong_of_levelSum S.tower (u + (localChainDepth Λ.stepParams S.β u)) m q₂ hq₂
    (1 / (Λ.stepParams.side : ℝ) ^ (localChainDepth Λ.stepParams S.β u)) ρ₀ τ hτ0.le hτ1 (localChainDepth Λ.stepParams S.β u)
    (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) X _ c1 d2
  have hsmall := c3 eH eL
  have hcurv := a₁ hlocal hsmall μ ν hμν
  have hcz : ∑ i ∈ Finset.range (localChainDepth Λ.stepParams S.β u), (if h : u + i + 1 ≤ S.data.windowLevel then
      coldFailureTerm S.tower u m i (S.sideAtLevel (u + i + 1)) (S.sampleAtLevel (u + i + 1) h w)
        (lowerSite S u z (i + 1) (S.sideAtLevel (u + i + 1))) else 0) = 0 := by
    rw [← eCL]
    exact levelSum_coldFailure_eq_zero S.tower u m (localChainDepth Λ.stepParams S.β u) _ db o c2
  have hcz' := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by
    split_ifs
    · exact coldFailureTerm_nonneg _ _ _ _ _ _ _
    · exact le_rfl)).1 hcz
  rw [deviationMass_eq_levelSum, eRL] at hcurv
  have hlev : ∀ d < (localChainDepth Λ.stepParams S.β u), u + d + 1 ≤ S.data.windowLevel := fun d hd => by omega
  have hpow := geometric_sum_pow_le (localChainDepth Λ.stepParams S.β u) (2 * q) (by omega)
    (fun d => if h : u + d + 1 ≤ S.data.windowLevel then transportTerm S.tower u ρ₀ Λ.table.ρA μ ν d (S.sideAtLevel (u + d + 1))
      (S.sampleAtLevel (u + d + 1) h w) (lowerSite S u z (d + 1) (S.sideAtLevel (u + d + 1))) else 0)
    (fun d => transportPowerObs u z μ ν q d S w)
    (fun d hd => by
      beta_reduce
      split_ifs
      · exact Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
      · exact le_rfl)
    (fun d hd => by
      beta_reduce
      rw [transportPowerObs_eq]
      split_ifs
      · exact Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (pow_nonneg (le_min (norm_nonneg _) zero_le_one) _)
      · exact le_rfl)
    (fun d hd => by
      beta_reduce
      rw [transportPowerObs_eq, dif_pos (hlev d hd), dif_pos (hlev d hd)]
      have h5 := hcz' d (Finset.mem_range.mpr hd)
      rw [dif_pos (hlev d hd)] at h5
      exact transportTerm_pow_le S.tower u m q hq ρ₀ Λ.table.ρA μ ν d _ _ _ h5 hσ (hsub d hd) _ (hrow d hd))
  have hsame : curvature (S.stateAtLevel u hu w).1 (S.siteAt u z) μ ν =
      curvature (topField Λ.stepParams u _ (sampleBelow Λ.stepParams u (localChainDepth Λ.stepParams S.β u) _ db)) o μ ν := by
    have e1 : (S.stateAtLevel u hu w).1 = topField Λ.stepParams u _ (S.sampleAtLevel u hu w) := stageState_fst S.tower u _ _
    rw [e1]
    have e2 : fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u) (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
        (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) = S.sideAtLevel u := by
      have h1 := fineSide_sideAtLevel S (u + (localChainDepth Λ.stepParams S.β u)) (localChainDepth Λ.stepParams S.β u) hK
      rw [h1]
      exact fineSide_sideAtLevel S u (localChainDepth Λ.stepParams S.β u) (by omega)
    refine (curvature_congr S u z μ ν e2 ?_).symm
    exact sampleBelow_heq_sampleAtLevel S u w hu (localChainDepth Λ.stepParams S.β u)
      (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams S.β u)
        (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u))) (by omega) db
      (fineSide_sideAtLevel S (u + (localChainDepth Λ.stepParams S.β u)) (localChainDepth Λ.stepParams S.β u) hK)
      (sampleBelow_heq_sampleAtLevel S (u + (localChainDepth Λ.stepParams S.β u)) w (by omega) (localChainDepth Λ.stepParams S.β u)
        (S.sideAtLevel (u + localChainDepth Λ.stepParams S.β u + localChainDepth Λ.stepParams S.β u)) hK X rfl HEq.rfl)
  rw [hsame] at hoff
  set E := ∑ i ∈ Finset.range (localChainDepth Λ.stepParams S.β u), (if h : u + i + 1 ≤ S.data.windowLevel then
      transportTerm S.tower u ρ₀ Λ.table.ρA μ ν i (S.sideAtLevel (u + i + 1)) (S.sampleAtLevel (u + i + 1) h w)
        (lowerSite S u z (i + 1) (S.sideAtLevel (u + i + 1))) else 0) with hE
  set A := C₁ * flowCouplings Λ.stepParams S.β u ^ (-(1 / 2 : ℝ)) with hA
  have hA0 : 0 ≤ A := mul_nonneg hC₁ (Real.rpow_nonneg hx0.le _)
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun i _ => by
    split_ifs
    · exact Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
    · exact le_rfl
  have hmain : curvature (topField Λ.stepParams u _ (sampleBelow Λ.stepParams u (localChainDepth Λ.stepParams S.β u) _ db)) o μ ν ^ (2 * q) ≤
      16 ^ (2 * q) * ∑ d ∈ Finset.range (localChainDepth Λ.stepParams S.β u), transportPowerObs u z μ ν q d S w + (2 * A) ^ (2 * q) := by
    have f1 : curvature (topField Λ.stepParams u _ (sampleBelow Λ.stepParams u (localChainDepth Λ.stepParams S.β u) _ db)) o μ ν ^ (2 * q) ≤
        (E + A) ^ (2 * q) :=
      pow_le_pow_left₀ (curvature_nonneg _ _ _ _) hcurv _
    have f2 : (E + A) ^ (2 * q) ≤ (2 * E) ^ (2 * q) + (2 * A) ^ (2 * q) := by
      rcases le_total E A with h | h
      · have g1 : (E + A) ^ (2 * q) ≤ (2 * A) ^ (2 * q) := pow_le_pow_left₀ (by linarith) (by linarith) _
        have g2 : 0 ≤ (2 * E) ^ (2 * q) := by positivity
        linarith
      · have g1 : (E + A) ^ (2 * q) ≤ (2 * E) ^ (2 * q) := pow_le_pow_left₀ (by linarith) (by linarith) _
        have g2 : 0 ≤ (2 * A) ^ (2 * q) := by positivity
        linarith
    have f3 : (2 * E) ^ (2 * q) ≤ 16 ^ (2 * q) * ∑ d ∈ Finset.range (localChainDepth Λ.stepParams S.β u), transportPowerObs u z μ ν q d S w := by
      rw [mul_pow]
      have g1 := mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ 2 ^ (2 * q))
      refine g1.trans ?_
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ nP
      have g2 : (8 : ℝ) ^ (2 * q - 1) ≤ 8 ^ (2 * q) := pow_le_pow_right₀ (by norm_num) (by omega)
      have g3 : (2 : ℝ) ^ (2 * q) * 8 ^ (2 * q) = 16 ^ (2 * q) := by rw [← mul_pow]; norm_num
      rw [← g3]
      exact mul_le_mul_of_nonneg_left g2 (by positivity)
    linarith
  have p1 := mul_nonneg hcinv nQL
  have p2 := mul_nonneg hcinv nQH
  have p3 := mul_nonneg h4.le (add_nonneg (add_nonneg (add_nonneg (add_nonneg p1 p2) nSL) nSH) nH)
  linarith
end
section
variable {T : TranslatedLaws} {J : Type} {X : J → T.Family} {P : Measure (TranslateValues J)}
private theorem ae_le_zero_of_eventually (hL : IsJointLimitLaw T X P) {I : Type} [Fintype I] (ι : I → J) (φ : (I → ℝ) → ℝ)
    (hφ : Continuous φ) (h : ∀ᶠ i in atTop, ∀ᵐ ω ∂(T.μ i), φ (fun c => X (ι c) i ω) ≤ 0) :
    ∀ᵐ v ∂P, φ (fun c => v (ι c, 0)) ≤ 0 := by apply _root_.YangMills.SharedProofs.p13419 <;> assumption
private theorem shiftInvariantSigma_le : shiftInvariantSigma J ≤ (inferInstance : MeasurableSpace (TranslateValues J)) := inf_le_right
private theorem ae_invariantCondExp_le_linear [IsProbabilityMeasure P] {ι : Type} (I : Finset ι) (c : ι → ℝ) (hc : ∀ e ∈ I, 0 ≤ c e)
    (f : ι → TranslateValues J → ℝ) (hf : ∀ e ∈ I, Integrable (f e) P) (b : ι → ℝ)
    (hb : ∀ e ∈ I, ∀ᵐ v ∂P, invariantCondExp P (f e) v ≤ b e) (a : ℝ)
    {Y : TranslateValues J → ℝ} (hY : Integrable Y P) (hle : ∀ᵐ v ∂P, Y v ≤ a + ∑ e ∈ I, c e * f e v) :
    ∀ᵐ v ∂P, invariantCondExp P Y v ≤ a + ∑ e ∈ I, c e * b e := by
  have hg : ∀ e ∈ I, Integrable (c e • f e) P := fun e he => (hf e he).smul (c e)
  have hsum : Integrable (∑ e ∈ I, c e • f e) P := integrable_finset_sum' _ hg
  have hall : Integrable (fun v => a + (∑ e ∈ I, c e • f e) v) P := (integrable_const a).add hsum
  have hle' : Y ≤ᵐ[P] fun v => a + (∑ e ∈ I, c e • f e) v := by
    filter_upwards [hle] with v hv
    have : (∑ e ∈ I, c e • f e) v = ∑ e ∈ I, c e * f e v := by
      rw [Finset.sum_apply]
      rfl
    rw [this]
    exact hv
  have c1 := condExp_mono (m := shiftInvariantSigma J) hY hall hle'
  have c2 := condExp_add (μ := P) (integrable_const a) hsum (shiftInvariantSigma J)
  have c3 : P[fun _ : TranslateValues J => a | shiftInvariantSigma J] = fun _ => a := condExp_const shiftInvariantSigma_le a
  have c4 := condExp_finsetSum (μ := P) (s := I) (f := fun e => c e • f e) hg (shiftInvariantSigma J)
  have c5 : ∀ᵐ v ∂P, ∀ e ∈ I, (P[c e • f e | shiftInvariantSigma J]) v = c e * invariantCondExp P (f e) v ∧
      invariantCondExp P (f e) v ≤ b e := by
    refine (ae_ball_iff I.countable_toSet).2 fun e he => ?_
    filter_upwards [condExp_smul (μ := P) (c e) (f e) (shiftInvariantSigma J), hb e he] with v a₁ a₂
    exact ⟨by simpa [smul_eq_mul, invariantCondExp] using a₁, a₂⟩
  filter_upwards [c1, c2, c4, c5] with v a₁ a₂ a₃ a₄
  have a₂' : (P[fun v => a + (∑ e ∈ I, c e • f e) v | shiftInvariantSigma J]) v =
      (P[fun _ : TranslateValues J => a | shiftInvariantSigma J]) v + (P[∑ e ∈ I, c e • f e | shiftInvariantSigma J]) v := a₂
  show (P[Y | shiftInvariantSigma J]) v ≤ _
  refine a₁.trans ?_
  rw [a₂', c3, a₃, Finset.sum_apply]
  refine add_le_add le_rfl (Finset.sum_le_sum fun e he => ?_)
  rw [(a₄ e he).1]
  exact mul_le_mul_of_nonneg_left (a₄ e he).2 (hc e he)
private theorem hasBoundedMoments_of_abs_le {T : TranslatedLaws} {X : T.Family} (hp : ∀ i, IsProbabilityMeasure (T.μ i))
    (hb : ∀ i, AEMeasurable (X i) (T.μ i)) {C : ℝ} (hC : ∀ i, ∀ᵐ ω ∂(T.μ i), |X i ω| ≤ C) :
    TranslatedLaws.HasBoundedMoments X := by apply _root_.YangMills.SharedProofs.p39822 <;> assumption
end
section
variable {n : ℕ} [NeZero n]
private theorem card_supBall_le (o : TorusSite n) {m : ℝ} (hm : 0 ≤ m) : (supBall o m).card ≤ (2 * ⌊m⌋₊ + 1) ^ 4 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.LocalEventLikely.card_supBall_le <;> assumption
private theorem card_sitesInBlocks_le (L : ℕ) [NeZero L] (Z : Finset (TorusSite n)) :
    (sitesInBlocks L Z).card ≤ Z.card * (2 * L + 1) ^ 4 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.LocalEventLikely.card_sitesInBlocks_le <;> assumption
private theorem card_thickening_sitesInBlocks_le (L r m : ℕ) [NeZero L] (c : TorusSite n) :
    (thickening (4 * r) (sitesInBlocks L (supBall c (m : ℝ)))).card ≤ (2 * m + 1) ^ 4 * (2 * L + 1) ^ 4 * (8 * r + 1) ^ 4 := by
  classical
  refine (card_thickening_le (4 * r) _).trans ?_
  have e : 2 * (4 * r) + 1 = 8 * r + 1 := by ring
  rw [e]
  refine Nat.mul_le_mul_right _ ((card_sitesInBlocks_le L _).trans (Nat.mul_le_mul_right _ ?_))
  have := card_supBall_le c (m := (m : ℝ)) (Nat.cast_nonneg _)
  simpa using this
private theorem card_blocksNearFreeCores_le (L r m : ℕ) [NeZero L] (c : TorusSite n) :
    (blocksNearFreeCores L r (supBall c (m : ℝ))).card ≤ (2 * m + 1) ^ 4 * (2 * L + 1) ^ 4 * (8 * r + 1) ^ 4 := by
  classical
  exact Finset.card_image_le.trans (card_thickening_sitesInBlocks_le L r m c)
private theorem card_chartBondsInBlocks_le {L n : ℕ} [NeZero L] [NeZero n] (o : TorusSite n) {R : ℝ} (hR : 0 ≤ R) :
    ((chartBondsInBlocks L (supBall o R)).card : ℝ) ≤ 4 * (2 * R + 1) ^ 4 * (2 * (L : ℝ) + 1) ^ 4 := by apply _root_.YangMills.SharedProofs.p5403 <;> assumption
private theorem bond_mem_supBall_of_chart {L : ℕ} [NeZero L] (hodd : Odd L) (hL2 : 2 ≤ L) (c : TorusSite n) {R : ℝ} (R' Rr : ℕ)
    (hR : R ≤ R') (hRr : L + L * (R' + 1) + 1 ≤ Rr) {b : TorusBond (n * L)} (hb : b ∈ chartBondsInBlocks L (supBall c R))
    (c' : TorusBond (n * L))
    (h : parentBlock L c'.1 = parentBlock L b.1 ∨ parentBlock L c'.1 = parentBlock L (b.1 + unitStep _ b.2)) :
    c'.1 ∈ supBall (blockCentreSite L c) (Rr : ℝ) ∧ c'.1 + unitStep _ c'.2 ∈ supBall (blockCentreSite L c) (Rr : ℝ) := by
  haveI : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have hb2 : parentBlock L b.1 ∈ supBall c R := (Finset.mem_filter.mp hb).2
  have d1 : TorusFields.supDist (parentBlock L b.1) c ≤ R' := by
    have h1 := mem_supBall.mp hb2
    exact_mod_cast h1.trans hR
  have d2 : TorusFields.supDist (parentBlock L c'.1) c ≤ R' + 1 := by
    rcases h with h | h
    · rw [h]
      omega
    · rw [h]
      have t1 := supDist_triangle (parentBlock L (b.1 + unitStep _ b.2)) (parentBlock L b.1) c
      have t2 : TorusFields.supDist (b.1 + unitStep _ b.2) b.1 ≤ 1 := by
        rw [supDist_comm]
        exact supDist_add_unitStep_le _ _
      have t3 := supDist_parentBlock_le_one hL2 _ _ t2
      omega
  have d3 := supDist_blockCentreSite_le hodd c'.1 c
  have d4 : L * TorusFields.supDist (parentBlock L c'.1) c ≤ L * (R' + 1) := Nat.mul_le_mul_left _ d2
  have d5 : TorusFields.supDist c'.1 (blockCentreSite L c) + 1 ≤ Rr := by omega
  refine ⟨mem_supBall.mpr (by exact_mod_cast (by omega : TorusFields.supDist c'.1 (blockCentreSite L c) ≤ Rr)), mem_supBall.mpr ?_⟩
  have t1 := supDist_triangle (c'.1 + unitStep _ c'.2) c'.1 (blockCentreSite L c)
  have t2 : TorusFields.supDist (c'.1 + unitStep _ c'.2) c'.1 ≤ 1 := by
    rw [supDist_comm]
    exact supDist_add_unitStep_le _ _
  exact_mod_cast (by omega : TorusFields.supDist (c'.1 + unitStep _ c'.2) (blockCentreSite L c) ≤ Rr)
private theorem site_mem_supBall_of_thickening {L : ℕ} [NeZero L] (hodd : Odd L) (c : TorusSite n) (m r Rr : ℕ)
    (hRr : 4 * r + L + L * m + 1 ≤ Rr) {y : TorusSite (n * L)}
    (hy : y ∈ thickening (4 * r) (sitesInBlocks L (supBall c (m : ℝ)))) :
    y ∈ supBall (blockCentreSite L c) (Rr : ℝ) ∧ ∀ μ : Fin 4, y + unitStep _ μ ∈ supBall (blockCentreSite L c) (Rr : ℝ) := by
  haveI : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  obtain ⟨y₀, hy₀, hd⟩ := (mem_thickening _ _ _).mp hy
  have d1 : TorusFields.supDist (parentBlock L y₀) c ≤ m := by
    have h1 := mem_supBall.mp (ClusterExpansionOfAStep.mem_sitesInBlocks.mp hy₀)
    exact_mod_cast h1
  have d3 := supDist_blockCentreSite_le hodd y₀ c
  have d4 : L * TorusFields.supDist (parentBlock L y₀) c ≤ L * m := Nat.mul_le_mul_left _ d1
  have t1 := supDist_triangle y y₀ (blockCentreSite L c)
  refine ⟨mem_supBall.mpr (by exact_mod_cast (by omega : TorusFields.supDist y (blockCentreSite L c) ≤ Rr)), fun μ => mem_supBall.mpr ?_⟩
  have t2 := supDist_triangle (y + unitStep _ μ) y (blockCentreSite L c)
  have t3 : TorusFields.supDist (y + unitStep _ μ) y ≤ 1 := by
    rw [supDist_comm]
    exact supDist_add_unitStep_le _ _
  exact_mod_cast (by omega : TorusFields.supDist (y + unitStep _ μ) (blockCentreSite L c) ≤ Rr)
private theorem supBall_parentBlock_subset {L : ℕ} [NeZero L] (c o : TorusSite n) (m r t Rc : ℕ) (ht : TorusFields.supDist c o ≤ t)
    (hRc : 2 * m + 4 * r + 1 + t ≤ Rc) {y : TorusSite (n * L)} (hy : y ∈ thickening (4 * r) (sitesInBlocks L (supBall c (m : ℝ)))) :
    supBall (parentBlock L y) (m : ℝ) ⊆ supBall o (Rc : ℝ) := by
  haveI : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  intro y₁ h₁
  obtain ⟨y₀, hy₀, hd⟩ := (mem_thickening _ _ _).mp hy
  have d1 : TorusFields.supDist (parentBlock L y₀) c ≤ m := by
    have h1 := mem_supBall.mp (ClusterExpansionOfAStep.mem_sitesInBlocks.mp hy₀)
    exact_mod_cast h1
  have d2 : TorusFields.supDist y₁ (parentBlock L y) ≤ m := by
    have h1 := mem_supBall.mp h₁
    exact_mod_cast h1
  have d3 := supDist_parentBlock_le_div_add_one L y y₀
  have d4 : TorusFields.supDist y y₀ / L ≤ TorusFields.supDist y y₀ := Nat.div_le_self _ _
  have t1 := supDist_triangle y₁ (parentBlock L y) o
  have t2 := supDist_triangle (parentBlock L y) (parentBlock L y₀) o
  have t3 := supDist_triangle (parentBlock L y₀) c o
  exact mem_supBall.mpr (by exact_mod_cast (by omega : TorusFields.supDist y₁ o ≤ Rc))
private theorem supBall_subset_supBall (c o : TorusSite n) (m t Rc : ℕ) (ht : TorusFields.supDist c o ≤ t) (hRc : m + t ≤ Rc) :
    supBall c (m : ℝ) ⊆ supBall o (Rc : ℝ) := by
  intro y h
  have d := mem_supBall.mp h
  have d' : TorusFields.supDist y c ≤ m := by exact_mod_cast d
  have t1 := supDist_triangle y c o
  exact mem_supBall.mpr (by exact_mod_cast (by omega : TorusFields.supDist y o ≤ Rc))
private theorem chartBondsInBlocks_mono {L : ℕ} [NeZero L] (c : TorusSite n) {R R' : ℝ} (h : R ≤ R') :
    chartBondsInBlocks L (supBall c R) ⊆ chartBondsInBlocks L (supBall c R') := by
  intro b hb
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hb
  exact Finset.mem_filter.mpr ⟨h1, mem_supBall.mpr ((mem_supBall.mp h2).trans h)⟩
end
section
private theorem eventually_mul_pow_mul_exp_le_one (K c : ℝ) (hc : 0 < c) (a : ℕ) :
    ∀ᶠ x : ℝ in atTop, K * x ^ a * Real.exp (-(c * x)) ≤ 1 := by
  have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero a
  have h1 : Tendsto (fun x : ℝ => c * x) atTop atTop := tendsto_id.const_mul_atTop hc
  have h2 := (h.comp h1).const_mul (K / c ^ a)
  rw [mul_zero] at h2
  filter_upwards [h2.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with x hx
  have hc' : c ^ a ≠ 0 := (pow_pos hc a).ne'
  have e : K * x ^ a * Real.exp (-(c * x)) = K / c ^ a * ((fun x : ℝ => x ^ a * Real.exp (-x)) ∘ fun x : ℝ => c * x) x := by
    simp only [Function.comp, mul_pow]
    field_simp
  rw [e]
  exact hx.le
private theorem rpow_neg_half_pow {x : ℝ} (hx : 0 < x) (q : ℕ) : (x ^ (-(1 / 2 : ℝ))) ^ (2 * q) = (x ^ q)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  have : -(1 / 2 : ℝ) * ((2 * q : ℕ) : ℝ) = -(q : ℝ) := by
    push_cast
    ring
  rw [this, Real.rpow_neg hx.le, Real.rpow_natCast]
private theorem inv_rpow_neg_third_pow {x : ℝ} (hx : 0 < x) (q : ℕ) : ((x ^ (-(1 / 3 : ℝ))) ^ (2 * (3 * q)))⁻¹ = x ^ (2 * q) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  have : -(1 / 3 : ℝ) * ((2 * (3 * q) : ℕ) : ℝ) = -((2 * q : ℕ) : ℝ) := by
    push_cast
    ring
  rw [this, Real.rpow_neg hx.le, Real.rpow_natCast, inv_inv]
private theorem bound_sum_le {x : ℝ} (hx : 1 ≤ x) (q : ℕ) (Ap Cp' Cq' C₁' Nb ε Am cc : ℝ) (M : ℕ) (hM : (M : ℝ) ≤ x) (hAp : 0 ≤ Ap)
    (hAp8 : Ap ≤ 8) (hCp : 0 ≤ Cp') (hCq : 0 ≤ Cq') (hC₁ : 0 ≤ C₁') (hNb : Nb + 1 ≤ x ^ 10) (hNb0 : 0 ≤ Nb)
    (hε : ε = (x ^ (3 * q + 40))⁻¹) (hAm : Am = x) (hcc : cc = x ^ (2 * (q + 4))) :
    C₁' * (x ^ q)⁻¹ + (16 ^ (2 * q) * (Ap * (Cp' * (x ^ q)⁻¹ + 2 * ε)) +
      4 ^ q * ((cc * (M * (Am * (Cq' * (x ^ (3 * (q + 4)))⁻¹ + 2 * ε))) + cc * (M * (Am * (Cq' * (x ^ (3 * (q + 4)))⁻¹ + 2 * ε))) +
        M * (Nb * ε + ε) + M * (Nb * ε + ε)) + ε)) ≤
      (C₁' + 16 ^ (2 * q) * (8 * (Cp' + 2)) + 4 ^ q * (2 * (Cq' + 2) + 2 + 1)) * (x ^ q)⁻¹ := by
  have hx0 : 0 < x := by linarith
  set inv := (x ^ q)⁻¹ with hinv
  have hi0 : 0 < inv := inv_pos.mpr (pow_pos hx0 q)
  have hpow : ∀ a b : ℕ, a + q ≤ b → x ^ a * (x ^ b)⁻¹ ≤ inv := by
    intro a b hab
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    have e : x ^ a * (x ^ (a + q + c))⁻¹ = inv * (x ^ c)⁻¹ := by
      rw [hinv, pow_add, pow_add]
      field_simp
    rw [e]
    have h1 : (x ^ c)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hx)
    exact mul_le_of_le_one_right hi0.le h1
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hεi : ε ≤ inv := by
    have := hpow 0 (3 * q + 40) (by omega)
    rw [pow_zero, one_mul] at this
    rw [hε]
    exact this
  have t2 : Ap * (Cp' * inv + 2 * ε) ≤ 8 * (Cp' + 2) * inv := by
    have h1 : Cp' * inv + 2 * ε ≤ (Cp' + 2) * inv := by nlinarith
    have h2 : 0 ≤ (Cp' + 2) * inv := by positivity
    calc Ap * (Cp' * inv + 2 * ε) ≤ Ap * ((Cp' + 2) * inv) := mul_le_mul_of_nonneg_left h1 hAp
      _ ≤ 8 * ((Cp' + 2) * inv) := mul_le_mul_of_nonneg_right hAp8 h2
      _ = _ := by ring
  have hMx : cc * (M * Am) ≤ x ^ (2 * q + 10) := by
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have h1 : (M : ℝ) * Am ≤ x * x := by
      rw [hAm]
      exact mul_le_mul_of_nonneg_right hM hx0.le
    rw [hcc]
    have h2 : x ^ (2 * (q + 4)) * (x * x) ≤ x ^ (2 * q + 10) := by
      apply le_of_eq
      ring
    exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans h2
  have t3 : cc * (M * (Am * (Cq' * (x ^ (3 * (q + 4)))⁻¹ + 2 * ε))) ≤ (Cq' + 2) * inv := by
    have e1 : cc * (M * (Am * (Cq' * (x ^ (3 * (q + 4)))⁻¹ + 2 * ε))) =
        (cc * (M * Am)) * (Cq' * (x ^ (3 * (q + 4)))⁻¹ + 2 * ε) := by ring
    rw [e1]
    have h0 : 0 ≤ Cq' * (x ^ (3 * (q + 4)))⁻¹ + 2 * ε := by positivity
    refine (mul_le_mul_of_nonneg_right hMx h0).trans ?_
    have a1 := hpow (2 * q + 10) (3 * (q + 4)) (by omega)
    have a2 := hpow (2 * q + 10) (3 * q + 40) (by omega)
    rw [← hε] at a2
    have a3 := mul_le_mul_of_nonneg_left a1 hCq
    nlinarith
  have t4 : (M : ℝ) * (Nb * ε + ε) ≤ inv := by
    have e1 : (M : ℝ) * (Nb * ε + ε) = M * (Nb + 1) * ε := by ring
    rw [e1]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have h1 : (M : ℝ) * (Nb + 1) ≤ x * x ^ 10 := mul_le_mul hM hNb (by linarith) hx0.le
    have h2 := mul_le_mul_of_nonneg_right h1 hε0
    have a2 := hpow 11 (3 * q + 40) (by omega)
    rw [← hε] at a2
    have e2 : x * x ^ 10 = x ^ 11 := by ring
    rw [e2] at h2
    exact h2.trans a2
  have h16 : (0 : ℝ) ≤ 16 ^ (2 * q) := by positivity
  have h4 : (0 : ℝ) ≤ 4 ^ q := by positivity
  have s1 := mul_le_mul_of_nonneg_left t2 h16
  have s2 : 4 ^ q * ((cc * (M * (Am * (Cq' * (x ^ (3 * (q + 4)))⁻¹ + 2 * ε))) + cc * (M * (Am * (Cq' * (x ^ (3 * (q + 4)))⁻¹ + 2 * ε))) +
        M * (Nb * ε + ε) + M * (Nb * ε + ε)) + ε) ≤ 4 ^ q * ((2 * (Cq' + 2) + 2 + 1) * inv) := by
    refine mul_le_mul_of_nonneg_left ?_ h4
    linarith
  calc _ ≤ C₁' * inv + (16 ^ (2 * q) * (8 * (Cp' + 2) * inv) + 4 ^ q * ((2 * (Cq' + 2) + 2 + 1) * inv)) := by linarith
    _ = _ := by ring
end
section
private theorem hullParams_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllHullParameters Q₁) (h₂ : ForAllHullParameters Q₂) :
    ForAllHullParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p1668 <;> assumption
private theorem hullParams_imp {Q₁ Q₂ : MomentParameters → Prop} (h : ForAllHullParameters Q₁) (f : ∀ Λ, Λ.k ≤ 8 → Q₁ Λ → Q₂ Λ) :
    ForAllHullParameters Q₂ := by apply _root_.YangMills.SharedProofs.p30752 <;> assumption
private theorem hullParams_of_params {Q : MomentParameters → Prop} (h : ForAllParameters Q) : ForAllHullParameters Q := by apply _root_.YangMills.SharedProofs.p12974 <;> assumption
private theorem hullParams_of_parameters {P : ParameterAssignment → ℝ → Prop} (h : HoldsOnParameterFamilies P) :
    ForAllHullParameters fun Λ => P Λ.table Λ.floor := by
  intro a ha
  obtain ⟨L₀, r₀, C₀, hr, h⟩ := h a ha
  refine ⟨L₀, r₀, C₀, hr, ?_⟩
  intro L hodd hL Tb e1 e2 hD hCS hCH hrt hC
  obtain ⟨y₀, h⟩ := h L hodd hL Tb e1 e2 hD hCS hCH hrt hC
  exact ⟨0, fun Kr _ _ _ _ _ => ⟨y₀, fun y hy hR hW g _ _ k _ _ _ R d _ => h y hy hR hW⟩⟩
private theorem isBlockTorusSide_sideAtLevel {Λ : MomentParameters} (S : MomentPoint Λ) (hfit : Λ.stepParams.Admissible) (u : ℕ) :
    IsBlockTorusSide Λ.stepParams (S.sideAtLevel u) := by apply _root_.YangMills.SharedProofs.p591 <;> assumption
private theorem stageOnFlow_of_point {Λ : MomentParameters} (S : MomentPoint Λ) {j : ℕ} (hj : j ≤ S.data.windowLevel) :
    StageOnFlow Λ.table Λ.response Λ.floor S.β j (⟨S.tower.stage j, S.resp j⟩ : StageWithResponse Λ.stepParams) := by apply _root_.YangMills.SharedProofs.p21183 <;> assumption
private theorem points_fields_eq {Λ : MomentParameters} {S : MomentPoint Λ} (F : LimitLawAtPoint S) (n : ℕ) :
    (F.points n).data.windowLevel = S.data.windowLevel ∧ (F.points n).β = S.β ∧ (F.points n).tower = S.tower := by apply _root_.YangMills.SharedProofs.p61479 <;> assumption
private theorem params_admissible :
    ForAllParameters fun Λ => Λ.table.Admissible ∧ Λ.table.floorMin ≤ Λ.floor ∧ Λ.floor ≤ (Λ.g ^ 2)⁻¹ := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, fun L _ _ Tb _ _ hD _ _ _ _ Kr _ => ?_⟩
  refine ⟨Tb.floorMin, fun y hy _ _ g _ hgy k _ _ _ R d _ => ⟨hD, hy, hgy⟩⟩
private theorem measurableSet_sigma_fst_eq {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    MeasurableSet {z : Sigma β | z.1 = a} := by apply _root_.YangMills.SharedProofs.p1937 <;> assumption
private theorem dvd_period_and_le {Λ : MomentParameters} (S : MomentPoint Λ) (hfit : Λ.stepParams.Admissible) :
    Λ.stepParams.side ∣ S.data.period Λ.stepParams.side ∧ 64 ≤ S.data.period Λ.stepParams.side := by apply _root_.YangMills.SharedProofs.p32373 <;> assumption
end
section
variable {Λ : MomentParameters}
private theorem measurable_truncatedDeviationCases (S : MomentPoint Λ) (hd : SampleFacts S) (k j q : ℕ) (hj : j + 1 ≤ S.data.windowLevel)
    (cen : (S : MomentPoint Λ) → TorusSite (S.sideAtLevel (j + 1)))
    (Z : (S : MomentPoint Λ) → Finset (TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side)))
    (a : (S : MomentPoint Λ) → TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side) → ℝ)
    (hq : ∀ b ∈ Z S, Measurable fun p : TorusField (S.sideAtLevel (j + 1)) × TorusField (S.sideAtLevel (j + 1) * Λ.stepParams.side) =>
      ‖coldDeviation S.tower j p.1 p.2 (cen S) (localBlockSide Λ.stepParams S.β k) b‖) :
    Measurable (caseObservable j (truncatedDeviationCases k j q cen Z a) S) := by
  have hJ : Measurable fun p : TorusField (S.sideAtLevel (j + 1)) × TorusField (S.sideAtLevel (j + 1) * Λ.stepParams.side) =>
      ∑ b ∈ Z S, a S b * min ‖coldDeviation S.tower j p.1 p.2 (cen S) (localBlockSide Λ.stepParams S.β k) b‖ 1 ^ (2 * q) :=
    Finset.measurable_sum _ fun b hb => (((hq b hb).min measurable_const).pow_const _).const_mul _
  have hp : Measurable fun x : MarkedSample Λ.stepParams (j + 1) (S.sideAtLevel (j + 1)) =>
      ((x.2.2.1, topField Λ.stepParams j _ x.1) : TorusField (S.sideAtLevel (j + 1)) × TorusField (S.sideAtLevel (j + 1) * Λ.stepParams.side)) :=
    (measurable_topField Λ.stepParams (j + 1) _).prodMk ((measurable_topField Λ.stepParams _ _).comp (measurable_sample_fst Λ.stepParams _ _))
  have hl : Measurable (caseLift S.tower j _ (truncatedDeviationCases k j q cen Z a S)) := measurable_of_eq_comp hJ hp fun _ => rfl
  have e : caseObservable j (truncatedDeviationCases k j q cen Z a) S =
      fun w => caseLift S.tower j _ (truncatedDeviationCases k j q cen Z a S) (S.sampleAtLevel (j + 1) hj w) :=
    funext fun w => dif_pos hj
  rw [e]
  exact hl.comp (hd.sampleAtLevel_map (j + 1) hj).1
private theorem abs_truncatedDeviationCases_le (S : MomentPoint Λ) (k j q : ℕ)
    (cen : (S : MomentPoint Λ) → TorusSite (S.sideAtLevel (j + 1)))
    (Z : (S : MomentPoint Λ) → Finset (TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side)))
    (a : (S : MomentPoint Λ) → TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side) → ℝ) (A : ℝ) (hA : 0 ≤ A) (ha : ∀ b, 0 ≤ a S b)
    (hs : ∑ b ∈ Z S, a S b ≤ A) (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    |caseObservable j (truncatedDeviationCases k j q cen Z a) S w| ≤ A := by
  classical
  unfold caseObservable
  split_ifs with hj
  · set x := S.sampleAtLevel (j + 1) hj w
    have e : caseLift S.tower j _ (truncatedDeviationCases k j q cen Z a S) x = ∑ b ∈ Z S, a S b *
        min ‖coldDeviation S.tower j x.2.2.1 (topField Λ.stepParams j _ x.1) (cen S) (localBlockSide Λ.stepParams S.β k) b‖ 1 ^ (2 * q) := rfl
    rw [e, abs_of_nonneg (Finset.sum_nonneg fun b _ => mul_nonneg (ha b) (pow_nonneg (le_min (norm_nonneg _) zero_le_one) _))]
    refine le_trans (Finset.sum_le_sum fun b _ => ?_) hs
    have h1 : min ‖coldDeviation S.tower j x.2.2.1 (topField Λ.stepParams j _ x.1) (cen S) (localBlockSide Λ.stepParams S.β k) b‖ 1 ^ (2 * q) ≤ 1 :=
      pow_le_one₀ (le_min (norm_nonneg _) zero_le_one) (min_le_right _ _)
    exact (mul_le_mul_of_nonneg_left h1 (ha b)).trans (by simp)
  · simpa using hA
private theorem measurable_badOrSupportSiteCase (S : MomentPoint Λ) (hd : SampleFacts S) (j : ℕ) (hj : j + 1 ≤ S.data.windowLevel)
    (Z : (S : MomentPoint Λ) → Finset (TorusSite (S.sideAtLevel (j + 1) * Λ.stepParams.side))) :
    Measurable (caseObservable j (badOrSupportSiteCase j Z) S) := by
  classical
  have hStm : Measurable fun u : MarkedSample Λ.stepParams (j + 1) (S.sideAtLevel (j + 1)) =>
      stageState S.tower j (S.sideAtLevel (j + 1) * Λ.stepParams.side) u.1 :=
    (hd.measurable_stageState j _).comp (measurable_sample_fst Λ.stepParams j _)
  have hsnd : Measurable (fun u : MarkedSample Λ.stepParams (j + 1) (S.sideAtLevel (j + 1)) => u.2) := measurable_snd
  have hBm : Measurable (fun u : MarkedSample Λ.stepParams (j + 1) (S.sideAtLevel (j + 1)) => u.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp hsnd)
  have e : caseLift S.tower j _ (badOrSupportSiteCase j Z S) = fun u =>
      if (((show Finset (TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side)) from u.2.2.2).image Prod.fst ∪
        (stageState S.tower j _ u.1).2.1) ∩ Z S).Nonempty then (1 : ℝ) else 0 := rfl
  have hl : Measurable (caseLift S.tower j _ (badOrSupportSiteCase j Z S)) := by
    rw [e]
    refine Measurable.ite ?_ measurable_const measurable_const
    have e2 : {u : MarkedSample Λ.stepParams (j + 1) (S.sideAtLevel (j + 1)) |
        (((show Finset (TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side)) from u.2.2.2).image Prod.fst ∪
          (stageState S.tower j _ u.1).2.1) ∩ Z S).Nonempty} =
        ⋃ d ∈ {d : Finset (TorusSite (S.sideAtLevel (j + 1) * Λ.stepParams.side)) ×
            Finset (TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side)) | ((d.2.image Prod.fst ∪ d.1) ∩ Z S).Nonempty},
          ({u | (stageState S.tower j _ u.1).2.1 = d.1} ∩
            {u | (u.2.2.2 : Finset (TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side))) = d.2}) := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop, Prod.exists]
      constructor
      · intro h1
        exact ⟨_, _, h1, rfl, rfl⟩
      · rintro ⟨a, c, h1, rfl, rfl⟩
        exact h1
    rw [e2]
    refine MeasurableSet.biUnion (Set.to_countable _) fun d _ => MeasurableSet.inter ?_ ?_
    · exact hStm (measurable_snd (measurableSet_sigma_fst_eq d.1))
    · exact hBm (MeasurableSpace.measurableSet_top (s := {d.2}))
  have e3 : caseObservable j (badOrSupportSiteCase j Z) S =
      fun w => caseLift S.tower j _ (badOrSupportSiteCase j Z S) (S.sampleAtLevel (j + 1) hj w) :=
    funext fun w => dif_pos hj
  rw [e3]
  exact hl.comp (hd.sampleAtLevel_map (j + 1) hj).1
private theorem abs_badOrSupportSiteCase_le (S : MomentPoint Λ) (j : ℕ)
    (Z : (S : MomentPoint Λ) → Finset (TorusSite (S.sideAtLevel (j + 1) * Λ.stepParams.side)))
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    |caseObservable j (badOrSupportSiteCase j Z) S w| ≤ 1 := by
  classical
  unfold caseObservable
  split_ifs with hj
  · show |(if _ then (1 : ℝ) else 0)| ≤ 1
    split_ifs <;> simp
  · simp
private theorem measurable_largeHullIndicator (S : MomentPoint Λ) (hd : SampleFacts S) (u : ℕ) (hu : u ≤ S.data.windowLevel)
    (z : Fin 4 → ℤ) : Measurable (largeHullIndicator u z 0 S) := by
  classical
  have e : largeHullIndicator u z 0 S = fun w => if S.siteAt u z ∈ (S.stateAtLevel u hu w).2.1 then 1 else 0 :=
    funext fun w => largeHullIndicator_zero_eq S hu z w
  rw [e]
  refine Measurable.ite ?_ measurable_const measurable_const
  have hst : Measurable (S.stateAtLevel u hu) := (hd.measurable_stageState u (S.sideAtLevel u)).comp (hd.sampleAtLevel_map u hu).1
  have e2 : {w | S.siteAt u z ∈ (S.stateAtLevel u hu w).2.1} =
      ⋃ a ∈ {a : Finset (TorusSite (S.sideAtLevel u)) | S.siteAt u z ∈ a}, {w | (S.stateAtLevel u hu w).2.1 = a} := by
    ext w
    simp
  rw [e2]
  exact MeasurableSet.biUnion (Set.to_countable _) fun a _ => (measurable_snd.comp hst) (measurableSet_sigma_fst_eq a)
private theorem abs_largeHullIndicator_le (S : MomentPoint Λ) (u : ℕ) (z : Fin 4 → ℤ)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) : |largeHullIndicator u z 0 S w| ≤ 1 := by apply _root_.YangMills.SharedProofs.p33608 <;> assumption
private theorem clearCurvaturePower_le_four_pow (S : MomentPoint Λ) (u : ℕ) (z : Fin 4 → ℤ) (μ ν : Fin 4) (q : ℕ)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) : clearCurvaturePower u z μ ν q S w ≤ 4 ^ q := by
  classical
  by_cases hu : u ≤ S.data.windowLevel
  · refine (clearCurvaturePower_le S hu z μ ν q w).trans ?_
    have := pow_le_pow_left₀ (curvature_nonneg _ _ _ _) (curvature_le_two (S.stateAtLevel u hu w).1 (S.siteAt u z) μ ν) (2 * q)
    have e : (2 : ℝ) ^ (2 * q) = 4 ^ q := by
      rw [pow_mul]
      norm_num
    exact this.trans e.le
  · unfold clearCurvaturePower
    rw [dif_neg hu]
    positivity
private theorem isLocalChainAbove_of_point (hyg : Λ.floor ≤ (Λ.g ^ 2)⁻¹) (hB : 0 < 2 * Λ.stepParams.B) (P : MomentPoint Λ) (u n : ℕ)
    [NeZero n] (x₀ : ℝ) (h1 : x₀ ≤ P.coupling u) (hx1 : 1 ≤ P.coupling u)
    (hK : u + 2 * localChainDepth Λ.stepParams P.β u + 1 ≤ P.data.windowLevel) (hs : (2 : ℝ) ^ 10 * localBoxRadius (P.coupling u) ≤ n) :
    IsLocalChainAbove Λ.table Λ.floor P.tower P.β u n 1 x₀ := by
  have hstand : IsTowerAtParameters Λ.table Λ.floor P.tower P.β (u + 2 * localChainDepth Λ.stepParams P.β u) :=
    ⟨P.startsAtWilson, fun j hj => (stageOnFlow_of_point P (by omega)).coupling_eq,
      fun j hj => (stageOnFlow_of_point P (by omega)).onFamily.onFamily⟩
  refine ⟨h1, ?_, hstand, P.isCutoff, P.marksMeasurable, hs, le_rfl, Real.one_le_rpow hx1 (by norm_num)⟩
  intro j hj
  have hjK : j < P.data.windowLevel := by
    have : j ≤ u + 2 * localChainDepth Λ.stepParams P.β u := hj
    omega
  have h2 := P.passage.2 j hjK
  have h3 : Λ.stepParams.y₁ = Λ.floor := rfl
  have h4 : couplingWindowTop Λ.stepParams Λ.g = (Λ.g ^ 2)⁻¹ + 2 * Λ.stepParams.B := rfl
  rw [h3]
  linarith
private theorem sideAtLevel_antitone (P : MomentPoint Λ) {a b : ℕ} (h : a ≤ b) : P.sideAtLevel b ≤ P.sideAtLevel a := by
  show fineSide Λ.stepParams.side (P.data.windowLevel - b) (P.data.period Λ.stepParams.side) ≤
    fineSide Λ.stepParams.side (P.data.windowLevel - a) (P.data.period Λ.stepParams.side)
  rw [fineSide_eq, fineSide_eq]
  have hL : 0 < Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hL (by omega))
private theorem le_sideAtLevel (P : MomentPoint Λ) (hL2 : 2 ≤ Λ.stepParams.side) (a E : ℕ) (hK : P.data.windowLevel = a + (E + 1)) :
    (E : ℝ) + 1 ≤ P.sideAtLevel a := by
  have e1 : P.sideAtLevel a = P.data.period Λ.stepParams.side * Λ.stepParams.side ^ (E + 1) := by
    show fineSide Λ.stepParams.side (P.data.windowLevel - a) (P.data.period Λ.stepParams.side) = _
    rw [fineSide_eq]
    congr 2
    omega
  have n1 : E + 1 < 2 ^ (E + 1) := Nat.lt_two_pow_self
  have n2 : 2 ^ (E + 1) ≤ Λ.stepParams.side ^ (E + 1) := Nat.pow_le_pow_left hL2 _
  have n3 : 1 ≤ P.data.period Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have n4 : E + 1 ≤ P.sideAtLevel a := by
    rw [e1]
    calc E + 1 ≤ Λ.stepParams.side ^ (E + 1) := by omega
      _ ≤ _ := Nat.le_mul_of_pos_left _ n3
  exact_mod_cast n4
end
section
private theorem hullDecayRate_pos {Tb : ParameterAssignment} (h : Tb.Admissible) : 0 < hullDecayRate Tb := by apply _root_.YangMills.SharedProofs.p22298 <;> assumption
private theorem gasRate_pos {Tb : ParameterAssignment} (h : Tb.Admissible) (h4 : 0 < Tb.κ₁) : 0 < Tb.gasRate := by
  unfold ParameterAssignment.gasRate
  have h1 := h.cE_pos
  have h2 := h.κ_pos
  have h3 : 0 < Tb.threshold := h.σ_pos
  have : 0 < min Tb.cE (min (Tb.κ * Tb.threshold ^ 2) (Tb.κ₁ * Tb.threshold ^ 2)) :=
    lt_min h1 (lt_min (by positivity) (by positivity))
  positivity
private theorem clusterRange_small {x : ℝ} (hx : 1521 ≤ x) :
    (clusterRange (2 * x) : ℝ) ≤ x ∧ 4 * (clusterRange (2 * x) : ℝ) ^ 2 + 3 ≤ x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  set y := x ^ ((1 : ℝ) / 4) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hx1 (by norm_num)
  have hyy : y ^ 4 = x := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have e1 : (2 * x) ^ ((1 : ℝ) / 100) ≤ y := by
    have h1 : 2 * x ≤ x ^ 2 := by nlinarith
    have h2 : (2 * x) ^ ((1 : ℝ) / 100) ≤ (x ^ 2) ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow (by linarith) h1 (by norm_num)
    have h3 : (x ^ 2) ^ ((1 : ℝ) / 100) = x ^ ((1 : ℝ) / 50) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    have h4 : x ^ ((1 : ℝ) / 50) ≤ y := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    linarith
  have e2 : (clusterRange (2 * x) : ℝ) ≤ 2 * y := by
    have h1 := (Nat.ceil_lt_add_one (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 2 * x) ((1 : ℝ) / 100))).le
    have h2 : (clusterRange (2 * x) : ℝ) = (⌈(2 * x) ^ ((1 : ℝ) / 100)⌉₊ : ℝ) := rfl
    linarith
  have e0 : (0 : ℝ) ≤ clusterRange (2 * x) := Nat.cast_nonneg _
  have hy2 : 39 ≤ y ^ 2 := by
    by_contra h
    push Not at h
    have h1 : y ^ 2 * y ^ 2 < 39 * 39 := by nlinarith
    have e : y ^ 2 * y ^ 2 = y ^ 4 := by ring
    rw [e, hyy] at h1
    norm_num at h1
    linarith
  have hyy2 : y ≤ y ^ 2 := by nlinarith
  constructor
  · nlinarith
  · have h1 : (clusterRange (2 * x) : ℝ) ^ 2 ≤ (2 * y) ^ 2 := pow_le_pow_left₀ e0 e2 2
    nlinarith
private theorem eventually_numeric_bounds (hFl : localChainFloorsStatement) (Kf c₀ K₁ K₂ e₁ e₂ B' : ℝ) (hKf : 0 ≤ Kf) (hc₀ : 0 < c₀)
    (he₁ : 0 < e₁) (he₂ : 0 < e₂) (P : ℕ) :
    ∃ X : ℝ, ∀ x, X ≤ x → 1521 ≤ x ∧ 800 * B' ≤ x ∧ K₂ + 2 ≤ x ^ 2 ∧ 8 * B' * Real.log x ^ 2 ≤ x ∧ LocalChainFloors Kf c₀ x ∧
      K₁ * x ^ (4 + P) * Real.exp (-(e₁ * x)) ≤ 1 ∧ K₂ * x ^ (8 + P) * Real.exp (-(e₂ * x)) ≤ 1 := by
  have a1 := hFl Kf c₀ hKf hc₀
  have a2 := eventually_mul_pow_mul_exp_le_one K₁ e₁ he₁ (4 + P)
  have a3 := eventually_mul_pow_mul_exp_le_one K₂ e₂ he₂ (8 + P)
  have hε : 0 < 1 / (8 * (|B'| + 1)) := by positivity
  have a4 := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound hε
  have a5 : ∀ᶠ x : ℝ in atTop, K₂ + 2 ≤ x ^ 2 := (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).eventually_ge_atTop _
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1
    (a1.and (a2.and (a3.and (a4.and (a5.and ((eventually_ge_atTop 1521).and (eventually_ge_atTop (800 * B'))))))))
  refine ⟨X, fun x hx => ?_⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hX x hx
  refine ⟨b6, b7, b5, ?_, b1, b2, b3⟩
  have hx0 : 0 < x := by linarith
  have h1 : Real.log x ^ 2 ≤ 1 / (8 * (|B'| + 1)) * x := by
    have : ‖Real.log x ^ 2‖ ≤ 1 / (8 * (|B'| + 1)) * ‖id x‖ := b4
    simpa [Real.norm_eq_abs, abs_of_pos hx0, abs_of_nonneg (sq_nonneg (Real.log x))] using this
  have h2 : 8 * B' * Real.log x ^ 2 ≤ 8 * (|B'| + 1) * Real.log x ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self B']) (sq_nonneg _)
  have h3 : 8 * (|B'| + 1) * Real.log x ^ 2 ≤ 8 * (|B'| + 1) * (1 / (8 * (|B'| + 1)) * x) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : 8 * (|B'| + 1) * (1 / (8 * (|B'| + 1)) * x) = x := by
    field_simp
  linarith
private theorem eventually_room (D Ξ Cw : ℝ) (hD : 0 < D) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → 2 ≤ x ∧ Cw * Real.log x ≤ x / 2 ∧
      (4 * Real.log x + 1) + 2 * Real.log (2 * x) ^ 2 + 2 ^ 10 * (2 * x) ^ ((1 : ℝ) / 20) + 8 ≤ (x - Ξ) / D := by
  set ε : ℝ := 1 / (2 * D * 2 ^ 12) with hε
  have hε0 : 0 < ε := by positivity
  set ε' : ℝ := 1 / (2 * (|Cw| + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  have e0 : ∀ᶠ x : ℝ in atTop, max 2 (2 * (9 * D + |Ξ|)) ≤ x := eventually_ge_atTop _
  have e1 := Real.isLittleO_log_id_atTop.bound hε0
  have e1' := Real.isLittleO_log_id_atTop.bound hε'0
  have e2 := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound hε0
  have e3 : ∀ᶠ x : ℝ in atTop, x ^ (-(19 / 20 : ℝ)) ≤ ε :=
    (tendsto_rpow_neg_atTop (y := 19 / 20) (by norm_num)).eventually_le_const hε0
  have e4 : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop 1
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp (e0.and (e1.and (e1'.and (e2.and (e3.and e4)))))
  refine ⟨X, fun x hx => ?_⟩
  obtain ⟨h0, h1, h1', h2, h3, h4⟩ := hX x hx
  have hx2 : 2 ≤ x := (le_max_left _ _).trans h0
  have hxb : 2 * (9 * D + |Ξ|) ≤ x := (le_max_right _ _).trans h0
  have hx0 : 0 < x := by linarith
  set l := Real.log x with hl
  have hl0 : 0 ≤ l := by linarith
  simp only [id, Real.norm_eq_abs, abs_of_nonneg hl0, abs_of_pos hx0] at h1 h1'
  have h2' : l ^ 2 ≤ ε * x := by
    have : ‖Real.log x ^ 2‖ ≤ ε * ‖id x‖ := h2
    simpa [Real.norm_eq_abs, abs_of_pos hx0, abs_of_nonneg (sq_nonneg l), ← hl] using this
  have hr : x ^ ((1 : ℝ) / 20) ≤ ε * x := by
    have e : x ^ ((1 : ℝ) / 20) = x ^ (-(19 / 20 : ℝ)) * x := by
      nth_rewrite 3 [← Real.rpow_one x]
      rw [← Real.rpow_add hx0]
      norm_num
    rw [e]
    exact mul_le_mul_of_nonneg_right h3 hx0.le
  have hlog2 : Real.log (2 * x) ≤ 2 * l := by
    rw [Real.log_mul (by norm_num) hx0.ne']
    have : Real.log 2 ≤ l := Real.log_le_log (by norm_num) hx2
    linarith
  have hlog0 : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hlog2sq : Real.log (2 * x) ^ 2 ≤ 4 * l ^ 2 := by nlinarith
  have hr2 : (2 * x) ^ ((1 : ℝ) / 20) ≤ 2 * x ^ ((1 : ℝ) / 20) := by
    rw [Real.mul_rpow (by norm_num) hx0.le]
    have : (2 : ℝ) ^ ((1 : ℝ) / 20) ≤ 2 := by
      calc (2 : ℝ) ^ ((1 : ℝ) / 20) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hx0.le _)
  refine ⟨hx2, ?_, ?_⟩
  · have hcw : Cw * l ≤ (|Cw| + 1) * l := mul_le_mul_of_nonneg_right (by linarith [le_abs_self Cw]) hl0
    have : (|Cw| + 1) * l ≤ (|Cw| + 1) * (ε' * x) := mul_le_mul_of_nonneg_left h1' (by positivity)
    have e : (|Cw| + 1) * (ε' * x) = x / 2 := by
      rw [hε']
      field_simp
    linarith
  · rw [le_div_iff₀ hD]
    have hsum : (4 * l + 1) + 2 * Real.log (2 * x) ^ 2 + 2 ^ 10 * (2 * x) ^ ((1 : ℝ) / 20) + 8 ≤ 2060 * (ε * x) + 9 := by
      nlinarith
    have hεx : 2060 * (ε * x) * D ≤ x / 2 := by
      have e : ε * D = 1 / 2 ^ 13 := by
        rw [hε]
        field_simp
      have : 2060 * (ε * x) * D = (2060 / 2 ^ 13) * x := by
        calc 2060 * (ε * x) * D = 2060 * (ε * D) * x := by ring
          _ = _ := by rw [e]; ring
      rw [this]
      nlinarith
    have hΞ := le_abs_self Ξ
    nlinarith
abbrev _root_.YangMills.SharedProofs.p10067 := @eventually_room
end
section
private theorem abs_flowCouplings_sub_le {Λ : MomentParameters} (T : StageTower Λ.stepParams) (β : ℝ) (u D : ℕ)
    (h : ∀ s ≤ u + D, (T.stage s).coupling = flowCouplings Λ.stepParams β s ∧
      |(T.stage s).nextCoupling - (T.stage s).coupling| ≤ 2 * Λ.stepParams.B) :
    ∀ a ≤ D, |flowCouplings Λ.stepParams β (u + a) - flowCouplings Λ.stepParams β u| ≤ 2 * Λ.stepParams.B * a := by
  intro a
  induction a with
  | zero =>
    intro _
    simp
  | succ a ih =>
    intro ha
    have h1 := ih (by omega)
    obtain ⟨e1, e2⟩ := h (u + a) (by omega)
    obtain ⟨e3, -⟩ := h (u + a + 1) (by omega)
    have e4 : (T.stage (u + a + 1)).coupling = (T.stage (u + a)).nextCoupling := rfl
    have e5 : flowCouplings Λ.stepParams β (u + (a + 1)) = (T.stage (u + a)).nextCoupling := by
      show flowCouplings Λ.stepParams β (u + a + 1) = _
      rw [← e3, e4]
    rw [e5]
    rw [e1] at e2
    have h2 := abs_sub_le (T.stage (u + a)).nextCoupling (flowCouplings Λ.stepParams β (u + a)) (flowCouplings Λ.stepParams β u)
    push_cast
    linarith
end
section
variable {Λ : MomentParameters} {S : MomentPoint Λ}
private def LimitLawAtPoint.extend (F : LimitLawAtPoint S) {J' : Type} [Countable J'] (g' : J' → SampleObservable Λ)
    (hm : ∀ j, TranslatedLaws.HasBoundedMoments (sampleFamily F.rule F.points F.period (g' j))) (sub : ℕ → ℕ) (hsub : StrictMono sub)
    (P' : Measure (TranslateValues (F.Index ⊕ J')))
    (hL : IsJointLimitLaw ((translatedTori F.points F.period).subsequence sub)
      (fun j i => Sum.elim (fun j => sampleFamily F.rule F.points F.period (F.observables j))
        (fun j => sampleFamily F.rule F.points F.period (g' j)) j (sub i)) P') :
    LimitLawAtPoint S where
  rule := F.rule
  rule_admissible := F.rule_admissible
  period := F.period
  one_le_period := F.one_le_period
  exponents := F.exponents ∘ sub
  strictMono_exponents := F.strictMono_exponents.comp hsub
  points := F.points ∘ sub
  points_eq := fun i => F.points_eq (sub i)
  Index := F.Index ⊕ J'
  countable_index := by
    haveI := F.countable_index
    infer_instance
  observables := Sum.elim F.observables g'
  hasBoundedMoments := by
    rintro (j | j)
    · exact ⟨fun i => (F.hasBoundedMoments j).aemeasurable (sub i), fun q => by
        obtain ⟨C, h⟩ := (F.hasBoundedMoments j).moment_bound q
        exact ⟨C, fun i => h (sub i)⟩⟩
    · exact ⟨fun i => (hm j).aemeasurable (sub i), fun q => by
        obtain ⟨C, h⟩ := (hm j).moment_bound q
        exact ⟨C, fun i => h (sub i)⟩⟩
  law := P'
  isJointLimitLaw := by
    have e : (fun (j : F.Index ⊕ J') => sampleFamily F.rule (F.points ∘ sub) F.period (Sum.elim F.observables g' j)) =
        fun j i => Sum.elim (fun j => sampleFamily F.rule F.points F.period (F.observables j))
          (fun j => sampleFamily F.rule F.points F.period (g' j)) j (sub i) := by
      funext j
      cases j <;> rfl
    rw [e]
    exact hL
private theorem integrable_eval_zero {F : LimitLawAtPoint S} (hM : jointLimitPropertiesStatement)
    (hk : (translatedTori F.points F.period).IsPreserving) (j : F.Index) :
    Integrable (fun v : TranslateValues F.Index => v (j, 0)) F.law := by apply _root_.YangMills.SharedProofs.p44385 <;> assumption
end
set_option maxHeartbeats 4000000 in
theorem curvatureLimitMomentStatement_holds (hF1 : stepFluctuationBoundStatement) (hF2 : siteIndicatorLimitBoundStatement)
    (hR1 : curvatureBelowFluctuationMassStatement) (hR2 : localChainSmallUnderFluctuationsStatement)
    (hHull : limitHullBoundsStatement) (hExt : jointLimitExtendStatement) (hMn : jointLimitPropertiesStatement)
    (hPL : largerToriStatement) (hWS : scaleWindowStatement) (hStp : localChainStepsWellPosedStatement)
    (hRow : transportedCurlFunctionalBoundsStatement) (hCB : coldBallDeviationMeasurableStatement) (hFl : localChainFloorsStatement)
    (hSB : StageStatesMeasurableStatement) (hLD : sampleBelowLawStatement) (hDL : forgetLastStepStatement)
    (hAR : ruleDrawsChainStatement) : curvatureLimitMomentStatement := by
  unfold stepFluctuationBoundStatement at hF1
  unfold siteIndicatorLimitBoundStatement at hF2
  unfold curvatureBelowFluctuationMassStatement at hR1
  unfold localChainSmallUnderFluctuationsStatement at hR2
  unfold limitHullBoundsStatement at hHull
  unfold largerToriStatement at hPL
  unfold scaleWindowStatement ForAllPoints at hWS
  unfold localChainStepsWellPosedStatement at hStp
  unfold transportedCurlFunctionalBoundsStatement at hRow
  unfold coldBallDeviationMeasurableStatement at hCB
  unfold curvatureLimitMomentStatement
  refine hullParams_imp (hullParams_and hF1 (hullParams_and hF2 (hullParams_and (hullParams_of_parameters hR1)
    (hullParams_and (hullParams_of_parameters hR2) (hullParams_and hHull (hullParams_and hPL
      (hullParams_and (hullParams_of_params hWS) (hullParams_and (hullParams_of_parameters hStp)
        (hullParams_and (hullParams_of_parameters hRow) (hullParams_and (hullParams_of_parameters hCB)
          (hullParams_of_params params_admissible))))))))))) ?_
  rintro Λ - ⟨A1, A2, ⟨C₁, xR1, HR1⟩, ⟨xR2, HR2⟩, ⟨Ch, -, hHl⟩, hP, ⟨Cw, _, Xw, _, _, hW⟩, hSt', hRw, ⟨xB, hBo⟩, hDr, hy, hyg⟩
  have hfit : Λ.stepParams.Admissible := hDr.fits Λ.floor hy
  have hlam := hfit.depth_lt
  have hodd : Odd Λ.stepParams.side := hDr.L_odd
  have hL2 : 2 ≤ Λ.stepParams.side := by
    have := hfit.L_ge
    omega
  have hBpos : 0 < Λ.stepParams.B := hfit.B_pos
  have hBp : 0 < 2 * Λ.stepParams.B := by linarith
  have hσ : Λ.stepParams.threshold / 64 ≤ 1 := by
    have h1 : Λ.stepParams.threshold ≤ 1 := hDr.σ_one
    have h0 := hfit.σ_pos
    linarith
  have hc5 : 0 < hullDecayRate Λ.table := hullDecayRate_pos hDr
  have hch : 0 < Λ.table.gasRate := gasRate_pos hDr hfit.κ₁_pos
  have hPF : ∀ P : MomentPoint Λ, SampleFacts P := fun P =>
    ⟨fun u n _ => hSB Λ.stepParams hfit P.tower u n,
      fun s d n _ => (hLD Λ.stepParams hfit hlam P.tower P.isCutoff P.marksMeasurable P.β (fun _ => 0)).1 s d n,
      fun u n _ => (hDL Λ.stepParams hfit hlam P.tower P.isCutoff P.marksMeasurable P.β u n).1⟩
  have etaStar : ∀ qq : ℕ, ∃ Cc xc : ℝ, 0 ≤ Cc ∧ ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (k j Rc Rr : ℕ)
      (cen : (S : MomentPoint Λ) → TorusSite (S.sideAtLevel (j + 1)))
      (Z : (S : MomentPoint Λ) → Finset (TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side)))
      (a : (S : MomentPoint Λ) → TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side) → ℝ) (A E : ℝ)
      (o : ∀ i, TorusSite ((F.points i).sideAtLevel (j + 1) * Λ.stepParams.side)) (jX : F.Index),
      1 ≤ qq → k ≤ j → j < k + 2 * localChainDepth Λ.stepParams S.β k → j + 1 ≤ S.data.windowLevel → 0 ≤ A → 0 ≤ E →
      (S.tower.stage j).nextCoupling ≤ 1.01 * (S.tower.stage j).coupling →
      (∀ i, IsLocalChainAbove Λ.table Λ.floor (F.points i).tower (F.points i).β k ((F.points i).sideAtLevel (j + 1)) 1 xc) →
      (∀ i, Z (F.points i) ⊆ chartBondsInBlocks Λ.stepParams.side
        (supBall (cen (F.points i)) ((localBlockSide Λ.stepParams (F.points i).β k : ℝ) / 8))) →
      (∀ i b, 0 ≤ a (F.points i) b) → (∀ i, ∑ b ∈ Z (F.points i), a (F.points i) b ≤ A) →
      (∀ i, supBall (cen (F.points i)) (localBlockSide Λ.stepParams (F.points i).β k) ⊆
        supBall ((F.points i).originSite (j + 1) ((F.points i).sideAtLevel (j + 1))) (Rc : ℝ)) →
      (∀ i, ((blocksNearFreeCores Λ.stepParams.side ((F.points i).tower.stage j).toStepSetup.range
          (supBall (cen (F.points i)) (localBlockSide Λ.stepParams (F.points i).β k))).card : ℝ) *
        Real.exp (-(7 * Λ.table.gasRate * ((F.points i).tower.stage j).coupling)) ≤ E) →
      (∀ i, ∀ b ∈ Z (F.points i), ∀ c : TorusBond ((F.points i).sideAtLevel (j + 1) * Λ.stepParams.side),
        (parentBlock Λ.stepParams.side c.1 = parentBlock Λ.stepParams.side b.1 ∨
          parentBlock Λ.stepParams.side c.1 = parentBlock Λ.stepParams.side (b.1 + unitStep _ b.2)) →
        c.1 ∈ supBall (o i) (Rr : ℝ) ∧ c.1 + unitStep _ c.2 ∈ supBall (o i) (Rr : ℝ)) →
      F.observables jX = caseObservable j (truncatedDeviationCases k j qq cen Z a) →
      ∀ᵐ v ∂F.law, F.condMeanAt jX v ≤ A * ((Cc * flowCouplings Λ.stepParams S.β k ^ (-(1 / 2 : ℝ))) ^ (2 * qq) + E) +
        A * (2 * (Rc : ℝ) + 1) ^ 4 * Real.exp (-(hullDecayRate Λ.table * S.coupling (j + 1))) := by
    intro qq
    obtain ⟨Cc, xc, h0, H⟩ := A1 qq
    refine ⟨Cc, xc, h0, ?_⟩
    intro S F k j Rc Rr cen Z a A E o jX hq hkj
    obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le hkj
    intro hj hK hA hE hx hloc hZ ha hsum hbox hEb hlocal hg
    exact H S F k j' Rc Rr cen Z a A E o jX hq (by omega) hK hA hE hx hloc hZ ha hsum hbox hEb hlocal hg
  have boJ : ∀ (P : MomentPoint Λ) (k j : ℕ) (c : TorusSite (P.sideAtLevel (j + 1)))
      (b : TorusBond (P.sideAtLevel (j + 1) * Λ.stepParams.side)),
      k ≤ j → j < k + 2 * localChainDepth Λ.stepParams P.β k →
      IsLocalChainAbove Λ.table Λ.floor P.tower P.β k (P.sideAtLevel (j + 1)) 1 xB →
      b ∈ chartBondsInBlocks Λ.stepParams.side (supBall c ((localBlockSide Λ.stepParams P.β k : ℝ) / 8)) →
      Measurable fun p : TorusField (P.sideAtLevel (j + 1)) × TorusField (P.sideAtLevel (j + 1) * Λ.stepParams.side) =>
        ‖coldDeviation P.tower j p.1 p.2 c (localBlockSide Λ.stepParams P.β k) b‖ := by
    intro P k j c b hkj
    obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le hkj
    intro hj hOn hb
    exact measurable_norm_of_measurableQuaternion (hBo P.tower P.β k (P.sideAtLevel (k + j' + 1)) 1 j' c b hOn
      (isBlockTorusSide_sideAtLevel P hfit _).1 (Nat.lt_of_add_lt_add_left hj) hb)
  obtain ⟨Xr, hXr⟩ := eventually_room (2 * Λ.stepParams.B) (couplingWindowTop Λ.stepParams Λ.g) (Cw 0) hBp
  have core : ∀ q : ℕ, ∃ Aq Xq : ℝ, 0 ≤ Aq ∧ ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (u E : ℕ) (z : Fin 4 → ℤ) (μ ν : Fin 4)
      (j : F.Index),
      1 ≤ q → μ < ν → Xq ≤ S.coupling u → S.data.windowLevel = u + 2 * localChainDepth Λ.stepParams S.β u + (E + 1) →
      (2 : ℝ) ^ 10 * localBoxRadius (S.coupling u) ≤ (E : ℝ) + 1 →
      0 ≤ S.scaleCoupling → S.scaleCoupling ≤ 2 * S.coupling u → (∀ a, (z a).natAbs ≤ 4 * S.range ^ 2) →
      F.observables j = clearCurvaturePower u z μ ν q →
      ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ Aq * (S.coupling u ^ q)⁻¹ := by
    intro q
    obtain ⟨Cp, xp, hCp, HP⟩ := etaStar q
    obtain ⟨Cq, xq, hCq, HQ⟩ := etaStar (3 * (q + 4))
    obtain ⟨Xn, hXn⟩ := eventually_numeric_bounds hFl (4 * (2 * (Λ.stepParams.side : ℝ) + 1) ^ 4) 1 (19 ^ 4)
      (3 ^ 4 * (2 * (Λ.stepParams.side : ℝ) + 1) ^ 4 * 9 ^ 4)
      (hullDecayRate Λ.table / 2) (7 * Λ.table.gasRate / 2) Λ.stepParams.B (by positivity) one_pos (by positivity) (by positivity)
      (3 * q + 40)
    refine ⟨(2 * |C₁|) ^ (2 * q) + 16 ^ (2 * q) * (8 * (Cp ^ (2 * q) + 2)) + 4 ^ q * (2 * (Cq ^ (2 * (3 * (q + 4))) + 2) + 2 + 1),
      max Xn (max (max xp xq) (max (max xR1 xR2) xB)), by positivity, ?_⟩
    intro S F u E z μ ν j hq hμν hXc hKE hWd hxs0 hxs hz hj
    classical
    haveI := F.countable_index
    have hXnx : Xn ≤ S.coupling u := (le_max_left _ _).trans hXc
    have hxpx : xp ≤ S.coupling u := (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hXc
    have hxqx : xq ≤ S.coupling u := (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hXc
    have hxR1 : xR1 ≤ S.coupling u :=
      ((((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hXc
    have hxR2 : xR2 ≤ S.coupling u :=
      ((((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hXc
    have hxB : xB ≤ S.coupling u := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hXc
    obtain ⟨n1, n2, n3, n4, Fl, n6, n7⟩ := hXn _ hXnx
    obtain ⟨x, hxd⟩ : ∃ x, x = S.coupling u := ⟨_, rfl⟩
    rw [← hxd] at n1 n2 n3 n4 Fl n6 n7 hXnx hxpx hxqx hxR1 hxR2 hxB hWd hxs ⊢
    have hx1 : 1 ≤ x := by linarith
    have hx0 : 0 < x := by linarith
    have hxc : flowCouplings Λ.stepParams S.β u = x := hxd.symm
    obtain ⟨M, hM⟩ : ∃ M, M = localChainDepth Λ.stepParams S.β u := ⟨_, rfl⟩
    obtain ⟨m, hm⟩ : ∃ m, m = localBlockSide Λ.stepParams S.β u := ⟨_, rfl⟩
    obtain ⟨ρ₀, hρ⟩ : ∃ ρ₀, ρ₀ = localLogScale Λ.stepParams S.β u := ⟨_, rfl⟩
    rw [← hM] at hKE
    have hMd : M = ⌊Real.log x ^ 2⌋₊ := by rw [hM, hxd]; rfl
    have hmd : m = ⌊x ^ ((1 : ℝ) / 20)⌋₊ := by rw [hm, hxd]; rfl
    have hρd : ρ₀ = (⌊Real.log x ^ 3⌋₊ : ℝ) := by rw [hρ, hxd]; rfl
    have hMl : (M : ℝ) ≤ Real.log x ^ 2 := by rw [hMd]; exact Nat.floor_le (sq_nonneg _)
    have hlogs : ρ₀ + M + 4 ≤ x ^ ((1 : ℝ) / 1000) := by rw [hρd, hMd]; exact Fl.logs_le
    have hρ1 : 1 ≤ ρ₀ := by rw [hρd]; exact Fl.one_le_scale
    have hxpow : x ^ ((1 : ℝ) / 1000) ≤ x := by
      have := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 : ℝ) / 1000 ≤ 1)
      simpa using this
    have hMx : (M : ℝ) ≤ x := by linarith
    have hmr : (m : ℝ) ≤ x ^ ((1 : ℝ) / 20) := by rw [hmd]; exact Nat.floor_le (Real.rpow_nonneg hx0.le _)
    have hmx : (m : ℝ) ≤ x := by
      have := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 : ℝ) / 20 ≤ 1)
      simp only [Real.rpow_one] at this
      linarith
    have rad0 : 20 * x ^ ((1 : ℝ) / 90) + 4 * ρ₀ + 4 ≤ (m : ℝ) / 8 := by rw [hρd, hmd]; exact Fl.radii_le
    have hp90 : 1 ≤ x ^ ((1 : ℝ) / 90) := Real.one_le_rpow hx1 (by norm_num)
    have hβ : ∀ (F' : LimitLawAtPoint S) i, (F'.points i).β = S.β := fun F' i => (points_fields_eq F' i).2.1
    have hKF : ∀ (F' : LimitLawAtPoint S) i, (F'.points i).data.windowLevel = S.data.windowLevel := fun F' i => (points_fields_eq F' i).1
    have hTF : ∀ (F' : LimitLawAtPoint S) i, (F'.points i).tower = S.tower := fun F' i => (points_fields_eq F' i).2.2
    have hxP : ∀ P : MomentPoint Λ, P.β = S.β → P.coupling u = x := fun P h => by
      rw [hxd]
      unfold MomentPoint.coupling
      rw [h]
    have hMP : ∀ P : MomentPoint Λ, P.β = S.β → localChainDepth Λ.stepParams P.β u = M := fun P h => by rw [h, hM]
    have hmP : ∀ P : MomentPoint Λ, P.β = S.β → localBlockSide Λ.stepParams P.β u = m := fun P h => by rw [h, hm]
    have hρP : ∀ P : MomentPoint Λ, P.β = S.β → localLogScale Λ.stepParams P.β u = ρ₀ := fun P h => by rw [h, hρ]
    have onP : ∀ (P : MomentPoint Λ), P.β = S.β → P.data.windowLevel = S.data.windowLevel → ∀ (a : ℕ) (x₀ : ℝ), x₀ ≤ x →
        a ≤ u + M + M → IsLocalChainAbove Λ.table Λ.floor P.tower P.β u (P.sideAtLevel a) 1 x₀ := by
      intro P hβ' hK' a x₀ hx₀ ha
      have hKM : P.data.windowLevel = (u + M + M) + (E + 1) := by omega
      have h1 := le_sideAtLevel P hL2 (u + M + M) E hKM
      have h2 : (P.sideAtLevel (u + M + M) : ℝ) ≤ P.sideAtLevel a := by exact_mod_cast sideAtLevel_antitone P ha
      refine isLocalChainAbove_of_point hyg hBp P u _ x₀ (by rw [hxP P hβ']; exact hx₀) (by rw [hxP P hβ']; exact hx1)
        (by rw [hMP P hβ']; omega) ?_
      rw [hxP P hβ']
      linarith
    have hOnS := onP S rfl rfl (u + M + M) x le_rfl le_rfl
    have hsteps := hSt' S.tower S.β u (S.sideAtLevel (u + M + M)) 1 x hOnS
    rw [← hM] at hsteps
    have hnear := abs_flowCouplings_sub_le S.tower S.β u (2 * M) (fun s hs => by
      obtain ⟨-, a2, a3, -⟩ := hsteps s hs
      exact ⟨a2, a3⟩)
    have hBM : 4 * Λ.stepParams.B * M ≤ x / 2 := by
      have h1 := mul_le_mul_of_nonneg_left hMl (by linarith : 0 ≤ 8 * Λ.stepParams.B)
      linarith
    have hlev : ∀ s, u ≤ s → s ≤ u + 2 * M → x / 2 ≤ S.coupling s ∧ S.coupling s ≤ 2 * x := by
      intro s h1 h2
      obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le h1
      have h3 := hnear a (by omega)
      rw [hxc] at h3
      have h4 : (a : ℝ) ≤ 2 * M := by exact_mod_cast (by omega : a ≤ 2 * M)
      have h5 : 2 * Λ.stepParams.B * a ≤ 2 * Λ.stepParams.B * (2 * M) := mul_le_mul_of_nonneg_left h4 hBp.le
      have h6 := abs_le.mp h3
      have e : S.coupling (u + a) = flowCouplings Λ.stepParams S.β (u + a) := rfl
      rw [e]
      constructor <;> linarith [h6.1, h6.2]
    have hlevx : ∀ s, s ≤ u + 2 * M → (S.tower.stage s).coupling = S.coupling s := fun s hs => (hsteps s hs).2.1
    have hx' : ∀ s, u ≤ s → s ≤ u + 2 * M → (S.tower.stage s).nextCoupling ≤ 1.01 * (S.tower.stage s).coupling := by
      intro s h1 h2
      obtain ⟨-, a2, a3, -⟩ := hsteps s h2
      have h4 := (abs_le.mp a3).2
      have h5 := (hlev s h1 h2).1
      have h6 : (S.tower.stage s).coupling = S.coupling s := a2
      have hB' : Λ.table.B = Λ.stepParams.B := rfl
      rw [hB'] at h4
      rw [h6] at h4 ⊢
      linarith
    obtain ⟨rb, hrb⟩ : ∃ rb, rb = clusterRange (2 * x) := ⟨_, rfl⟩
    obtain ⟨hrbx, hrb2⟩ := clusterRange_small n1
    rw [← hrb] at hrbx hrb2
    have hrS : ∀ s, u ≤ s → s ≤ u + 2 * M → (S.tower.stage s).toStepSetup.range ≤ rb := by
      intro s h1 h2
      have h3 : (S.tower.stage s).toStepSetup.range = clusterRange (S.coupling s) := by
        rw [← hlevx s h2]
        rfl
      rw [h3, hrb]
      exact Nat.ceil_mono (Real.rpow_le_rpow (by linarith [(hlev s h1 h2).1]) (hlev s h1 h2).2 (by norm_num))
    have hSr : S.range ≤ rb := by
      rw [hrb]
      exact Nat.ceil_mono (Real.rpow_le_rpow hxs0 hxs (by norm_num))
    obtain ⟨tN, htN⟩ : ∃ tN, tN = 4 * S.range ^ 2 + 3 := ⟨_, rfl⟩
    have ht3 : 3 ≤ tN := by omega
    have hz' : ∀ a, (z a).natAbs ≤ tN := fun a => by
      have := hz a
      omega
    have htx : (tN : ℝ) ≤ x := by
      have h1 : (S.range : ℝ) ≤ rb := by exact_mod_cast hSr
      have h2 : (S.range : ℝ) ^ 2 ≤ (rb : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
      rw [htN]
      push_cast
      linarith
    obtain ⟨Rc, hRc⟩ : ∃ Rc, Rc = 2 * m + 4 * rb + 1 + tN := ⟨_, rfl⟩
    obtain ⟨Rr, hRr⟩ : ∃ Rr, Rr = 4 * rb + Λ.stepParams.side + Λ.stepParams.side * (m + 1) + 1 := ⟨_, rfl⟩
    obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (x ^ (3 * q + 40))⁻¹ := ⟨_, rfl⟩
    have hε0 : 0 ≤ ε := by rw [hε]; positivity
    have hRcx : (Rc : ℝ) ≤ 8 * x := by
      rw [hRc]
      push_cast
      linarith
    have hpowx : ∀ a b : ℕ, x ^ (a + b) * (x ^ b)⁻¹ = x ^ a := fun a b => by
      rw [pow_add, mul_assoc, mul_inv_cancel₀ (pow_pos hx0 b).ne', mul_one]
    have hHb : ∀ s, u ≤ s → s ≤ u + 2 * M →
        (2 * (Rc : ℝ) + 1) ^ 4 * Real.exp (-(hullDecayRate Λ.table * S.coupling s)) ≤ ε := by
      intro s h1 h2
      have a1 : (2 * (Rc : ℝ) + 1) ^ 4 ≤ 19 ^ 4 * x ^ 4 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith) 4
      have a2 : Real.exp (-(hullDecayRate Λ.table * S.coupling s)) ≤ Real.exp (-(hullDecayRate Λ.table / 2 * x)) := by
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_left (hlev s h1 h2).1 hc5.le
        linarith
      have a3 : (2 * (Rc : ℝ) + 1) ^ 4 * Real.exp (-(hullDecayRate Λ.table * S.coupling s)) ≤
          19 ^ 4 * x ^ 4 * Real.exp (-(hullDecayRate Λ.table / 2 * x)) :=
        mul_le_mul a1 a2 (Real.exp_pos _).le (by positivity)
      refine a3.trans ?_
      have a4 : (19 : ℝ) ^ 4 * x ^ (4 + (3 * q + 40)) * Real.exp (-(hullDecayRate Λ.table / 2 * x)) ≤ 1 := n6
      rw [hε, ← mul_one ((x ^ (3 * q + 40))⁻¹)]
      have a5 := mul_le_mul_of_nonneg_left a4 (inv_pos.mpr (pow_pos hx0 (3 * q + 40))).le
      refine le_trans (le_of_eq ?_) a5
      have e := hpowx 4 (3 * q + 40)
      calc 19 ^ 4 * x ^ 4 * Real.exp (-(hullDecayRate Λ.table / 2 * x))
          = 19 ^ 4 * (x ^ (4 + (3 * q + 40)) * (x ^ (3 * q + 40))⁻¹) * Real.exp (-(hullDecayRate Λ.table / 2 * x)) := by rw [e]
        _ = _ := by ring
    have hNb : ∀ r, r ≤ rb → (((2 * m + 1) ^ 4 * (2 * Λ.stepParams.side + 1) ^ 4 * (8 * r + 1) ^ 4 : ℕ) : ℝ) ≤
        3 ^ 4 * (2 * (Λ.stepParams.side : ℝ) + 1) ^ 4 * 9 ^ 4 * x ^ 8 := by
      intro r hr
      have h1 : (r : ℝ) ≤ rb := by exact_mod_cast hr
      have a1 : (2 * (m : ℝ) + 1) ^ 4 ≤ (3 * x) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
      have a2 : (8 * (r : ℝ) + 1) ^ 4 ≤ (9 * x) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
      push_cast
      have a3 := mul_le_mul_of_nonneg_right a1 (by positivity : (0 : ℝ) ≤ (2 * (Λ.stepParams.side : ℝ) + 1) ^ 4)
      have a4 := mul_le_mul a3 a2 (by positivity) (by positivity)
      refine a4.trans (le_of_eq ?_)
      ring
    have hEb : ∀ s, u ≤ s → s ≤ u + 2 * M → ∀ r, r ≤ rb →
        (((2 * m + 1) ^ 4 * (2 * Λ.stepParams.side + 1) ^ 4 * (8 * r + 1) ^ 4 : ℕ) : ℝ) *
          Real.exp (-(7 * Λ.table.gasRate * S.coupling s)) ≤ ε := by
      intro s h1 h2 r hr
      have a2 : Real.exp (-(7 * Λ.table.gasRate * S.coupling s)) ≤ Real.exp (-(7 * Λ.table.gasRate / 2 * x)) := by
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_left (hlev s h1 h2).1 (by positivity : 0 ≤ 7 * Λ.table.gasRate)
        linarith
      have a3 := mul_le_mul (hNb r hr) a2 (Real.exp_pos _).le (by positivity)
      refine a3.trans ?_
      have a4 : 3 ^ 4 * (2 * (Λ.stepParams.side : ℝ) + 1) ^ 4 * 9 ^ 4 * x ^ (8 + (3 * q + 40)) *
          Real.exp (-(7 * Λ.table.gasRate / 2 * x)) ≤ 1 := n7
      rw [hε, ← mul_one ((x ^ (3 * q + 40))⁻¹)]
      have a5 := mul_le_mul_of_nonneg_left a4 (inv_pos.mpr (pow_pos hx0 (3 * q + 40))).le
      refine le_trans (le_of_eq ?_) a5
      have e := hpowx 8 (3 * q + 40)
      calc 3 ^ 4 * (2 * (Λ.stepParams.side : ℝ) + 1) ^ 4 * 9 ^ 4 * x ^ 8 * Real.exp (-(7 * Λ.table.gasRate / 2 * x))
          = 3 ^ 4 * (2 * (Λ.stepParams.side : ℝ) + 1) ^ 4 * 9 ^ 4 * (x ^ (8 + (3 * q + 40)) * (x ^ (3 * q + 40))⁻¹) *
              Real.exp (-(7 * Λ.table.gasRate / 2 * x)) := by rw [e]
        _ = _ := by ring
    have hRad : ∀ (nn : ℝ), 0 ≤ nn → nn ≤ 1 → ∀ i,
        (ballRadius Λ.stepParams.side nn ρ₀ i + 1) / (Λ.stepParams.side : ℝ) + 2 ≤ (m : ℝ) / 8 := by
      intro nn h0 h1 i
      have hL1 : (1 : ℝ) ≤ (Λ.stepParams.side : ℝ) := by exact_mod_cast (by omega : 1 ≤ Λ.stepParams.side)
      have hpow : (1 : ℝ) ≤ (Λ.stepParams.side : ℝ) ^ i := one_le_pow₀ hL1
      have h2 : ballRadius Λ.stepParams.side nn ρ₀ i ≤ 20 + 4 * ρ₀ := by
        unfold ballRadius
        have h3 : 20 * nn / (Λ.stepParams.side : ℝ) ^ i ≤ 20 * nn := div_le_self (by positivity) hpow
        linarith
      have h4 : 0 ≤ ballRadius Λ.stepParams.side nn ρ₀ i := by
        unfold ballRadius
        have : 0 ≤ ρ₀ := by linarith
        positivity
      have h5 : (ballRadius Λ.stepParams.side nn ρ₀ i + 1) / (Λ.stepParams.side : ℝ) ≤ ballRadius Λ.stepParams.side nn ρ₀ i + 1 :=
        div_le_self (by linarith) hL1
      linarith
    have hRad2 : ∀ d, ballRadius Λ.stepParams.side 1 ρ₀ (d + 1) - 3 * ρ₀ ≤ (m : ℝ) / 8 := by
      intro d
      have hL1 : (1 : ℝ) ≤ (Λ.stepParams.side : ℝ) := by exact_mod_cast (by omega : 1 ≤ Λ.stepParams.side)
      have hpow : (1 : ℝ) ≤ (Λ.stepParams.side : ℝ) ^ (d + 1) := one_le_pow₀ hL1
      unfold ballRadius
      have h3 : 20 * 1 / (Λ.stepParams.side : ℝ) ^ (d + 1) ≤ 20 * 1 := div_le_self (by positivity) hpow
      linarith
    have hm8 : (m : ℝ) / 8 ≤ m := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      linarith
    have hCard : ∀ {n : ℕ} [NeZero n] (c : TorusSite n) (R : ℝ), 0 ≤ R → R ≤ (m : ℝ) / 8 →
        ((chartBondsInBlocks Λ.stepParams.side (supBall c R)).card : ℝ) ≤ x := by
      intro n _ c R h0 h1
      refine (card_chartBondsInBlocks_le c h0).trans ?_
      have h2 : 2 * R + 1 ≤ x ^ ((1 : ℝ) / 20) := by linarith
      have h3 : (2 * R + 1) ^ 4 ≤ x ^ ((1 : ℝ) / 5) := by
        have h4 := pow_le_pow_left₀ (by positivity) h2 4
        refine h4.trans (le_of_eq ?_)
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
        norm_num
      have h5 : 4 * (2 * (Λ.stepParams.side : ℝ) + 1) ^ 4 * x ^ ((1 : ℝ) / 5) ≤ x := Fl.card_le
      have h6 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 4 * (2 * (Λ.stepParams.side : ℝ) + 1) ^ 4)
      calc 4 * (2 * R + 1) ^ 4 * (2 * (Λ.stepParams.side : ℝ) + 1) ^ 4 = 4 * (2 * (Λ.stepParams.side : ℝ) + 1) ^ 4 * (2 * R + 1) ^ 4 := by ring
        _ ≤ _ := h6.trans h5
    have hCenL : ∀ (P : MomentPoint Λ) (i : ℕ), TorusFields.supDist (lowerCentre u z i P) (P.originSite (u + i + 1) (P.sideAtLevel (u + i + 1))) ≤ tN :=
      fun P i => lowerCentre_near P hodd hL2 u z tN ht3 hz' i
    have hCenH : ∀ (P : MomentPoint Λ) (i : ℕ),
        TorusFields.supDist (upperCentre u M z i P) (P.originSite (u + M + i + 1) (P.sideAtLevel (u + M + i + 1))) ≤ tN :=
      fun P i => upperCentre_near P hodd hL2 u M z tN ht3 hz' i
    have hcb : m + tN ≤ Rc := by omega
    have hRr1 : Λ.stepParams.side + Λ.stepParams.side * (m + 1) + 1 ≤ Rr := by omega
    have hEnear : ∀ (P : MomentPoint Λ), P.tower = S.tower → ∀ s, u ≤ s → s ≤ u + 2 * M → ∀ {n : ℕ} [NeZero n] (c : TorusSite n),
        ((blocksNearFreeCores Λ.stepParams.side (P.tower.stage s).toStepSetup.range (supBall c (m : ℝ))).card : ℝ) *
          Real.exp (-(7 * Λ.table.gasRate * (P.tower.stage s).coupling)) ≤ ε := by
      intro P hT s h1 h2 n _ c
      rw [hT, hlevx s h2]
      have h3 := card_blocksNearFreeCores_le Λ.stepParams.side (S.tower.stage s).toStepSetup.range m c
      have h4 : ((blocksNearFreeCores Λ.stepParams.side (S.tower.stage s).toStepSetup.range (supBall c (m : ℝ))).card : ℝ) ≤
          (((2 * m + 1) ^ 4 * (2 * Λ.stepParams.side + 1) ^ 4 * (8 * (S.tower.stage s).toStepSetup.range + 1) ^ 4 : ℕ) : ℝ) := by
        exact_mod_cast h3
      exact (mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le).trans (hEb s h1 h2 _ (hrS s h1 h2))
    have hlt : ∀ d, d < M → u + d < u + 2 * localChainDepth Λ.stepParams S.β u := fun d hd => by rw [← hM]; omega
    have hlt2 : ∀ d, d < M → u + M + d < u + 2 * localChainDepth Λ.stepParams S.β u := fun d hd => by rw [← hM]; omega
    have hrowP : ∀ (P : MomentPoint Λ) (d : ℕ), ∑ b ∈ lowerBonds u z d P, lowerWeight u z μ ν d P b ≤ 4 * (1 / 2) ^ d := by
      intro P d
      have hbs := isBlockTorusSide_sideAtLevel P hfit (u + d + 1)
      have hLp : 1 ≤ Λ.stepParams.side := by omega
      have hN : Λ.table.n₀ ≤ P.sideAtLevel (u + d + 1) * Λ.stepParams.side := by
        have h1 : Λ.stepParams.side * Λ.stepParams.n₀ ≤ P.sideAtLevel (u + d + 1) := hbs.2
        have h2 : Λ.stepParams.n₀ ≤ Λ.stepParams.side * Λ.stepParams.n₀ := Nat.le_mul_of_pos_left _ hLp
        have h3 : P.sideAtLevel (u + d + 1) ≤ P.sideAtLevel (u + d + 1) * Λ.stepParams.side := Nat.le_mul_of_pos_right _ hLp
        exact h2.trans (h1.trans h3)
      have h1 := (hRw.1 u d (P.sideAtLevel (u + d + 1) * Λ.stepParams.side) hN
        (lowerSite P u z (d + 1) (P.sideAtLevel (u + d + 1)), μ, ν) (by
          simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hμν, fun _ _ => trivial⟩)).2
      exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _) h1
    have hZlow : ∀ (P : MomentPoint Λ), P.β = S.β → ∀ d,
        lowerBonds u z d P ⊆ chartBondsInBlocks Λ.stepParams.side (supBall (lowerCentre u z d P) ((m : ℝ) / 8)) := by
      intro P h d
      unfold lowerBonds readBondsAtLevel
      rw [hρP P h]
      exact chartBondsInBlocks_mono _ (hRad2 d)
    have hZql : ∀ (P : MomentPoint Λ), P.β = S.β → ∀ i,
        lowerMaxBonds u z i P ⊆ chartBondsInBlocks Λ.stepParams.side (supBall (lowerCentre u z i P) ((m : ℝ) / 8)) := by
      intro P h i
      unfold lowerMaxBonds
      rw [hρP P h]
      exact chartBondsInBlocks_mono _ (hRad 1 zero_le_one le_rfl i)
    have hnn : (1 : ℝ) / (Λ.stepParams.side : ℝ) ^ M ≤ 1 := by
      have hL1 : (1 : ℝ) ≤ (Λ.stepParams.side : ℝ) := by exact_mod_cast (by omega : 1 ≤ Λ.stepParams.side)
      exact div_le_one_of_le₀ (one_le_pow₀ hL1) (by positivity)
    have hZqh : ∀ (P : MomentPoint Λ), P.β = S.β → ∀ i,
        upperMaxBonds u M z i P ⊆ chartBondsInBlocks Λ.stepParams.side (supBall (upperCentre u M z i P) ((m : ℝ) / 8)) := by
      intro P h i
      unfold upperMaxBonds
      rw [hρP P h]
      exact chartBondsInBlocks_mono _ (hRad _ (by positivity) hnn i)
    have hm0 : (0 : ℝ) ≤ (m : ℝ) / 8 := by positivity
    have hRadP : ∀ i, (0 : ℝ) ≤ (ballRadius Λ.stepParams.side 1 ρ₀ i + 1) / (Λ.stepParams.side : ℝ) + 2 := fun i => by
      have : 0 ≤ ρ₀ := by linarith
      unfold ballRadius
      positivity
    have hRadQ : ∀ i, (0 : ℝ) ≤ (ballRadius Λ.stepParams.side (1 / (Λ.stepParams.side : ℝ) ^ M) ρ₀ i + 1) / (Λ.stepParams.side : ℝ) + 2 :=
      fun i => by
        have : 0 ≤ ρ₀ := by linarith
        unfold ballRadius
        positivity
    have hsumQL : ∀ (P : MomentPoint Λ), P.β = S.β → ∀ i, ∑ b ∈ lowerMaxBonds u z i P, (1 : ℝ) ≤ x := by
      intro P h i
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      unfold lowerMaxBonds
      rw [hρP P h]
      exact hCard _ _ (hRadP i) (hRad 1 zero_le_one le_rfl i)
    have hsumQH : ∀ (P : MomentPoint Λ), P.β = S.β → ∀ i, ∑ b ∈ upperMaxBonds u M z i P, (1 : ℝ) ≤ x := by
      intro P h i
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      unfold upperMaxBonds
      rw [hρP P h]
      exact hCard _ _ (hRadQ i) (hRad _ (by positivity) hnn i)
    have hHle : ∀ (A : ℝ), 0 ≤ A → ∀ s, u ≤ s → s ≤ u + 2 * M → ∀ c : ℝ,
        A * (c + ε) + A * (2 * (Rc : ℝ) + 1) ^ 4 * Real.exp (-(hullDecayRate Λ.table * S.coupling s)) ≤ A * (c + 2 * ε) := by
      intro A hA s h1 h2 c
      have h3 := mul_le_mul_of_nonneg_left (hHb s h1 h2) hA
      nlinarith
    have starP : ∀ (F' : LimitLawAtPoint S) (d : ℕ), d < M → ∀ jX : F'.Index, F'.observables jX = transportPowerObs u z μ ν q d →
        ∀ᵐ v ∂F'.law, F'.condMeanAt jX v ≤ (4 * (1 / 2) ^ d) * ((Cp * x ^ (-(1 / 2 : ℝ))) ^ (2 * q) + 2 * ε) := by
      intro F' d hd jX hg
      have hZ := fun i => hZlow (F'.points i) (hβ F' i) d
      have h := HP S F' u (u + d) Rc Rr (lowerCentre u z d) (lowerBonds u z d) (lowerWeight u z μ ν d) (4 * (1 / 2) ^ d) ε
        (fun i => blockCentreSite Λ.stepParams.side (lowerCentre u z d (F'.points i))) jX hq (Nat.le_add_right _ _) (hlt d hd)
        (by omega) (by positivity) hε0
        (hx' _ (by omega) (by omega)) (fun i => onP _ (hβ F' i) (hKF F' i) _ xp hxpx (by omega))
        (fun i => by rw [hmP _ (hβ F' i)]; exact hZ i) (fun i b => abs_nonneg _) (fun i => hrowP _ d)
        (fun i => by rw [hmP _ (hβ F' i)]; exact supBall_subset_supBall _ _ m tN Rc (hCenL _ d) hcb)
        (fun i => by rw [hmP _ (hβ F' i)]; exact hEnear _ (hTF F' i) (u + d) (by omega) (by omega) _)
        (fun i b hb c hc => bond_mem_supBall_of_chart hodd hL2 _ m Rr (by linarith) hRr1 (hZ i hb) c hc) hg
      filter_upwards [h] with v hv
      refine hv.trans ?_
      rw [hxc]
      exact hHle _ (by positivity) (u + d + 1) (by omega) (by omega) _
    have starQL : ∀ (F' : LimitLawAtPoint S) (d : ℕ), d < M → ∀ jX : F'.Index,
        F'.observables jX = lowerMaxObs u z (3 * (q + 4)) d → ∀ᵐ v ∂F'.law,
          F'.condMeanAt jX v ≤ x * ((Cq * x ^ (-(1 / 2 : ℝ))) ^ (2 * (3 * (q + 4))) + 2 * ε) := by
      intro F' d hd jX hg
      have hZ := fun i => hZql (F'.points i) (hβ F' i) d
      have h := HQ S F' u (u + d) Rc Rr (lowerCentre u z d) (lowerMaxBonds u z d) (fun _ _ => 1) x ε
        (fun i => blockCentreSite Λ.stepParams.side (lowerCentre u z d (F'.points i))) jX (by omega) (Nat.le_add_right _ _) (hlt d hd)
        (by omega) hx0.le hε0
        (hx' _ (by omega) (by omega)) (fun i => onP _ (hβ F' i) (hKF F' i) _ xq hxqx (by omega))
        (fun i => by rw [hmP _ (hβ F' i)]; exact hZ i) (fun i b => zero_le_one) (fun i => hsumQL _ (hβ F' i) d)
        (fun i => by rw [hmP _ (hβ F' i)]; exact supBall_subset_supBall _ _ m tN Rc (hCenL _ d) hcb)
        (fun i => by rw [hmP _ (hβ F' i)]; exact hEnear _ (hTF F' i) (u + d) (by omega) (by omega) _)
        (fun i b hb c hc => bond_mem_supBall_of_chart hodd hL2 _ m Rr (by linarith) hRr1 (hZ i hb) c hc) hg
      filter_upwards [h] with v hv
      refine hv.trans ?_
      rw [hxc]
      exact hHle _ hx0.le (u + d + 1) (by omega) (by omega) _
    have starQH : ∀ (F' : LimitLawAtPoint S) (d : ℕ), d < M → ∀ jX : F'.Index,
        F'.observables jX = upperMaxObs u M z (3 * (q + 4)) d → ∀ᵐ v ∂F'.law,
          F'.condMeanAt jX v ≤ x * ((Cq * x ^ (-(1 / 2 : ℝ))) ^ (2 * (3 * (q + 4))) + 2 * ε) := by
      intro F' d hd jX hg
      have hZ := fun i => hZqh (F'.points i) (hβ F' i) d
      have h := HQ S F' u (u + M + d) Rc Rr (upperCentre u M z d) (upperMaxBonds u M z d) (fun _ _ => 1) x ε
        (fun i => blockCentreSite Λ.stepParams.side (upperCentre u M z d (F'.points i))) jX (by omega) (by omega) (hlt2 d hd)
        (by omega) hx0.le hε0
        (hx' _ (by omega) (by omega)) (fun i => onP _ (hβ F' i) (hKF F' i) _ xq hxqx (by omega))
        (fun i => by rw [hmP _ (hβ F' i)]; exact hZ i) (fun i b => zero_le_one) (fun i => hsumQH _ (hβ F' i) d)
        (fun i => by rw [hmP _ (hβ F' i)]; exact supBall_subset_supBall _ _ m tN Rc (hCenH _ d) hcb)
        (fun i => by rw [hmP _ (hβ F' i)]; exact hEnear _ (hTF F' i) (u + M + d) (by omega) (by omega) _)
        (fun i b hb c hc => bond_mem_supBall_of_chart hodd hL2 _ m Rr (by linarith) hRr1 (hZ i hb) c hc) hg
      filter_upwards [h] with v hv
      refine hv.trans ?_
      rw [hxc]
      exact hHle _ hx0.le (u + M + d + 1) (by omega) (by omega) _
    obtain ⟨Nz, hNz⟩ : ∃ Nz : ℝ, Nz = 3 ^ 4 * (2 * (Λ.stepParams.side : ℝ) + 1) ^ 4 * 9 ^ 4 * x ^ 8 := ⟨_, rfl⟩
    have hNz0 : 0 ≤ Nz := by rw [hNz]; positivity
    have hRr2 : ∀ r, r ≤ rb → 4 * r + Λ.stepParams.side + Λ.stepParams.side * m + 1 ≤ Rr := fun r hr => by
      have : Λ.stepParams.side * m ≤ Λ.stepParams.side * (m + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    have hsiteLow : ∀ (F' : LimitLawAtPoint S) (d : ℕ), d < M → ∀ i (y : TorusSite ((F'.points i).sideAtLevel (u + d + 1) * Λ.stepParams.side)),
        y ∈ lowerSites u z d (F'.points i) →
        y ∈ thickening (4 * ((F'.points i).tower.stage (u + d)).toStepSetup.range)
            (sitesInBlocks Λ.stepParams.side (supBall (lowerCentre u z d (F'.points i)) (m : ℝ))) ∧
          ((F'.points i).tower.stage (u + d)).toStepSetup.range ≤ rb := by
      intro F' d hd i y hy
      unfold lowerSites at hy
      rw [hmP _ (hβ F' i)] at hy
      refine ⟨hy, ?_⟩
      rw [hTF F' i]
      exact hrS _ (by omega) (by omega)
    have hsiteHigh : ∀ (F' : LimitLawAtPoint S) (d : ℕ), d < M →
        ∀ i (y : TorusSite ((F'.points i).sideAtLevel (u + M + d + 1) * Λ.stepParams.side)), y ∈ upperSites u M z d (F'.points i) →
        y ∈ thickening (4 * ((F'.points i).tower.stage (u + M + d)).toStepSetup.range)
            (sitesInBlocks Λ.stepParams.side (supBall (upperCentre u M z d (F'.points i)) (m : ℝ))) ∧
          ((F'.points i).tower.stage (u + M + d)).toStepSetup.range ≤ rb := by
      intro F' d hd i y hy
      unfold upperSites at hy
      rw [hmP _ (hβ F' i)] at hy
      refine ⟨hy, ?_⟩
      rw [hTF F' i]
      exact hrS _ (by omega) (by omega)
    have starSL : ∀ (F' : LimitLawAtPoint S) (d : ℕ), d < M → ∀ jX : F'.Index, F'.observables jX = lowerSiteObs u z d →
        ∀ᵐ v ∂F'.law, F'.condMeanAt jX v ≤ Nz * ε + ε := by
      intro F' d hd jX hg
      have hc : ∀ i, ((lowerSites u z d (F'.points i)).card : ℝ) ≤ Nz := by
        intro i
        have hr : ((F'.points i).tower.stage (u + d)).toStepSetup.range ≤ rb := by
          rw [hTF F' i]
          exact hrS _ (by omega) (by omega)
        unfold lowerSites
        rw [hmP _ (hβ F' i), hNz]
        have h1 := card_thickening_sitesInBlocks_le Λ.stepParams.side ((F'.points i).tower.stage (u + d)).toStepSetup.range m
          (lowerCentre u z d (F'.points i))
        have h2 : ((thickening (4 * ((F'.points i).tower.stage (u + d)).toStepSetup.range)
            (sitesInBlocks Λ.stepParams.side (supBall (lowerCentre u z d (F'.points i)) (m : ℝ)))).card : ℝ) ≤
            (((2 * m + 1) ^ 4 * (2 * Λ.stepParams.side + 1) ^ 4 *
              (8 * ((F'.points i).tower.stage (u + d)).toStepSetup.range + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast h1
        exact h2.trans (hNb _ hr)
      have h := A2 S F' (u + d) Rc Rr (lowerSites u z d) (m : ℝ) Nz ε
        (fun i => blockCentreSite Λ.stepParams.side (lowerCentre u z d (F'.points i))) jX (by omega) (Nat.cast_nonneg _) hε0 hNz0
        (hx' _ (by omega) (by omega)) hc
        (fun i y hy => by
          obtain ⟨a1, a2⟩ := hsiteLow F' d hd i y hy
          exact supBall_parentBlock_subset _ _ m _ tN Rc (hCenL _ d) (by omega) a1)
        (fun i c => hEnear _ (hTF F' i) (u + d) (by omega) (by omega) c)
        (fun i y hy => by
          obtain ⟨a1, a2⟩ := hsiteLow F' d hd i y hy
          exact site_mem_supBall_of_thickening hodd _ m _ Rr (hRr2 _ a2) a1) hg
      filter_upwards [h] with v hv
      exact hv.trans (add_le_add le_rfl (hHb _ (by omega) (by omega)))
    have starSH : ∀ (F' : LimitLawAtPoint S) (d : ℕ), d < M → ∀ jX : F'.Index, F'.observables jX = upperSiteObs u M z d →
        ∀ᵐ v ∂F'.law, F'.condMeanAt jX v ≤ Nz * ε + ε := by
      intro F' d hd jX hg
      have hc : ∀ i, ((upperSites u M z d (F'.points i)).card : ℝ) ≤ Nz := by
        intro i
        have hr : ((F'.points i).tower.stage (u + M + d)).toStepSetup.range ≤ rb := by
          rw [hTF F' i]
          exact hrS _ (by omega) (by omega)
        unfold upperSites
        rw [hmP _ (hβ F' i), hNz]
        have h1 := card_thickening_sitesInBlocks_le Λ.stepParams.side ((F'.points i).tower.stage (u + M + d)).toStepSetup.range m
          (upperCentre u M z d (F'.points i))
        have h2 : ((thickening (4 * ((F'.points i).tower.stage (u + M + d)).toStepSetup.range)
            (sitesInBlocks Λ.stepParams.side (supBall (upperCentre u M z d (F'.points i)) (m : ℝ)))).card : ℝ) ≤
            (((2 * m + 1) ^ 4 * (2 * Λ.stepParams.side + 1) ^ 4 *
              (8 * ((F'.points i).tower.stage (u + M + d)).toStepSetup.range + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast h1
        exact h2.trans (hNb _ hr)
      have h := A2 S F' (u + M + d) Rc Rr (upperSites u M z d) (m : ℝ) Nz ε
        (fun i => blockCentreSite Λ.stepParams.side (upperCentre u M z d (F'.points i))) jX (by omega) (Nat.cast_nonneg _) hε0 hNz0
        (hx' _ (by omega) (by omega)) hc
        (fun i y hy => by
          obtain ⟨a1, a2⟩ := hsiteHigh F' d hd i y hy
          exact supBall_parentBlock_subset _ _ m _ tN Rc (hCenH _ d) (by omega) a1)
        (fun i c => hEnear _ (hTF F' i) (u + M + d) (by omega) (by omega) c)
        (fun i y hy => by
          obtain ⟨a1, a2⟩ := hsiteHigh F' d hd i y hy
          exact site_mem_supBall_of_thickening hodd _ m _ Rr (hRr2 _ a2) a1) hg
      filter_upwards [h] with v hv
      exact hv.trans (add_le_add le_rfl (hHb _ (by omega) (by omega)))
    have under : ∀ P : MomentPoint Λ, P.β = S.β → P.data.windowLevel = S.data.windowLevel → P.tower = S.tower →
        ∀ᵐ w ∂(P.law P.data.windowLevel (P.data.period Λ.stepParams.side)),
        clearCurvaturePower u z μ ν q P w ≤ 16 ^ (2 * q) * ∑ d ∈ Finset.range M, transportPowerObs u z μ ν q d P w +
          (2 * (|C₁| * x ^ (-(1 / 2 : ℝ)))) ^ (2 * q) +
          4 ^ q * (((x ^ (-(1 / 3 : ℝ))) ^ (2 * (3 * (q + 4))))⁻¹ * ∑ i ∈ Finset.range M, lowerMaxObs u z (3 * (q + 4)) i P w +
            ((x ^ (-(1 / 3 : ℝ))) ^ (2 * (3 * (q + 4))))⁻¹ * ∑ i ∈ Finset.range M, upperMaxObs u M z (3 * (q + 4)) i P w +
            ∑ i ∈ Finset.range M, lowerSiteObs u z i P w + ∑ i ∈ Finset.range M, upperSiteObs u M z i P w +
            ∑ z' ∈ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(Rc : ℤ)) (Rc : ℤ)), largeHullIndicator (u + M + M) z' 0 P w) := by
      intro P hβP hKP hTP
      have hMP' := hMP P hβP
      have hxcP : flowCouplings Λ.stepParams P.β u = x := by
        rw [← hxP P hβP]
        rfl
      have hKK : u + localChainDepth Λ.stepParams P.β u + localChainDepth Λ.stepParams P.β u ≤ P.data.windowLevel := by
        rw [hMP']
        omega
      have hOn₁ : IsLocalChainAbove Λ.table Λ.floor P.tower P.β u
          (P.sideAtLevel (u + localChainDepth Λ.stepParams P.β u + localChainDepth Λ.stepParams P.β u)) 1 xR1 :=
        onP P hβP hKP _ xR1 hxR1 (by rw [hMP'])
      have hOn₂ : IsLocalChainAbove Λ.table Λ.floor P.tower P.β u
          (P.sideAtLevel (u + localChainDepth Λ.stepParams P.β u + localChainDepth Λ.stepParams P.β u)) 1 xR2 :=
        onP P hβP hKP _ xR2 hxR2 (by rw [hMP'])
      have hLN := (isBlockTorusSide_sideAtLevel P hfit (u + localChainDepth Λ.stepParams P.β u + localChainDepth Λ.stepParams P.β u)).1
      have H1 := HR1 P.tower P.β u _ (lowerSite P u z (localChainDepth Λ.stepParams P.β u)
        (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams P.β u)
          (P.sideAtLevel (u + localChainDepth Λ.stepParams P.β u + localChainDepth Λ.stepParams P.β u)))) hOn₁ hLN
      have H2 := HR2 P.tower P.β u _ 1 (lowerSite P u z (localChainDepth Λ.stepParams P.β u)
        (fineSide Λ.stepParams.side (localChainDepth Λ.stepParams P.β u)
          (P.sideAtLevel (u + localChainDepth Λ.stepParams P.β u + localChainDepth Λ.stepParams P.β u)))) hOn₂ hLN
      have key := clearCurvaturePower_ae_le P u z μ ν hμν q (3 * (q + 4)) hq (by omega) hKK |C₁| (abs_nonneg _) Rc hσ
        (by rw [hxcP]; exact hx1)
        (H1.mono fun w hw a b c d e => (hw a b c d e).trans (add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by rw [hxcP]; exact hx0.le) _))))
        H2 (fun d _ => hrowP P d)
        (fun d _ => by
          rw [hmP P hβP]
          exact (hZlow P hβP d).trans (chartBondsInBlocks_mono _ hm8))
        (by
          rw [hmP P hβP]
          refine supBall_subset_supBall _ _ m tN Rc ?_ hcb
          exact supDist_siteAbove_originSite_le P hodd hL2 (u + localChainDepth Λ.stepParams P.β u) tN ht3 _ _ _
            (upperSite_near P hodd hL2 u _ z tN ht3 hz' _ _))
        (hPF P)
      rw [hMP', hxcP] at key
      exact key
    have hkF := ((hP S).2.2.2 F.rule F.exponents F.points F.period F.rule_admissible F.one_le_period F.strictMono_exponents
      F.points_eq).1
    have hdraw : ∀ i, Measurable ((F.points i).sampleOf F.rule) ∧
        (F.points i).sampleLaw.map ((F.points i).sampleOf F.rule) =
          (F.points i).law (F.points i).data.windowLevel ((F.points i).data.period Λ.stepParams.side) := fun i => by
      have hr : F.rule.IsAdmissible (F.points i).tower := by
        rw [hTF F i]
        exact F.rule_admissible
      obtain ⟨d1, d2⟩ := dvd_period_and_le (F.points i) hfit
      exact hAR Λ.stepParams hfit (F.points i).tower F.rule (F.points i).β (F.points i).isCutoff (F.points i).marksMeasurable hr
        (F.points i).data.windowLevel _ d1 d2
    have hae : ∀ i (Q : MarkedSample Λ.stepParams (F.points i).data.windowLevel ((F.points i).data.period Λ.stepParams.side) → Prop),
        (∀ᵐ w ∂((F.points i).law (F.points i).data.windowLevel ((F.points i).data.period Λ.stepParams.side)), Q w) →
          ∀ᵐ ω ∂(F.points i).sampleLaw, Q ((F.points i).sampleOf F.rule ω) := by
      intro i Q hQ
      rw [← (hdraw i).2] at hQ
      exact ae_of_ae_map (hdraw i).1.aemeasurable hQ
    have hfam : ∀ {g : SampleObservable Λ} {C : ℝ}, (∀ i, Measurable (g (F.points i))) → (∀ i w, |g (F.points i) w| ≤ C) →
        TranslatedLaws.HasBoundedMoments (sampleFamily F.rule F.points F.period g) := by
      intro g C h1 h2
      exact hasBoundedMoments_of_abs_le hkF.isProbability (fun i => ((h1 i).comp (hdraw i).1).aemeasurable)
        (fun i => ae_of_all _ fun ω => h2 i _)
    have hKM : ∀ i, u + M + M ≤ (F.points i).data.windowLevel := fun i => by
      rw [hKF F i]
      omega
    have hKl : ∀ d, d < M → ∀ i, u + d + 1 ≤ (F.points i).data.windowLevel := fun d hd i => by
      have := hKM i
      omega
    have hKh : ∀ d, d < M → ∀ i, u + M + d + 1 ≤ (F.points i).data.windowLevel := fun d hd i => by
      have := hKM i
      omega
    have hOnB : ∀ (i a : ℕ), a ≤ u + M + M →
        IsLocalChainAbove Λ.table Λ.floor (F.points i).tower (F.points i).β u ((F.points i).sideAtLevel a) 1 xB := fun i a ha =>
      onP _ (hβ F i) (hKF F i) a xB hxB ha
    have hltP : ∀ (i d : ℕ), d < M → u + d < u + 2 * localChainDepth Λ.stepParams (F.points i).β u := fun i d hd => by
      rw [hMP _ (hβ F i)]
      omega
    have hltQ : ∀ (i d : ℕ), d < M → u + M + d < u + 2 * localChainDepth Λ.stepParams (F.points i).β u := fun i d hd => by
      rw [hMP _ (hβ F i)]
      omega
    let g' : ((Fin 5 × Fin M) ⊕ (Fin 4 → ℤ)) → SampleObservable Λ := Sum.elim
      (fun p => ![transportPowerObs u z μ ν q p.2, lowerMaxObs u z (3 * (q + 4)) p.2, upperMaxObs u M z (3 * (q + 4)) p.2,
        lowerSiteObs u z p.2, upperSiteObs u M z p.2] p.1)
      (fun z' => largeHullIndicator (u + M + M) z' 0)
    have hm : ∀ e, TranslatedLaws.HasBoundedMoments (sampleFamily F.rule F.points F.period (g' e)) := by
      rintro (⟨k, ⟨d, hd⟩⟩ | z')
      · fin_cases k
        · refine hfam (g := transportPowerObs u z μ ν q d) (C := 4) (fun i => ?_) (fun i w => ?_)
          · exact measurable_truncatedDeviationCases (F.points i) (hPF _) u (u + d) q (hKl d hd i) _ _ _ fun b hb =>
              boJ _ u (u + d) _ b (Nat.le_add_right _ _) (hltP i d hd) (hOnB i _ (by omega)) (by
                rw [hmP _ (hβ F i)]
                exact hZlow _ (hβ F i) d hb)
          · refine abs_truncatedDeviationCases_le (F.points i) u (u + d) q _ _ _ 4 (by norm_num) (fun b => abs_nonneg _)
              ((hrowP _ d).trans ?_) w
            have : ((1 : ℝ) / 2) ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
            linarith
        · refine hfam (g := lowerMaxObs u z (3 * (q + 4)) d) (C := x) (fun i => ?_) (fun i w => ?_)
          · exact measurable_truncatedDeviationCases (F.points i) (hPF _) u (u + d) _ (hKl d hd i) _ _ _ fun b hb =>
              boJ _ u (u + d) _ b (Nat.le_add_right _ _) (hltP i d hd) (hOnB i _ (by omega)) (by
                rw [hmP _ (hβ F i)]
                exact hZql _ (hβ F i) d hb)
          · exact abs_truncatedDeviationCases_le (F.points i) u (u + d) _ _ _ _ x hx0.le (fun b => zero_le_one)
              (hsumQL _ (hβ F i) d) w
        · refine hfam (g := upperMaxObs u M z (3 * (q + 4)) d) (C := x) (fun i => ?_) (fun i w => ?_)
          · exact measurable_truncatedDeviationCases (F.points i) (hPF _) u (u + M + d) _ (hKh d hd i) _ _ _ fun b hb =>
              boJ _ u (u + M + d) _ b (by omega) (hltQ i d hd) (hOnB i _ (by omega)) (by
                rw [hmP _ (hβ F i)]
                exact hZqh _ (hβ F i) d hb)
          · exact abs_truncatedDeviationCases_le (F.points i) u (u + M + d) _ _ _ _ x hx0.le (fun b => zero_le_one)
              (hsumQH _ (hβ F i) d) w
        · exact hfam (g := lowerSiteObs u z d) (C := 1)
            (fun i => measurable_badOrSupportSiteCase (F.points i) (hPF _) (u + d) (hKl d hd i) _)
            (fun i w => abs_badOrSupportSiteCase_le _ _ _ w)
        · exact hfam (g := upperSiteObs u M z d) (C := 1)
            (fun i => measurable_badOrSupportSiteCase (F.points i) (hPF _) (u + M + d) (hKh d hd i) _)
            (fun i w => abs_badOrSupportSiteCase_le _ _ _ w)
      · exact hfam (g := largeHullIndicator (u + M + M) z' 0) (C := 1)
          (fun i => measurable_largeHullIndicator (F.points i) (hPF _) _ (hKM i) z')
          (fun i w => abs_largeHullIndicator_le _ _ _ w)
    have final : ∀ (G : LimitLawAtPoint S) (jG : G.Index) (ι : ((Fin 5 × Fin M) ⊕ (Fin 4 → ℤ)) → G.Index),
        (∀ e, G.observables (ι e) = g' e) →
        G.observables jG = clearCurvaturePower u z μ ν q → (translatedTori G.points G.period).IsPreserving →
        (∀ n (Q : MarkedSample Λ.stepParams (G.points n).data.windowLevel ((G.points n).data.period Λ.stepParams.side) → Prop),
          (∀ᵐ w ∂((G.points n).law (G.points n).data.windowLevel ((G.points n).data.period Λ.stepParams.side)), Q w) →
            ∀ᵐ ω ∂(G.points n).sampleLaw, Q ((G.points n).sampleOf G.rule ω)) →
        ∀ᵐ v ∂G.law, 0 ≤ G.condMeanAt jG v ∧ G.condMeanAt jG v ≤ ((2 * |C₁|) ^ (2 * q) + 16 ^ (2 * q) * (8 * (Cp ^ (2 * q) + 2)) +
          4 ^ q * (2 * (Cq ^ (2 * (3 * (q + 4))) + 2) + 2 + 1)) * (x ^ q)⁻¹ := by
      intro G jG ι hι hjG hkG haeG
      haveI hPr : IsProbabilityMeasure G.law := G.isJointLimitLaw.isProbability
      obtain ⟨cc, hcc⟩ : ∃ cc : ℝ, cc = ((x ^ (-(1 / 3 : ℝ))) ^ (2 * (3 * (q + 4))))⁻¹ := ⟨_, rfl⟩
      have hcc0 : 0 ≤ cc := by
        rw [hcc]
        have := Real.rpow_nonneg hx0.le (-(1 / 3 : ℝ))
        positivity
      obtain ⟨ν₁, hν₁⟩ : ∃ ν₁ : ℝ, ν₁ = (Cp * x ^ (-(1 / 2 : ℝ))) ^ (2 * q) + 2 * ε := ⟨_, rfl⟩
      obtain ⟨ν₂, hν₂⟩ : ∃ ν₂ : ℝ, ν₂ = (Cq * x ^ (-(1 / 2 : ℝ))) ^ (2 * (3 * (q + 4))) + 2 * ε := ⟨_, rfl⟩
      obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ, a₀ = (2 * (|C₁| * x ^ (-(1 / 2 : ℝ)))) ^ (2 * q) := ⟨_, rfl⟩
      let I : Finset ((Fin 5 × Fin M) ⊕ (Fin 4 → ℤ)) := (Finset.univ : Finset (Fin 5 × Fin M)).disjSum
        (Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(Rc : ℤ)) (Rc : ℤ)))
      let cf : ((Fin 5 × Fin M) ⊕ (Fin 4 → ℤ)) → ℝ :=
        Sum.elim (fun p => ![16 ^ (2 * q), 4 ^ q * cc, 4 ^ q * cc, 4 ^ q, 4 ^ q] p.1) (fun _ => 4 ^ q)
      let bf : ((Fin 5 × Fin M) ⊕ (Fin 4 → ℤ)) → ℝ := Sum.elim
        (fun p => ![(4 * (1 / 2) ^ (p.2 : ℕ)) * ν₁, x * ν₂, x * ν₂, Nz * ε + ε, Nz * ε + ε] p.1)
        (fun _ => Real.exp (-(hullDecayRate Λ.table * S.coupling (u + M + M))))
      have hsumI : ∀ f : ((Fin 5 × Fin M) ⊕ (Fin 4 → ℤ)) → ℝ, ∑ e ∈ I, cf e * f e =
          16 ^ (2 * q) * ∑ i : Fin M, f (.inl (0, i)) + 4 ^ q * cc * ∑ i : Fin M, f (.inl (1, i)) +
            4 ^ q * cc * ∑ i : Fin M, f (.inl (2, i)) +
            4 ^ q * ∑ i : Fin M, f (.inl (3, i)) + 4 ^ q * ∑ i : Fin M, f (.inl (4, i)) +
            4 ^ q * ∑ z' ∈ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(Rc : ℤ)) (Rc : ℤ)), f (.inr z') := by
        intro f
        rw [Finset.sum_disjSum, Fintype.sum_prod_type, Fin.sum_univ_five]
        simp only [cf, Sum.elim_inl, Sum.elim_inr, Finset.mul_sum]
        rfl
      have hcf : ∀ e ∈ I, 0 ≤ cf e := by
        rintro (⟨k, d⟩ | z') _
        · fin_cases k <;> simp [cf] <;> positivity
        · simp only [cf, Sum.elim_inr]
          positivity
      have hgj : ∀ n w, G.observables jG (G.points n) w = clearCurvaturePower u z μ ν q (G.points n) w := fun n w => by
        rw [hjG]
      have hle : ∀ᵐ v ∂G.law, v (jG, 0) ≤ a₀ + ∑ e ∈ I, cf e * v (ι e, 0) := by
        have h := ae_le_zero_of_eventually G.isJointLimitLaw (I := Unit ⊕ {e // e ∈ I}) (Sum.elim (fun _ => jG) (fun e => ι e.1))
          (fun y => y (.inl ()) - (a₀ + ∑ e : {e // e ∈ I}, cf e.1 * y (.inr e))) (by fun_prop)
          (Eventually.of_forall fun n => ?_)
        · filter_upwards [h] with v hv
          have hv' : v (jG, 0) - (a₀ + ∑ e : {e // e ∈ I}, cf e.1 * v (ι e.1, 0)) ≤ 0 := hv
          have e3 := Finset.sum_coe_sort I fun e => cf e * v (ι e, 0)
          rw [e3] at hv'
          linarith
        · have h0 := under (G.points n) (hβ G n) (hKF G n) (hTF G n)
          have h1 := haeG n _ h0
          filter_upwards [h1] with ω hω
          show G.observables jG (G.points n) ((G.points n).sampleOf G.rule ω) -
            (a₀ + ∑ e : {e // e ∈ I}, cf e.1 * G.observables (ι e.1) (G.points n) ((G.points n).sampleOf G.rule ω)) ≤ 0
          have e3 := Finset.sum_coe_sort I fun e => cf e * G.observables (ι e) (G.points n) ((G.points n).sampleOf G.rule ω)
          rw [e3, hsumI (fun e => G.observables (ι e) (G.points n) ((G.points n).sampleOf G.rule ω)), hgj]
          have f1 : ∑ i : Fin M, G.observables (ι (.inl (0, i))) (G.points n) ((G.points n).sampleOf G.rule ω) =
              ∑ d ∈ Finset.range M, transportPowerObs u z μ ν q d (G.points n) ((G.points n).sampleOf G.rule ω) := by
            rw [Finset.sum_range]
            exact Finset.sum_congr rfl fun i _ => congrFun (congrFun (hι (.inl (0, i))) _) _
          have f2 : ∑ i : Fin M, G.observables (ι (.inl (1, i))) (G.points n) ((G.points n).sampleOf G.rule ω) =
              ∑ d ∈ Finset.range M, lowerMaxObs u z (3 * (q + 4)) d (G.points n) ((G.points n).sampleOf G.rule ω) := by
            rw [Finset.sum_range]
            exact Finset.sum_congr rfl fun i _ => congrFun (congrFun (hι (.inl (1, i))) _) _
          have f3 : ∑ i : Fin M, G.observables (ι (.inl (2, i))) (G.points n) ((G.points n).sampleOf G.rule ω) =
              ∑ d ∈ Finset.range M, upperMaxObs u M z (3 * (q + 4)) d (G.points n) ((G.points n).sampleOf G.rule ω) := by
            rw [Finset.sum_range]
            exact Finset.sum_congr rfl fun i _ => congrFun (congrFun (hι (.inl (2, i))) _) _
          have f4 : ∑ i : Fin M, G.observables (ι (.inl (3, i))) (G.points n) ((G.points n).sampleOf G.rule ω) =
              ∑ d ∈ Finset.range M, lowerSiteObs u z d (G.points n) ((G.points n).sampleOf G.rule ω) := by
            rw [Finset.sum_range]
            exact Finset.sum_congr rfl fun i _ => congrFun (congrFun (hι (.inl (3, i))) _) _
          have f5 : ∑ i : Fin M, G.observables (ι (.inl (4, i))) (G.points n) ((G.points n).sampleOf G.rule ω) =
              ∑ d ∈ Finset.range M, upperSiteObs u M z d (G.points n) ((G.points n).sampleOf G.rule ω) := by
            rw [Finset.sum_range]
            exact Finset.sum_congr rfl fun i _ => congrFun (congrFun (hι (.inl (4, i))) _) _
          have f6 : ∑ z' ∈ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(Rc : ℤ)) (Rc : ℤ)),
                G.observables (ι (.inr z')) (G.points n) ((G.points n).sampleOf G.rule ω) =
              ∑ z' ∈ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(Rc : ℤ)) (Rc : ℤ)),
                largeHullIndicator (u + M + M) z' 0 (G.points n) ((G.points n).sampleOf G.rule ω) :=
            Finset.sum_congr rfl fun z' _ => congrFun (congrFun (hι (.inr z')) _) _
          rw [f1, f2, f3, f4, f5, f6, ha₀, hcc]
          beta_reduce at hω
          refine sub_nonpos.mpr (le_trans hω (le_of_eq ?_))
          ring
      have hb : ∀ e ∈ I, ∀ᵐ v ∂G.law, invariantCondExp G.law (fun v => v (ι e, 0)) v ≤ bf e := by
        rintro (⟨k, ⟨d, hd⟩⟩ | z') _
        · fin_cases k
          · have h := starP G d hd (ι (.inl (0, ⟨d, hd⟩))) (hι _)
            rw [← hν₁] at h
            exact h
          · have h := starQL G d hd (ι (.inl (1, ⟨d, hd⟩))) (hι _)
            rw [← hν₂] at h
            exact h
          · have h := starQH G d hd (ι (.inl (2, ⟨d, hd⟩))) (hι _)
            rw [← hν₂] at h
            exact h
          · exact starSL G d hd (ι (.inl (3, ⟨d, hd⟩))) (hι _)
          · exact starSH G d hd (ι (.inl (4, ⟨d, hd⟩))) (hι _)
        · have h := (hHl S G (u + M + M) z' (by omega)).1 0 (ι (.inr z')) le_rfl (hι _)
          filter_upwards [h] with v hv
          exact show G.condMeanAt (ι (.inr z')) v ≤ Real.exp (-(hullDecayRate Λ.table * S.coupling (u + M + M))) from by simpa using hv
      have hS := ae_invariantCondExp_le_linear I cf hcf (fun e v => v (ι e, 0)) (fun e _ => integrable_eval_zero hMn hkG (ι e)) bf hb a₀
        (integrable_eval_zero hMn hkG jG) hle
      have hnn : ∀ᵐ v ∂G.law, 0 ≤ v (jG, 0) := by
        have h := ae_le_zero_of_eventually G.isJointLimitLaw (I := Unit) (fun _ => jG) (fun y => -y ()) (by fun_prop)
          (Eventually.of_forall fun n => ae_of_all _ fun ω => by
            show -G.observables jG (G.points n) ((G.points n).sampleOf G.rule ω) ≤ 0
            rw [hgj]
            have h0 : 0 ≤ clearCurvaturePower u z μ ν q (G.points n) ((G.points n).sampleOf G.rule ω) := by
              unfold clearCurvaturePower
              split_ifs
              · exact pow_nonneg (curvature_nonneg _ _ _ _) _
              · exact le_rfl
              · exact le_rfl
            linarith)
        filter_upwards [h] with v hv
        have hv' : -v (jG, 0) ≤ 0 := hv
        linarith
      have hlow : 0 ≤ᵐ[G.law] G.law[fun v : TranslateValues G.Index => v (jG, 0) | shiftInvariantSigma G.Index] := condExp_nonneg hnn
      have hsb := hsumI bf
      have e1 : (Cp * x ^ (-(1 / 2 : ℝ))) ^ (2 * q) = Cp ^ (2 * q) * (x ^ q)⁻¹ := by rw [mul_pow, rpow_neg_half_pow hx0]
      have e2 : (Cq * x ^ (-(1 / 2 : ℝ))) ^ (2 * (3 * (q + 4))) = Cq ^ (2 * (3 * (q + 4))) * (x ^ (3 * (q + 4)))⁻¹ := by
        rw [mul_pow, rpow_neg_half_pow hx0]
      have e3 : cc = x ^ (2 * (q + 4)) := by rw [hcc]; exact inv_rpow_neg_third_pow hx0 (q + 4)
      have e4 : a₀ = (2 * |C₁|) ^ (2 * q) * (x ^ q)⁻¹ := by
        rw [ha₀, ← mul_assoc, mul_pow, rpow_neg_half_pow hx0]
      obtain ⟨Ap, hAp⟩ : ∃ Ap : ℝ, Ap = ∑ i : Fin M, 4 * (1 / 2 : ℝ) ^ (i : ℕ) := ⟨_, rfl⟩
      have hAp0 : 0 ≤ Ap := by
        rw [hAp]
        exact Finset.sum_nonneg fun _ _ => by positivity
      have hAp8 : Ap ≤ 8 := by
        rw [hAp, ← Finset.sum_range (fun i => 4 * (1 / 2 : ℝ) ^ i)]
        have h1 : ∀ D : ℕ, ∑ i ∈ Finset.range D, 4 * (1 / 2 : ℝ) ^ i = 8 - 8 * (1 / 2) ^ D := by
          intro D
          induction D with
          | zero => simp
          | succ D ih =>
            rw [Finset.sum_range_succ, ih, pow_succ]
            ring
        rw [h1]
        have : (0 : ℝ) ≤ (1 / 2) ^ M := by positivity
        linarith
      have hNz1 : Nz + 1 ≤ x ^ 10 := by
        have h1 : (1 : ℝ) ≤ x ^ 8 := one_le_pow₀ hx1
        have h2 := mul_le_mul_of_nonneg_right n3 (by positivity : 0 ≤ x ^ 8)
        have e5 : x ^ 2 * x ^ 8 = x ^ 10 := by ring
        rw [e5] at h2
        rw [hNz]
        nlinarith
      have hsb2 := bound_sum_le hx1 q Ap (Cp ^ (2 * q)) (Cq ^ (2 * (3 * (q + 4)))) ((2 * |C₁|) ^ (2 * q)) Nz ε x cc M hMx hAp0 hAp8
        (by positivity) (by positivity) (by positivity) hNz1 hNz0 hε rfl e3
      have t1 : ∑ i : Fin M, bf (.inl (0, i)) = Ap * (Cp ^ (2 * q) * (x ^ q)⁻¹ + 2 * ε) := by
        rw [hAp, Finset.sum_mul, ← e1, ← hν₁]
        rfl
      have t2 : ∑ i : Fin M, bf (.inl (1, i)) = M * (x * (Cq ^ (2 * (3 * (q + 4))) * (x ^ (3 * (q + 4)))⁻¹ + 2 * ε)) := by
        rw [← e2, ← hν₂]
        have : ∀ i : Fin M, bf (.inl (1, i)) = x * ν₂ := fun _ => rfl
        simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have t3 : ∑ i : Fin M, bf (.inl (2, i)) = M * (x * (Cq ^ (2 * (3 * (q + 4))) * (x ^ (3 * (q + 4)))⁻¹ + 2 * ε)) := by
        rw [← e2, ← hν₂]
        have : ∀ i : Fin M, bf (.inl (2, i)) = x * ν₂ := fun _ => rfl
        simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have t4 : ∑ i : Fin M, bf (.inl (3, i)) = M * (Nz * ε + ε) := by
        have : ∀ i : Fin M, bf (.inl (3, i)) = Nz * ε + ε := fun _ => rfl
        simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have t5 : ∑ i : Fin M, bf (.inl (4, i)) = M * (Nz * ε + ε) := by
        have : ∀ i : Fin M, bf (.inl (4, i)) = Nz * ε + ε := fun _ => rfl
        simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have t6 : ∑ z' ∈ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(Rc : ℤ)) (Rc : ℤ)), bf (.inr z') ≤ ε := by
        have : ∀ z' : Fin 4 → ℤ, bf (.inr z') = Real.exp (-(hullDecayRate Λ.table * S.coupling (u + M + M))) := fun _ => rfl
        simp only [this, Finset.sum_const, nsmul_eq_mul]
        have hc : ((Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(Rc : ℤ)) (Rc : ℤ))).card : ℝ) = (2 * (Rc : ℝ) + 1) ^ 4 := by
          rw [Fintype.card_piFinset]
          simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          have e3' : ((Rc : ℤ) + 1 - -(Rc : ℤ)).toNat = 2 * Rc + 1 := by omega
          rw [e3']
          push_cast
          ring
        rw [hc]
        exact hHb _ (by omega) (by omega)
      rw [t1, t2, t3, t4, t5] at hsb
      have h4q : (0 : ℝ) ≤ 4 ^ q := by positivity
      have t7 := mul_le_mul_of_nonneg_left t6 h4q
      filter_upwards [hS, hlow] with v hv hv0
      refine ⟨hv0, ?_⟩
      have hv' : G.condMeanAt jG v ≤ a₀ + ∑ e ∈ I, cf e * bf e := hv
      refine hv'.trans ?_
      rw [hsb, e4]
      linarith only [hsb2, t7]
    obtain ⟨sub, P', hsub, hlim, -, htr⟩ := hExt (translatedTori F.points F.period) F.Index ((Fin 5 × Fin M) ⊕ (Fin 4 → ℤ))
      (fun j => sampleFamily F.rule F.points F.period (F.observables j)) (fun e => sampleFamily F.rule F.points F.period (g' e)) F.law
      hkF F.hasBoundedMoments hm F.isJointLimitLaw
    have hfin := final (LimitLawAtPoint.extend F g' hm sub hsub P' hlim) (Sum.inl j) Sum.inr (fun _ => rfl) hj
      ⟨fun i => hkF.isProbability (sub i), fun i => hkF.measurePreserving (sub i)⟩ (fun n Q hQ => hae (sub n) Q hQ)
    have hY : Integrable (evalAtZero j) F.law := integrable_eval_zero hMn hkF j
    have h2 := htr (evalAtZero j) 0 _ hY hfin
    filter_upwards [h2] with v hv
    exact hv.2
  choose Aq Xq hA hcore using core
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, X₀ = max (max Xw Xr) Λ.floor := ⟨_, rfl⟩
  obtain ⟨Xb, hXb⟩ : ∃ Xb : ℕ → ℝ, Xb = fun q => max X₀ (max 1 (2 * Xq q)) := ⟨_, rfl⟩
  refine ⟨fun q => max (Aq q * 2 ^ q) (4 ^ q * Xb q ^ q), X₀, ?_, ?_⟩
  · rw [hX₀]
    exact le_max_right _ _
  intro S F t hS ht u hu1 hu2 z μ ν hμν hz q j hq hj
  classical
  haveI := F.countable_index
  have hXw : Xw ≤ S.scaleCoupling := by
    have : Xw ≤ X₀ := by rw [hX₀]; exact (le_max_left _ _).trans (le_max_left _ _)
    exact this.trans hS
  have hXrx : Xr ≤ S.scaleCoupling := by
    have : Xr ≤ X₀ := by rw [hX₀]; exact (le_max_right _ _).trans (le_max_left _ _)
    exact this.trans hS
  obtain ⟨hx2, hlogb, hroomx⟩ := hXr S.scaleCoupling hXrx
  have hx0 : 0 < S.scaleCoupling := by linarith
  have hq0 : ∀ z : ℝ, 0 < z → z ^ (-(q : ℝ)) = (z ^ q)⁻¹ := fun z hz => by
    rw [Real.rpow_neg hz.le, Real.rpow_natCast]
  by_cases hbig : Xb q ≤ S.scaleCoupling
  · have hxq : 2 * Xq q ≤ S.scaleCoupling := by
      have : 2 * Xq q ≤ Xb q := by
        rw [hXb]
        exact (le_max_right _ _).trans (le_max_right _ _)
      exact this.trans hbig
    have hXq1 : 1 ≤ S.scaleCoupling := by
      have : 1 ≤ Xb q := by
        rw [hXb]
        exact (le_max_left _ _).trans (le_max_right _ _)
      exact this.trans hbig
    obtain ⟨a0, b0, e0⟩ := F.points_eq 0
    have p1 : (F.points 0).scaleCoupling = S.scaleCoupling := by rw [e0]; rfl
    have p2 : (F.points 0).logIndex = S.logIndex := by rw [e0]; rfl
    have p3 : ∀ v, (F.points 0).coupling v = S.coupling v := fun v => by rw [e0]; rfl
    have p4 : (F.points 0).data.windowLevel = S.data.windowLevel := by rw [e0]; rfl
    have p5 : (F.points 0).data.scaleLevel = S.data.scaleLevel := by rw [e0]; rfl
    obtain ⟨-, -, -, hKs, -, htK, hcl⟩ := hW (F.points 0) (by rw [p1]; exact hXw)
    rw [p1, p4, p5] at hKs
    have ht0 := ht 0
    rw [ht0, p2, p4] at htK
    have hts : t ≤ S.data.scaleLevel := by
      rw [← ht0, ← p5]
      classical
      unfold MomentPoint.lastSeparated
      exact Nat.findGreatest_le _
    have hu3 : u ≤ (F.points 0).lastSeparated + 2 * (F.points 0).logIndex + 3 := by
      rw [ht0, p2]
      omega
    obtain ⟨habs, -⟩ := hcl u (by rw [ht0]; exact hu1) hu3
    rw [p3, p1] at habs
    have hxu := abs_le.mp habs
    have hxu1 : S.scaleCoupling / 2 ≤ S.coupling u := by linarith [hxu.1]
    have hxu2 : S.coupling u ≤ 2 * S.scaleCoupling := by linarith [hxu.2]
    have hxu0 : 1 ≤ S.coupling u := by linarith
    obtain ⟨M, hMdef⟩ : ∃ M, M = localChainDepth Λ.stepParams S.β u := ⟨_, rfl⟩
    have hMr : (M : ℝ) ≤ Real.log (2 * S.scaleCoupling) ^ 2 := by
      rw [hMdef]
      exact (Nat.floor_le (sq_nonneg _)).trans
        (pow_le_pow_left₀ (Real.log_nonneg hxu0) (Real.log_le_log (by linarith) hxu2) 2)
    have hlog0 : 0 ≤ Real.log S.scaleCoupling := Real.log_nonneg (by linarith)
    have hN₀ : (S.logIndex : ℝ) ≤ 4 * Real.log S.scaleCoupling + 1 :=
      (Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * Real.log S.scaleCoupling)).le
    obtain ⟨Wd, hWd⟩ : ∃ Wd : ℝ, Wd = 2 ^ 10 * (2 * S.scaleCoupling) ^ ((1 : ℝ) / 20) := ⟨_, rfl⟩
    rw [← hWd] at hroomx
    have hreal : (u : ℝ) + 2 * M + Wd + 1 ≤ S.data.windowLevel := by
      have a1 : (u : ℝ) ≤ S.data.scaleLevel + S.logIndex + 2 := by
        exact_mod_cast (by omega : u ≤ S.data.scaleLevel + S.logIndex + 2)
      linarith
    have hWd0 : 0 ≤ Wd := by
      rw [hWd]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _)
    have hK : u + 2 * M + 1 ≤ S.data.windowLevel := by
      have : ((u + 2 * M + 1 : ℕ) : ℝ) ≤ S.data.windowLevel := by
        push_cast
        linarith
      exact_mod_cast this
    obtain ⟨E, hE⟩ : ∃ E, S.data.windowLevel = u + 2 * M + (E + 1) := ⟨S.data.windowLevel - (u + 2 * M) - 1, by omega⟩
    have hEr : Wd ≤ (E : ℝ) + 1 := by
      have : (S.data.windowLevel : ℝ) = u + 2 * M + (E + 1) := by exact_mod_cast hE
      linarith
    have r1 : localBoxRadius (S.coupling u) ≤ (2 * S.scaleCoupling) ^ ((1 : ℝ) / 20) := by
      have : localBoxRadius (S.coupling u) ≤ S.coupling u ^ ((1 : ℝ) / 20) := Nat.floor_le (Real.rpow_nonneg (by linarith) _)
      exact this.trans (Real.rpow_le_rpow (by linarith) hxu2 (by norm_num))
    have r2 : (2 : ℝ) ^ 10 * localBoxRadius (S.coupling u) ≤ Wd := by
      rw [hWd]
      exact mul_le_mul_of_nonneg_left r1 (by positivity)
    subst hMdef
    have hcl2 := hcore q S F u E z μ ν j hq hμν (by linarith) hE (r2.trans hEr) hx0.le (by linarith) hz hj
    filter_upwards [hcl2] with v hv
    refine hv.trans ?_
    show Aq q * (S.coupling u ^ q)⁻¹ ≤ max (Aq q * 2 ^ q) (4 ^ q * Xb q ^ q) * S.scaleCoupling ^ (-(q : ℝ))
    have hxu00 : 0 < S.coupling u := by linarith
    rw [hq0 _ hx0]
    have c1 : (S.coupling u ^ q)⁻¹ ≤ 2 ^ q * (S.scaleCoupling ^ q)⁻¹ := by
      have h1 : (S.scaleCoupling / 2) ^ q ≤ S.coupling u ^ q := pow_le_pow_left₀ (by positivity) hxu1 q
      have h2 := inv_anti₀ (by positivity) h1
      refine h2.trans (le_of_eq ?_)
      rw [div_pow, inv_div, div_eq_mul_inv]
    have c2 : Aq q * 2 ^ q ≤ max (Aq q * 2 ^ q) (4 ^ q * Xb q ^ q) := le_max_left _ _
    have c3 : 0 ≤ (S.scaleCoupling ^ q)⁻¹ := by positivity
    calc Aq q * (S.coupling u ^ q)⁻¹ ≤ Aq q * (2 ^ q * (S.scaleCoupling ^ q)⁻¹) := mul_le_mul_of_nonneg_left c1 (hA q)
      _ = (Aq q * 2 ^ q) * (S.scaleCoupling ^ q)⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right c2 c3
  · have hlt : S.scaleCoupling < Xb q := not_le.mp hbig
    have hkF := ((hP S).2.2.2 F.rule F.exponents F.points F.period F.rule_admissible F.one_le_period F.strictMono_exponents
      F.points_eq).1
    haveI hPr : IsProbabilityMeasure F.law := F.isJointLimitLaw.isProbability
    have B1 : ∀ᵐ v ∂F.law, v (j, 0) ≤ 4 ^ q := by
      have h := ae_le_zero_of_eventually F.isJointLimitLaw (I := Unit) (fun _ => j) (fun y => y () - 4 ^ q) (by fun_prop)
        (Eventually.of_forall fun n => ae_of_all _ fun ω => by
          show F.observables j (F.points n) ((F.points n).sampleOf F.rule ω) - 4 ^ q ≤ 0
          rw [hj]
          have := clearCurvaturePower_le_four_pow (F.points n) u z μ ν q ((F.points n).sampleOf F.rule ω)
          linarith)
      filter_upwards [h] with v hv
      have hv' : v (j, 0) - 4 ^ q ≤ 0 := hv
      linarith
    have c1 := condExp_mono (m := shiftInvariantSigma F.Index) (integrable_eval_zero hMn hkF j) (integrable_const ((4 : ℝ) ^ q)) B1
    have c2 : F.law[fun _ : TranslateValues F.Index => (4 : ℝ) ^ q | shiftInvariantSigma F.Index] = fun _ => 4 ^ q :=
      condExp_const shiftInvariantSigma_le _
    filter_upwards [c1] with v hv
    have hv' : F.condMeanAt j v ≤ (F.law[fun _ : TranslateValues F.Index => (4 : ℝ) ^ q | shiftInvariantSigma F.Index]) v := hv
    rw [c2] at hv'
    refine hv'.trans ?_
    show (4 : ℝ) ^ q ≤ max (Aq q * 2 ^ q) (4 ^ q * Xb q ^ q) * S.scaleCoupling ^ (-(q : ℝ))
    rw [hq0 _ hx0]
    have c3 : (4 : ℝ) ^ q * Xb q ^ q ≤ max (Aq q * 2 ^ q) (4 ^ q * Xb q ^ q) := le_max_right _ _
    have c4 : S.scaleCoupling ^ q ≤ Xb q ^ q := pow_le_pow_left₀ hx0.le hlt.le q
    have c5 : 0 < S.scaleCoupling ^ q := by positivity
    have c6 : 1 ≤ Xb q ^ q * (S.scaleCoupling ^ q)⁻¹ := by
      rw [← div_eq_mul_inv, one_le_div c5]
      exact c4
    have c7 : (0 : ℝ) ≤ 4 ^ q := by positivity
    calc (4 : ℝ) ^ q = 4 ^ q * 1 := (mul_one _).symm
      _ ≤ 4 ^ q * (Xb q ^ q * (S.scaleCoupling ^ q)⁻¹) := mul_le_mul_of_nonneg_left c6 c7
      _ = (4 ^ q * Xb q ^ q) * (S.scaleCoupling ^ q)⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right c3 (by positivity)
end YangMills.Construction.MomentLaw
end
