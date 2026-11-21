import YangMills.Construction.CellOfTheFlow.TheDrawOfTheNoiseIsBorelProof
import YangMills.Construction.ClusterExpansionOfAStep.FactorsAtACaseProof
import YangMills.Construction.HullsInEveryVolume.OneStepDownFromAHullProof
import YangMills.Construction.HullsInEveryVolume.ReachOfAUnit
import YangMills.Construction.LawByMomentsOfTheFlow.HullsInALimitFieldProof
import YangMills.Construction.SixteenPointsOnASmallTorus.LevelsOfARadiusProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped unitInterval
namespace YangMills.Construction.HullTrees
open TorusFields TorusLumps StepSettings StepCosts ChainNoise WeightedResponses LumpContours
namespace UnitIndicatorLocality
section Sets
variable {n : ℕ} [NeZero n]
private theorem mem_box_iff {y z : TorusSite n} {m : ℕ} : z ∈ HullTrees.box y m ↔ _root_.YangMills.Construction.TorusFields.supDist z y ≤ m := by apply _root_.YangMills.SharedProofs.p104074 <;> assumption
private theorem mem_sitesInBlocks_iff {L : ℕ} [NeZero L] {S : Finset (TorusSite n)} {x : TorusSite (n * L)} :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by apply _root_.YangMills.Construction.CongruentBoxes.mem_sitesInBlocks <;> assumption
private theorem thickening_sitesInBlocks_subset {L : ℕ} [NeZero L] (hL : 8 ≤ L) {S Q : Finset (TorusSite n)}
    (h : ∀ a ∈ S, ∀ c, _root_.YangMills.Construction.TorusFields.supDist c a ≤ 1 → c ∈ Q) : thickening 5 (sitesInBlocks L S) ⊆ sitesInBlocks L Q := by
  intro x hx
  obtain ⟨x', hx', hd⟩ := (mem_thickening _ _ _).1 hx
  refine mem_sitesInBlocks_iff.2 (h _ (mem_sitesInBlocks_iff.1 hx') _ ?_)
  have h1 := TorusBalls.supDist_parentBlock_le_div_add_one L x x'
  have h2 : _root_.YangMills.Construction.TorusFields.supDist x x' / L = 0 := Nat.div_eq_of_lt (by omega)
  omega
private theorem sitesUnder_mono (L : ℕ) [NeZero L] : ∀ (u n : ℕ) [NeZero n] {Q Q' : Finset (TorusSite n)}, Q ⊆ Q' →
    sitesUnder L u n Q ⊆ sitesUnder L u n Q' := by apply _root_.YangMills.SharedProofs.p53753 <;> assumption
private theorem noiseAgreeAbove_mono (ℓ : StepParameters) : ∀ (u n : ℕ) [NeZero n] {Q Q' : Finset (TorusSite n)}
    {U U' : ChainNoise ℓ u n}, Q ⊆ Q' → NoiseAgreeAbove ℓ u n Q' U U' → NoiseAgreeAbove ℓ u n Q U U' := by apply _root_.YangMills.SharedProofs.p6852 <;> assumption
private theorem noiseAgreeAbove_symm (ℓ : StepParameters) : ∀ (u n : ℕ) [NeZero n] {Q : Finset (TorusSite n)}
    {U U' : ChainNoise ℓ u n}, NoiseAgreeAbove ℓ u n Q U U' → NoiseAgreeAbove ℓ u n Q U' U := by
  intro u
  induction u with
  | zero =>
    intro n _ Q U U' _
    trivial
  | succ u ih =>
    intro n _ Q U U' hU
    obtain ⟨h0, h1, h2, h3⟩ := hU
    exact ⟨ih (n * ℓ.side) h0, fun y hy => (h1 y hy).symm, fun c hc => (h2 c hc).symm,
      fun b hb => (h3 b hb).symm⟩
private theorem dependsAbove_mono {ℓ : StepParameters} {u n : ℕ} [NeZero n] {Q Q' : Finset (TorusSite n)}
    {Φ : TorusField (fineSide ℓ.side u n) × ChainNoise ℓ u n → ℝ} (h : Q ⊆ Q') (hΦ : DependsAbove ℓ u n Q Φ) :
    DependsAbove ℓ u n Q' Φ := fun W W' U U' hW hU =>
  hΦ W W' U U' (fun b h1 h2 => hW b (sitesUnder_mono ℓ.side u n h h1) (sitesUnder_mono ℓ.side u n h h2))
    (noiseAgreeAbove_mono ℓ u n h hU)
end Sets
section Field
variable {ℓ : StepParameters}
private theorem topField_depends (rule : NoiseRule ℓ) (T : StageTower ℓ) (hr : rule.IsAdmissible T)
    (hL : 8 ≤ ℓ.side) :
    ∀ (s n : ℕ) [NeZero n] (P Q : Finset (TorusSite n)) (W W' : TorusField (fineSide ℓ.side s n))
      (U U' : ChainNoise ℓ s n),
      thickening 5 P ⊆ Q →
      (∀ b : TorusBond (fineSide ℓ.side s n), b.1 ∈ sitesUnder ℓ.side s n Q →
        b.1 + unitStep (fineSide ℓ.side s n) b.2 ∈ sitesUnder ℓ.side s n Q → W b.1 b.2 = W' b.1 b.2) →
      NoiseAgreeAbove ℓ s n Q U U' →
      ∀ c : TorusBond n, c.1 ∈ P → c.1 + unitStep n c.2 ∈ P →
        topField ℓ s n (rule.chain T s n W U) c.1 c.2 =
          topField ℓ s n (rule.chain T s n W' U') c.1 c.2 := by
  intro s
  induction s with
  | zero =>
    intro n _ P Q W W' U U' hPQ hW _ c h1 h2
    have sub : P ⊆ Q := fun x hx => hPQ ((mem_thickening _ _ _).2 ⟨x, hx, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩)
    exact hW c (sub h1) (sub h2)
  | succ s ih =>
    intro n _ P Q W W' U U' hPQ hW hU c h1 h2
    obtain ⟨hU0, hUb, hUc, -⟩ := hU
    have hsub : P ⊆ Q := fun x hx => hPQ ((mem_thickening _ _ _).2 ⟨x, hx, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩)
    have hnear : thickening 5 (sitesInBlocks ℓ.side (thickening 4 P)) ⊆ sitesInBlocks ℓ.side Q := by
      refine thickening_sitesInBlocks_subset hL fun a ha c hc => hPQ ?_
      obtain ⟨x, hx, hd⟩ := (mem_thickening _ _ _).1 ha
      have := _root_.YangMills.Construction.TorusFields.supDist_triangle c a x
      exact (mem_thickening _ _ _).2 ⟨x, hx, by omega⟩
    have hlow := ih (n * ℓ.side) (sitesInBlocks ℓ.side (thickening 4 P)) (sitesInBlocks ℓ.side Q) W W' U.1 U'.1
      hnear hW hU0
    set W₁ := topField ℓ s (n * ℓ.side) (rule.chain T s (n * ℓ.side) W U.1) with hW₁
    set W₁' := topField ℓ s (n * ℓ.side) (rule.chain T s (n * ℓ.side) W' U'.1) with hW₁'
    have hagree : ∀ y ∈ P, ∀ k ≤ 4, AgreeAbove ℓ.side (HullTrees.box y k) W₁ W₁' := by
      intro y hy k hk b b1 b2
      have into : ∀ v, v ∈ HullTrees.box y k → v ∈ thickening 4 P := fun v hv =>
        (mem_thickening _ _ _).2 ⟨y, hy, (mem_box_iff.1 hv).trans hk⟩
      exact hlow b (mem_sitesInBlocks_iff.2 (into _ b1)) (mem_sitesInBlocks_iff.2 (into _ b2))
    have hbase : ∀ y ∈ P, rule.base s n W₁ y (U.2.1 y) = rule.base s n W₁' y (U'.2.1 y) := by
      intro y hy
      rw [hUb y (hsub hy)]
      exact hr.base_depends s n W₁ W₁' y _ (hagree y hy 3 (by norm_num))
    show rule.value s n W₁ (fun y => rule.base s n W₁ y (U.2.1 y)) (c.1, c.2) (U.2.2.1 (c.1, c.2)) =
      rule.value s n W₁' (fun y => rule.base s n W₁' y (U'.2.1 y)) (c.1, c.2) (U'.2.2.1 (c.1, c.2))
    rw [hUc (c.1, c.2) (hsub h1)]
    exact hr.value_depends s n W₁ W₁' _ _ (c.1, c.2) _ (hagree c.1 h1 4 le_rfl) (hbase _ h1) (hbase _ h2)
end Field
section Hot
private theorem containsHotPlaquette_of_agree (ℓ : StepParameters) {n : ℕ} [NeZero n] {V V' : TorusField n}
    {B : Finset (TorusSite n)}
    (h : ∀ c : TorusBond n, c.1 ∈ B → c.1 + unitStep n c.2 ∈ B → V c.1 c.2 = V' c.1 c.2)
    (hh : ContainsHotPlaquette ℓ V B) : ContainsHotPlaquette ℓ V' B := by
  classical
  obtain ⟨⟨x, μ, ν⟩, hp, hs⟩ := hh
  refine ⟨(x, μ, ν), hp, ?_⟩
  have hc : ∀ z ∈ plaquetteVertices x μ ν, z ∈ B := (Finset.mem_filter.1 hp).2.2
  have c1 : x ∈ B := hc _ (by simp [plaquetteVertices])
  have c2 : x + unitStep n μ ∈ B := hc _ (by simp [plaquetteVertices])
  have c3 : x + unitStep n ν ∈ B := hc _ (by simp [plaquetteVertices])
  have c4 : x + unitStep n μ + unitStep n ν ∈ B := hc _ (by simp [plaquetteVertices])
  have c5 : x + unitStep n ν + unitStep n μ ∈ B := by
    rw [add_right_comm]
    exact c4
  have e1 : V x μ = V' x μ := h (x, μ) c1 c2
  have e2 : V (x + unitStep n μ) ν = V' (x + unitStep n μ) ν := h (x + unitStep n μ, ν) c2 c4
  have e3 : V (x + unitStep n ν) μ = V' (x + unitStep n ν) μ := h (x + unitStep n ν, μ) c3 c5
  have e4 : V x ν = V' x ν := h (x, ν) c1 c3
  have e : TorusFields.curvature V x μ ν = TorusFields.curvature V' x μ ν := by
    unfold TorusFields.curvature TorusFields.holonomy
    rw [e1, e2, e3, e4]
  show ℓ.threshold ≤ TorusFields.curvature V' x μ ν
  rw [← e]
  exact hs
private theorem mem_torusHotSites_of_agree (ℓ : StepParameters) (hL : Odd ℓ.side) {m : ℕ} [NeZero m]
    (W W' : TorusField m) (z : TorusSite m)
    (hag : ∀ u i, _root_.YangMills.Construction.TorusFields.supDist u z ≤ 2 ^ 15 + 2 + ℓ.side → W u i = W' u i) (hz : z ∈ torusHotSites ℓ W) :
    z ∈ torusHotSites ℓ W' := by apply _root_.YangMills.SharedProofs.p17017 <;> assumption
end Hot
section Marks
private theorem bondMark_congr (hframe : FrameLocality.FrameCoordLocal) (hblocks : BlockDataIsLocal)
    {R : StepSetup} (hfit : R.params.Admissible) {n : ℕ} [NeZero n] {V V' : TorusField n}
    {W W' : TorusField (n * R.params.side)} (b : TorusBond (n * R.params.side)) (h16 : 16 ≤ n)
    (hm : 0 < R.frameReach) (hm2 : 4 * R.frameReach + 5 < n)
    (hV : FieldsAgreeNear V V' (parentBlock R.params.side b.1) (parentBlock R.params.side b.1) R.frameReach)
    (hV1 : V (parentBlock R.params.side b.1) b.2 = V' (parentBlock R.params.side b.1) b.2)
    (hW : ∀ (e : Fin 4 → ℤ) (k : Fin 4), (∀ j, (e j).natAbs ≤ 4 * R.params.side) →
      W (b.1 + siteOfInt e) k = W' (b.1 + siteOfInt e) k) :
    StepSettings.bondMark R V W b = StepSettings.bondMark R V' W' b := by apply _root_.YangMills.SharedProofs.p1768 <;> assumption
private theorem hotCore_and_bondMark_congr (hframe : FrameLocality.FrameCoordLocal) (hblocks : BlockDataIsLocal)
    {R : StepSetup} (hfit : R.params.Admissible) {n : ℕ} [NeZero n] {V V' : TorusField n}
    {W W' : TorusField (n * R.params.side)} (b : TorusBond (n * R.params.side)) (h16 : 16 ≤ n)
    (hm : 0 < R.frameReach) {D : ℕ}
    (hD1 : 2 * R.nextRange + 2 ^ 15 + 3 + R.params.side ≤ D) (hD2 : 2 * R.frameReach + 3 ≤ D)
    (hv : ∀ c : TorusBond n, _root_.YangMills.Construction.TorusFields.supDist c.1 (parentBlock R.params.side b.1) ≤ D →
      _root_.YangMills.Construction.TorusFields.supDist (c.1 + unitStep n c.2) (parentBlock R.params.side b.1) ≤ D → V c.1 c.2 = V' c.1 c.2)
    (hw : ∀ c : TorusBond (n * R.params.side),
      _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side c.1) (parentBlock R.params.side b.1) ≤ D →
      _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side (c.1 + unitStep _ c.2)) (parentBlock R.params.side b.1) ≤ D →
        W c.1 c.2 = W' c.1 c.2) :
    (parentBlock R.params.side b.1 ∈ hotCoreSites R V ↔ parentBlock R.params.side b.1 ∈ hotCoreSites R V') ∧
      StepSettings.bondMark R V W b = StepSettings.bondMark R V' W' b := by
  classical
  have hodd := hfit.L_odd
  have hLg := hfit.L_ge
  set y := parentBlock R.params.side b.1 with hy
  have one : ∀ {V V' : TorusField n}, (∀ c : TorusBond n, _root_.YangMills.Construction.TorusFields.supDist c.1 y ≤ D →
      _root_.YangMills.Construction.TorusFields.supDist (c.1 + unitStep n c.2) y ≤ D → V c.1 c.2 = V' c.1 c.2) →
      y ∈ hotCoreSites R V → y ∈ hotCoreSites R V' := by
    intro V V' h hz
    obtain ⟨x, hx, hd⟩ := (mem_thickening _ _ _).1 hz
    refine (mem_thickening _ _ _).2 ⟨x, mem_torusHotSites_of_agree R.params hodd V V' x (fun u i hu => ?_) hx, hd⟩
    have t1 := _root_.YangMills.Construction.TorusFields.supDist_triangle u x y
    have t2 : _root_.YangMills.Construction.TorusFields.supDist x y = _root_.YangMills.Construction.TorusFields.supDist y x := _root_.YangMills.Construction.TorusFields.supDist_comm _ _
    have t3 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le u i
    have t4 := _root_.YangMills.Construction.TorusFields.supDist_triangle (u + unitStep n i) u y
    have t5 : _root_.YangMills.Construction.TorusFields.supDist (u + unitStep n i) u = _root_.YangMills.Construction.TorusFields.supDist u (u + unitStep n i) := _root_.YangMills.Construction.TorusFields.supDist_comm _ _
    exact h (u, i) (by show _root_.YangMills.Construction.TorusFields.supDist u y ≤ D; omega) (by show _root_.YangMills.Construction.TorusFields.supDist (u + unitStep n i) y ≤ D; omega)
  refine ⟨⟨one hv, one fun c h1 h2 => (hv c h1 h2).symm⟩, ?_⟩
  by_cases hbig : 4 * R.frameReach + 5 < n
  · refine bondMark_congr hframe hblocks hfit b h16 hm hbig ?_ ?_ ?_
    · intro e he
      have h1 : _root_.YangMills.Construction.TorusFields.supDist (y + siteOfInt e.1) y ≤ R.frameReach := by
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
        refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ _ fun i => ?_
        have := abs_le.1 (he.1 i)
        omega
      have t3 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le (y + siteOfInt e.1) e.2
      have t4 := _root_.YangMills.Construction.TorusFields.supDist_triangle (y + siteOfInt e.1 + unitStep n e.2) (y + siteOfInt e.1) y
      have t5 := _root_.YangMills.Construction.TorusFields.supDist_comm (y + siteOfInt e.1 + unitStep n e.2) (y + siteOfInt e.1)
      exact hv (y + siteOfInt e.1, e.2) (by show _root_.YangMills.Construction.TorusFields.supDist (y + siteOfInt e.1) y ≤ D; omega)
        (by show _root_.YangMills.Construction.TorusFields.supDist (y + siteOfInt e.1 + unitStep n e.2) y ≤ D; omega)
    · have t3 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le y b.2
      have t5 := _root_.YangMills.Construction.TorusFields.supDist_comm (y + unitStep n b.2) y
      have t0 := _root_.YangMills.Construction.TorusFields.supDist_self y
      exact hv (y, b.2) (by show _root_.YangMills.Construction.TorusFields.supDist y y ≤ D; omega) (by show _root_.YangMills.Construction.TorusFields.supDist (y + unitStep n b.2) y ≤ D; omega)
    · intro e k he
      have hv0 : _root_.YangMills.Construction.TorusFields.supDist (b.1 + siteOfInt e) b.1 ≤ 4 * R.params.side := by
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
        exact _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ _ he
      have hbl : ∀ u : TorusSite (n * R.params.side), _root_.YangMills.Construction.TorusFields.supDist u b.1 ≤ 4 * R.params.side + 1 →
          _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side u) y ≤ D := by
        intro u hu
        have h1 : _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side u) y ≤ _root_.YangMills.Construction.TorusFields.supDist u b.1 / R.params.side + 1 :=
          TorusBalls.supDist_parentBlock_le_div_add_one R.params.side u b.1
        have h2 : _root_.YangMills.Construction.TorusFields.supDist u b.1 / R.params.side ≤ 4 := by
          apply Nat.lt_succ_iff.1
          rw [Nat.div_lt_iff_lt_mul (by omega)]
          omega
        omega
      have hv1 : _root_.YangMills.Construction.TorusFields.supDist (b.1 + siteOfInt e + unitStep _ k) b.1 ≤ 4 * R.params.side + 1 := by
        have e1 := _root_.YangMills.Construction.TorusFields.supDist_triangle (b.1 + siteOfInt e + unitStep _ k) (b.1 + siteOfInt e) b.1
        have e2 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le (b.1 + siteOfInt e) k
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at e2
        omega
      exact hw (b.1 + siteOfInt e, k) (hbl _ (by show _root_.YangMills.Construction.TorusFields.supDist (b.1 + siteOfInt e) b.1 ≤ _; omega)) (hbl _ hv1)
  · have hall : ∀ p q : TorusSite n, _root_.YangMills.Construction.TorusFields.supDist p q ≤ D := fun p q => by
      have := SettingShifts.two_mul_supDist_le p q
      omega
    have eV : V = V' := funext fun x => funext fun i => hv (x, i) (hall _ _) (hall _ _)
    have eW : W = W' := funext fun x => funext fun i => hw (x, i) (hall _ _) (hall _ _)
    rw [eV, eW]
private theorem mem_markedBonds_iff {R : StepSetup} {n : ℕ} [NeZero n] {C : Finset (TorusSite n)}
    {b : TorusBond (n * R.params.side)} :
    b ∈ markedBonds R C ↔ b ∈ chartBonds R.params.side n ∧ parentBlock R.params.side b.1 ∉ C := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseFactors.mem_markedBonds_iff <;> assumption
private theorem mem_stepOutcome_bad_iff {ℓ : StepParameters} (rule : NoiseRule ℓ) (T : StageTower ℓ) (s n : ℕ)
    [NeZero n] (W : TorusField (n * ℓ.side)) (U : StepNoise ℓ n) (b : TorusBond (n * ℓ.side)) :
    b ∈ (show Finset (TorusBond (n * ℓ.side)) from (rule.stepOutcome T s n W U).2.2) ↔
      b ∈ markedBonds (T.stage s).toStepSetup
          (hotCoreSites (T.stage s).toStepSetup (rule.stepOutcome T s n W U).2.1) ∧
        ¬ ((U.2.2 b : ℝ) < StepSettings.bondMark (T.stage s).toStepSetup (rule.stepOutcome T s n W U).2.1 W b) :=
  Finset.mem_filter
end Marks
section Borel
private theorem measurable_of_countable_fibres {X D Z : Type} [MeasurableSpace X] [Countable D] [MeasurableSpace Z]
    (f : X → D) (hf : ∀ d, MeasurableSet {x | f x = d}) (G : D → X → Z) (hG : ∀ d, Measurable (G d)) :
    Measurable fun x => G (f x) x := by apply _root_.YangMills.SharedProofs.p26930 <;> assumption
private theorem measurableSet_finsetFilter_eq {X α : Type} [MeasurableSpace X] (s : Finset α) (c : α → X → Prop)
    (hc : ∀ p, MeasurableSet {x | c p x}) (inst : ∀ x, DecidablePred fun p => c p x) (A : Finset α) :
    MeasurableSet {x | s.filter (fun p => c p x) = A} := by apply _root_.YangMills.SharedProofs.p36363 <;> assumption
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem bondMark_eq_sum_markLaw (hLn : R.params.side ∣ n) (n64 : 64 ≤ n) {C : Finset (TorusSite n)}
    {b : TorusBond (n * R.params.side)} (hb : b ∈ markedBonds R C) {V : TorusField n} (hV : hotCoreSites R V = C)
    (W : TorusField (n * R.params.side)) :
    StepSettings.bondMark R V W b = ∑ t ∈ ((markedBonds R C).erase b).powerset, markLaw R W V t := by apply _root_.YangMills.SharedProofs.p31262 <;> assumption
private theorem measurableSet_hotCoreSites_eq (hfit : R.params.Admissible) (hLn : R.params.side ∣ n)
    (C : Finset (TorusSite n)) : MeasurableSet {V : TorusField n | hotCoreSites R V = C} := by apply _root_.YangMills.SharedProofs.p8979 <;> assumption
private theorem measurable_badBonds {X : Type} [MeasurableSpace X] (hfit : R.params.Admissible)
    (hLn : R.params.side ∣ n) (n64 : 64 ≤ n)
    (hco : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    {W : X → TorusField (n * R.params.side)} (hW : Measurable W) {V : X → TorusField n} (hV : Measurable V)
    {ξ : X → TorusBond (n * R.params.side) → I} (hξ : Measurable ξ) {f : X → BondSet (n * R.params.side)}
    (hf : ∀ x (b : TorusBond (n * R.params.side)), b ∈ (show Finset (TorusBond (n * R.params.side)) from f x) ↔
      b ∈ markedBonds R (hotCoreSites R (V x)) ∧
        ¬ (((ξ x b : I) : ℝ) < StepSettings.bondMark R (V x) (W x) b)) :
    Measurable f := by
  classical
  have : Countable (BondSet (n * R.params.side)) :=
    inferInstanceAs (Countable (Finset (TorusBond (n * R.params.side))))
  have hp : Measurable fun x => (W x, V x) := hW.prodMk hV
  have hs : ∀ t : Finset (TorusBond (n * R.params.side)), Measurable fun x => markLaw R (W x) (V x) t := fun t => by
    have h := (hco t).comp hp
    exact h
  let G : Finset (TorusSite n) → X → BondSet (n * R.params.side) := fun C x =>
    (markedBonds R C).filter fun b =>
      ¬ (((ξ x b : I) : ℝ) < ∑ t ∈ ((markedBonds R C).erase b).powerset, markLaw R (W x) (V x) t)
  have hG : ∀ C, Measurable (G C) := by
    intro C
    refine measurable_to_countable' fun a => ?_
    have h1 : ∀ b, Measurable fun x =>
        ∑ t ∈ ((markedBonds R C).erase b).powerset, markLaw R (W x) (V x) t := fun b =>
      Finset.measurable_sum _ fun t _ => hs t
    have h2 : ∀ b, Measurable fun x => ((ξ x b : I) : ℝ) := fun b =>
      measurable_subtype_coe.comp ((measurable_pi_apply b).comp hξ)
    exact measurableSet_finsetFilter_eq (markedBonds R C)
      (fun b x => ¬ (((ξ x b : I) : ℝ) < ∑ t ∈ ((markedBonds R C).erase b).powerset, markLaw R (W x) (V x) t))
      (fun b => (measurableSet_lt (h2 b) (h1 b)).compl) _ a
  have e : f = fun x => G (hotCoreSites R (V x)) x := by
    funext x
    refine (Finset.ext fun b => ?_ : (show Finset (TorusBond (n * R.params.side)) from f x) =
      (show Finset (TorusBond (n * R.params.side)) from G (hotCoreSites R (V x)) x))
    rw [hf x b]
    show _ ↔ b ∈ (markedBonds R (hotCoreSites R (V x))).filter _
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hb, h⟩
      exact ⟨hb, by rwa [← bondMark_eq_sum_markLaw hLn n64 hb rfl]⟩
    · rintro ⟨hb, h⟩
      exact ⟨hb, by rwa [bondMark_eq_sum_markLaw hLn n64 hb rfl]⟩
  rw [e]
  exact measurable_of_countable_fibres (fun x => hotCoreSites R (V x))
    (fun C => hV (measurableSet_hotCoreSites_eq hfit hLn C)) G hG
omit [NeZero n] in
private theorem measurableSet_containsHotPlaquette (ℓ : StepParameters) [NeZero n] (B : Finset (TorusSite n)) :
    MeasurableSet {V : TorusField n | ContainsHotPlaquette ℓ V B} := by
  have e : {V : TorusField n | ContainsHotPlaquette ℓ V B} =
      ⋃ p ∈ plaquettesIn B, {V : TorusField n | ℓ.threshold ≤ TorusFields.curvature V p.1 p.2.1 p.2.2} := by
    ext V
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    rfl
  rw [e]
  exact Finset.measurableSet_biUnion _ fun p _ =>
    (isClosed_le continuous_const (continuous_curvature (n := n) p.1 p.2.1 p.2.2)).measurableSet
section Chain
variable {ℓ : StepParameters}
private theorem measurable_topField (rule : NoiseRule ℓ) (T : StageTower ℓ) (hr : rule.IsAdmissible T) :
    ∀ (s n : ℕ) [NeZero n], Measurable fun p : TorusField (fineSide ℓ.side s n) × ChainNoise ℓ s n =>
      topField ℓ s n (rule.chain T s n p.1 p.2) := by
  intro s
  induction s with
  | zero =>
    intro n _
    exact measurable_fst
  | succ s ih =>
    intro n _
    have hlow : Measurable fun p : TorusField (fineSide ℓ.side (s + 1) n) × ChainNoise ℓ (s + 1) n =>
        ((p.1, p.2.1) : TorusField (fineSide ℓ.side s (n * ℓ.side)) × ChainNoise ℓ s (n * ℓ.side)) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have hW₁ := (ih (n * ℓ.side)).comp hlow
    have hstep : Measurable fun p : TorusField (fineSide ℓ.side (s + 1) n) × ChainNoise ℓ (s + 1) n =>
        (p.2.2 : StepNoise ℓ n) := measurable_snd.comp measurable_snd
    have ho : Measurable fun p : TorusField (fineSide ℓ.side (s + 1) n) × ChainNoise ℓ (s + 1) n =>
        (fun y : TorusSite n => rule.base s n
          (topField ℓ s (n * ℓ.side) (rule.chain T s (n * ℓ.side) p.1 p.2.1)) y (p.2.2.1 y)) :=
      measurable_pi_iff.2 fun y => (hr.base_measurable s n y).comp
        (hW₁.prodMk ((measurable_pi_apply y).comp (measurable_fst.comp hstep)))
    refine measurable_pi_iff.2 fun y => measurable_pi_iff.2 fun i => ?_
    exact measurable_of_countable_fibres _ (fun d => ho (measurableSet_singleton d))
      (fun (d : TorusSite n → BlockOffset ℓ.side)
          (p : TorusField (fineSide ℓ.side (s + 1) n) × ChainNoise ℓ (s + 1) n) =>
        rule.value s n (topField ℓ s (n * ℓ.side) (rule.chain T s (n * ℓ.side) p.1 p.2.1)) d (y, i)
          (p.2.2.2.1 (y, i)))
      (fun d => (hr.value_measurable s n d (y, i)).comp (hW₁.prodMk
        ((measurable_pi_apply (y, i)).comp (measurable_fst.comp (measurable_snd.comp hstep)))))
private theorem measurable_lastBadBonds (rule : NoiseRule ℓ) (T : StageTower ℓ) (hr : rule.IsAdmissible T)
    (hfit : ℓ.Admissible) (hco : T.MarksMeasurable) (s n : ℕ) [NeZero n] (hLn : ℓ.side ∣ n) (n64 : 64 ≤ n) :
    Measurable fun p : TorusField (fineSide ℓ.side (s + 1) n) × ChainNoise ℓ (s + 1) n =>
      (rule.chain T (s + 1) n p.1 p.2).2.2.2 := by
  have hlow : Measurable fun p : TorusField (fineSide ℓ.side (s + 1) n) × ChainNoise ℓ (s + 1) n =>
      ((p.1, p.2.1) : TorusField (fineSide ℓ.side s (n * ℓ.side)) × ChainNoise ℓ s (n * ℓ.side)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hstep : Measurable fun p : TorusField (fineSide ℓ.side (s + 1) n) × ChainNoise ℓ (s + 1) n =>
      (p.2.2 : StepNoise ℓ n) := measurable_snd.comp measurable_snd
  exact measurable_badBonds (R := (T.stage s).toStepSetup) hfit hLn n64 (fun bad => hco s n bad)
    ((measurable_topField rule T hr s (n * ℓ.side)).comp hlow) (measurable_topField rule T hr (s + 1) n)
    (ξ := fun p => p.2.2.2.2) (measurable_snd.comp (measurable_snd.comp hstep))
    (fun p b => mem_stepOutcome_bad_iff rule T s n _ p.2.2 b)
private theorem measurable_unitIndicator (rule : NoiseRule ℓ) (T : StageTower ℓ) (hr : rule.IsAdmissible T)
    (hfit : ℓ.Admissible) (hco : T.MarksMeasurable) (u n : ℕ) [NeZero n] (z : TorusSite n) (hLn : ℓ.side ∣ n)
    (n64 : 64 ≤ n) : Measurable (unitIndicator rule T u n z) := by
  classical
  have hset : MeasurableSet {p : TorusField (fineSide ℓ.side u n) × ChainNoise ℓ u n |
      IsUnit T u n (rule.chain T u n p.1 p.2) z} := by
    have hhot := measurable_topField rule T hr u n
      (measurableSet_containsHotPlaquette ℓ (HullTrees.box z (4 * stageRange T u)))
    cases u with
    | zero =>
      have e : {p : TorusField (fineSide ℓ.side 0 n) × ChainNoise ℓ 0 n |
            IsUnit T 0 n (rule.chain T 0 n p.1 p.2) z} =
          (fun p : TorusField (fineSide ℓ.side 0 n) × ChainNoise ℓ 0 n =>
              topField ℓ 0 n (rule.chain T 0 n p.1 p.2)) ⁻¹'
            {V : TorusField n | ContainsHotPlaquette ℓ V (HullTrees.box z (4 * stageRange T 0))} := by
        ext p
        simp [IsUnit, ContainsBadBlock]
      rw [e]
      exact hhot
    | succ s =>
      have hb := measurable_lastBadBonds rule T hr hfit hco s n hLn n64
        (MeasurableSpace.measurableSet_top (s := {S : BondSet (n * ℓ.side) |
          ∃ b : TorusBond (n * ℓ.side), b ∈ (show Finset (TorusBond (n * ℓ.side)) from S) ∧
            parentBlock ℓ.side b.1 ∈ HullTrees.box z (4 * stageRange T (s + 1))}))
      exact hhot.union hb
  show Measurable fun p => unitIndicator rule T u n z p
  unfold unitIndicator
  exact Measurable.ite hset measurable_const measurable_const
end Chain
end Borel
section Unit
variable {ℓ : StepParameters}
private theorem containsBadBlock_of_agree (hframe : FrameLocality.FrameCoordLocal) (hblocks : BlockDataIsLocal)
    (hfit : ℓ.Admissible) (T : StageTower ℓ) (rule : NoiseRule ℓ) (hr : rule.IsAdmissible T) (s n : ℕ) [NeZero n]
    (z : TorusSite n) (h16 : 16 ≤ n)
    (hR : 2 ^ 16 + ℓ.side ≤ stageRange T (s + 1)) (h1 : 2 ^ 16 ≤ stageRange T s)
    (h2 : stageRange T s ≤ 2 * stageRange T (s + 1))
    (W W' : TorusField (fineSide ℓ.side (s + 1) n)) (U U' : ChainNoise ℓ (s + 1) n)
    (hW : ∀ b : TorusBond (fineSide ℓ.side (s + 1) n),
      b.1 ∈ sitesUnder ℓ.side (s + 1) n (HullTrees.box z (7 * stageRange T (s + 1))) →
      b.1 + unitStep (fineSide ℓ.side (s + 1) n) b.2 ∈
        sitesUnder ℓ.side (s + 1) n (HullTrees.box z (7 * stageRange T (s + 1))) →
      W b.1 b.2 = W' b.1 b.2)
    (hU : NoiseAgreeAbove ℓ (s + 1) n (HullTrees.box z (7 * stageRange T (s + 1))) U U')
    (hb : ContainsBadBlock ℓ (s + 1) n (rule.chain T (s + 1) n W U)
      (HullTrees.box z (4 * stageRange T (s + 1)))) :
    ContainsBadBlock ℓ (s + 1) n (rule.chain T (s + 1) n W' U') (HullTrees.box z (4 * stageRange T (s + 1))) := by
  have hL8 : 8 ≤ ℓ.side := by
    have := hfit.L_ge
    omega
  obtain ⟨r, hr'⟩ : ∃ r, r = stageRange T (s + 1) := ⟨_, rfl⟩
  rw [← hr'] at hW hU hb hR h2 ⊢
  obtain ⟨P, hP⟩ : ∃ P, P = HullTrees.box z (6 * r + 2 ^ 15 + 3 + ℓ.side) := ⟨_, rfl⟩
  have hnear : ∀ a ∈ P, ∀ c, _root_.YangMills.Construction.TorusFields.supDist c a ≤ 5 → c ∈ HullTrees.box z (7 * r) := by
    intro a ha c hc
    rw [hP] at ha
    have e1 := mem_box_iff.1 ha
    have e2 := _root_.YangMills.Construction.TorusFields.supDist_triangle c a z
    exact mem_box_iff.2 (by omega)
  have hPQ : thickening 5 P ⊆ HullTrees.box z (7 * r) := fun x hx => by
    obtain ⟨a, ha, hd⟩ := (mem_thickening _ _ _).1 hx
    exact hnear a ha x hd
  have hV := topField_depends rule T hr hL8 (s + 1) n P _ W W' U U' hPQ hW hU
  have hW₁ := topField_depends rule T hr hL8 s (n * ℓ.side) (sitesInBlocks ℓ.side P)
    (sitesInBlocks ℓ.side (HullTrees.box z (7 * r))) W W' U.1 U'.1
    (thickening_sitesInBlocks_subset hL8 fun a ha c hc => hnear a ha c (by omega)) hW hU.1
  obtain ⟨b, hbad, hy⟩ := hb
  have hy' := mem_box_iff.1 hy
  have e1 : (T.stage s).toStepSetup.nextRange = r := hr'.symm
  have e2 : (T.stage s).toStepSetup.frameReach = stageRange T s / 2 ^ 11 := rfl
  have hm : 0 < (T.stage s).toStepSetup.frameReach := by
    rw [e2]
    omega
  have hinP : ∀ c : TorusSite n, _root_.YangMills.Construction.TorusFields.supDist c (parentBlock ℓ.side b.1) ≤ 2 * r + 2 ^ 15 + 3 + ℓ.side → c ∈ P := by
    intro c hc
    have e3 := _root_.YangMills.Construction.TorusFields.supDist_triangle c (parentBlock ℓ.side b.1) z
    rw [hP]
    exact mem_box_iff.2 (by omega)
  obtain ⟨hhull, hmark⟩ := hotCore_and_bondMark_congr hframe hblocks (R := (T.stage s).toStepSetup) hfit
    (V := topField ℓ (s + 1) n (rule.chain T (s + 1) n W U))
    (V' := topField ℓ (s + 1) n (rule.chain T (s + 1) n W' U'))
    (W := topField ℓ s (n * ℓ.side) (rule.chain T s (n * ℓ.side) W U.1))
    (W' := topField ℓ s (n * ℓ.side) (rule.chain T s (n * ℓ.side) W' U'.1)) b h16 hm
    (D := 2 * r + 2 ^ 15 + 3 + ℓ.side) (by rw [e1]) (by rw [e2]; show _ ≤ 2 * r + 2 ^ 15 + 3 + ℓ.side; omega)
    (fun c c1 c2 => hV c (hinP _ c1) (hinP _ c2))
    (fun c c1 c2 => hW₁ c (mem_sitesInBlocks_iff.2 (hinP _ c1)) (mem_sitesInBlocks_iff.2 (hinP _ c2)))
  have hξ : U.2.2.2 b = U'.2.2.2 b := hU.2.2.2 b (mem_box_iff.2 (by omega))
  obtain ⟨hb1, hb2⟩ := (mem_stepOutcome_bad_iff rule T s n _ U.2 b).1 hbad
  obtain ⟨hc1, hc2⟩ := mem_markedBonds_iff.1 hb1
  refine ⟨b, (mem_stepOutcome_bad_iff rule T s n _ U'.2 b).2
    ⟨mem_markedBonds_iff.2 ⟨hc1, fun h => hc2 (hhull.2 h)⟩, ?_⟩, hy⟩
  intro hlt
  refine hb2 ?_
  have hm' : StepSettings.bondMark (T.stage s).toStepSetup (rule.stepOutcome T s n _ U.2).2.1 _ b =
      StepSettings.bondMark (T.stage s).toStepSetup (rule.stepOutcome T s n _ U'.2).2.1 _ b := hmark
  rw [hm', hξ]
  exact hlt
private theorem isUnit_of_agree (hframe : FrameLocality.FrameCoordLocal) (hblocks : BlockDataIsLocal)
    (hfit : ℓ.Admissible) (T : StageTower ℓ) (rule : NoiseRule ℓ) (hr : rule.IsAdmissible T) (u n : ℕ) [NeZero n]
    (z : TorusSite n) (h16 : 16 ≤ n) (hR : 2 ^ 16 + ℓ.side ≤ stageRange T u)
    (hdown : ∀ s, u = s + 1 → 2 ^ 16 ≤ stageRange T s ∧ stageRange T s ≤ 2 * stageRange T u)
    (W W' : TorusField (fineSide ℓ.side u n)) (U U' : ChainNoise ℓ u n)
    (hW : ∀ b : TorusBond (fineSide ℓ.side u n), b.1 ∈ sitesUnder ℓ.side u n (HullTrees.box z (7 * stageRange T u)) →
      b.1 + unitStep (fineSide ℓ.side u n) b.2 ∈ sitesUnder ℓ.side u n (HullTrees.box z (7 * stageRange T u)) →
      W b.1 b.2 = W' b.1 b.2)
    (hU : NoiseAgreeAbove ℓ u n (HullTrees.box z (7 * stageRange T u)) U U')
    (hunit : IsUnit T u n (rule.chain T u n W U) z) : IsUnit T u n (rule.chain T u n W' U') z := by
  have hL8 : 8 ≤ ℓ.side := by
    have := hfit.L_ge
    omega
  rcases hunit with hh | hb
  · refine Or.inl (containsHotPlaquette_of_agree ℓ (fun c c1 c2 => ?_) hh)
    have hPQ : thickening 5 (HullTrees.box z (4 * stageRange T u)) ⊆ HullTrees.box z (7 * stageRange T u) :=
      fun x hx => by
        obtain ⟨a, ha, hd⟩ := (mem_thickening _ _ _).1 hx
        have e1 := mem_box_iff.1 ha
        have e2 := _root_.YangMills.Construction.TorusFields.supDist_triangle x a z
        exact mem_box_iff.2 (by omega)
    exact topField_depends rule T hr hL8 u n _ _ W W' U U' hPQ hW hU c c1 c2
  · refine Or.inr ?_
    cases u with
    | zero => exact hb.elim
    | succ s =>
      obtain ⟨h1, h2⟩ := hdown s rfl
      exact containsBadBlock_of_agree hframe hblocks hfit T rule hr s n z h16 hR h1 h2 W W' U U' hW hU hb
end Unit
section ScaleFlow
private theorem le_clusterRange_of_pow_le {x : ℝ} {N : ℕ} (h : (N : ℝ) ^ 100 ≤ x) : N ≤ clusterRange x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.NearPotentialBound.le_clusterRange_of_pow_le <;> assumption
private theorem clusterRange_le_two_mul {x x' : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x') (h : x ≤ 2 * x') :
    clusterRange x ≤ 2 * clusterRange x' := by apply _root_.YangMills.SharedProofs.p21096 <;> assumption
private theorem expansionCoupling_spec {ℓ : StepParameters} (hret : StepReturn.ExpansionReturnsAt ℓ) {t : ℕ}
    {x : ℝ} {D : TorusFunctional} (hy : ℓ.y₁ ≤ x) (hrow : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
      |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
end ScaleFlow
end UnitIndicatorLocality
open UnitIndicatorLocality in
theorem unitIndicatorLocal_holds (hframe : FrameLocality.FrameCoordLocal) (hblocks : BlockDataIsLocal) :
    unitIndicatorLocal := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hdrawn _ _ _ _
  refine ⟨0, ?_⟩
  intro Kr _ _ _ _ _
  refine ⟨max Tb.floorMin (max (((2 ^ 16 + Tb.side : ℕ) : ℝ) ^ 100) (2 * Tb.B + 1)), ?_⟩
  intro y hy hret hrow g β K m T u n _ hat rule hrule z
  classical
  have hfit := hdrawn.fits y ((le_max_left _ _).trans hy)
  have hy1 : (((2 ^ 16 + Tb.side : ℕ) : ℝ) ^ 100) ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy2 : 2 * Tb.B + 1 ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hrun := hat.chain
  have hΞ : windowUpper (Tb.stepParameters y) g = (g ^ 2)⁻¹ + 2 * Tb.B := rfl
  have hB : 0 < Tb.B := hfit.B_pos
  have hfloor := hrun.le_inv_sq
  have habove := hrun.upper_le
  have hpass := hrun.isFirst
  rw [hΞ] at habove
  have hpass2 : ∀ k < K, (g ^ 2)⁻¹ + 2 * Tb.B < (couplingFlow (Tb.stepParameters y) β k).1 := fun k hk => by
    have := hpass.2 k hk
    rwa [hΞ] at this
  have hfl : ∀ j < K, y ≤ (couplingFlow (Tb.stepParameters y) β j).1 := fun j hj => by
    have := hpass2 j hj
    linarith
  have hrows : ∀ j ≤ K, HasExpansion (Tb.stepParameters y) j (couplingFlow (Tb.stepParameters y) β j).1
      (couplingFlow (Tb.stepParameters y) β j).2 := by
    intro j
    induction j with
    | zero =>
      intro _
      exact hrow β (by linarith)
    | succ j ih =>
      intro hj
      exact (expansionCoupling_spec hret (hfl j (by omega)) (ih (by omega))).1
  have hmove : ∀ j < K, |(couplingFlow (Tb.stepParameters y) β (j + 1)).1 -
      (couplingFlow (Tb.stepParameters y) β j).1| ≤ 2 * Tb.B := fun j hj =>
    (expansionCoupling_spec hret (hfl j hj) (hrows j hj.le)).2
  have hall : ∀ j ≤ K, y ≤ (couplingFlow (Tb.stepParameters y) β j).1 := by
    intro j hj
    rcases hj.lt_or_eq with h | rfl
    · exact hfl j h
    · cases j with
      | zero =>
        show y ≤ β
        linarith
      | succ k =>
        have h1 := abs_le.1 (hmove k (by omega))
        have h2 := hpass2 k (by omega)
        linarith [h1.1]
  have hx : ∀ j ≤ K, (T.stage j).coupling = (couplingFlow (Tb.stepParameters y) β j).1 := fun j hj =>
    hrun.follows j (by omega)
  have hrange : ∀ j ≤ K, 2 ^ 16 + (Tb.stepParameters y).side ≤ stageRange T j := fun j hj => by
    show 2 ^ 16 + Tb.side ≤ clusterRange (T.stage j).coupling
    rw [hx j hj]
    exact le_clusterRange_of_pow_le (hy1.trans (hall j hj))
  have hu := hat.le
  have hdown : ∀ s, u = s + 1 → 2 ^ 16 ≤ stageRange T s ∧ stageRange T s ≤ 2 * stageRange T u := by
    rintro s rfl
    refine ⟨by have := hrange s (by omega); omega, ?_⟩
    show clusterRange (T.stage s).coupling ≤ 2 * clusterRange (T.stage (s + 1)).coupling
    rw [hx s (by omega), hx (s + 1) hu]
    have h1 := abs_le.1 (hmove s (by omega))
    have h2 := hall s (by omega)
    have h3 := hall (s + 1) hu
    exact clusterRange_le_two_mul (by linarith) (by linarith) (by linarith [h1.1])
  have hside : n = 2 * Tb.side ^ m * Tb.side ^ (K - u) := by
    rw [hat.side_eq]
    unfold torusSideAtLevel
    rw [fineSide_eq]
  have hvol := hrun.volume_le
  have hLg : 2 ^ 16 ≤ Tb.side := hfit.L_ge
  have hn₀ : 4096 ≤ Tb.n₀ := hfit.n₀_ge
  have hmul : 64 ≤ Tb.side * Tb.n₀ := by nlinarith
  have hm1 : m ≠ 0 := by
    rintro rfl
    simp only [pow_zero, mul_one] at hvol
    omega
  have hle : 2 * Tb.side ^ m ≤ n := by
    rw [hside]
    exact Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
  have n64 : 64 ≤ n := by omega
  have hLn : (Tb.stepParameters y).side ∣ n := by
    rw [hside]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self _ hm1) 2) _
  have hreads : DependsAbove (Tb.stepParameters y) u n (HullTrees.box z (7 * stageRange T u))
      (unitIndicator rule T u n z) := by
    intro W W' U U' hW hU
    have hiff : IsUnit T u n (rule.chain T u n W U) z ↔ IsUnit T u n (rule.chain T u n W' U') z :=
      ⟨isUnit_of_agree hframe hblocks hfit T rule hrule u n z (by omega) (hrange u hu) hdown W W' U U' hW hU,
        isUnit_of_agree hframe hblocks hfit T rule hrule u n z (by omega) (hrange u hu) hdown W' W U' U
          (fun b h1 h2 => (hW b h1 h2).symm) (noiseAgreeAbove_symm _ u n hU)⟩
    show (if IsUnit T u n (rule.chain T u n W U) z then (1 : ℝ) else 0) =
      if IsUnit T u n (rule.chain T u n W' U') z then (1 : ℝ) else 0
    exact if_congr hiff rfl rfl
  refine ⟨hreads, fun G c hsub => ⟨measurable_unitIndicator rule T hrule hfit hrun.marks u n z hLn n64,
    ⟨1, fun p => ?_⟩, fun p => ?_, dependsAbove_mono hsub hreads⟩⟩
  · show |if IsUnit T u n (rule.chain T u n p.1 p.2) z then (1 : ℝ) else 0| ≤ 1
    split_ifs <;> simp
  · show 0 ≤ if IsUnit T u n (rule.chain T u n p.1 p.2) z then (1 : ℝ) else 0
    split_ifs <;> simp
end YangMills.Construction.HullTrees
end
