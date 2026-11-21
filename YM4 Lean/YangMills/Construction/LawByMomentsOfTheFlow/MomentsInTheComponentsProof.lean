import YangMills.Construction.LawByMomentsOfTheFlow.LawInTheComponentsProof
import YangMills.Construction.LawByMomentsOfTheFlow.LimitFieldReadsTheComponents
import YangMills.Construction.LawByMomentsOfTheFlow.LimitFieldsExist
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAtTheLastFarLevelInALimitField
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsByTheGaussianChain
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsOfTheResponsesInALimitField
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.MomentMethod YangMills.Construction.TorusLimits YangMills.Construction.ChainNoise YangMills.Construction.InfiniteLattice YangMills.Construction.LevelTestFunctions
private theorem pow_mul_exp_neg_rpow_le {x : ℝ} (hx : 1 ≤ x) {b : ℕ} (hb : b ≤ 8) :
    x ^ b * Real.exp (-(x ^ ((1 : ℝ) / 200))) ≤ (Nat.factorial 1700 : ℝ) * x ^ (-(1 / 2) : ℝ) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (Nat.factorial 1700 : ℝ) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = x ^ ((1 : ℝ) / 200) := ⟨_, rfl⟩
  have hw0 : 0 < w := hw ▸ Real.rpow_pos_of_pos hx0 _
  have hpow : w ^ 1700 = x ^ ((17 : ℝ) / 2) := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have h1 : w ^ 1700 / N ≤ Real.exp w := by
    rw [hN]
    exact Real.pow_div_factorial_le_exp _ hw0.le 1700
  have h2 : Real.exp (-w) ≤ N / w ^ 1700 := by
    rw [Real.exp_neg]
    have := inv_anti₀ (by positivity) h1
    rwa [inv_div] at this
  have h3 : x ^ b ≤ x ^ (8 : ℕ) := pow_le_pow_right₀ hx hb
  rw [← hN, ← hw]
  calc x ^ b * Real.exp (-w) ≤ x ^ (8 : ℕ) * (N / w ^ 1700) :=
        mul_le_mul h3 h2 (Real.exp_pos _).le (by positivity)
    _ = N * (x ^ (8 : ℝ) / x ^ ((17 : ℝ) / 2)) := by
        rw [hpow, ← Real.rpow_natCast x 8]
        push_cast
        ring
    _ = N * x ^ (-(1 / 2) : ℝ) := by
        rw [← Real.rpow_sub hx0]
        norm_num
section PointFacts
variable {Λ : MomentParameters}
private theorem sameDataOtherSide_withSideExponent (S : MomentPoint Λ) (m : ℕ) (hp hs) :
    S.SameDataOtherSide (S.withSideExponent m hp hs) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩
private theorem scaleCoupling_eq_of_sameData {S S' : MomentPoint Λ} (h : S.SameDataOtherSide S') :
    S'.scaleCoupling = S.scaleCoupling := by
  unfold MomentPoint.scaleCoupling MomentPoint.coupling
  rw [h.scaleLevel_eq, h.β_eq]
private theorem range_eq_of_sameData {S S' : MomentPoint Λ} (h : S.SameDataOtherSide S') : S'.range = S.range := by
  unfold MomentPoint.range
  rw [scaleCoupling_eq_of_sameData h]
end PointFacts
private theorem forAllHullParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllHullParameters Q₁)
    (h₂ : ForAllHullParameters Q₂) : ForAllHullParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p1668 <;> assumption
private theorem forAllHullParameters_mono {Q₁ Q₂ : MomentParameters → Prop} (h : ForAllHullParameters Q₁)
    (f : ∀ Λ : MomentParameters, 2 ≤ Λ.k → Λ.k ≤ 8 → 0 < Λ.stepParams.coupling → Q₁ Λ → Q₂ Λ) : ForAllHullParameters Q₂ := by apply _root_.YangMills.SharedProofs.p22893 <;> assumption
section LimitLaw
variable {Λ : MomentParameters}
set_option maxHeartbeats 4000000 in
private theorem moment_bounds_at_point (hE : exists_jointLimitLaw_statement)
    (hR : ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (K : ℕ) (ν : Measure (RefinedGaugeField Λ.stepParams.side K))
      (κ : Kernel (RefinedGaugeField Λ.stepParams.side K) (RefinedGaugeField Λ.stepParams.side K)) (c : Fin Λ.k → ℝ)
      (B : Finset (Fin Λ.k)) (j : F.Index) (b₁ b₂ : ℝ), S.data.windowLevel = K →
      IsTorusLimitAlong Λ.stepParams.side K S.β ν F.exponents → IsPeriodicConditionalKernel Λ.stepParams.side K ν F.period κ →
      F.observables j = bottomProduct c B → (∀ᵐ v ∂F.law, b₁ ≤ F.condMeanAt j v ∧ F.condMeanAt j v ≤ b₂) →
      ∀ᵐ U ∂ν, b₁ ≤ S.centredStateMoment (κ U) c B ∧ S.centredStateMoment (κ U) c B ≤ b₂)
    {C₄ : ℕ → ℝ} {X₄ C₅ X₅ C₆ X₆ X₀ N : ℝ} (hN0 : 0 ≤ N)
    (hpe : ∀ (x : ℝ), 1 ≤ x → ∀ b : ℕ, b ≤ 8 → x ^ b * Real.exp (-(x ^ ((1 : ℝ) / 200))) ≤ N * x ^ (-(1 / 2) : ℝ))
    (h41 : ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (c : Fin Λ.k → ℝ),
      (∀ i, Tendsto (fun m => (F.points m).kappaAtLast i) atTop (𝓝 (c i))) → ∀ (B : Finset (Fin Λ.k)) (j j' : F.Index),
      F.observables j = bottomProduct c B → F.observables j' = responseProduct B →
      (X₄ ≤ S.scaleCoupling → ∀ᵐ v ∂F.law, |F.condMeanAt j v - F.condMeanAt j' v| ≤ Real.exp (-(S.scaleCoupling ^ ((1 : ℝ) / 200)))) ∧
      ∀ M : ℕ, S.scaleCoupling ≤ M → ∀ᵐ v ∂F.law, |F.condMeanAt j v| ≤ C₄ M)
    (h51 : ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (d : ℕ → ℕ)
      (μ : ∀ m, Measure (LevelChain Λ.stepParams.side ((F.points m).lastSeparated + d m) ((F.points m).data.period Λ.stepParams.side))),
      (∀ m, (F.points m).lastSeparated + d m = (F.points m).data.windowLevel) →
      (∀ m, IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling ((F.points m).lastSeparated + d m) ((F.points m).data.period Λ.stepParams.side)) (μ m)) →
      ∀ (B : Finset (Fin Λ.k)) (e : ℝ),
        Tendsto (fun m => ∫ X, ∏ i ∈ B, (F.points m).halfForm (d m) ((F.points m).data.period Λ.stepParams.side) i X ∂(μ m)) atTop (𝓝 e) →
        ∀ j : F.Index, F.observables j = responseProduct B → X₅ ≤ S.scaleCoupling →
          ∀ᵐ v ∂F.law, |S.scaleCoupling ^ B.card * F.condMeanAt j v - e| ≤
            C₅ * (S.range : ℝ) ^ (4 * B.card + 3) * S.scaleCoupling ^ (-(1 / 2) + 1 / 1000 : ℝ))
    (hPL : ∀ S : MomentPoint Λ, (∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
        ({ S.data with sideExponent := m } : LevelData Λ.k).SupAdmissible Λ.stepParams.side Λ.R Λ.d ∧
        Λ.stepParams.side * Λ.stepParams.n₀ ≤ ({ S.data with sideExponent := m } : LevelData Λ.k).period Λ.stepParams.side) ∧
      (∃ b : ℝ, ∀ (m : ℕ) hp hs (i : Fin Λ.k), |(S.withSideExponent m hp hs).kappaAtLast i| ≤ b) ∧
      (∃ rule : NoiseRule Λ.stepParams, rule.IsAdmissible S.tower) ∧
      ∀ (rule : NoiseRule Λ.stepParams) (ms : ℕ → ℕ) (Sq : ℕ → MomentPoint Λ) (p : ℕ), rule.IsAdmissible S.tower → 1 ≤ p →
        StrictMono ms → (∀ i, ∃ hp hs, Sq i = S.withSideExponent (ms i) hp hs) → (translatedTori Sq p).IsPreserving ∧
        ∀ (c : Fin Λ.k → ℝ) (B : Finset (Fin Λ.k)), TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (bottomProduct c B)) ∧
          TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (responseProduct B)))
    (hMG : ∀ S : MomentPoint Λ, X₆ ≤ S.scaleCoupling → ∀ d : ℕ, S.lastSeparated + d = S.data.windowLevel →
      ∀ μ : Measure (LevelChain Λ.stepParams.side (S.lastSeparated + d) (S.data.period Λ.stepParams.side)),
      IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling (S.lastSeparated + d) (S.data.period Λ.stepParams.side)) μ →
      ∀ B : Finset (Fin Λ.k), |∫ X, ∏ i ∈ B, S.halfForm d (S.data.period Λ.stepParams.side) i X ∂μ| ≤
        C₆ * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 1000))
    (hGa : ∀ (s n : ℕ) [NeZero n], ∃ μ : Measure (LevelChain Λ.stepParams.side s n), IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling s n) μ)
    (hk8 : Λ.k ≤ 8) (hX₁ : 1 ≤ X₀) (hX₄ : X₄ ≤ X₀) (hX₅ : X₅ ≤ X₀) (hX₆ : X₆ ≤ X₀)
    {K : ℕ} {ν : Measure (RefinedGaugeField Λ.stepParams.side K)} {ms₀ : ℕ → ℕ} (S : MomentPoint Λ) (hK : S.data.windowLevel = K)
    (hν : IsTorusLimitAlong Λ.stepParams.side K S.β ν ms₀) {p : ℕ} (hp : 1 ≤ p)
    {κ : Kernel (RefinedGaugeField Λ.stepParams.side K) (RefinedGaugeField Λ.stepParams.side K)}
    (hκ : IsPeriodicConditionalKernel Λ.stepParams.side K ν p κ) :
    ∃ c : Fin Λ.k → ℝ, ∀ᵐ U ∂ν,
      (S.scaleCoupling ≤ X₀ → ∀ B : Finset (Fin Λ.k), |S.centredStateMoment (κ U) c B| ≤ |C₄ ⌈X₀⌉₊| + |C₅| + N + |C₆|) ∧
      (X₀ ≤ S.scaleCoupling → ∀ δ : ℝ, 0 < δ → ∃ (S' : MomentPoint Λ) (d : ℕ) (_ : S'.lastSeparated + d = S'.data.windowLevel)
          (μ : Measure (LevelChain Λ.stepParams.side (S'.lastSeparated + d) (S'.data.period Λ.stepParams.side))), S.SameDataOtherSide S' ∧
          IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling (S'.lastSeparated + d) (S'.data.period Λ.stepParams.side)) μ ∧
          ∀ B : Finset (Fin Λ.k),
            |S.scaleCoupling ^ B.card * S.centredStateMoment (κ U) c B - ∫ X, ∏ i ∈ B, S'.halfForm d (S'.data.period Λ.stepParams.side) i X ∂μ| ≤
              (|C₄ ⌈X₀⌉₊| + |C₅| + N + |C₆|) * (S.range : ℝ) ^ (4 * B.card + 3) * S.scaleCoupling ^ (-(1 / 2) + 1 / 1000 : ℝ) + δ ∧
            |∫ X, ∏ i ∈ B, S'.halfForm d (S'.data.period Λ.stepParams.side) i X ∂μ| ≤
              (|C₄ ⌈X₀⌉₊| + |C₅| + N + |C₆|) * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 1000)) := by
  obtain ⟨⟨m₀, hm₀⟩, ⟨bc, hbc⟩, ⟨rule, hrule⟩, hmom⟩ := hPL S
  obtain ⟨hνpos, hνmono, hνlim⟩ := hν
  have hge : ∀ i, m₀ ≤ ms₀ (i + m₀) := fun i =>
    le_trans (by omega) (hνmono.le_apply (x := i + m₀))
  obtain ⟨Sq₁, hSq₁⟩ : ∃ Sq₁ : ℕ → MomentPoint Λ, ∀ i, ∃ hp hs, Sq₁ i = S.withSideExponent (ms₀ (i + m₀)) hp hs :=
    ⟨fun i => S.withSideExponent (ms₀ (i + m₀)) (hm₀ _ (hge i)).1 (hm₀ _ (hge i)).2, fun i => ⟨_, _, rfl⟩⟩
  have hside : ∀ i, S.SameDataOtherSide (Sq₁ i) := fun i => by
    obtain ⟨a, b, h⟩ := hSq₁ i
    rw [h]
    exact sameDataOtherSide_withSideExponent S _ a b
  have hcb : ∀ i (l : Fin Λ.k), |(Sq₁ i).kappaAtLast l| ≤ bc := fun i l => by
    obtain ⟨a, b, h⟩ := hSq₁ i
    rw [h]
    exact hbc _ a b l
  have ht : ∀ i, (Sq₁ i).lastSeparated + ((Sq₁ i).data.windowLevel - (Sq₁ i).lastSeparated) = (Sq₁ i).data.windowLevel :=
    fun i => Nat.add_sub_of_le (Sq₁ i).lastSeparated_le
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℕ, ∀ i, (Sq₁ i).lastSeparated + d i = (Sq₁ i).data.windowLevel := ⟨_, ht⟩
  choose μ hμ using fun i => hGa ((Sq₁ i).lastSeparated + d i) ((Sq₁ i).data.period Λ.stepParams.side)
  obtain ⟨EG, hEG⟩ : ∃ EG : ℕ → Finset (Fin Λ.k) → ℝ, ∀ i B,
      EG i B = ∫ X, ∏ l ∈ B, (Sq₁ i).halfForm (d i) ((Sq₁ i).data.period Λ.stepParams.side) l X ∂(μ i) :=
    ⟨_, fun _ _ => rfl⟩
  have hEGb : X₀ ≤ S.scaleCoupling → ∀ i B, |EG i B| ≤ C₆ * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 1000) := by
    intro hx i B
    have hh := hMG (Sq₁ i) (by rw [scaleCoupling_eq_of_sameData (hside i)]; exact hX₆.trans hx) (d i) (hd i) (μ i) (hμ i) B
    rw [scaleCoupling_eq_of_sameData (hside i), range_eq_of_sameData (hside i)] at hh
    rw [hEG]
    exact hh
  obtain ⟨u, hu⟩ : ∃ u : ℕ → (Fin Λ.k → ℝ) × (Finset (Fin Λ.k) → ℝ), ∀ i,
      u i = (fun l => (Sq₁ i).kappaAtLast l, fun B => if X₀ ≤ S.scaleCoupling then EG i B else 0) := ⟨_, fun _ => rfl⟩
  obtain ⟨Rb, hRb⟩ : ∃ Rb : ℝ, Rb = |bc| + ∑ B : Finset (Fin Λ.k), |C₆ * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 1000)| :=
    ⟨_, rfl⟩
  have hRb0 : 0 ≤ Rb := by
    rw [hRb]
    positivity
  have hub : ∀ i, u i ∈ Metric.closedBall (0 : (Fin Λ.k → ℝ) × (Finset (Fin Λ.k) → ℝ)) Rb := by
    intro i
    rw [mem_closedBall_zero_iff, Prod.norm_def, hu]
    refine max_le ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg hRb0).2 fun l => ?_
      rw [Real.norm_eq_abs, hRb]
      have h1 := (hcb i l).trans (le_abs_self _)
      have h2 : 0 ≤ ∑ B : Finset (Fin Λ.k), |C₆ * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 1000)| :=
        Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    · refine (pi_norm_le_iff_of_nonneg hRb0).2 fun B => ?_
      rw [Real.norm_eq_abs, hRb]
      have h2 : |C₆ * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 1000)| ≤
          ∑ B : Finset (Fin Λ.k), |C₆ * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 1000)| :=
        Finset.single_le_sum
          (f := fun B : Finset (Fin Λ.k) => |C₆ * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 1000)|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ B)
      have h3 := abs_nonneg bc
      by_cases hx : X₀ ≤ S.scaleCoupling
      · simp only [if_pos hx]
        have := (hEGb hx i B).trans (le_abs_self _)
        linarith
      · simp only [if_neg hx, abs_zero]
        have h5 : 0 ≤ ∑ B : Finset (Fin Λ.k), |C₆ * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 1000)| :=
          Finset.sum_nonneg fun _ _ => abs_nonneg _
        linarith
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hub
  obtain ⟨c, hc⟩ : ∃ c, c = a.1 := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = a.2 := ⟨_, rfl⟩
  have hcl : ∀ l, Tendsto (fun i => (Sq₁ (φ i)).kappaAtLast l) atTop (𝓝 (c l)) := by
    intro l
    have h1 := ((continuous_apply l).comp continuous_fst).continuousAt.tendsto.comp hlim
    rw [hc]
    refine h1.congr fun i => ?_
    simp [hu]
  have hel : X₀ ≤ S.scaleCoupling → ∀ B, Tendsto (fun i => EG (φ i) B) atTop (𝓝 (e B)) := by
    intro hx B
    have h1 := ((continuous_apply B).comp continuous_snd).continuousAt.tendsto.comp hlim
    rw [he]
    refine h1.congr fun i => ?_
    simp [hu, hx]
  have hms₂ : StrictMono fun i => ms₀ (φ i + m₀) := fun i j hij => hνmono (by have := hφ hij; omega)
  obtain ⟨hkeep₂, hfam₂⟩ := hmom rule (fun i => ms₀ (φ i + m₀)) (fun i => Sq₁ (φ i)) p hrule hp hms₂ (fun i => hSq₁ (φ i))
  obtain ⟨g, hg⟩ : ∃ g : Finset (Fin Λ.k) ⊕ Finset (Fin Λ.k) → SampleObservable Λ,
      g = Sum.elim (bottomProduct c) responseProduct := ⟨_, rfl⟩
  have hgm : ∀ j, TranslatedLaws.HasBoundedMoments (sampleFamily rule (fun i => Sq₁ (φ i)) p (g j)) := by
    rintro (B | B)
    · rw [hg]
      exact (hfam₂ c B).1
    · rw [hg]
      exact (hfam₂ c B).2
  obtain ⟨sub, P, hsub, hP⟩ := hE (translatedTori (fun i => Sq₁ (φ i)) p) (Finset (Fin Λ.k) ⊕ Finset (Fin Λ.k))
    (fun j => sampleFamily rule (fun i => Sq₁ (φ i)) p (g j)) hkeep₂ hgm
  have hms₃ : StrictMono fun i => ms₀ (φ (sub i) + m₀) := fun i j hij => hms₂ (hsub hij)
  obtain ⟨-, hfam₃⟩ := hmom rule (fun i => ms₀ (φ (sub i) + m₀)) (fun i => Sq₁ (φ (sub i))) p hrule hp hms₃
    (fun i => hSq₁ (φ (sub i)))
  let F : LimitLawAtPoint S :=
    { rule := rule, rule_admissible := hrule, period := p, one_le_period := hp,
      exponents := fun i => ms₀ (φ (sub i) + m₀), strictMono_exponents := hms₃,
      points := fun i => Sq₁ (φ (sub i)), points_eq := fun i => hSq₁ (φ (sub i)),
      Index := Finset (Fin Λ.k) ⊕ Finset (Fin Λ.k), countable_index := inferInstance, observables := g,
      hasBoundedMoments := by
        rintro (B | B)
        · rw [hg]
          exact (hfam₃ c B).1
        · rw [hg]
          exact (hfam₃ c B).2
      law := P, isJointLimitLaw := hP }
  have hFlim : IsTorusLimitAlong Λ.stepParams.side K S.β ν F.exponents := by
    refine ⟨fun i => hνpos _, hms₃, fun A hA => (hνlim A hA).comp ?_⟩
    have h1 : StrictMono fun i => φ (sub i) + m₀ := fun i j hij => by
      have := hφ (hsub hij)
      show φ (sub i) + m₀ < φ (sub j) + m₀
      omega
    exact h1.tendsto_atTop
  have hcF : ∀ l, Tendsto (fun m => (F.points m).kappaAtLast l) atTop (𝓝 (c l)) := fun l =>
    (hcl l).comp hsub.tendsto_atTop
  have hgl : ∀ B, F.observables (Sum.inl B) = bottomProduct c B := fun B => by
    show g (Sum.inl B) = _
    rw [hg]
    rfl
  have hgr : ∀ B, F.observables (Sum.inr B) = responseProduct B := fun B => by
    show g (Sum.inr B) = _
    rw [hg]
    rfl
  obtain ⟨Cf, hCf⟩ : ∃ Cf, Cf = |C₄ ⌈X₀⌉₊| + |C₅| + N + |C₆| := ⟨_, rfl⟩
  have hsmall : S.scaleCoupling ≤ X₀ → ∀ᵐ U ∂ν, ∀ B : Finset (Fin Λ.k), |S.centredStateMoment (κ U) c B| ≤ Cf := by
    intro hs
    rw [ae_all_iff]
    intro B
    have h1 := (h41 S F c hcF B (Sum.inl B) (Sum.inr B) (hgl B) (hgr B)).2 ⌈X₀⌉₊ (hs.trans (Nat.le_ceil _))
    have h2 : ∀ᵐ v ∂F.law, -Cf ≤ F.condMeanAt (Sum.inl B) v ∧ F.condMeanAt (Sum.inl B) v ≤ Cf := by
      filter_upwards [h1] with v hv
      have h3 : |C₄ ⌈X₀⌉₊| ≤ Cf := by
        rw [hCf]
        linarith [abs_nonneg C₅, abs_nonneg C₆]
      exact abs_le.mp (hv.trans ((le_abs_self _).trans h3))
    filter_upwards [hR S F K ν κ c B (Sum.inl B) _ _ hK hFlim hκ (hgl B) h2] with U hU
    exact abs_le.mpr hU
  have hlarge : X₀ ≤ S.scaleCoupling → ∀ᵐ U ∂ν, ∀ B : Finset (Fin Λ.k),
      |S.scaleCoupling ^ B.card * S.centredStateMoment (κ U) c B - e B| ≤
      C₅ * (S.range : ℝ) ^ (4 * B.card + 3) * S.scaleCoupling ^ (-(1 / 2) + 1 / 1000 : ℝ) +
        S.scaleCoupling ^ B.card * Real.exp (-(S.scaleCoupling ^ ((1 : ℝ) / 200))) := by
    intro hl
    have hx1 : 1 ≤ S.scaleCoupling := hX₁.trans hl
    have hx0 : 0 < S.scaleCoupling := by linarith
    rw [ae_all_iff]
    intro B
    have hxb : 0 < S.scaleCoupling ^ B.card := pow_pos hx0 _
    have h1 := (h41 S F c hcF B (Sum.inl B) (Sum.inr B) (hgl B) (hgr B)).1 (hX₄.trans hl)
    have hEt : Tendsto (fun m => ∫ X, ∏ i ∈ B, (F.points m).halfForm (d (φ (sub m))) ((F.points m).data.period Λ.stepParams.side) i X
        ∂(μ (φ (sub m)))) atTop (𝓝 (e B)) :=
      (((hel hl B).comp hsub.tendsto_atTop).congr fun m => hEG _ _)
    have h2 := h51 S F (fun m => d (φ (sub m))) (fun m => μ (φ (sub m))) (fun m => hd _) (fun m => hμ _) B (e B) hEt
      (Sum.inr B) (hgr B) (hX₅.trans hl)
    obtain ⟨bd, hbd⟩ : ∃ bd, bd = C₅ * (S.range : ℝ) ^ (4 * B.card + 3) * S.scaleCoupling ^ (-(1 / 2) + 1 / 1000 : ℝ) +
      S.scaleCoupling ^ B.card * Real.exp (-(S.scaleCoupling ^ ((1 : ℝ) / 200))) := ⟨_, rfl⟩
    have h3 : ∀ᵐ v ∂F.law, (e B - bd) / S.scaleCoupling ^ B.card ≤ F.condMeanAt (Sum.inl B) v ∧
        F.condMeanAt (Sum.inl B) v ≤ (e B + bd) / S.scaleCoupling ^ B.card := by
      filter_upwards [h1, h2] with v hv1 hv2
      have h4 : |S.scaleCoupling ^ B.card * F.condMeanAt (Sum.inl B) v - e B| ≤ bd := by
        have h5 : S.scaleCoupling ^ B.card * F.condMeanAt (Sum.inl B) v - e B =
            (S.scaleCoupling ^ B.card * F.condMeanAt (Sum.inr B) v - e B) +
              S.scaleCoupling ^ B.card * (F.condMeanAt (Sum.inl B) v - F.condMeanAt (Sum.inr B) v) := by ring
        rw [h5, hbd]
        refine (abs_add_le _ _).trans (add_le_add hv2 ?_)
        rw [abs_mul, abs_of_pos hxb]
        exact mul_le_mul_of_nonneg_left hv1 hxb.le
      have h6 := abs_le.mp h4
      rw [div_le_iff₀ hxb, le_div_iff₀ hxb]
      constructor <;> linarith [h6.1, h6.2]
    filter_upwards [hR S F K ν κ c B (Sum.inl B) _ _ hK hFlim hκ (hgl B) h3] with U hU
    obtain ⟨hU1, hU2⟩ := hU
    rw [div_le_iff₀ hxb] at hU1
    rw [le_div_iff₀ hxb] at hU2
    rw [← hbd, abs_le]
    constructor <;> linarith
  refine ⟨c, ?_⟩
  have hboth : ∀ᵐ U ∂ν, (S.scaleCoupling ≤ X₀ → ∀ B : Finset (Fin Λ.k), |S.centredStateMoment (κ U) c B| ≤ Cf) ∧
      (X₀ ≤ S.scaleCoupling → ∀ B : Finset (Fin Λ.k), |S.scaleCoupling ^ B.card * S.centredStateMoment (κ U) c B - e B| ≤
        C₅ * (S.range : ℝ) ^ (4 * B.card + 3) * S.scaleCoupling ^ (-(1 / 2) + 1 / 1000 : ℝ) +
          S.scaleCoupling ^ B.card * Real.exp (-(S.scaleCoupling ^ ((1 : ℝ) / 200)))) := by
    by_cases h1 : S.scaleCoupling ≤ X₀ <;> by_cases h2 : X₀ ≤ S.scaleCoupling
    · filter_upwards [hsmall h1, hlarge h2] with U a1 a2
      exact ⟨fun _ => a1, fun _ => a2⟩
    · filter_upwards [hsmall h1] with U a1
      exact ⟨fun _ => a1, fun h => absurd h h2⟩
    · filter_upwards [hlarge h2] with U a2
      exact ⟨fun h => absurd h h1, fun _ => a2⟩
    · exact absurd (le_total _ _) (by tauto)
  filter_upwards [hboth] with U hU
  rw [← hCf]
  refine ⟨hU.1, fun hl δ hδ => ?_⟩
  have hx1 : 1 ≤ S.scaleCoupling := hX₁.trans hl
  have hx0 : 0 < S.scaleCoupling := by linarith
  have hev : ∀ᶠ i in atTop, ∀ B : Finset (Fin Λ.k), |EG (φ i) B - e B| < δ := by
    rw [eventually_all]
    intro B
    have := (Metric.tendsto_nhds.mp (hel hl B)) δ hδ
    filter_upwards [this] with i hi
    rwa [Real.dist_eq] at hi
  obtain ⟨i, hi⟩ := hev.exists
  refine ⟨Sq₁ (φ i), d (φ i), hd _, μ (φ i), hside _, hμ _, fun B => ⟨?_, ?_⟩⟩
  · rw [← hEG]
    have h1 := hU.2 hl B
    have h2 := hi B
    have hr1 : (1 : ℝ) ≤ (S.range : ℝ) := by
      have h3 : 1 ≤ S.scaleCoupling ^ ((1 : ℝ) / 100) := Real.one_le_rpow hx1 (by norm_num)
      have h4 : S.scaleCoupling ^ ((1 : ℝ) / 100) ≤ (S.range : ℝ) := Nat.le_ceil _
      linarith
    have hbk : B.card ≤ 8 := by
      have := Finset.card_le_univ B
      simp only [Fintype.card_fin] at this
      omega
    have hpe' := hpe S.scaleCoupling hx1 B.card hbk
    obtain ⟨e₀, he₀⟩ : ∃ e₀, e₀ = S.scaleCoupling ^ (-(1 / 2) + 1 / 1000 : ℝ) := ⟨_, rfl⟩
    have he₀0 : 0 < e₀ := he₀ ▸ Real.rpow_pos_of_pos hx0 _
    obtain ⟨R', hR'⟩ : ∃ R', R' = (S.range : ℝ) ^ (4 * B.card + 3) := ⟨_, rfl⟩
    have hR'1 : 1 ≤ R' := hR' ▸ one_le_pow₀ hr1
    have hhalf : S.scaleCoupling ^ (-(1 / 2) : ℝ) ≤ e₀ := by
      rw [he₀]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rw [← he₀, ← hR'] at h1 ⊢
    have hNe : N * S.scaleCoupling ^ (-(1 / 2) : ℝ) ≤ N * (R' * e₀) := by
      refine mul_le_mul_of_nonneg_left (hhalf.trans ?_) hN0
      exact le_mul_of_one_le_left he₀0.le hR'1
    have hC5 : C₅ * R' * e₀ ≤ |C₅| * (R' * e₀) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have hCf' : (|C₅| + N) * (R' * e₀) ≤ Cf * (R' * e₀) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [hCf]
      linarith [abs_nonneg (C₄ ⌈X₀⌉₊), abs_nonneg C₆]
    have htri : |S.scaleCoupling ^ B.card * S.centredStateMoment (κ U) c B - EG (φ i) B| ≤
        |S.scaleCoupling ^ B.card * S.centredStateMoment (κ U) c B - e B| + |EG (φ i) B - e B| := by
      have := abs_sub_le (S.scaleCoupling ^ B.card * S.centredStateMoment (κ U) c B) (e B) (EG (φ i) B)
      rwa [abs_sub_comm (e B)] at this
    have hfin : Cf * R' * e₀ = Cf * (R' * e₀) := by ring
    rw [hfin]
    have h7 : (|C₅| + N) * (R' * e₀) = |C₅| * (R' * e₀) + N * (R' * e₀) := by ring
    linarith
  · rw [← hEG]
    refine (hEGb hl _ B).trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (pow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg hx0.le _)
    rw [hCf]
    linarith [le_abs_self C₆, abs_nonneg (C₄ ⌈X₀⌉₊), abs_nonneg C₅]
end LimitLaw
theorem componentMomentStatement_holds (hE : exists_jointLimitLaw_statement) (hR : componentsReadLimitLawStatement)
    (h41 : lastSeparatedLevelMomentStatement) (h51 : limitResponseMomentStatement)
    (hPL : largerToriStatement) (hMG : gaussianChainMomentsStatement) (hG : levelChainCanonicalGaussianStatement) :
    componentMomentStatement := by
  unfold gaussianChainMomentsStatement ForAllHullPoints at hMG
  have h := forAllHullParameters_and hR (forAllHullParameters_and h41 (forAllHullParameters_and h51
    (forAllHullParameters_and hPL hMG)))
  refine forAllHullParameters_mono h fun Λ hk2 hk8 hapos hh => ?_
  obtain ⟨hR, ⟨C₄, X₄, -, h41⟩, ⟨C₅, X₅, -, h51⟩, hPL, ⟨C₆, c₆, X₆, -, -, hMG⟩⟩ := hh
  obtain ⟨N, hN0, hpe⟩ : ∃ N : ℝ, 0 ≤ N ∧ ∀ (x : ℝ), 1 ≤ x → ∀ b : ℕ, b ≤ 8 →
      x ^ b * Real.exp (-(x ^ ((1 : ℝ) / 200))) ≤ N * x ^ (-(1 / 2) : ℝ) :=
    ⟨_, Nat.cast_nonneg _, fun x hx b hb => pow_mul_exp_neg_rpow_le hx hb⟩
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, X₀ = max 1 (max X₄ (max X₅ X₆)) := ⟨_, rfl⟩
  have hX₁ : 1 ≤ X₀ := hX₀ ▸ le_max_left _ _
  have hX₄ : X₄ ≤ X₀ := hX₀ ▸ (le_max_left _ _).trans (le_max_right _ _)
  have hX₅ : X₅ ≤ X₀ := hX₀ ▸ (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hX₆ : X₆ ≤ X₀ := hX₀ ▸ (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨|C₄ ⌈X₀⌉₊| + |C₅| + N + |C₆ 1|, X₀, hX₁, ?_⟩
  intro K β hβ hKp ν hν p hp κ hκ S hK hβS
  obtain ⟨ms, hms⟩ := hν
  have hms' : IsTorusLimitAlong Λ.stepParams.side K S.β ν ms := by
    rw [hβS]
    exact hms
  exact moment_bounds_at_point hE hR hN0 hpe h41 h51 hPL (fun S hx d hd μ hμ B => (hMG S hx d hd μ hμ B).2.2)
    (fun s n _ => hG Λ.stepParams.side Λ.stepParams.coupling hapos s n) hk8 hX₁ hX₄ hX₅ hX₆ S hK hms' hp hκ
end YangMills.Construction.MomentLaw
end
