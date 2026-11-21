import YangMills.Construction.HullsInEveryVolume.ClassesOfAHullAreShort
import YangMills.Construction.HullsInEveryVolume.LocalHullLiesInTheHull
import YangMills.Construction.HullsInEveryVolume.MomentOfTheLocalHull
import YangMills.Construction.HullsInEveryVolume.MomentsOfTheSizesOfAHull
import YangMills.Construction.HullsInEveryVolume.NoisesCarryTheChain
import YangMills.Construction.HullsInEveryVolume.RatesOfTheMomentsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
open TorusFields TorusLumps StepSettings RenormalizationStepParameters StepReturn WeightedResponses ResponseInTheExpansion
section Numerics
private theorem dyadic_sum_bound (c E Lr : ℝ) (hc : 0 < c) (hE : 0 ≤ E) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (x r : ℝ) (k N : ℕ), 1 ≤ x → 1 ≤ r → r ≤ 2 * x → 1 ≤ k →
      ∑ i ∈ Finset.range N, (16 * (k : ℝ) * (4 * 56 ^ 4 * Lr ^ 4 * r ^ 4 * ((2 : ℝ) ^ i) ^ 4)) ^ k *
          Real.exp (E * Real.log x) * Real.exp (-(3 / 8 * (c * x)) - c * x / 8 * 2 ^ i) ≤
        C ^ k * (k.factorial : ℝ) ^ 6 * Real.exp (-(c * x / 4)) := by apply _root_.YangMills.SharedProofs.p100659 <;> assumption
end Numerics
section Holder
variable {Ω : Type} [MeasurableSpace Ω]
private theorem integral_mul_indicator_le (μ : Measure Ω) [IsProbabilityMeasure μ] {φ ψ : Ω → ℝ} (hm : Measurable φ)
    (h0 : ∀ w, 0 ≤ φ w) {B : ℝ} (hB : ∀ w, φ w ≤ B) {A : Set Ω} (hA : MeasurableSet A) {p k : ℕ}
    (hp : 2 ≤ p) (hψ : ∀ w, φ w ^ p = ψ w) {E₀ lx Λ t : ℝ} (hlx : 0 ≤ lx) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ p)
    (hmom : ∫ w, ψ w ∂μ ≤ 16 ^ (k * p) * ((k * p).factorial : ℝ) * Real.exp (E₀ * lx * Λ))
    (hP : μ.real A ≤ Real.exp (-t)) (ht : 0 ≤ t) :
    ∫ w, φ w * A.indicator (1 : Ω → ℝ) w ∂μ ≤
      (16 * (k : ℝ) * p) ^ k * Real.exp (|E₀| * lx) * Real.exp (-(t / 2)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0 : ℝ) < p := by linarith
  have hc := Real.HolderConjugate.conjExponent hp1
  set q : ℝ := Real.conjExponent p with hq
  have hq0 : 0 < q := hc.symm.pos
  have hg0 : ∀ w, 0 ≤ A.indicator (1 : Ω → ℝ) w := fun w =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) w
  have hg1 : ∀ w, A.indicator (1 : Ω → ℝ) w ≤ 1 := fun w => by
    by_cases hw : w ∈ A <;> simp [hw]
  have hgm : Measurable (A.indicator (1 : Ω → ℝ)) := measurable_const.indicator hA
  have hmem1 : MemLp φ (ENNReal.ofReal p) μ :=
    MemLp.of_bound hm.aestronglyMeasurable B (ae_of_all _ fun w => by
      rw [Real.norm_of_nonneg (h0 w)]
      exact hB w)
  have hmem2 : MemLp (A.indicator (1 : Ω → ℝ)) (ENNReal.ofReal q) μ :=
    MemLp.of_bound hgm.aestronglyMeasurable 1 (ae_of_all _ fun w => by
      rw [Real.norm_of_nonneg (hg0 w)]
      exact hg1 w)
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hc (ae_of_all _ h0) (ae_of_all _ hg0) hmem1 hmem2
  have e1 : ∫ w, φ w ^ (p : ℝ) ∂μ = ∫ w, ψ w ∂μ := by
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    show φ w ^ (p : ℝ) = ψ w
    rw [Real.rpow_natCast, hψ]
  have e2 : ∫ w, A.indicator (1 : Ω → ℝ) w ^ q ∂μ = μ.real A := by
    have e : (fun w => A.indicator (1 : Ω → ℝ) w ^ q) = A.indicator (1 : Ω → ℝ) := by
      funext w
      by_cases hw : w ∈ A
      · simp [hw]
      · simp [hw, Real.zero_rpow hq0.ne']
    rw [e]
    exact integral_indicator_one hA
  rw [e1, e2] at hH
  refine hH.trans ?_
  have hψ0 : 0 ≤ ∫ w, ψ w ∂μ := integral_nonneg fun w => by
    show 0 ≤ ψ w
    rw [← hψ w]
    exact pow_nonneg (h0 w) p
  set A₁ : ℝ := (16 * (k : ℝ) * p) ^ k * Real.exp (|E₀| * lx) with hA₁
  have hA₁0 : 0 ≤ A₁ := by positivity
  have hmomA : ∫ w, ψ w ∂μ ≤ A₁ ^ p := by
    refine hmom.trans ?_
    have hf : ((k * p).factorial : ℝ) ≤ ((k : ℝ) * p) ^ (k * p) := by
      have := Nat.factorial_le_pow (k * p)
      exact_mod_cast this
    have he : Real.exp (E₀ * lx * Λ) ≤ Real.exp (|E₀| * lx) ^ p := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have h1 : E₀ * lx * Λ ≤ |E₀| * lx * Λ := by
        have := le_abs_self E₀
        gcongr
      have h2 : |E₀| * lx * Λ ≤ |E₀| * lx * p := by
        gcongr
      linarith
    calc (16 : ℝ) ^ (k * p) * ((k * p).factorial : ℝ) * Real.exp (E₀ * lx * Λ)
        ≤ (16 : ℝ) ^ (k * p) * ((k : ℝ) * p) ^ (k * p) * Real.exp (|E₀| * lx) ^ p := by gcongr
      _ = A₁ ^ p := by
        rw [hA₁, mul_pow _ (Real.exp (|E₀| * lx)) p, ← pow_mul, mul_assoc (16 : ℝ) (k : ℝ) (p : ℝ),
          mul_pow (16 : ℝ) ((k : ℝ) * p) (k * p)]
  have hfirst : (∫ w, ψ w ∂μ) ^ (1 / (p : ℝ)) ≤ A₁ := by
    calc (∫ w, ψ w ∂μ) ^ (1 / (p : ℝ)) ≤ (A₁ ^ p) ^ (1 / (p : ℝ)) :=
          Real.rpow_le_rpow hψ0 hmomA (by positivity)
      _ = A₁ := by
        rw [one_div]
        exact Real.pow_rpow_inv_natCast hA₁0 (by omega)
  have hqi : 1 / 2 ≤ 1 / q := by
    have h := hc.inv_add_inv_eq_one
    have h2 : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ hp0 (by norm_num)]
      norm_num
      exact_mod_cast hp
    rw [one_div q]
    linarith
  have hsecond : (μ.real A) ^ (1 / q) ≤ Real.exp (-(t / 2)) := by
    calc (μ.real A) ^ (1 / q) ≤ (Real.exp (-t)) ^ (1 / q) :=
          Real.rpow_le_rpow measureReal_nonneg hP (by positivity)
      _ = Real.exp (-t * (1 / q)) := (Real.exp_mul _ _).symm
      _ ≤ Real.exp (-(t / 2)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  calc (∫ w, ψ w ∂μ) ^ (1 / (p : ℝ)) * (μ.real A) ^ (1 / q)
      ≤ A₁ * Real.exp (-(t / 2)) := by
        gcongr
    _ = _ := by rw [hA₁]
end Holder
section Fibres
variable {X : Type} [MeasurableSpace X]
private theorem measurableSet_setOf_comp {A : Type} [Countable A] {f : X → A} (h : ∀ a, MeasurableSet {x | f x = a})
    (P : A → Prop) : MeasurableSet {x | P (f x)} := by apply _root_.YangMills.SharedProofs.p67002 <;> assumption
private theorem measurableSet_sigma_fst_eq {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    MeasurableSet {z : Sigma β | z.1 = a} := by apply _root_.YangMills.SharedProofs.p1937 <;> assumption
end Fibres
section LocalHullData
variable {ℓ : StepParameters} (T : StageTower ℓ) (s₁ : ℝ)
open Classical in
private theorem measurableSet_localHullData_fst_eq (hC : ∀ (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)),
      MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    (hq : ∀ (n : ℕ) [NeZero n], Measurable (stageState T 0 n)) (j : ℕ) :
    ∀ (n : ℕ) [NeZero n] (Q a : Finset (TorusSite n)),
      MeasurableSet {w : MarkedSample ℓ j n | (localHullData T s₁ j n w Q).1 = a} := by apply _root_.YangMills.Construction.HullMeans.measurableSet_localHullData_fst_eq <;> assumption
open Classical in
private theorem measurable_localHullData_snd (hC : ∀ (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)),
      MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    (hq : ∀ (n : ℕ) [NeZero n], Measurable (stageState T 0 n)) (j : ℕ) :
    ∀ (n : ℕ) [NeZero n] (Q : Finset (TorusSite n)) (y : TorusSite n),
      Measurable fun w : MarkedSample ℓ j n => (localHullData T s₁ j n w Q).2 y := by apply _root_.YangMills.Construction.HullMeans.measurable_localHullData_snd <;> assumption
private theorem localHullData_snd_nonneg (hs : 0 ≤ s₁) (j : ℕ) :
    ∀ (n : ℕ) [NeZero n] (w : MarkedSample ℓ j n) (Q : Finset (TorusSite n)) (y : TorusSite n),
      0 ≤ (localHullData T s₁ j n w Q).2 y := by
  induction j with
  | zero =>
    intro n _ w Q y
    exact le_rfl
  | succ j ih =>
    intro n _ w Q y
    simp only [localHullData]
    split_ifs
    · exact add_nonneg hs (Finset.sum_nonneg fun z _ => ih _ _ _ _)
    · exact hs
    · exact le_rfl
private theorem localHullData_snd_bounded (j : ℕ) :
    ∀ (n : ℕ) [NeZero n], ∃ B : ℝ, 0 ≤ B ∧ ∀ (w : MarkedSample ℓ j n) (Q : Finset (TorusSite n)) (y : TorusSite n),
      |(localHullData T s₁ j n w Q).2 y| ≤ B := by
  classical
  induction j with
  | zero =>
    intro n _
    exact ⟨0, le_rfl, fun w Q y => by simp [localHullData]⟩
  | succ j ih =>
    intro n _
    obtain ⟨B, hB0, hB⟩ := ih (n * ℓ.side)
    refine ⟨|s₁| + (Fintype.card (TorusSite (n * ℓ.side)) : ℝ) * B, by positivity, fun w Q y => ?_⟩
    simp only [localHullData]
    have hcard : ∀ S : Finset (TorusSite (n * ℓ.side)), ∀ f : TorusSite (n * ℓ.side) → ℝ, (∀ z, |f z| ≤ B) →
        |∑ z ∈ S, f z| ≤ (Fintype.card (TorusSite (n * ℓ.side)) : ℝ) * B := by
      intro S f hf
      calc |∑ z ∈ S, f z| ≤ ∑ z ∈ S, |f z| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _z ∈ S, B := Finset.sum_le_sum fun z _ => hf z
        _ = (S.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := by
          gcongr
          exact Finset.card_le_univ S
    split_ifs
    · exact (abs_add_le _ _).trans (by gcongr; exact hcard _ _ fun z => hB _ _ z)
    · have : 0 ≤ (Fintype.card (TorusSite (n * ℓ.side)) : ℝ) * B := by positivity
      linarith
    · rw [abs_zero]
      positivity
end LocalHullData
section SiteMoments
variable {ℓ : StepParameters} (T : StageTower ℓ) (s₁ : ℝ) (u n : ℕ) [NeZero n]
private theorem localScoreMoment_nonneg (hs : 0 ≤ s₁) (y : TorusSite n) (D : ℝ) (k : ℕ) (w : MarkedSample ℓ u n) :
    0 ≤ localScoreMoment T s₁ u n y D k w := by
  unfold localScoreMoment
  split_ifs
  · exact pow_nonneg (localHullData_snd_nonneg T s₁ hs u n w _ y) k
  · exact le_rfl
private theorem localScoreMoment_pow (y : TorusSite n) (D : ℝ) (k p : ℕ) (hp : p ≠ 0) (w : MarkedSample ℓ u n) :
    localScoreMoment T s₁ u n y D k w ^ p = localScoreMoment T s₁ u n y D (k * p) w := by
  unfold localScoreMoment
  split_ifs
  · rw [← pow_mul]
  · exact zero_pow hp
open Classical in
private theorem measurable_localScoreMoment (hC : ∀ (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)),
      MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    (hq : ∀ (n : ℕ) [NeZero n], Measurable (stageState T 0 n)) (y : TorusSite n) (D : ℝ) (k : ℕ) :
    Measurable (localScoreMoment T s₁ u n y D k) := by
  show Measurable fun w => if y ∈ (localHullData T s₁ u n w (localHullBox T u y D)).1 then
    ((localHullData T s₁ u n w (localHullBox T u y D)).2 y) ^ k else 0
  exact Measurable.ite (measurableSet_setOf_comp
      (measurableSet_localHullData_fst_eq T s₁ hC hq u n (localHullBox T u y D)) (fun Y => y ∈ Y))
    ((measurable_localHullData_snd T s₁ hC hq u n _ y).pow_const k) measurable_const
private theorem localScoreMoment_bounded (hs : 0 ≤ s₁) (y : TorusSite n) (D : ℝ) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : MarkedSample ℓ u n, localScoreMoment T s₁ u n y D k w ≤ B := by
  obtain ⟨B, hB0, hB⟩ := localHullData_snd_bounded (ℓ := ℓ) T s₁ u n
  refine ⟨B ^ k, by positivity, fun w => ?_⟩
  unfold localScoreMoment
  split_ifs
  · exact pow_le_pow_left₀ (localHullData_snd_nonneg T s₁ hs u n w _ y) ((le_abs_self _).trans (hB w _ y)) k
  · positivity
private def dyadicLower (r : ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => 2 ^ i * r
private theorem dyadicLower_nonneg {r : ℝ} (hr : 0 ≤ r) (i : ℕ) : 0 ≤ dyadicLower r i := by
  cases i with
  | zero => exact le_rfl
  | succ i => exact mul_nonneg (by positivity) hr
private theorem supDiam_le_sup (X : Finset (TorusSite n)) :
    supDiam X ≤ Finset.univ.sup fun a : TorusSite n => Finset.univ.sup fun b : TorusSite n => supDist a b :=
  Finset.sup_le fun a _ => Finset.sup_le fun b _ =>
    (Finset.le_sup (f := fun b : TorusSite n => supDist a b) (Finset.mem_univ b)).trans
      (Finset.le_sup (f := fun a : TorusSite n => Finset.univ.sup fun b : TorusSite n => supDist a b) (Finset.mem_univ a))
private theorem exists_dyadic_scale {r : ℝ} (hr : 1 ≤ r) (d : ℕ) :
    ∃ i ≤ d, (d : ℝ) < 2 ^ i * r ∧ dyadicLower r i ≤ d := by
  classical
  have hd : (d : ℝ) < 2 ^ d * r := by
    have h1 : (d : ℝ) < 2 ^ d := by exact_mod_cast Nat.lt_two_pow_self
    nlinarith
  have hex : ∃ i : ℕ, (d : ℝ) < 2 ^ i * r := ⟨d, hd⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hd, Nat.find_spec hex, ?_⟩
  have key : ∀ i : ℕ, (∀ j < i, ¬ (d : ℝ) < 2 ^ j * r) → dyadicLower r i ≤ d := by
    intro i h
    cases i with
    | zero => exact Nat.cast_nonneg d
    | succ j => exact not_lt.mp (h j (Nat.lt_succ_self j))
  exact key _ fun j hj => Nat.find_min hex hj
open Classical in
private theorem siteSize_moment_at_stage (β : ℝ) [IsProbabilityMeasure (markedSampleLaw T β u n)] (hs : 0 ≤ s₁)
    (hC : ∀ (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)),
      MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    (hq : ∀ (n : ℕ) [NeZero n], Measurable (stageState T 0 n)) (hqu : Measurable (stageState T u n))
    (z : TorusSite n) {c E₀ Lr C : ℝ} (hc : 0 < c) (hL : 1 ≤ Lr)
    (hCs : ∀ (x r : ℝ) (k N : ℕ), 1 ≤ x → 1 ≤ r → r ≤ 2 * x → 1 ≤ k →
      ∑ i ∈ Finset.range N, (16 * (k : ℝ) * (4 * 56 ^ 4 * Lr ^ 4 * r ^ 4 * ((2 : ℝ) ^ i) ^ 4)) ^ k *
          Real.exp (|E₀| * Real.log x) * Real.exp (-(3 / 8 * (c * x)) - c * x / 8 * 2 ^ i) ≤
        C ^ k * (k.factorial : ℝ) ^ 6 * Real.exp (-(c * x / 4)))
    (hx : 1 ≤ stageCoupling T u) (hr : (1 : ℝ) ≤ (stageRange T u : ℝ))
    (hrx : (stageRange T u : ℝ) ≤ 2 * stageCoupling T u)
    (hloc : ∀ (w : MarkedSample ℓ u n) (D : ℝ), 0 < D → z ∈ hullSet T u n w →
      ((supDiam (hullClass (stageRange T u) (hullSet T u n w) z) : ℕ) : ℝ) < D →
      z ∈ (localHullData T s₁ u n w (localHullBox T u z D)).1 ∧
        (localHullData T s₁ u n w (localHullBox T u z D)).2 z = siteSize T s₁ u n w z)
    (hcl : ∀ D : ℝ, 0 ≤ D → (markedSampleLaw T β u n).real {w | z ∈ hullSet T u n w ∧
        D ≤ (supDiam (hullClass (stageRange T u) (hullSet T u n w) z) : ℝ)} ≤
      Real.exp (-(c * stageCoupling T u * (1 + D / (stageRange T u : ℝ)))))
    (hmom : ∀ (D : ℝ) (k : ℕ), 0 < D → 1 ≤ k →
      ∫ w, localScoreMoment T s₁ u n z D k w ∂(markedSampleLaw T β u n) ≤
        16 ^ k * (k.factorial : ℝ) * Real.exp (E₀ * Real.log (stageCoupling T u) *
          (Lr * (16 * D + 40 * (stageRange T u : ℝ))) ^ 4))
    (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun w => siteSize T s₁ u n w z ^ k) (markedSampleLaw T β u n) ∧
      ∫ w, siteSize T s₁ u n w z ^ k ∂(markedSampleLaw T β u n) ≤
        C ^ k * (k.factorial : ℝ) ^ 6 * Real.exp (-(c * stageCoupling T u / 4)) := by
  set μ := markedSampleLaw T β u n with hμ
  set x : ℝ := stageCoupling T u with hxd
  set r : ℝ := (stageRange T u : ℝ) with hrd
  have hr0 : 0 < r := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  set Dm : ℕ := Finset.univ.sup fun a : TorusSite n => Finset.univ.sup fun b : TorusSite n => supDist a b with hDm
  have hY : ∀ b : Finset (TorusSite n), MeasurableSet {w : MarkedSample ℓ u n | hullSet T u n w = b} := by
    intro b
    have h : MeasurableSet {q : StageState T u n | q.2.1 = b} := measurable_snd (measurableSet_sigma_fst_eq b)
    exact hqu h
  have hsz : ∀ w, siteSize T s₁ u n w z = if z ∈ hullSet T u n w then
      (localHullData T s₁ u n w (localHullBox T u z ((Dm : ℝ) + 1))).2 z else 0 := by
    intro w
    by_cases h : z ∈ hullSet T u n w
    · rw [if_pos h]
      refine ((hloc w _ (by positivity) h ?_).2).symm
      have h1 : ((supDiam (hullClass (stageRange T u) (hullSet T u n w) z) : ℕ) : ℝ) ≤ Dm := by
        exact_mod_cast supDiam_le_sup n _
      linarith
    · rw [if_neg h]
      exact dif_neg h
  have hsm : Measurable fun w => siteSize T s₁ u n w z := by
    have e : (fun w => siteSize T s₁ u n w z) = fun w => if z ∈ hullSet T u n w then
        (localHullData T s₁ u n w (localHullBox T u z ((Dm : ℝ) + 1))).2 z else 0 := funext hsz
    rw [e]
    exact Measurable.ite (measurableSet_setOf_comp hY fun Y => z ∈ Y)
      (measurable_localHullData_snd T s₁ hC hq u n _ z) measurable_const
  obtain ⟨Bs, hBs0, hBs⟩ := localHullData_snd_bounded (ℓ := ℓ) T s₁ u n
  have hsb : ∀ w, |siteSize T s₁ u n w z| ≤ Bs := by
    intro w
    rw [hsz w]
    split_ifs
    · exact hBs w _ z
    · simpa using hBs0
  have hint : Integrable (fun w => siteSize T s₁ u n w z ^ k) μ :=
    Integrable.of_bound (hsm.pow_const k).aestronglyMeasurable (Bs ^ k) (ae_of_all _ fun w => by
      rw [norm_pow, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hsb w) k)
  refine ⟨hint, ?_⟩
  set Φ : ℕ → ℕ → MarkedSample ℓ u n → ℝ := fun i m => localScoreMoment T s₁ u n z (2 ^ i * r) m with hΦ
  set S : ℕ → Set (MarkedSample ℓ u n) := fun i => {w | z ∈ hullSet T u n w ∧
    dyadicLower r i ≤ (supDiam (hullClass (stageRange T u) (hullSet T u n w) z) : ℝ)} with hS
  have hSm : ∀ i, MeasurableSet (S i) := fun i =>
    measurableSet_setOf_comp hY fun Y => z ∈ Y ∧ dyadicLower r i ≤ (supDiam (hullClass (stageRange T u) Y z) : ℝ)
  have hSP : ∀ i, μ.real (S i) ≤ Real.exp (-(c * x * (1 + dyadicLower r i / r))) := fun i =>
    hcl _ (dyadicLower_nonneg hr0.le i)
  have hΦ0 : ∀ i m w, 0 ≤ Φ i m w := fun i m w => localScoreMoment_nonneg T s₁ u n hs z _ m w
  have hΦm : ∀ i m, Measurable (Φ i m) := fun i m => measurable_localScoreMoment T s₁ u n hC hq z _ m
  have hind0 : ∀ (A : Set (MarkedSample ℓ u n)) w, 0 ≤ A.indicator (1 : MarkedSample ℓ u n → ℝ) w := fun A w =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) w
  have hind1 : ∀ (A : Set (MarkedSample ℓ u n)) w, A.indicator (1 : MarkedSample ℓ u n → ℝ) w ≤ 1 := fun A w => by
    by_cases hw : w ∈ A <;> simp [hw]
  have hterm : ∀ i, ∫ w, Φ i k w * (S i).indicator (1 : MarkedSample ℓ u n → ℝ) w ∂μ ≤
      (16 * (k : ℝ) * (4 * 56 ^ 4 * Lr ^ 4 * r ^ 4 * ((2 : ℝ) ^ i) ^ 4)) ^ k *
        Real.exp (|E₀| * Real.log x) * Real.exp (-(3 / 8 * (c * x)) - c * x / 8 * 2 ^ i) := by
    intro i
    have h2i : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    set Λ : ℝ := (Lr * (16 * (2 ^ i * r) + 40 * r)) ^ 4 with hΛ
    have hinner : 1 ≤ 16 * (2 ^ i * r) + 40 * r := by nlinarith
    have hΛ1 : 1 ≤ Λ := one_le_pow₀ (one_le_mul_of_one_le_of_one_le hL hinner)
    have hΛ0 : 0 ≤ Λ := by linarith
    set p : ℕ := ⌈Λ⌉₊ + 2 with hp
    have hp2 : 2 ≤ p := by omega
    have hΛp : Λ ≤ p := by
      have := Nat.le_ceil Λ
      rw [hp]
      push_cast
      linarith
    have hpA : (p : ℝ) ≤ 4 * 56 ^ 4 * Lr ^ 4 * r ^ 4 * ((2 : ℝ) ^ i) ^ 4 := by
      have h1 := Nat.ceil_lt_add_one hΛ0
      have h2 : (p : ℝ) ≤ 4 * Λ := by
        rw [hp]
        push_cast
        linarith
      have h3 : Λ ≤ (Lr * (56 * 2 ^ i * r)) ^ 4 := by
        rw [hΛ]
        have : 16 * (2 ^ i * r) + 40 * r ≤ 56 * 2 ^ i * r := by nlinarith
        gcongr
      have h4 : (Lr * (56 * 2 ^ i * r)) ^ 4 = 56 ^ 4 * Lr ^ 4 * r ^ 4 * ((2 : ℝ) ^ i) ^ 4 := by ring
      rw [h4] at h3
      nlinarith
    have hkp : 1 ≤ k * p := Nat.mul_pos hk (by omega)
    have ht : 0 ≤ c * x * (1 + dyadicLower r i / r) := by
      have := div_nonneg (dyadicLower_nonneg hr0.le i) hr0.le
      positivity
    obtain ⟨B, _, hB⟩ := localScoreMoment_bounded T s₁ u n hs z (2 ^ i * r) k
    have h1 := integral_mul_indicator_le μ (φ := Φ i k) (ψ := localScoreMoment T s₁ u n z (2 ^ i * r) (k * p))
      (hΦm i k) (hΦ0 i k) hB (hSm i) (p := p) (k := k) hp2
      (fun w => localScoreMoment_pow T s₁ u n z _ k p (by omega) w)
      (E₀ := E₀) (lx := Real.log x) (Λ := Λ) hlx hΛ0 hΛp (hmom _ (k * p) (by positivity) hkp) (hSP i) ht
    refine h1.trans ?_
    have hcx : 0 < c * x := by positivity
    have ht2 : -(c * x * (1 + dyadicLower r i / r) / 2) ≤ -(3 / 8 * (c * x)) - c * x / 8 * 2 ^ i := by
      cases i with
      | zero =>
        have e : dyadicLower r 0 = 0 := rfl
        rw [e]
        simp only [zero_div, add_zero, pow_zero]
        linarith
      | succ j =>
        have e : dyadicLower r (j + 1) / r = 2 ^ j := by
          show 2 ^ j * r / r = 2 ^ j
          field_simp
        rw [e, pow_succ]
        have h2 : (0 : ℝ) < 2 ^ j := by positivity
        nlinarith [mul_pos hcx h2]
    gcongr
  have hcov : ∀ w, siteSize T s₁ u n w z ^ k ≤
      ∑ i ∈ Finset.range (Dm + 1), Φ i k w * (S i).indicator (1 : MarkedSample ℓ u n → ℝ) w := by
    intro w
    have hnn : ∀ i ∈ Finset.range (Dm + 1), 0 ≤ Φ i k w * (S i).indicator (1 : MarkedSample ℓ u n → ℝ) w :=
      fun i _ => mul_nonneg (hΦ0 i k w) (hind0 _ w)
    by_cases h : z ∈ hullSet T u n w
    · obtain ⟨i, hi, hlt, hge⟩ := exists_dyadic_scale hr (supDiam (hullClass (stageRange T u) (hullSet T u n w) z))
      have hiD : i ∈ Finset.range (Dm + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le (hi.trans (supDiam_le_sup n _)))
      have hwS : w ∈ S i := ⟨h, hge⟩
      have hl := hloc w (2 ^ i * r) (by positivity) h hlt
      have e : siteSize T s₁ u n w z ^ k = Φ i k w * (S i).indicator (1 : MarkedSample ℓ u n → ℝ) w := by
        have e1 : Φ i k w = siteSize T s₁ u n w z ^ k := by
          show localScoreMoment T s₁ u n z (2 ^ i * r) k w = _
          unfold localScoreMoment
          rw [if_pos hl.1, hl.2]
        rw [e1, Set.indicator_of_mem hwS]
        simp
      rw [e]
      exact Finset.single_le_sum hnn hiD
    · have e : siteSize T s₁ u n w z = 0 := by
        rw [hsz w, if_neg h]
      rw [e, zero_pow (by omega)]
      exact Finset.sum_nonneg hnn
  have hpiece : ∀ i, Integrable (fun w => Φ i k w * (S i).indicator (1 : MarkedSample ℓ u n → ℝ) w) μ := by
    intro i
    obtain ⟨B, hB0, hB⟩ := localScoreMoment_bounded T s₁ u n hs z (2 ^ i * r) k
    have hgm : Measurable ((S i).indicator (1 : MarkedSample ℓ u n → ℝ)) := measurable_const.indicator (hSm i)
    refine Integrable.of_bound ((hΦm i k).mul hgm).aestronglyMeasurable B (ae_of_all _ fun w => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hΦ0 i k w) (hind0 _ w))]
    calc Φ i k w * (S i).indicator (1 : MarkedSample ℓ u n → ℝ) w ≤ B * 1 :=
          mul_le_mul (hB w) (hind1 _ w) (hind0 _ w) hB0
      _ = B := mul_one B
  calc ∫ w, siteSize T s₁ u n w z ^ k ∂μ
      ≤ ∫ w, ∑ i ∈ Finset.range (Dm + 1), Φ i k w * (S i).indicator (1 : MarkedSample ℓ u n → ℝ) w ∂μ :=
        integral_mono hint (integrable_finsetSum _ fun i _ => hpiece i) hcov
    _ = ∑ i ∈ Finset.range (Dm + 1), ∫ w, Φ i k w * (S i).indicator (1 : MarkedSample ℓ u n → ℝ) w ∂μ :=
        integral_finsetSum _ fun i _ => hpiece i
    _ ≤ ∑ i ∈ Finset.range (Dm + 1), (16 * (k : ℝ) * (4 * 56 ^ 4 * Lr ^ 4 * r ^ 4 * ((2 : ℝ) ^ i) ^ 4)) ^ k *
          Real.exp (|E₀| * Real.log x) * Real.exp (-(3 / 8 * (c * x)) - c * x / 8 * 2 ^ i) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ ≤ C ^ k * (k.factorial : ℝ) ^ 6 * Real.exp (-(c * x / 4)) := hCs x r k _ hx hr hrx hk
end SiteMoments
section Parameters
private theorem eventuallyInParameters_and {P Q : ParameterAssignment → ResponseParameters → ℝ → Prop}
    (hP : EventuallyInParameters P) (hQ : EventuallyInParameters Q) :
    EventuallyInParameters fun Tb Kr y => P Tb Kr y ∧ Q Tb Kr y := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := hP a ha
  obtain ⟨L₂, r₂, C₂, hr₂, H₂⟩ := hQ a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max C₁ C₂, fun c => lt_min (hr₁ c) (hr₂ c),
    fun L hL hLL Tb hTa hTL hD hC hO hrt hCd => ?_⟩
  obtain ⟨M₁, G₁⟩ := H₁ L hL (le_of_max_le_left hLL) Tb hTa hTL hD hC hO (hrt.trans (min_le_left _ _))
    (le_of_max_le_left hCd)
  obtain ⟨M₂, G₂⟩ := H₂ L hL (le_of_max_le_right hLL) Tb hTa hTL hD hC hO (hrt.trans (min_le_right _ _))
    (le_of_max_le_right hCd)
  refine ⟨max M₁ M₂, fun Kr hM hη hN hF hRs => ?_⟩
  obtain ⟨y₁, F₁⟩ := G₁ Kr (le_of_max_le_left hM) hη hN hF hRs
  obtain ⟨y₂, F₂⟩ := G₂ Kr (le_of_max_le_right hM) hη hN hF hRs
  exact ⟨max y₁ y₂, fun y hy hR hW =>
    ⟨F₁ y (le_of_max_le_left hy) hR hW, F₂ y (le_of_max_le_right hy) hR hW⟩⟩
private theorem y₁_le_couplingFlow_fst {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ)
    (hW : ∀ β : ℝ, ℓ.y₁ ≤ β → HasExpansion ℓ 0 β (wilsonWeight β)) (hB : 0 ≤ ℓ.B) {g β : ℝ} {K : ℕ}
    (hy : ℓ.y₁ ≤ (g ^ 2)⁻¹) (hβ : windowUpper ℓ g ≤ β) (hK : IsFirstCrossing ℓ (windowUpper ℓ g) β K) :
    ∀ j ≤ K, ℓ.y₁ ≤ (couplingFlow ℓ β j).1 := by apply _root_.YangMills.Construction.HullMeans.y₁_le_couplingFlow_of_le_crossing <;> assumption
private theorem hullDecayRate_pos (Tb : ParameterAssignment) (hD : Tb.Admissible) : 0 < hullDecayRate Tb := by apply _root_.YangMills.SharedProofs.p22298 <;> assumption
end Parameters
theorem siteSizeMomentStatement_holds (h₁ : hullClassDiameterTailStatement) (h₂ : localHullSubsetStatement)
    (h₃ : localHullMomentBound) (h₄ : ChainNoise.noiseRepresentationStatement)
    (h₅ : StageStatesMeasurableStatement) (h₆ : chainMeasurabilityStatement) :
    siteSizeMomentStatement := by
  obtain ⟨CE, h₃⟩ := h₃
  have H := eventuallyInParameters_and h₁ (eventuallyInParameters_and h₂ (eventuallyInParameters_and h₃ h₄))
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt₀, H⟩ := H a ha
  refine ⟨L₀, rt₀, C₀, hrt₀, fun L hL hLL Tb hTa hTL hD hCold hOn hrt hCd => ?_⟩
  obtain ⟨M, G⟩ := H L hL hLL Tb hTa hTL hD hCold hOn hrt hCd
  refine ⟨M, fun Kr hM hη hN hF hRs => ?_⟩
  obtain ⟨y₀, F⟩ := G Kr hM hη hN hF hRs
  refine ⟨max y₀ Tb.floorMin, fun y hy hR hW g => ?_⟩
  obtain ⟨p₁, p₂, p₃, p₄⟩ := F y (le_of_max_le_left hy) hR hW
  have hyT : Tb.floorMin ≤ y := le_of_max_le_right hy
  have hfit : (Tb.stepParameters y).Admissible := hD.fits y hyT
  have hy1 : 1 ≤ y := by
    have h1 : Tb.yC ≤ Tb.floorMin := le_max_left _ _
    linarith [hD.yC_ge]
  have hc : 0 < hullDecayRate Tb := hullDecayRate_pos Tb hD
  have hL1 : (1 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) := by
    have h2 : 1 ≤ Tb.side := le_trans (by norm_num) hD.L_ge
    show (1 : ℝ) ≤ (Tb.side : ℝ)
    exact_mod_cast h2
  have hs : 0 ≤ Kr.s₁ := by
    have f := hF y
    have ha1 : (1 : ℝ) ≤ (Tb.stepParameters y).coupling := hD.a_ge
    have hC0 : 0 ≤ Kr.C₀ := by
      rw [f.C₀_eq]
      linarith [f.N₀_nonneg, f.Kc_ge]
    rw [f.s₁_eq]
    have : 0 ≤ 2 * ((Tb.stepParameters y).side : ℝ) ^ 4 * (Kr.C₀ + 2) := by positivity
    linarith
  obtain ⟨C, hC1, hCs⟩ := dyadic_sum_bound (hullDecayRate Tb) |CE Tb| ((Tb.stepParameters y).side : ℝ) hc (abs_nonneg _)
  refine ⟨C, hC1, fun β K m T u n _ hlev z k hk => ?_⟩
  have hrun := hlev.chain
  have hxy : y ≤ stageCoupling T u := by
    have e : stageCoupling T u = (couplingFlow (Tb.stepParameters y) β u).1 :=
      hrun.follows u (by have := hlev.le; omega)
    rw [e]
    exact y₁_le_couplingFlow_fst hR hW (by have := hD.B_ge; show 0 ≤ Tb.B; linarith) hrun.le_inv_sq hrun.upper_le
      hrun.isFirst u hlev.le
  have hx : 1 ≤ stageCoupling T u := hy1.trans hxy
  have hpow : stageCoupling T u ^ ((1 : ℝ) / 100) ≤ stageCoupling T u := by
    calc stageCoupling T u ^ ((1 : ℝ) / 100) ≤ stageCoupling T u ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      _ = stageCoupling T u := Real.rpow_one _
  have hpos : 0 < stageCoupling T u ^ ((1 : ℝ) / 100) := Real.rpow_pos_of_pos (by linarith) _
  have hr : (1 : ℝ) ≤ (stageRange T u : ℝ) := by
    have : 1 ≤ stageRange T u := Nat.ceil_pos.mpr hpos
    exact_mod_cast this
  have hrx : (stageRange T u : ℝ) ≤ 2 * stageCoupling T u := by
    have h1 : (stageRange T u : ℝ) < stageCoupling T u ^ ((1 : ℝ) / 100) + 1 := Nat.ceil_lt_add_one hpos.le
    linarith
  have hfibre := h₆.1
  have hq : ∀ (s m : ℕ) [NeZero m], Measurable (stageState T s m) := fun s m _ => h₅ _ hfit T s m
  have : IsProbabilityMeasure (markedSampleLaw T β u n) :=
    (h₆.2.2 _ hfit hD.L_gt T hrun.cutoff_bottom hrun.marks β u n).1
  obtain ⟨rule, hrule⟩ := (p₄ g β K m T hrun).1
  exact siteSize_moment_at_stage T Kr.s₁ u n β hs hfibre (hq 0) (hq u n) z hc hL1 hCs hx hr hrx
    (fun w D hD0 hz hd => (p₂ g β K m T).1 u n hlev w |>.2 z D hD0 hz hd)
    (fun D hD0 => p₁ g β K m T u n hlev z D hD0)
    (fun D k hD0 hk => (p₃ g β K m T u n hlev rule hrule z D k hD0 hk).2) k hk
end YangMills.Construction.HullTrees
end
