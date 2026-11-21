import YangMills.Construction.ColdStepAtMirrorFrames.RimMeanIsAWeightedMean
import YangMills.Construction.SummableBoundsOfTheFlow.IntegralOfASmoothFamily
import YangMills.Construction.SummableBoundsOfTheFlow.LeastChartEnergyIsSmooth
import YangMills.Construction.SummableBoundsOfTheFlow.MeanUnderAConfiningExponentProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheExcessOfTheDensitiesIsSmallProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheExponentOfALawIsASumOfItsPartsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory Set Filter Topology
namespace YangMills.Construction
open ColdStepAtMirrorFrames IteratedDerivative ScaledVariables StepDensities ReferenceDensity
  ConfiningMeans Estimates
open BlockAverages hiding bondSpread
namespace StepDensities
namespace MeansInWeight
section AffineCalculus
variable {E G H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
private theorem iteratedFDeriv_comp_affine {n : ℕ} {f : E → H} (A : G →ᴬ[ℝ] E) {x : G}
    (hf : ContDiffAt ℝ n f (A x)) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv ℝ i (f ∘ A) x =
      (iteratedFDeriv ℝ i f (A x)).compContinuousLinearMap fun _ => A.contLinear := by apply _root_.YangMills.SharedProofs.p8585 <;> assumption
private def clmToAffine (L : G →L[ℝ] E) : G →ᴬ[ℝ] E :=
  ⟨⟨fun z => L z, L.toLinearMap, fun p w => by simp [vadd_eq_add]⟩, L.continuous⟩
private theorem norm_iteratedFDeriv_comp_clm_le {n : ℕ} {f : E → H} (L : G →L[ℝ] E) (hL : ‖L‖ ≤ 1) {x : G}
    (hf : ContDiffAt ℝ n f (L x)) {i : ℕ} (hi : i ≤ n) :
    ‖iteratedFDeriv ℝ i (fun z => f (L z)) x‖ ≤ ‖iteratedFDeriv ℝ i f (L x)‖ := by
  have h := iteratedFDeriv_comp_affine (clmToAffine L) (x := x) hf hi
  have e : (fun z => f (L z)) = f ∘ clmToAffine L := rfl
  rw [e, h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ∏ _j : Fin i, ‖(clmToAffine L).contLinear‖ ≤ 1 := by
    refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => ?_
    exact hL
  calc _ ≤ ‖iteratedFDeriv ℝ i f ((clmToAffine L) x)‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = _ := by rw [mul_one]; rfl
private theorem norm_iteratedFDeriv_mul_le_eight {B : Set E} (hB : IsOpen B) {f g : E → ℝ}
    (hf : ContDiffOn ℝ 3 f B) (hg : ContDiffOn ℝ 3 g B) {x : E} (hx : x ∈ B) {W₁ W₂ : ℝ} (hW₁ : 0 ≤ W₁)
    (hW₂ : 0 ≤ W₂) (h₁ : ∀ i, i ≤ 3 → ‖iteratedFDeriv ℝ i f x‖ ≤ W₁)
    (h₂ : ∀ i, i ≤ 3 → ‖iteratedFDeriv ℝ i g x‖ ≤ W₂)
    {j : ℕ} (hj : j ≤ 3) : ‖iteratedFDeriv ℝ j (fun y => f y * g y) x‖ ≤ 8 * (W₁ * W₂) := by apply _root_.YangMills.SharedProofs.p56328 <;> assumption
end AffineCalculus
private theorem integral_sq_substitution {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1)) :
    ∫ θ in (0 : ℝ)..1, g θ = ∫ u in (0 : ℝ)..1, g (u ^ 2) * (2 * u) := by
  have h := intervalIntegral.integral_comp_mul_deriv' (a := (0 : ℝ)) (b := 1) (f := fun u => u ^ 2)
    (f' := fun u => 2 * u) (g := g) (fun x _ => by simpa using hasDerivAt_pow 2 x)
    (by fun_prop) (hg.mono ?_)
  · simpa using h.symm
  · rintro _ ⟨u, hu, rfl⟩
    rw [uIcc_of_le zero_le_one] at hu
    exact ⟨by positivity, by nlinarith [hu.1, hu.2]⟩
private theorem continuousOn_of_comp_sq {g : ℝ → ℝ} (h : ContinuousOn (fun u => g (u ^ 2)) (Icc 0 1)) :
    ContinuousOn g (Icc 0 1) := by
  have h1 : ContinuousOn (fun θ : ℝ => g (Real.sqrt θ ^ 2)) (Icc 0 1) :=
    h.comp Real.continuous_sqrt.continuousOn fun θ hθ =>
      ⟨Real.sqrt_nonneg _, by
        have := Real.sqrt_le_sqrt hθ.2
        simpa using this⟩
  refine h1.congr fun θ hθ => ?_
  show g θ = g (Real.sqrt θ ^ 2)
  rw [Real.sq_sqrt hθ.1]
section WeightAndMove
variable {F : BlockFrame}
private def weightMoveFamily (M : ℝ → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (q : ℝ × (Fin k → ℝ)) : ℝ :=
  M (q.1 ^ 2) (leftTranslate (bondSpread c X q.2) V)
private theorem isOpen_contDiffAt_set {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] (f : P → Q) : IsOpen {z | ContDiffAt ℝ 3 f z} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  exact (show ContDiffAt ℝ 3 f z from hz).eventually (by simp)
private theorem continuousOn_tube {k : ℕ} {f : ℝ × (Fin k → ℝ) → ℝ}
    (h : ∀ u ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 3 f (u, 0)) :
    ∃ r : ℝ, 0 < r ∧ ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ContinuousOn (fun u => f (u, τ)) (Icc 0 1) := by
  have hsub : (Icc (0 : ℝ) 1) ×ˢ ({0} : Set (Fin k → ℝ)) ⊆ {z | ContDiffAt ℝ 3 f z} := by
    rintro ⟨u, t⟩ ⟨hu, ht⟩
    obtain rfl : t = 0 := ht
    exact h u hu
  obtain ⟨U, W, hU, hW, hUs, hW0, hUW⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton (isOpen_contDiffAt_set f) hsub
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW 0 (hW0 rfl)
  refine ⟨r, hr, fun τ hτ u hu => ?_⟩
  have hz : (u, τ) ∈ {z | ContDiffAt ℝ 3 f z} := hUW ⟨hUs hu, hball hτ⟩
  have hc : ContinuousAt f (u, τ) := (show ContDiffAt ℝ 3 f (u, τ) from hz).continuousAt
  have h2 : ContinuousAt (fun u' : ℝ => (u', τ)) u := by fun_prop
  exact (ContinuousAt.comp (f := fun u' : ℝ => (u', τ)) hc h2).continuousWithinAt
private theorem integral_weight_eventuallyEq {M : ℝ → F.GaugeField F.top → ℝ}
    {V : F.GaugeField F.top} {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hJ : ∀ u ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 3 (weightMoveFamily M V c X) (u, 0)) :
    (fun τ => ∫ θ in (0 : ℝ)..1, M θ (leftTranslate (bondSpread c X τ) V)) =ᶠ[𝓝 0]
      fun τ => ∫ u in (0 : ℝ)..1, weightMoveFamily M V c X (u, τ) * (2 * u) := by
  obtain ⟨r, hr, hc⟩ := continuousOn_tube hJ
  filter_upwards [Metric.ball_mem_nhds (0 : Fin k → ℝ) hr] with τ hτ
  have h1 := hc τ hτ
  exact integral_sq_substitution (g := fun θ => M θ (leftTranslate (bondSpread c X τ) V))
    (continuousOn_of_comp_sq h1)
private theorem contDiffAt_mul_two_fst {k : ℕ} {f : ℝ × (Fin k → ℝ) → ℝ} {u : ℝ}
    (h : ContDiffAt ℝ 3 f (u, 0)) :
    ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun q : ℝ × (Fin k → ℝ) => f q * (2 * q.1)) (u, 0) :=
  h.mul (contDiff_const.mul contDiff_fst).contDiffAt
private theorem derivUnderWeight_of_joint (hL : DerivAlongRulesHold) (hI : IntervalIntegralSmoothFamily)
    {M : ℝ → F.GaugeField F.top → ℝ} {V : F.GaugeField F.top}
    (hJ : ∀ (k' : ℕ) (c' : Fin k' → F.Site F.top × Fin 4) (X' : Fin k' → imaginaryQuaternions),
      ∀ u ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 3 (weightMoveFamily M V c' X') (u, 0))
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3) :
    DerivUnderWeightIntegral M V c X := by
  have rules := hL.1 (Fin k → ℝ) ℝ
  have rulesJ := hL.1 (ℝ × (Fin k → ℝ)) ℝ
  set e : Fin k → Fin k → ℝ := fun l => Pi.single l 1 with he
  set l : List (Fin k → ℝ) := List.ofFn e with hl
  have hlen : l.length = k := by simp [hl]
  set J := weightMoveFamily M V c X with hJdef
  have hD : ∀ u ∈ Icc (0 : ℝ) 1, bondDeriv (M (u ^ 2)) V c X =
      derivAlong J (l.map (ContinuousLinearMap.inr ℝ ℝ (Fin k → ℝ))) (u, 0) := by
    intro u hu
    have h0 : ContDiffAt ℝ ((l.length : ℕ) : WithTop ℕ∞) J
        ((u, 0) + ContinuousLinearMap.inr ℝ ℝ (Fin k → ℝ) 0) := by
      simpa [hlen] using (hJ k c X u hu).of_le (by exact_mod_cast hk)
    have h1 := hL.2 (ℝ × (Fin k → ℝ)) (Fin k → ℝ) ℝ J (ContinuousLinearMap.inr ℝ ℝ (Fin k → ℝ)) (u, 0) 0 l h0
    have h2 : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞)
        (fun τ => J ((u, 0) + ContinuousLinearMap.inr ℝ ℝ (Fin k → ℝ) τ)) 0 := by
      have h3 : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) (fun τ : Fin k → ℝ =>
          ((u, 0) + ContinuousLinearMap.inr ℝ ℝ (Fin k → ℝ) τ : ℝ × (Fin k → ℝ))) 0 := by
        fun_prop
      have h4 : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) J
          (((u, 0) : ℝ × (Fin k → ℝ)) + ContinuousLinearMap.inr ℝ ℝ (Fin k → ℝ) 0) := by
        simpa [hlen] using h0
      exact ContDiffAt.comp (0 : Fin k → ℝ) h4 h3
    have h5 := rules.iteratedFDeriv_eq _ 0 k e h2
    simp only [map_zero, add_zero] at h1
    rw [← h1, ← h5]
    have e₂ : (fun τ => J ((u, 0) + ContinuousLinearMap.inr ℝ ℝ (Fin k → ℝ) τ)) =
        fun τ => M (u ^ 2) (leftTranslate (bondSpread c X τ) V) := by
      funext τ
      simp [hJdef, weightMoveFamily]
    rw [e₂]
    rfl
  set L := l.map (ContinuousLinearMap.inr ℝ ℝ (Fin k → ℝ)) with hLdef
  have hLlen : L.length = k := by simp [hLdef, hlen]
  have hcont : ContinuousOn (fun θ => bondDeriv (M θ) V c X) (Icc 0 1) := by
    apply continuousOn_of_comp_sq
    have h1 : ContinuousOn (fun u : ℝ => derivAlong J L (u, 0)) (Icc 0 1) := by
      intro u hu
      have h2 := rulesJ.contDiffAt J (u, 0) 0 L (by
        rw [hLlen]
        simpa using (hJ k c X u hu).of_le (by exact_mod_cast hk))
      have h3 : ContinuousAt (derivAlong J L) (u, 0) := h2.continuousAt
      have h4 : ContinuousAt (fun u' : ℝ => ((u', 0) : ℝ × (Fin k → ℝ))) u := by fun_prop
      exact (ContinuousAt.comp (f := fun u' : ℝ => ((u', 0) : ℝ × (Fin k → ℝ))) h3 h4).continuousWithinAt
    exact h1.congr hD
  refine ⟨fun k' c' X' => ?_, hcont.intervalIntegrable_of_Icc zero_le_one, ?_⟩
  · have h1 := (hI (Fin k' → ℝ) (fun q => weightMoveFamily M V c' X' q * (2 * q.1)) 0 3
      fun v hv => contDiffAt_mul_two_fst (hJ k' c' X' v hv)).1
    have h1' : ContDiffAt ℝ 3 (fun τ : Fin k' → ℝ =>
        ∫ u in (0 : ℝ)..1, weightMoveFamily M V c' X' (u, τ) * (2 * u)) 0 := by
      exact_mod_cast h1
    exact h1'.congr_of_eventuallyEq (integral_weight_eventuallyEq c' X' (hJ k' c' X'))
  · obtain ⟨h1, h2⟩ := hI (Fin k → ℝ) (fun q => J q * (2 * q.1)) 0 3
      fun v hv => contDiffAt_mul_two_fst (hJ k c X v hv)
    have g := integral_weight_eventuallyEq (M := M) (V := V) c X (hJ k c X)
    show iteratedFDeriv ℝ k (fun τ => ∫ θ in (0 : ℝ)..1, M θ (leftTranslate (bondSpread c X τ) V)) 0 e = _
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ g k).eq_of_nhds, rules.iteratedFDeriv_eq _ 0 k e
      (h1.of_le (by exact_mod_cast hk)), h2 (List.ofFn e) (by simpa using hk), integral_sq_substitution hcont]
    refine intervalIntegral.integral_congr fun v hv => ?_
    have hv' : v ∈ Icc (0 : ℝ) 1 := by rwa [uIcc_of_le zero_le_one] at hv
    have hs : ContDiffAt ℝ (k : WithTop ℕ∞) (fun τ : Fin k → ℝ => J (v, τ)) 0 := by
      have h3 : ContDiffAt ℝ (k : WithTop ℕ∞) (fun τ : Fin k → ℝ => ((v, τ) : ℝ × (Fin k → ℝ))) 0 := by
        fun_prop
      exact ContDiffAt.comp (0 : Fin k → ℝ) ((hJ k c X v hv').of_le (by exact_mod_cast hk)) h3
    have e₁ : (fun τ : Fin k → ℝ => J (v, τ) * (2 * v)) = (2 * v) • fun τ : Fin k → ℝ => J (v, τ) := by
      funext τ
      simp [mul_comm]
    have hs₂ : ContDiffAt ℝ (k : WithTop ℕ∞) (fun τ : Fin k → ℝ => J (v, τ) * (2 * v)) 0 :=
      hs.mul contDiffAt_const
    simp only []
    rw [← rules.iteratedFDeriv_eq _ 0 k e hs₂, e₁, iteratedFDeriv_const_smul_apply hs]
    simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    rw [mul_comm]
    rfl
end WeightAndMove
section UniformBounds
variable {P P' Ω : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup P'] [NormedSpace ℝ P']
private structure UniformC3 (B : Set P) (S : Set Ω) (W : Ω → ℝ) (G : P → Ω → ℝ) : Prop where
  smooth : ∀ ω ∈ S, ContDiffOn ℝ 3 (fun s => G s ω) B
  bound : ∀ ω ∈ S, ∀ j, j ≤ 3 → ∀ s ∈ B, ‖iteratedFDeriv ℝ j (fun s => G s ω) s‖ ≤ W ω
variable {B : Set P} {S : Set Ω} {W W₁ W₂ : Ω → ℝ} {G G₁ G₂ : P → Ω → ℝ}
private theorem UniformC3.add (hB : IsOpen B) (h₁ : UniformC3 B S W₁ G₁) (h₂ : UniformC3 B S W₂ G₂) :
    UniformC3 B S (fun ω => W₁ ω + W₂ ω) fun s ω => G₁ s ω + G₂ s ω := by
  refine ⟨fun ω hω => (h₁.smooth ω hω).add (h₂.smooth ω hω), fun ω hω j hj s hs => ?_⟩
  have a₁ := ((h₁.smooth ω hω).contDiffAt (hB.mem_nhds hs)).of_le (m := j) (by exact_mod_cast hj)
  have a₂ := ((h₂.smooth ω hω).contDiffAt (hB.mem_nhds hs)).of_le (m := j) (by exact_mod_cast hj)
  have e : iteratedFDeriv ℝ j (fun s => G₁ s ω + G₂ s ω) s =
      iteratedFDeriv ℝ j (fun s => G₁ s ω) s + iteratedFDeriv ℝ j (fun s => G₂ s ω) s :=
    iteratedFDeriv_add_apply a₁ a₂
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (h₁.bound ω hω j hj s hs) (h₂.bound ω hω j hj s hs))
private theorem UniformC3.mul (hB : IsOpen B) (h₁ : UniformC3 B S W₁ G₁) (h₂ : UniformC3 B S W₂ G₂)
    (p₁ : ∀ ω ∈ S, 0 ≤ W₁ ω) (p₂ : ∀ ω ∈ S, 0 ≤ W₂ ω) :
    UniformC3 B S (fun ω => 8 * (W₁ ω * W₂ ω)) fun s ω => G₁ s ω * G₂ s ω :=
  ⟨fun ω hω => (h₁.smooth ω hω).mul (h₂.smooth ω hω), fun ω hω _ hj s hs =>
    norm_iteratedFDeriv_mul_le_eight hB (h₁.smooth ω hω) (h₂.smooth ω hω) hs (p₁ ω hω) (p₂ ω hω)
      (fun i hi => h₁.bound ω hω i hi s hs) (fun i hi => h₂.bound ω hω i hi s hs) hj⟩
private theorem uniformC3_of_param [FiniteDimensional ℝ P] {φ : P → ℝ} (hφ : ContDiff ℝ 3 φ) {r : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ UniformC3 (Metric.ball (0 : P) r) S (fun _ => C) fun s _ => φ s := by
  haveI : ProperSpace P := FiniteDimensional.proper_real P
  have hbd : ∀ i : ℕ, i ≤ 3 → ∃ M : ℝ, ∀ p ∈ Metric.closedBall (0 : P) r, ‖iteratedFDeriv ℝ i φ p‖ ≤ M := by
    intro i hi
    exact (isCompact_closedBall _ _).exists_bound_of_continuousOn
      (hφ.continuous_iteratedFDeriv (m := i) (by exact_mod_cast hi)).continuousOn
  choose! M hM using hbd
  refine ⟨|M 0| + |M 1| + |M 2| + |M 3|, by positivity, ⟨fun _ _ => hφ.contDiffOn, fun _ _ j hj s hs => ?_⟩⟩
  refine (hM j hj s (Metric.ball_subset_closedBall hs)).trans ?_
  have a0 := abs_nonneg (M 0)
  have a1 := abs_nonneg (M 1)
  have a2 := abs_nonneg (M 2)
  have a3 := abs_nonneg (M 3)
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · linarith [le_abs_self (M 0)]
  · linarith [le_abs_self (M 1)]
  · linarith [le_abs_self (M 2)]
  · linarith [le_abs_self (M 3)]
private theorem uniformC3_const (B : Set P) (g : Ω → ℝ) :
    UniformC3 B S (fun ω => |g ω|) fun _ ω => g ω := by
  refine ⟨fun _ _ => contDiffOn_const, fun ω _ j _ s _ => ?_⟩
  by_cases hj : j = 0
  · subst hj
    simp
  · rw [iteratedFDeriv_const_of_ne hj]
    simpa using abs_nonneg (g ω)
private theorem UniformC3.sum {α : Type} (hB : IsOpen B) (I : Finset α) {Gs : α → P → Ω → ℝ}
    {Ws : α → Ω → ℝ} (h : ∀ a ∈ I, UniformC3 B S (Ws a) (Gs a)) :
    UniformC3 B S (fun ω => ∑ a ∈ I, Ws a ω) fun s ω => ∑ a ∈ I, Gs a s ω := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    have := uniformC3_const (S := S) B (fun _ : Ω => (0 : ℝ))
    simpa using this
  | insert a I ha ih =>
    have h1 := h a (Finset.mem_insert_self a I)
    have h2 := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    have h3 := h1.add hB h2
    simpa only [Finset.sum_insert ha] using h3
private theorem UniformC3.mono {W' : Ω → ℝ} (h : UniformC3 B S W G) (hW : ∀ ω ∈ S, W ω ≤ W' ω) :
    UniformC3 B S W' G :=
  ⟨h.smooth, fun ω hω j hj s hs => (h.bound ω hω j hj s hs).trans (hW ω hω)⟩
private theorem UniformC3.along {B' : Set P'} (L : P' →L[ℝ] P) (hL : ‖L‖ ≤ 1) (hB : IsOpen B)
    (hB' : ∀ s ∈ B', L s ∈ B) (h : UniformC3 B S W G) : UniformC3 B' S W fun s ω => G (L s) ω := by
  refine ⟨fun ω hω => (h.smooth ω hω).comp L.contDiff.contDiffOn hB', fun ω hω j hj s hs => ?_⟩
  have h1 := ((h.smooth ω hω).contDiffAt (hB.mem_nhds (hB' s hs))).of_le (m := ((3 : ℕ) : WithTop ℕ∞))
    (by norm_num)
  exact (norm_iteratedFDeriv_comp_clm_le L hL h1 hj).trans (h.bound ω hω j hj _ (hB' s hs))
private theorem UniformC3.congr {G' : P → Ω → ℝ} (hB : IsOpen B) (h : UniformC3 B S W G)
    (e : ∀ ω ∈ S, ∀ s ∈ B, G' s ω = G s ω) : UniformC3 B S W G' := by
  refine ⟨fun ω hω => (h.smooth ω hω).congr fun s hs => e ω hω s hs, fun ω hω j hj s hs => ?_⟩
  have h1 : (fun s => G' s ω) =ᶠ[𝓝 s] fun s => G s ω := by
    filter_upwards [hB.mem_nhds hs] with x hx using e ω hω x hx
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ h1 j).eq_of_nhds]
  exact h.bound ω hω j hj s hs
private theorem UniformC3.comp_right {Ω' : Type} {S' : Set Ω'} (φ : Ω' → Ω) (hφ : ∀ ω ∈ S', φ ω ∈ S)
    (h : UniformC3 B S W G) : UniformC3 B S' (fun ω => W (φ ω)) fun s ω => G s (φ ω) :=
  ⟨fun ω hω => h.smooth _ (hφ ω hω), fun ω hω j hj s hs => h.bound _ (hφ ω hω) j hj s hs⟩
end UniformBounds
section ScaleJets
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
private def scaleDirs (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (i : ℕ) : List (ℝ × P) :=
  (List.replicate i (1 : ℝ)).map (ContinuousLinearMap.inl ℝ ℝ P)
private def moveDirs {j : ℕ} (w : Fin j → P) : List (ℝ × P) :=
  (List.ofFn w).map (ContinuousLinearMap.inr ℝ ℝ P)
private theorem scaleDirs_length (i : ℕ) : (scaleDirs P i).length = i := by simp [scaleDirs]
private theorem moveDirs_length {j : ℕ} (w : Fin j → P) : (moveDirs w).length = j := by simp [moveDirs]
private theorem iteratedDeriv_fst_eq_derivAlong (hL : DerivAlongRulesHold) {g : ℝ × P → ℝ} {a : ℝ} {b : P}
    {i : ℕ} (hg : ContDiffAt ℝ (i : WithTop ℕ∞) g (a, b)) :
    iteratedDeriv i (fun l => g (l, b)) a = derivAlong g (scaleDirs P i) (a, b) := by
  have e : ∀ l : ℝ, ((0 : ℝ), b) + ContinuousLinearMap.inl ℝ ℝ P l = (l, b) := fun l => by simp
  have h0 : ContDiffAt ℝ (((List.replicate i (1 : ℝ)).length : ℕ) : WithTop ℕ∞) g
      (((0 : ℝ), b) + ContinuousLinearMap.inl ℝ ℝ P a) := by simpa [e] using hg
  have h1 := hL.2 (ℝ × P) ℝ ℝ g (ContinuousLinearMap.inl ℝ ℝ P) (0, b) a (List.replicate i 1) h0
  have hs : ContDiffAt ℝ (i : WithTop ℕ∞) (fun l : ℝ => g (l, b)) a := by
    have h3 : ContDiffAt ℝ (i : WithTop ℕ∞) (fun l : ℝ => (l, b)) a := by fun_prop
    exact ContDiffAt.comp a hg h3
  have h2 := (hL.1 ℝ ℝ).iteratedFDeriv_eq _ a i (fun _ => 1) hs
  rw [iteratedDeriv_eq_iteratedFDeriv, h2, List.ofFn_const]
  simp only [e] at h1
  exact h1
private theorem iteratedFDeriv_snd_eq_derivAlong (hL : DerivAlongRulesHold) {g : ℝ × P → ℝ} {a : ℝ} {b : P}
    {j : ℕ} (w : Fin j → P) (hg : ContDiffAt ℝ (j : WithTop ℕ∞) g (a, b)) :
    iteratedFDeriv ℝ j (fun σ => g (a, σ)) b w = derivAlong g (moveDirs w) (a, b) := by
  have e : ∀ σ : P, (a, (0 : P)) + ContinuousLinearMap.inr ℝ ℝ P σ = (a, σ) := fun σ => by simp
  have h0 : ContDiffAt ℝ (((List.ofFn w).length : ℕ) : WithTop ℕ∞) g
      ((a, (0 : P)) + ContinuousLinearMap.inr ℝ ℝ P b) := by simpa [e] using hg
  have h1 := hL.2 (ℝ × P) P ℝ g (ContinuousLinearMap.inr ℝ ℝ P) (a, 0) b (List.ofFn w) h0
  have hs : ContDiffAt ℝ (j : WithTop ℕ∞) (fun σ : P => g (a, σ)) b := by
    have h3 : ContDiffAt ℝ (j : WithTop ℕ∞) (fun σ : P => (a, σ)) b := by fun_prop
    exact ContDiffAt.comp b hg h3
  have h2 := (hL.1 P ℝ).iteratedFDeriv_eq _ b j w hs
  rw [h2]
  simp only [e] at h1
  exact h1
private theorem eventually_contDiffAt_snd {N : ℕ} {f : ℝ × P → ℝ}
    (hf : ContDiffAt ℝ (N : WithTop ℕ∞) f (0, 0)) :
    ∀ᶠ σ in 𝓝 (0 : P), ContDiffAt ℝ (N : WithTop ℕ∞) f (0, σ) := by
  have h1 : ∀ᶠ z in 𝓝 ((0 : ℝ), (0 : P)), ContDiffAt ℝ (N : WithTop ℕ∞) f z := hf.eventually (by simp)
  have h2 : Tendsto (fun σ : P => ((0 : ℝ), σ)) (𝓝 0) (𝓝 (0, 0)) :=
    (Continuous.prodMk_right (0 : ℝ)).tendsto 0
  exact h2.eventually h1
private theorem eventually_contDiffAt_fst {N : ℕ} {f : ℝ × P → ℝ}
    (hf : ContDiffAt ℝ (N : WithTop ℕ∞) f (0, 0)) :
    ∀ᶠ l in 𝓝 (0 : ℝ), ContDiffAt ℝ (N : WithTop ℕ∞) f (l, 0) := by
  have h1 : ∀ᶠ z in 𝓝 ((0 : ℝ), (0 : P)), ContDiffAt ℝ (N : WithTop ℕ∞) f z := hf.eventually (by simp)
  have h2 : Tendsto (fun l : ℝ => (l, (0 : P))) (𝓝 0) (𝓝 (0, 0)) :=
    (Continuous.prodMk_left (0 : P)).tendsto 0
  exact h2.eventually h1
private theorem contDiffAt_scaleJet (hL : DerivAlongRulesHold) {f : ℝ × P → ℝ} {n i : ℕ}
    (hf : ContDiffAt ℝ ((n + i : ℕ) : WithTop ℕ∞) f (0, 0)) :
    ContDiffAt ℝ (n : WithTop ℕ∞) (fun σ => iteratedDeriv i (fun l => f (l, σ)) 0) 0 := by
  have h1 : ContDiffAt ℝ (n : WithTop ℕ∞) (derivAlong f (scaleDirs P i)) (0, 0) :=
    (hL.1 (ℝ × P) ℝ).contDiffAt f (0, 0) n (scaleDirs P i) (by rw [scaleDirs_length]; exact hf)
  have h2 : ContDiffAt ℝ (n : WithTop ℕ∞) (fun σ : P => ((0 : ℝ), σ)) 0 := by fun_prop
  have h3 := ContDiffAt.comp (0 : P) h1 h2
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [eventually_contDiffAt_snd hf] with σ hσ
  exact iteratedDeriv_fst_eq_derivAlong hL (hσ.of_le (by exact_mod_cast Nat.le_add_left i n))
private theorem scaleJet_comm (hL : DerivAlongRulesHold) {f : ℝ × P → ℝ} {i j : ℕ} (w : Fin j → P)
    (hf : ContDiffAt ℝ ((i + j : ℕ) : WithTop ℕ∞) f (0, 0)) :
    iteratedFDeriv ℝ j (fun σ => iteratedDeriv i (fun l => f (l, σ)) 0) 0 w =
      iteratedDeriv i (fun l => iteratedFDeriv ℝ j (fun σ => f (l, σ)) 0 w) 0 := by
  have rules := hL.1 (ℝ × P) ℝ
  set R := scaleDirs P i with hR
  set Lw := moveDirs w with hLw
  have hRl : R.length = i := scaleDirs_length i
  have hLl : Lw.length = j := moveDirs_length w
  have gl : (fun σ => iteratedDeriv i (fun l => f (l, σ)) 0) =ᶠ[𝓝 0] fun σ => derivAlong f R (0, σ) := by
    filter_upwards [eventually_contDiffAt_snd hf] with σ hσ
    exact iteratedDeriv_fst_eq_derivAlong hL (hσ.of_le (by exact_mod_cast Nat.le_add_right i j))
  have h₁s : ContDiffAt ℝ (j : WithTop ℕ∞) (derivAlong f R) (0, 0) :=
    rules.contDiffAt f (0, 0) j R (by
      rw [hRl, Nat.add_comm]
      exact hf)
  have left : iteratedFDeriv ℝ j (fun σ => iteratedDeriv i (fun l => f (l, σ)) 0) 0 w =
      derivAlong f (Lw ++ R) (0, 0) := by
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ gl j).eq_of_nhds, iteratedFDeriv_snd_eq_derivAlong hL w h₁s,
      rules.append]
  have gr : (fun l => iteratedFDeriv ℝ j (fun σ => f (l, σ)) 0 w) =ᶠ[𝓝 0] fun l => derivAlong f Lw (l, 0) := by
    filter_upwards [eventually_contDiffAt_fst hf] with l hl
    exact iteratedFDeriv_snd_eq_derivAlong hL w (hl.of_le (by exact_mod_cast Nat.le_add_left j i))
  have h₂s : ContDiffAt ℝ (i : WithTop ℕ∞) (derivAlong f Lw) (0, 0) :=
    rules.contDiffAt f (0, 0) i Lw (by
      rw [hLl]
      exact hf)
  have right : iteratedDeriv i (fun l => iteratedFDeriv ℝ j (fun σ => f (l, σ)) 0 w) 0 =
      derivAlong f (R ++ Lw) (0, 0) := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq i gr, iteratedDeriv_fst_eq_derivAlong hL h₂s, rules.append]
  rw [left, right]
  refine rules.perm f (0, 0) _ _ List.perm_append_comm ?_
  rw [List.length_append, hLl, hRl, Nat.add_comm]
  exact hf
end ScaleJets
section ObservableBounds
variable {F : BlockFrame}
private def scaleJet (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (i : ℕ)
    (ζ : StepVariable (finiteCells F)) (V : F.GaugeField F.top) : ℝ :=
  iteratedDeriv i (fun l => Ob l ζ V) 0
variable {κ ρ l₁ K : ℝ} {Y : F.Cell} {V : F.GaugeField F.top}
  {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
private theorem contDiffAt_scale_move (h : IsSmoothObservable κ ρ l₁ K Y V Ob) {l : ℝ}
    {ζ : StepVariable (finiteCells F)} (hb : MemScaledBalls ρ |l| ζ) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    ContDiffAt ℝ ((6 : ℕ) : WithTop ℕ∞)
      (fun q : ℝ × (Fin k → ℝ) => Ob q.1 ζ (leftTranslate (bondSpread c X q.2) V)) (l, 0) := by
  have h1 := h.contDiffAt l ζ k c X hb
  have h2 : ContDiffAt ℝ ((6 : ℕ) : WithTop ℕ∞)
      (fun q : ℝ × (Fin k → ℝ) => ((q.1, ζ), q.2) :
        ℝ × (Fin k → ℝ) → (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ)) (l, 0) := by
    fun_prop
  exact ContDiffAt.comp (l, (0 : Fin k → ℝ)) (g := fun q : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ) =>
    Ob q.1.1 q.1.2 (leftTranslate (bondSpread c X q.2) V)) h1 h2
private theorem memScaledBalls_zero (hρ : 0 < ρ) (ζ : StepVariable (finiteCells F)) :
    MemScaledBalls ρ |(0 : ℝ)| ζ := by
  intro b
  simpa using hρ
private theorem bondDeriv_scaleJet (hL : DerivAlongRulesHold) (h : IsSmoothObservable κ ρ l₁ K Y V Ob)
    (hρ : 0 < ρ) (ζ : StepVariable (finiteCells F)) {i j : ℕ} (hij : i + j ≤ 6)
    (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions) :
    bondDeriv (scaleJet Ob i ζ) V c X = scaleDeriv Ob V c X i ζ 0 :=
  scaleJet_comm hL (f := fun q : ℝ × (Fin j → ℝ) => Ob q.1 ζ (leftTranslate (bondSpread c X q.2) V)) _
    ((contDiffAt_scale_move h (memScaledBalls_zero hρ ζ) c X).of_le (by exact_mod_cast hij))
private theorem abs_scaleDeriv_zero_le (h : IsSmoothObservable κ ρ l₁ K Y V Ob) (hl : 0 < l₁) (hρ : 0 < ρ)
    {k i : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (ζ : StepVariable (finiteCells F)) (hki : IsControlledOrder k i) (hX : AreUnitVectors X) :
    |scaleDeriv Ob V c X i ζ 0| ≤
      K * (1 + localWeight κ Y ζ) ^ 7 * Real.exp (-(2 ^ 4 * κ * bondSpan Y c)) := by
  set R := ‖ζ‖ with hR
  have hb : ∀ b, ‖ζ b‖ ≤ R := fun b => norm_le_pi_norm ζ b
  have hc := h.continuousOn k i c X R hki
  set Sset : Set (ℝ × StepVariable (finiteCells F)) := {q | 0 ≤ q.1 ∧ q.1 ≤ l₁ ∧ MemScaledBalls ρ q.1 q.2 ∧
    ∀ b, ‖q.2 b‖ ≤ R} with hS
  have hin : ((0 : ℝ), ζ) ∈ Sset := ⟨le_rfl, hl.le, fun b => by simpa using hρ, hb⟩
  have h1 := hc _ hin
  set ε : ℝ := min l₁ (ρ / (R + 1)) with hε
  have hεp : 0 < ε := lt_min hl (by positivity)
  have hmem : ∀ᶠ l in 𝓝[>] (0 : ℝ), l ∈ Ioo (0 : ℝ) ε := Ioo_mem_nhdsGT hεp
  have ht : Tendsto (fun l : ℝ => ((l, ζ) : ℝ × StepVariable (finiteCells F))) (𝓝[>] 0)
      (𝓝[Sset] (0, ζ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((Continuous.prodMk_left ζ).tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [hmem] with l hl'
      refine ⟨hl'.1.le, hl'.2.le.trans (min_le_left _ _), fun b => ?_, hb⟩
      have h2 : l ≤ ρ / (R + 1) := hl'.2.le.trans (min_le_right _ _)
      calc l * ‖ζ b‖ ≤ ρ / (R + 1) * R := by
            have := hb b
            have := hl'.1.le
            gcongr
        _ < ρ := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith
  have h3 := (h1.tendsto.comp ht).abs
  refine le_of_tendsto h3 ?_
  filter_upwards [hmem] with l hl'
  have hl₁ : l ≤ l₁ := hl'.2.le.trans (min_le_left _ _)
  have hinb : MemScaledBalls ρ l ζ := by
    intro b
    have h2 : l ≤ ρ / (R + 1) := hl'.2.le.trans (min_le_right _ _)
    calc l * ‖ζ b‖ ≤ ρ / (R + 1) * R := by
          have := hb b
          have := hl'.1.le
          gcongr
      _ < ρ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
  exact h.deriv_le k i c X l ζ hki hX hl'.1 hl₁ hinb
private theorem localWeight_le (hκ : 0 ≤ κ) (ζ : StepVariable (finiteCells F)) :
    localWeight κ Y ζ ≤ (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ) * ‖ζ‖ := by
  unfold localWeight
  calc ∑ b : ↥(chordBonds (finiteCells F)),
        Real.exp (-(2 ^ 4 * κ * cellSupDist (enclosingCell b.1.1) Y)) * ‖ζ b‖
      ≤ ∑ _b : ↥(chordBonds (finiteCells F)), ‖ζ‖ := by
        refine Finset.sum_le_sum fun b _ => ?_
        have h1 : Real.exp (-(2 ^ 4 * κ * cellSupDist (enclosingCell b.1.1) Y)) ≤ 1 := by
          rw [Real.exp_le_one_iff, neg_nonpos]
          exact mul_nonneg (mul_nonneg (by norm_num) hκ) (Nat.cast_nonneg _)
        calc _ ≤ 1 * ‖ζ‖ := mul_le_mul h1 (norm_le_pi_norm ζ b) (norm_nonneg _) zero_le_one
          _ = ‖ζ‖ := one_mul _
    _ = _ := by simp
private theorem one_add_localWeight_pow_le (hκ : 0 ≤ κ) (ζ : StepVariable (finiteCells F)) :
    (1 + localWeight κ Y ζ) ^ 7 ≤
      (1 + (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ)) ^ 7 * (1 + ‖ζ‖) ^ 7 := by
  have hN : 0 ≤ localWeight κ Y ζ := by
    unfold localWeight
    exact Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by linarith) ?_ 7
  have h1 := localWeight_le (Y := Y) hκ ζ
  have h2 : 0 ≤ (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ) := Nat.cast_nonneg _
  have h3 := norm_nonneg ζ
  nlinarith [mul_nonneg h2 h3]
private theorem exp_neg_span_le_one (hκ : 0 ≤ κ) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) :
    Real.exp (-(2 ^ 4 * κ * bondSpan Y c)) ≤ 1 := by
  rw [Real.exp_le_one_iff, neg_nonpos]
  exact mul_nonneg (mul_nonneg (by norm_num) hκ) (Nat.cast_nonneg _)
private theorem isControlledOrder_of_le {j : ℕ} (hj : j ≤ 3) {i : ℕ} (hi : i ≤ 2) : IsControlledOrder j i :=
  Or.inl ⟨hj, hi⟩
private structure MoveChart (s : ℝ) (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (r Cc : ℝ) : Prop where
  pos : 0 < r
  nonneg : 0 ≤ Cc
  chart : ∀ (G : F.GaugeField F.top → ℝ) (D : ℝ), 0 ≤ D →
      (∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ (q : ℕ) (c' : Fin q → F.Site F.top × Fin 4)
        (X' : Fin q → imaginaryQuaternions),
        AreUnitVectors X' → ContDiffAt ℝ 3
          (fun σ : Fin q → ℝ => G (leftTranslate (bondSpread c' X' σ) (leftTranslate (bondSpread c X τ) V))) 0) →
      (∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ (i : ℕ) (c' : Fin i → F.Site F.top × Fin 4)
        (X' : Fin i → imaginaryQuaternions),
        i ≤ 3 → AreUnitVectors X' → |bondDeriv G (leftTranslate (bondSpread c X τ) V) c' X'| ≤ D) →
      ContDiffOn ℝ 3 (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) V)) (Metric.ball 0 r) ∧
      ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ i, i ≤ 3 →
        ‖iteratedFDeriv ℝ i (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) V)) τ‖ ≤ Cc * D
  cold : ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, IsSmallCurvature s (leftTranslate (bondSpread c X τ) V)
variable {s : ℝ} {k : ℕ} {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {r Cc : ℝ}
private theorem uniformC3_scaleJet (hL : DerivAlongRulesHold) (hCh : MoveChart s V c X r Cc)
    (hOb : IsSmoothAtSmallCurvature s κ ρ l₁ K Y Ob) (hl : 0 < l₁) (hρ : 0 < ρ) (hκ : 0 ≤ κ) (hK : 0 ≤ K)
    {i : ℕ} (hi : i ≤ 2) :
    UniformC3 (Metric.ball (0 : Fin k → ℝ) r) (univ : Set (StepVariable (finiteCells F)))
      (fun ζ => Cc * (K * (1 + localWeight κ Y ζ) ^ 7))
      (fun τ ζ => scaleJet Ob i ζ (leftTranslate (bondSpread c X τ) V)) := by
  have key : ∀ ζ : StepVariable (finiteCells F), _ := fun ζ =>
    hCh.chart (scaleJet Ob i ζ) (K * (1 + localWeight κ Y ζ) ^ 7) (by
        have : 0 ≤ localWeight κ Y ζ := by
          unfold localWeight
          exact Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
        positivity)
      (fun τ hτ q c' X' _ => by
        have h1 := (contDiffAt_scale_move (hOb _ (hCh.cold τ hτ)) (memScaledBalls_zero hρ ζ) c' X').of_le
          (m := ((3 + i : ℕ) : WithTop ℕ∞)) (by exact_mod_cast (by omega : 3 + i ≤ 6))
        exact_mod_cast contDiffAt_scaleJet hL h1)
      (fun τ hτ j c' X' hj hX' => by
        have hO := hOb _ (hCh.cold τ hτ)
        rw [bondDeriv_scaleJet hL hO hρ ζ (by omega) c' X']
        refine (abs_scaleDeriv_zero_le hO hl hρ c' X' ζ (isControlledOrder_of_le hj hi) hX').trans ?_
        have h2 := exp_neg_span_le_one (Y := Y) hκ c'
        have h3 : 0 ≤ K * (1 + localWeight κ Y ζ) ^ 7 := by
          have : 0 ≤ localWeight κ Y ζ := by
            unfold localWeight
            exact Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
          positivity
        calc _ ≤ K * (1 + localWeight κ Y ζ) ^ 7 * 1 := mul_le_mul_of_nonneg_left h2 h3
          _ = _ := mul_one _)
  exact ⟨fun ζ _ => (key ζ).1, fun ζ _ j hj τ hτ => (key ζ).2 τ hτ j hj⟩
private theorem uniformC3_scale (hCh : MoveChart s V c X r Cc) (hOb : IsSmoothAtSmallCurvature s κ ρ l₁ K Y Ob)
    (hκ : 0 ≤ κ) (hK : 0 ≤ K) {l : ℝ} (hl : 0 < l) (hl₁ : l ≤ l₁) :
    UniformC3 (Metric.ball (0 : Fin k → ℝ) r) {ζ : StepVariable (finiteCells F) | MemScaledBalls ρ l ζ}
      (fun ζ => Cc * (K * (1 + localWeight κ Y ζ) ^ 7))
      (fun τ ζ => Ob l ζ (leftTranslate (bondSpread c X τ) V)) := by
  have hN : ∀ ζ, 0 ≤ K * (1 + localWeight κ Y ζ) ^ 7 := fun ζ => by
    have : 0 ≤ localWeight κ Y ζ := by
      unfold localWeight
      exact Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    positivity
  have key : ∀ ζ : StepVariable (finiteCells F), MemScaledBalls ρ l ζ → _ := fun ζ hζ =>
    hCh.chart (Ob l ζ) (K * (1 + localWeight κ Y ζ) ^ 7) (hN ζ)
      (fun τ hτ q c' X' _ => by
        have hb : MemScaledBalls ρ |l| ζ := by rwa [abs_of_pos hl]
        have h1 := (contDiffAt_scale_move (hOb _ (hCh.cold τ hτ)) hb c' X').of_le
          (m := ((3 : ℕ) : WithTop ℕ∞)) (by norm_num)
        have h2 : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun σ : Fin q → ℝ => ((l, σ) : ℝ × (Fin q → ℝ))) 0 := by
          fun_prop
        exact_mod_cast ContDiffAt.comp (0 : Fin q → ℝ) h1 h2)
      (fun τ hτ j c' X' hj hX' => by
        have hO := hOb _ (hCh.cold τ hτ)
        have h1 := hO.deriv_le j 0 c' X' l ζ (isControlledOrder_of_le hj (by norm_num)) hX' hl hl₁ hζ
        have h2 := exp_neg_span_le_one (Y := Y) hκ c'
        calc |bondDeriv (Ob l ζ) (leftTranslate (bondSpread c X τ) V) c' X'| ≤ _ := h1
          _ ≤ K * (1 + localWeight κ Y ζ) ^ 7 * 1 := mul_le_mul_of_nonneg_left h2 (hN ζ)
          _ = _ := mul_one _)
  exact ⟨fun ζ hζ => (key ζ hζ).1, fun ζ hζ j hj τ hτ => (key ζ hζ).2 τ hτ j hj⟩
end ObservableBounds
section PolynomialGrowth
variable {E P : Type} [NormedAddCommGroup E] [NormedAddCommGroup P] [NormedSpace ℝ P] {B : Set P}
  {G G₁ G₂ : P → E → ℝ}
private def PolyGrowthC3 (B : Set P) (G : P → E → ℝ) : Prop :=
  ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ UniformC3 B (univ : Set E) (fun ζ => C * (1 + ‖ζ‖) ^ m) G
private theorem one_le_one_add_norm (ζ : E) : (1 : ℝ) ≤ 1 + ‖ζ‖ := by linarith [norm_nonneg ζ]
private theorem PolyGrowthC3.of_uniform {W : E → ℝ} (h : UniformC3 B (univ : Set E) W G) {C : ℝ} {m : ℕ}
    (hC : 0 ≤ C) (hW : ∀ ζ, W ζ ≤ C * (1 + ‖ζ‖) ^ m) : PolyGrowthC3 B G :=
  ⟨C, m, hC, h.mono fun ζ _ => hW ζ⟩
private theorem PolyGrowthC3.add (hB : IsOpen B) (h₁ : PolyGrowthC3 B G₁) (h₂ : PolyGrowthC3 B G₂) :
    PolyGrowthC3 B fun s ζ => G₁ s ζ + G₂ s ζ := by
  obtain ⟨C₁, m₁, p₁, t₁⟩ := h₁
  obtain ⟨C₂, m₂, p₂, t₂⟩ := h₂
  refine PolyGrowthC3.of_uniform (t₁.add hB t₂) (C := C₁ + C₂) (m := m₁ + m₂) (by positivity) fun ζ => ?_
  have h1 := one_le_one_add_norm ζ
  have a₁ : (1 + ‖ζ‖) ^ m₁ ≤ (1 + ‖ζ‖) ^ (m₁ + m₂) := pow_le_pow_right₀ h1 (by omega)
  have a₂ : (1 + ‖ζ‖) ^ m₂ ≤ (1 + ‖ζ‖) ^ (m₁ + m₂) := pow_le_pow_right₀ h1 (by omega)
  calc _ ≤ C₁ * (1 + ‖ζ‖) ^ (m₁ + m₂) + C₂ * (1 + ‖ζ‖) ^ (m₁ + m₂) := by gcongr
    _ = _ := by ring
private theorem PolyGrowthC3.mul (hB : IsOpen B) (h₁ : PolyGrowthC3 B G₁) (h₂ : PolyGrowthC3 B G₂) :
    PolyGrowthC3 B fun s ζ => G₁ s ζ * G₂ s ζ := by
  obtain ⟨C₁, m₁, p₁, t₁⟩ := h₁
  obtain ⟨C₂, m₂, p₂, t₂⟩ := h₂
  have hp : ∀ (C : ℝ) (m : ℕ), 0 ≤ C → ∀ ζ : E, ζ ∈ (univ : Set E) → 0 ≤ C * (1 + ‖ζ‖) ^ m :=
    fun C m hC ζ _ => by positivity
  refine PolyGrowthC3.of_uniform (t₁.mul hB t₂ (hp C₁ m₁ p₁) (hp C₂ m₂ p₂)) (C := 8 * (C₁ * C₂))
    (m := m₁ + m₂) (by positivity) fun ζ => ?_
  rw [pow_add]
  exact le_of_eq (by ring)
private theorem PolyGrowthC3.sum {α : Type} (hB : IsOpen B) (I : Finset α) {Gs : α → P → E → ℝ}
    (h : ∀ a ∈ I, PolyGrowthC3 B (Gs a)) : PolyGrowthC3 B fun s ζ => ∑ a ∈ I, Gs a s ζ := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    have h0 := PolyGrowthC3.of_uniform (uniformC3_const (S := univ) B (fun _ : E => (0 : ℝ))) (C := 0) (m := 0)
      le_rfl fun ζ => by simp
    simpa using h0
  | insert a I ha ih =>
    have h1 := h a (Finset.mem_insert_self a I)
    have h2 := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    have h3 := h1.add hB h2
    simpa only [Finset.sum_insert ha] using h3
private theorem PolyGrowthC3.const (g : E → ℝ) {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hg : ∀ ζ, |g ζ| ≤ C * (1 + ‖ζ‖) ^ m) : PolyGrowthC3 B fun _ ζ => g ζ :=
  PolyGrowthC3.of_uniform (uniformC3_const B g) hC hg
private theorem PolyGrowthC3.param [FiniteDimensional ℝ P] {φ : P → ℝ} (hφ : ContDiff ℝ 3 φ) {r : ℝ} :
    PolyGrowthC3 (E := E) (Metric.ball (0 : P) r) fun s _ => φ s := by
  obtain ⟨C, hC, t⟩ := uniformC3_of_param (S := (univ : Set E)) hφ (r := r)
  exact PolyGrowthC3.of_uniform t (C := C) (m := 0) hC fun ζ => by simp
private theorem PolyGrowthC3.eval (h : PolyGrowthC3 B G) (ζ₀ : E) :
    PolyGrowthC3 (E := E) B fun s _ => G s ζ₀ := by
  obtain ⟨C, m, hC, t⟩ := h
  have t' : UniformC3 B (univ : Set E) (fun _ => C * (1 + ‖ζ₀‖) ^ m) fun s _ => G s ζ₀ :=
    ⟨fun _ _ => t.smooth ζ₀ trivial, fun _ _ j hj s hs => t.bound ζ₀ trivial j hj s hs⟩
  exact PolyGrowthC3.of_uniform t' (C := C * (1 + ‖ζ₀‖) ^ m) (m := 0) (by positivity) fun ζ => by simp
private theorem PolyGrowthC3.neg [FiniteDimensional ℝ P] {r : ℝ} (h : PolyGrowthC3 (Metric.ball (0 : P) r) G) :
    PolyGrowthC3 (Metric.ball (0 : P) r) fun s ζ => - G s ζ := by
  have h1 := (PolyGrowthC3.param (E := E) (φ := fun _ : P => (-1 : ℝ)) contDiff_const (r := r)).mul
    Metric.isOpen_ball h
  simpa using h1
private theorem PolyGrowthC3.sub [FiniteDimensional ℝ P] {r : ℝ} (h₁ : PolyGrowthC3 (Metric.ball (0 : P) r) G₁)
    (h₂ : PolyGrowthC3 (Metric.ball (0 : P) r) G₂) :
    PolyGrowthC3 (Metric.ball (0 : P) r) fun s ζ => G₁ s ζ - G₂ s ζ := by
  have h := h₁.add Metric.isOpen_ball h₂.neg
  simpa [sub_eq_add_neg] using h
private theorem PolyGrowthC3.congr {G' : P → E → ℝ} (hB : IsOpen B) (h : PolyGrowthC3 B G)
    (e : ∀ s ∈ B, ∀ ζ, G' s ζ = G s ζ) : PolyGrowthC3 B G' := by
  obtain ⟨C, m, hC, t⟩ := h
  exact ⟨C, m, hC, t.congr hB fun ζ _ s hs => e s hs ζ⟩
end PolynomialGrowth
private theorem contDiffOn_confiningMean {ι : Type} [Fintype ι] {n : ℕ} (hMC : ConfiningGibbsMeanContDiff)
    {B : Set (Fin n → ℝ)} (hB : IsOpen B) {c : ℝ} (hc : 0 < c)
    {A H : (Fin n → ℝ) → BondField ι → ℝ} (pA : PolyGrowthC3 B A) (pH : PolyGrowthC3 B H)
    (mA : ∀ s ∈ B, Measurable (A s)) (mH : ∀ s ∈ B, Measurable (H s))
    (floor : ∀ s ∈ B, ∀ ζ, c * ‖ζ‖ ^ 2 ≤ A s ζ) :
    ContDiffOn ℝ 3 (fun s => (∫ ζ, H s ζ * Real.exp (- A s ζ)) / ∫ ζ, Real.exp (- A s ζ)) B := by
  obtain ⟨C₁, m₁, p₁, t₁⟩ := pA
  obtain ⟨C₂, m₂, p₂, t₂⟩ := pH
  have key : ∀ (C : ℝ) (m : ℕ) (ζ : BondField ι), 0 ≤ C → C ≤ C₁ + C₂ → m ≤ m₁ + m₂ →
      C * (1 + ‖ζ‖) ^ m ≤ (C₁ + C₂) * (1 + ‖ζ‖) ^ (m₁ + m₂) := by
    intro C m ζ h0 h1 h2
    have : (1 + ‖ζ‖) ^ m ≤ (1 + ‖ζ‖) ^ (m₁ + m₂) := pow_le_pow_right₀ (one_le_one_add_norm ζ) h2
    gcongr
  refine hMC ι n (m₁ + m₂) B c (C₁ + C₂) A H hB hc ⟨mA, fun ζ => t₁.smooth ζ trivial, ?_⟩
    ⟨mH, fun ζ => t₂.smooth ζ trivial, ?_⟩ floor
  · intro ζ j hj s hs
    exact (t₁.bound ζ trivial j hj s hs).trans (key C₁ m₁ ζ p₁ (by linarith) (by omega))
  · intro ζ j hj s hs
    exact (t₂.bound ζ trivial j hj s hs).trans (key C₂ m₂ ζ p₂ (by linarith) (by omega))
section LawExponents
variable {F : BlockFrame}
private def halfSquare (lam : ℝ) (ζ : StepVariable (finiteCells F)) : ℝ :=
  lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2
private def remainderSum (a ρ lam l : ℝ) (V : F.GaugeField F.top) (ζ : StepVariable (finiteCells F)) : ℝ :=
  ∑ Y ∈ finiteCells F, rescaledCellRemainder a ρ lam l Y V ζ
private def expansionTotal (a ρ : ℝ) (f : LocalFamily) (l : ℝ) (V : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) : ℝ :=
  ∑ Y ∈ finiteCells F, rescaledCellExpansion a ρ f l Y V ζ
private theorem mem_finiteCells (hfin : Finite F.Cell) (Y : F.Cell) : Y ∈ finiteCells F := by apply _root_.YangMills.SharedProofs.p8277 <;> assumption
private theorem sum_cells_indicator (hfin : Finite F.Cell) (g : ↥(chordBonds (finiteCells F)) → ℝ) :
    ∑ Y ∈ finiteCells F, ∑ b : ↥(chordBonds (finiteCells F)),
      (if enclosingCell b.1.1 = Y then g b else 0) = ∑ b, g b := by apply _root_.YangMills.SharedProofs.p35694 <;> assumption
private theorem sum_rescaledCellTerm (hfin : Finite F.Cell) (a ρ lam l : ℝ) (V : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) :
    ∑ Y ∈ finiteCells F, rescaledCellTerm a ρ l Y V ζ = remainderSum a ρ lam l V ζ + halfSquare lam ζ := by
  have h1 := sum_cells_indicator hfin fun b => ‖ζ b‖ ^ 2
  simp only [remainderSum, rescaledCellRemainder, halfSquare, Finset.sum_sub_distrib, ← Finset.mul_sum, h1]
  ring
private theorem sum_centredExpansion (hfin : Finite F.Cell) (a ρ : ℝ) (f : LocalFamily) (l : ℝ)
    (V : F.GaugeField F.top) (ζ : StepVariable (finiteCells F)) :
    ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion true a ρ 0 f y (l • ζ) V = expansionTotal a ρ f l V ζ := by
  classical
  simp only [expansionTotal, rescaledCellExpansion, cellCentredExpansion]
  rw [Finset.sum_fiberwise_of_maps_to (fun y _ => mem_finiteCells hfin (enclosingCell y))]
private theorem lawExponent_tilted (hfin : Finite F.Cell) (a ρ lam : ℝ) (f : LocalFamily) (ν l : ℝ)
    (V : F.GaugeField F.top) (ζ : StepVariable (finiteCells F)) :
    rescaledLawExponent a ρ lam f l V (.tilted ν) ζ =
      halfSquare lam ζ + 1 * remainderSum a ρ lam l V ζ - ν * expansionTotal a ρ f l V ζ := by
  simp only [rescaledLawExponent, rescaledExponent]
  rw [sum_rescaledCellTerm hfin a ρ lam, sum_centredExpansion hfin]
  ring
private theorem lawExponent_interpolated (hfin : Finite F.Cell) (a ρ lam : ℝ) (f : LocalFamily) (τ l : ℝ)
    (V : F.GaugeField F.top) (ζ : StepVariable (finiteCells F)) :
    rescaledLawExponent a ρ lam f l V (.interpolated τ) ζ =
      halfSquare lam ζ + τ * remainderSum a ρ lam l V ζ - 0 * expansionTotal a ρ f l V ζ := by
  simp only [rescaledLawExponent, rescaledExponent]
  rw [sum_rescaledCellTerm hfin a ρ lam, sum_centredExpansion hfin]
  simp only [halfSquare]
  ring
private theorem sum_secondDerivAlong_bondVariation {Ψ : StepVariable (finiteCells F) → ℝ} (h : ContDiffAt ℝ 2 Ψ 0)
    (ζ : StepVariable (finiteCells F)) :
    ∑ b : ↥(chordBonds (finiteCells F)), secondDerivAlong Ψ 0 (bondVariation b (ζ b)) ζ =
      secondDerivAlong Ψ 0 ζ ζ := by
  have hf : ContDiffAt ℝ 1 (fderiv ℝ Ψ) 0 := h.fderiv_right (m := 1) (by norm_num)
  have hd : ∀ u : StepVariable (finiteCells F), DifferentiableAt ℝ (fun ζ' => fderiv ℝ Ψ ζ' u) 0 := fun u =>
    (hf.differentiableAt (by norm_num)).clm_apply (differentiableAt_const u)
  have hs : ζ = ∑ b : ↥(chordBonds (finiteCells F)), bondVariation b (ζ b) := by
    funext x
    simp [bondVariation, Finset.sum_apply, Pi.single_apply]
  unfold secondDerivAlong
  have e : (fun ζ' => fderiv ℝ Ψ ζ' ζ) =
      fun ζ' => ∑ b : ↥(chordBonds (finiteCells F)), fderiv ℝ Ψ ζ' (bondVariation b (ζ b)) := by
    funext ζ'
    rw [← map_sum, ← hs]
  rw [e, fderiv_fun_sum fun b _ => hd _]
  simp
private theorem integral_one_sub_mul (C : ℝ) : ∫ v in (0 : ℝ)..1, (1 - v) * C = 1 / 2 * C := by
  rw [intervalIntegral.integral_mul_const]
  congr 1
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (show IntervalIntegrable (fun x : ℝ => x) volume 0 1 from continuous_id.intervalIntegrable 0 1)]
  simp only [intervalIntegral.integral_const, integral_id]
  norm_num
private theorem rescaledCellTerm_sub_zero (a ρ : ℝ) (Y : F.Cell) (V : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) :
    rescaledCellTerm a ρ 0 Y V ζ - rescaledCellTerm a ρ 0 Y V 0 =
      ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
        1 / 2 * secondDerivAlong (chartedEnergyAtMinimizer a ρ V) 0 (bondVariation b (ζ b)) ζ else 0 := by
  simp only [rescaledCellTerm, mul_zero, zero_smul, integral_one_sub_mul]
  have h0 : ∀ b : ↥(chordBonds (finiteCells F)), secondDerivAlong (chartedEnergyAtMinimizer a ρ V) 0
      (bondVariation b ((0 : StepVariable (finiteCells F)) b)) 0 = 0 := fun b => by
    simp [secondDerivAlong]
  simp only [h0, mul_zero, ite_self, Finset.sum_const_zero]
  ring
private def gaussianExponent (a ρ lam : ℝ) (f : LocalFamily) (law : StepLaw) (V : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) : ℝ :=
  rescaledLawExponent a ρ lam f 0 V law ζ - rescaledLawExponent a ρ lam f 0 V law 0
private theorem gaussianExponent_eq {a ρ lam : ℝ} {f : LocalFamily} {law : StepLaw} {V : F.GaugeField F.top}
    {α β : ℝ}
    (h : ∀ ζ : StepVariable (finiteCells F), rescaledLawExponent a ρ lam f 0 V law ζ =
      halfSquare lam ζ + α * remainderSum a ρ lam 0 V ζ - β * expansionTotal a ρ f 0 V ζ)
    (ζ : StepVariable (finiteCells F)) :
    gaussianExponent a ρ lam f law V ζ =
      halfSquare lam ζ + α * (remainderSum a ρ lam 0 V ζ - remainderSum a ρ lam 0 V 0) := by
  have e : expansionTotal a ρ f 0 V ζ = expansionTotal a ρ f 0 V 0 := by simp [expansionTotal, rescaledCellExpansion]
  have e₀ : halfSquare lam (0 : StepVariable (finiteCells F)) = 0 := by simp [halfSquare]
  rw [gaussianExponent, h, h, e, e₀]
  ring
private theorem remainderSum_sub_nonneg (hfin : Finite F.Cell) {a ρ lam : ℝ} {V : F.GaugeField F.top}
    (hS : ContDiffAt ℝ 2 (chartedEnergyAtMinimizer a ρ V) 0)
    (hq : ∀ u : StepVariable (finiteCells F),
      lam * ∑ b, ‖u b‖ ^ 2 ≤ secondDerivAlong (chartedEnergyAtMinimizer a ρ V) 0 u u)
    (ζ : StepVariable (finiteCells F)) :
    0 ≤ remainderSum a ρ lam 0 V ζ - remainderSum a ρ lam 0 V 0 := by
  have h1 := sum_rescaledCellTerm hfin a ρ lam 0 V ζ
  have h2 := sum_rescaledCellTerm hfin a ρ lam 0 V 0
  have e₀ : halfSquare lam (0 : StepVariable (finiteCells F)) = 0 := by simp [halfSquare]
  have h3 : ∑ Y ∈ finiteCells F, rescaledCellTerm a ρ 0 Y V ζ - ∑ Y ∈ finiteCells F, rescaledCellTerm a ρ 0 Y V 0 =
      1 / 2 * secondDerivAlong (chartedEnergyAtMinimizer a ρ V) 0 ζ ζ := by
    rw [← Finset.sum_sub_distrib]
    simp only [rescaledCellTerm_sub_zero]
    rw [sum_cells_indicator hfin, ← Finset.mul_sum, sum_secondDerivAlong_bondVariation hS]
  have h4 := hq ζ
  simp only [halfSquare] at h1 h2 e₀ ⊢
  rw [e₀] at h2
  nlinarith
private theorem halfSquare_ge {lam : ℝ} (hlam : 0 < lam) (ζ : StepVariable (finiteCells F)) :
    lam / 2 * ‖ζ‖ ^ 2 ≤ halfSquare lam ζ := by
  have h1 : ‖ζ‖ ≤ Real.sqrt (∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun b => ?_
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun b => ‖ζ b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ b)
  have h2 : ‖ζ‖ ^ 2 ≤ ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg ζ) h1 2
    rwa [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)] at this
  unfold halfSquare
  gcongr
private theorem abs_halfSquare_le (lam : ℝ) (ζ : StepVariable (finiteCells F)) :
    |halfSquare lam ζ| ≤
      (|lam| / 2 * (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ)) * (1 + ‖ζ‖) ^ 2 := by
  have h1 : ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2 ≤
      (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ) * (1 + ‖ζ‖) ^ 2 := by
    calc ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2
        ≤ ∑ _b : ↥(chordBonds (finiteCells F)), (1 + ‖ζ‖) ^ 2 := by
          refine Finset.sum_le_sum fun b _ => ?_
          have := norm_le_pi_norm ζ b
          have h0 := norm_nonneg (ζ b)
          gcongr
          linarith
      _ = _ := by simp
  have h2 : 0 ≤ ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  unfold halfSquare
  rw [abs_mul, abs_div, abs_of_nonneg h2, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc |lam| / 2 * _ ≤ |lam| / 2 * ((Fintype.card ↥(chordBonds (finiteCells F)) : ℝ) * (1 + ‖ζ‖) ^ 2) := by
        gcongr
    _ = _ := by ring
end LawExponents
section TailParameters
private def tailProj (k : ℕ) : (Fin (k + 1) → ℝ) →L[ℝ] Fin k → ℝ :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ
private theorem tailProj_norm_le (k : ℕ) : ‖tailProj k‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun s => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg s)).2 fun i => ?_
  exact norm_le_pi_norm s i.succ
private theorem tailProj_mem_ball {k : ℕ} {r : ℝ} {s : Fin (k + 1) → ℝ}
    (hs : s ∈ Metric.ball (0 : Fin (k + 1) → ℝ) r) : tailProj k s ∈ Metric.ball (0 : Fin k → ℝ) r := by
  rw [mem_ball_zero_iff] at hs ⊢
  calc ‖tailProj k s‖ ≤ ‖tailProj k‖ * ‖s‖ := (tailProj k).le_opNorm s
    _ ≤ 1 * ‖s‖ := by gcongr; exact tailProj_norm_le k
    _ < r := by simpa using hs
private theorem contDiff_shifted_sq {k : ℕ} (u₀ : ℝ) :
    ContDiff ℝ 3 fun s : Fin (k + 1) → ℝ => (u₀ + s 0) ^ 2 :=
  (contDiff_const.add (contDiff_apply ℝ ℝ (0 : Fin (k + 1)))).pow 2
variable {F : BlockFrame}
private theorem weightMoveFamily_contDiffAt_of_param {M : ℝ → F.GaugeField F.top → ℝ} {V : F.GaugeField F.top}
    {u₀ : ℝ} {k : ℕ} {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {r : ℝ} (hr : 0 < r)
    (h : ContDiffOn ℝ 3 (fun s : Fin (k + 1) → ℝ =>
      M ((u₀ + s 0) ^ 2) (leftTranslate (bondSpread c X (tailProj k s)) V)) (Metric.ball 0 r)) :
    ContDiffAt ℝ 3 (weightMoveFamily M V c X) (u₀, 0) := by
  set Lv : ℝ × (Fin k → ℝ) → Fin (k + 1) → ℝ := fun q => Fin.cons (q.1 - u₀) q.2 with hLv
  have hLs : ContDiff ℝ 3 Lv := by
    refine contDiff_pi.mpr fun i => ?_
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [hLv] using (contDiff_fst.sub contDiff_const : ContDiff ℝ 3 fun q : ℝ × (Fin k → ℝ) => q.1 - u₀)
    · have hi : ContDiff ℝ 3 fun q : ℝ × (Fin k → ℝ) => q.2 i := (contDiff_apply ℝ ℝ i).comp contDiff_snd
      simpa [hLv] using hi
  have hL0 : Lv (u₀, 0) = 0 := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [hLv]
  have hNa := h.contDiffAt (Metric.ball_mem_nhds _ hr)
  have hcomp := ContDiffAt.comp (f := Lv) ((u₀, 0) : ℝ × (Fin k → ℝ))
    (by rw [hL0]; exact hNa : ContDiffAt ℝ 3 _ (Lv (u₀, 0))) hLs.contDiffAt
  refine hcomp.congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
  have e₁ : tailProj k (Lv q) = q.2 := by
    funext i
    simp [tailProj, hLv]
  have e₂ : u₀ + Lv q 0 = q.1 := by simp [hLv]
  simp only [weightMoveFamily, Function.comp, e₁, e₂]
end TailParameters
section SmallCurvature
variable {F : BlockFrame}
private theorem leftTranslate_bondSpread_zero {j k : ℕ} (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) (W : F.GaugeField j) :
    leftTranslate (bondSpread c X 0) W = W := by apply _root_.YangMills.SharedProofs.p1939 <;> assumption
private theorem eventually_isSmallCurvature {k : ℕ} (hF : ∀ i, F.extent i ≠ 0) (s : ℝ) (V : F.GaugeField F.top)
    (hV : IsSmallCurvature s V) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), IsSmallCurvature s (leftTranslate (bondSpread c X τ) V) := by apply _root_.YangMills.SharedProofs.p8866 <;> assumption
private theorem exists_moveChart (hC : ContDiffBoundOnParameterBall) (hF : ∀ i, F.extent i ≠ 0) {s : ℝ}
    {V : F.GaugeField F.top} (hV : IsSmallCurvature s V) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    ∃ r Cc : ℝ, MoveChart s V c X r Cc := by
  obtain ⟨r₀, C, hr₀, hC0, g⟩ := hC F F.top k c X
  obtain ⟨r₁, hr₁, hb⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_isSmallCurvature hF s V hV c X)
  refine ⟨min r₀ r₁, C, lt_min hr₀ hr₁, hC0, fun G D hD a b =>
    g (min r₀ r₁) (lt_min hr₀ hr₁) (min_le_left _ _) V G D hD a b, fun τ hτ => hb τ ?_⟩
  exact Metric.ball_subset_ball (min_le_right _ _) hτ
private theorem bondDeriv_fin_zero (G : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G V c X = G V := by apply _root_.YangMills.SharedProofs.p1654 <;> assumption
variable {κ ρ l₁ K : ℝ} {Y : F.Cell} {V : F.GaugeField F.top}
  {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
private theorem continuous_scaleJet (h : IsSmoothObservable κ ρ l₁ K Y V Ob) (hl : 0 < l₁) (hρ : 0 < ρ) {i : ℕ}
    (hi : i ≤ 2) : Continuous fun ζ => scaleJet Ob i ζ V := by
  have e : ∀ ζ, scaleJet Ob i ζ V =
      scaleDeriv Ob V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) i ζ 0 := by
    intro ζ
    simp only [scaleJet, scaleDeriv, bondDeriv_fin_zero]
  refine continuous_iff_continuousAt.2 fun ζ₀ => ?_
  have hc := h.continuousOn 0 i Fin.elim0 Fin.elim0 (‖ζ₀‖ + 1) (Or.inl ⟨by norm_num, hi⟩)
  have hin : ((0 : ℝ), ζ₀) ∈ {q : ℝ × StepVariable (finiteCells F) | 0 ≤ q.1 ∧ q.1 ≤ l₁ ∧
      MemScaledBalls ρ q.1 q.2 ∧ ∀ b, ‖q.2 b‖ ≤ ‖ζ₀‖ + 1} :=
    ⟨le_rfl, hl.le, fun b => by simpa using hρ, fun b => (norm_le_pi_norm ζ₀ b).trans (by linarith)⟩
  have h1 := hc _ hin
  have h2 : ContinuousAt (fun ζ : StepVariable (finiteCells F) => ((0 : ℝ), ζ)) ζ₀ := by fun_prop
  have hmem : ∀ᶠ ζ in 𝓝 ζ₀, ((0 : ℝ), ζ) ∈ {q : ℝ × StepVariable (finiteCells F) | 0 ≤ q.1 ∧ q.1 ≤ l₁ ∧
      MemScaledBalls ρ q.1 q.2 ∧ ∀ b, ‖q.2 b‖ ≤ ‖ζ₀‖ + 1} := by
    filter_upwards [Metric.ball_mem_nhds ζ₀ one_pos] with ζ hζ
    refine ⟨le_rfl, hl.le, fun b => by simpa using hρ, fun b => (norm_le_pi_norm ζ b).trans ?_⟩
    have := dist_eq_norm ζ ζ₀ ▸ (Metric.mem_ball.1 hζ).le
    linarith [norm_le_insert' ζ ζ₀]
  have h3 := ContinuousWithinAt.tendsto h1
  have h4 : Tendsto (fun ζ : StepVariable (finiteCells F) => ((0 : ℝ), ζ)) (𝓝 ζ₀)
      (𝓝[{q : ℝ × StepVariable (finiteCells F) | 0 ≤ q.1 ∧ q.1 ≤ l₁ ∧ MemScaledBalls ρ q.1 q.2 ∧
        ∀ b, ‖q.2 b‖ ≤ ‖ζ₀‖ + 1}] ((0 : ℝ), ζ₀)) :=
    tendsto_nhdsWithin_iff.2 ⟨h2.tendsto, hmem⟩
  have h5 := h3.comp h4
  simp only [e]
  exact h5
private theorem contDiffAt_scale (h : IsSmoothObservable κ ρ l₁ K Y V Ob) (hρ : 0 < ρ)
    (ζ : StepVariable (finiteCells F)) {i : ℕ} (hi : i ≤ 6) :
    ContDiffAt ℝ (i : WithTop ℕ∞) (fun l => Ob l ζ V) 0 := by
  have h1 := (contDiffAt_scale_move h (memScaledBalls_zero hρ ζ) (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
    (Fin.elim0 : Fin 0 → imaginaryQuaternions)).of_le (m := (i : WithTop ℕ∞)) (by exact_mod_cast hi)
  have h2 : ContDiffAt ℝ (i : WithTop ℕ∞) (fun l : ℝ => ((l, 0) : ℝ × (Fin 0 → ℝ))) 0 := by fun_prop
  have h3 := ContDiffAt.comp (0 : ℝ) h1 h2
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun l => ?_)
  simp only [Function.comp, leftTranslate_bondSpread_zero]
private theorem continuousOn_observable (h : IsSmoothObservable κ ρ l₁ K Y V Ob) {l : ℝ} (hl : 0 < l) :
    ContinuousOn (fun ζ => Ob l ζ V) {ζ | MemScaledBalls ρ l ζ} := by
  intro ζ hζ
  have hb : MemScaledBalls ρ |l| ζ := by rwa [abs_of_pos hl]
  have h1 := h.contDiffAt l ζ 0 Fin.elim0 Fin.elim0 hb
  have h2 : ContinuousAt (fun ζ' : StepVariable (finiteCells F) =>
      (((l, ζ'), 0) : (ℝ × StepVariable (finiteCells F)) × (Fin 0 → ℝ))) ζ := by
    fun_prop
  have h3 := ContinuousAt.comp (f := fun ζ' : StepVariable (finiteCells F) =>
      (((l, ζ'), 0) : (ℝ × StepVariable (finiteCells F)) × (Fin 0 → ℝ)))
    (g := fun q : (ℝ × StepVariable (finiteCells F)) × (Fin 0 → ℝ) =>
      Ob q.1.1 q.1.2 (leftTranslate (bondSpread Fin.elim0 Fin.elim0 q.2) V)) h1.continuousAt h2
  simp only [Function.comp_def, leftTranslate_bondSpread_zero] at h3
  exact h3.continuousWithinAt
end SmallCurvature
section GaussianMeans
variable {F : BlockFrame} {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {l₁ KS K : ℝ} {f : LocalFamily} {Y : F.Cell}
  {V : F.GaugeField F.top} {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
private structure MeanData (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (l₁ KS : ℝ) (f : LocalFamily) (F : BlockFrame) : Prop where
  ρ_pos : 0 < T.ballRadius
  κ_pos : 0 ≤ T.κ
  l₁_pos : 0 < l₁
  KS_pos : 0 ≤ KS
  lam_pos : 0 < T.lam
  fin : Finite F.Cell
  remainder : ∀ Y : F.Cell, IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius l₁ KS Y
    (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ)
  row : ∀ Y : F.Cell, IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius l₁ KS Y
    (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ)
  second : ∀ V' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' →
    ContDiffAt ℝ 2 (chartedEnergyAtMinimizer T.a T.ρA V') 0 ∧ ∀ u : StepVariable (finiteCells F),
      T.lam * ∑ b, ‖u b‖ ^ 2 ≤ secondDerivAlong (chartedEnergyAtMinimizer T.a T.ρA V') 0 u u
private structure LawKind (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (f : LocalFamily) (F : BlockFrame) (kind : ℝ → StepLaw)
    (α β : ℝ → ℝ) : Prop where
  smooth_α : ContDiff ℝ 3 α
  smooth_β : ContDiff ℝ 3 β
  nonneg : ∀ u : ℝ, 0 ≤ α (u ^ 2)
  law : ∀ (θ l : ℝ) (V : F.GaugeField F.top) (ζ : StepVariable (finiteCells F)),
    rescaledLawExponent T.a T.ρA T.lam f l V (kind θ) ζ =
      halfSquare T.lam ζ + α θ * remainderSum T.a T.ρA T.lam l V ζ - β θ * expansionTotal T.a T.ρA f l V ζ
variable {s : ℝ} {k : ℕ} {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {r Cc : ℝ}
private theorem polyGrowth_scaleJet (hL : DerivAlongRulesHold) (hCh : MoveChart s V c X r Cc) {κ ρ : ℝ}
    (hOb : IsSmoothAtSmallCurvature s κ ρ l₁ K Y Ob) (hl : 0 < l₁) (hρ : 0 < ρ) (hκ : 0 ≤ κ) (hK : 0 ≤ K)
    {i : ℕ} (hi : i ≤ 2) :
    PolyGrowthC3 (Metric.ball (0 : Fin (k + 1) → ℝ) r)
      fun t ζ => scaleJet Ob i ζ (leftTranslate (bondSpread c X (tailProj k t)) V) := by
  have t₀ := (uniformC3_scaleJet hL hCh hOb hl hρ hκ hK hi).along (tailProj k) (tailProj_norm_le k)
    Metric.isOpen_ball (B' := Metric.ball (0 : Fin (k + 1) → ℝ) r) (fun _ hs => tailProj_mem_ball hs)
  have hCc := hCh.nonneg
  refine PolyGrowthC3.of_uniform t₀ (C := Cc * (K * (1 + (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ)) ^ 7))
    (m := 7) (by positivity) fun ζ => ?_
  have h1 := one_add_localWeight_pow_le (Y := Y) hκ ζ
  calc Cc * (K * (1 + localWeight κ Y ζ) ^ 7)
      ≤ Cc * (K * ((1 + (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ)) ^ 7 * (1 + ‖ζ‖) ^ 7)) := by gcongr
    _ = _ := by ring
private theorem measurable_scaleJet (hCh : MoveChart s V c X r Cc) {κ ρ : ℝ}
    (hOb : IsSmoothAtSmallCurvature s κ ρ l₁ K Y Ob) (hl : 0 < l₁) (hρ : 0 < ρ) {i : ℕ} (hi : i ≤ 2)
    {t : Fin (k + 1) → ℝ} (ht : t ∈ Metric.ball (0 : Fin (k + 1) → ℝ) r) :
    Measurable fun ζ => scaleJet Ob i ζ (leftTranslate (bondSpread c X (tailProj k t)) V) :=
  (continuous_scaleJet (hOb _ (hCh.cold _ (tailProj_mem_ball ht))) hl hρ hi).measurable
private theorem polyGrowth_remainder (hL : DerivAlongRulesHold) (hCh : MoveChart (5 / 4 * T.σ) V c X r Cc)
    (D : MeanData T l₁ KS f F) {i : ℕ} (hi : i ≤ 2) :
    PolyGrowthC3 (Metric.ball (0 : Fin (k + 1) → ℝ) r) fun t ζ => ∑ Y ∈ finiteCells F,
      scaleJet (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) i ζ
        (leftTranslate (bondSpread c X (tailProj k t)) V) :=
  PolyGrowthC3.sum Metric.isOpen_ball _ fun Y _ =>
    polyGrowth_scaleJet hL hCh (D.remainder Y) D.l₁_pos D.ρ_pos D.κ_pos D.KS_pos hi
private theorem polyGrowth_expansion (hL : DerivAlongRulesHold) (hCh : MoveChart (5 / 4 * T.σ) V c X r Cc)
    (D : MeanData T l₁ KS f F) {i : ℕ} (hi : i ≤ 2) :
    PolyGrowthC3 (Metric.ball (0 : Fin (k + 1) → ℝ) r) fun t ζ => ∑ Y ∈ finiteCells F,
      scaleJet (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ) i ζ
        (leftTranslate (bondSpread c X (tailProj k t)) V) :=
  PolyGrowthC3.sum Metric.isOpen_ball _ fun Y _ =>
    polyGrowth_scaleJet hL hCh (D.row Y) D.l₁_pos D.ρ_pos D.κ_pos D.KS_pos hi
private theorem gaussianExponent_confining (hL : DerivAlongRulesHold) (hCh : MoveChart (5 / 4 * T.σ) V c X r Cc)
    (D : MeanData T l₁ KS f F) {kind : ℝ → StepLaw} {α β : ℝ → ℝ} (hk : LawKind T f F kind α β) (u₀ : ℝ) :
    PolyGrowthC3 (Metric.ball (0 : Fin (k + 1) → ℝ) r)
        (fun t ζ => gaussianExponent T.a T.ρA T.lam f (kind ((u₀ + t 0) ^ 2))
          (leftTranslate (bondSpread c X (tailProj k t)) V) ζ) ∧
      (∀ t ∈ Metric.ball (0 : Fin (k + 1) → ℝ) r, Measurable fun ζ =>
        gaussianExponent T.a T.ρA T.lam f (kind ((u₀ + t 0) ^ 2))
          (leftTranslate (bondSpread c X (tailProj k t)) V) ζ) ∧
      ∀ t ∈ Metric.ball (0 : Fin (k + 1) → ℝ) r, ∀ ζ : StepVariable (finiteCells F), T.lam / 2 * ‖ζ‖ ^ 2 ≤
        gaussianExponent T.a T.ρA T.lam f (kind ((u₀ + t 0) ^ 2))
          (leftTranslate (bondSpread c X (tailProj k t)) V) ζ := by
  have hB : IsOpen (Metric.ball (0 : Fin (k + 1) → ℝ) r) := Metric.isOpen_ball
  have eqB : ∀ (V' : F.GaugeField F.top) (ζ : StepVariable (finiteCells F)),
      remainderSum T.a T.ρA T.lam 0 V' ζ =
        ∑ Y ∈ finiteCells F, scaleJet (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) 0 ζ V' := by
    intro V' ζ
    simp [remainderSum, scaleJet]
  have eqA : ∀ t ζ, gaussianExponent T.a T.ρA T.lam f (kind ((u₀ + t 0) ^ 2))
      (leftTranslate (bondSpread c X (tailProj k t)) V) ζ =
      halfSquare T.lam ζ + α ((u₀ + t 0) ^ 2) *
        (remainderSum T.a T.ρA T.lam 0 (leftTranslate (bondSpread c X (tailProj k t)) V) ζ -
          remainderSum T.a T.ρA T.lam 0 (leftTranslate (bondSpread c X (tailProj k t)) V) 0) := fun t ζ =>
    gaussianExponent_eq (fun ζ' => hk.law _ 0 _ ζ') ζ
  have pB := polyGrowth_remainder hL hCh D (i := 0) (by norm_num)
  simp only [← eqB] at pB
  have pQ : PolyGrowthC3 (Metric.ball (0 : Fin (k + 1) → ℝ) r)
      fun (_ : Fin (k + 1) → ℝ) ζ => halfSquare (F := F) T.lam ζ :=
    PolyGrowthC3.const _ (by positivity) (abs_halfSquare_le T.lam)
  have pα : PolyGrowthC3 (E := StepVariable (finiteCells F)) (Metric.ball (0 : Fin (k + 1) → ℝ) r)
      fun t _ => α ((u₀ + t 0) ^ 2) := PolyGrowthC3.param (hk.smooth_α.comp (contDiff_shifted_sq u₀))
  refine ⟨?_, fun t ht => ?_, fun t ht ζ => ?_⟩
  · have h := pQ.add hB (pα.mul hB (pB.sub (pB.eval 0)))
    simp only [← eqA] at h
    exact h
  · have hc : Continuous fun ζ : StepVariable (finiteCells F) =>
        remainderSum T.a T.ρA T.lam 0 (leftTranslate (bondSpread c X (tailProj k t)) V) ζ := by
      simp only [eqB]
      exact continuous_finset_sum _ fun Y _ =>
        continuous_scaleJet (D.remainder Y _ (hCh.cold _ (tailProj_mem_ball ht))) D.l₁_pos D.ρ_pos (by norm_num)
    have hq : Continuous fun ζ : StepVariable (finiteCells F) => halfSquare T.lam ζ := by
      unfold halfSquare
      fun_prop
    simp only [eqA]
    exact (hq.add (continuous_const.mul (hc.sub continuous_const))).measurable
  · rw [eqA]
    obtain ⟨h₁, h₂⟩ := D.second _ (hCh.cold _ (tailProj_mem_ball ht))
    have h₃ := remainderSum_sub_nonneg D.fin h₁ h₂ ζ
    have h₄ := halfSquare_ge (F := F) D.lam_pos ζ
    have h₅ := hk.nonneg (u₀ + t 0)
    have := mul_nonneg h₅ h₃
    linarith
private theorem contDiffOn_gaussianMean (hMC : ConfiningGibbsMeanContDiff) (hL : DerivAlongRulesHold)
    (hCh : MoveChart (5 / 4 * T.σ) V c X r Cc) (D : MeanData T l₁ KS f F) {kind : ℝ → StepLaw} {α β : ℝ → ℝ}
    (hk : LawKind T f F kind α β) (u₀ : ℝ) {H : (Fin (k + 1) → ℝ) → StepVariable (finiteCells F) → ℝ}
    (pH : PolyGrowthC3 (Metric.ball (0 : Fin (k + 1) → ℝ) r) H)
    (mH : ∀ t ∈ Metric.ball (0 : Fin (k + 1) → ℝ) r, Measurable (H t)) :
    ContDiffOn ℝ 3 (fun t => gaussianMean T.a T.ρA T.lam f (leftTranslate (bondSpread c X (tailProj k t)) V)
      (kind ((u₀ + t 0) ^ 2)) (H t)) (Metric.ball 0 r) := by
  obtain ⟨pA, mA, floor⟩ := gaussianExponent_confining hL hCh D hk u₀ (k := k) (c := c) (X := X)
  have hc : 0 < T.lam / 2 := by linarith [D.lam_pos]
  exact contDiffOn_confiningMean hMC Metric.isOpen_ball hc pA pH mA mH floor
private theorem contDiffAt_gaussianWeightFamily (hMC : ConfiningGibbsMeanContDiff) (hL : DerivAlongRulesHold)
    (hCh : MoveChart (5 / 4 * T.σ) V c X r Cc) (D : MeanData T l₁ KS f F) {kind : ℝ → StepLaw} {α β : ℝ → ℝ}
    (hk : LawKind T f F kind α β) (hOb : IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius l₁ K Y Ob)
    (hK : 0 ≤ K) (u₀ : ℝ) :
    ContDiffAt ℝ 3 (weightMoveFamily (fun θ => observableGaussianMean T.a T.ρA T.lam f (kind θ) Ob) V c X)
      (u₀, 0) := by
  refine weightMoveFamily_contDiffAt_of_param hCh.pos ?_
  have h := contDiffOn_gaussianMean hMC hL hCh D hk u₀
    (H := fun t ζ => scaleJet Ob 0 ζ (leftTranslate (bondSpread c X (tailProj k t)) V))
    (polyGrowth_scaleJet hL hCh hOb D.l₁_pos D.ρ_pos D.κ_pos hK (by norm_num))
    (fun t ht => measurable_scaleJet hCh hOb D.l₁_pos D.ρ_pos (by norm_num) ht)
  refine h.congr fun t _ => ?_
  simp [observableGaussianMean, scaleJet]
private theorem taylorCoeff_lawExponent (D : MeanData T l₁ KS f F) {kind : ℝ → StepLaw} {α β : ℝ → ℝ}
    (hk : LawKind T f F kind α β) {V' : F.GaugeField F.top} (hV' : IsSmallCurvature (5 / 4 * T.σ) V') (θ : ℝ)
    (ζ : StepVariable (finiteCells F)) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ 2) :
    taylorCoeffAtZero i (fun l => rescaledLawExponent T.a T.ρA T.lam f l V' (kind θ) ζ) =
      (α θ * ∑ Y ∈ finiteCells F, scaleJet (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) i ζ V' -
        β θ * ∑ Y ∈ finiteCells F, scaleJet (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ) i ζ V') /
          (i.factorial : ℝ) := by
  have hfun : (fun l => rescaledLawExponent T.a T.ρA T.lam f l V' (kind θ) ζ) =
      fun l => (halfSquare T.lam ζ + α θ * remainderSum T.a T.ρA T.lam l V' ζ) -
        β θ * expansionTotal T.a T.ρA f l V' ζ :=
    funext fun l => hk.law θ l V' ζ
  have hb : ∀ Y ∈ finiteCells F, ContDiffAt ℝ (i : WithTop ℕ∞)
      (fun l => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) 0 :=
    fun Y _ => contDiffAt_scale (D.remainder Y V' hV') D.ρ_pos ζ (by omega)
  have hr : ∀ Y ∈ finiteCells F, ContDiffAt ℝ (i : WithTop ℕ∞) (fun l => rescaledCellExpansion T.a T.ρA f l Y V' ζ) 0 :=
    fun Y _ => contDiffAt_scale (D.row Y V' hV') D.ρ_pos ζ (by omega)
  have hbS : ContDiffAt ℝ (i : WithTop ℕ∞) (fun l => remainderSum T.a T.ρA T.lam l V' ζ) 0 := ContDiffAt.sum hb
  have hrS : ContDiffAt ℝ (i : WithTop ℕ∞) (fun l => expansionTotal T.a T.ρA f l V' ζ) 0 := ContDiffAt.sum hr
  simp only [taylorCoeffAtZero]
  rw [hfun, iteratedDeriv_fun_sub (contDiffAt_const.add (contDiffAt_const.mul hbS)) (contDiffAt_const.mul hrS),
    iteratedDeriv_const_add (by omega), iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  have e₁ : iteratedDeriv i (fun l => remainderSum T.a T.ρA T.lam l V' ζ) 0 =
      ∑ Y ∈ finiteCells F, scaleJet (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) i ζ V' :=
    iteratedDeriv_fun_sum hb
  have e₂ : iteratedDeriv i (fun l => expansionTotal T.a T.ρA f l V' ζ) 0 =
      ∑ Y ∈ finiteCells F, scaleJet (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ) i ζ V' :=
    iteratedDeriv_fun_sum hr
  rw [e₁, e₂]
private theorem contDiffAt_coeffWeightFamily (hMC : ConfiningGibbsMeanContDiff) (hL : DerivAlongRulesHold)
    (hCh : MoveChart (5 / 4 * T.σ) V c X r Cc) (D : MeanData T l₁ KS f F) {kind : ℝ → StepLaw} {α β : ℝ → ℝ}
    (hk : LawKind T f F kind α β) (hOb : IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius l₁ K Y Ob)
    (hK : 0 ≤ K) (u₀ : ℝ) :
    ContDiffAt ℝ 3 (weightMoveFamily (fun θ => observableSecondOrderCoeff T.a T.ρA T.lam f (kind θ) Ob) V c X)
      (u₀, 0) := by
  refine weightMoveFamily_contDiffAt_of_param hCh.pos ?_
  have hB : IsOpen (Metric.ball (0 : Fin (k + 1) → ℝ) r) := Metric.isOpen_ball
  set Vt : (Fin (k + 1) → ℝ) → F.GaugeField F.top := fun t => leftTranslate (bondSpread c X (tailProj k t)) V
    with hVt
  set wt : (Fin (k + 1) → ℝ) → ℝ := fun t => (u₀ + t 0) ^ 2 with hwt
  set Of : ℕ → (Fin (k + 1) → ℝ) → StepVariable (finiteCells F) → ℝ :=
    fun i t ζ => taylorCoeffAtZero i fun l => Ob l ζ (Vt t) with hOf
  set Uf : ℕ → (Fin (k + 1) → ℝ) → StepVariable (finiteCells F) → ℝ :=
    fun i t ζ => taylorCoeffAtZero i fun l => rescaledLawExponent T.a T.ρA T.lam f l (Vt t) (kind (wt t)) ζ
    with hUf
  have pInv : ∀ i : ℕ, PolyGrowthC3 (E := StepVariable (finiteCells F)) (Metric.ball (0 : Fin (k + 1) → ℝ) r)
      fun _ _ => ((i.factorial : ℝ))⁻¹ := fun i => PolyGrowthC3.param contDiff_const
  have pO : ∀ i, i ≤ 2 → PolyGrowthC3 (Metric.ball (0 : Fin (k + 1) → ℝ) r) (Of i) := by
    intro i hi
    have h := (polyGrowth_scaleJet hL hCh hOb D.l₁_pos D.ρ_pos D.κ_pos hK hi).mul hB (pInv i)
    exact h.congr hB fun t _ ζ => by simp [hOf, taylorCoeffAtZero, scaleJet, div_eq_mul_inv, hVt]
  have mO : ∀ i, i ≤ 2 → ∀ t ∈ Metric.ball (0 : Fin (k + 1) → ℝ) r, Measurable (Of i t) := by
    intro i hi t ht
    have h := (measurable_scaleJet hCh hOb D.l₁_pos D.ρ_pos hi ht).mul_const ((i.factorial : ℝ))⁻¹
    have e : Of i t = fun ζ =>
        scaleJet Ob i ζ (leftTranslate (bondSpread c X (tailProj k t)) V) * ((i.factorial : ℝ))⁻¹ := by
      funext ζ
      simp [hOf, taylorCoeffAtZero, scaleJet, div_eq_mul_inv, hVt]
    rw [e]
    exact h
  have eU : ∀ i, 1 ≤ i → i ≤ 2 → ∀ t ∈ Metric.ball (0 : Fin (k + 1) → ℝ) r, ∀ ζ, Uf i t ζ =
      (α (wt t) * ∑ Y ∈ finiteCells F,
          scaleJet (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) i ζ (Vt t) -
        β (wt t) * ∑ Y ∈ finiteCells F, scaleJet (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ) i ζ (Vt t)) *
          ((i.factorial : ℝ))⁻¹ := by
    intro i h1 h2 t ht ζ
    rw [← div_eq_mul_inv]
    exact taylorCoeff_lawExponent D hk (hCh.cold _ (tailProj_mem_ball ht)) (wt t) ζ h1 h2
  have pU : ∀ i, 1 ≤ i → i ≤ 2 → PolyGrowthC3 (Metric.ball (0 : Fin (k + 1) → ℝ) r) (Uf i) := by
    intro i h1 h2
    have pα : PolyGrowthC3 (E := StepVariable (finiteCells F)) (Metric.ball (0 : Fin (k + 1) → ℝ) r)
        fun t _ => α (wt t) := PolyGrowthC3.param (hk.smooth_α.comp (contDiff_shifted_sq u₀))
    have pβ : PolyGrowthC3 (E := StepVariable (finiteCells F)) (Metric.ball (0 : Fin (k + 1) → ℝ) r)
        fun t _ => β (wt t) := PolyGrowthC3.param (hk.smooth_β.comp (contDiff_shifted_sq u₀))
    have h := ((pα.mul hB (polyGrowth_remainder hL hCh D h2)).sub
      (pβ.mul hB (polyGrowth_expansion hL hCh D h2))).mul hB (pInv i)
    exact h.congr hB (eU i h1 h2)
  have mU : ∀ i, 1 ≤ i → i ≤ 2 → ∀ t ∈ Metric.ball (0 : Fin (k + 1) → ℝ) r, Measurable (Uf i t) := by
    intro i h1 h2 t ht
    have e : Uf i t = _ := funext (eU i h1 h2 t ht)
    rw [e]
    have hc₁ : Continuous fun ζ => ∑ Y ∈ finiteCells F,
        scaleJet (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) i ζ (Vt t) :=
      continuous_finset_sum _ fun Y _ =>
        continuous_scaleJet (D.remainder Y _ (hCh.cold _ (tailProj_mem_ball ht))) D.l₁_pos D.ρ_pos h2
    have hc₂ : Continuous fun ζ => ∑ Y ∈ finiteCells F,
        scaleJet (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ) i ζ (Vt t) :=
      continuous_finset_sum _ fun Y _ =>
        continuous_scaleJet (D.row Y _ (hCh.cold _ (tailProj_mem_ball ht))) D.l₁_pos D.ρ_pos h2
    exact (((continuous_const.mul hc₁).sub (continuous_const.mul hc₂)).mul continuous_const).measurable
  have g : ∀ H : (Fin (k + 1) → ℝ) → StepVariable (finiteCells F) → ℝ,
      PolyGrowthC3 (Metric.ball (0 : Fin (k + 1) → ℝ) r) H →
      (∀ t ∈ Metric.ball (0 : Fin (k + 1) → ℝ) r, Measurable (H t)) →
      ContDiffOn ℝ 3 (fun t => gaussianMean T.a T.ρA T.lam f (Vt t) (kind (wt t)) (H t))
        (Metric.ball 0 r) := fun H p m => contDiffOn_gaussianMean hMC hL hCh D hk u₀ p m
  have pU1 := pU 1 le_rfl (by norm_num)
  have pU2 := pU 2 (by norm_num) le_rfl
  have mU1 := mU 1 le_rfl (by norm_num)
  have mU2 := mU 2 (by norm_num) le_rfl
  have pO0 := pO 0 (by norm_num)
  have pO1 := pO 1 (by norm_num)
  have pO2 := pO 2 le_rfl
  have mO0 := mO 0 (by norm_num)
  have mO1 := mO 1 (by norm_num)
  have mO2 := mO 2 le_rfl
  have pSq : PolyGrowthC3 (Metric.ball (0 : Fin (k + 1) → ℝ) r) fun t ζ => Uf 1 t ζ ^ 2 :=
    (pU1.mul hB pU1).congr hB fun t _ ζ => sq _
  have mSq : ∀ t ∈ Metric.ball (0 : Fin (k + 1) → ℝ) r, Measurable fun ζ => Uf 1 t ζ ^ 2 :=
    fun t ht => (mU1 t ht).pow_const 2
  have c₁ := (g _ (pO1.mul hB pU1) fun t ht => (mO1 t ht).mul (mU1 t ht)).sub ((g _ pO1 mO1).mul (g _ pU1 mU1))
  have c₂ := (g _ (pO0.mul hB pU2) fun t ht => (mO0 t ht).mul (mU2 t ht)).sub ((g _ pO0 mO0).mul (g _ pU2 mU2))
  have c₃ := (g _ (pO0.mul hB pSq) fun t ht => (mO0 t ht).mul (mSq t ht)).sub ((g _ pO0 mO0).mul (g _ pSq mSq))
  have hfin := (((g _ pO2 mO2).sub c₁).sub c₂).add (contDiffOn_const (c := (1 / 2 : ℝ)).mul c₃)
  exact hfin.congr fun t _ => rfl
end GaussianMeans
section PositiveScale
variable {F : BlockFrame} {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {l₁ KS K : ℝ} {f : LocalFamily} {Y : F.Cell}
  {V : F.GaugeField F.top} {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
  {s : ℝ} {k : ℕ} {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {r Cc : ℝ}
private theorem norm_le_of_memScaledBalls {ρ l : ℝ} (hρ : 0 < ρ) (hl : 0 < l) {ζ : StepVariable (finiteCells F)}
    (h : MemScaledBalls ρ l ζ) : ‖ζ‖ ≤ ρ / l := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun b => ?_
  rw [le_div_iff₀ hl, mul_comm]
  exact (h b).le
private theorem exists_uniformC3_scale (hCh : MoveChart s V c X r Cc) {κ ρ : ℝ}
    (hOb : IsSmoothAtSmallCurvature s κ ρ l₁ K Y Ob) (hρ : 0 < ρ) (hκ : 0 ≤ κ) (hK : 0 ≤ K) {l : ℝ} (hl : 0 < l)
    (hl₁ : l ≤ l₁) : ∃ C : ℝ, 0 ≤ C ∧ UniformC3 (Metric.ball (0 : Fin (k + 1) → ℝ) r)
      {ζ : StepVariable (finiteCells F) | MemScaledBalls ρ l ζ} (fun _ => C)
      (fun t ζ => Ob l ζ (leftTranslate (bondSpread c X (tailProj k t)) V)) := by
  have t₀ := (uniformC3_scale hCh hOb hκ hK hl hl₁).along (tailProj k) (tailProj_norm_le k) Metric.isOpen_ball
    (B' := Metric.ball (0 : Fin (k + 1) → ℝ) r) (fun _ hs => tailProj_mem_ball hs)
  have hCc := hCh.nonneg
  refine ⟨Cc * (K * ((1 + (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ)) ^ 7 * (1 + ρ / l) ^ 7)),
    by positivity, t₀.mono fun ζ hζ => ?_⟩
  have h1 := one_add_localWeight_pow_le (Y := Y) hκ ζ
  have h2 := norm_le_of_memScaledBalls hρ hl hζ
  have h3 : (1 + ‖ζ‖) ^ 7 ≤ (1 + ρ / l) ^ 7 := pow_le_pow_left₀ (by positivity) (by linarith) 7
  calc Cc * (K * (1 + localWeight κ Y ζ) ^ 7)
      ≤ Cc * (K * ((1 + (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ)) ^ 7 * (1 + ‖ζ‖) ^ 7)) := by gcongr
    _ ≤ _ := by gcongr
private theorem stepLawExponent_smul {l : ℝ} (hl : 0 < l) {V' : F.GaugeField F.top}
    {ζ : StepVariable (finiteCells F)}
    (hE : ∀ ν : ℝ, stepExponent true T.a T.ρA (l⁻¹ ^ 2) 0 f ν V' (l • ζ) = rescaledExponent T.a T.ρA f ν l V' ζ)
    (law : StepLaw) :
    stepLawExponent T.a T.ρA T.lam (l⁻¹ ^ 2) f V' law (l • ζ) =
      rescaledLawExponent T.a T.ρA T.lam f l V' law ζ := by
  cases law with
  | tilted ν => exact hE ν
  | interpolated τ =>
    simp only [stepLawExponent, rescaledLawExponent]
    rw [hE 0]
    congr 2
    unfold totalQuadratic
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e : ‖(l • ζ) b‖ = l * ‖ζ b‖ := by
      rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hl]
    rw [e]
    field_simp
private theorem isDominated_of_uniformC3 {Ω : Type} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [SecondCountableTopology Ω] {μ : Measure Ω} {n : ℕ} {B : Set (Fin n → ℝ)}
    {S : Set Ω} {C : ℝ} {G : (Fin n → ℝ) → Ω → ℝ} (hS : MeasurableSet S) (hae : ∀ᵐ ω ∂μ, ω ∈ S)
    (hc : ∀ t ∈ B, ContinuousOn (G t) S) (h : UniformC3 B S (fun _ => C) G) :
    IsDominatedSmoothFamily μ 3 B C G := by
  refine ⟨fun t ht => ?_, ?_, ?_⟩
  · have h1 : AEStronglyMeasurable (G t) (μ.restrict S) := (hc t ht).aestronglyMeasurable hS
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at h1
  · filter_upwards [hae] with ω hω
    exact_mod_cast h.smooth ω hω
  · filter_upwards [hae] with ω hω j hj t ht
    exact h.bound ω hω j hj t ht
private theorem contDiffAt_scaleWeightFamily (hW : GibbsMeanDifferentiation) (hR : CutoffMeanIsGibbsMean)
    (hCh : MoveChart (5 / 4 * T.σ) V c X r Cc) (D : MeanData T l₁ KS f F) {kind : ℝ → StepLaw} {α β : ℝ → ℝ}
    (hk : LawKind T f F kind α β) (hcut : IsCutoff T.ballRadius T.p)
    (hE : ∀ (V' : F.GaugeField F.top) (ν l : ℝ) (ζ : StepVariable (finiteCells F)),
      IsSmallCurvature (5 / 4 * T.σ) V' → 0 < l → l ≤ l₁ → MemScaledBalls T.ballRadius l ζ →
      stepExponent true T.a T.ρA (l⁻¹ ^ 2) 0 f ν V' (l • ζ) = rescaledExponent T.a T.ρA f ν l V' ζ)
    (hOb : IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius l₁ K Y Ob) (hK : 0 ≤ K) {l : ℝ} (hl : 0 < l)
    (hl₁ : l ≤ l₁) (u₀ : ℝ) :
    ContDiffAt ℝ 3 (weightMoveFamily (fun θ =>
      observableMean T.a T.ρA T.ballRadius T.lam T.p f (kind θ) Ob l) V c X) (u₀, 0) := by
  refine weightMoveFamily_contDiffAt_of_param hCh.pos ?_
  have hρ := D.ρ_pos
  have hκ := D.κ_pos
  have hB : IsOpen (Metric.ball (0 : Fin (k + 1) → ℝ) r) := Metric.isOpen_ball
  obtain ⟨hfinite, hne, hae, hmean⟩ := hR F T.ballRadius T.p hρ hcut
  haveI := hfinite
  set Sη : Set (StepVariable (finiteCells F)) := {η | ∀ b, ‖η b‖ < T.ballRadius} with hSη
  set Sζ : Set (StepVariable (finiteCells F)) := {ζ | MemScaledBalls T.ballRadius l ζ} with hSζ
  have hSo : IsOpen Sη := by
    have e : Sη = ⋂ b, {η | ‖η b‖ < T.ballRadius} := by
      ext η
      simp [hSη]
    rw [e]
    exact isOpen_iInter_of_finite fun b => isOpen_lt (by fun_prop) continuous_const
  have hφ : ∀ η ∈ Sη, l⁻¹ • η ∈ Sζ := by
    intro η hη b
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hl), ← mul_assoc,
      mul_inv_cancel₀ hl.ne', one_mul]
    exact hη b
  set Vt : (Fin (k + 1) → ℝ) → F.GaugeField F.top := fun t => leftTranslate (bondSpread c X (tailProj k t)) V
    with hVt
  set wt : (Fin (k + 1) → ℝ) → ℝ := fun t => (u₀ + t 0) ^ 2 with hwt
  have tb := fun Y' => exists_uniformC3_scale hCh (D.remainder Y') hρ hκ D.KS_pos hl hl₁
  have tr := fun Y' => exists_uniformC3_scale hCh (D.row Y') hρ hκ D.KS_pos hl hl₁
  choose Cb pb tb using tb
  choose Cr pr tr using tr
  have tB := UniformC3.sum hB (finiteCells F) fun Y' _ => tb Y'
  have tR := UniformC3.sum hB (finiteCells F) fun Y' _ => tr Y'
  obtain ⟨Cα, pα, tα⟩ := uniformC3_of_param (S := Sζ) (hk.smooth_α.comp (contDiff_shifted_sq (k := k) u₀)) (r := r)
  obtain ⟨Cβ, pβ, tβ⟩ := uniformC3_of_param (S := Sζ) (hk.smooth_β.neg.comp (contDiff_shifted_sq (k := k) u₀))
    (r := r)
  have hnn : ∀ (C : ℝ), 0 ≤ C → ∀ ω ∈ Sζ, 0 ≤ (fun _ : StepVariable (finiteCells F) => C) ω := fun C h _ _ => h
  have hsb : 0 ≤ ∑ Y' ∈ finiteCells F, Cb Y' := Finset.sum_nonneg fun Y' _ => pb Y'
  have hsr : 0 ≤ ∑ Y' ∈ finiteCells F, Cr Y' := Finset.sum_nonneg fun Y' _ => pr Y'
  set Cq : ℝ := (|T.lam| / 2 * (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ)) * (1 + T.ballRadius / l) ^ 2
    with hCq
  have tQ : UniformC3 (Metric.ball (0 : Fin (k + 1) → ℝ) r) Sζ (fun _ => Cq)
      fun _ ζ => halfSquare (F := F) T.lam ζ := by
    refine (uniformC3_const _ _).mono fun ζ hζ => (abs_halfSquare_le T.lam ζ).trans ?_
    have h2 := norm_le_of_memScaledBalls hρ hl hζ
    rw [hCq]
    have h3 : (1 + ‖ζ‖) ^ 2 ≤ (1 + T.ballRadius / l) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    gcongr
  have tG := (tQ.add hB (tα.mul hB tB (hnn _ pα) (hnn _ hsb))).add hB (tβ.mul hB tR (hnn _ pβ) (hnn _ hsr))
  have eqA : ∀ η ∈ Sη, ∀ t ∈ Metric.ball (0 : Fin (k + 1) → ℝ) r,
      stepLawExponent T.a T.ρA T.lam (l⁻¹ ^ 2) f (Vt t) (kind (wt t)) η =
        halfSquare T.lam (l⁻¹ • η) + α (wt t) * remainderSum T.a T.ρA T.lam l (Vt t) (l⁻¹ • η) +
          (-β (wt t)) * expansionTotal T.a T.ρA f l (Vt t) (l⁻¹ • η) := by
    intro η hη t ht
    have hcold := hCh.cold _ (tailProj_mem_ball ht)
    have e₁ : l • l⁻¹ • η = η := smul_inv_smul₀ hl.ne' η
    have h1 := stepLawExponent_smul (T := T) (f := f) hl (V' := Vt t) (ζ := l⁻¹ • η)
      (fun ν => hE _ ν l _ hcold hl hl₁ (hφ η hη)) (kind (wt t))
    rw [e₁] at h1
    rw [h1, hk.law]
    ring
  set KA : ℝ := Cq + 8 * (Cα * ∑ Y' ∈ finiteCells F, Cb Y') + 8 * (Cβ * ∑ Y' ∈ finiteCells F, Cr Y') with hKA
  have tA : UniformC3 (Metric.ball (0 : Fin (k + 1) → ℝ) r) Sη (fun _ => KA)
      fun t η => stepLawExponent T.a T.ρA T.lam (l⁻¹ ^ 2) f (Vt t) (kind (wt t)) η := by
    refine (UniformC3.comp_right (fun η => l⁻¹ • η) hφ tG).congr hB ?_ |>.mono fun _ _ => le_rfl
    intro η hη t ht
    rw [eqA η hη t ht]
    rfl
  obtain ⟨KH, pKH, tH₀⟩ := exists_uniformC3_scale hCh hOb hρ hκ hK hl hl₁
  have tH : UniformC3 (Metric.ball (0 : Fin (k + 1) → ℝ) r) Sη (fun _ => KH)
      fun t η => Ob l (l⁻¹ • η) (Vt t) := UniformC3.comp_right (fun η => l⁻¹ • η) hφ tH₀
  have hφc : ContinuousOn (fun η : StepVariable (finiteCells F) => l⁻¹ • η) Sη := by fun_prop
  have hcH : ∀ t ∈ Metric.ball (0 : Fin (k + 1) → ℝ) r, ContinuousOn (fun η => Ob l (l⁻¹ • η) (Vt t)) Sη :=
    fun t ht => (continuousOn_observable (hOb _ (hCh.cold _ (tailProj_mem_ball ht))) hl).comp hφc hφ
  have hcA : ∀ t ∈ Metric.ball (0 : Fin (k + 1) → ℝ) r, ContinuousOn
      (fun η => stepLawExponent T.a T.ρA T.lam (l⁻¹ ^ 2) f (Vt t) (kind (wt t)) η) Sη := by
    intro t ht
    have hcold := hCh.cold _ (tailProj_mem_ball ht)
    have hq : Continuous fun ζ : StepVariable (finiteCells F) => halfSquare T.lam ζ := by
      unfold halfSquare
      fun_prop
    have hb : ContinuousOn (fun ζ => remainderSum T.a T.ρA T.lam l (Vt t) ζ) Sζ :=
      continuousOn_finset_sum _ fun Y' _ => continuousOn_observable (D.remainder Y' _ hcold) hl
    have hr : ContinuousOn (fun ζ => expansionTotal T.a T.ρA f l (Vt t) ζ) Sζ :=
      continuousOn_finset_sum _ fun Y' _ => continuousOn_observable (D.row Y' _ hcold) hl
    have h1 : ContinuousOn (fun η : StepVariable (finiteCells F) => halfSquare T.lam (l⁻¹ • η) +
        α (wt t) * remainderSum T.a T.ρA T.lam l (Vt t) (l⁻¹ • η) +
          (-β (wt t)) * expansionTotal T.a T.ρA f l (Vt t) (l⁻¹ • η)) Sη :=
      ((hq.continuousOn.comp hφc hφ).add (continuousOn_const.mul (hb.comp hφc hφ))).add
        (continuousOn_const.mul (hr.comp hφc hφ))
    exact h1.congr fun η hη => eqA η hη t ht
  have hae' : ∀ᵐ η ∂cutoffLaw F T.ballRadius T.p, η ∈ Sη := hae
  have hMC := (hW.2 (StepVariable (finiteCells F)) (cutoffLaw F T.ballRadius T.p) (k + 1) (Metric.ball 0 r)
    (max KA KH) _ _ hB hne
    (isDominated_of_uniformC3 hSo.measurableSet hae' hcA (tA.mono fun _ _ => le_max_left _ _))
    (isDominated_of_uniformC3 hSo.measurableSet hae' hcH (tH.mono fun _ _ => le_max_right _ _))).1
  refine hMC.congr fun t _ => ?_
  simp only [observableMean, rescaledMean]
  exact hmean _ _
end PositiveScale
end MeansInWeight
open MeansInWeight in
theorem meansDifferentiableInWeight (hS : rescaledPartsSmoothStatement)
    (hX : RescaledExponentAgrees) (hLE : chartedEnergyAtMinimizerRegular)
    (hR : CutoffMeanIsGibbsMean) (hW : GibbsMeanDifferentiation)
    (hL : DerivAlongRulesHold) (hI : IntervalIntegralSmoothFamily)
    (hC : ContDiffBoundOnParameterBall) (hMC : ConfiningGibbsMeanContDiff) :
    meansDifferentiableInWeightStatement := by
  unfold meansDifferentiableInWeightStatement
  refine EventuallyOrdered.mono ((hS.and hX).and hLE) ?_
  rintro T hT hn ⟨⟨cS, l₂, hl₂, cX⟩, cL⟩ e
  obtain ⟨l₃, KS, hl₃, hKS, gS⟩ := cS e
  refine ⟨min l₂ l₃, lt_min hl₂ hl₃, fun l₁ hl₁ hle t f F V Y kind K Ob k c X hf hF hV hkind hK hOb _ => ?_⟩
  have hl₁₂ : l₁ ≤ l₂ := hle.trans (min_le_left _ _)
  have hl₁₃ : l₁ ≤ l₃ := hle.trans (min_le_right _ _)
  have hside : ∀ i, F.extent i ≠ 0 := by
    obtain ⟨_, _, n, hn', hn₀⟩ := hF
    intro i
    rw [hn' i]
    omega
  have hσ : 0 < T.σ := hT.σ_pos
  have hρ : 0 < T.ballRadius := by
    unfold StepParameters.ballRadius
    positivity
  have hfinite : Finite F.Cell := by
    have h : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by simp [BlockFrame.period, hside i]⟩
    exact (Pi.finite : Finite (F.Site F.top))
  have hlam : 0 < T.lam := (cL t F V hF hV).2.2.2.1
  have D : MeanData T l₁ KS f F := by
    refine ⟨hρ, hT.κ_pos.le, hl₁, hKS, hlam, hfinite, fun Y' V' hV' => (gS l₁ hl₁ hl₁₃ t f F V' Y' hf hF hV').1,
      fun Y' V' hV' => (gS l₁ hl₁ hl₁₃ t f F V' Y' hf hF hV').2, fun V' hV' => ?_⟩
    obtain ⟨h₁, -, -, -, h₂⟩ := cL t F V' hF hV'
    have h0 : (0 : StepVariable (finiteCells F)) ∈
        {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} := fun b => by
      simpa using hρ
    have ho : IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} := by
      have e : {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} =
          ⋂ b, {η | ‖η b‖ < T.ballRadius} := by
        ext η
        simp
      rw [e]
      exact isOpen_iInter_of_finite fun b => isOpen_lt (by fun_prop) continuous_const
    exact ⟨h₁.contDiffAt (ho.mem_nhds h0), fun u => h₂ 0 u h0⟩
  obtain ⟨α, β, hk⟩ : ∃ α β : ℝ → ℝ, LawKind T f F kind α β := by
    rcases hkind with rfl | rfl
    · exact ⟨fun _ => 1, fun θ => θ, contDiff_const, contDiff_id, fun _ => zero_le_one,
        fun θ l V' ζ => lawExponent_tilted D.fin _ _ _ _ θ l V' ζ⟩
    · exact ⟨fun θ => θ, fun _ => 0, contDiff_id, contDiff_const, fun u => sq_nonneg u,
        fun θ l V' ζ => lawExponent_interpolated D.fin _ _ _ _ θ l V' ζ⟩
  have hE : ∀ (V' : F.GaugeField F.top) (ν l : ℝ) (ζ : StepVariable (finiteCells F)),
      IsSmallCurvature (5 / 4 * T.σ) V' → 0 < l → l ≤ l₁ → MemScaledBalls T.ballRadius l ζ →
      stepExponent true T.a T.ρA (l⁻¹ ^ 2) 0 f ν V' (l • ζ) = rescaledExponent T.a T.ρA f ν l V' ζ :=
    fun V' ν l ζ hV' h0 h1 hb => (cX t F V' f ν l Y ζ hF hV' h0 (h1.trans hl₁₂) hb).1
  refine ⟨fun hk3 => ⟨fun l h0 h1 => ?_, ?_⟩, fun hk2 => ?_⟩
  · refine derivUnderWeight_of_joint hL hI (fun k' c' X' u _ => ?_) c X hk3
    obtain ⟨r, Cc, hCh⟩ := exists_moveChart hC hside hV c' X'
    exact contDiffAt_scaleWeightFamily hW hR hCh D hk hT.cutoff hE hOb hK h0 h1 u
  · refine derivUnderWeight_of_joint hL hI (fun k' c' X' u _ => ?_) c X hk3
    obtain ⟨r, Cc, hCh⟩ := exists_moveChart hC hside hV c' X'
    exact contDiffAt_gaussianWeightFamily hMC hL hCh D hk hOb hK u
  · refine derivUnderWeight_of_joint hL hI (fun k' c' X' u _ => ?_) c X (by omega)
    obtain ⟨r, Cc, hCh⟩ := exists_moveChart hC hside hV c' X'
    exact contDiffAt_coeffWeightFamily hMC hL hCh D hk hOb hK u
end StepDensities
end YangMills.Construction
end
