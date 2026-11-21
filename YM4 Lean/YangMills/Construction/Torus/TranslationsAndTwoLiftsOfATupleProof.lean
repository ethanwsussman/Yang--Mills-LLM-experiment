import YangMills.Construction.Continuum.RingsRingTracesAndTheirIntegralsProof
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.Torus.LiftOfABallAndOfAFunction
import YangMills.Construction.Torus.TranslationsAndTwoLiftsOfATuple
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open TorusMetric PeriodicLattice TestFunctions
namespace FreeRingKernels.TranslationInvariance
variable {n : ℕ}
theorem cyclicTrace_translate (σ : Fin n → Fin n) (x : Fin n → Fin 4 → ℝ) (v : Fin 4 → ℝ) :
    cyclicTrace σ (fun i => x i + v) = cyclicTrace σ x := by
  simp only [cyclicTrace, cyclicPropagatorProduct, add_sub_add_right_eq_sub]
theorem freeRingKernelAlong_translate (σ : Fin n → Fin n) (f : Fin n → (Fin 4 → ℝ) → ℝ)
    (v : Fin 4 → ℝ) :
    freeRingKernelAlong σ (fun j y => f j (y - v)) = freeRingKernelAlong σ f := by apply _root_.YangMills.Construction.FreeRingKernels.RingIntegrals.integral_comp_sub_cyclicTrace <;> assumption
theorem freeRingKernel_translate (R : Set (Fin n → Fin n)) (f : Fin n → (Fin 4 → ℝ) → ℝ)
    (v : Fin 4 → ℝ) : freeRingKernel R (fun j y => f j (y - v)) = freeRingKernel R f := by
  unfold freeRingKernel
  split_ifs with hR
  · exact freeRingKernelAlong_translate _ _ _
  · rfl
theorem freeBoxKernel_translate (f : Fin 4 → (Fin 4 → ℝ) → ℝ) (v : Fin 4 → ℝ) :
    freeBoxKernel (fun j y => f j (y - v)) = freeBoxKernel f := by
  simp only [freeBoxKernel, freeRingKernel_translate]
theorem kernelsTranslationInvariant : KernelsTranslationInvariant :=
  ⟨fun _ _ R _ f _ v => freeRingKernel_translate R f v, fun f _ v => freeBoxKernel_translate f v,
    fun x _ v => by simp only [freeBoxDensity, cyclicTrace_translate]⟩
theorem euclidNormVec_eq_norm (v : Fin 4 → ℝ) :
    euclidNormVec v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 4))‖ := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_eq_norm <;> assumption
theorem euclidNormVec_sub_le_add (a b c : Fin 4 → ℝ) :
    euclidNormVec (a - b) ≤ euclidNormVec (a - c) + euclidNormVec (b - c) := by
  rw [euclidNormVec_eq_norm, euclidNormVec_eq_norm, euclidNormVec_eq_norm,
    ← sub_sub_sub_cancel_right a b c, WithLp.toLp_sub]
  exact norm_sub_le _ _
theorem torusProj_sub (S : ℝ) (a b : Fin 4 → ℝ) :
    torusProj S (a - b) = torusProj S a - torusProj S b := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
theorem sub_mem_closedBallR4_of_proj_mem (hS : MinimalLiftUnique)
    (hB : BallLift.BallAndFunctionLift) (s : Conventions.StandingParameters)
    {z z' : s.Torus} {r r' : ℝ} {c c' : Fin 4 → ℝ}
    (hr : IsAdmissibleRadius s.L s.m r) (hr' : IsAdmissibleRadius s.L s.m r')
    (hc : c ∈ liftsOf z) (hc' : c' ∈ liftsOf z') {p p' y : Fin 4 → ℝ}
    (hp : p ∈ closedBallR4 c r) (hp' : p' ∈ closedBallR4 c' r')
    (hproj : torusProj (torusSide s.L s.m) p = torusProj (torusSide s.L s.m) p')
    (hy : y ∈ closedBallR4 c' r') (hw : torusProj (torusSide s.L s.m) y ∈ closedBallTorus z r) :
    y - (p' - p) ∈ closedBallR4 c r := by
  obtain ⟨⟨iso, bij⟩, -⟩ := hB s z r c hr hc
  obtain ⟨⟨iso', -⟩, -⟩ := hB s z' r' c' hr' hc'
  obtain ⟨u, hu, hup⟩ := bij.surjOn hw
  have e₁ := iso u hu p hp
  have e₂ := iso' y hy p' hp'
  rw [hup, hproj] at e₁
  have hlt : torusEuclidNorm (torusProj (torusSide s.L s.m) y - torusProj (torusSide s.L s.m) p')
      < s.side / 2 := by
    have hu' : euclidNormVec (u - c) ≤ r := hu
    have hp'' : euclidNormVec (p - c) ≤ r := hp
    have ht := euclidNormVec_sub_le_add u p c
    have hside : s.side = torusSide s.L s.m := rfl
    have hr2 := hr.2
    rw [e₁, hside]
    linarith
  obtain ⟨v, -, huniq⟩ := (hS s _ hlt).1
  have a₁ : IsMinimalLift (torusProj (torusSide s.L s.m) y - torusProj (torusSide s.L s.m) p')
      (u - p) :=
    ⟨by rw [torusProj_sub, hup, hproj], e₁.symm⟩
  have a₂ : IsMinimalLift (torusProj (torusSide s.L s.m) y - torusProj (torusSide s.L s.m) p')
      (y - p') :=
    ⟨torusProj_sub _ _ _, e₂.symm⟩
  have heq : u - p = y - p' := (huniq _ a₁).trans (huniq _ a₂).symm
  have hy' : y - (p' - p) = u := by
    funext μ
    have := congrFun heq μ
    simp only [Pi.sub_apply] at this ⊢
    linarith
  rw [hy']
  exact hu
theorem liftsDifferByPeriod (hS : MinimalLiftUnique)
    (hB : BallLift.BallAndFunctionLift) : LiftsDifferByPeriod := by
  intro s n _ f z z' r r' hz hz' c hc c' hc'
  by_cases hne : ∃ i w, f i w ≠ 0
  · obtain ⟨i₀, w₀, hw₀⟩ := hne
    have mem : ∀ i w, f i w ≠ 0 → w ∈ closedBallTorus z r := fun i w h =>
      hz.2 i (@subset_closure _ (metricTopology s.L s.m) _ w h)
    have mem' : ∀ i w, f i w ≠ 0 → w ∈ closedBallTorus z' r' := fun i w h =>
      hz'.2 i (@subset_closure _ (metricTopology s.L s.m) _ w h)
    obtain ⟨⟨-, bij⟩, -⟩ := hB s z r c hz.1 hc
    obtain ⟨⟨-, bij'⟩, -⟩ := hB s z' r' c' hz'.1 hc'
    obtain ⟨p, hp, hpw⟩ := bij.surjOn (mem i₀ w₀ hw₀)
    obtain ⟨p', hp', hpw'⟩ := bij'.surjOn (mem' i₀ w₀ hw₀)
    have hproj : torusProj (torusSide s.L s.m) p = torusProj (torusSide s.L s.m) p' :=
      hpw.trans hpw'.symm
    have hper : ∀ μ, ∃ k : ℤ, p' μ - p μ = s.side * (k : ℝ) := by
      intro μ
      have h : ((p' μ - p μ : ℝ) : AddCircle (torusSide s.L s.m)) = 0 := by
        rw [AddCircle.coe_sub, sub_eq_zero]
        exact (congrFun hproj μ).symm
      obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).1 h
      refine ⟨k, ?_⟩
      rw [← hk, zsmul_eq_mul, mul_comm]
      rfl
    choose k hk using hper
    have hd : ∀ y : Fin 4 → ℝ, (fun α => y α - s.side * (k α : ℝ)) = y - (p' - p) := by
      intro y
      funext α
      simp only [Pi.sub_apply, hk]
    have hpd : ∀ y, torusProj (torusSide s.L s.m) (y - (p' - p)) = torusProj (torusSide s.L s.m) y := by
      intro y
      rw [torusProj_sub, torusProj_sub, hproj, sub_self, sub_zero]
    refine ⟨k, fun i => funext fun y => ?_⟩
    simp only [hd]
    by_cases hf : f i (torusProj (torusSide s.L s.m) y) = 0
    · have l₁ : ballIndicatorLift c' r' (f i) y = 0 := by
        simp [ballIndicatorLift, indicator, hf]
      have l₂ : ballIndicatorLift c r (f i) (y - (p' - p)) = 0 := by
        simp [ballIndicatorLift, indicator, hpd, hf]
      rw [l₁, l₂]
    · have hiff : y ∈ closedBallR4 c' r' ↔ y - (p' - p) ∈ closedBallR4 c r := by
        constructor
        · intro hy
          exact sub_mem_closedBallR4_of_proj_mem hS hB s hz.1 hz'.1 hc hc' hp hp' hproj hy (mem i _ hf)
        · intro hy
          have hw : torusProj (torusSide s.L s.m) (y - (p' - p)) ∈ closedBallTorus z' r' := by
            rw [hpd]
            exact mem' i _ hf
          have := sub_mem_closedBallR4_of_proj_mem hS hB s hz'.1 hz.1 hc' hc hp' hp hproj.symm hy hw
          have hback : y - (p' - p) - (p - p') = y := by
            funext μ
            simp only [Pi.sub_apply]
            ring
          rwa [hback] at this
      by_cases hy : y ∈ closedBallR4 c' r'
      · have hy' := hiff.1 hy
        simp [ballIndicatorLift, indicator, hy, hy', hpd]
      · have hy' : y - (p' - p) ∉ closedBallR4 c r := fun h => hy (hiff.2 h)
        simp [ballIndicatorLift, indicator, hy, hy']
  · have hzero : ∀ i w, f i w = 0 := by
      intro i w
      by_contra h
      exact hne ⟨i, w, h⟩
    refine ⟨0, fun i => funext fun y => ?_⟩
    simp [ballIndicatorLift, indicator, hzero]
theorem isAdmissibleTestFamily_of_isTupleLift (hB : BallLift.BallAndFunctionLift)
    (s : Conventions.StandingParameters) {f : Fin n → s.Torus → ℝ} (hf : IsTorusKernelFamily f)
    {g : Fin n → (Fin 4 → ℝ) → ℝ} (hg : IsTupleLift f g) : IsAdmissibleTestFamily g := by
  obtain ⟨z, r, hz, c, hc, hgi⟩ := hg
  obtain rfl : g = fun i => ballIndicatorLift c r (f i) := funext hgi
  have lift : ∀ i, IsFunctionLift z r c (f i) (ballIndicatorLift c r (f i)) :=
    fun i => ⟨hz.1, hc, hz.2 i, rfl⟩
  have A := hB s z r c hz.1 hc
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun i j hij => ?_⟩
  · exact (A.2.1 _ _ (lift j)).2.2.2.2.2.2 (hf.1 j).measurable
  · obtain ⟨C, hC⟩ := (hf.1 j).bounded
    refine ⟨max C 0, fun y => ?_⟩
    by_cases hy : y ∈ closedBallR4 c r
    · simp only [ballIndicatorLift, indicator, hy, if_true, Function.comp]
      exact le_max_of_le_left (hC _)
    · simp [ballIndicatorLift, indicator, hy]
  · exact (A.2.1 _ _ (lift j)).2.2.1
  · exact (A.2.2 _ _ _ _ (lift i) (lift j)).2 (hf.2.1 hij)
theorem exists_translate_of_isTupleLift (hS : MinimalLiftUnique)
    (hB : BallLift.BallAndFunctionLift) (s : Conventions.StandingParameters) (hn : 1 ≤ n)
    {f : Fin n → s.Torus → ℝ} {g g' : Fin n → (Fin 4 → ℝ) → ℝ}
    (hg : IsTupleLift f g) (hg' : IsTupleLift f g') :
    ∃ v : Fin 4 → ℝ, g' = fun j y => g j (y - v) := by
  obtain ⟨z, r, hz, c, hc, hgi⟩ := hg
  obtain ⟨z', r', hz', c', hc', hgi'⟩ := hg'
  obtain ⟨k, hk⟩ := liftsDifferByPeriod hS hB s n hn f z z' r r' hz hz' c hc c' hc'
  refine ⟨fun α => s.side * (k α : ℝ), funext fun j => ?_⟩
  rw [hgi', hk j, hgi j]
  rfl
theorem statement_holds (hB : BallLift.BallAndFunctionLift)
    (hS : MinimalLiftUnique) : Statement := by
  refine ⟨kernelsTranslationInvariant, liftsDifferByPeriod hS hB, ?_, ?_⟩
  · intro s n hn f hf
    refine ⟨fun g hg => isAdmissibleTestFamily_of_isTupleLift hB s hf hg, fun g g' hg hg' R _ => ?_⟩
    obtain ⟨v, rfl⟩ := exists_translate_of_isTupleLift hS hB s (by omega) hg hg'
    exact (freeRingKernel_translate R g v).symm
  · intro s f _ g g' hg hg'
    obtain ⟨v, rfl⟩ := exists_translate_of_isTupleLift hS hB s (by omega) hg hg'
    exact (freeBoxKernel_translate g v).symm
end FreeRingKernels.TranslationInvariance
end YangMills.Construction
end
