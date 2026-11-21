import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.RunningCouplingSlope.KernelOfASmallFamily
import YangMills.Construction.SixteenPointsOnASmallTorus.SizeOfACopyProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
open Filter
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps RenormalizationStepParameters SlopeCoefficient
namespace RunningCouplingSlope.HessianOfSmallDensity
variable {n : ℕ}
theorem eventually_isCold_nhds_trivialField [NeZero n] {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ V in 𝓝 (trivialField n), IsCold σ V := by apply _root_.YangMills.SharedProofs.p23383 <;> assumption
theorem isCold_trivialField {σ : ℝ} (hσ : 0 < σ) : IsCold σ (trivialField n) := by apply _root_.YangMills.Construction.AbelianSecondOrder.isCold_trivialField <;> assumption
theorem centeredDensityTotal_eq_sum (f : LocalDensity) [hn : NeZero n] (V : TorusField n) :
    centeredDensityTotal f n V = ∑ y, centered f n y V := by
  unfold centeredDensityTotal
  rw [dif_neg hn.out]
theorem supDist_le_supportDiam_pair (y : TorusSite n) (c c' : TorusBond n) :
    _root_.YangMills.Construction.TorusFields.supDist y c.1 ≤ supportDiam y ![c, c'] ∧ _root_.YangMills.Construction.TorusFields.supDist c.1 c'.1 ≤ supportDiam y ![c, c'] := by
  constructor
  · refine le_trans ?_ (le_max_left _ _)
    exact Finset.le_sup (f := fun l : Fin 2 => _root_.YangMills.Construction.TorusFields.supDist y ((![c, c'] : Fin 2 → TorusBond n) l).1) (Finset.mem_univ (0 : Fin 2))
  · refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (Finset.le_sup (f := fun l : Fin 2 => Finset.univ.sup fun l' : Fin 2 =>
      _root_.YangMills.Construction.TorusFields.supDist ((![c, c'] : Fin 2 → TorusBond n) l).1 ((![c, c'] : Fin 2 → TorusBond n) l').1) (Finset.mem_univ (0 : Fin 2)))
    exact Finset.le_sup (f := fun l' : Fin 2 =>
      _root_.YangMills.Construction.TorusFields.supDist ((![c, c'] : Fin 2 → TorusBond n) 0).1 ((![c, c'] : Fin 2 → TorusBond n) l').1) (Finset.mem_univ (1 : Fin 2))
theorem supDist_comm (x y : TorusSite n) : _root_.YangMills.Construction.TorusFields.supDist x y = _root_.YangMills.Construction.TorusFields.supDist y x := by apply _root_.YangMills.SharedProofs.p9265 <;> assumption
theorem smallDensityHessianBound_of_expDecay (hS : ExpDecayTorusSumBounded) : SmallDensityHessianBound := by
  intro T hT
  have hrt : 0 < T.rt := hT.rt_pos
  set R : ℝ := T.rt / 2 ^ 10 with hR
  obtain ⟨S, hS0, hSum⟩ := hS (R / 2) (by positivity)
  refine ⟨S, R / 2, hS0, by positivity, fun y e g hy he hg n hn => ?_⟩
  have hfit := hT.fits y hy
  have hn₀ : (T.stepParameters y).n₀ ≤ n := hn
  have hn0 : n ≠ 0 := by
    have : 4096 ≤ (T.stepParameters y).n₀ := hfit.n₀_ge
    omega
  haveI : NeZero n := ⟨hn0⟩
  have hσ : 0 < (T.stepParameters y).threshold := hfit.σ_pos
  have hsm : ∀ (v : TorusSite n) (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => g n v (perturb c X σ (trivialField n))) 0 := fun v k c X =>
    hg.smooth n hn₀ v _ (isCold_trivialField hσ) k c X
  have hsum : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      (fun σ : Fin k → ℝ => centeredDensityTotal g n (perturb c X σ (trivialField n))) =
        ∑ v, (fun σ : Fin k → ℝ => g n v (perturb c X σ (trivialField n)) - g n v (trivialField n)) := by
    intro k c X
    funext σ
    rw [centeredDensityTotal_eq_sum, Finset.sum_apply]
    rfl
  have hsmooth : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => centeredDensityTotal g n (perturb c X σ (trivialField n))) 0 := by
    intro k c X
    rw [hsum]
    have hc : ∀ v ∈ (Finset.univ : Finset (TorusSite n)),
        ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => g n v (perturb c X σ (trivialField n)) - g n v (trivialField n)) 0 :=
      fun v _ => ((hsm v k c X).of_le (by norm_num)).sub contDiffAt_const
    have := ContDiffAt.sum hc
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun σ => ?_)
    simp [Finset.sum_apply]
  refine ⟨⟨hsmooth, ?_⟩, ?_⟩
  · have hnear : ∀ᶠ p : (TorusSite n → UnitQuaternion) × TorusField n in 𝓝 (1, trivialField n),
        IsCold (T.stepParameters y).threshold p.2 :=
      (continuous_snd.tendsto ((1 : TorusSite n → UnitQuaternion), trivialField n)).eventually
        (eventually_isCold_nhds_trivialField hσ)
    filter_upwards [hnear] with p hp
    rw [centeredDensityTotal_eq_sum, centeredDensityTotal_eq_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [centered]
    rw [hg.gauge n hn₀ v p.1 p.2 hp]
  · intro c c' X X' hX hX'
    have hexpand : hessianAtTrivial (centeredDensityTotal g) n c c' X X' =
        ∑ v, mixedDeriv (g n v) (trivialField n) ![c, c'] ![X, X'] := by
      unfold hessianAtTrivial mixedDeriv
      have hc : ∀ v ∈ (Finset.univ : Finset (TorusSite n)), ContDiffAt ℝ 2
          (fun σ : Fin 2 → ℝ => g n v (perturb ![c, c'] ![X, X'] σ (trivialField n)) - g n v (trivialField n)) 0 :=
        fun v _ => ((hsm v 2 _ _).of_le (by norm_num)).sub contDiffAt_const
      rw [hsum, iteratedFDeriv_sum_apply hc, ContinuousMultilinearMap.sum_apply]
      refine Finset.sum_congr rfl fun v _ => ?_
      have h1 : iteratedFDeriv ℝ 2
          (fun σ : Fin 2 → ℝ => g n v (perturb ![c, c'] ![X, X'] σ (trivialField n)) - g n v (trivialField n)) 0 =
          iteratedFDeriv ℝ 2 (fun σ : Fin 2 → ℝ => g n v (perturb ![c, c'] ![X, X'] σ (trivialField n))) 0 := by
        have h2 := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := 2)
          (f := fun σ : Fin 2 → ℝ => g n v (perturb ![c, c'] ![X, X'] σ (trivialField n)))
          (g := fun _ => g n v (trivialField n)) (x := 0) ((hsm v 2 _ _).of_le (by norm_num)) contDiffAt_const
        rw [iteratedFDeriv_const_of_ne (by norm_num)] at h2
        have h3 : iteratedFDeriv ℝ 2 (fun σ : Fin 2 → ℝ => g n v (perturb ![c, c'] ![X, X'] σ (trivialField n))) 0 -
            (0 : (Fin 2 → ℝ) → (Fin 2 → ℝ) [×2]→L[ℝ] ℝ) 0 =
            iteratedFDeriv ℝ 2 (fun σ : Fin 2 → ℝ => g n v (perturb ![c, c'] ![X, X'] σ (trivialField n))) 0 := by
          simp
        exact h2.trans h3
      rw [h1]
    have hun : AreUnitVectors ![X, X'] := by
      intro l
      fin_cases l
      · exact hX
      · exact hX'
    rw [hexpand]
    set d : ℝ := (_root_.YangMills.Construction.TorusFields.supDist c.1 c'.1 : ℝ) with hd
    have hv : ∀ v : TorusSite n, |mixedDeriv (g n v) (trivialField n) ![c, c'] ![X, X']| ≤
        e * Real.exp (-(R / 2 * d)) * Real.exp (-(R / 2 * _root_.YangMills.Construction.TorusFields.supDist c.1 v)) := by
      intro v
      have h1 := hg.decay n hn₀ v (trivialField n) (isCold_trivialField hσ) 2 ![c, c'] ![X, X'] (by norm_num)
        (by norm_num) hun
      have h2 : Real.exp (R * (supportDiam v ![c, c'] : ℝ)) ≤
          (T.stepParameters y).weight (supportDiam v ![c, c']) := by
        unfold StepParameters.weight StepParameters.weightRate
        exact le_mul_of_one_le_left (Real.exp_pos _).le (le_max_left _ _)
      have hw : 0 < Real.exp (R * (supportDiam v ![c, c'] : ℝ)) := Real.exp_pos _
      have h3 : e / (T.stepParameters y).weight (supportDiam v ![c, c']) ≤
          e * Real.exp (-(R * (supportDiam v ![c, c'] : ℝ))) := by
        rw [Real.exp_neg, ← div_eq_mul_inv]
        exact div_le_div_of_nonneg_left he hw h2
      obtain ⟨s1, s2⟩ := _root_.YangMills.Construction.RunningCouplingSlope.HessianOfSmallDensity.supDist_le_supportDiam_pair v c c'
      have s1' : (_root_.YangMills.Construction.TorusFields.supDist c.1 v : ℝ) ≤ supportDiam v ![c, c'] := by
        rw [_root_.YangMills.Construction.RunningCouplingSlope.HessianOfSmallDensity.supDist_comm]
        exact_mod_cast s1
      have s2' : d ≤ supportDiam v ![c, c'] := by
        rw [hd]
        exact_mod_cast s2
      have h4 : Real.exp (-(R * (supportDiam v ![c, c'] : ℝ))) ≤
          Real.exp (-(R / 2 * d)) * Real.exp (-(R / 2 * _root_.YangMills.Construction.TorusFields.supDist c.1 v)) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        nlinarith
      calc _ ≤ e * Real.exp (-(R * (supportDiam v ![c, c'] : ℝ))) := h1.trans h3
        _ ≤ e * (Real.exp (-(R / 2 * d)) * Real.exp (-(R / 2 * _root_.YangMills.Construction.TorusFields.supDist c.1 v))) :=
            mul_le_mul_of_nonneg_left h4 he
        _ = _ := by ring
    calc |∑ v, mixedDeriv (g n v) (trivialField n) ![c, c'] ![X, X']|
        ≤ ∑ v, |mixedDeriv (g n v) (trivialField n) ![c, c'] ![X, X']| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ v : TorusSite n, e * Real.exp (-(R / 2 * d)) * Real.exp (-(R / 2 * _root_.YangMills.Construction.TorusFields.supDist c.1 v)) :=
          Finset.sum_le_sum fun v _ => hv v
      _ = e * Real.exp (-(R / 2 * d)) * ∑ v : TorusSite n, Real.exp (-(R / 2 * _root_.YangMills.Construction.TorusFields.supDist c.1 v)) := by
          rw [Finset.mul_sum]
      _ ≤ e * Real.exp (-(R / 2 * d)) * S :=
          mul_le_mul_of_nonneg_left (hSum n c.1) (by positivity)
      _ = _ := by ring
end RunningCouplingSlope.HessianOfSmallDensity
end YangMills.Construction
end
