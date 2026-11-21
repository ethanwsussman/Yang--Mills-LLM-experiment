import YangMills.Construction.ColdChainAtEveryLevel.DerivativesAlongLines
import YangMills.Construction.ColdChainAtEveryLevel.SeminormsOfCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ChartCoordinates
open BlockAverages LineDerivatives CoordinateSeminorms
variable {F : BlockFrame}
abbrev ChartPoint (F : BlockFrame) : Type :=
  ChartVector F × (F.Site F.top → Fin 4 → imaginaryQuaternions)
def onChartPoints (Φ : ChainChart F → (F.Site F.top → Fin 4 → imaginaryQuaternions) → ℝ)
    (x : ChartPoint F) : ℝ :=
  Φ (toChart x.1) x.2
def chartPoint (A : ChainChart F) (e : F.Site F.top → Fin 4 → imaginaryQuaternions) : ChartPoint F :=
  (ofChart A, e)
variable {Φ : ChainChart F → (F.Site F.top → Fin 4 → imaginaryQuaternions) → ℝ}
theorem alongDirections_onChartPoints {k : ℕ} (U : ChainChart F) (A : Fin k → ChainChart F)
    (e : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions) :
    alongDirections (onChartPoints Φ) (chartPoint U 0) (fun l => chartPoint (A l) (e l)) =
      fun t => Φ (chartShiftAlong U A t) (topVariationAlong e t) := by
  funext t
  unfold alongDirections onChartPoints chartPoint
  have h1 : toChart ((ofChart U, (0 : F.Site F.top → Fin 4 → imaginaryQuaternions)) +
      ∑ l, t l • (ofChart (A l), e l)).1 = chartShiftAlong U A t := by
    apply chainChart_ext
    · funext x i
      simp [toChart, ofChart, chartShiftAlong, Prod.fst_sum, Finset.sum_apply]
    · funext j x i
      simp [toChart, ofChart, chartShiftAlong, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
  have h2 : ((ofChart U, (0 : F.Site F.top → Fin 4 → imaginaryQuaternions)) +
      ∑ l, t l • (ofChart (A l), e l)).2 = topVariationAlong e t := by
    funext y i
    simp [topVariationAlong, Prod.snd_sum, Finset.sum_apply]
  rw [h1, h2]
theorem mixedDeriv_onChartPoints {k : ℕ} (U : ChainChart F) (A : Fin k → ChainChart F)
    (e : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions) :
    mixedDeriv (onChartPoints Φ) (chartPoint U 0) (fun l => chartPoint (A l) (e l)) =
      localIteratedDeriv Φ U A e := by
  unfold mixedDeriv localIteratedDeriv
  rw [alongDirections_onChartPoints]
theorem analyticAlongDirections_of_isLocalObservable {S : Finset F.Cell} {R : F.FieldChain} {Y : F.Cell}
    {B : Finset (F.Site F.top × Fin 4)} {Ck : ℕ → ℝ}
    {U : ChainChart F} (h : IsLocalRepresentation S R Y B Ck U Φ) :
    AnalyticAlongDirections (onChartPoints Φ) (chartPoint U 0) := by
  intro k A
  have e : A = fun l => chartPoint (toChart (A l).1) (A l).2 := rfl
  rw [e, alongDirections_onChartPoints]
  exact h.analyticAt _ _
theorem chartPoint_add_smul (U D : ChainChart F) (r : ℝ) :
    chartPoint U 0 + r • chartPoint D 0 = chartPoint (chartMove U D r) 0 := by
  apply Prod.ext
  · apply Prod.ext
    · funext x i
      simp [chartPoint, ofChart, chartMove]
    · funext j x i
      simp [chartPoint, ofChart, chartMove]
  · funext y i
    simp [chartPoint]
theorem mixedDeriv_update_add {E : Type*} [AddCommGroup E] [Module ℝ E] {J : E → ℝ} {W : E}
    (hW : AnalyticAlongDirections J W) {m : ℕ} (a : Fin m → E) (l : Fin m) (x y : E) :
    mixedDeriv J W (Function.update a l (x + y)) =
      mixedDeriv J W (Function.update a l x) + mixedDeriv J W (Function.update a l y) := by
  classical
  set T : Fin (m + 2) → E := Fin.snoc (Fin.snoc a x : Fin (m + 1) → E) y with hT
  set i₀ : Fin m → Fin (m + 2) := fun i => i.castSucc.castSucc with hi₀
  set ix : Fin (m + 2) := (Fin.last m).castSucc with hix
  set iy : Fin (m + 2) := Fin.last (m + 1) with hiy
  have T0 : ∀ i, T (i₀ i) = a i := fun i => by simp [hT, hi₀]
  have Tx : T ix = x := by simp [hT, hix]
  have Ty : T iy = y := by simp [hT, hiy]
  let standingConstraints : Fin m → Fin (m + 2) → ℝ := fun i => Pi.single (i₀ i) 1
  let rx : Fin (m + 2) → ℝ := Pi.single ix 1
  let ry : Fin (m + 2) → ℝ := Pi.single iy 1
  have hsum : ∀ j, ∑ p, (Pi.single j (1 : ℝ) : Fin (m + 2) → ℝ) p • T p = T j := fun j => by
    simp [Pi.single_apply]
  have e : ∀ (r : Fin (m + 2) → ℝ) (z : E), (∑ p, r p • T p = z) →
      mixedDeriv J W (Function.update a l z) =
        iteratedFDeriv ℝ m (alongDirections J W T) 0 (Function.update standingConstraints l r) := by
    intro r z hz
    rw [← mixedDeriv_linComb hW T (Function.update standingConstraints l r)]
    congr 1
    funext i
    by_cases hi : i = l
    · subst hi
      simp [hz]
    · simp only [Function.update_of_ne hi, standingConstraints, hsum, T0]
  have ex := e rx x (by rw [hsum, Tx])
  have ey := e ry y (by rw [hsum, Ty])
  have exy := e (rx + ry) (x + y) (by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    rw [hsum, hsum, Tx, Ty])
  rw [ex, ey, exy, ContinuousMultilinearMap.map_update_add]
theorem mixedDeriv_add_sub_eq_sum {E : Type*} [AddCommGroup E] [Module ℝ E] {J : E → ℝ} {W : E}
    (hW : AnalyticAlongDirections J W) {m : ℕ} (a g : Fin m → E) :
    mixedDeriv J W (fun i => a i + g i) - mixedDeriv J W a = ∑ l : Fin m,
      mixedDeriv J W (fun i => if i < l then a i + g i else if i = l then g i else a i) := by
  classical
  set v : ℕ → Fin m → E := fun k i => if i.val < k then a i + g i else a i with hv
  have e0 : v 0 = a := by
    funext i
    simp [hv]
  have em : v m = fun i => a i + g i := by
    funext i
    simp [hv, i.isLt]
  have hstep : ∀ l : Fin m, mixedDeriv J W (v (l.val + 1)) - mixedDeriv J W (v l.val) =
      mixedDeriv J W (fun i => if i < l then a i + g i else if i = l then g i else a i) := by
    intro l
    have e1 : v (l.val + 1) = Function.update (v l.val) l (a l + g l) := by
      funext i
      by_cases hi : i = l
      · subst hi
        simp [hv]
      · have hne : i.val ≠ l.val := fun h => hi (Fin.ext h)
        rw [Function.update_of_ne hi]
        simp only [hv]
        by_cases h1 : i.val < l.val
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]
    have e2 : v l.val = Function.update (v l.val) l (a l) := by
      funext i
      by_cases hi : i = l
      · subst hi
        simp [hv]
      · rw [Function.update_of_ne hi]
    have e3 : (fun i => if i < l then a i + g i else if i = l then g i else a i) =
        Function.update (v l.val) l (g l) := by
      funext i
      by_cases hi : i = l
      · subst hi
        simp
      · rw [Function.update_of_ne hi]
        simp only [hv, hi, if_false, Fin.lt_def]
    rw [e1, e3, mixedDeriv_update_add hW]
    nth_rewrite 2 [e2]
    ring_nf
    rw [show Function.update (v l.val) l (a l) = v l.val from e2.symm]
    ring
  rw [← em]
  have := Finset.sum_range_sub (fun k => mixedDeriv J W (v k)) m
  rw [e0] at this
  rw [← this, Finset.sum_range]
  exact Finset.sum_congr rfl fun l _ => hstep l
section Comparison
variable {S : Finset F.Cell} {R : F.FieldChain} {Y : F.Cell} {B : Finset (F.Site F.top × Fin 4)}
  {Ck : ℕ → ℝ}
theorem cons_chartPoint {m : ℕ} (D : ChainChart F) (A : Fin m → ChainChart F)
    (e : Fin m → F.Site F.top → Fin 4 → imaginaryQuaternions) :
    (Fin.cons (chartPoint D 0) (fun l => chartPoint (A l) (e l)) : Fin (m + 1) → ChartPoint F) =
      fun l => chartPoint ((Fin.cons D A : Fin (m + 1) → ChainChart F) l)
        ((Fin.cons (0 : F.Site F.top → Fin 4 → imaginaryQuaternions) e :
          Fin (m + 1) → F.Site F.top → Fin 4 → imaginaryQuaternions) l) := by
  funext l
  refine Fin.cases rfl (fun i => rfl) l
theorem abs_evaluationIteratedDeriv_sub_le_of_segment {U D : ChainChart F}
    (hl : ∀ r ∈ Set.Icc (0 : ℝ) 1, IsLocalRepresentation S R Y B Ck (chartMove U D r) Φ)
    {m : ℕ} (A : Fin m → ChainChart F) (e : Fin m → F.Site F.top → Fin 4 → imaginaryQuaternions) {K : ℝ}
    (hb : ∀ r ∈ Set.Icc (0 : ℝ) 1, |localIteratedDeriv Φ (chartMove U D r)
      (Fin.cons D A : Fin (m + 1) → ChainChart F)
      (Fin.cons (0 : F.Site F.top → Fin 4 → imaginaryQuaternions) e :
        Fin (m + 1) → F.Site F.top → Fin 4 → imaginaryQuaternions)| ≤ K) :
    |localIteratedDeriv Φ (chartMove U D 1) A e - localIteratedDeriv Φ U A e| ≤ K := by
  have hG : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      AnalyticAlongDirections (onChartPoints Φ) (chartPoint U 0 + r • chartPoint D 0) := fun r hr => by
    rw [chartPoint_add_smul]
    exact analyticAlongDirections_of_isLocalObservable (hl r hr)
  have h := abs_mixedDeriv_sub_sub_le hG (fun l => chartPoint (A l) (e l)) 0 K (fun r hr => by
    rw [chartPoint_add_smul, cons_chartPoint, mixedDeriv_onChartPoints, sub_zero]
    exact hb r hr)
  have e1 : chartPoint U 0 + chartPoint D 0 = chartPoint (chartMove U D 1) 0 := by
    rw [← chartPoint_add_smul, one_smul]
  rw [e1, mixedDeriv_onChartPoints, mixedDeriv_onChartPoints, sub_zero] at h
  exact h
theorem localDirectionSize_zero (D : ChainChart F) :
    localDirectionSize S R B Y D 0 = localNorm S R D (oneSiteWeights F) Y := by
  unfold localDirectionSize topVariationNorm
  simp
theorem prod_localDirectionSize_cons {m : ℕ} (D : ChainChart F) (A : Fin m → ChainChart F)
    (e : Fin m → F.Site F.top → Fin 4 → imaginaryQuaternions) :
    ∏ l, localDirectionSize S R B Y ((Fin.cons D A : Fin (m + 1) → ChainChart F) l)
        ((Fin.cons (0 : F.Site F.top → Fin 4 → imaginaryQuaternions) e :
          Fin (m + 1) → F.Site F.top → Fin 4 → imaginaryQuaternions) l) =
      localNorm S R D (oneSiteWeights F) Y * ∏ l, localDirectionSize S R B Y (A l) (e l) := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, localDirectionSize_zero]
theorem localDirectionSize_nonneg (A : ChainChart F) (e : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    0 ≤ localDirectionSize S R B Y A e := by
  unfold localDirectionSize topVariationNorm localNorm
  exact add_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
theorem chartMove_chartMove_neg_one (A A₂ : ChainChart F) :
    chartMove A₂ (chartMove A A₂ (-1)) 1 = A := by
  apply chainChart_ext
  · funext x i
    simp only [chartMove, one_smul]
    module
  · funext j x i
    simp only [chartMove, one_smul]
    module
theorem chartMove_self_chartMove_neg_one (A A₂ : ChainChart F) :
    chartMove A (chartMove A A₂ (-1)) (-1) = A₂ := by
  apply chainChart_ext
  · funext x i
    simp only [chartMove]
    module
  · funext j x i
    simp only [chartMove]
    module
theorem localNorm_le_add_localNorm_sub (A A₂ : ChainChart F) :
    localNorm S R A₂ (oneSiteWeights F) Y ≤ localNorm S R A (oneSiteWeights F) Y +
      localNorm S R (chartMove A A₂ (-1)) (oneSiteWeights F) Y := by
  have h := localNorm_chartMove_le S R A (chartMove A A₂ (-1)) (-1) (oneSiteWeights F)
    (fun _ _ => zero_le_one) Y
  rw [chartMove_self_chartMove_neg_one] at h
  simpa using h
theorem abs_evaluationIteratedDeriv_sub_le {U : ChainChart F} (h : IsLocalRepresentation S R Y B Ck U Φ)
    (hCk : ∀ k, 0 ≤ Ck k) {m : ℕ} (A A₂ : Fin m → ChainChart F)
    (e : Fin m → F.Site F.top → Fin 4 → imaginaryQuaternions) :
    |localIteratedDeriv Φ U A e - localIteratedDeriv Φ U A₂ e| ≤ Ck m * ∑ l,
      localNorm S R (chartMove (A l) (A₂ l) (-1)) (oneSiteWeights F) Y * ∏ l' ∈ Finset.univ.erase l,
        (localDirectionSize S R B Y (A l') (e l') +
          localNorm S R (chartMove (A l') (A₂ l') (-1)) (oneSiteWeights F) Y) := by
  classical
  set G : Fin m → ChainChart F := fun l => chartMove (A l) (A₂ l) (-1) with hG
  have hW := analyticAlongDirections_of_isLocalObservable h
  have hs := mixedDeriv_add_sub_eq_sum hW (fun i => chartPoint (A₂ i) (e i)) (fun i => chartPoint (G i) 0)
  have e1 : (fun i => chartPoint (A₂ i) (e i) + chartPoint (G i) 0) = fun i => chartPoint (A i) (e i) := by
    funext i
    apply Prod.ext
    · have := chartMove_chartMove_neg_one (A i) (A₂ i)
      apply Prod.ext
      · funext x j
        have h1 := congrArg (fun Z : ChainChart F => Z.fine x j) this
        simpa [chartPoint, ofChart, chartMove, hG] using h1
      · funext k x j
        have h1 := congrArg (fun Z : ChainChart F => Z.coarse k x j) this
        simpa [chartPoint, ofChart, chartMove, hG] using h1
    · simp [chartPoint]
  rw [e1, mixedDeriv_onChartPoints, mixedDeriv_onChartPoints] at hs
  rw [hs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  set Cc : Fin m → ChainChart F := fun i => if i < l then A i else if i = l then G i else A₂ i with hCc
  set Ee : Fin m → F.Site F.top → Fin 4 → imaginaryQuaternions := fun i => if i = l then 0 else e i with hEe
  have e2 : (fun i => if i < l then chartPoint (A i) (e i) else if i = l then chartPoint (G i) 0
      else chartPoint (A₂ i) (e i)) = fun i => chartPoint (Cc i) (Ee i) := by
    funext i
    simp only [hCc, hEe]
    by_cases h1 : i < l
    · have h2 : i ≠ l := ne_of_lt h1
      rw [if_pos h1, if_pos h1, if_neg h2]
    · by_cases h2 : i = l
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, if_pos h2]
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, if_neg h2]
  have e3 : (fun i => if i < l then chartPoint (A₂ i) (e i) + chartPoint (G i) 0
      else if i = l then chartPoint (G i) 0 else chartPoint (A₂ i) (e i)) =
      fun i => if i < l then chartPoint (A i) (e i) else if i = l then chartPoint (G i) 0
        else chartPoint (A₂ i) (e i) := by
    funext i
    by_cases h1 : i < l
    · rw [if_pos h1, if_pos h1]
      exact congrFun e1 i
    · rw [if_neg h1, if_neg h1]
  rw [e3, e2, mixedDeriv_onChartPoints]
  have hb := h.iteratedDeriv_le m Cc Ee
  rw [Real.norm_eq_abs] at hb
  refine hb.trans (mul_le_mul_of_nonneg_left ?_ (hCk m))
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l)]
  have h0 : localDirectionSize S R B Y (Cc l) (Ee l) = localNorm S R (G l) (oneSiteWeights F) Y := by
    simp only [hCc, hEe, lt_irrefl, if_false, if_true, localDirectionSize_zero]
  rw [h0]
  refine mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod (fun i _ => localDirectionSize_nonneg _ _) fun i hi => ?_) (Real.sqrt_nonneg _)
  have hil : i ≠ l := (Finset.mem_erase.1 hi).1
  have hGn : 0 ≤ localNorm S R (G i) (oneSiteWeights F) Y := Real.sqrt_nonneg _
  simp only [hCc, hEe, if_neg hil]
  by_cases h1 : i < l
  · rw [if_pos h1]
    linarith
  · rw [if_neg h1]
    have := localNorm_le_add_localNorm_sub (S := S) (R := R) (Y := Y) (A i) (A₂ i)
    unfold localDirectionSize at *
    linarith
theorem localIteratedDeriv_zero (Φ : ChainChart F → (F.Site F.top → Fin 4 → imaginaryQuaternions) → ℝ)
    (U : ChainChart F) (A : Fin 0 → ChainChart F) (e : Fin 0 → F.Site F.top → Fin 4 → imaginaryQuaternions) :
    localIteratedDeriv Φ U A e = Φ U (fun _ _ => 0) := by
  unfold localIteratedDeriv
  rw [iteratedFDeriv_zero_apply]
  have h1 : chartShiftAlong U A 0 = U := by
    obtain ⟨u, mu⟩ := U
    simp [chartShiftAlong]
  have h2 : topVariationAlong e 0 = fun _ _ => 0 := by
    funext y i
    simp [topVariationAlong]
  simp only [h1, h2]
theorem localIteratedDeriv_sub_of_one {U : ChainChart F} (h : IsLocalRepresentation S R Y B Ck U Φ)
    (A A₂ : Fin 1 → ChainChart F) (e : Fin 1 → F.Site F.top → Fin 4 → imaginaryQuaternions) :
    localIteratedDeriv Φ U A e - localIteratedDeriv Φ U A₂ e =
      localIteratedDeriv Φ U (fun l => chartMove (A l) (A₂ l) (-1)) (fun _ => 0) := by
  classical
  have hW := analyticAlongDirections_of_isLocalObservable h
  have hs := mixedDeriv_add_sub_eq_sum hW (fun i => chartPoint (A₂ i) (e i))
    (fun i => chartPoint (chartMove (A i) (A₂ i) (-1)) 0)
  have e1 : (fun i => chartPoint (A₂ i) (e i) + chartPoint (chartMove (A i) (A₂ i) (-1)) 0) =
      fun i => chartPoint (A i) (e i) := by
    funext i
    apply Prod.ext
    · have := chartMove_chartMove_neg_one (A i) (A₂ i)
      apply Prod.ext
      · funext x j
        have h1 := congrArg (fun Z : ChainChart F => Z.fine x j) this
        simpa [chartPoint, ofChart, chartMove] using h1
      · funext k x j
        have h1 := congrArg (fun Z : ChainChart F => Z.coarse k x j) this
        simpa [chartPoint, ofChart, chartMove] using h1
    · simp [chartPoint]
  rw [e1, mixedDeriv_onChartPoints, mixedDeriv_onChartPoints] at hs
  rw [hs, Fin.sum_univ_one]
  have e2 : (fun i : Fin 1 => if i < 0 then chartPoint (A₂ i) (e i) + chartPoint (chartMove (A i) (A₂ i) (-1)) 0
      else if i = 0 then chartPoint (chartMove (A i) (A₂ i) (-1)) 0 else chartPoint (A₂ i) (e i)) =
      fun i => chartPoint (chartMove (A i) (A₂ i) (-1)) 0 := by
    funext i
    have : i = 0 := Subsingleton.elim _ _
    subst this
    simp
  rw [e2]
  have e3 := mixedDeriv_onChartPoints (Φ := Φ) U (fun l => chartMove (A l) (A₂ l) (-1)) (fun _ => 0)
  exact e3
end Comparison
end YangMills.Construction.ChartCoordinates
end
