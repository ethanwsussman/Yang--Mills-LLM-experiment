import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace YangMills.Construction
namespace LineDerivatives
section Composition
variable {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
theorem iteratedFDeriv_comp_continuousLinearMap {f : H → ℝ} (T : G →L[ℝ] H) {x : G}
    (hf : AnalyticAt ℝ f (T x)) (k : ℕ) (v : Fin k → G) :
    iteratedFDeriv ℝ k (f ∘ T) x v = iteratedFDeriv ℝ k f (T x) (fun i => T (v i)) := by
  obtain ⟨s, hs, hso, hxs⟩ := eventually_nhds_iff.1 hf.eventually_analyticAt
  have hc : ContDiffOn ℝ k f s := fun y hy => ((hs y hy).contDiffAt.of_le le_top).contDiffWithinAt
  have hpre : IsOpen (T ⁻¹' s) := hso.preimage T.continuous
  have h := T.iteratedFDerivWithin_comp_right hc hso.uniqueDiffOn hpre.uniqueDiffOn hxs (i := k) le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hpre (show x ∈ T ⁻¹' s from hxs),
    iteratedFDerivWithin_of_isOpen k hso hxs] at h
  rw [h]
  rfl
end Composition
variable {E : Type*} [AddCommGroup E] [Module ℝ E] (J : E → ℝ)
def alongDirections (U : E) {k : ℕ} (A : Fin k → E) (t : Fin k → ℝ) : ℝ := J (U + ∑ l, t l • A l)
def AnalyticAlongDirections (U : E) : Prop := ∀ (k : ℕ) (A : Fin k → E), AnalyticAt ℝ (alongDirections J U A) 0
def mixedDeriv (U : E) {k : ℕ} (A : Fin k → E) : ℝ :=
  iteratedFDeriv ℝ k (alongDirections J U A) 0 (fun l => Pi.single l 1)
variable {J}
def coeffMap {k m : ℕ} (M : Fin k → Fin m → ℝ) : (Fin k → ℝ) →L[ℝ] (Fin m → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun t l => ∑ i, t i * M i l
      map_add' := fun t t' => by
        funext l
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r t => by
        funext l
        simp [Finset.mul_sum, mul_assoc] }
theorem coeffMap_apply {k m : ℕ} (M : Fin k → Fin m → ℝ) (t : Fin k → ℝ) (l : Fin m) :
    coeffMap M t l = ∑ i, t i * M i l := rfl
theorem coeffMap_single {k m : ℕ} (M : Fin k → Fin m → ℝ) (i : Fin k) :
    coeffMap M (Pi.single i 1) = M i := by
  funext l
  rw [coeffMap_apply, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp
theorem alongDirections_linComb {U : E} {k m : ℕ} (A : Fin m → E) (M : Fin k → Fin m → ℝ) :
    alongDirections J U (fun i => ∑ l, M i l • A l) = alongDirections J U A ∘ coeffMap M := by
  funext t
  simp only [alongDirections, Function.comp, coeffMap_apply]
  congr 2
  simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
theorem mixedDeriv_linComb {U : E} (hU : AnalyticAlongDirections J U) {k m : ℕ} (A : Fin m → E)
    (M : Fin k → Fin m → ℝ) :
    mixedDeriv J U (fun i => ∑ l, M i l • A l) = iteratedFDeriv ℝ k (alongDirections J U A) 0 M := by
  unfold mixedDeriv
  rw [alongDirections_linComb, iteratedFDeriv_comp_continuousLinearMap _ (by simpa using hU m A)]
  simp [coeffMap_single]
theorem alongDirections_single (U A : E) (τ : ℝ) :
    alongDirections J U ![A] (fun _ => τ) = J (U + τ • A) := by
  simp [alongDirections]
theorem hasDerivAt_along {U : E} (hU : AnalyticAlongDirections J U) (A : E) :
    HasDerivAt (fun τ : ℝ => J (U + τ • A)) (mixedDeriv J U ![A]) 0 := by
  have h1 : HasFDerivAt (alongDirections J U ![A]) (fderiv ℝ (alongDirections J U ![A]) 0)
      ((fun _ => (0 : ℝ)) : Fin 1 → ℝ) :=
    ((hU 1 ![A]).differentiableAt).hasFDerivAt
  have h2 : HasDerivAt (fun τ : ℝ => ((fun _ => τ) : Fin 1 → ℝ)) (fun _ => (1 : ℝ)) 0 :=
    hasDerivAt_pi.2 fun _ => hasDerivAt_id _
  have h3 := h1.comp_hasDerivAt (0 : ℝ) h2
  have e : (alongDirections J U ![A] ∘ fun τ : ℝ => ((fun _ => τ) : Fin 1 → ℝ)) =
      fun τ : ℝ => J (U + τ • A) := by
    funext τ
    exact alongDirections_single U A τ
  rw [e] at h3
  have e2 : mixedDeriv J U ![A] = fderiv ℝ (alongDirections J U ![A]) 0 (fun _ => (1 : ℝ)) := by
    unfold mixedDeriv
    rw [iteratedFDeriv_one_apply]
    congr 1
    funext i
    fin_cases i
    simp
  rw [e2]
  exact h3
theorem deriv_along {U : E} (hU : AnalyticAlongDirections J U) (A : E) :
    deriv (fun τ : ℝ => J (U + τ • A)) 0 = mixedDeriv J U ![A] := (hasDerivAt_along hU A).deriv
def consZeroMap (k : ℕ) : (Fin k → ℝ) →L[ℝ] (Fin (k + 1) → ℝ) :=
  coeffMap fun i => Pi.single i.succ 1
theorem consZeroMap_apply (k : ℕ) (t : Fin k → ℝ) : consZeroMap k t = Fin.cons 0 t := by
  funext l
  refine Fin.cases ?_ (fun i => ?_) l
  · simp [consZeroMap, coeffMap_apply]
  · simp only [consZeroMap, coeffMap_apply, Fin.cons_succ]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      have : i.succ ≠ b.succ := fun h => hb (Fin.succ_injective _ h).symm
      simp [Pi.single_eq_of_ne this]
    · simp
theorem hasDerivAt_mixedDeriv {W : E} (hW : AnalyticAlongDirections J W) (X : E) {k : ℕ} (A : Fin k → E) :
    HasDerivAt (fun r : ℝ => mixedDeriv J (W + r • X) A)
      (mixedDeriv J W (Fin.cons X A : Fin (k + 1) → E)) 0 := by
  set ψ := alongDirections J W (Fin.cons X A : Fin (k + 1) → E) with hψ
  have hana : AnalyticAt ℝ ψ 0 := hW _ _
  set e0 : Fin (k + 1) → ℝ := Pi.single 0 1 with he0
  set v : Fin k → (Fin (k + 1) → ℝ) := fun i => Pi.single i.succ 1 with hv
  have hcont : Tendsto (fun r : ℝ => r • e0) (𝓝 0) (𝓝 0) := by
    have : Continuous fun r : ℝ => r • e0 := by fun_prop
    simpa using this.tendsto 0
  have hev : ∀ᶠ r : ℝ in 𝓝 0, AnalyticAt ℝ ψ (r • e0) := hcont.eventually hana.eventually_analyticAt
  have hline : ∀ r : ℝ, alongDirections J (W + r • X) A = (fun y => ψ (r • e0 + y)) ∘ consZeroMap k := by
    intro r
    funext t
    simp only [Function.comp, hψ, alongDirections, consZeroMap_apply, Fin.sum_univ_succ]
    congr 1
    have : (r • e0 + Fin.cons 0 t : Fin (k + 1) → ℝ) 0 = r := by simp [he0]
    rw [this]
    have h2 : ∀ i : Fin k, (r • e0 + Fin.cons 0 t : Fin (k + 1) → ℝ) i.succ = t i := by
      intro i
      simp [he0]
    simp only [h2, Fin.cons_zero, Fin.cons_succ, add_assoc]
  have hT : ∀ i : Fin k, consZeroMap k (Pi.single i 1) = v i := fun i => coeffMap_single _ i
  have heq : ∀ᶠ r : ℝ in 𝓝 0, mixedDeriv J (W + r • X) A = iteratedFDeriv ℝ k ψ (r • e0) v := by
    filter_upwards [hev] with r hr
    unfold mixedDeriv
    have hshift : AnalyticAt ℝ (fun y => ψ (r • e0 + y)) (consZeroMap k 0) := by
      have h1 : AnalyticAt ℝ (fun y : Fin (k + 1) → ℝ => r • e0 + y) (consZeroMap k 0) :=
        analyticAt_const.add analyticAt_id
      exact AnalyticAt.comp_of_eq (g := ψ) hr h1 (by simp)
    rw [hline r, iteratedFDeriv_comp_continuousLinearMap (consZeroMap k) hshift]
    simp only [hT, map_zero]
    rw [iteratedFDeriv_comp_add_left]
    simp
  have hG : DifferentiableAt ℝ (iteratedFDeriv ℝ k ψ) 0 :=
    (hana.contDiffAt.differentiableAt_iteratedFDeriv (m := k) (by exact_mod_cast WithTop.coe_lt_top _))
  have hcurve : HasDerivAt (fun r : ℝ => r • e0) e0 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const e0
  have h1 : HasDerivAt (fun r : ℝ => iteratedFDeriv ℝ k ψ (r • e0))
      (fderiv ℝ (iteratedFDeriv ℝ k ψ) 0 e0) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hG.hasFDerivAt hcurve (by simp)
  have h2 : HasDerivAt (fun r : ℝ => iteratedFDeriv ℝ k ψ (r • e0) v)
      (fderiv ℝ (iteratedFDeriv ℝ k ψ) 0 e0 v) 0 := by
    have := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin (k + 1) → ℝ) ℝ v).hasFDerivAt).comp_hasDerivAt
      (0 : ℝ) h1
    exact this
  have e3 : mixedDeriv J W (Fin.cons X A : Fin (k + 1) → E) = fderiv ℝ (iteratedFDeriv ℝ k ψ) 0 e0 v := by
    unfold mixedDeriv
    have e4 : (Fin.tail fun l : Fin (k + 1) => (Pi.single l 1 : Fin (k + 1) → ℝ)) = v := by
      funext i
      simp [Fin.tail, hv]
    rw [iteratedFDeriv_succ_apply_left, e4]
  rw [e3]
  exact h2.congr_of_eventuallyEq heq
theorem hasDerivAt_mixedDeriv_at {W X : E} {r : ℝ} (hW : AnalyticAlongDirections J (W + r • X)) {k : ℕ}
    (A : Fin k → E) :
    HasDerivAt (fun r' : ℝ => mixedDeriv J (W + r' • X) A)
      (mixedDeriv J (W + r • X) (Fin.cons X A : Fin (k + 1) → E)) r := by
  have h := hasDerivAt_mixedDeriv hW X A
  have h1 : HasDerivAt (fun r' : ℝ => mixedDeriv J ((W + r • X) + (r' - r) • X) A)
      (mixedDeriv J (W + r • X) (Fin.cons X A : Fin (k + 1) → E)) r := by
    have h2 : HasDerivAt (fun q : ℝ => mixedDeriv J ((W + r • X) + q • X) A)
        (mixedDeriv J (W + r • X) (Fin.cons X A : Fin (k + 1) → E)) (r - r) := by
      simpa using h
    exact h2.comp_sub_const r r
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun r' => ?_)
  have : (W + r • X) + (r' - r) • X = W + r' • X := by
    rw [sub_smul]
    abel
  simp only [this]
theorem abs_mixedDeriv_sub_sub_le {W X : E} (hG : ∀ r ∈ Set.Icc (0 : ℝ) 1, AnalyticAlongDirections J (W + r • X))
    {k : ℕ} (A : Fin k → E) (Q K : ℝ) (hb : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      |mixedDeriv J (W + r • X) (Fin.cons X A : Fin (k + 1) → E) - Q| ≤ K) :
    |mixedDeriv J (W + X) A - mixedDeriv J W A - Q| ≤ K := by
  set f : ℝ → ℝ := fun r => mixedDeriv J (W + r • X) A - r * Q with hf
  have hd : ∀ r ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f
      (mixedDeriv J (W + r • X) (Fin.cons X A : Fin (k + 1) → E) - Q) (Set.Icc 0 1) r := by
    intro r hr
    have h1 := hasDerivAt_mixedDeriv_at (hG r hr) A
    have h2 : HasDerivAt (fun r : ℝ => r * Q) Q r := by
      simpa using (hasDerivAt_id r).mul_const Q
    exact (h1.sub h2).hasDerivWithinAt
  have h3 := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hd
    (fun r hr => by simpa using hb r hr) (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  simp only [hf] at h3
  simp only [one_smul, zero_smul, add_zero, one_mul, zero_mul, sub_zero, Real.norm_eq_abs] at h3
  have e : mixedDeriv J (W + X) A - Q - mixedDeriv J W A = mixedDeriv J (W + X) A - mixedDeriv J W A - Q := by
    ring
  rw [e] at h3
  simpa using h3
theorem mixedDeriv_one_add {U : E} (hU : AnalyticAlongDirections J U) (A A' : E) :
    mixedDeriv J U ![A + A'] = mixedDeriv J U ![A] + mixedDeriv J U ![A'] := by
  have hh : ∀ t t' : ℝ, mixedDeriv J U ![t • A + t' • A'] =
      t * fderiv ℝ (alongDirections J U ![A, A']) 0 (Pi.single 0 1) +
        t' * fderiv ℝ (alongDirections J U ![A, A']) 0 (Pi.single 1 1) := by
    intro t t'
    have e : (![t • A + t' • A'] : Fin 1 → E) =
        fun i => ∑ l, (![![t, t']] : Fin 1 → Fin 2 → ℝ) i l • (![A, A'] : Fin 2 → E) l := by
      funext i
      fin_cases i
      simp [Fin.sum_univ_two]
    have e3 : (![![t, t']] : Fin 1 → Fin 2 → ℝ) 0 = t • Pi.single 0 1 + t' • Pi.single 1 1 := by
      funext i
      fin_cases i <;> simp
    rw [e, mixedDeriv_linComb hU, iteratedFDeriv_one_apply]
    rw [e3, map_add, map_smul, map_smul]
    simp
  have h1 := hh 1 1
  have h2 := hh 1 0
  have h3 := hh 0 1
  simp only [one_smul, zero_smul, add_zero, zero_add, one_mul, zero_mul] at h1 h2 h3
  rw [h1, h2, h3]
theorem mixedDeriv_one_smul {U : E} (hU : AnalyticAlongDirections J U) (t : ℝ) (A : E) :
    mixedDeriv J U ![t • A] = t * mixedDeriv J U ![A] := by
  have e : (![t • A] : Fin 1 → E) = fun i => ∑ l, (![![t]] : Fin 1 → Fin 1 → ℝ) i l • (![A] : Fin 1 → E) l := by
    funext i
    fin_cases i
    simp
  have e' : (![A] : Fin 1 → E) = fun i => ∑ l, (![![1]] : Fin 1 → Fin 1 → ℝ) i l • (![A] : Fin 1 → E) l := by
    funext i
    fin_cases i
    simp
  rw [e, mixedDeriv_linComb hU]
  conv_rhs => rw [e', mixedDeriv_linComb hU]
  rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply]
  have e3 : (![![t]] : Fin 1 → Fin 1 → ℝ) 0 = t • (![![1]] : Fin 1 → Fin 1 → ℝ) 0 := by
    funext i
    fin_cases i
    simp
  rw [e3, map_smul]
  simp
theorem mixedDeriv_two_linComb {U : E} (hU : AnalyticAlongDirections J U) (A : Fin 3 → E) (x y : Fin 3 → ℝ) :
    mixedDeriv J U ![∑ l, x l • A l, ∑ l, y l • A l] = iteratedFDeriv ℝ 2 (alongDirections J U A) 0 ![x, y] := by
  have e : (![∑ l, x l • A l, ∑ l, y l • A l] : Fin 2 → E) =
      fun i => ∑ l, (![x, y] : Fin 2 → Fin 3 → ℝ) i l • A l := by
    funext i
    fin_cases i <;> simp
  rw [e, mixedDeriv_linComb hU]
section Bilinear
variable {U : E}
theorem mixedDeriv_two_add_left (hU : AnalyticAlongDirections J U) (A A' B : E) :
    mixedDeriv J U ![A + A', B] = mixedDeriv J U ![A, B] + mixedDeriv J U ![A', B] := by
  set D : Fin 3 → E := ![A, A', B] with hD
  have e1 : A + A' = ∑ l, (![1, 1, 0] : Fin 3 → ℝ) l • D l := by simp [hD, Fin.sum_univ_three]
  have e2 : A = ∑ l, (![1, 0, 0] : Fin 3 → ℝ) l • D l := by simp [hD, Fin.sum_univ_three]
  have e3 : A' = ∑ l, (![0, 1, 0] : Fin 3 → ℝ) l • D l := by simp [hD, Fin.sum_univ_three]
  have e4 : B = ∑ l, (![0, 0, 1] : Fin 3 → ℝ) l • D l := by simp [hD, Fin.sum_univ_three]
  conv_lhs => rw [e1, e4, mixedDeriv_two_linComb hU]
  conv_rhs => rw [e2, e3, e4, mixedDeriv_two_linComb hU, mixedDeriv_two_linComb hU]
  set M := iteratedFDeriv ℝ 2 (alongDirections J U D) 0
  have h := M.map_update_add ![(![0, 0, 0] : Fin 3 → ℝ), ![0, 0, 1]] 0 ![1, 0, 0] ![0, 1, 0]
  have u : ∀ x : Fin 3 → ℝ, Function.update ![(![0, 0, 0] : Fin 3 → ℝ), ![0, 0, 1]] 0 x = ![x, ![0, 0, 1]] := by
    intro x
    funext i
    fin_cases i <;> simp
  rw [u, u, u] at h
  rw [← h]
  congr 2
  funext l
  fin_cases l <;> simp
theorem mixedDeriv_two_smul_left (hU : AnalyticAlongDirections J U) (t : ℝ) (A B : E) :
    mixedDeriv J U ![t • A, B] = t * mixedDeriv J U ![A, B] := by
  set D : Fin 3 → E := ![A, B, 0] with hD
  have e1 : t • A = ∑ l, (![t, 0, 0] : Fin 3 → ℝ) l • D l := by simp [hD, Fin.sum_univ_three]
  have e2 : A = ∑ l, (![1, 0, 0] : Fin 3 → ℝ) l • D l := by simp [hD, Fin.sum_univ_three]
  have e4 : B = ∑ l, (![0, 1, 0] : Fin 3 → ℝ) l • D l := by simp [hD, Fin.sum_univ_three]
  conv_lhs => rw [e1, e4, mixedDeriv_two_linComb hU]
  conv_rhs => rw [e2, e4, mixedDeriv_two_linComb hU]
  set M := iteratedFDeriv ℝ 2 (alongDirections J U D) 0
  have h := M.map_update_smul ![(![0, 0, 0] : Fin 3 → ℝ), ![0, 1, 0]] 0 t ![1, 0, 0]
  have u : ∀ x : Fin 3 → ℝ, Function.update ![(![0, 0, 0] : Fin 3 → ℝ), ![0, 1, 0]] 0 x = ![x, ![0, 1, 0]] := by
    intro x
    funext i
    fin_cases i <;> simp
  rw [u, u] at h
  rw [smul_eq_mul] at h
  rw [← h]
  congr 2
  funext l
  fin_cases l <;> simp
theorem mixedDeriv_two_add_right (hU : AnalyticAlongDirections J U) (A B B' : E) :
    mixedDeriv J U ![A, B + B'] = mixedDeriv J U ![A, B] + mixedDeriv J U ![A, B'] := by
  set D : Fin 3 → E := ![A, B, B'] with hD
  have e1 : B + B' = ∑ l, (![0, 1, 1] : Fin 3 → ℝ) l • D l := by simp [hD, Fin.sum_univ_three]
  have e2 : B = ∑ l, (![0, 1, 0] : Fin 3 → ℝ) l • D l := by simp [hD, Fin.sum_univ_three]
  have e3 : B' = ∑ l, (![0, 0, 1] : Fin 3 → ℝ) l • D l := by simp [hD, Fin.sum_univ_three]
  have e4 : A = ∑ l, (![1, 0, 0] : Fin 3 → ℝ) l • D l := by simp [hD, Fin.sum_univ_three]
  conv_lhs => rw [e1, e4, mixedDeriv_two_linComb hU]
  conv_rhs => rw [e2, e3, e4, mixedDeriv_two_linComb hU, mixedDeriv_two_linComb hU]
  set M := iteratedFDeriv ℝ 2 (alongDirections J U D) 0
  have h := M.map_update_add ![(![1, 0, 0] : Fin 3 → ℝ), ![0, 0, 0]] 1 ![0, 1, 0] ![0, 0, 1]
  have u : ∀ x : Fin 3 → ℝ, Function.update ![(![1, 0, 0] : Fin 3 → ℝ), ![0, 0, 0]] 1 x = ![![1, 0, 0], x] := by
    intro x
    funext i
    fin_cases i <;> simp
  rw [u, u, u] at h
  rw [← h]
  congr 2
  funext l
  fin_cases l <;> simp
theorem mixedDeriv_two_smul_right (hU : AnalyticAlongDirections J U) (t : ℝ) (A B : E) :
    mixedDeriv J U ![A, t • B] = t * mixedDeriv J U ![A, B] := by
  set D : Fin 3 → E := ![A, B, 0] with hD
  have e1 : t • B = ∑ l, (![0, t, 0] : Fin 3 → ℝ) l • D l := by simp [hD, Fin.sum_univ_three]
  have e2 : B = ∑ l, (![0, 1, 0] : Fin 3 → ℝ) l • D l := by simp [hD, Fin.sum_univ_three]
  have e4 : A = ∑ l, (![1, 0, 0] : Fin 3 → ℝ) l • D l := by simp [hD, Fin.sum_univ_three]
  conv_lhs => rw [e1, e4, mixedDeriv_two_linComb hU]
  conv_rhs => rw [e2, e4, mixedDeriv_two_linComb hU]
  set M := iteratedFDeriv ℝ 2 (alongDirections J U D) 0
  have h := M.map_update_smul ![(![1, 0, 0] : Fin 3 → ℝ), ![0, 0, 0]] 1 t ![0, 1, 0]
  have u : ∀ x : Fin 3 → ℝ, Function.update ![(![1, 0, 0] : Fin 3 → ℝ), ![0, 0, 0]] 1 x = ![![1, 0, 0], x] := by
    intro x
    funext i
    fin_cases i <;> simp
  rw [u, u] at h
  rw [smul_eq_mul] at h
  rw [← h]
  congr 2
  funext l
  fin_cases l <;> simp
end Bilinear
theorem deriv_deriv_along {U : E} (A : E) (hU : AnalyticAlongDirections J U)
    (hnear : ∀ᶠ τ : ℝ in 𝓝 0, AnalyticAlongDirections J (U + τ • A)) :
    deriv (deriv fun τ : ℝ => J (U + τ • A)) 0 = mixedDeriv J U ![A, A] := by
  have h1 : (deriv fun τ : ℝ => J (U + τ • A)) =ᶠ[𝓝 0] fun τ => mixedDeriv J (U + τ • A) ![A] := by
    filter_upwards [hnear] with τ hτ
    have h2 := hasDerivAt_along hτ A
    have h3 : HasDerivAt (fun q : ℝ => J (U + τ • A + (q - τ) • A)) (mixedDeriv J (U + τ • A) ![A]) τ := by
      have h5 : HasDerivAt (fun q : ℝ => J (U + τ • A + q • A)) (mixedDeriv J (U + τ • A) ![A]) (τ - τ) := by
        simpa using h2
      exact h5.comp_sub_const τ τ
    have e : (fun q : ℝ => J (U + τ • A + (q - τ) • A)) = fun q => J (U + q • A) := by
      funext q
      congr 1
      rw [sub_smul]
      abel
    rw [e] at h3
    exact h3.deriv
  rw [h1.deriv_eq]
  have h2 := (hasDerivAt_mixedDeriv hU A ![A]).deriv
  rw [h2]
  rfl
theorem deriv_deriv_along_two {W : E} (X A : E) (hW : AnalyticAlongDirections J W)
    (hnear : ∀ᶠ τ : ℝ in 𝓝 0, AnalyticAlongDirections J (W + τ • X)) :
    deriv (fun τ : ℝ => deriv (fun σ : ℝ => J ((W + τ • X) + σ • A)) 0) 0 = mixedDeriv J W ![X, A] := by
  have h1 : (fun τ : ℝ => deriv (fun σ : ℝ => J ((W + τ • X) + σ • A)) 0) =ᶠ[𝓝 0]
      fun τ => mixedDeriv J (W + τ • X) ![A] := by
    filter_upwards [hnear] with τ hτ
    exact deriv_along hτ A
  rw [h1.deriv_eq]
  have h2 := (hasDerivAt_mixedDeriv hW X ![A]).deriv
  rw [h2]
  rfl
end LineDerivatives
end YangMills.Construction
end
