import YangMills.Construction.ColdStepAtMirrorFrames.DifferenceOfTwoJets
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderNearOne
import YangMills.Construction.ColdStepAtMirrorFrames.ThreeDerivativesOfAComposite
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace SecondOrderNearCriticalAux
variable {F : BlockFrame}
theorem sum_const_mul_prod_norm {j k : ℕ} {B : Finset (F.Site j × Fin 4)} (d : ℝ)
    (Z : Fin k → ↥B → imaginaryQuaternions) :
    ∑ c : Fin k → ↥B, d * ∏ l, ‖Z l (c l)‖ = d * ∏ l, ∑ b, ‖Z l b‖ := by
  rw [← Finset.mul_sum, Finset.prod_univ_sum, Fintype.piFinset_univ]
theorem iteratedFDeriv_apply_component {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {j : ℕ}
    {B : Finset (F.Site j × Fin 4)} (A : P → ↥B → imaginaryQuaternions) (hA : ContDiffAt ℝ 3 A 0)
    (i : ℕ) (hi : i ≤ 3) (m : Fin i → P) (b : ↥B) :
    iteratedFDeriv ℝ i A 0 m b = iteratedFDeriv ℝ i (fun τ => A τ b) 0 m := by
  have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥B => imaginaryQuaternions) b).iteratedFDeriv_comp_left hA
    (i := i) (by exact_mod_cast hi)
  have e : (fun τ => A τ b) =
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥B => imaginaryQuaternions) b) ∘ A := rfl
  rw [e, h]
  simp
theorem bilinear_sub_left {E G' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G']
    [NormedSpace ℝ G'] (T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) G') (a a' b : E) :
    T ![a, b] - T ![a', b] = T ![a - a', b] := by
  classical
  have key := T.toMultilinearMap.map_update_sub ![a, b] 0 a a'
  have e1 : Function.update ![a, b] 0 a = ![a, b] := by
    funext i; fin_cases i <;> simp
  have e2 : Function.update ![a, b] 0 a' = ![a', b] := by
    funext i; fin_cases i <;> simp
  have e3 : Function.update ![a, b] 0 (a - a') = ![a - a', b] := by
    funext i; fin_cases i <;> simp
  rw [e1, e2, e3] at key
  exact key.symm
theorem bilinear_sub_right {E G' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G']
    [NormedSpace ℝ G'] (T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) G') (a b b' : E) :
    T ![a, b] - T ![a, b'] = T ![a, b - b'] := by
  classical
  have key := T.toMultilinearMap.map_update_sub ![a, b] 1 b b'
  have e1 : Function.update ![a, b] 1 b = ![a, b] := by
    funext i; fin_cases i <;> simp
  have e2 : Function.update ![a, b] 1 b' = ![a, b'] := by
    funext i; fin_cases i <;> simp
  have e3 : Function.update ![a, b] 1 (b - b') = ![a, b - b'] := by
    funext i; fin_cases i <;> simp
  rw [e1, e2, e3] at key
  exact key.symm
end SecondOrderNearCriticalAux
open SecondOrderNearCriticalAux
theorem secondOrderNearCritical_holds (hjet : FormCompositionJet) (hdiff : JetDifferenceBound)
    (hcomp : ThirdOrderChainRule) : SecondOrderNearCritical := by
  intro F j B G G₀ W W₀ P _ _ Wf Wf₀ A A₀ d₀ Eg S Δ u v hG hG₀ hA hA0 hev hB hB0 hev₀ hd hEg hS b₁ b₂ z₁ e₂
    s₁ s₂ s₃ s₄ s₅ g₁ g₂
  obtain ⟨hcd, -, hbd⟩ := hjet ℝ F j B G W hG
  obtain ⟨hcd₀, -, hbd₀⟩ := hjet ℝ F j B G₀ W₀ hG₀
  have c1 : ContDiffAt ℝ 3 (formComposition B G W) (A 0) := by rw [hA0]; exact hcd
  have c2 : ContDiffAt ℝ 3 (formComposition B G₀ W₀) (A₀ 0) := by rw [hB0]; exact hcd₀
  obtain ⟨-, h1, h2, -⟩ := hcomp (formComposition B G W) A 0 c1 hA
  obtain ⟨-, k1, k2, -⟩ := hcomp (formComposition B G₀ W₀) A₀ 0 c2 hB
  have hEq : (fun τ => G (Wf τ)) =ᶠ[𝓝 0] formComposition B G W ∘ A := hev.mono fun τ h => by
    simp only [Function.comp_apply, formComposition]
    rw [h]
  have hEq₀ : (fun τ => G₀ (Wf₀ τ)) =ᶠ[𝓝 0] formComposition B G₀ W₀ ∘ A₀ := hev₀.mono fun τ h => by
    simp only [Function.comp_apply, formComposition]
    rw [h]
  have d : ∀ i, iteratedFDeriv ℝ i (fun τ => G (Wf τ)) 0 = iteratedFDeriv ℝ i (formComposition B G W ∘ A) 0 :=
    fun i => (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hEq i).self_of_nhds
  have d₂ : ∀ i, iteratedFDeriv ℝ i (fun τ => G₀ (Wf₀ τ)) 0 =
      iteratedFDeriv ℝ i (formComposition B G₀ W₀ ∘ A₀) 0 :=
    fun i => (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hEq₀ i).self_of_nhds
  rw [d 2, d₂ 2, d 1, h2 u v, k2 u v, h1 u, hA0, hB0]
  set ZU := iteratedFDeriv ℝ 1 A 0 ![u] with hZU
  set ZV := iteratedFDeriv ℝ 1 A 0 ![v] with hZV
  set YU := iteratedFDeriv ℝ 1 A₀ 0 ![u] with hYU
  set YV := iteratedFDeriv ℝ 1 A₀ 0 ![v] with hYV
  set ZW := iteratedFDeriv ℝ 2 A 0 ![u, v] with hZW
  set YW := iteratedFDeriv ℝ 2 A₀ 0 ![u, v] with hYW
  have nU : ∑ b, ‖ZU b‖ ≤ S := by
    refine le_trans (le_of_eq ?_) s₁
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hZU, iteratedFDeriv_apply_component A hA 1 (by norm_num)]
    rfl
  have nV : ∑ b, ‖ZV b‖ ≤ S := by
    refine le_trans (le_of_eq ?_) s₂
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hZV, iteratedFDeriv_apply_component A hA 1 (by norm_num)]
    rfl
  have mV : ∑ b, ‖YV b‖ ≤ S := by
    refine le_trans (le_of_eq ?_) s₃
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hYV, iteratedFDeriv_apply_component A₀ hB 1 (by norm_num)]
    rfl
  have nW : ∑ b, ‖ZW b‖ ≤ S := by
    refine le_trans (le_of_eq ?_) s₅
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hZW, iteratedFDeriv_apply_component A hA 2 (by norm_num)]
    rfl
  have gU : ∑ b, ‖(ZU - YU) b‖ ≤ Δ := by
    refine le_trans (le_of_eq ?_) g₁
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Pi.sub_apply, hZU, hYU, iteratedFDeriv_apply_component A hA 1 (by norm_num),
      iteratedFDeriv_apply_component A₀ hB 1 (by norm_num)]
  have gV : ∑ b, ‖(ZV - YV) b‖ ≤ Δ := by
    refine le_trans (le_of_eq ?_) g₂
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Pi.sub_apply, hZV, hYV, iteratedFDeriv_apply_component A hA 1 (by norm_num),
      iteratedFDeriv_apply_component A₀ hB 1 (by norm_num)]
  have D1 : ∀ Z : ↥B → imaginaryQuaternions,
      ‖iteratedFDeriv ℝ 1 (formComposition B G W) 0 ![Z] - iteratedFDeriv ℝ 1 (formComposition B G₀ W₀) 0 ![Z]‖ ≤
      d₀ * ∑ b, ‖Z b‖ := fun Z => by
    have key := hdiff ℝ F j B G G₀ W W₀ 1 (fun _ => d₀) hG hG₀ (by norm_num) (fun _ => hd)
      (fun c X hX => by simpa [Real.norm_eq_abs] using b₁ c X hX) ![Z]
    rw [sum_const_mul_prod_norm] at key
    simpa using key
  have D2 : ∀ Z Z' : ↥B → imaginaryQuaternions,
      ‖iteratedFDeriv ℝ 2 (formComposition B G W) 0 ![Z, Z'] -
        iteratedFDeriv ℝ 2 (formComposition B G₀ W₀) 0 ![Z, Z']‖ ≤
      d₀ * ((∑ b, ‖Z b‖) * ∑ b, ‖Z' b‖) := fun Z Z' => by
    have key := hdiff ℝ F j B G G₀ W W₀ 2 (fun _ => d₀) hG hG₀ (by norm_num) (fun _ => hd)
      (fun c X hX => by simpa [Real.norm_eq_abs] using b₂ c X hX) ![Z, Z']
    rw [sum_const_mul_prod_norm] at key
    simpa [Fin.prod_univ_two] using key
  have J1 : ∀ Z : ↥B → imaginaryQuaternions, iteratedFDeriv ℝ 1 (formComposition B G₀ W₀) 0 ![Z] = 0 := fun Z => by
    have key := hbd₀ 1 (fun _ => 0) (by norm_num) (fun _ => le_rfl)
      (fun c X hX => by simp [z₁ c X hX]) ![Z]
    simpa using key
  have J2 : ∀ Z Z' : ↥B → imaginaryQuaternions, |iteratedFDeriv ℝ 2 (formComposition B G₀ W₀) 0 ![Z, Z']| ≤
      Eg * ((∑ b, ‖Z b‖) * ∑ b, ‖Z' b‖) := fun Z Z' => by
    have key := hbd₀ 2 (fun _ => Eg) (by norm_num) (fun _ => hEg)
      (fun c X hX => by simpa [Real.norm_eq_abs] using e₂ c X hX) ![Z, Z']
    rw [sum_const_mul_prod_norm] at key
    simpa [Fin.prod_univ_two, Real.norm_eq_abs] using key
  have n0U : 0 ≤ ∑ b, ‖ZU b‖ := Finset.sum_nonneg fun b _ => norm_nonneg _
  have n0V : 0 ≤ ∑ b, ‖ZV b‖ := Finset.sum_nonneg fun b _ => norm_nonneg _
  have n0Y : 0 ≤ ∑ b, ‖YV b‖ := Finset.sum_nonneg fun b _ => norm_nonneg _
  have n0g : 0 ≤ ∑ b, ‖(ZU - YU) b‖ := Finset.sum_nonneg fun b _ => norm_nonneg _
  have n0h : 0 ≤ ∑ b, ‖(ZV - YV) b‖ := Finset.sum_nonneg fun b _ => norm_nonneg _
  have hΔ : 0 ≤ Δ := n0g.trans gU
  constructor
  · have split : iteratedFDeriv ℝ 2 (formComposition B G W) 0 ![ZU, ZV] +
          iteratedFDeriv ℝ 1 (formComposition B G W) 0 ![ZW] -
        (iteratedFDeriv ℝ 2 (formComposition B G₀ W₀) 0 ![YU, YV] +
          iteratedFDeriv ℝ 1 (formComposition B G₀ W₀) 0 ![YW]) =
        (iteratedFDeriv ℝ 2 (formComposition B G W) 0 ![ZU, ZV] -
          iteratedFDeriv ℝ 2 (formComposition B G₀ W₀) 0 ![ZU, ZV]) +
        iteratedFDeriv ℝ 2 (formComposition B G₀ W₀) 0 ![ZU - YU, ZV] +
        iteratedFDeriv ℝ 2 (formComposition B G₀ W₀) 0 ![YU, ZV - YV] +
        (iteratedFDeriv ℝ 1 (formComposition B G W) 0 ![ZW] -
          iteratedFDeriv ℝ 1 (formComposition B G₀ W₀) 0 ![ZW]) := by
      rw [← bilinear_sub_left, ← bilinear_sub_right, J1 YW, J1 ZW]
      ring
    rw [split]
    have t1 := D2 ZU ZV
    have t2 := J2 (ZU - YU) ZV
    have t3 := J2 YU (ZV - YV)
    have t4 := D1 ZW
    rw [Real.norm_eq_abs] at t1 t4
    have nYU : ∑ b, ‖YU b‖ ≤ S := by
      refine le_trans (le_of_eq ?_) s₄
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hYU, iteratedFDeriv_apply_component A₀ hB 1 (by norm_num)]
      rfl
    have n0YU : 0 ≤ ∑ b, ‖YU b‖ := Finset.sum_nonneg fun b _ => norm_nonneg _
    have a1 : d₀ * ((∑ b, ‖ZU b‖) * ∑ b, ‖ZV b‖) ≤ d₀ * S ^ 2 := by
      have key := mul_le_mul nU nV n0V hS
      exact mul_le_mul_of_nonneg_left (by nlinarith) hd
    have a2 : Eg * ((∑ b, ‖(ZU - YU) b‖) * ∑ b, ‖ZV b‖) ≤ Eg * S * Δ := by
      have key := mul_le_mul gU nV n0V hΔ
      calc _ ≤ Eg * (Δ * S) := mul_le_mul_of_nonneg_left key hEg
        _ = _ := by ring
    have a3 : Eg * ((∑ b, ‖YU b‖) * ∑ b, ‖(ZV - YV) b‖) ≤ Eg * S * Δ := by
      have key := mul_le_mul nYU gV n0h hS
      calc _ ≤ Eg * (S * Δ) := mul_le_mul_of_nonneg_left key hEg
        _ = _ := by ring
    have a4 : d₀ * ∑ b, ‖ZW b‖ ≤ d₀ * S := mul_le_mul_of_nonneg_left nW hd
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add_left (abs_add_le _ _) _).trans ?_
    refine (add_le_add_left (add_le_add_left (abs_add_le _ _) _) _).trans ?_
    have q1 := t1.trans a1
    have q2 := t2.trans a2
    have q3 := t3.trans a3
    have q4 := t4.trans a4
    linarith
  · have t := D1 ZU
    rw [J1 ZU, sub_zero, Real.norm_eq_abs] at t
    exact t.trans (mul_le_mul_of_nonneg_left nU hd)
end YangMills.Construction.ColdStepAtMirrorFrames
end
