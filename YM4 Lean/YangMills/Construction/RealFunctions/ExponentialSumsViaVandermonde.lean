import YangMills.Construction.FreeKernel.SymbolDerivativeEstimates
import YangMills.Construction.RealFunctions.ExponentialSumsDetermined
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ExpSums
open Matrix in
theorem exists_isVandermondeInverse (F : Finset ℤ) : ∃ W, IsVandermondeInverse F W := by
  classical
  let e : F ≃ Fin F.card := F.equivFin
  let v : Fin F.card → ℂ := fun i => -4 * (((e.symm i : F) : ℤ) : ℂ)
  have hv : Function.Injective v := by
    intro i j hij
    have h1 : (((e.symm i : F) : ℤ) : ℂ) = (((e.symm j : F) : ℤ) : ℂ) :=
      mul_left_cancel₀ (by norm_num : (-4 : ℂ) ≠ 0) hij
    have h2 : ((e.symm i : F) : ℤ) = ((e.symm j : F) : ℤ) := by exact_mod_cast h1
    exact e.symm.injective (Subtype.ext h2)
  let M : Matrix (Fin F.card) (Fin F.card) ℂ := (Matrix.vandermonde v)ᵀ
  have hdet : IsUnit M.det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hv)
  have hP : vandermondeOfFreqs F = M.submatrix id e := by
    ext l h
    simp [vandermondeOfFreqs, M, v, Matrix.vandermonde_apply]
  refine ⟨(M⁻¹).submatrix e id, ?_, ?_⟩
  · rw [hP, Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv M hdet]
    simp
  · rw [hP, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      Matrix.nonsing_inv_mul M hdet]
    simp
theorem hasDerivAt_cexp_mul_ofReal (c : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ))) (c * Complex.exp (c * (s : ℂ))) s := by apply _root_.YangMills.Construction.LatticeKernel.SymbolEstimates.hasDerivAt_cexp_mul_ofReal <;> assumption
theorem hasDerivAt_sum_mul_cexp {ι : Type} (u : Finset ι) (a c : ι → ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ∑ i ∈ u, a i * Complex.exp (c i * (t : ℂ)))
      (∑ i ∈ u, a i * (c i * Complex.exp (c i * (s : ℂ)))) s :=
  HasDerivAt.fun_sum fun i _ => (hasDerivAt_cexp_mul_ofReal (c i) s).const_mul (a i)
theorem deriv_expSum (F : Finset ℤ) (b : F → ℂ) :
    deriv (expSum F b) =
      expSum F (fun h => b h * (-4 * ((h : ℤ) : ℂ))) := by
  funext s
  have h := hasDerivAt_sum_mul_cexp (Finset.univ : Finset F) b (fun h => -4 * ((h : ℤ) : ℂ)) s
  have h' : HasDerivAt (expSum F b) _ s := h
  rw [h'.deriv]
  unfold expSum
  exact Finset.sum_congr rfl fun i _ => by ring
theorem iteratedDeriv_expSum (F : Finset ℤ) (b : F → ℂ) (n : ℕ) :
    iteratedDeriv n (expSum F b) =
      expSum F (fun h => b h * (-4 * ((h : ℤ) : ℂ)) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, deriv_expSum]
    congr 1
    funext h
    ring
theorem iteratedDeriv_expSum_zero (F : Finset ℤ) (b : F → ℂ) (n : Fin F.card) :
    iteratedDeriv (n : ℕ) (expSum F b) 0 = (vandermondeOfFreqs F).mulVec b n := by
  rw [iteratedDeriv_expSum]
  simp only [expSum, Matrix.mulVec, dotProduct, vandermondeOfFreqs, Matrix.of_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp [mul_comm]
theorem coeff_eq_sum_vandermondeInverse (F : Finset ℤ) (b : F → ℂ) (h : F) :
    b h = ∑ l : Fin F.card, vandermondeInverse F h l *
      iteratedDeriv (l : ℕ) (expSum F b) 0 := by
  have hW : IsVandermondeInverse F (vandermondeInverse F) :=
    Classical.epsilon_spec (exists_isVandermondeInverse F)
  have key : (vandermondeInverse F).mulVec ((vandermondeOfFreqs F).mulVec b) = b := by
    rw [Matrix.mulVec_mulVec, hW.2, Matrix.one_mulVec]
  calc b h = (vandermondeInverse F).mulVec ((vandermondeOfFreqs F).mulVec b) h := by rw [key]
    _ = _ := by
      simp only [Matrix.mulVec.eq_1 (vandermondeInverse F), dotProduct]
      exact Finset.sum_congr rfl fun l _ => by
        rw [iteratedDeriv_expSum_zero]
theorem eq_mul_cexp_of_deriv_add_mul_eq_zero (c : ℂ) (u : ℝ → ℂ) (hu : Differentiable ℝ u)
    (h : ∀ s, deriv u s + c * u s = 0) (s : ℝ) :
    u s = u 0 * Complex.exp (-c * (s : ℂ)) := by
  have hv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => u t * Complex.exp (c * (t : ℂ))) 0 t := by
    intro t
    have h1 := (hu t).hasDerivAt.mul (hasDerivAt_cexp_mul_ofReal c t)
    have h2 : deriv u t * Complex.exp (c * (t : ℂ)) + u t * (c * Complex.exp (c * (t : ℂ))) = 0 := by
      have : deriv u t * Complex.exp (c * (t : ℂ)) + u t * (c * Complex.exp (c * (t : ℂ))) =
          (deriv u t + c * u t) * Complex.exp (c * (t : ℂ)) := by ring
      rw [this, h t, zero_mul]
    rw [h2] at h1
    exact h1
  have hconst := is_const_of_deriv_eq_zero (𝕜 := ℝ)
    (fun t => (hv t).differentiableAt) (fun t => (hv t).deriv) s 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at hconst
  rw [← hconst, mul_assoc, ← Complex.exp_add]
  simp
theorem exists_sum_cexp_of_derivAddSMul_eq (t : Finset ℤ) (h : ℤ) (hh : h ∉ t) (f : ℝ → ℂ)
    (hf : Differentiable ℝ f) (b : ℤ → ℂ)
    (hb : ∀ s : ℝ, derivAddSMul (4 * (h : ℂ)) f s =
      ∑ k ∈ t, b k * Complex.exp (-4 * (k : ℂ) * (s : ℂ))) :
    ∃ b' : ℤ → ℂ, ∀ s : ℝ,
      f s = ∑ k ∈ insert h t, b' k * Complex.exp (-4 * (k : ℂ) * (s : ℂ)) := by
  classical
  let a : ℤ → ℂ := fun k => b k / (4 * (h : ℂ) - 4 * (k : ℂ))
  let P : ℝ → ℂ := fun s => ∑ k ∈ t, a k * Complex.exp (-4 * (k : ℂ) * (s : ℂ))
  have hP : ∀ s : ℝ, HasDerivAt P
      (∑ k ∈ t, a k * (-4 * (k : ℂ) * Complex.exp (-4 * (k : ℂ) * (s : ℂ)))) s :=
    fun s => hasDerivAt_sum_mul_cexp t a (fun k => -4 * (k : ℂ)) s
  let u : ℝ → ℂ := fun s => f s - P s
  have hud : ∀ s, HasDerivAt u
      (deriv f s - ∑ k ∈ t, a k * (-4 * (k : ℂ) * Complex.exp (-4 * (k : ℂ) * (s : ℂ)))) s :=
    fun s => (hf s).hasDerivAt.sub (hP s)
  have hu : Differentiable ℝ u := fun s => (hud s).differentiableAt
  have hode : ∀ s, deriv u s + (4 * (h : ℂ)) * u s = 0 := by
    intro s
    rw [(hud s).deriv]
    have h1 := hb s
    simp only [derivAddSMul] at h1
    have h2 : ∑ k ∈ t, a k * (-4 * (k : ℂ) * Complex.exp (-4 * (k : ℂ) * (s : ℂ)))
        + 4 * (h : ℂ) * P s = ∑ k ∈ t, b k * Complex.exp (-4 * (k : ℂ) * (s : ℂ)) := by
      simp only [P]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hne : (4 * (h : ℂ) - 4 * (k : ℂ)) ≠ 0 := by
        intro h0
        have h3 : (h : ℂ) = (k : ℂ) := by linear_combination h0 / 4
        have h4 : h = k := by exact_mod_cast h3
        exact hh (h4 ▸ hk)
      have h8 : a k * (4 * (h : ℂ) - 4 * (k : ℂ)) = b k := div_mul_cancel₀ _ hne
      rw [← h8]
      ring
    simp only [u]
    linear_combination h1 - h2
  refine ⟨fun k => if k = h then u 0 else a k, fun s => ?_⟩
  rw [Finset.sum_insert hh]
  have h5 := eq_mul_cexp_of_deriv_add_mul_eq_zero (4 * (h : ℂ)) u hu hode s
  have h6 : f s = u s + P s := by simp [u]
  rw [h6, h5]
  have h7 : (-(4 * (h : ℂ)) * (s : ℂ)) = -4 * (h : ℂ) * (s : ℂ) := by ring
  rw [h7]
  beta_reduce
  rw [if_pos rfl]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkh : k ≠ h := fun e => hh (e ▸ hk)
  rw [if_neg hkh]
theorem exists_sum_cexp_of_foldr_derivAddSMul_eq_zero (L : List ℤ) (hL : L.Nodup) :
    ∀ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f →
      (∀ s : ℝ, L.foldr (fun (h : ℤ) g => derivAddSMul (4 * (h : ℂ)) g) f s = 0) →
      ∃ b : ℤ → ℂ, ∀ s : ℝ,
        f s = ∑ k ∈ L.toFinset, b k * Complex.exp (-4 * (k : ℂ) * (s : ℂ)) := by
  classical
  induction L using List.reverseRecOn with
  | nil =>
    intro f _ hz
    exact ⟨0, fun s => by simpa using hz s⟩
  | append_singleton t h ih =>
    intro f hf hz
    have hnd : t.Nodup := (List.nodup_append.mp hL).1
    have hnot : h ∉ t := by
      intro hmem
      have := List.nodup_append.mp hL
      exact this.2.2 h hmem h (by simp) rfl
    rw [List.foldr_append] at hz
    simp only [List.foldr_cons, List.foldr_nil] at hz
    obtain ⟨hd, hf'⟩ := contDiff_infty_iff_deriv.mp hf
    have hg : ContDiff ℝ (⊤ : ℕ∞) (derivAddSMul (4 * (h : ℂ)) f) :=
      hf'.add (contDiff_const.mul hf)
    obtain ⟨b, hb⟩ := ih hnd _ hg hz
    have hnot' : h ∉ t.toFinset := by simpa using hnot
    obtain ⟨b', hb'⟩ := exists_sum_cexp_of_derivAddSMul_eq t.toFinset h hnot' f hd b hb
    refine ⟨b', fun s => ?_⟩
    rw [hb' s]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext x
    simp
theorem expSumsDetermined_holds : ExpSumsDetermined := by
  intro F _
  have hW : IsVandermondeInverse F (vandermondeInverse F) :=
    Classical.epsilon_spec (exists_isVandermondeInverse F)
  refine ⟨hW, ?_, ?_, ?_⟩
  · intro b f hf h
    have : f = expSum F b := funext hf
    rw [this]
    exact coeff_eq_sum_vandermondeInverse F b h
  · intro b b' hbb h
    have : expSum F b = expSum F b' := funext hbb
    rw [coeff_eq_sum_vandermondeInverse F b h, coeff_eq_sum_vandermondeInverse F b' h, this]
  · intro f hf hz
    obtain ⟨b, hb⟩ := exists_sum_cexp_of_foldr_derivAddSMul_eq_zero (F.sort (· ≤ ·))
      (F.sort_nodup (· ≤ ·)) f hf hz
    refine ⟨fun h => b h, fun s => ?_⟩
    rw [hb s, Finset.sort_toFinset]
    exact (Finset.sum_coe_sort F (fun k => b k * Complex.exp (-4 * (k : ℂ) * (s : ℂ)))).symm
end YangMills.Construction.ExpSums
end
