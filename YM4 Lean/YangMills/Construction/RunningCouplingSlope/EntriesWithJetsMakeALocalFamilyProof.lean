import YangMills.Construction.RunningCouplingSlope.EntriesWithJetsMakeALocalFamily
import YangMills.Construction.RunningCouplingSlope.KernelsNearTheCellsAreBoundedProof
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower
section SecondOrderJets
variable {g h : ℝ → ℝ → ℂ}
private theorem differentiable_of_contDiff_two (hg : ContDiff ℝ 2 (fun w : ℝ × ℝ => g w.1 w.2)) :
    Differentiable ℝ (fun w : ℝ × ℝ => g w.1 w.2) :=
  hg.differentiable (by norm_num)
private theorem differentiableAt_snd (hg : ContDiff ℝ 2 (fun w : ℝ × ℝ => g w.1 w.2)) (s : ℝ) :
    DifferentiableAt ℝ (fun t => g s t) 0 := by
  have h1 : Differentiable ℝ (fun t : ℝ => ((s, t) : ℝ × ℝ)) := by fun_prop
  exact ((differentiable_of_contDiff_two hg).comp h1) 0
private theorem differentiableAt_fst (hg : ContDiff ℝ 2 (fun w : ℝ × ℝ => g w.1 w.2)) :
    DifferentiableAt ℝ (fun s => g s 0) 0 := by
  have h1 : Differentiable ℝ (fun s : ℝ => ((s, 0) : ℝ × ℝ)) := by fun_prop
  exact ((differentiable_of_contDiff_two hg).comp h1) 0
private theorem differentiableAt_snd_zero (hg : ContDiff ℝ 2 (fun w : ℝ × ℝ => g w.1 w.2)) :
    DifferentiableAt ℝ (fun t => g 0 t) 0 := differentiableAt_snd hg 0
private theorem deriv_snd_eq_fderiv (hg : ContDiff ℝ 2 (fun w : ℝ × ℝ => g w.1 w.2)) (s : ℝ) :
    deriv (fun t => g s t) 0 = fderiv ℝ (fun w : ℝ × ℝ => g w.1 w.2) (s, 0) (0, 1) := by
  have h0 : HasFDerivAt (fun w : ℝ × ℝ => g w.1 w.2)
      (fderiv ℝ (fun w : ℝ × ℝ => g w.1 w.2) (s, 0)) (s, 0) :=
    (differentiable_of_contDiff_two hg (s, 0)).hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => ((s, t) : ℝ × ℝ)) (0, 1) 0 :=
    (hasDerivAt_const (0 : ℝ) s).prodMk (hasDerivAt_id (0 : ℝ))
  exact (h0.comp_hasDerivAt (0 : ℝ) h1).deriv
private theorem differentiableAt_mixed (hg : ContDiff ℝ 2 (fun w : ℝ × ℝ => g w.1 w.2)) :
    DifferentiableAt ℝ (fun s => deriv (fun t => g s t) 0) 0 := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ (fun w : ℝ × ℝ => g w.1 w.2)) :=
    hg.fderiv_right (by norm_num)
  have h2 : ContDiff ℝ 1 (fun s : ℝ => ((s, 0) : ℝ × ℝ)) := by fun_prop
  have h3 : ContDiff ℝ 1 (fun s : ℝ => fderiv ℝ (fun w : ℝ × ℝ => g w.1 w.2) (s, 0) (0, 1)) :=
    (h1.comp h2).clm_apply contDiff_const
  have h4 : (fun s => deriv (fun t => g s t) 0) =
      fun s => fderiv ℝ (fun w : ℝ × ℝ => g w.1 w.2) (s, 0) (0, 1) :=
    funext (deriv_snd_eq_fderiv hg)
  rw [h4]
  exact (h3.differentiable (by norm_num)) 0
private theorem hasSecondOrderJet_const (w : ℂ) : HasSecondOrderJet (fun _ _ => w) w 0 0 0 where
  contDiff := contDiff_const
  apply_zero := rfl
  deriv_fst := by simp
  deriv_snd := by simp
  deriv_mixed := by simp
private theorem hasSecondOrderJet_add {v a b c v' a' b' c' : ℂ} (hg : HasSecondOrderJet g v a b c)
    (hh : HasSecondOrderJet h v' a' b' c') :
    HasSecondOrderJet (fun s t => g s t + h s t) (v + v') (a + a') (b + b') (c + c') where
  contDiff := hg.contDiff.add hh.contDiff
  apply_zero := by simp [hg.apply_zero, hh.apply_zero]
  deriv_fst := by
    have := ((differentiableAt_fst hg.contDiff).hasDerivAt.add
      (differentiableAt_fst hh.contDiff).hasDerivAt).deriv
    rw [hg.deriv_fst, hh.deriv_fst] at this
    exact this
  deriv_snd := by
    have := ((differentiableAt_snd_zero hg.contDiff).hasDerivAt.add
      (differentiableAt_snd_zero hh.contDiff).hasDerivAt).deriv
    rw [hg.deriv_snd, hh.deriv_snd] at this
    exact this
  deriv_mixed := by
    have e : (fun s => deriv (fun t => g s t + h s t) 0) =
        fun s => deriv (fun t => g s t) 0 + deriv (fun t => h s t) 0 := by
      funext s
      exact ((differentiableAt_snd hg.contDiff s).hasDerivAt.add
        (differentiableAt_snd hh.contDiff s).hasDerivAt).deriv
    rw [e]
    have := ((differentiableAt_mixed hg.contDiff).hasDerivAt.add
      (differentiableAt_mixed hh.contDiff).hasDerivAt).deriv
    rw [hg.deriv_mixed, hh.deriv_mixed] at this
    exact this
private theorem hasSecondOrderJet_mul {v a b c v' a' b' c' : ℂ} (hg : HasSecondOrderJet g v a b c)
    (hh : HasSecondOrderJet h v' a' b' c') :
    HasSecondOrderJet (fun s t => g s t * h s t) (v * v') (a * v' + v * a') (b * v' + v * b')
      (c * v' + a * b' + b * a' + v * c') where
  contDiff := hg.contDiff.mul hh.contDiff
  apply_zero := by simp [hg.apply_zero, hh.apply_zero]
  deriv_fst := by
    have := ((differentiableAt_fst hg.contDiff).hasDerivAt.mul
      (differentiableAt_fst hh.contDiff).hasDerivAt).deriv
    rw [hg.deriv_fst, hh.deriv_fst, hg.apply_zero, hh.apply_zero] at this
    exact this
  deriv_snd := by
    have := ((differentiableAt_snd_zero hg.contDiff).hasDerivAt.mul
      (differentiableAt_snd_zero hh.contDiff).hasDerivAt).deriv
    rw [hg.deriv_snd, hh.deriv_snd, hg.apply_zero, hh.apply_zero] at this
    exact this
  deriv_mixed := by
    have e : (fun s => deriv (fun t => g s t * h s t) 0) =
        fun s => deriv (fun t => g s t) 0 * h s 0 + g s 0 * deriv (fun t => h s t) 0 := by
      funext s
      exact ((differentiableAt_snd hg.contDiff s).hasDerivAt.mul
        (differentiableAt_snd hh.contDiff s).hasDerivAt).deriv
    rw [e]
    have h1 := (differentiableAt_mixed hg.contDiff).hasDerivAt.mul
      (differentiableAt_fst hh.contDiff).hasDerivAt
    have h2 := (differentiableAt_fst hg.contDiff).hasDerivAt.mul
      (differentiableAt_mixed hh.contDiff).hasDerivAt
    have := (h1.add h2).deriv
    rw [hg.deriv_mixed, hh.deriv_mixed, hg.deriv_fst, hh.deriv_fst, hg.deriv_snd, hh.deriv_snd,
      hg.apply_zero, hh.apply_zero] at this
    refine this.trans ?_
    ring
private theorem hasSecondOrderJet_sum {κ : Type} (S : Finset κ) {G : κ → ℝ → ℝ → ℂ}
    {v a b c : κ → ℂ} (hG : ∀ i ∈ S, HasSecondOrderJet (G i) (v i) (a i) (b i) (c i)) :
    HasSecondOrderJet (fun s t => ∑ i ∈ S, G i s t) (∑ i ∈ S, v i) (∑ i ∈ S, a i)
      (∑ i ∈ S, b i) (∑ i ∈ S, c i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hasSecondOrderJet_const 0
  | insert i S hi ih =>
    have h1 := hasSecondOrderJet_add (hG i (Finset.mem_insert_self i S))
      (ih fun j hj => hG j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using h1
private theorem hasSecondOrderJet_comp_linear {G : ℝ → ℂ} (α β : ℝ) (hG : ContDiff ℝ 2 G) :
    HasSecondOrderJet (fun s t => G (s * α + t * β)) (G 0) (α * deriv G 0) (β * deriv G 0)
      (α * β * deriv (deriv G) 0) := by
  have hd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have h1 : ContDiff ℝ 1 (deriv G) := by
    have h2 : ContDiff ℝ (1 + 1) G := by simpa [one_add_one_eq_two] using hG
    exact (contDiff_succ_iff_deriv.1 h2).2.2
  have hd' : Differentiable ℝ (deriv G) := h1.differentiable (by norm_num)
  have lin_fst : ∀ (t₀ s : ℝ), HasDerivAt (fun s : ℝ => s * α + t₀ * β) α s := fun t₀ s => by
    simpa using ((hasDerivAt_id s).mul_const α).add_const (t₀ * β)
  have lin_snd : ∀ (s₀ t : ℝ), HasDerivAt (fun t : ℝ => s₀ * α + t * β) β t := fun s₀ t => by
    simpa using ((hasDerivAt_id t).mul_const β).const_add (s₀ * α)
  refine ⟨?_, by simp, ?_, ?_, ?_⟩
  · have : ContDiff ℝ 2 (fun w : ℝ × ℝ => w.1 * α + w.2 * β) := by fun_prop
    exact hG.comp this
  · have h2 := HasDerivAt.scomp (0 : ℝ) (g₁ := G) (h := fun s : ℝ => s * α + 0 * β)
      (hd _).hasDerivAt (lin_fst 0 0)
    have := h2.deriv
    simpa [Function.comp_def, Complex.real_smul] using this
  · have h2 := HasDerivAt.scomp (0 : ℝ) (g₁ := G) (h := fun t : ℝ => 0 * α + t * β)
      (hd _).hasDerivAt (lin_snd 0 0)
    have := h2.deriv
    simpa [Function.comp_def, Complex.real_smul] using this
  · have e : (fun s => deriv (fun t => G (s * α + t * β)) 0) =
        fun s => (β : ℂ) * deriv G (s * α) := by
      funext s
      have h2 := HasDerivAt.scomp (0 : ℝ) (g₁ := G) (h := fun t : ℝ => s * α + t * β)
        (hd _).hasDerivAt (lin_snd s 0)
      have := h2.deriv
      simpa [Function.comp_def, Complex.real_smul] using this
    rw [e]
    have h3 := HasDerivAt.scomp (0 : ℝ) (g₁ := deriv G) (h := fun s : ℝ => s * α + 0 * β)
      (hd' _).hasDerivAt (lin_fst 0 0)
    have h4 : HasDerivAt (fun s : ℝ => deriv G (s * α)) ((α : ℂ) * deriv (deriv G) 0) 0 := by
      simpa [Function.comp_def, Complex.real_smul] using h3
    have := (h4.const_mul (β : ℂ)).deriv
    refine this.trans ?_
    ring
end SecondOrderJets
section CellBlocks
private theorem opNorm_le_sqrt_of_row_col_sums {ι ι' : Type} [Fintype ι] [Fintype ι']
    [DecidableEq ι]
    (A : Matrix ι' ι ℂ) (P Q : ℝ) (hP : ∀ p, ∑ q, ‖A p q‖ ≤ P) (hQ : ∀ q, ∑ p, ‖A p q‖ ≤ Q)
    (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q) : ‖A‖ ≤ Real.sqrt (P * Q) := by apply _root_.YangMills.SharedProofs.p56120 <;> assumption
variable {L n k : ℕ} {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι]
private theorem sum_le_card_mul_of_support {κ : Type} [Fintype κ] (f : κ → ℝ) (P : κ → Prop)
    (B : ℝ) (N : ℕ) (hB : 0 ≤ B) (hN : Nat.card {q // P q} ≤ N) (h0 : ∀ q, ¬ P q → f q = 0)
    (hf : ∀ q, f q ≤ B) : ∑ q, f q ≤ N * B := by
  classical
  have h1 : ∑ q, f q = ∑ q ∈ Finset.univ.filter P, f q := by
    refine (Finset.sum_filter_of_ne fun q _ hq => ?_).symm
    by_contra h
    exact hq (h0 q h)
  have h2 : (Finset.univ.filter P).card ≤ N := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hN
    exact hN
  calc ∑ q, f q = ∑ q ∈ Finset.univ.filter P, f q := h1
    _ ≤ ∑ _q ∈ Finset.univ.filter P, B := Finset.sum_le_sum fun q _ => hf q
    _ = (Finset.univ.filter P).card * B := by simp
    _ ≤ N * B := mul_le_mul_of_nonneg_right (by exact_mod_cast h2) hB
private theorem isLocalOnCells_of_sparsity
    (c : ι → PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k))
    (c' : ι' → PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k)) (θ K r : ℝ) (R C : ℕ)
    (S : ι' → ι → Prop) (hθ : 0 ≤ θ) (hK : 0 ≤ K) (hS : IsBoundedSparsityOnCells c c' S R C r)
    (A : Matrix ι' ι ℂ) (m : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k) → ℝ)
    (hm : ∀ y, 0 ≤ m y) (h0 : ∀ p q, ¬ S p q → A p q = 0)
    (hA : ∀ p q, ‖A p q‖ ≤ K * m (c' p)) :
    IsLocalOnCells c c' A (Real.sqrt ((R : ℝ) * C) * K * Real.exp (θ * r)) θ m := by
  classical
  intro y' y
  set B := blockBetween c c' A y' y with hB
  have hBent : ∀ p q, B p q = if c' p = y' ∧ c q = y then A p q else 0 := fun p q => by
    simp only [hB, blockBetween]
    congr
  have hb0 : 0 ≤ K * m y' := mul_nonneg hK (hm y')
  have hbound : ∀ p q, ‖B p q‖ ≤ K * m y' := by
    intro p q
    rw [hBent]
    split_ifs with h
    · rw [← h.1]
      exact hA p q
    · simpa using hb0
  have hzero : ∀ p q, ¬ S p q → B p q = 0 := by
    intro p q h
    rw [hBent]
    split_ifs
    · exact h0 p q h
    · rfl
  have hrow : ∀ p, ∑ q, ‖B p q‖ ≤ R * (K * m y') := fun p =>
    sum_le_card_mul_of_support _ (S p) _ _ hb0 (hS.row_card_le p)
      (fun q hq => by simp [hzero p q hq]) fun q => hbound p q
  have hcol : ∀ q, ∑ p, ‖B p q‖ ≤ C * (K * m y') := fun q =>
    sum_le_card_mul_of_support _ (fun p => S p q) _ _ hb0 (hS.col_card_le q)
      (fun p hp => by simp [hzero p q hp]) fun p => hbound p q
  have hnorm : ‖B‖ ≤ Real.sqrt ((R : ℝ) * C) * (K * m y') := by
    refine (opNorm_le_sqrt_of_row_col_sums B _ _ hrow hcol (by positivity)
      (by positivity)).trans (le_of_eq ?_)
    have e : (R : ℝ) * (K * m y') * (C * (K * m y')) = (R * C) * (K * m y') ^ 2 := by ring
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq hb0]
  by_cases hB0 : B = 0
  · rw [hB0, norm_zero]
    have := hm y'
    positivity
  · obtain ⟨p, q, hpq⟩ : ∃ p q, B p q ≠ 0 := by
      by_contra h
      push Not at h
      exact hB0 (Matrix.ext h)
    have hS' : S p q := by
      by_contra h
      exact hpq (hzero p q h)
    have hc : c' p = y' ∧ c q = y := by
      by_contra h
      exact hpq (by rw [hBent, if_neg h])
    have hd : cellDist y' y ≤ r := by
      have := hS.cellDist_le p q hS'
      rwa [hc.1, hc.2] at this
    have hone : 1 ≤ Real.exp (θ * r) * Real.exp (-(θ * cellDist y' y)) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      have := mul_le_mul_of_nonneg_left hd hθ
      linarith
    calc ‖B‖ ≤ Real.sqrt ((R : ℝ) * C) * (K * m y') := hnorm
      _ = Real.sqrt ((R : ℝ) * C) * K * m y' * 1 := by ring
      _ ≤ Real.sqrt ((R : ℝ) * C) * K * m y' *
          (Real.exp (θ * r) * Real.exp (-(θ * cellDist y' y))) :=
          mul_le_mul_of_nonneg_left hone (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hK) (hm y'))
      _ = _ := by ring
end CellBlocks
theorem localFamilyOfJetEntries_holds : LocalFamilyOfJetEntries := by
  refine ⟨⟨hasSecondOrderJet_const, hasSecondOrderJet_add, hasSecondOrderJet_mul,
    fun S _ _ _ _ _ h => hasSecondOrderJet_sum S h,
    fun α β h => hasSecondOrderJet_comp_linear α β h⟩, ?_⟩
  intro L n k ι ι' _ _ _ c c' T w θ K r R C S v a b d hθ hK hS hjet h0 hv ha hb hd
  have hw : ∀ (y₀ y : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k)),
      0 ≤ cellDecayWeight θ y₀ y := fun _ _ => (Real.exp_pos _).le
  refine ⟨fun p q => (hjet p q).contDiff.contDiffAt, ?_, ?_, ?_, ?_⟩
  · have e : T 0 0 = v := funext fun p => funext fun q => (hjet p q).apply_zero
    rw [e]
    exact isLocalOnCells_of_sparsity c c' θ K r R C S hθ hK hS v (fun _ => 1)
      (fun _ => zero_le_one) (fun p q h => (h0 p q h).1) (fun p q => by simpa using hv p q)
  · have e : derivFirst T = a := funext fun p => funext fun q => (hjet p q).deriv_fst
    rw [e]
    exact isLocalOnCells_of_sparsity c c' θ K r R C S hθ hK hS a _ (hw _)
      (fun p q h => (h0 p q h).2.1) ha
  · have e : derivSecond T = b := funext fun p => funext fun q => (hjet p q).deriv_snd
    rw [e]
    exact isLocalOnCells_of_sparsity c c' θ K r R C S hθ hK hS b _ (hw _)
      (fun p q h => (h0 p q h).2.2.1) hb
  · have e : derivMixed T = d := funext fun p => funext fun q => (hjet p q).deriv_mixed
    rw [e]
    exact isLocalOnCells_of_sparsity c c' θ K r R C S hθ hK hS d _
      (fun y => mul_nonneg (hw _ y) (hw _ y)) (fun p q h => (h0 p q h).2.2.2) hd
end YangMills.Construction.RunningCouplingSlope
end
