import YangMills.Construction.RunningCouplingSlope.DerivativeOfThePlainAverageAtOneProof
import YangMills.Construction.RunningCouplingSlope.PlainAverageAlongComplexCurvesProof
import YangMills.Construction.RunningCouplingSlope.PlainDifferentialAtOneOnComplexForms
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.HolDifferentialAtOneProof
open Tower Matrices
section Orders
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
abbrev permList (π : Equiv.Perm (Fin 4)) : List (Fin 4) := (List.finRange 4).map π
abbrev subsetOrderList {S : Finset (Fin 4)} (σ : Fin S.card ≃ S) : List (Fin 4) :=
  (List.finRange S.card).map fun i => ((σ i : S) : Fin 4)
theorem card_smul_sum_permList (S : Finset (Fin 4)) (F : List (Fin 4) → E)
    (hF : ∀ l, F l = F (l.filter (· ∈ S))) :
    (Fintype.card (Fin S.card ≃ S)) • ∑ π : Equiv.Perm (Fin 4), F (permList π) =
      (24 : ℕ) • ∑ σ : Fin S.card ≃ S, F (subsetOrderList σ) := by apply _root_.YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof.card_smul_sum_permList <;> assumption
end Orders
section Paths
variable {L m : ℕ} {j : ℤ}
theorem stepsThroughAxes_filter (d : Fin 4 → ℤ) (S : Finset (Fin 4)) (hS : ∀ μ, μ ∉ S → d μ = 0)
    (x : PeriodicLattice.Site L m j) (l : List (Fin 4)) :
    PeriodicLattice.stepsThroughAxes d x l = PeriodicLattice.stepsThroughAxes d x (l.filter (· ∈ S)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof.stepsThroughAxes_filter <;> assumption
theorem sum_perm_bondFormSumAlong_eq (A : PeriodicLattice.Bond L m j → ComplexMatrix2) {i : ℤ}
    (y : PeriodicLattice.Site L m i) (x : PeriodicLattice.Site L m j) :
    ∑ π : Equiv.Perm (Fin 4), PeriodicLattice.bondFormSumAlong A
        (PeriodicLattice.stepsThroughAxes (PeriodicLattice.blockOffset y x) (y.toSublattice j)
          (permList π)) =
      (24 : ℂ) • PeriodicLattice.contourFormAverage A y x := by apply _root_.YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof.sum_perm_bondFormSumAlong <;> assumption
end Paths
section Analysis
variable {L n k j : ℕ}
abbrev expFlow (B : Tower.Edge L n k j → ComplexMatrix2) (t : ℂ) : Tower.Edge L n k j → ComplexMatrix2 :=
  fun b => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • B b))
theorem matExp_inv (Z : ComplexMatrix2) :
    (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
theorem expTwist_smul_one (B : Tower.Edge L n k j → ComplexMatrix2) (hB : ∀ b, B b.opposite = -B b)
    (t : ℂ) :
    PeriodicLattice.expTwist (t • B) (fun _ => (1 : ComplexMatrix2)) = expFlow B t := by
  funext b
  simp only [PeriodicLattice.expTwist, Pi.smul_apply, mul_one]
  split_ifs with h
  · rfl
  · rw [matExp_inv, hB]
    congr 1
    simp
theorem hasDerivAt_matExp_I_smul (X : ComplexMatrix2) :
    HasDerivAt (fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • X))) (Complex.I • X) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℂ) (Complex.I • X) (0 : ℂ)
  have e : (fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • X))) =
      fun t : ℂ => NormedSpace.exp (t • Complex.I • X) := by
    funext t
    congr 1
    rw [smul_comm]
  rw [e]
  simpa using h
theorem expFlow_zero (B : Tower.Edge L n k j → ComplexMatrix2) : expFlow B 0 = fun _ => 1 := by
  funext b
  change ComplexMatrix2.matExp (Complex.I • ((0 : ℂ) • B b)) = 1
  rw [zero_smul, smul_zero]
  exact NormedSpace.exp_zero
theorem pathHolonomy_one (Γ : List (Tower.Edge L n k j)) :
    PeriodicLattice.pathHolonomy (fun _ : Tower.Edge L n k j => (1 : ComplexMatrix2)) Γ = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof.pathHolonomy_one <;> assumption
theorem hasDerivAt_pathHolonomy_expFlow (B : Tower.Edge L n k j → ComplexMatrix2)
    (Γ : List (Tower.Edge L n k j)) :
    HasDerivAt (fun t : ℂ => PeriodicLattice.pathHolonomy (expFlow B t) Γ)
      (Complex.I • PeriodicLattice.bondFormSumAlong B Γ) 0 := by
  induction Γ with
  | nil => simpa [PeriodicLattice.pathHolonomy, PeriodicLattice.bondFormSumAlong] using
      hasDerivAt_const (0 : ℂ) (1 : ComplexMatrix2)
  | cons b l ih =>
    have h := (hasDerivAt_matExp_I_smul (B b)).mul ih
    have h0 : PeriodicLattice.pathHolonomy (expFlow B 0) l = 1 := by
      rw [expFlow_zero, pathHolonomy_one]
    have e0 : ComplexMatrix2.matExp (Complex.I • ((0 : ℂ) • B b)) = 1 := congrFun (expFlow_zero B) b
    rw [h0, e0, mul_one, one_mul] at h
    have e : Complex.I • B b + Complex.I • PeriodicLattice.bondFormSumAlong B l =
        Complex.I • PeriodicLattice.bondFormSumAlong B (b :: l) := by
      simp [PeriodicLattice.bondFormSumAlong, smul_add]
    rw [e] at h
    exact h
theorem hasDerivAt_entry {W : ℂ → ComplexMatrix2} {D : ComplexMatrix2} (h : HasDerivAt W D 0)
    (a b : Fin 2) :
    HasDerivAt (fun t => W t a b) (D a b) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.ContourMeanDerivative.hasDerivAt_matrix_entry <;> assumption
theorem hasDerivAt_detRoot_and_normalized {W : ℂ → ComplexMatrix2} {D : ComplexMatrix2}
    (h : HasDerivAt W D 0) (h1 : W 0 = 1) (ht : ComplexMatrix2.fullTrace D = 0) :
    HasDerivAt (fun t => (Matrix.det (W t)) ^ (1 / 2 : ℂ)) 0 0 ∧
      HasDerivAt (fun t => ((Matrix.det (W t)) ^ (1 / 2 : ℂ))⁻¹ • W t) D 0 := by
  have hdet : HasDerivAt (fun t => Matrix.det (W t)) 0 0 := by
    have e : (fun t => Matrix.det (W t)) = fun t => W t 0 0 * W t 1 1 - W t 0 1 * W t 1 0 := by
      funext t
      exact Matrix.det_fin_two _
    rw [e]
    have := ((hasDerivAt_entry h 0 0).mul (hasDerivAt_entry h 1 1)).sub
      ((hasDerivAt_entry h 0 1).mul (hasDerivAt_entry h 1 0))
    have e0 : D 0 0 + D 1 1 = 0 := by
      simpa [ComplexMatrix2.fullTrace, Matrix.trace, Fin.sum_univ_two] using ht
    refine HasDerivAt.congr_deriv this ?_
    simp [h1, Matrix.one_apply]
    linear_combination e0
  have hd0 : Matrix.det (W 0) = 1 := by rw [h1]; simp
  have hr : HasDerivAt (fun z : ℂ => z ^ (1 / 2 : ℂ)) ((1 / 2 : ℂ) * (1 : ℂ) ^ ((1 / 2 : ℂ) - 1)) 1 := by
    have := (hasStrictDerivAt_id (1 : ℂ)).hasDerivAt.cpow_const (c := (1 / 2 : ℂ))
      (by simp [Complex.slitPlane])
    simpa using this
  have hroot : HasDerivAt (fun t => (Matrix.det (W t)) ^ (1 / 2 : ℂ)) 0 0 := by
    have := HasDerivAt.scomp (0 : ℂ) (g₁ := fun z : ℂ => z ^ (1 / 2 : ℂ)) (by rw [hd0]; exact hr) hdet
    exact HasDerivAt.congr_deriv this (by simp)
  refine ⟨hroot, ?_⟩
  have hr0 : (Matrix.det (W 0)) ^ (1 / 2 : ℂ) = 1 := by rw [hd0]; simp
  have hinv := hroot.inv (by rw [hr0]; exact one_ne_zero)
  have := hinv.smul h
  exact HasDerivAt.congr_deriv this (by simp [hr0, h1])
end Analysis
theorem holLeftDifferential_of_positive {L n k j : ℕ} (B : Tower.Edge L n k j → ComplexMatrix2)
    (c : Tower.Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) :
    Tower.holLeftDifferential normalizedMean (fun _ => 1) B c = Complex.I⁻¹ •
      deriv (fun t : ℂ => ComplexMatrix2.logSeries (normalizedMean (PeriodicLattice.expTwist (t • B)
        fun _ => (1 : ComplexMatrix2)) c *
          (normalizedMean (fun _ : Tower.Edge L n k j => (1 : ComplexMatrix2)) c)⁻¹)) 0 := by
  unfold Tower.holLeftDifferential Tower.extendOddly
  rw [if_pos hc]
  rfl
theorem holDifferentialAtOneEqSmoothing
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hb : PeriodicLattice.CrossingsAndBareBlocks.Statement) :
    HolDifferentialAtOneEqSmoothing := by
  intro L hL n k j hn hj B hB c hc
  have hform : ∀ b, B b.opposite = -B b := hB.2
  have hfl : ∀ t : ℂ, PeriodicLattice.expTwist (t • B) (fun _ => (1 : ComplexMatrix2)) = expFlow B t :=
    expTwist_smul_one B hform
  have hcard := ((hb L hL n k hn).1 j hj c hc).1
  have hLpos : 0 < L := by have := hL.2; omega
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Tower.Vertex L n k j)).Finite := by
    have h4 : Nat.card ↥(PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Tower.Vertex L n k j)) ≠ 0 := by rw [hcard]; positivity
    have := Nat.finite_of_card_ne_zero h4
    exact Set.toFinite _
  set S := hfin.toFinset with hSdef
  have hScard : S.card = L ^ 4 := by
    have h1 : S.card = (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Tower.Vertex L n k j)).ncard := (Set.ncard_eq_toFinset_card _ hfin).symm
    rw [h1, ← Nat.card_coe_set_eq, hcard]
  set w : ℂ := (1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L with hw
  have hmean : ∀ V : Tower.Edge L n k j → ComplexMatrix2, contourMean V c =
      w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), contourHolonomy V c x π := by
    intro V
    rw [contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin]
  let leg : Tower.Vertex L n k j → Equiv.Perm (Fin 4) → List (Tower.Edge L n k j) :=
    fun x π => contourLeg c.source x π
  let leg' : Tower.Vertex L n k j → Equiv.Perm (Fin 4) → List (Tower.Edge L n k j) :=
    fun x π => contourLeg c.target (PeriodicLattice.shiftAcross c x) π
  have hone : ∀ Γ : List (Tower.Edge L n k j),
      PeriodicLattice.pathHolonomy (expFlow B 0) Γ = 1 := fun Γ => by
    rw [expFlow_zero, pathHolonomy_one]
  have hinv1 : (1 : ComplexMatrix2)⁻¹ = 1 := Matrix.inv_eq_right_inv (mul_one 1)
  have hcv : ∀ x π, HasDerivAt (fun t => contourHolonomy (expFlow B t) c x π)
      (Complex.I • (PeriodicLattice.bondFormSumAlong B (leg x π) +
        PeriodicLattice.bondFormSumAlong B (PeriodicLattice.crossingPath c x) -
        PeriodicLattice.bondFormSumAlong B (leg' x π))) 0 := by
    intro x π
    have hX := hasDerivAt_pathHolonomy_expFlow B (leg x π)
    have hY := hasDerivAt_pathHolonomy_expFlow B (PeriodicLattice.crossingPath c x)
    have hZ0 := hasDerivAt_pathHolonomy_expFlow B (leg' x π)
    have hZ := (((hd.2 Set.univ _ _ _ _ _ _ Filter.univ_mem hZ0 hZ0 hZ0).2.1 (hone _)).2.1)
    have h3 := (hd.2 Set.univ _ _ _ _ _ _ Filter.univ_mem hX hY hZ).1
    refine HasDerivAt.congr_deriv h3 ?_
    simp only [hone, hinv1, mul_one, one_mul, smul_add, smul_sub, smul_neg]
    abel
  have hW : HasDerivAt (fun t => contourMean (expFlow B t) c)
      (w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4),
        Complex.I • (PeriodicLattice.bondFormSumAlong B (leg x π) +
          PeriodicLattice.bondFormSumAlong B (PeriodicLattice.crossingPath c x) -
          PeriodicLattice.bondFormSumAlong B (leg' x π))) 0 := by
    have h1 := (HasDerivAt.fun_sum (u := S) fun x _ =>
      HasDerivAt.fun_sum (u := Finset.univ) fun π _ => hcv x π).const_smul w
    have e : (fun t => contourMean (expFlow B t) c) = fun t => w • ∑ x ∈ S,
        ∑ π : Equiv.Perm (Fin 4), contourHolonomy (expFlow B t) c x π := by
      funext t
      exact hmean _
    rw [e]
    exact h1
  have hQ : ∀ x, ∑ π : Equiv.Perm (Fin 4), (PeriodicLattice.bondFormSumAlong B (leg x π) +
        PeriodicLattice.bondFormSumAlong B (PeriodicLattice.crossingPath c x) -
        PeriodicLattice.bondFormSumAlong B (leg' x π)) =
      (24 : ℂ) • (PeriodicLattice.contourFormAverage B c.source x +
        PeriodicLattice.bondFormSumAlong B (PeriodicLattice.crossingPath c x) -
        PeriodicLattice.contourFormAverage B c.target (PeriodicLattice.shiftAcross c x)) := by
    intro x
    have h1 := sum_perm_bondFormSumAlong_eq B c.source x
    have h2 := sum_perm_bondFormSumAlong_eq B c.target (PeriodicLattice.shiftAcross c x)
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, smul_sub, smul_add]
    simp only [leg, leg', contourLeg]
    rw [h1, h2]
    congr 2
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm]
    simp only [Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    norm_num [Nat.factorial]
  have hD : (w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4),
        Complex.I • (PeriodicLattice.bondFormSumAlong B (leg x π) +
          PeriodicLattice.bondFormSumAlong B (PeriodicLattice.crossingPath c x) -
          PeriodicLattice.bondFormSumAlong B (leg' x π))) =
      Complex.I • Tower.linearSmoothing L n k j B c := by
    have e1 : Tower.linearSmoothing L n k j B c = PeriodicLattice.inverseFourthPowerWeight L •
        ∑ x ∈ S, (PeriodicLattice.contourFormAverage B c.source x +
          PeriodicLattice.bondFormSumAlong B (PeriodicLattice.crossingPath c x) -
          PeriodicLattice.contourFormAverage B c.target (PeriodicLattice.shiftAcross c x)) := by
      change PeriodicLattice.inverseFourthPowerWeight L • PeriodicLattice.linearBlockSum B c = _
      rw [PeriodicLattice.linearBlockSum, finsum_mem_eq_finite_toFinset_sum _ hfin]
    rw [e1]
    simp only [← Finset.smul_sum, hQ]
    simp only [smul_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    rw [hw]
    ring
  have hW' : HasDerivAt (fun t => contourMean (expFlow B t) c)
      (Complex.I • Tower.linearSmoothing L n k j B c) 0 := hD ▸ hW
  have hval : contourMean (fun _ : Tower.Edge L n k j => (1 : ComplexMatrix2)) c = 1 := by
    rw [hmean]
    have e : ∀ x π, contourHolonomy (fun _ : Tower.Edge L n k j => (1 : ComplexMatrix2)) c x π = 1 := by
      intro x π
      simp only [contourHolonomy, pathHolonomy_one, hinv1, mul_one]
    simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, hScard]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
    have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hLpos.ne'
    have : w * (((L ^ 4 : ℕ) : ℂ) * ((Nat.factorial 4 : ℕ) : ℂ)) = 1 := by
      rw [hw, PeriodicLattice.inverseFourthPowerWeight]
      push_cast
      norm_num [Nat.factorial]
      field_simp
    rw [mul_assoc, this, one_smul]
  have hW1 : contourMean (expFlow B 0) c = 1 := by rw [expFlow_zero, hval]
  have htrB : ∀ b, ComplexMatrix2.fullTrace (B b) = 0 := by
    intro b
    obtain ⟨μ, h | h⟩ := b.isNeighbour
    · exact hB.1 b ⟨μ, h⟩
    · have hp : (PeriodicLattice.Bond.opposite b).IsPositivelyOriented :=
        ⟨μ, by change b.source - b.target = _; rw [← neg_sub, h, neg_neg]⟩
      have h1 : ComplexMatrix2.fullTrace _ = 0 := hB.1 _ hp
      rw [hform, ComplexMatrix2.fullTrace, Matrix.trace_neg, neg_eq_zero] at h1
      exact h1
  have htrΓ : ∀ Γ : List (Tower.Edge L n k j),
      ComplexMatrix2.fullTrace (PeriodicLattice.bondFormSumAlong B Γ) = 0 := by
    intro Γ
    induction Γ with
    | nil => simp [PeriodicLattice.bondFormSumAlong, ComplexMatrix2.fullTrace]
    | cons b l ih =>
      have := htrB b
      simp only [PeriodicLattice.bondFormSumAlong, List.map_cons, List.sum_cons,
        ComplexMatrix2.fullTrace, Matrix.trace_add] at ih this ⊢
      rw [ih, this, add_zero]
  have htr : ComplexMatrix2.fullTrace (Complex.I • Tower.linearSmoothing L n k j B c) = 0 := by
    rw [← hD]
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_sum, Matrix.trace_add,
      Matrix.trace_sub]
    have h1 := htrΓ
    simp only [ComplexMatrix2.fullTrace] at h1
    simp [h1]
  obtain ⟨hr, hu⟩ := hasDerivAt_detRoot_and_normalized hW' hW1 htr
  have hlen1 : meanRadius (fun _ : Tower.Edge L n k j => (1 : ComplexMatrix2)) c = 1 := by
    rw [meanRadius, hval]
    simp
  have hav1 : normalizedMean (fun _ : Tower.Edge L n k j => (1 : ComplexMatrix2)) c = 1 := by
    rw [normalizedMean, hlen1, hval]
    simp
  have hu0 : (Matrix.det (contourMean (expFlow B 0) c) ^ (1 / 2 : ℂ))⁻¹ •
      contourMean (expFlow B 0) c = 1 := by
    rw [hW1]
    simp
  have hlog := ((hd.2 Set.univ _ _ _ _ _ _ Filter.univ_mem hu hu hu).2.1 hu0).2.2.1
  have e2 : (fun t : ℂ => ComplexMatrix2.logSeries (normalizedMean (PeriodicLattice.expTwist (t • B)
        fun _ => (1 : ComplexMatrix2)) c *
          (normalizedMean (fun _ : Tower.Edge L n k j => (1 : ComplexMatrix2)) c)⁻¹)) =
        fun t => ComplexMatrix2.logSeries ((Matrix.det (contourMean (expFlow B t) c) ^ (1 / 2 : ℂ))⁻¹ •
          contourMean (expFlow B t) c) := by
      funext t
      rw [hav1, hinv1, mul_one, hfl t, normalizedMean, meanRadius]
  rw [holLeftDifferential_of_positive B c hc, e2, hlog.deriv, smul_smul,
    inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
end YangMills.Construction.RunningCouplingSlope.HolDifferentialAtOneProof
end
