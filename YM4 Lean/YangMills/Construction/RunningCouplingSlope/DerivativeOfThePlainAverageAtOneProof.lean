import YangMills.Construction.Lattice.CrossingsAndBareBlocksInTheToolbox
import YangMills.Construction.Matrices.PointwiseDerivativeRules
import YangMills.Construction.RunningCouplingSlope.DerivativeOfThePlainAverageAtOne
import YangMills.Construction.Towers.GaugeDirectionsInTheLeftChartProof
import YangMills.Construction.Towers.PathsDifferentiableAtZeroProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof
open Tower
section Permutations
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
abbrev permList (π : Equiv.Perm (Fin 4)) : List (Fin 4) := (List.finRange 4).map π
abbrev enumList {S : Finset (Fin 4)} (σ : Fin S.card ≃ S) : List (Fin 4) :=
  (List.finRange S.card).map fun i => ((σ i : S) : Fin 4)
theorem exists_enumList_eq_filter (S : Finset (Fin 4)) (π : Equiv.Perm (Fin 4)) :
    ∃ σ : Fin S.card ≃ S, enumList σ = (permList π).filter (· ∈ S) := by
  set l := (permList π).filter (· ∈ S) with hl
  have hnd : l.Nodup :=
    List.Nodup.filter _ ((List.nodup_finRange 4).map π.injective)
  have hmem : ∀ a, a ∈ l ↔ a ∈ S := by
    intro a
    simp only [hl, permList, List.mem_filter, List.mem_map, List.mem_finRange, true_and,
      decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨⟨π.symm a, by simp⟩, h⟩⟩
  have hlen : l.length = S.card := by
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext a
    simp [hmem]
  let f : Fin S.card → S := fun i =>
    ⟨l.get (Fin.cast hlen.symm i), (hmem _).mp (List.get_mem _ _)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i i' hii'
      have h1 : l.get (Fin.cast hlen.symm i) = l.get (Fin.cast hlen.symm i') :=
        congrArg Subtype.val hii'
      have h2 := (List.nodup_iff_injective_get.mp hnd) h1
      exact Fin.ext (by simpa using congrArg Fin.val h2)
    · rintro ⟨a, ha⟩
      obtain ⟨i, hi⟩ := List.get_of_mem ((hmem a).mpr ha)
      exact ⟨Fin.cast hlen i, Subtype.ext (by simpa [f] using hi)⟩
  refine ⟨Equiv.ofBijective f hf, ?_⟩
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    simp [f, Equiv.ofBijective]
theorem card_smul_sum_permList (S : Finset (Fin 4)) (F : List (Fin 4) → E)
    (hF : ∀ l, F l = F (l.filter (· ∈ S))) :
    (Fintype.card (Fin S.card ≃ S)) • ∑ π : Equiv.Perm (Fin 4), F (permList π) =
      (24 : ℕ) • ∑ σ : Fin S.card ≃ S, F (enumList σ) := by
  classical
  have hρ : ∀ (ρ : Equiv.Perm S) (a : Fin 4),
      (Equiv.Perm.ofSubtype ρ a ∈ S) ↔ a ∈ S := by
    intro ρ a
    by_cases ha : a ∈ S
    · have : Equiv.Perm.ofSubtype ρ a = (ρ ⟨a, ha⟩ : S) :=
        Equiv.Perm.ofSubtype_apply_of_mem ρ ha
      rw [this]
      exact ⟨fun _ => ha, fun _ => (ρ ⟨a, ha⟩).2⟩
    · have : Equiv.Perm.ofSubtype ρ a = a := Equiv.Perm.ofSubtype_apply_of_not_mem ρ ha
      rw [this]
  have hfilter : ∀ (ρ : Equiv.Perm S) (π : Equiv.Perm (Fin 4)),
      (permList (Equiv.Perm.ofSubtype ρ * π)).filter (· ∈ S) =
        ((permList π).filter (· ∈ S)).map (Equiv.Perm.ofSubtype ρ) := by
    intro ρ π
    have : permList (Equiv.Perm.ofSubtype ρ * π) =
        (permList π).map (Equiv.Perm.ofSubtype ρ) := by
      simp [permList, List.map_map, Function.comp_def]
    rw [this, List.filter_map]
    congr 1
    apply List.filter_congr
    intro a _
    simp [hρ]
  have hinner : ∀ π : Equiv.Perm (Fin 4),
      ∑ ρ : Equiv.Perm S, F (permList (Equiv.Perm.ofSubtype ρ * π)) =
        ∑ σ : Fin S.card ≃ S, F (enumList σ) := by
    intro π
    obtain ⟨σ₀, hσ₀⟩ := exists_enumList_eq_filter S π
    refine Fintype.sum_equiv
      ⟨fun ρ => σ₀.trans ρ, fun σ => σ₀.symm.trans σ, fun ρ => by ext a; simp,
        fun σ => by ext a; simp⟩ _ _ fun ρ => ?_
    rw [hF, hfilter, ← hσ₀]
    congr 1
    simp [enumList, List.map_map, Function.comp_def, Equiv.Perm.ofSubtype_apply_coe]
  have hshift : ∀ ρ : Equiv.Perm S, ∑ π : Equiv.Perm (Fin 4), F (permList π) =
      ∑ π : Equiv.Perm (Fin 4), F (permList (Equiv.Perm.ofSubtype ρ * π)) := by
    intro ρ
    exact (Fintype.sum_equiv (Equiv.mulLeft (Equiv.Perm.ofSubtype ρ)) _ _ fun π => rfl).symm
  have hcard : Fintype.card (Fin S.card ≃ S) = Fintype.card (Equiv.Perm S) := by
    rw [Fintype.card_equiv (Fintype.equivFinOfCardEq (by simp)).symm]
    simp [Fintype.card_perm]
  have h24 : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by
    simp [Fintype.card_perm]; rfl
  calc (Fintype.card (Fin S.card ≃ S)) • ∑ π : Equiv.Perm (Fin 4), F (permList π)
      = ∑ _ρ : Equiv.Perm S, ∑ π : Equiv.Perm (Fin 4), F (permList π) := by
        rw [hcard, Finset.sum_const, Finset.card_univ]
    _ = ∑ ρ : Equiv.Perm S, ∑ π : Equiv.Perm (Fin 4),
          F (permList (Equiv.Perm.ofSubtype ρ * π)) := Finset.sum_congr rfl fun ρ _ => hshift ρ
    _ = ∑ π : Equiv.Perm (Fin 4), ∑ ρ : Equiv.Perm S,
          F (permList (Equiv.Perm.ofSubtype ρ * π)) := Finset.sum_comm
    _ = ∑ _π : Equiv.Perm (Fin 4), ∑ σ : Fin S.card ≃ S, F (enumList σ) :=
        Finset.sum_congr rfl fun π _ => hinner π
    _ = (24 : ℕ) • ∑ σ : Fin S.card ≃ S, F (enumList σ) := by
        rw [Finset.sum_const, Finset.card_univ, h24]
end Permutations
section LatticePaths
variable {L m : ℕ} {j : ℤ}
theorem stepsThroughAxes_filter (d : Fin 4 → ℤ) (S : Finset (Fin 4)) (hS : ∀ μ, μ ∉ S → d μ = 0)
    (x : PeriodicLattice.Site L m j) (l : List (Fin 4)) :
    PeriodicLattice.stepsThroughAxes d x l =
      PeriodicLattice.stepsThroughAxes d x (l.filter (· ∈ S)) := by
  induction l generalizing x with
  | nil => rfl
  | cons μ l ih =>
    by_cases h : μ ∈ S
    · simp only [List.filter_cons, h, decide_true, if_true, PeriodicLattice.stepsThroughAxes]
      rw [ih]
    · have h0 := hS μ h
      simp only [List.filter_cons, h, decide_false, Bool.false_eq_true, if_false,
        PeriodicLattice.stepsThroughAxes, h0, zero_smul, add_zero]
      rw [ih]
      simp [PeriodicLattice.flowAlong, PeriodicLattice.forwardAxisPath]
theorem sum_perm_bondFormSumAlong (A : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) {i : ℤ}
    (y : PeriodicLattice.Site L m i) (x : PeriodicLattice.Site L m j) :
    ∑ π : Equiv.Perm (Fin 4), PeriodicLattice.bondFormSumAlong A
        (PeriodicLattice.stepsThroughAxes (PeriodicLattice.blockOffset y x) (y.toSublattice j)
          (permList π)) =
      (24 : ℂ) • PeriodicLattice.contourFormAverage A y x := by
  set S := PeriodicLattice.offsetAxes y x with hSdef
  have hS : ∀ μ, μ ∉ S → PeriodicLattice.blockOffset y x μ = 0 := by
    intro μ hμ
    by_contra h
    exact hμ (by simp [hSdef, PeriodicLattice.offsetAxes, h])
  let F : List (Fin 4) → Matrices.ComplexMatrix2 := fun l => PeriodicLattice.bondFormSumAlong A
    (PeriodicLattice.stepsThroughAxes (PeriodicLattice.blockOffset y x) (y.toSublattice j) l)
  have hF : ∀ l, F l = F (l.filter (· ∈ S)) := fun l => by
    simp only [F]
    rw [← stepsThroughAxes_filter _ S hS]
  have h := card_smul_sum_permList (E := Matrices.ComplexMatrix2) S F hF
  have hcard : ((Fintype.card (Fin S.card ≃ S) : ℕ) : ℂ) ≠ 0 := by
    have : Fintype.card (Fin S.card ≃ S) ≠ 0 := by
      have : Nonempty (Fin S.card ≃ S) := ⟨(Fintype.equivFinOfCardEq (by simp)).symm⟩
      exact Fintype.card_ne_zero
    exact_mod_cast this
  rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h
  have h2 : ∑ π : Equiv.Perm (Fin 4), F (permList π) =
      (((Fintype.card (Fin S.card ≃ S) : ℕ) : ℂ)⁻¹ * 24) • ∑ σ : Fin S.card ≃ S, F (enumList σ) := by
    rw [mul_smul]
    have h3 : ((24 : ℕ) : ℂ) = 24 := by norm_num
    rw [h3] at h
    rw [← h, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  change ∑ π : Equiv.Perm (Fin 4), F (permList π) = _
  rw [h2, PeriodicLattice.contourFormAverage, smul_smul]
  congr 1
  · push_cast
    rw [mul_comm]
end LatticePaths
section Derivatives
variable {L n k j : ℕ}
abbrev expFlow (B : Edge L n k j → Matrices.ComplexMatrix2) (t : ℝ) :
    Edge L n k j → Matrices.ComplexMatrix2 :=
  fun b => Matrices.ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • B b))
theorem matExp_inv (Z : Matrices.ComplexMatrix2) :
    (Matrices.ComplexMatrix2.matExp Z)⁻¹ = Matrices.ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
theorem expTwist_eq_expFlow (B : Edge L n k j → Matrices.ComplexMatrix2)
    (hB : ∀ b, B b.opposite = -B b) (t : ℝ) :
    PeriodicLattice.expTwist ((t : ℂ) • B) (fun _ => (1 : Matrices.ComplexMatrix2)) = expFlow B t := by
  funext b
  simp only [PeriodicLattice.expTwist, Pi.smul_apply, mul_one]
  split_ifs with h
  · rfl
  · rw [matExp_inv, hB]
    congr 1
    simp
theorem hasDerivAt_matExp_smul (X : Matrices.ComplexMatrix2) :
    HasDerivAt (fun t : ℝ => Matrices.ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • X)))
      (Complex.I • X) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (Complex.I • X) (0 : ℝ)
  have e : (fun t : ℝ => Matrices.ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • X))) =
      fun t : ℝ => NormedSpace.exp (t • Complex.I • X) := by
    funext t
    congr 1
    rw [smul_comm, Complex.coe_smul]
  rw [e]
  simpa using h
theorem expFlow_zero (B : Edge L n k j → Matrices.ComplexMatrix2) : expFlow B 0 = fun _ => 1 := by
  funext b
  change Matrices.ComplexMatrix2.matExp (Complex.I • (((0 : ℝ) : ℂ) • B b)) = 1
  rw [Complex.ofReal_zero, zero_smul, smul_zero]
  exact NormedSpace.exp_zero
theorem pathHolonomy_one (Γ : List (Edge L n k j)) :
    PeriodicLattice.pathHolonomy (fun _ : Edge L n k j => (1 : Matrices.ComplexMatrix2)) Γ = 1 := by
  induction Γ with
  | nil => rfl
  | cons b l ih =>
    simp only [PeriodicLattice.pathHolonomy, List.map_cons, List.prod_cons, one_mul] at ih ⊢
    exact ih
theorem hasDerivAt_pathHolonomy (B : Edge L n k j → Matrices.ComplexMatrix2) (Γ : List (Edge L n k j)) :
    HasDerivAt (fun t : ℝ => PeriodicLattice.pathHolonomy (expFlow B t) Γ)
      (Complex.I • PeriodicLattice.bondFormSumAlong B Γ) 0 := by
  induction Γ with
  | nil => simpa [PeriodicLattice.pathHolonomy, PeriodicLattice.bondFormSumAlong] using
      hasDerivAt_const (0 : ℝ) (1 : Matrices.ComplexMatrix2)
  | cons b l ih =>
    have h := (hasDerivAt_matExp_smul (B b)).mul ih
    have h0 : PeriodicLattice.pathHolonomy (expFlow B 0) l = 1 := by
      rw [expFlow_zero, pathHolonomy_one]
    have e0 : Matrices.ComplexMatrix2.matExp (Complex.I • (((0 : ℝ) : ℂ) • B b)) = 1 :=
      congrFun (expFlow_zero B) b
    rw [h0, e0, mul_one, one_mul] at h
    have e : Complex.I • B b + Complex.I • PeriodicLattice.bondFormSumAlong B l =
        Complex.I • PeriodicLattice.bondFormSumAlong B (b :: l) := by
      simp [PeriodicLattice.bondFormSumAlong, smul_add]
    rw [e] at h
    exact h
theorem hasDerivAt_entry {W : ℝ → Matrices.ComplexMatrix2} {D : Matrices.ComplexMatrix2}
    (h : HasDerivAt W D 0) (a b : Fin 2) :
    HasDerivAt (fun t => W t a b) (D a b) 0 := by apply _root_.YangMills.Construction.Tower.DiffAtZeroPaths.hasDerivAt_entry <;> assumption
theorem hasDerivAt_sqrtDet_and_unitPart {W : ℝ → Matrices.ComplexMatrix2} {D : Matrices.ComplexMatrix2}
    (h : HasDerivAt W D 0) (h1 : W 0 = 1) (ht : Matrices.ComplexMatrix2.fullTrace D = 0) :
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
      simpa [Matrices.ComplexMatrix2.fullTrace, Matrix.trace, Fin.sum_univ_two] using ht
    refine HasDerivAt.congr_deriv this ?_
    simp [h1, Matrix.one_apply]
    linear_combination e0
  have hd0 : Matrix.det (W 0) = 1 := by rw [h1]; simp
  have hr : HasDerivAt (fun z : ℂ => z ^ (1 / 2 : ℂ)) ((1 / 2 : ℂ) * (1 : ℂ) ^ ((1 / 2 : ℂ) - 1)) 1 := by
    have := (hasStrictDerivAt_id (1 : ℂ)).hasDerivAt.cpow_const (c := (1 / 2 : ℂ))
      (by simp [Complex.slitPlane])
    simpa using this
  have hroot : HasDerivAt (fun t => (Matrix.det (W t)) ^ (1 / 2 : ℂ)) 0 0 := by
    have := HasDerivAt.scomp (0 : ℝ) (g₁ := fun z : ℂ => z ^ (1 / 2 : ℂ)) (by rw [hd0]; exact hr) hdet
    exact HasDerivAt.congr_deriv this (by simp)
  refine ⟨hroot, ?_⟩
  have hr0 : (Matrix.det (W 0)) ^ (1 / 2 : ℂ) = 1 := by rw [hd0]; simp
  have hinv := hroot.inv (by rw [hr0]; exact one_ne_zero)
  have := hinv.smul h
  exact HasDerivAt.congr_deriv this (by simp [hr0, h1])
end Derivatives
theorem leftDifferential_of_positive {L n k j : ℕ} (B : Edge L n k j → Matrices.ComplexMatrix2)
    (c : Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) :
    leftDifferential normalizedMean (fun _ => 1) B c = Complex.I⁻¹ •
      deriv (fun t : ℝ => Matrices.ComplexMatrix2.logSeries
        (normalizedMean (PeriodicLattice.expTwist ((t : ℂ) • B)
          fun _ => (1 : Matrices.ComplexMatrix2)) c *
          (normalizedMean (fun _ : Edge L n k j => (1 : Matrices.ComplexMatrix2)) c)⁻¹)) 0 := by
  unfold leftDifferential extendOddly
  rw [if_pos hc]
  rfl
theorem normalizedMeanAtOne (hd : Matrices.ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hb : PeriodicLattice.CrossingsAndBareBlocks.Statement) :
    NormalizedMeanAtOne := by
  intro L hL n k j hn hj B hB c hc
  have hform : ∀ b, B b.opposite = -B b := hB.2
  have hfl : ∀ t : ℝ, PeriodicLattice.expTwist ((t : ℂ) • B)
      (fun _ => (1 : Matrices.ComplexMatrix2)) = expFlow B t :=
    expTwist_eq_expFlow B hform
  have hcard := ((hb L hL n k hn).1 j hj c hc).1
  have hLpos : 0 < L := by have := hL.2; omega
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := by
    have h4 : Nat.card ↥(PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Vertex L n k j)) ≠ 0 := by rw [hcard]; positivity
    have := Nat.finite_of_card_ne_zero h4
    exact Set.toFinite _
  set S := hfin.toFinset with hSdef
  have hScard : S.card = L ^ 4 := by
    have h1 : S.card = (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Vertex L n k j)).ncard := (Set.ncard_eq_toFinset_card _ hfin).symm
    rw [h1, ← Nat.card_coe_set_eq, hcard]
  set w : ℂ := (1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L with hw
  have hmean : ∀ V : Edge L n k j → Matrices.ComplexMatrix2, contourMean V c =
      w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), contourHolonomy V c x π := by
    intro V
    rw [contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin]
  let leg : Vertex L n k j → Equiv.Perm (Fin 4) → List (Edge L n k j) :=
    fun x π => contourLeg c.source x π
  let leg' : Vertex L n k j → Equiv.Perm (Fin 4) → List (Edge L n k j) :=
    fun x π => contourLeg c.target (PeriodicLattice.shiftAcross c x) π
  have hone : ∀ Γ : List (Edge L n k j),
      PeriodicLattice.pathHolonomy (expFlow B 0) Γ = 1 := fun Γ => by
    rw [expFlow_zero, pathHolonomy_one]
  have hinv1 : (1 : Matrices.ComplexMatrix2)⁻¹ = 1 := Matrix.inv_eq_right_inv (mul_one 1)
  have hcv : ∀ x π, HasDerivAt (fun t => contourHolonomy (expFlow B t) c x π)
      (Complex.I • (PeriodicLattice.bondFormSumAlong B (leg x π) +
        PeriodicLattice.bondFormSumAlong B (PeriodicLattice.crossingPath c x) -
        PeriodicLattice.bondFormSumAlong B (leg' x π))) 0 := by
    intro x π
    have hX := hasDerivAt_pathHolonomy B (leg x π)
    have hY := hasDerivAt_pathHolonomy B (PeriodicLattice.crossingPath c x)
    have hZ0 := hasDerivAt_pathHolonomy B (leg' x π)
    have hZ := (((hd.1 Set.univ _ _ _ _ _ _ Filter.univ_mem hZ0 hZ0 hZ0).2.1 (hone _)).2.1)
    have h3 := (hd.1 Set.univ _ _ _ _ _ _ Filter.univ_mem hX hY hZ).1
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
    have h1 := sum_perm_bondFormSumAlong B c.source x
    have h2 := sum_perm_bondFormSumAlong B c.target (PeriodicLattice.shiftAcross c x)
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
      Complex.I • linearSmoothing L n k j B c := by
    have e1 : linearSmoothing L n k j B c = PeriodicLattice.inverseFourthPowerWeight L •
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
      (Complex.I • linearSmoothing L n k j B c) 0 := hD ▸ hW
  have hval : contourMean (fun _ : Edge L n k j => (1 : Matrices.ComplexMatrix2)) c = 1 := by
    rw [hmean]
    have e : ∀ x π, contourHolonomy (fun _ : Edge L n k j => (1 : Matrices.ComplexMatrix2)) c x π = 1 := by
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
  have htrB : ∀ b, Matrices.ComplexMatrix2.fullTrace (B b) = 0 := by
    intro b
    obtain ⟨μ, h | h⟩ := b.isNeighbour
    · exact (hB.1 b ⟨μ, h⟩).2
    · have hp : (PeriodicLattice.Bond.opposite b).IsPositivelyOriented :=
        ⟨μ, by change b.source - b.target = _; rw [← neg_sub, h, neg_neg]⟩
      have h1 := (hB.1 _ hp).2
      rw [hform, Matrices.ComplexMatrix2.fullTrace, Matrix.trace_neg, neg_eq_zero] at h1
      exact h1
  have htrΓ : ∀ Γ : List (Edge L n k j),
      Matrices.ComplexMatrix2.fullTrace (PeriodicLattice.bondFormSumAlong B Γ) = 0 := by
    intro Γ
    induction Γ with
    | nil => simp [PeriodicLattice.bondFormSumAlong, Matrices.ComplexMatrix2.fullTrace]
    | cons b l ih =>
      have := htrB b
      simp only [PeriodicLattice.bondFormSumAlong, List.map_cons, List.sum_cons,
        Matrices.ComplexMatrix2.fullTrace, Matrix.trace_add] at ih this ⊢
      rw [ih, this, add_zero]
  have htr : Matrices.ComplexMatrix2.fullTrace (Complex.I • linearSmoothing L n k j B c) = 0 := by
    rw [← hD]
    simp only [Matrices.ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_sum,
      Matrix.trace_add, Matrix.trace_sub]
    have h1 := htrΓ
    simp only [Matrices.ComplexMatrix2.fullTrace] at h1
    simp [h1]
  obtain ⟨hr, hu⟩ := hasDerivAt_sqrtDet_and_unitPart hW' hW1 htr
  have hlen1 : meanRadius (fun _ : Edge L n k j => (1 : Matrices.ComplexMatrix2)) c = 1 := by
    rw [meanRadius, hval]
    simp
  have hav1 : normalizedMean (fun _ : Edge L n k j => (1 : Matrices.ComplexMatrix2)) c = 1 := by
    rw [normalizedMean, hlen1, hval]
    simp
  have hu0 : (Matrix.det (contourMean (expFlow B 0) c) ^ (1 / 2 : ℂ))⁻¹ •
      contourMean (expFlow B 0) c = 1 := by
    rw [hW1]
    simp
  have hlog := ((hd.1 Set.univ _ _ _ _ _ _ Filter.univ_mem hu hu hu).2.1 hu0).2.2.1
  refine ⟨hval, hlen1, hav1, ?_, ?_⟩
  · have e : (fun t : ℝ => meanRadius
        (PeriodicLattice.expTwist ((t : ℂ) • B) fun _ => (1 : Matrices.ComplexMatrix2)) c) =
        fun t => Matrix.det (contourMean (expFlow B t) c) ^ (1 / 2 : ℂ) := by
      funext t
      rw [hfl, meanRadius]
    rw [e]
    exact hr
  · have e2 : (fun t : ℝ => Matrices.ComplexMatrix2.logSeries
        (normalizedMean (PeriodicLattice.expTwist ((t : ℂ) • B)
          fun _ => (1 : Matrices.ComplexMatrix2)) c *
          (normalizedMean (fun _ : Edge L n k j => (1 : Matrices.ComplexMatrix2)) c)⁻¹)) =
        fun t => Matrices.ComplexMatrix2.logSeries
          ((Matrix.det (contourMean (expFlow B t) c) ^ (1 / 2 : ℂ))⁻¹ •
            contourMean (expFlow B t) c) := by
      funext t
      rw [hav1, hinv1, mul_one, hfl t, normalizedMean, meanRadius]
    rw [leftDifferential_of_positive B c hc, e2, hlog.deriv, smul_smul,
      inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
end YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof
end
