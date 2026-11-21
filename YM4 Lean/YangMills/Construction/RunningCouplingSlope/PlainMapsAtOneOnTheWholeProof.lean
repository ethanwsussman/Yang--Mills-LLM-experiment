import YangMills.Construction.RunningCouplingSlope.DerivativeOfThePlainAverageAtOneProof
import YangMills.Construction.RunningCouplingSlope.PlainDifferentialAtOneOnComplexFormsProof
import YangMills.Construction.RunningCouplingSlope.PlainMapsAtOneOnTheWhole
import YangMills.Construction.Towers.ObjectsOfATowerPickedByTheirPropertiesHaveThoseProperties
import YangMills.Construction.Towers.StepOfTheCovariantAveragesAtOneAtTheSideInfinityProof
import YangMills.Construction.Towers.StepsAtTheTrivialConfigurationOfTheScaledPictureOnTheWhole
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace FullLattice.TrivialFieldMaps
open Tower Tower.FullSpace
section Permutations
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
abbrev permList (π : Equiv.Perm (Fin 4)) : List (Fin 4) := (List.finRange 4).map π
abbrev enumList {S : Finset (Fin 4)} (σ : Fin S.card ≃ S) : List (Fin 4) :=
  (List.finRange S.card).map fun i => ((σ i : S) : Fin 4)
private theorem exists_enumList_eq_filter (S : Finset (Fin 4)) (π : Equiv.Perm (Fin 4)) :
    ∃ σ : Fin S.card ≃ S, enumList σ = (permList π).filter (· ∈ S) := by apply _root_.YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof.exists_enumList_eq_filter <;> assumption
private theorem card_smul_sum_permList (S : Finset (Fin 4)) (F : List (Fin 4) → E)
    (hF : ∀ l, F l = F (l.filter (· ∈ S))) :
    (Fintype.card (Fin S.card ≃ S)) • ∑ π : Equiv.Perm (Fin 4), F (permList π) =
      (24 : ℕ) • ∑ σ : Fin S.card ≃ S, F (enumList σ) := by apply _root_.YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof.card_smul_sum_permList <;> assumption
end Permutations
section Paths
variable {L : ℕ} {a a' : ℝ}
private theorem stepsInOrder_filter (d : Fin 4 → ℤ) (S : Finset (Fin 4))
    (hS : ∀ μ, μ ∉ S → d μ = 0) (x : InfiniteLattice.LatticePoint a') (l : List (Fin 4)) :
    FullSpace.stepsInOrder d x l = FullSpace.stepsInOrder d x (l.filter (· ∈ S)) := by
  induction l generalizing x with
  | nil => rfl
  | cons μ l ih =>
    by_cases h : μ ∈ S
    · simp only [List.filter_cons, h, decide_true, if_true, FullSpace.stepsInOrder]
      rw [ih]
    · have h0 := hS μ h
      simp only [List.filter_cons, h, decide_false, Bool.false_eq_true, if_false,
        FullSpace.stepsInOrder, h0, zero_smul, add_zero]
      rw [ih]
      simp [FullSpace.signedSteps, FullSpace.forwardSteps]
abbrev _root_.YangMills.SharedProofs.p61879 := @stepsInOrder_filter
private theorem sum_permList_sumAlong (A : InfiniteLattice.Link a' → Matrices.ComplexMatrix2)
    (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a') :
    ∑ π : Equiv.Perm (Fin 4), FullSpace.sumAlong A
        (FullSpace.stepsInOrder (FullSpace.cubeOffset L y x) (FullSpace.toFiner a' y) (permList π)) =
      (24 : ℂ) • FullSpace.contourAverage L A y x := by
  set S := FullSpace.offsetSupport L y x with hSdef
  have hS : ∀ μ, μ ∉ S → FullSpace.cubeOffset L y x μ = 0 := by
    intro μ hμ
    by_contra h
    exact hμ (by simp [hSdef, FullSpace.offsetSupport, h])
  let F : List (Fin 4) → Matrices.ComplexMatrix2 := fun l => FullSpace.sumAlong A
    (FullSpace.stepsInOrder (FullSpace.cubeOffset L y x) (FullSpace.toFiner a' y) l)
  have hF : ∀ l, F l = F (l.filter (· ∈ S)) := fun l => by
    simp only [F]
    rw [← stepsInOrder_filter _ S hS]
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
  rw [h2, FullSpace.contourAverage, smul_smul]
  congr 1
  · push_cast
    rw [mul_comm]
end Paths
section Analysis
variable {a : ℝ}
private abbrev expFlow (B : InfiniteLattice.Link a → Matrices.ComplexMatrix2) (t : ℂ) :
    InfiniteLattice.Link a → Matrices.ComplexMatrix2 :=
  fun b => Matrices.ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • B b))
private theorem matExp_inv (Z : Matrices.ComplexMatrix2) :
    (Matrices.ComplexMatrix2.matExp Z)⁻¹ = Matrices.ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
private theorem expTwist_smul_one (B : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (hB : ∀ b, B b.opposite = -B b) (t : ℂ) :
    FullSpace.expTwist (t • B) (fun _ => (1 : Matrices.ComplexMatrix2)) = expFlow B t := by
  funext b
  simp only [FullSpace.expTwist, Pi.smul_apply, mul_one]
  split_ifs with h
  · rfl
  · rw [matExp_inv, hB]
    congr 1
    simp
private theorem hasDerivAt_expFlow (X : Matrices.ComplexMatrix2) :
    HasDerivAt (fun t : ℂ => Matrices.ComplexMatrix2.matExp (Complex.I • (t • X)))
      (Complex.I • X) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.HolDifferentialAtOneProof.hasDerivAt_matExp_I_smul <;> assumption
private theorem expFlow_zero (B : InfiniteLattice.Link a → Matrices.ComplexMatrix2) :
    expFlow B 0 = fun _ => 1 := by
  funext b
  change Matrices.ComplexMatrix2.matExp (Complex.I • ((0 : ℂ) • B b)) = 1
  rw [zero_smul, smul_zero]
  exact NormedSpace.exp_zero
private theorem linkHolonomy_one (Γ : List (InfiniteLattice.Link a)) :
    FullSpace.linkHolonomy (fun _ : InfiniteLattice.Link a => (1 : Matrices.ComplexMatrix2)) Γ = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.StepAtTrivial.linkHolonomy_const_one <;> assumption
private theorem hasDerivAt_linkHolonomy (B : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (Γ : List (InfiniteLattice.Link a)) :
    HasDerivAt (fun t : ℂ => FullSpace.linkHolonomy (expFlow B t) Γ)
      (Complex.I • FullSpace.sumAlong B Γ) 0 := by
  induction Γ with
  | nil =>
    simpa [FullSpace.linkHolonomy, FullSpace.sumAlong] using
      hasDerivAt_const (0 : ℂ) (1 : Matrices.ComplexMatrix2)
  | cons b l ih =>
    have h := (hasDerivAt_expFlow (B b)).mul ih
    have h0 : FullSpace.linkHolonomy (expFlow B 0) l = 1 := by
      rw [expFlow_zero, linkHolonomy_one]
    have e0 : Matrices.ComplexMatrix2.matExp (Complex.I • ((0 : ℂ) • B b)) = 1 :=
      congrFun (expFlow_zero B) b
    rw [h0, e0, mul_one, one_mul] at h
    have e : Complex.I • B b + Complex.I • FullSpace.sumAlong B l =
        Complex.I • FullSpace.sumAlong B (b :: l) := by
      simp [FullSpace.sumAlong, smul_add]
    rw [e] at h
    exact h
private theorem hasDerivAt_entry {W : ℂ → Matrices.ComplexMatrix2} {D : Matrices.ComplexMatrix2}
    (h : HasDerivAt W D 0) (a b : Fin 2) :
    HasDerivAt (fun t => W t a b) (D a b) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.ContourMeanDerivative.hasDerivAt_matrix_entry <;> assumption
private theorem hasDerivAt_detNormalize {W : ℂ → Matrices.ComplexMatrix2}
    {D : Matrices.ComplexMatrix2} (h : HasDerivAt W D 0) (h1 : W 0 = 1)
    (ht : Matrices.ComplexMatrix2.fullTrace D = 0) :
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
  have hr : HasDerivAt (fun z : ℂ => z ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (1 : ℂ) ^ ((1 / 2 : ℂ) - 1)) 1 := by
    have := (hasStrictDerivAt_id (1 : ℂ)).hasDerivAt.cpow_const (c := (1 / 2 : ℂ))
      (by simp [Complex.slitPlane])
    simpa using this
  have hroot : HasDerivAt (fun t => (Matrix.det (W t)) ^ (1 / 2 : ℂ)) 0 0 := by
    have := HasDerivAt.scomp (0 : ℂ) (g₁ := fun z : ℂ => z ^ (1 / 2 : ℂ))
      (by rw [hd0]; exact hr) hdet
    exact HasDerivAt.congr_deriv this (by simp)
  have hr0 : (Matrix.det (W 0)) ^ (1 / 2 : ℂ) = 1 := by rw [hd0]; simp
  have hinv := hroot.inv (by rw [hr0]; exact one_ne_zero)
  have := hinv.smul h
  exact HasDerivAt.congr_deriv this (by simp [hr0, h1])
end Analysis
section Step
variable {L k j : ℕ}
private theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < Tower.meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
private theorem matrix_one_inv : (1 : Matrices.ComplexMatrix2)⁻¹ = 1 :=
  Matrix.inv_eq_right_inv (mul_one 1)
private theorem fullTrace_of_mem {a : ℝ} {B : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms a) (b : InfiniteLattice.Link a) :
    Matrices.ComplexMatrix2.fullTrace (B b) = 0 := by
  have hform : ∀ b, B b.opposite = -B b := hB.2
  obtain ⟨μ, h | h⟩ := b.isAdjacent
  · exact hB.1 b ⟨μ, h⟩
  · have hp : (InfiniteLattice.Link.opposite b).IsPositivelyOriented :=
      ⟨μ, by change b.initial - b.terminal = _; rw [← neg_sub, h, neg_neg]⟩
    have h1 : Matrices.ComplexMatrix2.fullTrace _ = 0 := hB.1 _ hp
    rw [hform, Matrices.ComplexMatrix2.fullTrace, Matrix.trace_neg, neg_eq_zero] at h1
    exact h1
private theorem fullTrace_sumAlong {a : ℝ} {B : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms a) (Γ : List (InfiniteLattice.Link a)) :
    Matrices.ComplexMatrix2.fullTrace (FullSpace.sumAlong B Γ) = 0 := by
  induction Γ with
  | nil => simp [FullSpace.sumAlong, Matrices.ComplexMatrix2.fullTrace]
  | cons b l ih =>
    have := fullTrace_of_mem hB b
    simp only [FullSpace.sumAlong, List.map_cons, List.sum_cons,
      Matrices.ComplexMatrix2.fullTrace, Matrix.trace_add] at ih this ⊢
    rw [ih, this, add_zero]
private theorem trivial_field_values
    (hd : Matrices.ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hb : Tower.SelectedObjects.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    {B : FullSpace.Edge L k j → Matrices.ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (Tower.meshAt L k j)) (c : FullSpace.Edge L k (j + 1))
    (hc : c.IsPositivelyOriented) :
    meanRadius (L := L) (k := k) (j := j) (fun _ => (1 : Matrices.ComplexMatrix2)) c = 1 ∧
      normalizedMean (L := L) (k := k) (j := j) (fun _ => (1 : Matrices.ComplexMatrix2)) c = 1 ∧
      Tower.logDirectionalDeriv ℂ (fun X => normalizedMean (L := L) (k := k) (j := j)
          (FullSpace.expTwist X fun _ => (1 : Matrices.ComplexMatrix2)) c)
        (normalizedMean (L := L) (k := k) (j := j) (fun _ => (1 : Matrices.ComplexMatrix2)) c) B =
        FullSpace.linearSmoothing (a := Tower.meshAt L k (j + 1)) L B c := by
  have hform : ∀ b, B b.opposite = -B b := hB.2
  have hfl : ∀ t : ℂ, FullSpace.expTwist (t • B) (fun _ => (1 : Matrices.ComplexMatrix2)) =
      expFlow B t :=
    expTwist_smul_one B hform
  have hblocks := (hb L hL).2 k (j + 1) (by omega) hj
  have hfin : (FullSpace.cubeVertices L (Tower.meshAt L k j) c.initial).Finite :=
    hblocks.cubeVertices_finite c.initial
  have hcard : (FullSpace.cubeVertices L (Tower.meshAt L k j) c.initial).ncard = L ^ 4 :=
    hblocks.cubeVertices_ncard c.initial
  have hLpos : 0 < L := by have := hL.2; omega
  set S := hfin.toFinset with hSdef
  have hScard : S.card = L ^ 4 := by
    have h1 : S.card = (FullSpace.cubeVertices L (Tower.meshAt L k j) c.initial).ncard :=
      (Set.ncard_eq_toFinset_card _ hfin).symm
    rw [h1, hcard]
  set w : ℂ := (1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L with hw
  have hmean : ∀ V : FullSpace.Edge L k j → Matrices.ComplexMatrix2, contourMean V c =
      w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), contourHolonomy V c x π := by
    intro V
    rw [contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin]
  let leg : FullSpace.Vertex L k j → Equiv.Perm (Fin 4) → List (FullSpace.Edge L k j) :=
    fun x π => contourLeg c.initial x π
  let leg' : FullSpace.Vertex L k j → Equiv.Perm (Fin 4) → List (FullSpace.Edge L k j) :=
    fun x π => contourLeg c.terminal (FullSpace.shifted c x) π
  have hone : ∀ Γ : List (FullSpace.Edge L k j), FullSpace.linkHolonomy (expFlow B 0) Γ = 1 :=
    fun Γ => by rw [expFlow_zero, linkHolonomy_one]
  have hcv : ∀ x π, HasDerivAt (fun t => contourHolonomy (expFlow B t) c x π)
      (Complex.I • (FullSpace.sumAlong B (leg x π) + FullSpace.sumAlong B (FullSpace.crossingPath c x) -
        FullSpace.sumAlong B (leg' x π))) 0 := by
    intro x π
    have hX := hasDerivAt_linkHolonomy B (leg x π)
    have hY := hasDerivAt_linkHolonomy B (FullSpace.crossingPath c x)
    have hZ0 := hasDerivAt_linkHolonomy B (leg' x π)
    have hZ := (((hd.2 Set.univ _ _ _ _ _ _ Filter.univ_mem hZ0 hZ0 hZ0).2.1 (hone _)).2.1)
    have h3 := (hd.2 Set.univ _ _ _ _ _ _ Filter.univ_mem hX hY hZ).1
    refine HasDerivAt.congr_deriv h3 ?_
    simp only [hone, matrix_one_inv, mul_one, one_mul, smul_add, smul_sub, smul_neg]
    abel
  have hW : HasDerivAt (fun t => contourMean (expFlow B t) c)
      (w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4),
        Complex.I • (FullSpace.sumAlong B (leg x π) + FullSpace.sumAlong B (FullSpace.crossingPath c x) -
          FullSpace.sumAlong B (leg' x π))) 0 := by
    have h1 := (HasDerivAt.fun_sum (u := S) fun x _ =>
      HasDerivAt.fun_sum (u := Finset.univ) fun π _ => hcv x π).const_smul w
    have e : (fun t => contourMean (expFlow B t) c) = fun t => w • ∑ x ∈ S,
        ∑ π : Equiv.Perm (Fin 4), contourHolonomy (expFlow B t) c x π := by
      funext t
      exact hmean _
    rw [e]
    exact h1
  have hQ : ∀ x, ∑ π : Equiv.Perm (Fin 4), (FullSpace.sumAlong B (leg x π) +
        FullSpace.sumAlong B (FullSpace.crossingPath c x) - FullSpace.sumAlong B (leg' x π)) =
      (24 : ℂ) • (FullSpace.contourAverage L B c.initial x +
        FullSpace.sumAlong B (FullSpace.crossingPath c x) -
        FullSpace.contourAverage L B c.terminal (FullSpace.shifted c x)) := by
    intro x
    have h1 := sum_permList_sumAlong (L := L) B c.initial x
    have h2 := sum_permList_sumAlong (L := L) B c.terminal (FullSpace.shifted c x)
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, smul_sub, smul_add]
    simp only [leg, leg', contourLeg]
    rw [h1, h2]
    congr 2
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm]
    simp only [Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    norm_num [Nat.factorial]
  have hD : (w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4),
        Complex.I • (FullSpace.sumAlong B (leg x π) + FullSpace.sumAlong B (FullSpace.crossingPath c x) -
          FullSpace.sumAlong B (leg' x π))) =
      Complex.I • FullSpace.linearSmoothing (a := Tower.meshAt L k (j + 1)) L B c := by
    have e1 : FullSpace.linearSmoothing (a := Tower.meshAt L k (j + 1)) L B c =
        PeriodicLattice.inverseFourthPowerWeight L •
        ∑ x ∈ S, (FullSpace.contourAverage L B c.initial x +
          FullSpace.sumAlong B (FullSpace.crossingPath c x) -
          FullSpace.contourAverage L B c.terminal (FullSpace.shifted c x)) := by
      change PeriodicLattice.inverseFourthPowerWeight L •
        ∑ᶠ x ∈ FullSpace.cubeVertices L (Tower.meshAt L k j) c.initial, _ = _
      rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    rw [e1]
    simp only [← Finset.smul_sum, hQ]
    simp only [smul_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    rw [hw]
    ring
  have hW' : HasDerivAt (fun t => contourMean (expFlow B t) c)
      (Complex.I • FullSpace.linearSmoothing (a := Tower.meshAt L k (j + 1)) L B c) 0 := hD ▸ hW
  have hval : contourMean (fun _ : FullSpace.Edge L k j => (1 : Matrices.ComplexMatrix2)) c = 1 := by
    rw [hmean]
    have e : ∀ x π, contourHolonomy
        (fun _ : FullSpace.Edge L k j => (1 : Matrices.ComplexMatrix2)) c x π = 1 := by
      intro x π
      simp only [contourHolonomy, linkHolonomy_one, matrix_one_inv, mul_one]
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
  have htr : Matrices.ComplexMatrix2.fullTrace
      (Complex.I • FullSpace.linearSmoothing (a := Tower.meshAt L k (j + 1)) L B c) = 0 := by
    rw [← hD]
    simp only [Matrices.ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_sum,
      Matrix.trace_add, Matrix.trace_sub]
    have h1 := fullTrace_sumAlong hB
    simp only [Matrices.ComplexMatrix2.fullTrace] at h1
    simp [h1]
  have hu := hasDerivAt_detNormalize hW' hW1 htr
  have hlen1 : meanRadius (fun _ : FullSpace.Edge L k j => (1 : Matrices.ComplexMatrix2)) c = 1 := by
    rw [meanRadius, hval]
    simp
  have hav1 : normalizedMean
      (fun _ : FullSpace.Edge L k j => (1 : Matrices.ComplexMatrix2)) c = 1 := by
    rw [normalizedMean, hlen1, hval]
    simp
  refine ⟨hlen1, hav1, ?_⟩
  have hu0 : (Matrix.det (contourMean (expFlow B 0) c) ^ (1 / 2 : ℂ))⁻¹ •
      contourMean (expFlow B 0) c = 1 := by
    rw [hW1]
    simp
  have hlog := ((hd.2 Set.univ _ _ _ _ _ _ Filter.univ_mem hu hu hu).2.1 hu0).2.2.1
  have e2 : (fun t : ℂ => Matrices.ComplexMatrix2.logSeries (normalizedMean (FullSpace.expTwist (t • B)
        fun _ => (1 : Matrices.ComplexMatrix2)) c *
          (normalizedMean (fun _ : FullSpace.Edge L k j => (1 : Matrices.ComplexMatrix2)) c)⁻¹)) =
        fun t => Matrices.ComplexMatrix2.logSeries
          ((Matrix.det (contourMean (expFlow B t) c) ^ (1 / 2 : ℂ))⁻¹ •
            contourMean (expFlow B t) c) := by
    funext t
    rw [hav1, matrix_one_inv, mul_one, hfl t, normalizedMean, meanRadius]
  change Complex.I⁻¹ • deriv (fun t : ℂ => Matrices.ComplexMatrix2.logSeries
      (normalizedMean (FullSpace.expTwist (t • B) fun _ => (1 : Matrices.ComplexMatrix2)) c *
        (normalizedMean (fun _ : FullSpace.Edge L k j => (1 : Matrices.ComplexMatrix2)) c)⁻¹)) 0 = _
  rw [e2, hlog.deriv, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
private theorem xor_opposite {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.xor_isPositivelyOriented_opposite <;> assumption
private theorem xor_opposite_edge (hL : Conventions.IsAdmissibleBlockingFactor L)
    (b : FullSpace.Edge L k j) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
  xor_opposite (meshAt_pos hL k j) b
private theorem extendOddly_opposite (hL : Conventions.IsAdmissibleBlockingFactor L)
    (f : FullSpace.Edge L k j → Matrices.ComplexMatrix2) (b : FullSpace.Edge L k j) :
    FullSpace.extendOddly f b.opposite = -FullSpace.extendOddly f b := by
  classical
  have hrr : b.opposite.opposite = b := rfl
  rcases xor_opposite_edge hL b with ⟨hp, hr⟩ | ⟨hp, hr⟩
  · simp only [FullSpace.extendOddly, if_pos hp, if_neg hr, hrr]
  · simp only [FullSpace.extendOddly, if_neg hr, if_pos hp, neg_neg]
abbrev _root_.YangMills.SharedProofs.p3001 := @extendOddly_opposite
private theorem meanIterate_trivial
    (hd : Matrices.ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hb : Tower.SelectedObjects.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) : ∀ j, j ≤ k →
    meanIterate (L := L) (k := k) (fun _ => 1) j = fun _ => (1 : Matrices.ComplexMatrix2)
  | 0, _ => rfl
  | j + 1, hj => by
    have hjk : j < k := hj
    have ih := meanIterate_trivial hd hb hL j hjk.le
    have hone : ∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
        normalizedMean (L := L) (k := k) (j := j)
          (fun _ => (1 : Matrices.ComplexMatrix2)) c = 1 := fun c hc =>
      (trivial_field_values hd hb hL hjk (FullSpace.complexEdgeForms _).zero_mem c hc).2.1
    funext c
    simp only [meanIterate, ih]
    split_ifs with h
    · exact hone c h
    · have hr : c.opposite.IsPositivelyOriented := by
        rcases xor_opposite_edge hL c with ⟨hp, -⟩ | ⟨hp, -⟩
        · exact absurd hp h
        · exact hp
      rw [hone _ hr, matrix_one_inv]
private theorem meanCovariantStep_opposite (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j < k) (V B : FullSpace.Edge L k j → Matrices.ComplexMatrix2)
    (c : FullSpace.Edge L k (j + 1)) :
    meanCovariantStep V B c.opposite = -meanCovariantStep V B c := by
  simp only [meanCovariantStep, Pi.add_apply, FullSpace.covDiff, extendOddly_opposite hL]
  abel
private theorem covariantSmoothingDeriv_opposite (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j < k) (V B : FullSpace.Edge L k j → Matrices.ComplexMatrix2)
    (c : FullSpace.Edge L k (j + 1)) :
    FullSpace.covariantSmoothingDeriv V B c.opposite = -FullSpace.covariantSmoothingDeriv V B c := by
  simp only [FullSpace.covariantSmoothingDeriv, FullSpace.complexSmoothingDeriv, Pi.add_apply,
    FullSpace.holLeftDifferential, FullSpace.covDiff, extendOddly_opposite hL]
  abel
open Tower.FullSpace.RescaledConditions in
private theorem meanCovariantStep_trivial
    (hd : Matrices.ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hb : Tower.SelectedObjects.Statement)
    (hS : ∀ i < k, TrivialStep L k i) (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    {B : FullSpace.Edge L k j → Matrices.ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (Tower.meshAt L k j)) :
    meanCovariantStep (fun _ : FullSpace.Edge L k j => (1 : Matrices.ComplexMatrix2)) B =
      FullSpace.crossingSmoothing (a := Tower.meshAt L k (j + 1)) L B := by
  obtain ⟨h1, -, h5, -⟩ := hS j hj
  obtain ⟨e1, e2, e3⟩ := h5 B hB
  rw [← e3]
  have hpos : ∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
      meanCovariantStep (fun _ : FullSpace.Edge L k j => (1 : Matrices.ComplexMatrix2)) B c =
        FullSpace.covariantSmoothingDeriv (L := L) (k := k) (j := j) (fun _ => 1) B c := by
    intro c hc
    obtain ⟨-, hav, hlog⟩ := trivial_field_values hd hb hL hj hB c hc
    simp only [meanCovariantStep, FullSpace.covariantSmoothingDeriv, Pi.add_apply, h1]
    have a2 : FullSpace.complexSmoothingDeriv (L := L) (k := k) (j := j) (fun _ => 1) B c =
        FullSpace.linearSmoothing (a := Tower.meshAt L k (j + 1)) L B c := congrFun e1 c
    rw [a2, ← hlog]
    classical
    simp only [FullSpace.covDiff, FullSpace.extendOddly, if_pos hc, hav]
  funext c
  rcases xor_opposite_edge hL c with ⟨hp, -⟩ | ⟨hr, -⟩
  · exact hpos c hp
  · have h1 := hpos c.opposite hr
    rw [meanCovariantStep_opposite hL hj, covariantSmoothingDeriv_opposite hL hj] at h1
    exact neg_injective h1
private theorem crossingSmoothing_mem_of_closed (S : AddSubmonoid Matrices.ComplexMatrix2)
    (hw : ∀ X ∈ S, PeriodicLattice.inverseFourthPowerWeight L • X ∈ S)
    {B : FullSpace.Edge L k j → Matrices.ComplexMatrix2}
    (hB : ∀ b, B b ∈ S) (c : FullSpace.Edge L k (j + 1)) :
    FullSpace.crossingSmoothing (a := Tower.meshAt L k (j + 1)) L B c ∈ S := by
  refine hw _ (finsum_mem_induction (· ∈ S) S.zero_mem (fun _ _ => S.add_mem) fun x _ => ?_)
  refine S.list_sum_mem ?_
  intro X hX
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hX
  exact hB b
abbrev _root_.YangMills.SharedProofs.p19945 := @crossingSmoothing_mem_of_closed
open Tower.FullSpace.RescaledConditions in
private theorem crossingSmoothing_mem
    (hd : Matrices.ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hb : Tower.SelectedObjects.Statement)
    (hS : ∀ i < k, TrivialStep L k i) (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    {B : FullSpace.Edge L k j → Matrices.ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (Tower.meshAt L k j)) :
    FullSpace.crossingSmoothing (a := Tower.meshAt L k (j + 1)) L B ∈
      FullSpace.complexEdgeForms (Tower.meshAt L k (j + 1)) := by
  refine ⟨fun c _ => ?_, fun c => ?_⟩
  · refine crossingSmoothing_mem_of_closed (L := L) (k := k) (j := j)
      Matrices.ComplexMatrix2.traceless.toAddSubgroup.toAddSubmonoid
      (fun X hX => ?_) (fun b => fullTrace_of_mem hB b) c
    exact Matrices.ComplexMatrix2.traceless.smul_mem _ hX
  · rw [← meanCovariantStep_trivial hd hb hS hL hj hB, meanCovariantStep_opposite hL hj]
open Tower.FullSpace.RescaledConditions in
private theorem meanCovariant_trivial
    (hd : Matrices.ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hb : Tower.SelectedObjects.Statement)
    (hS : ∀ i < k, TrivialStep L k i) (hL : Conventions.IsAdmissibleBlockingFactor L) : ∀ j, j ≤ k →
    ∀ B ∈ FullSpace.complexEdgeForms (Tower.meshAt L k 0),
      meanCovariant (L := L) (k := k) (fun _ => 1) j B = FullSpace.crossingSmoothingIter L k j B ∧
        FullSpace.crossingSmoothingIter L k j B ∈ FullSpace.complexEdgeForms (Tower.meshAt L k j)
  | 0, _, B, hB => ⟨rfl, hB⟩
  | j + 1, hj, B, hB => by
    have hjk : j < k := hj
    obtain ⟨e, m⟩ := meanCovariant_trivial hd hb hS hL j hjk.le B hB
    have e2 : FullSpace.crossingSmoothingIter L k (j + 1) B =
        FullSpace.crossingSmoothing (a := Tower.meshAt L k (j + 1)) L
          (FullSpace.crossingSmoothingIter L k j B) := rfl
    rw [e2]
    refine ⟨?_, crossingSmoothing_mem hd hb hS hL hjk m⟩
    show meanCovariantStep (meanIterate (fun _ => 1) j)
      (meanCovariant (fun _ => 1) j B) = _
    rw [meanIterate_trivial hd hb hL j hjk.le, e]
    exact meanCovariantStep_trivial hd hb hS hL hjk m
private theorem vertexSmoothing_mem_traceless
    {l : FullSpace.Vertex L k j → Matrices.ComplexMatrix2}
    (hl : ∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) (y : FullSpace.Vertex L k (j + 1)) :
    FullSpace.vertexSmoothing (a := Tower.meshAt L k (j + 1)) L l y ∈
      Matrices.ComplexMatrix2.traceless :=
  Matrices.ComplexMatrix2.traceless.smul_mem _
    (finsum_mem_induction (· ∈ Matrices.ComplexMatrix2.traceless)
      Matrices.ComplexMatrix2.traceless.zero_mem
      (fun _ _ => Matrices.ComplexMatrix2.traceless.add_mem) fun x _ => hl x)
open Tower.FullSpace.RescaledConditions in
private theorem meanCubeAverage_trivial
    (hd : Matrices.ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hb : Tower.SelectedObjects.Statement)
    (hS : ∀ i < k, TrivialStep L k i) (hL : Conventions.IsAdmissibleBlockingFactor L) : ∀ j, j ≤ k →
    ∀ l ∈ Matrices.GroupLieProduct.tracelessFunctions (FullSpace.Vertex L k 0),
      meanCubeAverage (L := L) (k := k) (fun _ => 1) j l = FullSpace.vertexSmoothingIter L k j l ∧
        FullSpace.vertexSmoothingIter L k j l ∈
          Matrices.GroupLieProduct.tracelessFunctions (FullSpace.Vertex L k j)
  | 0, _, l, hl => ⟨rfl, hl⟩
  | j + 1, hj, l, hl => by
    have hjk : j < k := hj
    obtain ⟨e, m⟩ := meanCubeAverage_trivial hd hb hS hL j hjk.le l hl
    have e2 : FullSpace.vertexSmoothingIter L k (j + 1) l =
        FullSpace.vertexSmoothing (a := Tower.meshAt L k (j + 1)) L
          (FullSpace.vertexSmoothingIter L k j l) := rfl
    rw [e2]
    refine ⟨?_, fun y _ => vertexSmoothing_mem_traceless (fun x => m x (Set.mem_univ x)) y⟩
    obtain ⟨-, -, -, h6⟩ := hS j hjk
    show FullSpace.adjointCubeAverage (meanIterate (fun _ => 1) j)
      (meanCubeAverage (fun _ => 1) j l) = _
    rw [meanIterate_trivial hd hb hL j hjk.le, e]
    exact h6 _ m
end Step
theorem meanMapsAtTrivialField_of
    (hd : Matrices.ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hb : Tower.SelectedObjects.Statement)
    (hS : Tower.FullSpace.RescaledTrivialSteps) :
    MeanMapsAtTrivialField := by
  intro L hL k hk
  have hs := (hS L hL k hk).2
  refine ⟨fun j hj => meanIterate_trivial hd hb hL j hj,
    fun j hj c hc => (trivial_field_values hd hb hL hj (FullSpace.complexEdgeForms _).zero_mem c hc).1,
    fun j hj B hB => meanCovariantStep_trivial hd hb hs hL hj hB,
    fun j hj B hB => (meanCovariant_trivial hd hb hs hL j hj B hB).1,
    fun j hj l hl => (meanCubeAverage_trivial hd hb hs hL j hj l hl).1⟩
end FullLattice.TrivialFieldMaps
theorem meanMapsAtTrivialField_holds
    (hd : Matrices.ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hb : Tower.SelectedObjects.Statement)
    (hS : Tower.FullSpace.RescaledTrivialSteps) :
    MeanMapsAtTrivialField := by apply _root_.YangMills.Construction.RunningCouplingSlope.FullLattice.TrivialFieldMaps.meanMapsAtTrivialField_of <;> assumption
end YangMills.Construction.RunningCouplingSlope
end
