import YangMills.Construction.OneLoopLaw.BondFormsAsSumsOfPlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.FourierExpansion
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.Tempered YangMills.Construction.PeriodicOperators.RiemannSums
open YangMills.Construction.InfiniteLattice (AmbientSpace)
theorem mem_periodLattice_iff {v : AmbientSpace} :
    v ∈ periodLattice ↔ ∃ q : Fin 4 → ℤ, ∀ i, v i = (q i : ℝ) * (2 * Real.pi) :=
  Iff.rfl
def dualPoint (N : ℕ) (j : Fin 4 → ℤ) : dualLattice N :=
  ⟨fun i => (j i : ℝ) * (2 * Real.pi / N), j, fun _ => rfl⟩
def dualClassOf (N : ℕ) (j : Fin 4 → Fin N) : DualClasses N :=
  QuotientAddGroup.mk (dualPoint N fun i => ((j i : ℕ) : ℤ))
theorem dualClass_mk_eq_iff {N : ℕ} (q q' : dualLattice N) :
    (QuotientAddGroup.mk q : DualClasses N) = QuotientAddGroup.mk q' ↔
      ((q' : AmbientSpace) - (q : AmbientSpace)) ∈ periodLattice := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  simp [sub_eq_neg_add]
theorem dualClassOf_bijective {N : ℕ} (hN : 0 < N) : Function.Bijective (dualClassOf N) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  constructor
  · intro j j' hjj
    obtain ⟨q, hq⟩ := mem_periodLattice_iff.1 ((dualClass_mk_eq_iff _ _).1 hjj)
    funext i
    have e1 := hq i
    simp only [dualPoint, Pi.sub_apply] at e1
    have e2 : (((j' i : ℕ) : ℝ) - ((j i : ℕ) : ℝ)) = (q i : ℝ) * N := by
      field_simp at e1
      push_cast at e1
      linarith
    have e3 : (((j' i : ℕ) : ℤ) - ((j i : ℕ) : ℤ)) = q i * N := by exact_mod_cast e2
    have e4 : (((j' i : ℕ) : ℤ) - ((j i : ℕ) : ℤ)) = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd (m := N) ⟨q i, by rw [e3]; ring⟩ ?_
      have := (j i).2
      have := (j' i).2
      exact abs_lt.2 ⟨by omega, by omega⟩
    exact Fin.ext (by omega)
  · intro c
    induction c using QuotientAddGroup.induction_on with
    | H q =>
      obtain ⟨q, m, hm⟩ := q
      have hlt : ∀ i, (m i % N).toNat < N := fun i => by
        have e1 := Int.emod_lt_of_pos (m i) hNz
        have e2 := Int.emod_nonneg (m i) hNz.ne'
        omega
      refine ⟨fun i => ⟨(m i % N).toNat, hlt i⟩, (dualClass_mk_eq_iff _ _).2 ⟨fun i => m i / N, fun i => ?_⟩⟩
      have e1 : (((m i % N).toNat : ℕ) : ℤ) = m i % N :=
        Int.toNat_of_nonneg (Int.emod_nonneg _ hNz.ne')
      have e2 : m i = m i % N + N * (m i / N) := (Int.emod_add_mul_ediv _ _).symm
      have e3 : (m i : ℝ) = ((m i % N : ℤ) : ℝ) + N * ((m i / N : ℤ) : ℝ) := by exact_mod_cast e2
      simp only [dualPoint, Pi.sub_apply, hm i, e1]
      rw [e3]
      field_simp
      ring
theorem exp_I_mul_int_mul_two_pi (k : ℤ) : Complex.exp (Complex.I * ((k : ℂ) * (2 * Real.pi))) = 1 := by
  rw [show Complex.I * ((k : ℂ) * (2 * Real.pi)) = (k : ℂ) * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I k
def intPhase (q : AmbientSpace) (z : Fin 4 → ℤ) : ℂ :=
  Complex.exp (Complex.I * bilinDot (toComplexVec q) (toComplexVec (castVec z)))
theorem intPhase_eq_of_sub_mem {q q' : AmbientSpace} (hq : q' - q ∈ periodLattice) (z : Fin 4 → ℤ) :
    intPhase q' z = intPhase q z := by
  obtain ⟨t, ht⟩ := mem_periodLattice_iff.1 hq
  have e1 : bilinDot (toComplexVec q') (toComplexVec (castVec z)) =
      bilinDot (toComplexVec q) (toComplexVec (castVec z)) +
        ((∑ i, t i * z i : ℤ) : ℂ) * (2 * Real.pi) := by
    simp only [bilinDot, toComplexVec, castVec]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e2 : q' i = q i + (t i : ℝ) * (2 * Real.pi) := by
      have := ht i
      simp only [Pi.sub_apply] at this
      linarith
    rw [e2]
    push_cast
    ring
  unfold intPhase
  rw [e1, mul_add, Complex.exp_add, exp_I_mul_int_mul_two_pi, mul_one]
def circleRoot (N : ℕ) (d : ℤ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * d / N)
theorem sum_circleRoot_pow {N : ℕ} (hN : 0 < N) (d : ℤ) :
    ∑ j : Fin N, circleRoot N d ^ (j : ℕ) = if (N : ℤ) ∣ d then (N : ℂ) else 0 := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Fin.sum_univ_eq_sum_range (fun j => circleRoot N d ^ j) N]
  split_ifs with hd
  · obtain ⟨e, rfl⟩ := hd
    have e1 : circleRoot N ((N : ℤ) * e) = 1 := by
      unfold circleRoot
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (((N : ℤ) * e : ℤ) : ℂ) / N =
          (e : ℂ) * (2 * Real.pi * Complex.I) by push_cast; field_simp]
      exact Complex.exp_int_mul_two_pi_mul_I e
    simp [e1]
  · have e1 : circleRoot N d ≠ 1 := by
      intro e1
      obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 e1
      apply hd
      refine ⟨k, ?_⟩
      have e2 : (d : ℂ) = (N : ℂ) * k := by
        field_simp at hk
        linear_combination hk
      exact_mod_cast e2
    have e2 : circleRoot N d ^ N = 1 := by
      unfold circleRoot
      rw [← Complex.exp_nat_mul,
        show (N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / N) =
          (d : ℂ) * (2 * Real.pi * Complex.I) by field_simp]
      exact Complex.exp_int_mul_two_pi_mul_I d
    rw [geom_sum_eq e1, e2, sub_self, zero_div]
theorem intPhase_dualPoint {N : ℕ} (hN : 0 < N) (j : Fin 4 → Fin N) (z : Fin 4 → ℤ) :
    intPhase (dualPoint N fun i => ((j i : ℕ) : ℤ) : dualLattice N) z =
      ∏ i, circleRoot N (z i) ^ (j i : ℕ) := by
  unfold intPhase
  simp only [bilinDot, toComplexVec, castVec, dualPoint, Finset.mul_sum]
  rw [Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold circleRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring
theorem sum_intPhase {N : ℕ} (hN : 0 < N) [Fintype (DualClasses N)]
    (rep : DualClasses N → dualLattice N) (hrep : ∀ c, (QuotientAddGroup.mk (rep c) : DualClasses N) = c)
    (z : Fin 4 → ℤ) :
    ∑ c, intPhase (rep c) z = if ∀ i, (N : ℤ) ∣ z i then (N : ℂ) ^ 4 else 0 := by
  classical
  rw [← (Equiv.ofBijective _ (dualClassOf_bijective hN)).sum_comp]
  have e1 : ∀ j : Fin 4 → Fin N,
      intPhase (rep (Equiv.ofBijective _ (dualClassOf_bijective hN) j)) z =
        ∏ i, circleRoot N (z i) ^ (j i : ℕ) := by
    intro j
    rw [← intPhase_dualPoint hN j z]
    exact intPhase_eq_of_sub_mem ((dualClass_mk_eq_iff _ _).1 (hrep _).symm ) z
  simp only [e1]
  have e2 := (Finset.prod_univ_sum (fun _ : Fin 4 => (Finset.univ : Finset (Fin N)))
    (fun i (j : Fin N) => circleRoot N (z i) ^ (j : ℕ)))
  rw [Fintype.piFinset_univ] at e2
  rw [← e2]
  simp only [sum_circleRoot_pow hN]
  split_ifs with hz
  · rw [Finset.prod_congr rfl fun i _ => if_pos (hz i)]
    simp
  · simp only [not_forall] at hz
    obtain ⟨i, hi⟩ := hz
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
theorem torusSide_eq_natCast (L n : ℕ) : PeriodicLattice.torusSide L n = ((2 * L ^ n : ℕ) : ℝ) := by
  simp [PeriodicLattice.torusSide]
theorem exists_int_of_addCircle_coe_eq {L n : ℕ} {u v : ℝ}
    (huv : (u : AddCircle (PeriodicLattice.torusSide L n)) = (v : AddCircle (PeriodicLattice.torusSide L n))) :
    ∃ k : ℤ, u = v + (k : ℝ) * ((2 * L ^ n : ℕ) : ℝ) := by
  have e1 : ((u - v : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) = 0 := by
    rw [AddCircle.coe_sub, huv, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).1 e1
  refine ⟨k, ?_⟩
  rw [zsmul_eq_mul, torusSide_eq_natCast] at hk
  linarith
theorem addCircle_intCast_eq_iff {L n : ℕ} (u v : ℤ) :
    ((u : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) = ((v : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) ↔
      ((2 * L ^ n : ℕ) : ℤ) ∣ u - v := by
  constructor
  · intro huv
    obtain ⟨k, hk⟩ := exists_int_of_addCircle_coe_eq huv
    refine ⟨k, ?_⟩
    have e1 : (u : ℝ) - v = (((2 * L ^ n : ℕ) : ℤ) * k : ℤ) := by
      push_cast at hk ⊢
      linarith
    exact_mod_cast e1
  · rintro ⟨k, hk⟩
    have e1 : ((u - v : ℤ) : ℝ) = (k : ℝ) * PeriodicLattice.torusSide L n := by
      rw [hk, torusSide_eq_natCast]
      push_cast
      ring
    have e2 : ((u : ℝ) - v : ℝ) = k • PeriodicLattice.torusSide L n := by
      rw [zsmul_eq_mul, ← e1]
      push_cast
      ring
    have e3 : (((u : ℝ) - v : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) = 0 :=
      (AddCircle.coe_eq_zero_iff _).2 ⟨k, e2.symm⟩
    rw [AddCircle.coe_sub] at e3
    exact sub_eq_zero.1 e3
theorem phase_eq_intPhase {L n : ℕ} (hL : 0 < L) {q : AmbientSpace} (hq : q ∈ dualLattice (2 * L ^ n))
    (z : Fin 4 → ℤ) (y : PeriodicLattice.FourTorus L n)
    (hy : ∀ i, y i = (((z i : ℤ) : ℝ) : AddCircle (PeriodicLattice.torusSide L n))) :
    Tempered.phase q y = intPhase q z := by
  have hN : ((2 * L ^ n : ℕ) : ℝ) ≠ 0 := by
    have : 0 < 2 * L ^ n := by positivity
    exact_mod_cast this.ne'
  have key : ∃ w : ℂ, ∀ v : AmbientSpace, (fun i => (v i : AddCircle (PeriodicLattice.torusSide L n))) = y →
      Complex.exp (Complex.I * bilinDot (toComplexVec q) (toComplexVec v)) = w := by
    refine ⟨intPhase q z, fun v hv => ?_⟩
    obtain ⟨m, hm⟩ := hq
    have e1 : ∀ i, ∃ k : ℤ, v i = (z i : ℝ) + (k : ℝ) * ((2 * L ^ n : ℕ) : ℝ) := fun i =>
      exists_int_of_addCircle_coe_eq ((congrFun hv i).trans (hy i))
    choose k hk using e1
    have e2 : bilinDot (toComplexVec q) (toComplexVec v) =
        bilinDot (toComplexVec q) (toComplexVec (castVec z)) +
          ((∑ i, m i * k i : ℤ) : ℂ) * (2 * Real.pi) := by
      simp only [bilinDot, toComplexVec, castVec]
      push_cast
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e3 : q i * v i = q i * (z i : ℝ) + (m i : ℝ) * (k i : ℝ) * (2 * Real.pi) := by
        rw [hk i, hm i]
        field_simp
      have e4 := congrArg (fun r : ℝ => (r : ℂ)) e3
      push_cast at e4
      exact e4
    unfold intPhase
    rw [e2, mul_add, Complex.exp_add, exp_I_mul_int_mul_two_pi, mul_one]
  have e5 := Classical.epsilon_spec key (castVec z) (by
    funext i
    exact (hy i).symm)
  exact e5.symm
theorem meshSize_levelDepth_zero (L : ℕ) : PeriodicLattice.meshSize L (PeriodicLattice.levelDepth 0 0) = 1 := by
  simp [PeriodicLattice.meshSize]
theorem edge_value_eq_sum {L n : ℕ} (hL : 0 < L) [Fintype (DualClasses (2 * L ^ n))] (a : Fin 3)
    (e : EffectiveAction.IntBond) (b : UnitEdge L n)
    (rep : DualClasses (2 * L ^ n) → dualLattice (2 * L ^ n))
    (hrep : ∀ c, (QuotientAddGroup.mk (rep c) : DualClasses (2 * L ^ n)) = c) :
    open Classical in
    (if b = (FunctionalStiffness.positiveImage L n e).1 then Matrices.ComplexMatrix2.pauliFamily a else 0) =
      (((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) • ∑ c : DualClasses (2 * L ^ n),
        Complex.exp (-(Complex.I * bilinDot (toComplexVec (rep c : AmbientSpace))
            (toComplexVec (castVec e.1)))) •
          (if b.target - b.source = PeriodicLattice.unitStep L n _ e.2 then
            Tempered.phase (rep c : AmbientSpace) (b.source : PeriodicLattice.FourTorus L n) •
              Matrices.ComplexMatrix2.pauliFamily a
          else 0) := by
  classical
  have hN : 0 < 2 * L ^ n := by positivity
  by_cases hst : b.target - b.source = PeriodicLattice.unitStep L n _ e.2
  · obtain ⟨z, hz⟩ := b.source.2
    have hz' : ∀ i, (b.source : PeriodicLattice.FourTorus L n) i =
        (((z i : ℤ) : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := fun i => by
      rw [hz i, meshSize_levelDepth_zero, mul_one]
    have hterm : ∀ c, Complex.exp (-(Complex.I * bilinDot (toComplexVec (rep c : AmbientSpace))
            (toComplexVec (castVec e.1)))) •
          (if b.target - b.source = PeriodicLattice.unitStep L n _ e.2 then
            Tempered.phase (rep c : AmbientSpace) (b.source : PeriodicLattice.FourTorus L n) •
              Matrices.ComplexMatrix2.pauliFamily a
          else 0) = intPhase (rep c : AmbientSpace) (z - e.1) • Matrices.ComplexMatrix2.pauliFamily a := by
      intro c
      rw [if_pos hst, phase_eq_intPhase hL (rep c).2 z _ hz', smul_smul]
      congr 1
      unfold intPhase
      rw [← Complex.exp_add]
      congr 1
      simp only [bilinDot, toComplexVec, castVec, Pi.sub_apply, Finset.mul_sum]
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    simp only [hterm]
    rw [← Finset.sum_smul, sum_intPhase hN rep hrep, smul_smul]
    by_cases hd : ∀ i, ((2 * L ^ n : ℕ) : ℤ) ∣ (z - e.1) i
    · have hb : b = (FunctionalStiffness.positiveImage L n e).1 := by
        have hs : b.source = EffectiveAction.projectSite L n 0 0 e.1 := by
          refine Subtype.ext (funext fun i => ?_)
          rw [hz' i]
          simp only [EffectiveAction.projectSite, meshSize_levelDepth_zero, mul_one]
          exact (addCircle_intCast_eq_iff _ _).2 (hd i)
        refine PeriodicLattice.Bond.ext hs ?_
        have e1 : b.target = b.source + PeriodicLattice.unitStep L n _ e.2 := by
          rw [← hst]
          abel
        rw [e1, hs]
        rfl
      rw [if_pos hb, if_pos hd]
      have e1 : (((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) * ((2 * L ^ n : ℕ) : ℂ) ^ 4 = 1 := by
        have e2 : ((2 * L ^ n : ℕ) : ℂ) = ((PeriodicLattice.torusSide L n : ℝ) : ℂ) := by
          rw [torusSide_eq_natCast]
          push_cast
          ring
        have e3 : ((PeriodicLattice.torusSide L n : ℝ) : ℂ) ≠ 0 := by
          rw [← e2]
          exact_mod_cast hN.ne'
        rw [e2]
        push_cast
        field_simp
      rw [e1, one_smul]
    · have hb : ¬ b = (FunctionalStiffness.positiveImage L n e).1 := by
        intro hb
        apply hd
        intro i
        have e1 : b.source = EffectiveAction.projectSite L n 0 0 e.1 := by
          rw [hb]
          rfl
        have e2 := congrFun (congrArg Subtype.val e1) i
        rw [hz' i] at e2
        simp only [EffectiveAction.projectSite, meshSize_levelDepth_zero, mul_one] at e2
        exact (addCircle_intCast_eq_iff _ _).1 e2
      rw [if_neg hb, if_neg hd]
      simp
  · have hb : ¬ b = (FunctionalStiffness.positiveImage L n e).1 := by
      intro hb
      apply hst
      rw [hb]
      change EffectiveAction.projectSite L n 0 0 e.1 + PeriodicLattice.unitStep L n _ e.2 -
        EffectiveAction.projectSite L n 0 0 e.1 = _
      abel
    rw [if_neg hb]
    simp [hst]
theorem bondFormFourierExpansion_holds : BondFormFourierExpansion := by
  intro L n hL _
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hN : 0 < 2 * L ^ n := by positivity
  have hfin : Finite (DualClasses (2 * L ^ n)) :=
    Finite.of_surjective _ (dualClassOf_bijective hN).2
  refine ⟨hfin, fun a e => ?_⟩
  let _ : Fintype (DualClasses (2 * L ^ n)) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  have hrep : ∀ c : DualClasses (2 * L ^ n),
      (QuotientAddGroup.mk (Quotient.out c : dualLattice (2 * L ^ n)) :
        DualClasses (2 * L ^ n)) = c := fun c => Quotient.out_eq c
  funext b
  simp only [FunctionalStiffness.liftedPauliForm, FunctionalStiffness.pauliEdgeForm, Pi.smul_apply,
    Finset.sum_apply, Tempered.fourierModeForm, Tower.extendOddly]
  by_cases hb : b.IsPositivelyOriented
  · simp only [if_pos hb]
    exact edge_value_eq_sum hL0 a e b _ hrep
  · simp only [if_neg hb]
    rw [edge_value_eq_sum hL0 a e b.opposite _ hrep]
    simp only [smul_neg, Finset.sum_neg_distrib]
end YangMills.Construction.OneLoopLaw.FourierExpansion
end
