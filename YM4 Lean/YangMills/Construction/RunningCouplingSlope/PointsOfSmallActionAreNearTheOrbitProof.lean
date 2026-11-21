import YangMills.Construction.RunningCouplingSlope.BranchOfLeastPointsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
open Filter Set
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.GaugeOrbitProximity
open Tower Matrices
section Developing
variable {G : Type*} [Group G]
private abbrev basisVec (μ : Fin 4) : Fin 4 → ℤ := Pi.single μ 1
private theorem exists_running_product (a : ℤ → G) :
    ∃ P : ℤ → G, P 0 = 1 ∧ ∀ n, P (n + 1) = P n * a n := by
  let pos : ℕ → G := fun n => Nat.rec 1 (fun i acc => acc * a i) n
  let neg : ℕ → G := fun n => Nat.rec 1 (fun i acc => acc * (a (-((i : ℤ) + 1)))⁻¹) n
  refine ⟨fun n => match n with
    | Int.ofNat m => pos m
    | Int.negSucc m => neg (m + 1), rfl, ?_⟩
  intro n
  cases n with
  | ofNat m =>
    show pos (m + 1) = pos m * a m
    rfl
  | negSucc m =>
    cases m with
    | zero =>
      show pos 0 = neg 1 * a (-1)
      show (1 : G) = 1 * (a (-((0 : ℤ) + 1)))⁻¹ * a (-1)
      simp
    | succ m =>
      show neg (m + 1) = neg (m + 2) * a (Int.negSucc (m + 1))
      have e : Int.negSucc (m + 1) = -(((m + 1 : ℕ) : ℤ) + 1) := by
        simp [Int.negSucc_eq]
      show neg (m + 1) = neg (m + 1) * (a (-(((m + 1 : ℕ) : ℤ) + 1)))⁻¹ * a (Int.negSucc (m + 1))
      rw [e]
      simp
private theorem exists_developing_partial (v : (Fin 4 → ℤ) → Fin 4 → G)
    (hsq : ∀ z μ ν, μ ≠ ν → v z μ * v (z + basisVec μ) ν = v z ν * v (z + basisVec ν) μ)
    (S : Finset (Fin 4)) :
    ∃ g : (Fin 4 → ℤ) → G, g 0 = 1 ∧ ∀ z, (∀ μ, μ ∉ S → z μ = 0) → ∀ μ ∈ S,
      g (z + basisVec μ) = g z * v z μ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 1, rfl, fun _ _ μ h => absurd h (by simp)⟩
  | insert ν S hν ih =>
    obtain ⟨g, g0, hg⟩ := ih
    choose P hP0 hP1 using fun z : Fin 4 → ℤ =>
      exists_running_product fun n => v (Function.update z ν n) ν
    let T : (Fin 4 → ℤ) → G := fun z => P (Function.update z ν 0) (z ν)
    have hTup : ∀ z, T (z + basisVec ν) = T z * v z ν := by
      intro z
      have e1 : Function.update (z + basisVec ν) ν 0 = Function.update z ν 0 := by
        funext ρ
        by_cases h : ρ = ν
        · subst h; simp
        · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
      have e2 : (z + basisVec ν) ν = z ν + 1 := by simp
      simp only [T]
      rw [e1, e2, hP1]
      congr 2
      funext ρ
      by_cases h : ρ = ν
      · subst h; simp
      · simp [Function.update_of_ne h]
    have hsame : ∀ (z : Fin 4 → ℤ) (μ : Fin 4), μ ≠ ν → ∀ n : ℤ,
        P (Function.update z ν 0) n * v (Function.update z ν n) μ =
          v (Function.update z ν 0) μ * P (Function.update (z + basisVec μ) ν 0) n := by
      intro z μ hμ n
      have e0 : ∀ m : ℤ, Function.update (z + basisVec μ) ν m =
          Function.update z ν m + basisVec μ := by
        intro m
        funext ρ
        by_cases h : ρ = ν
        · subst h
          simp [Pi.single_eq_of_ne (Ne.symm hμ)]
        · simp [Function.update_of_ne h]
      have e3 : ∀ m : ℤ, Function.update z ν (m + 1) = Function.update z ν m + basisVec ν := by
        intro m
        funext ρ
        by_cases h : ρ = ν
        · subst h; simp
        · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
      have estep : ∀ m : ℤ, v (Function.update z ν m) ν * v (Function.update z ν (m + 1)) μ =
          v (Function.update z ν m) μ * v (Function.update (z + basisVec μ) ν m) ν := by
        intro m
        rw [e3, e0]
        exact (hsq _ μ ν hμ).symm
      have hstep : ∀ m : ℤ, (P (Function.update z ν 0) m * v (Function.update z ν m) μ =
          v (Function.update z ν 0) μ * P (Function.update (z + basisVec μ) ν 0) m) ↔
          (P (Function.update z ν 0) (m + 1) * v (Function.update z ν (m + 1)) μ =
            v (Function.update z ν 0) μ * P (Function.update (z + basisVec μ) ν 0) (m + 1)) := by
        intro m
        rw [hP1, hP1]
        simp only [Function.update_idem]
        rw [mul_assoc (P _ m), estep m, ← mul_assoc (P _ m), ← mul_assoc (v _ μ),
          mul_left_inj]
      induction n using Int.induction_on with
      | zero =>
        rw [hP0, hP0, one_mul, mul_one]
      | succ m ih' => exact (hstep _).mp ih'
      | pred m ih' =>
        refine (hstep _).mpr ?_
        simpa using ih'
    refine ⟨fun z => g (Function.update z ν 0) * T z, ?_, ?_⟩
    · have e0 : Function.update (0 : Fin 4 → ℤ) ν 0 = 0 := by simp
      simp only [T, e0, Pi.zero_apply, hP0, g0, mul_one]
    · intro z hz μ hμ
      have hz0 : ∀ ρ, ρ ∉ S → Function.update z ν 0 ρ = 0 := by
        intro ρ hρ
        by_cases h : ρ = ν
        · subst h; simp
        · rw [Function.update_of_ne h]
          exact hz ρ (by simp [h, hρ])
      by_cases h : μ = ν
      · subst h
        have e1 : Function.update (z + basisVec μ) μ 0 = Function.update z μ 0 := by
          funext ρ
          by_cases h : ρ = μ
          · subst h; simp
          · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
        simp only [e1, hTup, mul_assoc]
      · have hμS : μ ∈ S := by simpa [h] using hμ
        have e1 : Function.update (z + basisVec μ) ν 0 = Function.update z ν 0 + basisVec μ := by
          funext ρ
          by_cases h' : ρ = ν
          · subst h'
            simp [Pi.single_eq_of_ne (Ne.symm h)]
          · simp [Function.update_of_ne h']
        have e2 : (z + basisVec μ) ν = z ν := by
          simp [Pi.single_eq_of_ne (Ne.symm h)]
        have e3 := hsame z μ h (z ν)
        rw [Function.update_eq_self] at e3
        simp only [T, e2]
        rw [e1, hg _ hz0 μ hμS, ← e1, mul_assoc, ← e3, mul_assoc]
private theorem exists_developing (v : (Fin 4 → ℤ) → Fin 4 → G)
    (hsq : ∀ z μ ν, μ ≠ ν → v z μ * v (z + basisVec μ) ν = v z ν * v (z + basisVec ν) μ) :
    ∃ g : (Fin 4 → ℤ) → G, g 0 = 1 ∧ ∀ z μ, g (z + basisVec μ) = g z * v z μ := by
  obtain ⟨g, g0, hg⟩ := exists_developing_partial v hsq Finset.univ
  exact ⟨g, g0, fun z μ => hg z (fun ρ h => absurd (Finset.mem_univ ρ) h) μ (Finset.mem_univ μ)⟩
private theorem const_of_step_invariant {α : Type*} (f : (Fin 4 → ℤ) → α)
    (h : ∀ z μ, f (z + basisVec μ) = f z) (z : Fin 4 → ℤ) : f z = f 0 := by apply _root_.YangMills.DeltaSharedProofs.p501362 <;> assumption
end Developing
section Sites
open PeriodicLattice (Site Bond unitStep)
variable {L m : ℕ} {i : ℤ}
private def coordSite (z : Fin 4 → ℤ) : Site L m i := ∑ μ, z μ • unitStep L m i μ
private theorem coordSite_add (z w : Fin 4 → ℤ) :
    (coordSite (z + w) : Site L m i) = coordSite z + coordSite w := by
  simp only [coordSite, Pi.add_apply, add_smul, Finset.sum_add_distrib]
private theorem coordSite_smul_basis (n : ℤ) (μ : Fin 4) :
    (coordSite (n • basisVec μ) : Site L m i) = n • unitStep L m i μ := by
  simp only [coordSite]
  rw [Finset.sum_eq_single μ]
  · simp
  · intro ρ _ h
    simp [Pi.single_eq_of_ne h]
  · intro h
    exact absurd (Finset.mem_univ μ) h
private theorem coordSite_add_basis (z : Fin 4 → ℤ) (μ : Fin 4) :
    (coordSite (z + basisVec μ) : Site L m i) = coordSite z + unitStep L m i μ := by
  rw [coordSite_add]
  have := coordSite_smul_basis (L := L) (m := m) (i := i) 1 μ
  simp only [one_smul] at this
  rw [this]
private theorem coordSite_add_smul_basis (z : Fin 4 → ℤ) (n : ℤ) (μ : Fin 4) :
    (coordSite (z + n • basisVec μ) : Site L m i) = coordSite z + n • unitStep L m i μ := by
  rw [coordSite_add, coordSite_smul_basis]
private structure IsDeveloping (V : PeriodicLattice.Bond L m i → ComplexMatrix2)
    (g : (Fin 4 → ℤ) → ComplexMatrix2) : Prop where
  mem_group : ∀ z, g z ∈ PeriodicLattice.compactGaugeGroup
  forward_eq : ∀ z μ, V (PeriodicLattice.Bond.forwardFrom (coordSite z) μ) = (g z)⁻¹ * g (z + basisVec μ)
private theorem det_eq_one_of_mem {g : ComplexMatrix2} (h : g ∈ PeriodicLattice.compactGaugeGroup) :
    Matrix.det g = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
private theorem isUnit_det_of_mem {g : ComplexMatrix2} (h : g ∈ PeriodicLattice.compactGaugeGroup) :
    IsUnit (Matrix.det g) := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
private theorem inv_mul_mul_inv_mul_cancel {A B C : ComplexMatrix2}
    (hB : B ∈ PeriodicLattice.compactGaugeGroup) :
    (A⁻¹ * B) * (B⁻¹ * C) = A⁻¹ * C := by
  rw [mul_assoc, ← mul_assoc B, Matrix.mul_nonsing_inv _ (isUnit_det_of_mem hB), one_mul]
private theorem pathHolonomy_nil (V : PeriodicLattice.Bond L m i → ComplexMatrix2) :
    PeriodicLattice.pathHolonomy V [] = 1 := rfl
private theorem pathHolonomy_cons (V : PeriodicLattice.Bond L m i → ComplexMatrix2)
    (b : PeriodicLattice.Bond L m i) (Γ : List (PeriodicLattice.Bond L m i)) :
    PeriodicLattice.pathHolonomy V (b :: Γ) = V b * PeriodicLattice.pathHolonomy V Γ := by
  simp [PeriodicLattice.pathHolonomy]
private theorem pathHolonomy_append (V : PeriodicLattice.Bond L m i → ComplexMatrix2)
    (Γ Γ' : List (PeriodicLattice.Bond L m i)) :
    PeriodicLattice.pathHolonomy V (Γ ++ Γ') =
      PeriodicLattice.pathHolonomy V Γ * PeriodicLattice.pathHolonomy V Γ' := by
  simp [PeriodicLattice.pathHolonomy]
variable {V : PeriodicLattice.Bond L m i → ComplexMatrix2} {g : (Fin 4 → ℤ) → ComplexMatrix2}
private theorem developing_inv_mul_self {z : Fin 4 → ℤ} (hg : IsDeveloping V g) :
    (g z)⁻¹ * g z = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_det_of_mem (hg.mem_group z))
private theorem pathHolonomy_forwardFlow (hg : IsDeveloping V g) (μ : Fin 4) (n : ℕ) : ∀ z,
    PeriodicLattice.pathHolonomy V (PeriodicLattice.forwardAxisPath (coordSite z) μ n) =
      (g z)⁻¹ * g (z + (n : ℤ) • basisVec μ) := by
  induction n with
  | zero =>
    intro z
    simp [PeriodicLattice.forwardAxisPath, pathHolonomy_nil, developing_inv_mul_self hg]
  | succ n ih =>
    intro z
    simp only [PeriodicLattice.forwardAxisPath]
    rw [pathHolonomy_cons, ← coordSite_add_basis, ih, hg.forward_eq,
      inv_mul_mul_inv_mul_cancel (hg.mem_group _)]
    congr 2
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    abel
private theorem pathHolonomy_backwardFlow (hV : V ∈ PeriodicLattice.compactGaugeFields L m i)
    (hg : IsDeveloping V g) (μ : Fin 4) (n : ℕ) : ∀ z,
    PeriodicLattice.pathHolonomy V (PeriodicLattice.backwardAxisPath (coordSite z) μ n) =
      (g z)⁻¹ * g (z - (n : ℤ) • basisVec μ) := by
  induction n with
  | zero =>
    intro z
    simp [PeriodicLattice.backwardAxisPath, pathHolonomy_nil, developing_inv_mul_self hg]
  | succ n ih =>
    intro z
    simp only [PeriodicLattice.backwardAxisPath]
    have hb : PeriodicLattice.Bond.backwardFrom (coordSite z : Site L m i) μ =
        (PeriodicLattice.Bond.forwardFrom (coordSite (z - basisVec μ) : Site L m i) μ).opposite := by
      have e : (coordSite z : Site L m i) = coordSite (z - basisVec μ) + unitStep L m i μ := by
        rw [← coordSite_add_basis]
        simp
      refine PeriodicLattice.Bond.ext ?_ ?_
      · simp only [PeriodicLattice.Bond.backwardFrom, PeriodicLattice.Bond.opposite,
          PeriodicLattice.Bond.forwardFrom]
        rw [e]
      · simp only [PeriodicLattice.Bond.backwardFrom, PeriodicLattice.Bond.opposite,
          PeriodicLattice.Bond.forwardFrom]
        rw [e]
        simp
    have hstep : (coordSite z - unitStep L m i μ : Site L m i) = coordSite (z - basisVec μ) := by
      have e : (coordSite z : Site L m i) = coordSite (z - basisVec μ) + unitStep L m i μ := by
        rw [← coordSite_add_basis]
        simp
      rw [e]
      simp
    rw [pathHolonomy_cons, hstep, ih, hb, hV.2 _ (Set.mem_univ _), hg.forward_eq,
      Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem (hg.mem_group _))]
    have e2 : z - basisVec μ + basisVec μ = z := by simp
    rw [e2, inv_mul_mul_inv_mul_cancel (hg.mem_group _)]
    congr 2
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    abel
private theorem pathHolonomy_flowAlong (hV : V ∈ PeriodicLattice.compactGaugeFields L m i)
    (hg : IsDeveloping V g) (μ : Fin 4) (n : ℤ) (z : Fin 4 → ℤ) :
    PeriodicLattice.pathHolonomy V (PeriodicLattice.flowAlong (coordSite z) μ n) =
      (g z)⁻¹ * g (z + n • basisVec μ) := by
  simp only [PeriodicLattice.flowAlong]
  split_ifs with h
  · have e : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg h
    rw [pathHolonomy_forwardFlow hg, e]
  · rw [pathHolonomy_backwardFlow hV hg]
    congr 2
    have e : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
    rw [e]
    simp [sub_eq_add_neg]
private theorem pathHolonomy_stepsThroughAxes (hV : V ∈ PeriodicLattice.compactGaugeFields L m i)
    (hg : IsDeveloping V g) (ν : Fin 4 → ℤ) (l : List (Fin 4)) : ∀ z,
    PeriodicLattice.pathHolonomy V (PeriodicLattice.stepsThroughAxes ν (coordSite z) l) =
      (g z)⁻¹ * g (z + (l.map fun μ => ν μ • basisVec μ).sum) := by
  induction l with
  | nil =>
    intro z
    simp [PeriodicLattice.stepsThroughAxes, pathHolonomy_nil, developing_inv_mul_self hg]
  | cons μ l ih =>
    intro z
    simp only [PeriodicLattice.stepsThroughAxes, List.map_cons, List.sum_cons]
    rw [pathHolonomy_append, pathHolonomy_flowAlong hV hg, ← coordSite_add_smul_basis, ih,
      inv_mul_mul_inv_mul_cancel (hg.mem_group _), add_assoc]
private theorem sum_perm_basis (ν : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    (((List.finRange 4).map π).map fun μ => ν μ • basisVec μ).sum = ν := by
  rw [List.map_map, ← Fin.sum_univ_def (fun ρ => ((fun μ => ν μ • basisVec μ) ∘ π) ρ)]
  have := Equiv.sum_comp π (fun μ => ν μ • basisVec μ)
  simp only [Function.comp_def]
  rw [this]
  funext ρ
  simp [Finset.sum_apply, Pi.single_apply]
end Sites
section Geometry
open PeriodicLattice (Site Bond unitStep levelDepth)
variable {L m : ℕ} {i : ℤ}
private theorem coe_toSublattice (hL : 0 < L) {i i' : ℤ} (h : i ≤ i') (y : Site L m i) :
    ((y.toSublattice i' : Site L m i') : PeriodicLattice.FourTorus L m) = y := by apply _root_.YangMills.SharedProofs.p9023 <;> assumption
private theorem coordSite_eq_iff (lc : PeriodicLattice.SublatticeCoordinates L m i)
    (z z' : Fin 4 → ℤ) :
    (coordSite z : Site L m i) = coordSite z' ↔
      ∀ μ, z μ ≡ z' μ [ZMOD (2 * PeriodicLattice.halfPeriod L m i : ℕ)] := by
  have h := lc.2.2.2.2.1 0 z z'
  simpa only [PeriodicLattice.offsetSite, zero_add, coordSite] using h
private theorem exists_coordSite (lc : PeriodicLattice.SublatticeCoordinates L m i)
    (x : Site L m i) : ∃ z : Fin 4 → ℤ, x = coordSite z := by
  obtain ⟨z, hz⟩ := lc.2.2.2.1 0 x
  refine ⟨z, ?_⟩
  simpa only [PeriodicLattice.offsetSite, zero_add, coordSite] using hz
private theorem zsmul_pointOnAxis (n : ℤ) (μ : Fin 4) (t : ℝ) :
    n • PeriodicLattice.pointOnAxis L m μ t = PeriodicLattice.pointOnAxis L m μ ((n : ℝ) * t) := by apply _root_.YangMills.SharedProofs.p34729 <;> assumption
private theorem coe_coordSite (z : Fin 4 → ℤ) :
    ((coordSite z : Site L m i) : PeriodicLattice.FourTorus L m) =
      ∑ μ, PeriodicLattice.pointOnAxis L m μ ((z μ : ℝ) * PeriodicLattice.meshSize L i) := by
  show (PeriodicLattice.sublattice L m i).subtype (∑ μ, z μ • unitStep L m i μ) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_zsmul]
  exact zsmul_pointOnAxis _ _ _
private theorem blockOffset_unique (lc : PeriodicLattice.SublatticeCoordinates L m i) {i₀ : ℤ}
    (hH : (L : ℤ) < 2 * (PeriodicLattice.halfPeriod L m i : ℕ))
    {y : Site L m i₀} {x : Site L m i} {ν ν' : Fin 4 → ℤ}
    (h : PeriodicLattice.IsBlockOffset y x ν) (h' : PeriodicLattice.IsBlockOffset y x ν') :
    ν = ν' := by
  have e : (coordSite ν : Site L m i) = coordSite ν' := by
    apply Subtype.ext
    rw [coe_coordSite, coe_coordSite, ← h.1, ← h'.1]
  have hc := (coordSite_eq_iff lc ν ν').mp e
  funext μ
  have h1 := h.2 μ
  have h2 := h'.2 μ
  obtain ⟨t, ht⟩ := (Int.modEq_iff_dvd.mp (hc μ))
  have hb : |ν' μ - ν μ| < 2 * (PeriodicLattice.halfPeriod L m i : ℕ) := by
    have := abs_sub (ν' μ) (ν μ)
    omega
  have ht0 : t = 0 := by
    by_contra hne
    have h3 : (2 * (PeriodicLattice.halfPeriod L m i : ℕ) : ℤ) ≤ |ν' μ - ν μ| := by
      rw [ht, abs_mul]
      have h4 : (1 : ℤ) ≤ |t| := Int.one_le_abs hne
      have h5 : (0 : ℤ) ≤ |((2 * PeriodicLattice.halfPeriod L m i : ℕ) : ℤ)| := abs_nonneg _
      have h6 : |((2 * PeriodicLattice.halfPeriod L m i : ℕ) : ℤ)| =
          2 * (PeriodicLattice.halfPeriod L m i : ℕ) := by
        rw [abs_of_nonneg (by positivity)]
        push_cast
        ring
      rw [h6] at h5 ⊢
      nlinarith
    omega
  rw [ht0] at ht
  simp only [mul_zero] at ht
  omega
private theorem axialPath_eq_flowAlong (lc : PeriodicLattice.SublatticeCoordinates L m i)
    (hLpos : 0 < L) (hH : (L : ℤ) < (PeriodicLattice.halfPeriod L m i : ℕ))
    (hH' : (PeriodicLattice.halfPeriod L m i : ℝ) = (L : ℝ) ^ ((m : ℤ) + i))
    (x : Site L m i) (μ : Fin 4) :
    PeriodicLattice.axialPath x (x + (L : ℤ) • unitStep L m i μ) =
      PeriodicLattice.flowAlong x μ (L : ℤ) := by
  have hex : ∃ q : Fin 4 × ℤ, PeriodicLattice.IsAxialDisplacement x
      (x + (L : ℤ) • unitStep L m i μ) q.1 q.2 := by
    refine ⟨(μ, (L : ℤ)), by simp, ?_⟩
    rw [← hH']
    simp only [abs_of_pos (show (0 : ℤ) < (L : ℤ) by exact_mod_cast hLpos)]
    exact_mod_cast hH
  simp only [PeriodicLattice.axialPath]
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  set q := hex.choose
  have e : (coordSite ((L : ℤ) • basisVec μ) : Site L m i) = coordSite (q.2 • basisVec q.1) := by
    rw [coordSite_smul_basis, coordSite_smul_basis, ← h1]
    simp
  have hc := (coordSite_eq_iff lc _ _).mp e
  have hq2 : |q.2| < ((PeriodicLattice.halfPeriod L m i : ℕ) : ℤ) := by
    rw [← hH'] at h2
    exact_mod_cast h2
  have hq1 : q.1 = μ := by
    by_contra hne
    have h3 := hc μ
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
      Pi.single_eq_of_ne (Ne.symm hne), mul_zero] at h3
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp h3
    have hN : (0 : ℤ) < ((2 * PeriodicLattice.halfPeriod L m i : ℕ) : ℤ) := by
      push_cast
      omega
    have : t = -1 ∨ t ≥ 0 ∨ t < -1 := by omega
    push_cast at ht hN
    rcases this with rfl | h4 | h4
    · omega
    · nlinarith
    · nlinarith
  have hq : q.2 = (L : ℤ) := by
    have h3 := hc μ
    rw [hq1] at h3
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h3
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp h3
    have ha := abs_lt.mp hq2
    have : t = 0 := by
      push_cast at ht
      by_contra hne
      have : t ≥ 1 ∨ t ≤ -1 := by omega
      rcases this with h4 | h4 <;> nlinarith [ha.1, ha.2]
    rw [this] at ht
    simp only [mul_zero] at ht
    omega
  rw [show q = (μ, (L : ℤ)) from Prod.ext hq1 hq]
end Geometry
section Step
open PeriodicLattice (unitStep)
variable {L n k j : ℕ}
private theorem toSublattice_coordSite (hL : 0 < L) (z : Fin 4 → ℤ) :
    ((coordSite z : Vertex L n k (j + 1)).toSublattice (PeriodicLattice.levelDepth k j) :
      Vertex L n k j) = coordSite ((L : ℤ) • z) := by
  apply Subtype.ext
  rw [coe_toSublattice hL (by simp only [PeriodicLattice.levelDepth]; push_cast; omega),
    coe_coordSite, coe_coordSite]
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  simp only [PeriodicLattice.meshSize, PeriodicLattice.levelDepth, Pi.smul_apply, smul_eq_mul,
    Int.cast_mul, Int.cast_natCast]
  have e : -(((k : ℤ) - ((j + 1 : ℕ) : ℤ))) = 1 + -((k : ℤ) - (j : ℤ)) := by
    push_cast
    ring
  rw [e, zpow_add₀ hL', zpow_one]
  ring
private theorem exists_blockOffset {i i₁ : ℤ} {m : ℕ} (hL : 0 < L) (h : i₁ = i + ((1 : ℕ) : ℤ))
    (bc : PeriodicLattice.RefinedBlockCoordinates L m i 1) (y : PeriodicLattice.Site L m i)
    (x : PeriodicLattice.Site L m i₁) (hx : x ∈ PeriodicLattice.sitesInBlock i₁ y) :
    ∃ ν, PeriodicLattice.IsBlockOffset y x ν := by
  subst h
  have h1 : (x : PeriodicLattice.FourTorus L m) ∈ PeriodicLattice.refinedBlock 1 y := hx
  rw [(bc y).2.1] at h1
  obtain ⟨p, hp, hpx⟩ := h1
  refine ⟨p, ?_, fun μ => ?_⟩
  · rw [← hpx]
    simp only [PeriodicLattice.refinedOffsetSite, PeriodicLattice.offsetSite]
    have e : ((y.toSublattice (i + ((1 : ℕ) : ℤ)) + ∑ μ, p μ • unitStep L m (i + ((1 : ℕ) : ℤ)) μ :
        PeriodicLattice.Site L m (i + ((1 : ℕ) : ℤ))) : PeriodicLattice.FourTorus L m) =
        (y.toSublattice (i + ((1 : ℕ) : ℤ)) : PeriodicLattice.Site L m (i + ((1 : ℕ) : ℤ))) +
          ((coordSite p : PeriodicLattice.Site L m (i + ((1 : ℕ) : ℤ))) :
            PeriodicLattice.FourTorus L m) := rfl
    rw [e, coe_toSublattice hL (by simp), coe_coordSite]
    abel
  · have := hp μ
    simpa using this
private theorem blockOffset_spec {i i₁ : ℤ} {m : ℕ} {y : PeriodicLattice.Site L m i}
    {x : PeriodicLattice.Site L m i₁} (h : ∃ ν, PeriodicLattice.IsBlockOffset y x ν) :
    PeriodicLattice.IsBlockOffset y x (PeriodicLattice.blockOffset y x) :=
  Classical.epsilon_spec h
private structure CoarseningData (L n k j : ℕ) : Prop where
  side_pos : 0 < L
  coords : PeriodicLattice.SublatticeCoordinates L n (PeriodicLattice.levelDepth k j)
  side_lt : (L : ℤ) < (PeriodicLattice.halfPeriod L n (PeriodicLattice.levelDepth k j) : ℕ)
  half_eq : (PeriodicLattice.halfPeriod L n (PeriodicLattice.levelDepth k j) : ℝ) =
    (L : ℝ) ^ ((n : ℤ) + PeriodicLattice.levelDepth k j)
  blocks : PeriodicLattice.RefinedBlockCoordinates L n (PeriodicLattice.levelDepth k (j + 1)) 1
private theorem contourHolonomy_of_developing (hS : CoarseningData L n k j)
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) {g : (Fin 4 → ℤ) → ComplexMatrix2} (hg : IsDeveloping V g)
    (z : Fin 4 → ℤ) (μ : Fin 4) (x : Vertex L n k j)
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
      (coordSite z : Vertex L n k (j + 1))) (π : Equiv.Perm (Fin 4)) :
    contourHolonomy V (PeriodicLattice.Bond.forwardFrom (coordSite z : Vertex L n k (j + 1)) μ) x π =
      (g ((L : ℤ) • z))⁻¹ * g ((L : ℤ) • (z + basisVec μ)) := by
  have hL := hS.side_pos
  set y : Vertex L n k (j + 1) := coordSite z with hy
  have hi : PeriodicLattice.levelDepth k j =
      PeriodicLattice.levelDepth k (j + 1) + ((1 : ℕ) : ℤ) := by
    simp only [PeriodicLattice.levelDepth]
    push_cast
    ring
  have hex := exists_blockOffset hL hi hS.blocks y x hx
  set ν := PeriodicLattice.blockOffset y x with hν
  have hsp : PeriodicLattice.IsBlockOffset y x ν := blockOffset_spec hex
  have hxz : x = coordSite ((L : ℤ) • z + ν) := by
    apply Subtype.ext
    rw [coordSite_add, ← toSublattice_coordSite hL z]
    show (x : PeriodicLattice.FourTorus L n) =
      ((y.toSublattice (PeriodicLattice.levelDepth k j) : Vertex L n k j) :
        PeriodicLattice.FourTorus L n) +
        ((coordSite ν : Vertex L n k j) : PeriodicLattice.FourTorus L n)
    rw [coe_toSublattice hL (by simp only [PeriodicLattice.levelDepth]; push_cast; omega),
      coe_coordSite ν, ← hsp.1]
    abel
  have hhead : (PeriodicLattice.Bond.forwardFrom y μ).target =
      (coordSite (z + basisVec μ) : Vertex L n k (j + 1)) := by
    rw [coordSite_add_basis]
    rfl
  have hstep : (((PeriodicLattice.Bond.forwardFrom y μ).target -
      (PeriodicLattice.Bond.forwardFrom y μ).source :
      Vertex L n k (j + 1)).toSublattice (PeriodicLattice.levelDepth k j) : Vertex L n k j) =
      (L : ℤ) • unitStep L n (PeriodicLattice.levelDepth k j) μ := by
    have e1 : ((PeriodicLattice.Bond.forwardFrom y μ).target -
        (PeriodicLattice.Bond.forwardFrom y μ).source : Vertex L n k (j + 1)) =
        coordSite (basisVec μ) := by
      have := coordSite_smul_basis (L := L) (m := n) (i := PeriodicLattice.levelDepth k (j + 1)) 1 μ
      simp only [one_smul] at this
      rw [this]
      simp [PeriodicLattice.Bond.forwardFrom]
    rw [e1, toSublattice_coordSite hL, ← coordSite_smul_basis]
  have hx' : PeriodicLattice.shiftAcross (PeriodicLattice.Bond.forwardFrom y μ) x =
      coordSite ((L : ℤ) • (z + basisVec μ) + ν) := by
    simp only [PeriodicLattice.shiftAcross]
    rw [hstep, hxz, ← coordSite_add_smul_basis]
    congr 1
    rw [smul_add]
    abel
  have hhl : ((PeriodicLattice.Bond.forwardFrom y μ).target.toSublattice
      (PeriodicLattice.levelDepth k j) : Vertex L n k j) =
      coordSite ((L : ℤ) • (z + basisVec μ)) := by
    rw [hhead, toSublattice_coordSite hL]
  have hsp' : PeriodicLattice.IsBlockOffset (PeriodicLattice.Bond.forwardFrom y μ).target
      (PeriodicLattice.shiftAcross (PeriodicLattice.Bond.forwardFrom y μ) x) ν := by
    refine ⟨?_, hsp.2⟩
    have e1 : ((PeriodicLattice.Bond.forwardFrom y μ).target : PeriodicLattice.FourTorus L n) =
        ((coordSite ((L : ℤ) • (z + basisVec μ)) : Vertex L n k j) :
          PeriodicLattice.FourTorus L n) := by
      rw [← hhl, coe_toSublattice hL
        (by simp only [PeriodicLattice.levelDepth]; push_cast; omega)]
    rw [e1, hx', coordSite_add, ← coe_coordSite ν]
    show ((coordSite ((L : ℤ) • (z + basisVec μ)) : Vertex L n k j) :
        PeriodicLattice.FourTorus L n) +
      ((coordSite ν : Vertex L n k j) : PeriodicLattice.FourTorus L n) - _ = _
    abel
  have hH2 : (L : ℤ) <
      2 * (PeriodicLattice.halfPeriod L n (PeriodicLattice.levelDepth k j) : ℕ) := by
    have := hS.side_lt
    omega
  have hν' : PeriodicLattice.blockOffset (PeriodicLattice.Bond.forwardFrom y μ).target
      (PeriodicLattice.shiftAcross (PeriodicLattice.Bond.forwardFrom y μ) x) = ν :=
    blockOffset_unique hS.coords hH2 (blockOffset_spec ⟨ν, hsp'⟩) hsp'
  have l1 : PeriodicLattice.pathHolonomy V
      (contourLeg (PeriodicLattice.Bond.forwardFrom y μ).source x π) =
      (g ((L : ℤ) • z))⁻¹ * g ((L : ℤ) • z + ν) := by
    show PeriodicLattice.pathHolonomy V (PeriodicLattice.stepsThroughAxes
      (PeriodicLattice.blockOffset y x)
      (y.toSublattice (PeriodicLattice.levelDepth k j)) ((List.finRange 4).map π)) = _
    rw [hy, toSublattice_coordSite hL, ← hy, ← hν, pathHolonomy_stepsThroughAxes hV hg,
      sum_perm_basis]
  have l2 : PeriodicLattice.pathHolonomy V (contourLeg (PeriodicLattice.Bond.forwardFrom y μ).target
      (PeriodicLattice.shiftAcross (PeriodicLattice.Bond.forwardFrom y μ) x) π) =
      (g ((L : ℤ) • (z + basisVec μ)))⁻¹ * g ((L : ℤ) • (z + basisVec μ) + ν) := by
    simp only [contourLeg]
    rw [hν', hhl, pathHolonomy_stepsThroughAxes hV hg, sum_perm_basis]
  have l3 : PeriodicLattice.pathHolonomy V
      (PeriodicLattice.crossingPath (PeriodicLattice.Bond.forwardFrom y μ) x) =
      (g ((L : ℤ) • z + ν))⁻¹ * g ((L : ℤ) • (z + basisVec μ) + ν) := by
    simp only [PeriodicLattice.crossingPath, PeriodicLattice.shiftAcross]
    rw [hstep, axialPath_eq_flowAlong hS.coords hL hS.side_lt hS.half_eq x μ, hxz,
      pathHolonomy_flowAlong hV hg]
    congr 2
    rw [smul_add]
    abel
  simp only [contourHolonomy]
  rw [l1, l3, l2, inv_mul_mul_inv_mul_cancel (hg.mem_group _), Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem (hg.mem_group _)), mul_assoc,
    ← mul_assoc (g _), Matrix.mul_nonsing_inv _ (isUnit_det_of_mem (hg.mem_group _)), one_mul]
end Step
section Average
variable {L n k j : ℕ}
private theorem pathHolonomy_const_one (Γ : List (Edge L n k j)) :
    PeriodicLattice.pathHolonomy (fun _ : Edge L n k j => (1 : ComplexMatrix2)) Γ = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof.pathHolonomy_one <;> assumption
private theorem contourMean_of_developing [Finite (Vertex L n k j)] (hS : CoarseningData L n k j)
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldSpace L n k j)
    {g : (Fin 4 → ℤ) → ComplexMatrix2}
    (hg : IsDeveloping V g) (z : Fin 4 → ℤ) (μ : Fin 4)
    (h1 : contourMean (fun _ : Edge L n k j => (1 : ComplexMatrix2))
      (PeriodicLattice.Bond.forwardFrom (coordSite z : Vertex L n k (j + 1)) μ) = 1) :
    contourMean V (PeriodicLattice.Bond.forwardFrom (coordSite z : Vertex L n k (j + 1)) μ) =
      (g ((L : ℤ) • z))⁻¹ * g ((L : ℤ) • (z + basisVec μ)) := by
  set G := (g ((L : ℤ) • z))⁻¹ * g ((L : ℤ) • (z + basisVec μ)) with hG
  set c := PeriodicLattice.Bond.forwardFrom (coordSite z : Vertex L n k (j + 1)) μ with hc
  have hs : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  have e0 : ∀ (x : Vertex L n k j) (π : Equiv.Perm (Fin 4)),
      contourHolonomy (fun _ : Edge L n k j => (1 : ComplexMatrix2)) c x π = 1 := by
    intro x π
    simp only [contourHolonomy, pathHolonomy_const_one]
    simp
  have e1 : ∀ x ∈ (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)), ∑ π : Equiv.Perm (Fin 4), contourHolonomy V c x π =
      G * ∑ π : Equiv.Perm (Fin 4),
        contourHolonomy (fun _ : Edge L n k j => (1 : ComplexMatrix2)) c x π := by
    intro x hx
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [e0, mul_one]
    exact contourHolonomy_of_developing hS hV hg z μ x hx π
  calc contourMean V c = G * contourMean (fun _ : Edge L n k j => (1 : ComplexMatrix2)) c := by
        simp only [contourMean]
        rw [finsum_mem_congr rfl e1, finsum_mem_eq_finite_toFinset_sum _ hs,
          finsum_mem_eq_finite_toFinset_sum _ hs, ← Finset.mul_sum, mul_smul_comm]
    _ = G := by rw [h1, mul_one]
end Average
section Limits
private theorem traceDefect_of_mem {g : ComplexMatrix2}
    (h : g ∈ PeriodicLattice.compactGaugeGroup) :
    0 ≤ traceDefect g ∧ (traceDefect g = 0 → g = 1) := by apply _root_.YangMills.SharedProofs.p27652 <;> assumption
private theorem inv_mem_compact {A : ComplexMatrix2} (h : A ∈ PeriodicLattice.compactGaugeGroup) :
    A⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
private theorem tendsto_matrix_inv {ι : Type*} {l : Filter ι} {f : ι → ComplexMatrix2}
    {A : ComplexMatrix2} (hf : Tendsto f l (𝓝 A)) (hA : Matrix.det A = 1) :
    Tendsto (fun m => (f m)⁻¹) l (𝓝 A⁻¹) := by apply _root_.YangMills.SharedProofs.p953 <;> assumption
end Limits
section LimitOfFields
variable {L n k j : ℕ}
private theorem tendsto_pathHolonomy {ι : Type*} {l : Filter ι}
    {W : ι → Edge L n k j → ComplexMatrix2}
    {V : Edge L n k j → ComplexMatrix2} (h : ∀ b, Tendsto (fun m => W m b) l (𝓝 (V b)))
    (Γ : List (Edge L n k j)) :
    Tendsto (fun m => PeriodicLattice.pathHolonomy (W m) Γ) l
      (𝓝 (PeriodicLattice.pathHolonomy V Γ)) := by apply _root_.YangMills.SharedProofs.p17103 <;> assumption
private theorem pathHolonomy_mem {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldSpace L n k j)
    (Γ : List (Edge L n k j)) :
    PeriodicLattice.pathHolonomy V Γ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.SharedProofs.p2470 <;> assumption
private theorem tendsto_contourMean [Finite (Vertex L n k j)] {ι : Type*} {l : Filter ι}
    {W : ι → Edge L n k j → ComplexMatrix2} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j)
    (h : ∀ b, Tendsto (fun m => W m b) l (𝓝 (V b))) (c : Edge L n k (j + 1)) :
    Tendsto (fun m => contourMean (W m) c) l (𝓝 (contourMean V c)) := by apply _root_.YangMills.SharedProofs.p67763 <;> assumption
private theorem meanRadius_re_nonneg [Finite (Vertex L n k j)] {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (c : Edge L n k (j + 1)) :
    0 ≤ (meanRadius V c).re := by apply _root_.YangMills.SharedProofs.p43485 <;> assumption
end LimitOfFields
section LimitStep
variable {L n k : ℕ}
private theorem isPositive_or_opposite {j : ℕ} (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem bond_opposite_opposite {j : ℕ} (b : Edge L n k j) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
private theorem levelField_succ_of_pos (X : ChainPoint L n k) {j : ℕ} (hj : j < k)
    (c : Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) :
    levelField X (j + 1) c = X.noise ⟨j, hj⟩ ⟨c, hc⟩ * normalizedMean (levelField X j) c := by apply _root_.YangMills.SharedProofs.p325 <;> assumption
private theorem levelField_succ_of_not_pos (X : ChainPoint L n k) {j : ℕ} (hj : j < k)
    (c : Edge L n k (j + 1)) (hc : ¬c.IsPositivelyOriented)
    (hc' : c.opposite.IsPositivelyOriented) :
    levelField X (j + 1) c =
      (X.noise ⟨j, hj⟩ ⟨c.opposite, hc'⟩ * normalizedMean (levelField X j) c.opposite)⁻¹ := by apply _root_.YangMills.SharedProofs.p3610 <;> assumption
private structure TowerData (L n k : ℕ) : Prop where
  side_pos : 0 < L
  finite_vertex : ∀ j, j ≤ k → Finite (Vertex L n k j)
  finite_positive : ∀ j, j ≤ k → Finite (PositiveEdge L n k j)
  finite_edge : ∀ j, j ≤ k → Finite (Edge L n k j)
  finite_face : Finite (Face L n k 0)
  not_both : ∀ j, j ≤ k → ∀ b : Edge L n k j, b.IsPositivelyOriented →
    ¬ b.opposite.IsPositivelyOriented
  mean_one : ∀ j, j < k → ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    contourMean (fun _ : Edge L n k j => (1 : ComplexMatrix2)) c = 1
  coords : ∀ j, j ≤ k → PeriodicLattice.SublatticeCoordinates L n (PeriodicLattice.levelDepth k j)
  coarsening : ∀ j, j < k → CoarseningData L n k j
private theorem exists_forwardFrom_of_pos {j : ℕ}
    (lc : PeriodicLattice.SublatticeCoordinates L n (PeriodicLattice.levelDepth k j))
    (c : Edge L n k j) (hc : c.IsPositivelyOriented) :
    ∃ (z : Fin 4 → ℤ) (μ : Fin 4),
      c = PeriodicLattice.Bond.forwardFrom (coordSite z : Vertex L n k j) μ := by
  obtain ⟨μ, hμ⟩ := hc
  obtain ⟨z, hz⟩ := exists_coordSite lc c.source
  refine ⟨z, μ, PeriodicLattice.Bond.ext hz ?_⟩
  simp only [PeriodicLattice.Bond.forwardFrom]
  rw [← hz, ← hμ]
  abel
private theorem continuous_traceDefect : Continuous traceDefect := by apply _root_.YangMills.SharedProofs.p10480 <;> assumption
private theorem limit_next_level (hT : TowerData L n k) {X : ℕ → ChainPoint L n k}
    {Y : ChainPoint L n k}
    (hY : ∀ i c, Y.noise i c ∈ PeriodicLattice.compactGaugeGroup)
    (hXn : ∀ m i c, (X m).noise i c ∈ PeriodicLattice.compactGaugeGroup)
    (hn : ∀ i c, Tendsto (fun m => (X m).noise i c) atTop (𝓝 (Y.noise i c)))
    (hsmall : ∀ (i : Fin k) (c : PositiveEdge L n k ((i : ℕ) + 1)), Tendsto (fun m =>
      (meanRadius (levelField (X m) i) c.1).re * traceDefect ((X m).noise i c)) atTop (𝓝 0))
    {j : ℕ} (hj : j < k) {g : (Fin 4 → ℤ) → ComplexMatrix2}
    (hV : levelField Y j ∈ fieldSpace L n k j)
    (hg : IsDeveloping (levelField Y j) g)
    (hW : ∀ b, Tendsto (fun m => levelField (X m) j b) atTop (𝓝 (levelField Y j b))) :
    levelField Y (j + 1) ∈ fieldSpace L n k (j + 1) ∧
      IsDeveloping (levelField Y (j + 1)) (fun z => g ((L : ℤ) • z)) ∧
      (∀ b, Tendsto (fun m => levelField (X m) (j + 1) b) atTop
        (𝓝 (levelField Y (j + 1) b))) ∧
      ∀ c, Y.noise ⟨j, hj⟩ c = 1 := by
  haveI := hT.finite_vertex j hj.le
  have key : ∀ c : Edge L n k (j + 1), ∀ hc : c.IsPositivelyOriented,
      ∃ G ∈ PeriodicLattice.compactGaugeGroup,
      normalizedMean (levelField Y j) c = G ∧ Y.noise ⟨j, hj⟩ ⟨c, hc⟩ = 1 ∧
      Tendsto (fun m => normalizedMean (levelField (X m) j) c) atTop (𝓝 G) ∧
      ∀ z μ, c = PeriodicLattice.Bond.forwardFrom (coordSite z : Vertex L n k (j + 1)) μ →
        G = (g ((L : ℤ) • z))⁻¹ * g ((L : ℤ) • (z + basisVec μ)) := by
    intro c hc
    obtain ⟨z, μ, hcz⟩ := exists_forwardFrom_of_pos (hT.coords (j + 1) hj) c hc
    have hM := contourMean_of_developing (hT.coarsening j hj) hV hg z μ
      (by rw [← hcz]; exact hT.mean_one j hj c hc)
    rw [← hcz] at hM
    set G := (g ((L : ℤ) • z))⁻¹ * g ((L : ℤ) • (z + basisVec μ)) with hG
    have hGr : G ∈ PeriodicLattice.compactGaugeGroup :=
      ComplexMatrix2.specialUnitary.mul_mem (inv_mem_compact (hg.mem_group _)) (hg.mem_group _)
    have hGd : Matrix.det G = 1 := det_eq_one_of_mem hGr
    have hlen : meanRadius (levelField Y j) c = 1 := by
      simp only [meanRadius]
      rw [hM, hGd, Complex.one_cpow]
    have hMt := tendsto_contourMean hV hW c
    rw [hM] at hMt
    have hdet : Tendsto (fun m => Matrix.det (contourMean (levelField (X m) j) c)) atTop
        (𝓝 1) := by
      have h := (Continuous.matrix_det continuous_id).tendsto G
      rw [show Matrix.det (id G) = 1 from hGd] at h
      exact h.comp hMt
    have hrt : Tendsto (fun m => meanRadius (levelField (X m) j) c) atTop (𝓝 1) := by
      have h := (continuousAt_cpow_const (a := (1 : ℂ)) (b := (1 / 2 : ℂ)) (by simp)).tendsto
      rw [Complex.one_cpow] at h
      exact h.comp hdet
    have hut : Tendsto (fun m => normalizedMean (levelField (X m) j) c) atTop (𝓝 G) := by
      have h := (hrt.inv₀ one_ne_zero).smul hMt
      simp only [normalizedMean]
      simpa only [inv_one, one_smul] using h
    have hnoise : Y.noise ⟨j, hj⟩ ⟨c, hc⟩ = 1 := by
      have h1 := hsmall ⟨j, hj⟩ ⟨c, hc⟩
      have h2 := (Complex.continuous_re.tendsto 1).comp hrt
      simp only [Complex.one_re] at h2
      have h3 := (continuous_traceDefect.tendsto _).comp (hn ⟨j, hj⟩ ⟨c, hc⟩)
      have h4 := h2.mul h3
      have h5 := tendsto_nhds_unique h1 h4
      rw [one_mul] at h5
      exact (traceDefect_of_mem (hY _ _)).2 h5.symm
    refine ⟨G, hGr, ?_, hnoise, hut, fun z' μ' h' => ?_⟩
    · simp only [normalizedMean]
      rw [hlen, hM, inv_one, one_smul]
    · have hm := contourMean_of_developing (hT.coarsening j hj) hV hg z' μ'
        (by rw [← h']; exact hT.mean_one j hj c hc)
      rw [← h', hM] at hm
      exact hm
  have hpos : ∀ c : Edge L n k (j + 1), ∀ hc : c.IsPositivelyOriented,
      ∃ G ∈ PeriodicLattice.compactGaugeGroup,
      levelField Y (j + 1) c = G ∧
      Tendsto (fun m => levelField (X m) (j + 1) c) atTop (𝓝 G) := by
    intro c hc
    obtain ⟨G, hG, h1, h2, h3, -⟩ := key c hc
    refine ⟨G, hG, ?_, ?_⟩
    · rw [levelField_succ_of_pos Y hj c hc, h1, h2, one_mul]
    · have e : (fun m => levelField (X m) (j + 1) c) = fun m =>
          (X m).noise ⟨j, hj⟩ ⟨c, hc⟩ * normalizedMean (levelField (X m) j) c := by
        funext m
        exact levelField_succ_of_pos _ hj c hc
      rw [e]
      have h4 := (hn ⟨j, hj⟩ ⟨c, hc⟩).mul h3
      rwa [h2, one_mul] at h4
  have hrev : ∀ (Z : ChainPoint L n k) (c : Edge L n k (j + 1)), ¬c.IsPositivelyOriented →
      levelField Z (j + 1) c = (levelField Z (j + 1) c.opposite)⁻¹ := by
    intro Z c hc
    have hc' := (isPositive_or_opposite c).resolve_left hc
    rw [levelField_succ_of_not_pos Z hj c hc hc', levelField_succ_of_pos Z hj c.opposite hc']
  have hreal : ∀ c : Edge L n k (j + 1),
      levelField Y (j + 1) c ∈ PeriodicLattice.compactGaugeGroup := by
    intro c
    by_cases hc : c.IsPositivelyOriented
    · obtain ⟨G, hG, h1, -⟩ := hpos c hc
      rwa [h1]
    · have hc' := (isPositive_or_opposite c).resolve_left hc
      obtain ⟨G, hG, h1, -⟩ := hpos _ hc'
      rw [hrev Y c hc, h1]
      exact inv_mem_compact hG
  refine ⟨⟨fun b _ => hreal b, fun b _ => ?_⟩, ⟨fun z => ?_, fun z μ => ?_⟩, fun b => ?_,
    fun c => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · have hb' := hT.not_both (j + 1) hj b hb
      rw [hrev Y _ hb', bond_opposite_opposite]
    · have hb' := (isPositive_or_opposite b).resolve_left hb
      rw [hrev Y b hb, Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem (hreal _))]
  · exact hg.mem_group _
  · have hc : (PeriodicLattice.Bond.forwardFrom (coordSite z : Vertex L n k (j + 1)) μ).IsPositivelyOriented :=
      ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
    obtain ⟨G, hG, h1, h2, h3, h4⟩ := key _ hc
    rw [levelField_succ_of_pos Y hj _ hc, h1, h2, one_mul]
    exact h4 z μ rfl
  · by_cases hb : b.IsPositivelyOriented
    · obtain ⟨G, hG, h1, h2⟩ := hpos b hb
      rw [h1]
      exact h2
    · have hb' := (isPositive_or_opposite b).resolve_left hb
      obtain ⟨G, hG, h1, h2⟩ := hpos _ hb'
      rw [hrev Y b hb, h1]
      have e : (fun m => levelField (X m) (j + 1) b) = fun m =>
          (levelField (X m) (j + 1) b.opposite)⁻¹ := by
        funext m
        exact hrev _ b hb
      rw [e]
      exact tendsto_matrix_inv h2 (det_eq_one_of_mem hG)
  · obtain ⟨G, hG, h1, h2, h3, -⟩ := key c.1 c.2
    exact h2
end LimitStep
section ActionBounds
variable {L n k : ℕ}
private theorem plaquetteCost_eq_traceDefect {j : ℤ} (U : PeriodicLattice.Bond L n j → ComplexMatrix2)
    (p : PeriodicLattice.Plaquette L n j) :
    PeriodicLattice.plaquetteCost U p = traceDefect (PeriodicLattice.plaquetteHolonomy U p) := by
  simp only [PeriodicLattice.plaquetteCost, traceDefect, ComplexMatrix2.halfTrace, Complex.mul_re]
  simp
private theorem plaquetteHolonomy_mem {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k 0) (p : Face L n k 0) :
    PeriodicLattice.plaquetteHolonomy U p ∈ PeriodicLattice.compactGaugeGroup :=
  pathHolonomy_mem hU _
private theorem action_parts_le (hT : TowerData L n k) {a : ℝ} (ha : 0 < a) {X : ChainPoint L n k}
    (hX : IsCompactValued X) :
    (∀ p, PeriodicLattice.plaquetteCost X.fine p ≤ chainAction a X) ∧
    ∀ (i : Fin k) (c : PositiveEdge L n k ((i : ℕ) + 1)),
      (meanRadius (levelField X i) c.1).re * traceDefect (X.noise i c) ≤ chainAction a X / a := by
  letI hFq : ∀ i : Fin k, Fintype (PositiveEdge L n k ((i : ℕ) + 1)) := fun i =>
    @Fintype.ofFinite _ (hT.finite_positive _ i.2)
  letI hFp : Fintype (Face L n k 0) := @Fintype.ofFinite _ hT.finite_face
  have hU : X.fine ∈ fieldSpace L n k 0 := hX.2 0 (Nat.zero_le _)
  have hp0 : ∀ p, 0 ≤ PeriodicLattice.plaquetteCost X.fine p := fun p => by
    rw [plaquetteCost_eq_traceDefect]
    exact (traceDefect_of_mem (plaquetteHolonomy_mem hU p)).1
  have ht0 : ∀ (i : Fin k) (c : PositiveEdge L n k ((i : ℕ) + 1)),
      0 ≤ (meanRadius (levelField X i) c.1).re * traceDefect (X.noise i c) := by
    intro i c
    haveI := hT.finite_vertex i i.2.le
    exact mul_nonneg (meanRadius_re_nonneg (hX.2 i i.2.le) _) (traceDefect_of_mem (hX.1 i c)).1
  have eF : chainAction a X = (∑ p : Face L n k 0, PeriodicLattice.plaquetteCost X.fine p) +
      a * ∑ i : Fin k, ∑ c : PositiveEdge L n k ((i : ℕ) + 1),
        (meanRadius (levelField X i) c.1).re * traceDefect (X.noise i c) := by
    simp only [chainAction, plaquetteAction, PeriodicLattice.wilsonAction, finsum_eq_sum_of_fintype]
  have hS : 0 ≤ ∑ i : Fin k, ∑ c : PositiveEdge L n k ((i : ℕ) + 1),
      (meanRadius (levelField X i) c.1).re * traceDefect (X.noise i c) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun c _ => ht0 i c
  have hA : 0 ≤ ∑ p : Face L n k 0, PeriodicLattice.plaquetteCost X.fine p :=
    Finset.sum_nonneg fun p _ => hp0 p
  refine ⟨fun p => ?_, fun i c => ?_⟩
  · have h1 := Finset.single_le_sum (fun p _ => hp0 p) (Finset.mem_univ p)
    rw [eF]
    nlinarith
  · rw [le_div_iff₀ ha, eF]
    have h1 := Finset.single_le_sum (fun c _ => ht0 i c) (Finset.mem_univ c)
    have h2 := Finset.single_le_sum (f := fun i : Fin k =>
      ∑ c : PositiveEdge L n k ((i : ℕ) + 1),
        (meanRadius (levelField X i) c.1).re * traceDefect (X.noise i c))
      (fun i _ => Finset.sum_nonneg fun c _ => ht0 i c) (Finset.mem_univ i)
    nlinarith
end ActionBounds
section TheLimit
variable {L n k : ℕ}
private theorem exists_developing_of_flat {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k 0)
    (hflat : ∀ p : Face L n k 0, PeriodicLattice.plaquetteHolonomy U p = 1) :
    ∃ g : (Fin 4 → ℤ) → ComplexMatrix2, g 0 = 1 ∧ IsDeveloping U g := by
  have hmem : ∀ b, U b ∈ PeriodicLattice.compactGaugeGroup := fun b => hU.1 b (Set.mem_univ b)
  have hsq0 : ∀ (x : Vertex L n k 0) (μ ν : Fin 4), μ < ν →
      U (PeriodicLattice.Bond.forwardFrom x μ) * U (PeriodicLattice.Bond.forwardFrom
        (x + PeriodicLattice.unitStep L n _ μ) ν) =
      U (PeriodicLattice.Bond.forwardFrom x ν) * U (PeriodicLattice.Bond.forwardFrom
        (x + PeriodicLattice.unitStep L n _ ν) μ) := by
    intro x μ ν h
    have hp := hflat ⟨x, μ, ν, h⟩
    simp only [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.Plaquette.boundaryBonds] at hp
    rw [pathHolonomy_cons, pathHolonomy_cons, pathHolonomy_cons, pathHolonomy_cons,
      pathHolonomy_nil, hU.2 _ (Set.mem_univ _), hU.2 _ (Set.mem_univ _), mul_one] at hp
    set A := U (PeriodicLattice.Bond.forwardFrom x μ)
    set B := U (PeriodicLattice.Bond.forwardFrom (x + PeriodicLattice.unitStep L n _ μ) ν)
    set C := U (PeriodicLattice.Bond.forwardFrom (x + PeriodicLattice.unitStep L n _ ν) μ)
    set D := U (PeriodicLattice.Bond.forwardFrom x ν)
    have uC : IsUnit (Matrix.det C) := isUnit_det_of_mem (hmem _)
    have uD : IsUnit (Matrix.det D) := isUnit_det_of_mem (hmem _)
    calc A * B = A * (B * (C⁻¹ * (D⁻¹ * (D * C)))) := by
          rw [← mul_assoc D⁻¹, Matrix.nonsing_inv_mul _ uD, one_mul,
            Matrix.nonsing_inv_mul _ uC, mul_one]
      _ = (A * (B * (C⁻¹ * D⁻¹))) * (D * C) := by simp only [mul_assoc]
      _ = D * C := by rw [hp, one_mul]
  let v : (Fin 4 → ℤ) → Fin 4 → ↥ComplexMatrix2.specialUnitary := fun z μ =>
    ⟨U (PeriodicLattice.Bond.forwardFrom (coordSite z : Vertex L n k 0) μ), hmem _⟩
  have hsq : ∀ z μ ν, μ ≠ ν → v z μ * v (z + basisVec μ) ν = v z ν * v (z + basisVec ν) μ := by
    intro z μ ν hne
    apply Subtype.ext
    show U _ * U _ = U _ * U _
    rw [coordSite_add_basis, coordSite_add_basis]
    rcases lt_or_gt_of_ne hne with h | h
    · exact hsq0 _ _ _ h
    · exact (hsq0 _ _ _ h).symm
  obtain ⟨γ, γ0, hγ⟩ := exists_developing v hsq
  refine ⟨fun z => (γ z : ComplexMatrix2), by simp only [γ0]; rfl,
    ⟨fun z => (γ z).2, fun z μ => ?_⟩⟩
  rw [hγ]
  show _ = ((γ z : ComplexMatrix2))⁻¹ * ((γ z : ComplexMatrix2) * U _)
  rw [← mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_of_mem (γ z).2), one_mul]
private theorem toSublattice_coordSite_top (hL : 0 < L) (z : Fin 4 → ℤ) :
    ((coordSite z : Vertex L n k k).toSublattice (PeriodicLattice.levelDepth k 0) :
      Vertex L n k 0) = coordSite ((L : ℤ) ^ k • z) := by
  apply Subtype.ext
  rw [coe_toSublattice hL (by simp only [PeriodicLattice.levelDepth]; push_cast; omega),
    coe_coordSite, coe_coordSite]
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  simp only [PeriodicLattice.meshSize, PeriodicLattice.levelDepth, Pi.smul_apply, smul_eq_mul,
    Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  simp only [sub_self, neg_zero, zpow_zero, mul_one, Nat.cast_zero, sub_zero]
  rw [zpow_neg, zpow_natCast]
  field_simp
private theorem developing_periodic (hT : TowerData L n k) {U : Edge L n k 0 → ComplexMatrix2}
    {g : (Fin 4 → ℤ) → ComplexMatrix2}
    (hg : IsDeveloping U g) (g0 : g 0 = 1) (hk : ∀ z, g ((L : ℤ) ^ k • z) = 1)
    {z z' : Fin 4 → ℤ} (h : (coordSite z : Vertex L n k 0) = coordSite z') : g z = g z' := by
  have lc := hT.coords 0 (Nat.zero_le _)
  set N : ℕ := 2 * PeriodicLattice.halfPeriod L n (PeriodicLattice.levelDepth k 0) with hN
  have hNk : (N : ℤ) = (L : ℤ) ^ k * (2 * (L : ℤ) ^ n) := by
    simp only [hN, PeriodicLattice.halfPeriod, PeriodicLattice.levelDepth]
    have e : ((n : ℤ) + ((k : ℤ) - ((0 : ℕ) : ℤ))).toNat = n + k := by
      push_cast
      omega
    rw [e]
    push_cast
    ring
  have hsame : ∀ (w : Fin 4 → ℤ) (ν : Fin 4),
      (coordSite (w + (N : ℤ) • basisVec ν) : Vertex L n k 0) = coordSite w := by
    intro w ν
    refine (coordSite_eq_iff lc _ _).mpr fun μ => ?_
    have : (w + (N : ℤ) • basisVec ν) μ = w μ + (N : ℤ) * (basisVec ν) μ := by simp
    rw [this]
    exact Int.modEq_iff_dvd.mpr ⟨-(basisVec ν) μ, by ring⟩
  have hper : ∀ (ν : Fin 4) (w : Fin 4 → ℤ), g (w + (N : ℤ) • basisVec ν) = g w := by
    intro ν
    have hstepf : ∀ (w : Fin 4 → ℤ) (μ : Fin 4),
        g (w + basisVec μ + (N : ℤ) • basisVec ν) * (g (w + basisVec μ))⁻¹ =
          g (w + (N : ℤ) • basisVec ν) * (g w)⁻¹ := by
      intro w μ
      have e1 : w + basisVec μ + (N : ℤ) • basisVec ν =
          (w + (N : ℤ) • basisVec ν) + basisVec μ := by abel
      have h1 := hg.forward_eq w μ
      have h2 := hg.forward_eq (w + (N : ℤ) • basisVec ν) μ
      rw [hsame, h1] at h2
      have h3 : g (w + (N : ℤ) • basisVec ν + basisVec μ) =
          g (w + (N : ℤ) • basisVec ν) * ((g w)⁻¹ * g (w + basisVec μ)) := by
        rw [h2, ← mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_det_of_mem (hg.mem_group _)),
          one_mul]
      rw [e1, h3, mul_assoc, mul_assoc,
        Matrix.mul_nonsing_inv _ (isUnit_det_of_mem (hg.mem_group _)), mul_one]
    have hconst := const_of_step_invariant
      (fun w => g (w + (N : ℤ) • basisVec ν) * (g w)⁻¹) hstepf
    intro w
    have h0 : g ((0 : Fin 4 → ℤ) + (N : ℤ) • basisVec ν) = 1 := by
      have e2 : (0 : Fin 4 → ℤ) + (N : ℤ) • basisVec ν =
          (L : ℤ) ^ k • ((2 * (L : ℤ) ^ n) • basisVec ν) := by
        rw [zero_add, hNk, mul_smul]
      rw [e2]
      exact hk _
    have h1 := hconst w
    simp only [h0, g0, inv_one, mul_one] at h1
    calc g (w + (N : ℤ) • basisVec ν) = g (w + (N : ℤ) • basisVec ν) * ((g w)⁻¹ * g w) := by
          rw [Matrix.nonsing_inv_mul _ (isUnit_det_of_mem (hg.mem_group _)), mul_one]
      _ = g w := by rw [← mul_assoc, h1, one_mul]
  have hline : ∀ (ν : Fin 4) (t : ℤ) (w : Fin 4 → ℤ),
      g (w + t • (N : ℤ) • basisVec ν) = g w := by
    intro ν t w
    induction t using Int.induction_on with
    | zero => simp
    | succ m ih =>
      rw [add_smul, one_smul, ← add_assoc, hper, ih]
    | pred m ih =>
      rw [← ih, ← hper ν (w + (-(m : ℤ) - 1) • (N : ℤ) • basisVec ν), add_assoc,
        ← add_one_zsmul]
      simp
  have hc := (coordSite_eq_iff lc z z').mp h
  have ht : ∀ μ, ∃ t : ℤ, z' μ - z μ = (N : ℤ) * t := fun μ => Int.modEq_iff_dvd.mp (hc μ)
  choose t ht using ht
  have hz : z' = (((z + t 0 • (N : ℤ) • basisVec 0) + t 1 • (N : ℤ) • basisVec 1) +
      t 2 • (N : ℤ) • basisVec 2) + t 3 • (N : ℤ) • basisVec 3 := by
    funext ρ
    have := ht ρ
    fin_cases ρ <;> simp at this ⊢ <;> linarith
  rw [hz, hline, hline, hline, hline]
private theorem subseq_tendsto_gauge_orbit (hT : TowerData L n k) {a : ℝ} (ha : 0 < a)
    {X : ℕ → ChainPoint L n k} (hX : ∀ m, IsCompactValued (X m))
    (hF : Tendsto (fun m => chainAction a (X m)) atTop (𝓝 0))
    (hW : ∀ b, Tendsto (fun m => levelField (X m) k b) atTop (𝓝 1)) :
    ∃ (φ : ℕ → ℕ) (v : Vertex L n k 0 → ComplexMatrix2), StrictMono φ ∧
      (∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) ∧
      (∀ y : Vertex L n k k, restrictVertexFunction k v y = 1) ∧
      (∀ b, Tendsto (fun m => (gaugeTransformPoint v (X (φ m))).fine b) atTop (𝓝 1)) ∧
      ∀ i c, Tendsto (fun m => (gaugeTransformPoint v (X (φ m))).noise i c) atTop (𝓝 1) := by
  have hU : ∀ m, (X m).fine ∈ fieldSpace L n k 0 := fun m => (hX m).2 0 (Nat.zero_le _)
  let x : ℕ → (Edge L n k 0 → ↥ComplexMatrix2.specialUnitary) ×
      ((i : Fin k) → PositiveEdge L n k ((i : ℕ) + 1) → ↥ComplexMatrix2.specialUnitary) :=
    fun m => (fun b => ⟨(X m).fine b, (hU m).1 b (Set.mem_univ b)⟩,
      fun i c => ⟨(X m).noise i c, (hX m).1 i c⟩)
  obtain ⟨A, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq x
  let Y : ChainPoint L n k := ⟨fun b => (A.1 b : ComplexMatrix2), fun i c => (A.2 i c : ComplexMatrix2)⟩
  have hYn : ∀ i c, Y.noise i c ∈ PeriodicLattice.compactGaugeGroup := fun i c => (A.2 i c).2
  have hb : ∀ b, Tendsto (fun m => (X (φ m)).fine b) atTop (𝓝 (Y.fine b)) := by
    intro b
    have h1 := (continuous_fst.tendsto A).comp hlim
    have h2 := tendsto_pi_nhds.mp h1 b
    exact (continuous_subtype_val.tendsto _).comp h2
  have hn : ∀ i c, Tendsto (fun m => (X (φ m)).noise i c) atTop (𝓝 (Y.noise i c)) := by
    intro i c
    have h1 := (continuous_snd.tendsto A).comp hlim
    have h2 := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h1 i) c
    exact (continuous_subtype_val.tendsto _).comp h2
  have hF' : Tendsto (fun m => chainAction a (X (φ m))) atTop (𝓝 0) :=
    hF.comp hφ.tendsto_atTop
  have hYc : Y.fine ∈ fieldSpace L n k 0 := by
    refine ⟨fun b _ => (A.1 b).2, fun b _ => ?_⟩
    have h1 := hb b.opposite
    have h2 := tendsto_matrix_inv (hb b) (det_eq_one_of_mem (A.1 b).2)
    have e : (fun m => (X (φ m)).fine b.opposite) = fun m => ((X (φ m)).fine b)⁻¹ := by
      funext m
      exact (hU (φ m)).2 b (Set.mem_univ b)
    rw [e] at h1
    exact tendsto_nhds_unique h1 h2
  have hflat : ∀ p : Face L n k 0, PeriodicLattice.plaquetteHolonomy Y.fine p = 1 := by
    intro p
    have h1 : Tendsto (fun m => PeriodicLattice.plaquetteCost (X (φ m)).fine p) atTop (𝓝 0) := by
      refine squeeze_zero (fun m => ?_) (fun m => (action_parts_le hT ha (hX (φ m))).1 p) hF'
      rw [plaquetteCost_eq_traceDefect]
      exact (traceDefect_of_mem (plaquetteHolonomy_mem (hU _) p)).1
    have h2 : Tendsto (fun m => PeriodicLattice.plaquetteCost (X (φ m)).fine p) atTop
        (𝓝 (traceDefect (PeriodicLattice.plaquetteHolonomy Y.fine p))) := by
      simp only [plaquetteCost_eq_traceDefect]
      exact (continuous_traceDefect.tendsto _).comp (tendsto_pathHolonomy hb _)
    exact (traceDefect_of_mem (plaquetteHolonomy_mem hYc p)).2 (tendsto_nhds_unique h2 h1)
  obtain ⟨g, g0, hg⟩ := exists_developing_of_flat hYc hflat
  have hsmall : ∀ (i : Fin k) (c : PositiveEdge L n k ((i : ℕ) + 1)), Tendsto (fun m =>
      (meanRadius (levelField (X (φ m)) i) c.1).re * traceDefect ((X (φ m)).noise i c)) atTop
      (𝓝 0) := by
    intro i c
    haveI := hT.finite_vertex i i.2.le
    have h0 : Tendsto (fun m => chainAction a (X (φ m)) / a) atTop (𝓝 0) := by
      simpa using hF'.div_const a
    exact squeeze_zero (fun m => mul_nonneg (meanRadius_re_nonneg ((hX (φ m)).2 i i.2.le) _)
      (traceDefect_of_mem ((hX (φ m)).1 i c)).1)
      (fun m => (action_parts_le hT ha (hX (φ m))).2 i c) h0
  have hlev : ∀ j, j ≤ k → levelField Y j ∈ fieldSpace L n k j ∧
      IsDeveloping (levelField Y j) (fun z => g ((L : ℤ) ^ j • z)) ∧
      (∀ b, Tendsto (fun m => levelField (X (φ m)) j b) atTop (𝓝 (levelField Y j b))) ∧
      ∀ i : Fin k, (i : ℕ) < j → ∀ c, Y.noise i c = 1 := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨hYc, ?_, hb, fun i h => absurd h (Nat.not_lt_zero _)⟩
      have e : (fun z : Fin 4 → ℤ => g ((L : ℤ) ^ 0 • z)) = g := by
        funext z
        simp
      rw [e]
      exact hg
    | succ j ih =>
      intro h
      have hj : j < k := h
      obtain ⟨h1, h2, h3, h4⟩ := ih hj.le
      obtain ⟨s1, s2, s3, s4⟩ :=
        limit_next_level hT hYn (fun m i c => (hX (φ m)).1 i c) hn hsmall hj h1 h2 h3
      refine ⟨s1, ?_, s3, fun i hi c => ?_⟩
      · have e : (fun z : Fin 4 → ℤ => g ((L : ℤ) ^ (j + 1) • z)) =
            fun z => (fun z' => g ((L : ℤ) ^ j • z')) ((L : ℤ) • z) := by
          funext z
          simp only [smul_smul, pow_succ]
        rw [e]
        exact s2
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h5 | h5
        · exact h4 i h5 c
        · have : i = ⟨j, hj⟩ := Fin.ext h5
          subst this
          exact s4 c
  obtain ⟨t1, t2, t3, t4⟩ := hlev k le_rfl
  have htop : levelField Y k = fun _ => 1 := by
    funext b
    exact tendsto_nhds_unique (t3 b) (hW b |>.comp hφ.tendsto_atTop)
  have hgk : ∀ z, g ((L : ℤ) ^ k • z) = 1 := by
    have hc := const_of_step_invariant (fun z => g ((L : ℤ) ^ k • z)) (by
      intro z μ
      have h1 := t2.forward_eq z μ
      rw [htop] at h1
      have h2 := t2.mem_group z
      simp only at h1 h2 ⊢
      calc g ((L : ℤ) ^ k • (z + basisVec μ)) = g ((L : ℤ) ^ k • z) *
            ((g ((L : ℤ) ^ k • z))⁻¹ * g ((L : ℤ) ^ k • (z + basisVec μ))) := by
            rw [← mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_det_of_mem h2), one_mul]
        _ = g ((L : ℤ) ^ k • z) := by rw [← h1, mul_one])
    intro z
    have h1 := hc z
    simp only [smul_zero, g0] at h1
    exact h1
  have lc0 := hT.coords 0 (Nat.zero_le _)
  let coordsOf : Vertex L n k 0 → Fin 4 → ℤ := fun y => (exists_coordSite lc0 y).choose
  have hcoordsOf : ∀ y, (coordSite (coordsOf y) : Vertex L n k 0) = y :=
    fun y => (exists_coordSite lc0 y).choose_spec.symm
  let v : Vertex L n k 0 → ComplexMatrix2 := fun y => g (coordsOf y)
  have hv : ∀ z, v (coordSite z) = g z := fun z => developing_periodic hT hg g0 hgk (hcoordsOf _)
  have hvr : ∀ y, v y ∈ PeriodicLattice.compactGaugeGroup := fun y => hg.mem_group _
  have hres : ∀ y : Vertex L n k k, restrictVertexFunction k v y = 1 := by
    intro y
    obtain ⟨z, rfl⟩ := exists_coordSite (hT.coords k le_rfl) y
    simp only [restrictVertexFunction, PeriodicLattice.restrictGaugeMap]
    rw [toSublattice_coordSite_top hT.side_pos, hv, hgk]
  have hbase : ∀ b, v b.source * Y.fine b * (v b.target)⁻¹ = 1 := by
    have hfw : ∀ z μ, v (coordSite z) *
        Y.fine (PeriodicLattice.Bond.forwardFrom (coordSite z : Vertex L n k 0) μ) *
        (v (coordSite z + PeriodicLattice.unitStep L n _ μ))⁻¹ = 1 := by
      intro z μ
      rw [← coordSite_add_basis, hv, hv, hg.forward_eq, ← mul_assoc,
        Matrix.mul_nonsing_inv _ (isUnit_det_of_mem (hg.mem_group _)),
        one_mul, Matrix.mul_nonsing_inv _ (isUnit_det_of_mem (hg.mem_group _))]
    intro b
    by_cases hbp : b.IsPositivelyOriented
    · obtain ⟨z, μ, rfl⟩ := exists_forwardFrom_of_pos lc0 b hbp
      exact hfw z μ
    · have hbr := (isPositive_or_opposite b).resolve_left hbp
      obtain ⟨z, μ, hz⟩ := exists_forwardFrom_of_pos lc0 b.opposite hbr
      have e1 : b = (PeriodicLattice.Bond.forwardFrom (coordSite z : Vertex L n k 0) μ).opposite := by
        rw [← hz, bond_opposite_opposite]
      have e2 := hfw z μ
      rw [e1, hYc.2 _ (Set.mem_univ _)]
      simp only [PeriodicLattice.Bond.opposite, PeriodicLattice.Bond.forwardFrom]
      simp only [PeriodicLattice.Bond.forwardFrom] at e2
      set P := v (coordSite z)
      set Q := Y.fine ⟨coordSite z, coordSite z + PeriodicLattice.unitStep L n _ μ, μ,
        Or.inl (by abel)⟩
      set R := v (coordSite z + PeriodicLattice.unitStep L n _ μ)
      have uP : IsUnit (Matrix.det P) := isUnit_det_of_mem (hvr _)
      have uR : IsUnit (Matrix.det R) := isUnit_det_of_mem (hvr _)
      have uQ : IsUnit (Matrix.det Q) := isUnit_det_of_mem ((A.1 _).2)
      have e3 : Q = P⁻¹ * R := by
        calc Q = P⁻¹ * (P * Q * R⁻¹) * R := by
              simp only [mul_assoc]
              rw [Matrix.nonsing_inv_mul _ uR, mul_one, ← mul_assoc,
                Matrix.nonsing_inv_mul _ uP, one_mul]
          _ = P⁻¹ * R := by rw [e2, mul_one]
      rw [e3, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ uP, ← mul_assoc,
        Matrix.mul_nonsing_inv _ uR, one_mul, Matrix.mul_nonsing_inv _ uP]
  refine ⟨φ, v, hφ, hvr, hres, fun b => ?_, fun i c => ?_⟩
  · have h1 := ((hb b).const_mul (v b.source)).mul_const ((v b.target)⁻¹)
    rw [hbase b] at h1
    exact h1
  · set w := restrictVertexFunction ((i : ℕ) + 1) v c.1.source with hw
    have hwr : w ∈ PeriodicLattice.compactGaugeGroup := hvr _
    have h1 := ((hn i c).const_mul w).mul_const w⁻¹
    rw [t4 i i.2 c, mul_one, Matrix.mul_nonsing_inv _ (isUnit_det_of_mem hwr)] at h1
    exact h1
end TheLimit
private theorem towerData_of (hd : NormalizedMeanAtOne)
    (hS : Tower.FaceSums.FacesAndPairings) (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hCo : PeriodicLattice.CoordinateDescription)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    TowerData L n k := by
  have hPS := fun (j : ℕ) (hj : j ≤ k) => (hS L hL k j hj).1 n hn
  have finite_vertex : ∀ j, j ≤ k → Finite (Vertex L n k j) := fun j hj =>
    Set.finite_univ_iff.mp ((hPS j hj).2.1 univ).2.1
  have hpos : 0 < L := by have := hL.2; omega
  have hC := hCo L n hL.1 hL.2 hn
  have hdep : ∀ j, j ≤ k → -(n : ℤ) ≤ PeriodicLattice.levelDepth k j := by
    intro j hj
    simp only [PeriodicLattice.levelDepth]
    omega
  refine
    { side_pos := hpos
      finite_vertex := finite_vertex
      finite_positive := fun j hj => Set.finite_univ_iff.mp ((hPS j hj).2.2.1 univ).2.1
      finite_edge := fun j hj => ?_
      finite_face := Set.finite_univ_iff.mp ((hPS 0 (Nat.zero_le _)).2.2.2 univ).2.1
      not_both := fun j hj b hb => ?_
      mean_one := fun j hj c hc =>
        (hd L hL n k j hn hj 0 (edgeFormSpace L n k j).zero_mem c hc).1
      coords := fun j hj => hC.1 _ (hdep j hj)
      coarsening := fun j hj => ?_ }
  · haveI := finite_vertex j hj
    have h : Function.Injective (fun b : Edge L n k j => (b.source, b.target)) := by
      intro b b' hb
      exact PeriodicLattice.Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
    exact Finite.of_injective _ h
  · obtain ⟨μ, hμ⟩ := hb
    rintro ⟨ν, hν⟩
    have hN := (hA L hL n j k hn hj).2.2.2.2.2.1
    have hs : QuotientLattices.IsSignedAxisStep
        (QuotientLattices.torusAxisSteps L n k j)
        (b.source : PeriodicLattice.FourTorus L n) (b.target : PeriodicLattice.FourTorus L n) 1 μ := by
      have h := congrArg Subtype.val hμ
      simpa [QuotientLattices.IsSignedAxisStep, QuotientLattices.torusAxisSteps] using h
    have hs' : QuotientLattices.IsSignedAxisStep
        (QuotientLattices.torusAxisSteps L n k j)
        (b.target : PeriodicLattice.FourTorus L n) (b.source : PeriodicLattice.FourTorus L n) 1 ν := by
      have h := congrArg Subtype.val hν
      simpa [QuotientLattices.IsSignedAxisStep, QuotientLattices.torusAxisSteps,
        PeriodicLattice.Bond.opposite] using h
    have hX := ((hN.2.2 _ b.source.2 _ b.target.2).2 1 μ hs).2
    rcases hX with ⟨-, h⟩ | ⟨-, h⟩
    · exact h ⟨ν, hs'⟩
    · exact h ⟨μ, hs⟩
  · have he : ((n : ℤ) + PeriodicLattice.levelDepth k j).toNat = n + (k - j) := by
      simp only [PeriodicLattice.levelDepth]
      omega
    have hge : 2 ≤ n + (k - j) := by omega
    have hL1 : 1 < L := by have := hL.2; omega
    refine ⟨hpos, hC.1 _ (hdep j hj.le), ?_, ?_, hC.2.2.1 _ 1 (hdep (j + 1) hj)⟩
    · simp only [PeriodicLattice.halfPeriod, he]
      have h1 : L ^ 1 < L ^ (n + (k - j)) := Nat.pow_lt_pow_right hL1 (by omega)
      rw [pow_one] at h1
      exact_mod_cast h1
    · simp only [PeriodicLattice.halfPeriod, he]
      have e2 : (n : ℤ) + PeriodicLattice.levelDepth k j = ((n + (k - j) : ℕ) : ℤ) := by
        simp only [PeriodicLattice.levelDepth]
        omega
      rw [e2, zpow_natCast]
      push_cast
      rfl
theorem smallActionNearGaugeOrbit_holds (hd : NormalizedMeanAtOne)
    (hS : Tower.FaceSums.FacesAndPairings)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hCo : PeriodicLattice.CoordinateDescription) :
    SmallActionNearGaugeOrbit := by
  intro a ha L hL k n _ hn ε hε
  have hT : TowerData L n k := towerData_of hd hS hA hCo hL hn
  by_contra hcon
  push_neg at hcon
  have hpos : ∀ m : ℕ, 0 < 1 / ((m : ℝ) + 1) := fun m => by positivity
  choose X hX hW hF hbad using fun m : ℕ => hcon (1 / ((m : ℝ) + 1)) (hpos m)
  have hlim : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hF0 : Tendsto (fun m => chainAction a (X m)) atTop (𝓝 0) := by
    refine squeeze_zero (fun m => ?_) (fun m => (hF m).le) hlim
    let p : Face L n k 0 := ⟨0, 0, 1, by decide⟩
    have h1 := (action_parts_le hT ha (hX m)).1 p
    rw [plaquetteCost_eq_traceDefect] at h1
    exact (traceDefect_of_mem (plaquetteHolonomy_mem ((hX m).2 0 (Nat.zero_le _)) p)).1.trans h1
  have hW0 : ∀ b, Tendsto (fun m => levelField (X m) k b) atTop (𝓝 1) := by
    intro b
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun m => (hW m b).le) hlim
  obtain ⟨φ, v, hφ, hvr, hres, hb, hn'⟩ := subseq_tendsto_gauge_orbit hT ha hX hF0 hW0
  haveI := hT.finite_edge 0 (Nat.zero_le _)
  have h1 : ∀ᶠ m in atTop, ∀ b,
      ComplexMatrix2.operatorNorm ((gaugeTransformPoint v (X (φ m))).fine b - 1) < ε := by
    refine Filter.eventually_all.mpr fun b => ?_
    have h := (tendsto_iff_norm_sub_tendsto_zero.mp (hb b))
    exact h.eventually_lt_const hε
  have h2 : ∀ᶠ m in atTop, ∀ i c,
      ComplexMatrix2.operatorNorm ((gaugeTransformPoint v (X (φ m))).noise i c - 1) < ε := by
    refine Filter.eventually_all.mpr fun i => ?_
    haveI := hT.finite_positive _ i.2
    refine Filter.eventually_all.mpr fun c => ?_
    have h := (tendsto_iff_norm_sub_tendsto_zero.mp (hn' i c))
    exact h.eventually_lt_const hε
  obtain ⟨m, hm1, hm2⟩ := (h1.and h2).exists
  obtain ⟨i, c, hic⟩ := hbad (φ m) v hvr hres hm1
  exact absurd (hm2 i c) (not_lt.mpr hic)
end YangMills.Construction.RunningCouplingSlope.GaugeOrbitProximity
end
