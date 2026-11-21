import YangMills.Construction.Lattice.EndPointsAndOrientationOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace BondEndpointsOrientation
theorem torusSide_eq_mul_meshSize {L m K k : ℕ} (hL : 0 < L) :
    torusSide L m = sideInLevelUnits L m K k * meshSize L (levelDepth K k) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  unfold torusSide sideInLevelUnits meshSize levelDepth
  rw [mul_assoc, ← zpow_add₀ hL']
  have h : (m : ℤ) + (K : ℤ) - (k : ℤ) + -((K : ℤ) - (k : ℤ)) = (m : ℤ) := by ring
  rw [h, zpow_natCast]
theorem two_mul_le_sideInLevelUnits {L m K k : ℕ} (hL : 0 < L) (hm : 0 < m) (hk : k ≤ K) :
    2 * (L : ℝ) ≤ sideInLevelUnits L m K k := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (m : ℤ) + (K : ℤ) - (k : ℤ) = ((n + 1 : ℕ) : ℤ) :=
    ⟨m + K - k - 1, by omega⟩
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h2 : (L : ℝ) ≤ (L : ℝ) ^ (n + 1) := le_self_pow₀ h1 (by omega)
  unfold sideInLevelUnits
  rw [hn, zpow_natCast]
  linarith
theorem meshSize_ne_zero {L : ℕ} (hL : 0 < L) (j : ℤ) : meshSize L j ≠ 0 := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  exact zpow_ne_zero _ hL'
theorem L_pos (s : Conventions.StandingParameters) : 0 < s.L := by
  have := s.isAdmissible.2
  omega
theorem six_le_two_mul_L (s : Conventions.StandingParameters) : (6 : ℝ) ≤ 2 * (s.L : ℝ) := by
  have h : 13 ≤ s.L := s.isAdmissible.2
  have h' : (13 : ℝ) ≤ s.L := by exact_mod_cast h
  linarith
theorem two_lt_sideInLevelUnits (s : Conventions.StandingParameters) {k : ℕ}
    (hk : k ≤ (s.K : ℕ)) : 2 < sideInLevelUnits s.L s.m s.K k := by
  have h1 := two_mul_le_sideInLevelUnits (K := s.K) (L_pos s) s.m.pos hk
  have h2 := six_le_two_mul_L s
  linarith
theorem coe_mul_meshSize_ne_zero (s : Conventions.StandingParameters) {k : ℕ}
    (hk : k ≤ (s.K : ℕ)) {t : ℝ} (h0 : t ≠ 0) (h2 : |t| ≤ 2) :
    ((t * meshSize s.L (levelDepth s.K k) : ℝ) : AddCircle (torusSide s.L s.m)) ≠ 0 := by
  intro h
  rw [AddCircle.coe_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have ha := meshSize_ne_zero (L_pos s) (levelDepth s.K k)
  have hN := two_lt_sideInLevelUnits s hk
  rw [torusSide_eq_mul_meshSize (K := s.K) (k := k) (L_pos s), zsmul_eq_mul,
    ← mul_assoc] at hn
  have ht : (n : ℝ) * sideInLevelUnits s.L s.m s.K k = t := mul_right_cancel₀ ha hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact h0 (by simpa using ht.symm)
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    exact_mod_cast this
  have hNpos : 0 < sideInLevelUnits s.L s.m s.K k := by linarith
  rw [← ht, abs_mul, abs_of_pos hNpos] at h2
  nlinarith
theorem pointClass_signedStep_self (s : Conventions.StandingParameters) (k : ℕ) (σ : ℝ)
    (μ : Fin 4) :
    s.pointClass (s.signedLatticeStep k σ μ) μ =
      ((σ * meshSize s.L (levelDepth s.K k) : ℝ) : AddCircle (torusSide s.L s.m)) := by
  simp [Conventions.StandingParameters.pointClass,
    Conventions.StandingParameters.signedLatticeStep, coordVec]
theorem pointClass_signedStep_of_ne (s : Conventions.StandingParameters) (k : ℕ) (σ : ℝ)
    {μ ν : Fin 4} (h : ν ≠ μ) : s.pointClass (s.signedLatticeStep k σ μ) ν = 0 := by
  simp [Conventions.StandingParameters.pointClass,
    Conventions.StandingParameters.signedLatticeStep, coordVec, Pi.single_eq_of_ne h]
theorem abs_le_two_of_sign {σ : ℝ} (h : σ = 1 ∨ σ = -1) : |σ| ≤ 2 := by
  rcases h with rfl | rfl <;> norm_num
theorem ne_zero_of_sign {σ : ℝ} (h : σ = 1 ∨ σ = -1) : σ ≠ 0 := by
  rcases h with rfl | rfl <;> norm_num
theorem pointClass_signedStep_ne_zero (s : Conventions.StandingParameters) {k : ℕ}
    (hk : k ≤ (s.K : ℕ)) {σ : ℝ} (μ : Fin 4) (hσ : σ = 1 ∨ σ = -1) :
    s.pointClass (s.signedLatticeStep k σ μ) ≠ s.pointClass 0 := by
  intro h
  have h' := congrFun h μ
  rw [pointClass_signedStep_self] at h'
  exact coe_mul_meshSize_ne_zero s hk (ne_zero_of_sign hσ) (abs_le_two_of_sign hσ)
    (by simpa [Conventions.StandingParameters.pointClass] using h')
theorem sign_axis_eq_of_pointClass_eq (s : Conventions.StandingParameters) {k : ℕ}
    (hk : k ≤ (s.K : ℕ)) {σ σ' : ℝ} {μ μ' : Fin 4}
    (hσ : σ = 1 ∨ σ = -1) (hσ' : σ' = 1 ∨ σ' = -1)
    (h : s.pointClass (s.signedLatticeStep k σ μ) = s.pointClass (s.signedLatticeStep k σ' μ')) :
    σ = σ' ∧ μ = μ' := by
  by_cases hμ : μ = μ'
  · subst hμ
    refine ⟨?_, rfl⟩
    by_contra hne
    have h' := congrFun h μ
    rw [pointClass_signedStep_self, pointClass_signedStep_self] at h'
    refine coe_mul_meshSize_ne_zero s hk (t := σ - σ') (sub_ne_zero.mpr hne) ?_ ?_
    · rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl <;> norm_num
    · rw [sub_mul, AddCircle.coe_sub, h', sub_self]
  · exfalso
    have h' := congrFun h μ
    rw [pointClass_signedStep_self, pointClass_signedStep_of_ne s k σ' hμ] at h'
    exact coe_mul_meshSize_ne_zero s hk (ne_zero_of_sign hσ) (abs_le_two_of_sign hσ) h'
theorem coe_unitStep (s : Conventions.StandingParameters) (k : ℕ) (μ : Fin 4) :
    ((unitStep s.L s.m (levelDepth s.K k) μ : Site s.L s.m (levelDepth s.K k)) : s.Torus) =
      s.pointClass (s.signedLatticeStep k 1 μ) := by
  funext ν
  by_cases h : ν = μ
  · subst h
    rw [pointClass_signedStep_self]
    simp [unitStep, pointOnAxis]
  · rw [pointClass_signedStep_of_ne s k 1 h]
    simp [unitStep, pointOnAxis, Pi.single_eq_of_ne h]
theorem pointClass_signedStep_neg (s : Conventions.StandingParameters) (k : ℕ) (σ : ℝ)
    (μ : Fin 4) :
    s.pointClass (s.signedLatticeStep k (-σ) μ) = -s.pointClass (s.signedLatticeStep k σ μ) := by
  funext ν
  by_cases h : ν = μ
  · subst h
    rw [Pi.neg_apply, pointClass_signedStep_self, pointClass_signedStep_self, neg_mul,
      AddCircle.coe_neg]
  · rw [Pi.neg_apply, pointClass_signedStep_of_ne s k _ h, pointClass_signedStep_of_ne s k _ h,
      neg_zero]
theorem exists_sign_axis (s : Conventions.StandingParameters) {k : ℕ} (c : s.BondAt k) :
    ∃ (σ : ℝ) (μ : Fin 4), s.HasSignAndAxis c σ μ := by
  obtain ⟨μ, h | h⟩ := c.isNeighbour
  · refine ⟨1, μ, Or.inl rfl, ?_⟩
    rw [← coe_unitStep, ← h]
    rfl
  · refine ⟨-1, μ, Or.inr rfl, ?_⟩
    rw [pointClass_signedStep_neg, ← coe_unitStep]
    have h' := congrArg (fun x : Site s.L s.m (levelDepth s.K k) => (x : s.Torus)) h
    exact h'
theorem sign_axis_unique (s : Conventions.StandingParameters) {k : ℕ} (hk : k ≤ (s.K : ℕ))
    {c : s.BondAt k} {σ σ' : ℝ} {μ μ' : Fin 4} (h : s.HasSignAndAxis c σ μ)
    (h' : s.HasSignAndAxis c σ' μ') : σ = σ' ∧ μ = μ' :=
  sign_axis_eq_of_pointClass_eq s hk h.1 h'.1 (h.2.symm.trans h'.2)
theorem hasSignAndAxis_opposite (s : Conventions.StandingParameters) {k : ℕ} {c : s.BondAt k}
    {σ : ℝ} {μ : Fin 4} (h : s.HasSignAndAxis c σ μ) : s.HasSignAndAxis c.opposite (-σ) μ := by
  refine ⟨?_, ?_⟩
  · rcases h.1 with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (by norm_num)
  · show (c.source : s.Torus) - (c.target : s.Torus) = _
    rw [pointClass_signedStep_neg, ← h.2]
    abel
theorem isPositivelyOriented_iff (s : Conventions.StandingParameters) {k : ℕ}
    (hk : k ≤ (s.K : ℕ)) {c : s.BondAt k} {σ : ℝ} {μ : Fin 4} (h : s.HasSignAndAxis c σ μ) :
    c.IsPositivelyOriented ↔ σ = 1 := by
  constructor
  · rintro ⟨ν, hν⟩
    have h1 : (c.target : s.Torus) - (c.source : s.Torus) =
        s.pointClass (s.signedLatticeStep k 1 ν) := by
      rw [← coe_unitStep, ← hν]
      rfl
    exact (sign_axis_eq_of_pointClass_eq s hk h.1 (Or.inl rfl) (h.2.symm.trans h1)).1
  · rintro rfl
    refine ⟨μ, Subtype.ext ?_⟩
    rw [coe_unitStep]
    exact h.2
theorem opposite_isPositivelyOriented_iff (s : Conventions.StandingParameters) {k : ℕ}
    (hk : k ≤ (s.K : ℕ)) {c : s.BondAt k} {σ : ℝ} {μ : Fin 4} (h : s.HasSignAndAxis c σ μ) :
    c.opposite.IsPositivelyOriented ↔ σ = -1 := by
  rw [isPositivelyOriented_iff s hk (hasSignAndAxis_opposite s h), neg_eq_iff_eq_neg]
theorem source_ne_target (s : Conventions.StandingParameters) {k : ℕ} (hk : k ≤ (s.K : ℕ))
    (c : s.BondAt k) : c.source ≠ c.target := by
  intro he
  obtain ⟨σ, μ, h⟩ := exists_sign_axis s c
  refine pointClass_signedStep_ne_zero s hk μ h.1 ?_
  rw [← h.2, he, sub_self]
  funext ν
  simp [Conventions.StandingParameters.pointClass]
end BondEndpointsOrientation
open BondEndpointsOrientation in
theorem BondEndpointsOrientation.holds : BondEndpointsOrientation.Statement := by
  intro s k hk
  refine ⟨⟨torusSide_eq_mul_meshSize (L_pos s),
      two_mul_le_sideInLevelUnits (L_pos s) s.m.pos hk, six_le_two_mul_L s,
      two_lt_sideInLevelUnits s hk⟩,
    fun σ μ hσ => pointClass_signedStep_ne_zero s hk μ hσ,
    fun σ σ' μ μ' hσ hσ' h => sign_axis_eq_of_pointClass_eq s hk hσ hσ' h, fun c => ?_⟩
  refine ⟨?_, source_ne_target s hk c, ?_, ?_, ?_, ?_⟩
  · obtain ⟨σ, μ, h⟩ := exists_sign_axis s c
    exact ⟨(σ, μ), h, fun p hp => by
      obtain ⟨h1, h2⟩ := sign_axis_unique s hk hp h
      exact Prod.ext h1 h2⟩
  · intro he
    exact source_ne_target s hk c (congrArg Bond.source he).symm
  · exact Bond.ext rfl rfl
  · intro σ μ h
    refine ⟨fun σ' μ' => ⟨fun h' => ?_, ?_⟩, isPositivelyOriented_iff s hk h,
      opposite_isPositivelyOriented_iff s hk h⟩
    · obtain ⟨h1, h2⟩ := sign_axis_unique s hk h' (hasSignAndAxis_opposite s h)
      exact ⟨h1, h2⟩
    · rintro ⟨rfl, rfl⟩
      exact hasSignAndAxis_opposite s h
  · obtain ⟨σ, μ, h⟩ := exists_sign_axis s c
    rcases h.1 with h1 | h1
    · refine Or.inl ⟨(isPositivelyOriented_iff s hk h).mpr h1, fun hr => ?_⟩
      have := (opposite_isPositivelyOriented_iff s hk h).mp hr
      rw [h1] at this
      norm_num at this
    · refine Or.inr ⟨(opposite_isPositivelyOriented_iff s hk h).mpr h1, fun hr => ?_⟩
      have := (isPositivelyOriented_iff s hk h).mp hr
      rw [h1] at this
      norm_num at this
end YangMills.Construction.PeriodicLattice
end
