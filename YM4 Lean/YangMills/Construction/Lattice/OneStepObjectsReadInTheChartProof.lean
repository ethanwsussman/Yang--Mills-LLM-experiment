import YangMills.Construction.Lattice.DoubleBlockContours
import YangMills.Construction.Lattice.OneStepObjectsReadInTheChart
import YangMills.Construction.Lattice.SiteCoordinatesProof
import YangMills.Construction.Lattice.StandardPartitionCubeGeometry
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ChartInvariance
section Coordinates
variable {L m : ℕ} {j j' : ℤ}
theorem coe_toSublattice (hL : 0 < L) (y : Site L m j) (h : j ≤ j') :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y :=
  Classical.epsilon_spec (p := fun x : Site L m j' => (x : FourTorus L m) = y)
    ⟨⟨y, sublattice_mono hL m h y.2⟩, rfl⟩
theorem zsmul_pointOnAxis (k : ℤ) (μ : Fin 4) (t : ℝ) :
    k • pointOnAxis L m μ t = pointOnAxis L m μ ((k : ℝ) * t) := by apply _root_.YangMills.SharedProofs.p34729 <;> assumption
theorem coe_zsmul_unitStep (k : ℤ) (μ : Fin 4) :
    ((k • unitStep L m j μ : Site L m j) : FourTorus L m) =
      pointOnAxis L m μ ((k : ℝ) * meshSize L j) :=
  zsmul_pointOnAxis k μ (meshSize L j)
theorem coe_sum_zsmul_unitStep (p : Fin 4 → ℤ) :
    ((∑ μ, p μ • unitStep L m j μ : Site L m j) : FourTorus L m) =
      ∑ μ, pointOnAxis L m μ ((p μ : ℝ) * meshSize L j) := by
  have h := map_sum (sublattice L m j).subtype (fun μ => p μ • unitStep L m j μ) Finset.univ
  simp only [AddSubgroup.subtype_apply, AddSubgroup.coe_zsmul] at h
  rw [h]
  exact Finset.sum_congr rfl fun μ _ => zsmul_pointOnAxis (p μ) μ (meshSize L j)
theorem sum_pointOnAxis_apply (t : Fin 4 → ℝ) (ν : Fin 4) :
    (∑ μ, pointOnAxis L m μ (t μ)) ν = (t ν : AddCircle (torusSide L m)) := by
  rw [Finset.sum_apply]
  simp [pointOnAxis, Pi.single_apply]
theorem torusProj_eq_sum (p : Fin 4 → ℤ) (s : ℝ) :
    TorusMetric.torusProj (torusSide L m) (fun μ => s * (p μ : ℝ)) =
      ∑ μ, pointOnAxis L m μ ((p μ : ℝ) * s) := by
  funext ν
  rw [sum_pointOnAxis_apply]
  simp [TorusMetric.torusProj, mul_comm]
theorem int_eq_zero_of_coe_mul_meshSize (hL : 0 < L) (a : ℤ)
    (h : (((a : ℝ) * meshSize L j' : ℝ) : AddCircle (torusSide L m)) = 0)
    (hb : |(a : ℝ)| < 2 * (L : ℝ) ^ ((m : ℤ) + j')) : a = 0 := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  obtain ⟨q, hq⟩ := (AddCircle.coe_eq_zero_iff _).1 h
  have hP : (0 : ℝ) < (L : ℝ) ^ j' := zpow_pos hL' _
  have hs : meshSize L j' * (L : ℝ) ^ j' = 1 := by
    unfold meshSize
    rw [zpow_neg]
    exact inv_mul_cancel₀ hP.ne'
  have hz : (L : ℝ) ^ ((m : ℤ) + j') = (L : ℝ) ^ m * (L : ℝ) ^ j' := by
    rw [zpow_add₀ hL'.ne', zpow_natCast]
  have ha : (a : ℝ) = (q : ℝ) * (2 * (L : ℝ) ^ ((m : ℤ) + j')) := by
    have h₁ : (q : ℝ) * torusSide L m = (a : ℝ) * meshSize L j' := by
      rw [← hq, zsmul_eq_mul]
    have h₂ := congrArg (· * (L : ℝ) ^ j') h₁
    simp only [mul_assoc, hs, mul_one] at h₂
    rw [← h₂, hz]
    unfold torusSide
    ring
  have hq0 : q = 0 := by
    by_contra hne
    have h₁ : (1 : ℝ) ≤ |(q : ℝ)| := by exact_mod_cast Int.one_le_abs hne
    have hB : (0 : ℝ) < 2 * (L : ℝ) ^ ((m : ℤ) + j') := by positivity
    rw [ha, abs_mul, abs_of_pos hB] at hb
    nlinarith
  rw [hq0] at ha
  exact_mod_cast (by simpa using ha : (a : ℝ) = 0)
theorem coefficients_eq_of_sum_eq (hL : 0 < L) (p q : Fin 4 → ℤ)
    (h : ∑ μ, pointOnAxis L m μ ((p μ : ℝ) * meshSize L j') =
      ∑ μ, pointOnAxis L m μ ((q μ : ℝ) * meshSize L j'))
    (hb : ∀ μ, |((p μ - q μ : ℤ) : ℝ)| < 2 * (L : ℝ) ^ ((m : ℤ) + j')) : p = q := by
  funext μ
  have h₁ := congrFun h μ
  rw [sum_pointOnAxis_apply (fun μ => (p μ : ℝ) * meshSize L j'),
    sum_pointOnAxis_apply (fun μ => (q μ : ℝ) * meshSize L j')] at h₁
  have h₂ : ((((p μ - q μ : ℤ) : ℝ) * meshSize L j' : ℝ) : AddCircle (torusSide L m)) = 0 := by
    push_cast
    rw [sub_mul, AddCircle.coe_sub, h₁, sub_self]
  have := int_eq_zero_of_coe_mul_meshSize hL _ h₂ (hb μ)
  omega
end Coordinates
structure RefinementData (L m : ℕ) (j j' : ℤ) : Prop where
  thirteen_le : 13 ≤ L
  odd : Odd L
  m_pos : 0 < m
  level_nonneg : 0 ≤ j
  succ_eq : j' = j + (1 : ℕ)
  block_eq_grid : ∀ y : Site L m j, refinedBlock 1 y = blockAsGrid 1 y
namespace RefinementData
variable {L m : ℕ} {j j' : ℤ} (D : RefinementData L m j j')
include D
theorem L_pos : 0 < L := by
  have := D.thirteen_le
  omega
theorem level_le : j ≤ j' := by
  rw [D.succ_eq]
  push_cast
  omega
theorem fine_nonneg : 0 ≤ j' := le_trans D.level_nonneg D.level_le
theorem L_lt_zpow : (L : ℝ) < (L : ℝ) ^ ((m : ℤ) + j') := by
  have h13 : (13 : ℝ) ≤ L := by exact_mod_cast D.thirteen_le
  have h₁ : (2 : ℤ) ≤ (m : ℤ) + j' := by
    have := D.succ_eq
    have := D.level_nonneg
    have := D.m_pos
    push_cast at *
    omega
  have h₂ := zpow_le_zpow_right₀ (a := (L : ℝ)) (by linarith) h₁
  have h₃ : (L : ℝ) ^ (2 : ℤ) = (L : ℝ) * L := by
    rw [zpow_ofNat, sq]
  have h₄ : (L : ℝ) * 13 ≤ (L : ℝ) * L := mul_le_mul_of_nonneg_left h13 (by linarith)
  rw [h₃] at h₂
  linarith
theorem abs_lt_of_le {a : ℤ} (h : |a| ≤ (L : ℤ) - 1) :
    |(a : ℝ)| < 2 * (L : ℝ) ^ ((m : ℤ) + j') := by
  have h₂ : |(a : ℝ)| ≤ (L : ℝ) - 1 := by
    calc |(a : ℝ)| = ((|a| : ℤ) : ℝ) := Int.cast_abs.symm
      _ ≤ (((L : ℤ) - 1 : ℤ) : ℝ) := Int.cast_le.mpr h
      _ = (L : ℝ) - 1 := by push_cast; ring
  have := D.L_lt_zpow
  have hL : (0 : ℝ) < L := by exact_mod_cast D.L_pos
  linarith
theorem offset_unique {y : Site L m j} {x : Site L m j'} {N N' : Fin 4 → ℤ}
    (h : IsBlockOffset y x N) (h' : IsBlockOffset y x N') : N = N' := by
  refine coefficients_eq_of_sum_eq D.L_pos N N' (h.1.symm.trans h'.1) fun μ => D.abs_lt_of_le ?_
  have := abs_sub (N μ) (N' μ)
  have := h.2 μ
  have := h'.2 μ
  linarith
theorem eq_add_sum {y : Site L m j} {x : Site L m j'} {N : Fin 4 → ℤ}
    (h : IsBlockOffset y x N) : x = y.toSublattice j' + ∑ μ, N μ • unitStep L m j' μ := by
  apply Subtype.ext
  rw [AddSubgroup.coe_add, coe_toSublattice D.L_pos y D.level_le, coe_sum_zsmul_unitStep]
  exact sub_eq_iff_eq_add'.1 h.1
theorem isBlockOffset_of_eq {y : Site L m j} {x : Site L m j'} {N : Fin 4 → ℤ}
    (hN : ∀ μ, 2 * |N μ| ≤ (L : ℤ) - 1) (h : x = y.toSublattice j' + ∑ μ, N μ • unitStep L m j' μ) :
    IsBlockOffset y x N := by
  refine ⟨?_, hN⟩
  rw [h, AddSubgroup.coe_add, coe_toSublattice D.L_pos y D.level_le, coe_sum_zsmul_unitStep]
  exact add_sub_cancel_left _ _
theorem add_sum_mem_unitBlock (y : Site L m j) (p : Fin 4 → ℤ) (hp : ∀ μ, 2 * |p μ| ≤ (L : ℤ) - 1) :
    ((y.toSublattice j' + ∑ μ, p μ • unitStep L m j' μ : Site L m j') : FourTorus L m) ∈ unitBlock y := by
  show _ ∈ refinedBlock 1 y
  rw [D.block_eq_grid y]
  refine ⟨p, fun μ => ?_, ?_⟩
  · have h : ((2 * |p μ| : ℤ) : ℝ) ≤ (((L : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast hp μ
    push_cast at h
    rw [pow_one]
    linarith
  · rw [AddSubgroup.coe_add, coe_toSublattice D.L_pos y D.level_le, coe_sum_zsmul_unitStep,
      ← D.succ_eq, torusProj_eq_sum]
theorem toSublattice_unitStep (ν : Fin 4) :
    (unitStep L m j ν).toSublattice j' = L • unitStep L m j' ν := by
  apply Subtype.ext
  rw [coe_toSublattice D.L_pos _ D.level_le, ← natCast_zsmul, coe_zsmul_unitStep]
  show pointOnAxis L m ν (meshSize L j) = _
  congr 1
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast D.L_pos.ne'
  unfold meshSize
  rw [D.succ_eq]
  push_cast
  rw [neg_add, zpow_add₀ hL, zpow_neg _ (1 : ℤ), zpow_one]
  field_simp
theorem target_toSublattice (c : Bond L m j) (ν : Fin 4) (hν : c.target - c.source = unitStep L m j ν) :
    c.target.toSublattice j' = c.source.toSublattice j' + L • unitStep L m j' ν := by
  apply Subtype.ext
  have hh : (c.target : FourTorus L m) = c.source + (unitStep L m j ν : Site L m j) := by
    rw [← hν]
    simp
  rw [AddSubgroup.coe_add, coe_toSublattice D.L_pos _ D.level_le, coe_toSublattice D.L_pos _ D.level_le, hh,
    ← D.toSublattice_unitStep ν, coe_toSublattice D.L_pos _ D.level_le]
theorem shiftAcross_eq (c : Bond L m j) (ν : Fin 4) (hν : c.target - c.source = unitStep L m j ν)
    (x : Site L m j') : shiftAcross c x = x + L • unitStep L m j' ν := by
  unfold shiftAcross
  rw [hν, D.toSublattice_unitStep]
theorem axialPath_eq (z : Site L m j') (ν : Fin 4) :
    axialPath z (z + L • unitStep L m j' ν) = forwardAxisPath z ν L := by
  have hL := D.L_pos
  have hN := D.L_lt_zpow
  have hwit : IsAxialDisplacement z (z + L • unitStep L m j' ν) ν (L : ℤ) :=
    ⟨by simp, by simpa using hN⟩
  have hex : ∃ q : Fin 4 × ℤ, IsAxialDisplacement z (z + L • unitStep L m j' ν) q.1 q.2 :=
    ⟨(ν, (L : ℤ)), hwit⟩
  have hq : hex.choose = (ν, (L : ℤ)) := by
    obtain ⟨h₁, h₂⟩ := hex.choose_spec
    rcases hc : hex.choose with ⟨μ, a⟩
    rw [hc] at h₁ h₂
    simp only at h₁ h₂
    have h₃ : ((L : ℤ) • unitStep L m j' ν : Site L m j') = a • unitStep L m j' μ := by
      rw [natCast_zsmul, ← h₁]
      abel
    have h₄ := congrFun (congrArg (fun w : Site L m j' => (w : FourTorus L m)) h₃) ν
    simp only [coe_zsmul_unitStep] at h₄
    have hLr : (0 : ℝ) < L := by exact_mod_cast hL
    have ha : |(a : ℝ)| < (L : ℝ) ^ ((m : ℤ) + j') := by
      simpa using h₂
    by_cases hμ : μ = ν
    · subst hμ
      simp only [pointOnAxis, Pi.single_eq_same] at h₄
      have h₅ : (((((L : ℤ) - a : ℤ) : ℝ) * meshSize L j' : ℝ) : AddCircle (torusSide L m)) = 0 := by
        push_cast at h₄ ⊢
        rw [sub_mul, AddCircle.coe_sub, h₄, sub_self]
      have h₆ := int_eq_zero_of_coe_mul_meshSize hL _ h₅ (by
        push_cast
        have := abs_sub (L : ℝ) (a : ℝ)
        rw [abs_of_pos hLr] at this
        linarith)
      have h₇ : a = (L : ℤ) := by omega
      rw [h₇]
    · have hne : ν ≠ μ := fun h => hμ h.symm
      simp only [pointOnAxis, Pi.single_eq_same, Pi.single_eq_of_ne hne] at h₄
      have h₆ := int_eq_zero_of_coe_mul_meshSize hL (L : ℤ) (by simpa using h₄) (by
        simp only [Int.cast_natCast]
        rw [abs_of_pos hLr]
        linarith)
      omega
  unfold axialPath
  rw [dif_pos hex, hq]
  simp [flowAlong]
theorem not_isPositivelyOriented_both (b : Bond L m j') (h : b.IsPositivelyOriented)
    (h' : b.opposite.IsPositivelyOriented) : False := by
  obtain ⟨μ, hμ⟩ := h
  obtain ⟨ν, hν⟩ := h'
  have hs : unitStep L m j' μ + unitStep L m j' ν = 0 := by
    rw [← hμ, ← hν]
    show b.target - b.source + (b.source - b.target) = 0
    abel
  have h₁ := congrFun (congrArg (fun w : Site L m j' => (w : FourTorus L m)) hs) μ
  have hbig := D.L_lt_zpow
  have h13 : (13 : ℝ) ≤ L := by exact_mod_cast D.thirteen_le
  by_cases hc : ν = μ
  · subst hc
    have h₂ : ((((2 : ℤ) : ℝ) * meshSize L j' : ℝ) : AddCircle (torusSide L m)) = 0 := by
      have h₃ : (((meshSize L j' + meshSize L j' : ℝ)) : AddCircle (torusSide L m)) = 0 := by
        rw [AddCircle.coe_add]
        simpa [unitStep, pointOnAxis] using h₁
      rw [← h₃]
      congr 1
      push_cast
      ring
    have := int_eq_zero_of_coe_mul_meshSize D.L_pos (j' := j') (m := m) 2 h₂ (by
      norm_num
      linarith)
    omega
  · have h₂ : ((((1 : ℤ) : ℝ) * meshSize L j' : ℝ) : AddCircle (torusSide L m)) = 0 := by
      simpa [unitStep, pointOnAxis, Pi.single_eq_of_ne (Ne.symm hc)] using h₁
    have := int_eq_zero_of_coe_mul_meshSize D.L_pos (j' := j') (m := m) 1 h₂ (by
      norm_num
      linarith)
    omega
theorem chartOffset_eq {o x : Site L m j'} {d : Fin 4 → ℤ}
    (h : IsChartOffset o x d) : chartOffset o x = d := by
  have hs : IsChartOffset o x (chartOffset o x) :=
    Classical.epsilon_spec (p := IsChartOffset o x) ⟨d, h⟩
  have hL : (0 : ℝ) < L := by exact_mod_cast D.L_pos
  have hsp : 0 < meshSize L j' := zpow_pos hL _
  refine coefficients_eq_of_sum_eq (m := m) (j' := j') D.L_pos _ _ ?_ fun μ => ?_
  · rw [← coe_sum_zsmul_unitStep, ← coe_sum_zsmul_unitStep, ← hs.1, ← h.1]
  · have h₁ := hs.2 μ
    have h₂ := h.2 μ
    have hz : torusSide L m = 2 * (L : ℝ) ^ ((m : ℤ) + j') * meshSize L j' := by
      unfold torusSide meshSize
      rw [zpow_add₀ hL.ne', zpow_natCast, zpow_neg]
      have : (L : ℝ) ^ j' ≠ 0 := (zpow_pos hL _).ne'
      field_simp
    rw [hz] at h₁ h₂
    have h₃ : ((|chartOffset o x μ| : ℤ) : ℝ) < (L : ℝ) ^ ((m : ℤ) + j') := by
      refine lt_of_mul_lt_mul_right ?_ hsp.le
      linarith
    have h₄ : ((|d μ| : ℤ) : ℝ) < (L : ℝ) ^ ((m : ℤ) + j') := by
      refine lt_of_mul_lt_mul_right ?_ hsp.le
      linarith
    have h₅ := abs_sub (chartOffset o x μ) (d μ)
    have h₆ : ((|chartOffset o x μ - d μ| : ℤ) : ℝ) ≤
        ((|chartOffset o x μ| : ℤ) : ℝ) + ((|d μ| : ℤ) : ℝ) := by
      exact_mod_cast h₅
    rw [Int.cast_abs] at h₆
    linarith
theorem abs_mul_meshSize_lt_half {a : ℤ} (h₀ : 0 ≤ a) (h₁ : a ≤ (L : ℤ) - 1) :
    ((|a| : ℤ) : ℝ) * meshSize L j' < torusSide L m / 2 := by
  have hL : (1 : ℝ) ≤ L := by
    have := D.thirteen_le
    exact_mod_cast (by omega : 1 ≤ L)
  have hsp : meshSize L j' ≤ 1 := by
    unfold meshSize
    exact zpow_le_one_of_nonpos₀ hL (by have := D.fine_nonneg; omega)
  have hm : (L : ℝ) ≤ (L : ℝ) ^ m := by
    have := D.m_pos
    calc (L : ℝ) = (L : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (L : ℝ) ^ m := pow_le_pow_right₀ hL this
  have ha : (a : ℝ) ≤ (L : ℝ) - 1 := by exact_mod_cast h₁
  have ha₀ : (0 : ℝ) ≤ a := by exact_mod_cast h₀
  rw [abs_of_nonneg h₀]
  have hs : torusSide L m / 2 = (L : ℝ) ^ m := by
    unfold torusSide
    ring
  rw [hs]
  nlinarith
end RefinementData
section Grid
variable {L m : ℕ} {j j' : ℤ}
def gridSite (j' : ℤ) (y : Site L m j) (t : Fin 4 → ℤ) : Site L m j' :=
  y.toSublattice j' + ∑ μ, t μ • unitStep L m j' μ
def InGrid (L : ℕ) (t : Fin 4 → ℤ) : Prop :=
  ∀ μ, -((L : ℤ) - 1) ≤ 2 * t μ ∧ 2 * t μ ≤ (L : ℤ) - 1
theorem InGrid.abs_le {t : Fin 4 → ℤ} (h : InGrid L t) (μ : Fin 4) :
    2 * |t μ| ≤ (L : ℤ) - 1 := by
  have := h μ
  rcases abs_cases (t μ) with ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> rw [h₁] <;> omega
theorem gridSite_add_single (y : Site L m j) (t : Fin 4 → ℤ) (μ : Fin 4) (a : ℤ) :
    gridSite j' y (t + Pi.single μ a) = gridSite j' y t + a • unitStep L m j' μ := by
  unfold gridSite
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, add_assoc]
  congr 2
  rw [Finset.sum_eq_single μ]
  · simp
  · intro ν _ hν
    simp [Pi.single_eq_of_ne hν]
  · simp
theorem forwardFlow_inside (D : RefinementData L m j j') (y : Site L m j) (μ : Fin 4) :
    ∀ (k : ℕ) (t : Fin 4 → ℤ), InGrid L t → InGrid L (t + Pi.single μ (k : ℤ)) →
      ∀ b ∈ forwardAxisPath (gridSite j' y t) μ k,
        (b.source : FourTorus L m) ∈ unitBlock y ∧ (b.target : FourTorus L m) ∈ unitBlock y := by
  intro k
  induction k with
  | zero =>
    intro t _ _ b hb
    simp [forwardAxisPath] at hb
  | succ k ih =>
    intro t ht ht' b hb
    have hone : InGrid L (t + Pi.single μ 1) := by
      intro ν
      have h₀ := ht ν
      have h₁ := ht' ν
      by_cases hν : ν = μ
      · subst hν
        simp only [Pi.add_apply, Pi.single_eq_same] at h₁ ⊢
        push_cast at h₁
        omega
      · simpa [Pi.single_eq_of_ne hν] using h₀
    have hrest : InGrid L (t + Pi.single μ 1 + Pi.single μ (k : ℤ)) := by
      have : t + Pi.single μ 1 + Pi.single μ (k : ℤ) = t + Pi.single μ ((k + 1 : ℕ) : ℤ) := by
        rw [add_assoc, ← Pi.single_add]
        push_cast
        rw [add_comm (1 : ℤ)]
      rw [this]
      exact ht'
    have hs : gridSite j' y t + unitStep L m j' μ = gridSite j' y (t + Pi.single μ 1) := by
      rw [gridSite_add_single, one_smul]
    simp only [forwardAxisPath, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨D.add_sum_mem_unitBlock y t ht.abs_le, by
        show ((gridSite j' y t + unitStep L m j' μ : Site L m j') : FourTorus L m) ∈ unitBlock y
        rw [hs]
        exact D.add_sum_mem_unitBlock y _ hone.abs_le⟩
    · rw [hs] at hb
      exact ih _ hone hrest b hb
theorem stepsThroughAxes_inside (D : RefinementData L m j j') (y : Site L m j) (d : Fin 4 → ℤ)
    (hd : ∀ μ, 0 ≤ d μ) :
    ∀ (l : List (Fin 4)) (t : Fin 4 → ℤ), l.Nodup → InGrid L t →
      (∀ μ ∈ l, 2 * (t μ + d μ) ≤ (L : ℤ) - 1) →
      ∀ b ∈ stepsThroughAxes d (gridSite j' y t) l,
        (b.source : FourTorus L m) ∈ unitBlock y ∧ (b.target : FourTorus L m) ∈ unitBlock y := by
  intro l
  induction l with
  | nil =>
    intro t _ _ _ b hb
    simp [stepsThroughAxes] at hb
  | cons μ l ih =>
    intro t hl ht hl' b hb
    have hnot : μ ∉ l := (List.nodup_cons.1 hl).1
    have hμ := hl' μ (List.mem_cons_self)
    have hnat : ((d μ).toNat : ℤ) = d μ := Int.toNat_of_nonneg (hd μ)
    have hnext : InGrid L (t + Pi.single μ (d μ)) := by
      intro ν
      have h₀ := ht ν
      by_cases hν : ν = μ
      · subst hν
        have := hd ν
        simp only [Pi.add_apply, Pi.single_eq_same]
        omega
      · simpa [Pi.single_eq_of_ne hν] using h₀
    simp only [stepsThroughAxes, List.mem_append] at hb
    rcases hb with hb | hb
    · have hb' : b ∈ forwardAxisPath (gridSite j' y t) μ (d μ).toNat := by
        simpa [flowAlong, hd μ] using hb
      exact forwardFlow_inside D y μ _ t ht (by rw [hnat]; exact hnext) b hb'
    · rw [← gridSite_add_single] at hb
      refine ih _ (List.nodup_cons.1 hl).2 hnext (fun ν hν => ?_) b hb
      have hne : ν ≠ μ := fun h => hnot (h ▸ hν)
      simpa [Pi.single_eq_of_ne hne] using hl' ν (List.mem_cons_of_mem _ hν)
theorem RefinementData.blockOffset_eq (D : RefinementData L m j j') {y : Site L m j}
    {x : Site L m j'} {N : Fin 4 → ℤ} (h : IsBlockOffset y x N) :
    blockOffset y x = N :=
  D.offset_unique (Classical.epsilon_spec (p := IsBlockOffset y x) ⟨N, h⟩) h
theorem RefinementData.two_mul_centreToFaceSteps (D : RefinementData L m j j') :
    2 * centreToFaceSteps L = (L : ℤ) - 1 := by
  obtain ⟨a, rfl⟩ := D.odd
  unfold centreToFaceSteps
  push_cast
  omega
theorem RefinementData.corner_inGrid (D : RefinementData L m j j') :
    InGrid L fun _ => -centreToFaceSteps L := by
  intro μ
  have := D.two_mul_centreToFaceSteps
  have := D.thirteen_le
  constructor <;> simp only <;> omega
theorem RefinementData.corner_eq_gridSite (y : Site L m j) :
    schemeBaseSite .cornered j' y = gridSite j' y fun _ => -centreToFaceSteps L := by
  simp only [schemeBaseSite, gridSite, neg_smul, Finset.sum_neg_distrib, ← Finset.smul_sum]
  abel
theorem RefinementData.centre_mem (D : RefinementData L m j j') (y : Site L m j) :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) ∈ unitBlock y := by
  simpa using D.add_sum_mem_unitBlock y 0 (fun μ => by
    have := D.thirteen_le
    simp only [Pi.zero_apply, abs_zero]
    omega)
theorem RefinementData.corner_mem (D : RefinementData L m j j') (y : Site L m j) :
    ((schemeBaseSite .cornered j' y : Site L m j') : FourTorus L m) ∈ unitBlock y := by
  rw [RefinementData.corner_eq_gridSite]
  exact D.add_sum_mem_unitBlock y _ D.corner_inGrid.abs_le
theorem RefinementData.base_mem (D : RefinementData L m j j') (s : AveragingScheme) (y : Site L m j) :
    ((schemeBaseSite s j' y : Site L m j') : FourTorus L m) ∈ unitBlock y := by
  cases s
  · exact D.centre_mem y
  · exact D.corner_mem y
theorem RefinementData.base_target (D : RefinementData L m j j') (s : AveragingScheme) (c : Bond L m j)
    (ν : Fin 4) (hν : c.target - c.source = unitStep L m j ν) :
    schemeBaseSite s j' c.target = schemeBaseSite s j' c.source + L • unitStep L m j' ν := by
  cases s
  · exact D.target_toSublattice c ν hν
  · simp only [schemeBaseSite]
    rw [D.target_toSublattice c ν hν]
    abel
theorem RefinementData.chartOffset_corner (D : RefinementData L m j j') {y : Site L m j}
    {x : Site L m j'} {N : Fin 4 → ℤ} (hN : IsBlockOffset y x N) :
    chartOffset (schemeBaseSite .cornered j' y) x = fun μ => N μ + centreToFaceSteps L := by
  apply D.chartOffset_eq
  refine ⟨?_, fun μ => ?_⟩
  · have hx := D.eq_add_sum hN
    have ho := RefinementData.corner_eq_gridSite (L := L) (m := m) (j' := j') y
    rw [ho]
    simp only [gridSite, add_smul, Finset.sum_add_distrib, neg_smul, Finset.sum_neg_distrib]
    nth_rewrite 1 [hx]
    abel
  · have h₁ := hN.2 μ
    have h₂ := D.two_mul_centreToFaceSteps
    have h₃ := neg_abs_le (N μ)
    have h₄ := le_abs_self (N μ)
    exact D.abs_mul_meshSize_lt_half (a := N μ + centreToFaceSteps L) (by omega) (by omega)
theorem RefinementData.comb_path_inside (D : RefinementData L m j j') {y : Site L m j}
    {x : Site L m j'} {N : Fin 4 → ℤ} (hN : IsBlockOffset y x N) :
    ∀ b ∈ stepsThroughAxes (fun μ => N μ + centreToFaceSteps L) (schemeBaseSite .cornered j' y)
        [3, 2, 1, 0],
      (b.source : FourTorus L m) ∈ unitBlock y ∧ (b.target : FourTorus L m) ∈ unitBlock y := by
  rw [RefinementData.corner_eq_gridSite]
  have h₂ := D.two_mul_centreToFaceSteps
  refine stepsThroughAxes_inside D y _ (fun μ => ?_) _ _ (by decide) D.corner_inGrid fun μ _ => ?_
  · have h₁ := hN.2 μ
    have h₃ := neg_abs_le (N μ)
    omega
  · have h₁ := hN.2 μ
    have h₄ := le_abs_self (N μ)
    omega
end Grid
section Means
theorem complexLogMean_reindex {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    (V : ι → Matrices.ComplexMatrix2) (V' : ι' → Matrices.ComplexMatrix2)
    (h : ∀ i, V' (e i) = V i) : complexLogMean V' = complexLogMean V := by
  have hV : V = V' ∘ e := funext fun i => (h i).symm
  subst hV
  unfold complexLogMean
  congr 1
  funext W
  apply propext
  have hsum : ∑ i, Matrices.ComplexMatrix2.logSeries ((V' ∘ e) i * W⁻¹) =
      ∑ i, Matrices.ComplexMatrix2.logSeries (V' i * W⁻¹) :=
    Equiv.sum_comp e fun i => Matrices.ComplexMatrix2.logSeries (V' i * W⁻¹)
  unfold Matrices.ComplexMatrix2.IsLogMean
  rw [hsum]
  constructor
  · rintro ⟨⟨h₁, h₂, h₃⟩, i, hi⟩
    exact ⟨⟨h₁, fun k => h₂ (e k), h₃⟩, e.symm i, by simpa using hi⟩
  · rintro ⟨⟨h₁, h₂, h₃⟩, i, hi⟩
    exact ⟨⟨h₁, fun k => by simpa using h₂ (e.symm k), h₃⟩, e i, hi⟩
theorem exists_ordering_equiv {A B : Finset (Fin 4)} (h : A = B) :
    ∃ e : (Fin A.card ≃ A) ≃ (Fin B.card ≃ B), ∀ σ : Fin A.card ≃ A,
      ((List.finRange _).map fun i => ((e σ i : B) : Fin 4)) =
        (List.finRange _).map fun i => ((σ i : A) : Fin 4) := by
  subst h
  exact ⟨Equiv.refl _, fun _ => rfl⟩
theorem sum_map_ordering {A : Type*} [AddCommMonoid A] (S : Finset (Fin 4))
    (σ : Fin S.card ≃ S) (g : Fin 4 → A) (hg : ∀ μ, μ ∉ S → g μ = 0) :
    (((List.finRange _).map fun i => ((σ i : S) : Fin 4)).map g).sum = ∑ μ, g μ := by
  rw [List.map_map]
  have h₁ : ((List.finRange S.card).map (g ∘ fun i => ((σ i : S) : Fin 4))).sum =
      ∑ i, g ((σ i : S) : Fin 4) := (Fin.sum_univ_def _).symm
  rw [h₁, Equiv.sum_comp σ fun s : S => g (s : Fin 4), Finset.sum_coe_sort S g]
  exact Finset.sum_subset (Finset.subset_univ S) fun μ _ hμ => hg μ hμ
end Means
section Chart
variable {L m K n m' K' n' : ℕ}
structure DoubleBlockData (c : BondAtLevel L m K (n + 1)) (ν : Fin 4) : Prop where
  refinement : RefinementData L m (levelDepth K (n + 1)) (levelDepth K n)
  target_sub : c.target - c.source = unitStep L m (levelDepth K (n + 1)) ν
  unitBlock_subset : ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
    unitBlock y ⊆ bondDoubleBlock c
  exists_offset : ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
    ∀ x : SiteAtLevel L m K n, (x : FourTorus L m) ∈ unitBlock y → ∃ N, IsBlockOffset y x N
  orderedContour_mem : ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
    ∀ x : SiteAtLevel L m K n, (x : FourTorus L m) ∈ unitBlock y → ∀ σ : AxisOrdering y x,
      ∀ b ∈ orderedContour y x σ, b ∈ (doubleBlockSymmetricSet c).bonds
  shift_mem : ∀ x : SiteAtLevel L m K n, (x : FourTorus L m) ∈ unitBlock c.source →
    ((x + L • unitStep L m (levelDepth K n) ν : SiteAtLevel L m K n) : FourTorus L m) ∈
        unitBlock c.target ∧
      ∀ b ∈ axialPath x (x + L • unitStep L m (levelDepth K n) ν),
        b ∈ (doubleBlockSymmetricSet c).bonds
theorem doubleBlockData (hq : StandardPartitionCubeGeometry)
    (hC : DoubleBlock.DoubleBlockContoursStatement) (hodd : Odd L) (h13 : 13 ≤ L) (hm : 0 < m)
    (hn : n < K) (c : BondAtLevel L m K (n + 1)) (ν : Fin 4)
    (hν : c.target - c.source = unitStep L m (levelDepth K (n + 1)) ν) : DoubleBlockData c ν := by
  have hj : 0 ≤ levelDepth K (n + 1) := by
    simp only [levelDepth]
    omega
  have hc := hC L m K hodd h13 hm n hn c
  refine ⟨⟨h13, hodd, hm, hj, by simp only [levelDepth]; push_cast; ring, fun y =>
      ((hq L m hodd h13 hm _ (by omega)).1 1).1 y⟩, hν, fun y hy => (hc.1 y hy).1,
    fun y hy x hx => ((hc.1 y hy).2 x hx).1, fun y hy x hx σ b hb => ?_, fun x hx => ?_⟩
  · obtain ⟨⟨N, hN⟩, hall⟩ := (hc.1 y hy).2 x hx
    obtain ⟨h₁, h₂⟩ := (hall N hN).2.2.2.2.2 _ ⟨σ, rfl⟩ b hb
    exact ⟨(hc.1 y hy).1 h₁, (hc.1 y hy).1 h₂⟩
  · have htarget : c.target = c.source + unitStep L m (levelDepth K (n + 1)) ν := by
      rw [← hν]
      abel
    let σ : AxisOrdering c.source x := (offsetAxes c.source x).equivFin.symm
    obtain ⟨⟨N, hN⟩, hall⟩ := (hc.1 c.source (Or.inl rfl)).2 x hx
    obtain ⟨g, -, hg⟩ := (hall N hN).2.1 _ ⟨σ, rfl⟩
    have h := hc.2 ν htarget x hx σ g hg
    unfold DoubleBlock.ContoursAcrossBond at h
    dsimp only at h
    exact ⟨h.1, fun b hb => h.2.2.2.2.2.2.2.2.2.2.2.1 b hb⟩
structure ChartData (c : BondAtLevel L m K (n + 1)) (c' : BondAtLevel L m' K' (n' + 1))
    (f : SiteAtLevel L m K n → SiteAtLevel L m' K' n') (ν : Fin 4) : Prop where
  domain : DoubleBlockData c ν
  codomain : DoubleBlockData c' ν
  isChart : IsDoubleBlockChart c c' f
def Corresponds (f : SiteAtLevel L m K n → SiteAtLevel L m' K' n') (c : BondAtLevel L m K (n + 1))
    (c' : BondAtLevel L m' K' (n' + 1)) (b : BondAtLevel L m K n) (b' : BondAtLevel L m' K' n') :
    Prop :=
  b ∈ (doubleBlockSymmetricSet c).bonds ∧ b' ∈ (doubleBlockSymmetricSet c').bonds ∧
    b'.source = f b.source ∧ b'.target = f b.target
def AgreeOn (f : SiteAtLevel L m K n → SiteAtLevel L m' K' n') (c : BondAtLevel L m K (n + 1))
    (c' : BondAtLevel L m' K' (n' + 1)) (W : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (W' : BondAtLevel L m' K' n' → Matrices.ComplexMatrix2) : Prop :=
  ∀ b b', Corresponds f c c' b b' → W' b' = W b
def EndpointPair (c : BondAtLevel L m K (n + 1)) (c' : BondAtLevel L m' K' (n' + 1))
    (y : SiteAtLevel L m K (n + 1)) (y' : SiteAtLevel L m' K' (n' + 1)) : Prop :=
  y = c.source ∧ y' = c'.source ∨ y = c.target ∧ y' = c'.target
theorem EndpointPair.left_end {c : BondAtLevel L m K (n + 1)} {c' : BondAtLevel L m' K' (n' + 1)}
    {y : SiteAtLevel L m K (n + 1)} {y' : SiteAtLevel L m' K' (n' + 1)}
    (h : EndpointPair c c' y y') : y = c.source ∨ y = c.target := h.imp And.left And.left
theorem EndpointPair.right_end {c : BondAtLevel L m K (n + 1)} {c' : BondAtLevel L m' K' (n' + 1)}
    {y : SiteAtLevel L m K (n + 1)} {y' : SiteAtLevel L m' K' (n' + 1)}
    (h : EndpointPair c c' y y') : y' = c'.source ∨ y' = c'.target := h.imp And.right And.right
theorem pathHolonomy_eq_of_forall₂ {f : SiteAtLevel L m K n → SiteAtLevel L m' K' n'}
    {c : BondAtLevel L m K (n + 1)} {c' : BondAtLevel L m' K' (n' + 1)}
    {W : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    {W' : BondAtLevel L m' K' n' → Matrices.ComplexMatrix2}
    (hW : AgreeOn f c c' W W') {Γ : List (BondAtLevel L m K n)}
    {Γ' : List (BondAtLevel L m' K' n')} (h : List.Forall₂ (Corresponds f c c') Γ Γ') :
    pathHolonomy W' Γ' = pathHolonomy W Γ := by
  induction h with
  | nil => rfl
  | cons hb _ ih =>
    simp only [pathHolonomy, List.map_cons, List.prod_cons] at ih ⊢
    rw [hW _ _ hb, ih]
namespace ChartData
variable {c : BondAtLevel L m K (n + 1)} {c' : BondAtLevel L m' K' (n' + 1)}
  {f : SiteAtLevel L m K n → SiteAtLevel L m' K' n'} {ν : Fin 4} (C : ChartData c c' f ν)
include C
theorem map_add_unitStep {x : SiteAtLevel L m K n} {μ : Fin 4}
    (hb : Bond.forwardFrom x μ ∈ (doubleBlockSymmetricSet c).bonds) :
    f (x + unitStep L m (levelDepth K n) μ) = f x + unitStep L m' (levelDepth K' n') μ :=
  C.isChart.map_unitStep x hb.1 μ hb.2
theorem corresponds_forwardFrom {x : SiteAtLevel L m K n} {μ : Fin 4}
    (hb : Bond.forwardFrom x μ ∈ (doubleBlockSymmetricSet c).bonds) :
    Corresponds f c c' (Bond.forwardFrom x μ) (Bond.forwardFrom (f x) μ) := by
  have e := C.map_add_unitStep hb
  refine ⟨hb, ⟨C.isChart.bijOn.mapsTo hb.1, ?_⟩, rfl, e.symm⟩
  show ((f x + unitStep L m' (levelDepth K' n') μ : SiteAtLevel L m' K' n') : FourTorus L m') ∈
    bondDoubleBlock c'
  rw [← e]
  exact C.isChart.bijOn.mapsTo hb.2
theorem map_sub_unitStep {x : SiteAtLevel L m K n} {μ : Fin 4}
    (hb : Bond.backwardFrom x μ ∈ (doubleBlockSymmetricSet c).bonds) :
    f (x - unitStep L m (levelDepth K n) μ) = f x - unitStep L m' (levelDepth K' n') μ := by
  have h₁ : x - unitStep L m (levelDepth K n) μ + unitStep L m (levelDepth K n) μ = x := by abel
  have e := C.isChart.map_unitStep (x - unitStep L m (levelDepth K n) μ) hb.2 μ
    (by rw [h₁]; exact hb.1)
  rw [h₁] at e
  rw [e]
  abel
theorem corresponds_backwardFrom {x : SiteAtLevel L m K n} {μ : Fin 4}
    (hb : Bond.backwardFrom x μ ∈ (doubleBlockSymmetricSet c).bonds) :
    Corresponds f c c' (Bond.backwardFrom x μ) (Bond.backwardFrom (f x) μ) := by
  have e := C.map_sub_unitStep hb
  refine ⟨hb, ⟨C.isChart.bijOn.mapsTo hb.1, ?_⟩, rfl, e.symm⟩
  show ((f x - unitStep L m' (levelDepth K' n') μ : SiteAtLevel L m' K' n') : FourTorus L m') ∈
    bondDoubleBlock c'
  rw [← e]
  exact C.isChart.bijOn.mapsTo hb.2
theorem forall₂_forwardFlow (μ : Fin 4) : ∀ (k : ℕ) (x : SiteAtLevel L m K n),
    (∀ b ∈ forwardAxisPath x μ k, b ∈ (doubleBlockSymmetricSet c).bonds) →
    List.Forall₂ (Corresponds f c c') (forwardAxisPath x μ k) (forwardAxisPath (f x) μ k) ∧
      f (x + (k : ℤ) • unitStep L m (levelDepth K n) μ) =
        f x + (k : ℤ) • unitStep L m' (levelDepth K' n') μ := by
  intro k
  induction k with
  | zero =>
    intro x _
    exact ⟨List.Forall₂.nil, by simp⟩
  | succ k ih =>
    intro x h
    have hb := h (Bond.forwardFrom x μ) (by simp [forwardAxisPath])
    have e := C.map_add_unitStep hb
    obtain ⟨h₁, h₂⟩ := ih (x + unitStep L m (levelDepth K n) μ)
      (fun b hb' => h b (by simp only [forwardAxisPath]; exact List.mem_cons_of_mem _ hb'))
    rw [e] at h₁ h₂
    refine ⟨List.Forall₂.cons (C.corresponds_forwardFrom hb) h₁, ?_⟩
    have hx : x + ((k + 1 : ℕ) : ℤ) • unitStep L m (levelDepth K n) μ =
        x + unitStep L m (levelDepth K n) μ + (k : ℤ) • unitStep L m (levelDepth K n) μ := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [hx, h₂]
    push_cast
    rw [add_smul, one_smul]
    abel
theorem forall₂_backwardFlow (μ : Fin 4) : ∀ (k : ℕ) (x : SiteAtLevel L m K n),
    (∀ b ∈ backwardAxisPath x μ k, b ∈ (doubleBlockSymmetricSet c).bonds) →
    List.Forall₂ (Corresponds f c c') (backwardAxisPath x μ k) (backwardAxisPath (f x) μ k) ∧
      f (x - (k : ℤ) • unitStep L m (levelDepth K n) μ) =
        f x - (k : ℤ) • unitStep L m' (levelDepth K' n') μ := by
  intro k
  induction k with
  | zero =>
    intro x _
    exact ⟨List.Forall₂.nil, by simp⟩
  | succ k ih =>
    intro x h
    have hb := h (Bond.backwardFrom x μ) (by simp [backwardAxisPath])
    have e := C.map_sub_unitStep hb
    obtain ⟨h₁, h₂⟩ := ih (x - unitStep L m (levelDepth K n) μ)
      (fun b hb' => h b (by simp only [backwardAxisPath]; exact List.mem_cons_of_mem _ hb'))
    rw [e] at h₁ h₂
    refine ⟨List.Forall₂.cons (C.corresponds_backwardFrom hb) h₁, ?_⟩
    have hx : x - ((k + 1 : ℕ) : ℤ) • unitStep L m (levelDepth K n) μ =
        x - unitStep L m (levelDepth K n) μ - (k : ℤ) • unitStep L m (levelDepth K n) μ := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [hx, h₂]
    push_cast
    rw [add_smul, one_smul]
    abel
theorem forall₂_flowAlong (μ : Fin 4) (a : ℤ) (x : SiteAtLevel L m K n)
    (h : ∀ b ∈ flowAlong x μ a, b ∈ (doubleBlockSymmetricSet c).bonds) :
    List.Forall₂ (Corresponds f c c') (flowAlong x μ a) (flowAlong (f x) μ a) ∧
      f (x + a • unitStep L m (levelDepth K n) μ) = f x + a • unitStep L m' (levelDepth K' n') μ := by
  unfold flowAlong at h ⊢
  split_ifs at h ⊢ with ha
  · have hk := C.forall₂_forwardFlow μ a.toNat x h
    rwa [Int.toNat_of_nonneg ha] at hk
  · have hk := C.forall₂_backwardFlow μ (-a).toNat x h
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ -a)] at hk
    simpa [sub_eq_add_neg] using hk
theorem forall₂_stepsThroughAxes (N : Fin 4 → ℤ) : ∀ (l : List (Fin 4)) (x : SiteAtLevel L m K n),
    (∀ b ∈ stepsThroughAxes N x l, b ∈ (doubleBlockSymmetricSet c).bonds) →
    List.Forall₂ (Corresponds f c c') (stepsThroughAxes N x l) (stepsThroughAxes N (f x) l) ∧
      f (x + (l.map fun μ => N μ • unitStep L m (levelDepth K n) μ).sum) =
        f x + (l.map fun μ => N μ • unitStep L m' (levelDepth K' n') μ).sum := by
  intro l
  induction l with
  | nil =>
    intro x _
    exact ⟨List.Forall₂.nil, by simp⟩
  | cons μ l ih =>
    intro x h
    simp only [stepsThroughAxes] at h ⊢
    obtain ⟨a₁, a₂⟩ := C.forall₂_flowAlong μ (N μ) x fun b hb => h b (List.mem_append_left _ hb)
    obtain ⟨b₁, b₂⟩ := ih (x + N μ • unitStep L m (levelDepth K n) μ)
      fun b hb => h b (List.mem_append_right _ hb)
    rw [a₂] at b₁ b₂
    refine ⟨List.rel_append a₁ b₁, ?_⟩
    simp only [List.map_cons, List.sum_cons, ← add_assoc]
    exact b₂
theorem map_shift {x : SiteAtLevel L m K n} (hx : (x : FourTorus L m) ∈ unitBlock c.source) :
    f (x + L • unitStep L m (levelDepth K n) ν) = f x + L • unitStep L m' (levelDepth K' n') ν ∧
      List.Forall₂ (Corresponds f c c') (axialPath x (x + L • unitStep L m (levelDepth K n) ν))
        (axialPath (f x) (f x + L • unitStep L m' (levelDepth K' n') ν)) := by
  have hb := (C.domain.shift_mem x hx).2
  rw [C.domain.refinement.axialPath_eq] at hb
  obtain ⟨h₁, h₂⟩ := C.forall₂_forwardFlow ν L x hb
  rw [C.domain.refinement.axialPath_eq, C.codomain.refinement.axialPath_eq]
  rw [natCast_zsmul, natCast_zsmul] at h₂
  exact ⟨h₂, h₁⟩
theorem map_centre {y : SiteAtLevel L m K (n + 1)} {y' : SiteAtLevel L m' K' (n' + 1)}
    (hp : EndpointPair c c' y y') :
    f (y.toSublattice (levelDepth K n)) = y'.toSublattice (levelDepth K' n') := by
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact C.isChart.map_source
  · rw [C.domain.refinement.target_toSublattice c ν C.domain.target_sub,
      C.codomain.refinement.target_toSublattice c' ν C.codomain.target_sub,
      (C.map_shift (C.domain.refinement.centre_mem c.source)).1, C.isChart.map_source]
theorem map_gridSite {y : SiteAtLevel L m K (n + 1)} {y' : SiteAtLevel L m' K' (n' + 1)}
    (hp : EndpointPair c c' y y') {x : SiteAtLevel L m K n} (hx : (x : FourTorus L m) ∈ unitBlock y)
    {N : Fin 4 → ℤ} (hN : IsBlockOffset y x N) :
    f x = y'.toSublattice (levelDepth K' n') + ∑ μ, N μ • unitStep L m' (levelDepth K' n') μ := by
  let σ : AxisOrdering y x := (offsetAxes y x).equivFin.symm
  have hbd := C.domain.refinement.blockOffset_eq hN
  have hzero : ∀ μ, μ ∉ offsetAxes y x → blockOffset y x μ = 0 := by
    intro μ hμ
    simpa [offsetAxes] using hμ
  have h₂ := (C.forall₂_stepsThroughAxes (blockOffset y x) _ (y.toSublattice (levelDepth K n))
    (C.domain.orderedContour_mem y hp.left_end x hx σ)).2
  rw [sum_map_ordering (offsetAxes y x) σ
      (fun μ => blockOffset y x μ • unitStep L m (levelDepth K n) μ)
      (fun μ hμ => by simp only [hzero μ hμ, zero_smul]),
    sum_map_ordering (offsetAxes y x) σ
      (fun μ => blockOffset y x μ • unitStep L m' (levelDepth K' n') μ)
      (fun μ hμ => by simp only [hzero μ hμ, zero_smul]),
    hbd, ← C.domain.refinement.eq_add_sum hN, C.map_centre hp] at h₂
  exact h₂
theorem isBlockOffset_map {y : SiteAtLevel L m K (n + 1)} {y' : SiteAtLevel L m' K' (n' + 1)}
    (hp : EndpointPair c c' y y') {x : SiteAtLevel L m K n} (hx : (x : FourTorus L m) ∈ unitBlock y)
    {N : Fin 4 → ℤ} (hN : IsBlockOffset y x N) : IsBlockOffset y' (f x) N :=
  C.codomain.refinement.isBlockOffset_of_eq hN.2 (C.map_gridSite hp hx hN)
theorem blockOffset_map {y : SiteAtLevel L m K (n + 1)} {y' : SiteAtLevel L m' K' (n' + 1)}
    (hp : EndpointPair c c' y y') {x : SiteAtLevel L m K n}
    (hx : (x : FourTorus L m) ∈ unitBlock y) :
    blockOffset y' (f x) = blockOffset y x := by
  obtain ⟨N, hN⟩ := C.domain.exists_offset y hp.left_end x hx
  rw [C.domain.refinement.blockOffset_eq hN,
    C.codomain.refinement.blockOffset_eq (C.isBlockOffset_map hp hx hN)]
theorem bijOn_sitesInBlock {y : SiteAtLevel L m K (n + 1)} {y' : SiteAtLevel L m' K' (n' + 1)}
    (hp : EndpointPair c c' y y') :
    Set.BijOn f (sitesInBlock (levelDepth K n) y) (sitesInBlock (levelDepth K' n') y') := by
  refine Set.BijOn.mk (fun x hx => ?_) ?_ (fun x' hx' => ?_)
  · obtain ⟨N, hN⟩ := C.domain.exists_offset y hp.left_end x hx
    show ((f x : SiteAtLevel L m' K' n') : FourTorus L m') ∈ unitBlock y'
    rw [C.map_gridSite hp hx hN]
    exact C.codomain.refinement.add_sum_mem_unitBlock y' N hN.2
  · exact C.isChart.bijOn.injOn.mono fun x hx => C.domain.unitBlock_subset y hp.left_end hx
  · obtain ⟨N, hN⟩ := C.codomain.exists_offset y' hp.right_end x' hx'
    have hmem := C.domain.refinement.add_sum_mem_unitBlock y N hN.2
    have hd : IsBlockOffset y (y.toSublattice (levelDepth K n) +
        ∑ μ, N μ • unitStep L m (levelDepth K n) μ) N :=
      C.domain.refinement.isBlockOffset_of_eq hN.2 rfl
    refine ⟨_, hmem, ?_⟩
    rw [C.map_gridSite hp hmem hd, ← C.codomain.refinement.eq_add_sum hN]
theorem contourHolonomy_centred {W : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    {W' : BondAtLevel L m' K' n' → Matrices.ComplexMatrix2}
    (hW : AgreeOn f c c' W W') {y : SiteAtLevel L m K (n + 1)} {y' : SiteAtLevel L m' K' (n' + 1)}
    (hp : EndpointPair c c' y y') {x : SiteAtLevel L m K n}
    (hx : (x : FourTorus L m) ∈ unitBlock y) :
    contourHolonomy .centred W' y' (f x) = contourHolonomy .centred W y x := by
  have hbd := C.blockOffset_map hp hx
  have hdirs : offsetAxes y x = offsetAxes y' (f x) := by
    simp only [offsetAxes, hbd]
  obtain ⟨e, he⟩ := exists_ordering_equiv hdirs
  refine complexLogMean_reindex e _ _ fun σ => ?_
  show pathHolonomy W' (orderedContour y' (f x) (e σ)) = pathHolonomy W (orderedContour y x σ)
  have h₁ := (C.forall₂_stepsThroughAxes (blockOffset y x) _ (y.toSublattice (levelDepth K n))
    (C.domain.orderedContour_mem y hp.left_end x hx σ)).1
  have h₂ : orderedContour y' (f x) (e σ) = stepsThroughAxes (blockOffset y x)
      (f (y.toSublattice (levelDepth K n)))
      ((List.finRange _).map fun i => ((σ i : offsetAxes y x) : Fin 4)) := by
    unfold orderedContour
    rw [he σ, hbd, C.map_centre hp]
  rw [h₂]
  exact pathHolonomy_eq_of_forall₂ hW h₁
theorem map_corner {y : SiteAtLevel L m K (n + 1)} {y' : SiteAtLevel L m' K' (n' + 1)}
    (hp : EndpointPair c c' y y') :
    f (schemeBaseSite .cornered (levelDepth K n) y) = schemeBaseSite .cornered (levelDepth K' n') y' := by
  have hd : IsBlockOffset y (schemeBaseSite .cornered (levelDepth K n) y)
      (fun _ => -centreToFaceSteps L) :=
    C.domain.refinement.isBlockOffset_of_eq C.domain.refinement.corner_inGrid.abs_le
      (RefinementData.corner_eq_gridSite y)
  rw [C.map_gridSite hp (C.domain.refinement.corner_mem y) hd, RefinementData.corner_eq_gridSite]
  rfl
theorem map_base (s : AveragingScheme) {y : SiteAtLevel L m K (n + 1)}
    {y' : SiteAtLevel L m' K' (n' + 1)} (hp : EndpointPair c c' y y') :
    f (schemeBaseSite s (levelDepth K n) y) = schemeBaseSite s (levelDepth K' n') y' := by
  cases s
  · exact C.map_centre hp
  · exact C.map_corner hp
theorem contourHolonomy_cornered {W : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    {W' : BondAtLevel L m' K' n' → Matrices.ComplexMatrix2}
    (hW : AgreeOn f c c' W W') {y : SiteAtLevel L m K (n + 1)} {y' : SiteAtLevel L m' K' (n' + 1)}
    (hp : EndpointPair c c' y y') {x : SiteAtLevel L m K n}
    (hx : (x : FourTorus L m) ∈ unitBlock y) :
    contourHolonomy .cornered W' y' (f x) = contourHolonomy .cornered W y x := by
  obtain ⟨N, hN⟩ := C.domain.exists_offset y hp.left_end x hx
  have hsub := C.domain.unitBlock_subset y hp.left_end
  have hin := C.domain.refinement.comb_path_inside hN
  have h₁ := (C.forall₂_stepsThroughAxes (fun μ => N μ + centreToFaceSteps L) [3, 2, 1, 0]
    (schemeBaseSite .cornered (levelDepth K n) y)
    (fun b hb => ⟨hsub (hin b hb).1, hsub (hin b hb).2⟩)).1
  show pathHolonomy W' (coordinateComb (schemeBaseSite .cornered (levelDepth K' n') y') (f x)) =
    pathHolonomy W (coordinateComb (schemeBaseSite .cornered (levelDepth K n) y) x)
  have e₁ : coordinateComb (schemeBaseSite .cornered (levelDepth K n) y) x =
      stepsThroughAxes (fun μ => N μ + centreToFaceSteps L)
        (schemeBaseSite .cornered (levelDepth K n) y) [3, 2, 1, 0] := by
    unfold coordinateComb
    rw [C.domain.refinement.chartOffset_corner hN]
  have e₂ : coordinateComb (schemeBaseSite .cornered (levelDepth K' n') y') (f x) =
      stepsThroughAxes (fun μ => N μ + centreToFaceSteps L)
        (f (schemeBaseSite .cornered (levelDepth K n) y)) [3, 2, 1, 0] := by
    unfold coordinateComb
    rw [C.codomain.refinement.chartOffset_corner (C.isBlockOffset_map hp hx hN), C.map_corner hp]
  rw [e₁, e₂]
  exact pathHolonomy_eq_of_forall₂ hW h₁
theorem contourHolonomy_eq (s : AveragingScheme) {W : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    {W' : BondAtLevel L m' K' n' → Matrices.ComplexMatrix2} (hW : AgreeOn f c c' W W')
    {y : SiteAtLevel L m K (n + 1)} {y' : SiteAtLevel L m' K' (n' + 1)}
    (hp : EndpointPair c c' y y') {x : SiteAtLevel L m K n}
    (hx : (x : FourTorus L m) ∈ unitBlock y) :
    contourHolonomy s W' y' (f x) = contourHolonomy s W y x := by
  cases s
  · exact C.contourHolonomy_centred hW hp hx
  · exact C.contourHolonomy_cornered hW hp hx
theorem sourcePair : EndpointPair c c' c.source c'.source := Or.inl ⟨rfl, rfl⟩
theorem targetPair : EndpointPair c c' c.target c'.target := Or.inr ⟨rfl, rfl⟩
theorem baseTransport_eq (s : AveragingScheme) {W : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    {W' : BondAtLevel L m' K' n' → Matrices.ComplexMatrix2} (hW : AgreeOn f c c' W W') :
    baseTransport s W' c' = baseTransport s W c := by
  unfold baseTransport
  rw [C.domain.refinement.base_target s c ν C.domain.target_sub,
    C.codomain.refinement.base_target s c' ν C.codomain.target_sub, ← C.map_base s C.sourcePair]
  exact pathHolonomy_eq_of_forall₂ hW (C.map_shift (C.domain.refinement.base_mem s c.source)).2
theorem localDefect_eq (s : AveragingScheme) {W : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    {W' : BondAtLevel L m' K' n' → Matrices.ComplexMatrix2} (hW : AgreeOn f c c' W W')
    {x : SiteAtLevel L m K n} (hx : (x : FourTorus L m) ∈ unitBlock c.source) :
    localDefect s W' c' (f x) = localDefect s W c x := by
  have hcross := C.map_shift hx
  have e₁ := C.domain.refinement.shiftAcross_eq c ν C.domain.target_sub x
  have e₂ := C.codomain.refinement.shiftAcross_eq c' ν C.codomain.target_sub (f x)
  have ht : shiftAcross c' (f x) = f (shiftAcross c x) := by
    rw [e₁, e₂, hcross.1]
  have hxh : ((shiftAcross c x : SiteAtLevel L m K n) : FourTorus L m) ∈ unitBlock c.target := by
    rw [e₁]
    exact (C.domain.shift_mem x hx).1
  have hc : pathHolonomy W' (crossingPath c' (f x)) = pathHolonomy W (crossingPath c x) := by
    unfold crossingPath
    rw [e₁, e₂]
    exact pathHolonomy_eq_of_forall₂ hW hcross.2
  unfold localDefect
  rw [ht, C.contourHolonomy_eq s hW C.sourcePair hx, C.contourHolonomy_eq s hW C.targetPair hxh,
    C.baseTransport_eq s hW, hc]
theorem schemeBlockAverage_eq (s : AveragingScheme)
    {W : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    {W' : BondAtLevel L m' K' n' → Matrices.ComplexMatrix2} (hW : AgreeOn f c c' W W') :
    schemeBlockAverage s W' c' = schemeBlockAverage s W c := by
  have hpos : c.IsPositivelyOriented := ⟨ν, C.domain.target_sub⟩
  have hpos' : c'.IsPositivelyOriented := ⟨ν, C.codomain.target_sub⟩
  have h₁ : schemeBlockAverage s W c = positiveBondAverage s W c := by
    unfold schemeBlockAverage
    exact if_pos hpos
  have h₂ : schemeBlockAverage s W' c' = positiveBondAverage s W' c' := by
    unfold schemeBlockAverage
    exact if_pos hpos'
  rw [h₁, h₂]
  unfold positiveBondAverage
  have h₃ : ∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source,
        Matrices.ComplexMatrix2.logSeries (localDefect s W c x) =
      ∑ᶠ x ∈ sitesInBlock (levelDepth K' n') c'.source,
        Matrices.ComplexMatrix2.logSeries (localDefect s W' c' x) :=
    finsum_mem_eq_of_bijOn f (C.bijOn_sitesInBlock C.sourcePair) fun x hx =>
      (congrArg Matrices.ComplexMatrix2.logSeries (C.localDefect_eq s hW hx)).symm
  rw [h₃, C.baseTransport_eq s hW]
theorem isPositivelyOriented_of_corresponds {b : BondAtLevel L m K n} {b' : BondAtLevel L m' K' n'}
    (hl : Corresponds f c c' b b') (hb : b.IsPositivelyOriented) : b'.IsPositivelyOriented := by
  obtain ⟨μ, h⟩ := hb
  have hh : b.target = b.source + unitStep L m (levelDepth K n) μ := by
    rw [← h]
    abel
  have e := C.isChart.map_unitStep b.source hl.1.1 μ (by rw [← hh]; exact hl.1.2)
  refine ⟨μ, ?_⟩
  rw [hl.2.2.2, hl.2.2.1, hh, e]
  abel
theorem corresponds_opposite {b : BondAtLevel L m K n} {b' : BondAtLevel L m' K' n'}
    (hl : Corresponds f c c' b b') : Corresponds f c c' b.opposite b'.opposite :=
  ⟨(doubleBlockSymmetricSet c).opposite_mem b hl.1,
    (doubleBlockSymmetricSet c').opposite_mem b' hl.2.1, hl.2.2.2, hl.2.2.1⟩
theorem isPositivelyOriented_iff {b : BondAtLevel L m K n} {b' : BondAtLevel L m' K' n'}
    (hl : Corresponds f c c' b b') : b.IsPositivelyOriented ↔ b'.IsPositivelyOriented := by
  refine ⟨C.isPositivelyOriented_of_corresponds hl, fun h => ?_⟩
  by_contra hnp
  exact C.codomain.refinement.not_isPositivelyOriented_both b' h
    (C.isPositivelyOriented_of_corresponds (C.corresponds_opposite hl)
      (Bond.opposite_isPositivelyOriented hnp))
theorem twistedConfig_agree {a : LieBondField (doubleBlockSymmetricSet c)}
    {a' : LieBondField (doubleBlockSymmetricSet c')} (ha : FieldsAgreeInChart f a a')
    {W : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    {W' : BondAtLevel L m' K' n' → Matrices.ComplexMatrix2} (hW : AgreeOn f c c' W W') :
    AgreeOn f c c' (twistedConfig c a W) (twistedConfig c' a' W') := by
  intro b b' hl
  have hv : ∀ {u : BondAtLevel L m K n} {u' : BondAtLevel L m' K' n'}, Corresponds f c c' u u' →
      ((a'.eval u' : ↥Matrices.ComplexMatrix2.traceless) : Matrices.ComplexMatrix2) = a.eval u :=
    fun {u u'} h => congrArg _ (ha u h.1 u' h.2.1 h.2.2.1 h.2.2.2)
  simp only [twistedConfig, expTwist]
  by_cases hb : b.IsPositivelyOriented
  · rw [if_pos hb, if_pos ((C.isPositivelyOriented_iff hl).1 hb), hv hl, hW _ _ hl]
  · have hr := C.corresponds_opposite hl
    rw [if_neg hb, if_neg (mt (C.isPositivelyOriented_iff hl).2 hb), hv hr, hW _ _ hr]
theorem expField_agree {a : LieBondField (doubleBlockSymmetricSet c)}
    {a' : LieBondField (doubleBlockSymmetricSet c')} (ha : FieldsAgreeInChart f a a') :
    AgreeOn f c c' (expOfBondField c a) (expOfBondField c' a') :=
  C.twistedConfig_agree ha fun _ _ _ => rfl
theorem stepLog_eq (s : AveragingScheme) {a : LieBondField (doubleBlockSymmetricSet c)}
    {a' : LieBondField (doubleBlockSymmetricSet c')} (ha : FieldsAgreeInChart f a a')
    {W : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    {W' : BondAtLevel L m' K' n' → Matrices.ComplexMatrix2}
    (hW : AgreeOn f c c' W W') {y : SiteAtLevel L m K (n + 1)} {y' : SiteAtLevel L m' K' (n' + 1)}
    (hp : EndpointPair c c' y y') {x : SiteAtLevel L m K n}
    (hx : (x : FourTorus L m) ∈ unitBlock y) :
    stepLog s c' a' W' y' (f x) = stepLog s c a W y x := by
  unfold stepLog stepRatio
  rw [C.contourHolonomy_eq s (C.twistedConfig_agree ha hW) hp hx, C.contourHolonomy_eq s hW hp hx]
theorem stepGauge_eq (s : AveragingScheme) {a : LieBondField (doubleBlockSymmetricSet c)}
    {a' : LieBondField (doubleBlockSymmetricSet c')} (ha : FieldsAgreeInChart f a a')
    {W : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    {W' : BondAtLevel L m' K' n' → Matrices.ComplexMatrix2}
    (hW : AgreeOn f c c' W W') {y : SiteAtLevel L m K (n + 1)} {y' : SiteAtLevel L m' K' (n' + 1)}
    (hp : EndpointPair c c' y y') : stepGauge s c' a' W' y' = stepGauge s c a W y := by
  have h : ∑ᶠ x ∈ sitesInBlock (levelDepth K n) y, stepLog s c a W y x =
      ∑ᶠ x ∈ sitesInBlock (levelDepth K' n') y', stepLog s c' a' W' y' x :=
    finsum_mem_eq_of_bijOn f (C.bijOn_sitesInBlock hp) fun x hx =>
      (C.stepLog_eq s ha hW hp hx).symm
  unfold stepGauge
  rw [h]
theorem stepVariable_eq (s : AveragingScheme) {a : LieBondField (doubleBlockSymmetricSet c)}
    {a' : LieBondField (doubleBlockSymmetricSet c')} (ha : FieldsAgreeInChart f a a')
    {W : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    {W' : BondAtLevel L m' K' n' → Matrices.ComplexMatrix2}
    (hW : AgreeOn f c c' W W') : stepVariable s c' a' W' = stepVariable s c a W := by
  unfold stepVariable stepProduct
  rw [C.stepGauge_eq s ha hW C.sourcePair, C.stepGauge_eq s ha hW C.targetPair,
    C.schemeBlockAverage_eq s (C.twistedConfig_agree ha hW), C.schemeBlockAverage_eq s hW]
end ChartData
end Chart
theorem stepObjectsChartInvariant_of (hq : StandardPartitionCubeGeometry)
    (hC : DoubleBlock.DoubleBlockContoursStatement) : StepObjectsChartInvariant := by
  intro L hL r _ m K n m' K' n' hm hn hm' hn' s μ c c' f hc hc' hf a₀ a a₀' a' _ _ ha₀ ha
  have C : ChartData c c' f μ :=
    ⟨doubleBlockData hq hC hL.1 hL.2 hm hn c μ hc, doubleBlockData hq hC hL.1 hL.2 hm' hn' c' μ hc',
      hf⟩
  have hW := C.expField_agree ha₀
  refine ⟨fun y y' hp x hx => C.stepLog_eq s ha hW hp hx, fun y y' hp => ?_,
    C.stepVariable_eq s ha hW, ?_⟩
  · unfold stepGaugeLogarithm
    rw [C.stepGauge_eq s ha hW hp]
  · unfold schemeAverageLog
    rw [C.schemeBlockAverage_eq s hW]
end YangMills.Construction.PeriodicLattice.ChartInvariance
