import YangMills.Construction.DirichletOperator.AveragedFormOnAScaledLattice
import YangMills.Construction.RegionSequence.AvgOpWeightFormula
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.BareDilation.AveragedFormReadsCentered
section
variable {N : ℕ}
def intPoint (s : PeriodicLattice.Mesh N) (a : Fin 4 → ℤ) : PeriodicLattice.GridPoint 4 s :=
  ∑ μ, a μ • s.basisStep μ
theorem intPoint_coe (s : PeriodicLattice.Mesh N) (a : Fin 4 → ℤ) (μ : Fin 4) :
    ((intPoint s a : PeriodicLattice.GridPoint 4 s) : PeriodicLattice.Torus 4 N) μ =
      (((a μ : ℝ) * s.h : ℝ) : AddCircle (N : ℝ)) := by
  simp only [intPoint, AddSubgroup.val_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single μ]
  · have h : ((a μ • s.basisStep μ : PeriodicLattice.GridPoint 4 s) : PeriodicLattice.Torus 4 N) μ =
        a μ • ((s.h : ℝ) : AddCircle (N : ℝ)) := by
      simp [PeriodicLattice.Mesh.basisStep, PeriodicLattice.axisMultiple]
    rw [h, ← AddCircle.coe_zsmul, zsmul_eq_mul]
  · intro ν _ hν
    simp [PeriodicLattice.Mesh.basisStep, PeriodicLattice.axisMultiple, Pi.single_eq_of_ne hν.symm]
  · simp
theorem site_ext (s : PeriodicLattice.Mesh N) {x y : PeriodicLattice.GridPoint 4 s}
    (h : ∀ μ, (x : PeriodicLattice.Torus 4 N) μ = (y : PeriodicLattice.Torus 4 N) μ) : x = y :=
  Subtype.ext (funext h)
theorem intPoint_add (s : PeriodicLattice.Mesh N) (a b : Fin 4 → ℤ) :
    intPoint s (a + b) = intPoint s a + intPoint s b := by
  simp only [intPoint, Pi.add_apply, add_smul, Finset.sum_add_distrib]
theorem intPoint_sub (s : PeriodicLattice.Mesh N) (a b : Fin 4 → ℤ) :
    intPoint s (a - b) = intPoint s a - intPoint s b := by
  simp only [intPoint, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
theorem exists_eq_intPoint (s : PeriodicLattice.Mesh N) (x : PeriodicLattice.GridPoint 4 s) :
    ∃ a, x = intPoint s a := by
  have h (μ : Fin 4) : ∃ k : ℤ, k • ((s.h : ℝ) : AddCircle (N : ℝ)) =
      (x : PeriodicLattice.Torus 4 N) μ :=
    AddSubgroup.mem_zmultiples_iff.mp (x.2 μ (mem_univ μ))
  choose k hk using h
  refine ⟨k, site_ext s fun μ => ?_⟩
  rw [intPoint_coe, ← hk μ, ← AddCircle.coe_zsmul, zsmul_eq_mul]
theorem exists_int_of_coe_eq (s : PeriodicLattice.Mesh N) {w : ℝ} {a : ℤ}
    (h : ((w : ℝ) : AddCircle (N : ℝ)) = (((a : ℝ) * s.h : ℝ) : AddCircle (N : ℝ))) :
    ∃ K : ℤ, w = (K : ℝ) * s.h ∧ ∃ n : ℤ, K = a + n * s.count := by
  have h0 : (((w - (a : ℝ) * s.h : ℝ)) : AddCircle (N : ℝ)) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (N : ℝ)).1 h0
  refine ⟨a + n * s.count, ?_, n, rfl⟩
  rw [zsmul_eq_mul, s.period_eq] at hn
  push_cast
  linarith
theorem intPoint_eq_of_modEq (s : PeriodicLattice.Mesh N) {a b : Fin 4 → ℤ}
    (h : ∀ μ, ∃ n : ℤ, b μ = a μ + n * s.count) : intPoint s b = intPoint s a := by
  refine site_ext s fun μ => ?_
  obtain ⟨n, hn⟩ := h μ
  rw [intPoint_coe, intPoint_coe, hn]
  have h0 : ((((n : ℝ) * s.count * s.h : ℝ)) : AddCircle (N : ℝ)) = 0 := by
    refine (AddCircle.coe_eq_zero_iff (N : ℝ)).2 ⟨n, ?_⟩
    rw [zsmul_eq_mul, s.period_eq]
    ring
  push_cast
  rw [add_mul, AddCircle.coe_add, h0, add_zero]
theorem modEq_of_intPoint_eq (s : PeriodicLattice.Mesh N) {a b : Fin 4 → ℤ}
    (h : intPoint s b = intPoint s a) (μ : Fin 4) :
    ∃ n : ℤ, b μ = a μ + n * s.count := by
  have hc : (((b μ : ℝ) * s.h : ℝ) : AddCircle (N : ℝ)) = (((a μ : ℝ) * s.h : ℝ) : AddCircle (N : ℝ)) := by
    rw [← intPoint_coe, ← intPoint_coe, h]
  obtain ⟨K, hK, n, hn⟩ := exists_int_of_coe_eq s hc
  refine ⟨n, ?_⟩
  have hh := s.h_pos.ne'
  have : (b μ : ℝ) = K := mul_right_cancel₀ hh hK
  have : b μ = K := by exact_mod_cast this
  omega
theorem nsmul_diagSum (s : PeriodicLattice.Mesh N) (k : ℕ) :
    k • (PeriodicLattice.diagSum s : PeriodicLattice.GridPoint 4 s) =
      intPoint s fun _ => (k : ℤ) := by
  simp only [intPoint, PeriodicLattice.diagSum, Finset.smul_sum, natCast_zsmul]
theorem shift_mem_halfOpenCube_iff (s : PeriodicLattice.Mesh N) {P : ℕ} (hP : Odd P)
    (x u : PeriodicLattice.GridPoint 4 s) :
    ((x + ((P - 1) / 2) • (PeriodicLattice.diagSum s : PeriodicLattice.GridPoint 4 s) :
        PeriodicLattice.GridPoint 4 s) : PeriodicLattice.Torus 4 N) ∈
      PeriodicLattice.halfOpenCube (u : PeriodicLattice.Torus 4 N) ((P : ℝ) * s.h) ↔
    ∃ d : Fin 4 → ℤ, (∀ μ, 2 * |d μ| < P) ∧ x = u + intPoint s d := by
  obtain ⟨c, hc⟩ := hP
  have hcP : (P - 1) / 2 = c := by omega
  rw [hcP, nsmul_diagSum]
  have hh := s.h_pos
  constructor
  · rintro ⟨w, hw, hv⟩
    obtain ⟨a, ha⟩ := exists_eq_intPoint s (x + intPoint s (fun _ => (c : ℤ)) - u)
    have hwa (μ : Fin 4) : ((w μ : ℝ) : AddCircle (N : ℝ)) = (((a μ : ℝ) * s.h : ℝ) : AddCircle (N : ℝ)) := by
      rw [← intPoint_coe, ← ha]
      have := congrFun hv μ
      simp only [AddSubgroup.coe_sub, AddSubgroup.coe_add, Pi.sub_apply, Pi.add_apply] at this ⊢
      rw [this]
      abel
    choose K hK n hn using fun μ => exists_int_of_coe_eq s (hwa μ)
    have hb (μ : Fin 4) : 0 ≤ K μ ∧ K μ < P := by
      have h1 := (hw μ).1
      have h2 := (hw μ).2
      rw [hK μ] at h1 h2
      have h1' : (0 : ℝ) ≤ K μ := nonneg_of_mul_nonneg_left h1 hh
      have h2' : (K μ : ℝ) < P := lt_of_mul_lt_mul_right h2 hh.le
      exact ⟨by exact_mod_cast h1', by exact_mod_cast h2'⟩
    refine ⟨K - fun _ => (c : ℤ), fun μ => ?_, ?_⟩
    · have := hb μ
      simp only [Pi.sub_apply]
      rcases abs_cases (K μ - (c : ℤ)) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    · have h1 : intPoint s K = intPoint s a := intPoint_eq_of_modEq s fun μ => ⟨n μ, hn μ⟩
      rw [intPoint_sub, h1, ← ha]
      abel
  · rintro ⟨d, hd, rfl⟩
    refine ⟨fun μ => ((d μ + c : ℤ) : ℝ) * s.h, fun μ => ?_, ?_⟩
    · have h3 := hd μ
      have h4 : -(c : ℤ) ≤ d μ ∧ d μ ≤ c := by
        rcases abs_cases (d μ) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
      have h5 : (0 : ℝ) ≤ ((d μ + c : ℤ) : ℝ) := by exact_mod_cast (by omega : 0 ≤ d μ + c)
      have h6 : ((d μ + c : ℤ) : ℝ) < P := by exact_mod_cast (by omega : d μ + c < P)
      exact ⟨mul_nonneg h5 hh.le, mul_lt_mul_of_pos_right h6 hh⟩
    · funext μ
      simp only [AddSubgroup.coe_add, Pi.add_apply]
      rw [intPoint_coe, intPoint_coe, add_assoc, ← AddCircle.coe_add]
      congr 2
      push_cast
      ring
end
section
variable {j N : ℕ} {𝒯 : RegionSequence.NestedRegions} {S : PeriodicLattice.Scales 4 𝒯.L j N} {r : ℝ}
theorem dilateEquiv_intPoint (R : DilationData 𝒯 S r) (s : PeriodicLattice.Mesh N) (a : Fin 4 → ℤ) :
    R.dilateEquiv (intPoint s a : PeriodicLattice.Torus 4 N) =
      Torus.torusProj 4 𝒯.side fun μ => (a μ : ℝ) * (r * s.h) := by
  funext μ
  change AddCircle.equivAddCircle (N : ℝ) 𝒯.side R.period_ne_zero R.side_ne_zero
      ((intPoint s a : PeriodicLattice.Torus 4 N) μ) = _
  rw [intPoint_coe, AddCircle.equivAddCircle_apply_mk]
  have hN := R.period_ne_zero
  change (((a μ : ℝ) * s.h * ((N : ℝ)⁻¹ * 𝒯.side) : ℝ) : AddCircle 𝒯.side) = _
  congr 1
  change _ = (a μ : ℝ) * (r * s.h)
  rw [R.side_eq]
  field_simp
theorem mem_sublattice_iff (R : DilationData 𝒯 S r) (s : PeriodicLattice.Mesh N) {σ : ℝ}
    (hσ : σ = r * s.h) (u : PeriodicLattice.Torus 4 N) :
    u ∈ PeriodicLattice.gridSubgroup 4 s ↔ R.dilateEquiv u ∈ Torus.spacingLattice 4 𝒯.side σ := by
  constructor
  · intro hu
    obtain ⟨a, ha⟩ := exists_eq_intPoint s ⟨u, hu⟩
    have h : u = intPoint s a := congrArg Subtype.val ha
    rw [h, dilateEquiv_intPoint]
    exact ⟨a, by rw [hσ]⟩
  · rintro ⟨k, hk⟩
    have h : u = intPoint s k := R.dilateEquiv.injective (by
      rw [hk, dilateEquiv_intPoint, hσ])
    rw [h]
    exact (intPoint s k).2
def siteEquivOf (R : DilationData 𝒯 S r) (s : PeriodicLattice.Mesh N) {σ : ℝ} (hσ : σ = r * s.h) :
    PeriodicLattice.GridPoint 4 s ≃ Dirichlet.LatticeSite 4 𝒯.side σ :=
  R.dilateEquiv.toEquiv.subtypeEquiv (mem_sublattice_iff R s hσ)
def linkEquivOf (R : DilationData 𝒯 S r) (s : PeriodicLattice.Mesh N) {σ : ℝ} (hσ : σ = r * s.h) :
    PeriodicLattice.Link 4 s ≃ Dirichlet.LatticeBond 4 𝒯.side σ where
  toFun q := ⟨siteEquivOf R s hσ q.2, q.1⟩
  invFun b := (b.dir, (siteEquivOf R s hσ).symm b.source)
  left_inv q := by simp
  right_inv b := by simp
theorem dilateEquiv_axisMultiple (R : DilationData 𝒯 S r) (s : PeriodicLattice.Mesh N) {σ : ℝ}
    (hσ : σ = r * s.h) (μ : Fin 4) :
    R.dilateEquiv (PeriodicLattice.axisMultiple μ s.h) =
      (Dirichlet.unitStep 4 𝒯.side σ μ : Torus.PeriodicTorus 4 𝒯.side) := by
  funext ν
  change AddCircle.equivAddCircle (N : ℝ) 𝒯.side R.period_ne_zero R.side_ne_zero
      (PeriodicLattice.axisMultiple μ s.h ν) = ((Pi.single μ σ : Fin 4 → ℝ) ν : AddCircle 𝒯.side)
  by_cases h : ν = μ
  · subst h
    simp only [PeriodicLattice.axisMultiple, Pi.single_eq_same]
    rw [AddCircle.equivAddCircle_apply_mk]
    have hN := R.period_ne_zero
    change ((s.h * ((N : ℝ)⁻¹ * 𝒯.side) : ℝ) : AddCircle 𝒯.side) = _
    congr 1
    rw [hσ, R.side_eq]
    field_simp
  · simp [PeriodicLattice.axisMultiple, Pi.single_eq_of_ne h]
theorem linkEquivOf_target (R : DilationData 𝒯 S r) (s : PeriodicLattice.Mesh N) {σ : ℝ}
    (hσ : σ = r * s.h) (q : PeriodicLattice.Link 4 s) :
    (((linkEquivOf R s hσ q).target : Dirichlet.LatticeSite 4 𝒯.side σ) :
        Torus.PeriodicTorus 4 𝒯.side) =
      R.dilateEquiv (PeriodicLattice.Link.target q : PeriodicLattice.Torus 4 N) := by
  change R.dilateEquiv (q.2 : PeriodicLattice.Torus 4 N) +
      (Dirichlet.unitStep 4 𝒯.side σ q.1 : Torus.PeriodicTorus 4 𝒯.side) =
    R.dilateEquiv ((q.2 : PeriodicLattice.Torus 4 N) + PeriodicLattice.axisMultiple q.1 s.h)
  rw [map_add, dilateEquiv_axisMultiple R s hσ]
theorem supNorm_sub_le_iff (R : DilationData 𝒯 S r) (s : PeriodicLattice.Mesh N) {P : ℕ}
    (hP : Odd P) (x u : PeriodicLattice.GridPoint 4 s) :
    Torus.supNorm (R.dilateEquiv (x : PeriodicLattice.Torus 4 N) -
        R.dilateEquiv (u : PeriodicLattice.Torus 4 N)) ≤ r * ((P : ℝ) * s.h) / 2 ↔
      ∃ d : Fin 4 → ℤ, (∀ μ, 2 * |d μ| < P) ∧ x = u + intPoint s d := by
  have hr := R.scale_pos
  have hh := s.h_pos
  have hrh : 0 < r * s.h := mul_pos hr hh
  obtain ⟨c, hc⟩ := hP
  obtain ⟨a, ha⟩ := exists_eq_intPoint s (x - u)
  have hdiff : R.dilateEquiv (x : PeriodicLattice.Torus 4 N) -
      R.dilateEquiv (u : PeriodicLattice.Torus 4 N) =
      Torus.torusProj 4 𝒯.side fun μ => (a μ : ℝ) * (r * s.h) := by
    rw [← map_sub, ← dilateEquiv_intPoint, ← ha]
    rfl
  constructor
  · intro hs
    have hlt : Torus.supNorm (R.dilateEquiv (x : PeriodicLattice.Torus 4 N) -
        R.dilateEquiv (u : PeriodicLattice.Torus 4 N)) < r * ((P : ℝ) * s.h) / 2 + r * s.h / 2 := by
      linarith
    rw [Torus.supNorm] at hlt
    obtain ⟨t, ⟨v, hv, rfl⟩, ht⟩ := exists_lt_of_csInf_lt (by exact ⟨_, _, hdiff.symm, rfl⟩) hlt
    have hK (μ : Fin 4) : ∃ K : ℤ, v μ = (K : ℝ) * (r * s.h) ∧ ∃ n : ℤ, K = a μ + n * s.count := by
      have hvμ : ((v μ : ℝ) : AddCircle 𝒯.side) = (((a μ : ℝ) * (r * s.h) : ℝ) : AddCircle 𝒯.side) := by
        rw [hdiff] at hv
        exact congrFun hv μ
      have h0 : (((v μ - (a μ : ℝ) * (r * s.h) : ℝ)) : AddCircle 𝒯.side) = 0 := by
        rw [AddCircle.coe_sub, hvμ, sub_self]
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff 𝒯.side).1 h0
      refine ⟨a μ + n * s.count, ?_, n, rfl⟩
      rw [zsmul_eq_mul, R.side_eq, s.period_eq] at hn
      push_cast
      linarith
    choose K hK n hn using hK
    refine ⟨K, fun μ => ?_, ?_⟩
    · have h1 : |v μ| < r * ((P : ℝ) * s.h) / 2 + r * s.h / 2 :=
        lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using norm_le_pi_norm v μ) ht
      rw [hK μ, abs_mul, abs_of_pos hrh] at h1
      have h2 : 2 * |(K μ : ℝ)| < (P : ℝ) + 1 := by
        have : 2 * |(K μ : ℝ)| * (r * s.h) < ((P : ℝ) + 1) * (r * s.h) := by nlinarith
        exact lt_of_mul_lt_mul_right this hrh.le
      have h3 : 2 * |K μ| < (P : ℤ) + 1 := by
        have : ((2 * |K μ| : ℤ) : ℝ) < (((P : ℤ) + 1 : ℤ) : ℝ) := by
          push_cast
          exact h2
        exact_mod_cast this
      omega
    · have h1 : intPoint s K = intPoint s a :=
        intPoint_eq_of_modEq s fun μ => ⟨n μ, hn μ⟩
      rw [h1, ← ha]
      abel
  · rintro ⟨d, hd, hx⟩
    have h1 : R.dilateEquiv (x : PeriodicLattice.Torus 4 N) -
        R.dilateEquiv (u : PeriodicLattice.Torus 4 N) =
        Torus.torusProj 4 𝒯.side fun μ => (d μ : ℝ) * (r * s.h) := by
      rw [← map_sub, ← dilateEquiv_intPoint R s d]
      congr 1
      rw [hx]
      simp
    rw [h1, Torus.supNorm]
    have hb : BddBelow {t | ∃ v : Fin 4 → ℝ, Torus.torusProj 4 𝒯.side v =
        Torus.torusProj 4 𝒯.side (fun μ => (d μ : ℝ) * (r * s.h)) ∧ t = ‖v‖} :=
      ⟨0, by
        rintro _ ⟨v, _, rfl⟩
        exact norm_nonneg v⟩
    refine (csInf_le hb ⟨_, rfl, rfl⟩).trans ?_
    · have hPos : 0 ≤ r * ((P : ℝ) * s.h) / 2 := by positivity
      refine (pi_norm_le_iff_of_nonneg hPos).2 fun μ => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hrh]
      have h2 : (2 : ℝ) * |(d μ : ℝ)| ≤ P := by
        have := (hd μ).le
        exact_mod_cast this
      nlinarith
theorem odd_L_pow (i : ℕ) : Odd (𝒯.L ^ i) := 𝒯.odd_L.pow
theorem L_ne_zero : (𝒯.L : ℝ) ≠ 0 := by
  have := 𝒯.thirteen_le_L
  exact_mod_cast (by omega : 𝒯.L ≠ 0)
theorem mem_centeredFineCell (x : PeriodicLattice.GridPoint 4 S.fineMesh)
    (y : PeriodicLattice.GridPoint 4 S.unitMesh) :
    x ∈ S.centeredFineCell y ↔
      ∃ d : Fin 4 → ℤ, (∀ μ, 2 * |d μ| < ((𝒯.L ^ j : ℕ) : ℤ)) ∧
        x = S.unitToFine y + intPoint S.fineMesh d := by
  have hbox := shift_mem_halfOpenCube_iff S.fineMesh (odd_L_pow (𝒯 := 𝒯) j) x (S.unitToFine y)
  have hone : (((𝒯.L ^ j : ℕ) : ℝ)) * S.fineMesh.h = 1 := by
    change (((𝒯.L ^ j : ℕ) : ℝ)) * PeriodicLattice.fineScale 𝒯.L j = 1
    have := pow_ne_zero j (L_ne_zero (𝒯 := 𝒯))
    rw [PeriodicLattice.fineScale]
    push_cast
    field_simp
  rw [hone] at hbox
  rw [← hbox]
  simp only [PeriodicLattice.Scales.centeredFineCell, Finset.mem_map_equiv,
    PeriodicLattice.Scales.fineCell, PeriodicLattice.sitesInCube, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rfl
theorem mem_centeredCoarseCell (y : PeriodicLattice.GridPoint 4 S.unitMesh)
    (y' : PeriodicLattice.GridPoint 4 S.coarseMesh) :
    y ∈ S.centeredCoarseCell y' ↔
      ∃ d : Fin 4 → ℤ, (∀ μ, 2 * |d μ| < (𝒯.L : ℤ)) ∧
        y = S.coarseToUnit y' + intPoint S.unitMesh d := by
  have hbox := shift_mem_halfOpenCube_iff S.unitMesh 𝒯.odd_L y (S.coarseToUnit y')
  have hone : (𝒯.L : ℝ) * S.unitMesh.h = 𝒯.L := by
    change (𝒯.L : ℝ) * 1 = 𝒯.L
    ring
  rw [hone] at hbox
  rw [← hbox]
  simp only [PeriodicLattice.Scales.centeredCoarseCell, Finset.mem_map_equiv,
    PeriodicLattice.Scales.coarseCell, PeriodicLattice.sitesInCube, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rfl
theorem coarseToUnit_intPoint (a : Fin 4 → ℤ) :
    S.coarseToUnit (intPoint S.coarseMesh a) =
      intPoint S.unitMesh fun μ => (𝒯.L : ℤ) * a μ := by
  refine site_ext S.unitMesh fun μ => ?_
  change ((intPoint S.coarseMesh a : PeriodicLattice.GridPoint 4 S.coarseMesh) :
    PeriodicLattice.Torus 4 N) μ = _
  rw [intPoint_coe, intPoint_coe]
  congr 1
  change (a μ : ℝ) * (𝒯.L : ℝ) = (((𝒯.L : ℤ) * a μ : ℤ) : ℝ) * 1
  push_cast
  ring
theorem unitToFine_intPoint (a : Fin 4 → ℤ) :
    S.unitToFine (intPoint S.unitMesh a) =
      intPoint S.fineMesh fun μ => ((𝒯.L ^ j : ℕ) : ℤ) * a μ := by
  refine site_ext S.fineMesh fun μ => ?_
  change ((intPoint S.unitMesh a : PeriodicLattice.GridPoint 4 S.unitMesh) :
    PeriodicLattice.Torus 4 N) μ = _
  rw [intPoint_coe, intPoint_coe]
  congr 1
  change (a μ : ℝ) * 1 =
    ((((𝒯.L ^ j : ℕ) : ℤ) * a μ : ℤ) : ℝ) * PeriodicLattice.fineScale 𝒯.L j
  have := pow_ne_zero j (L_ne_zero (𝒯 := 𝒯))
  rw [PeriodicLattice.fineScale]
  push_cast
  field_simp
theorem scale_eq_unit (R : DilationData 𝒯 S r) : 𝒯.scale j = r * S.unitMesh.h := by
  have := pow_ne_zero j (L_ne_zero (𝒯 := 𝒯))
  simp only [scale, Torus.scaleSpacing, zpow_natCast]
  rw [R.mesh_eq]
  change (𝒯.L : ℝ) ^ j * (r * PeriodicLattice.fineScale 𝒯.L j) = r * 1
  rw [PeriodicLattice.fineScale]
  field_simp
theorem scale_succ_eq_coarse (R : DilationData 𝒯 S r) :
    𝒯.scale (j + 1) = r * S.coarseMesh.h := by
  have := pow_ne_zero j (L_ne_zero (𝒯 := 𝒯))
  simp only [scale, Torus.scaleSpacing, zpow_natCast]
  rw [R.mesh_eq]
  change (𝒯.L : ℝ) ^ (j + 1) * (r * PeriodicLattice.fineScale 𝒯.L j) = r * 𝒯.L
  rw [PeriodicLattice.fineScale, pow_succ]
  field_simp
theorem mem_centeredCoarseCell_iff_cubeAt (R : DilationData 𝒯 S r)
    (y : PeriodicLattice.GridPoint 4 S.unitMesh) (y' : PeriodicLattice.GridPoint 4 S.coarseMesh) :
    y ∈ S.centeredCoarseCell y' ↔
      R.dilateEquiv (y : PeriodicLattice.Torus 4 N) ∈
        Torus.cubeAt (R.dilateEquiv (y' : PeriodicLattice.Torus 4 N)) (𝒯.scale (j + 1)) := by
  have h := supNorm_sub_le_iff R S.unitMesh 𝒯.odd_L y (S.coarseToUnit y')
  have hσ : r * ((𝒯.L : ℝ) * S.unitMesh.h) = 𝒯.scale (j + 1) := by
    rw [scale_succ_eq_coarse R]
    change r * ((𝒯.L : ℝ) * 1) = r * 𝒯.L
    ring
  rw [hσ] at h
  rw [mem_centeredCoarseCell]
  exact h.symm
theorem mem_centeredFineCell_iff_cubeAt (R : DilationData 𝒯 S r)
    (x : PeriodicLattice.GridPoint 4 S.fineMesh) (y : PeriodicLattice.GridPoint 4 S.unitMesh) :
    x ∈ S.centeredFineCell y ↔
      R.dilateEquiv (x : PeriodicLattice.Torus 4 N) ∈
        Torus.cubeAt (R.dilateEquiv (y : PeriodicLattice.Torus 4 N)) (𝒯.scale j) := by
  have h := supNorm_sub_le_iff R S.fineMesh (odd_L_pow (𝒯 := 𝒯) j) x (S.unitToFine y)
  have hσ : r * (((𝒯.L ^ j : ℕ) : ℝ) * S.fineMesh.h) = 𝒯.scale j := by
    rw [scale_eq_unit R]
    change r * (((𝒯.L ^ j : ℕ) : ℝ) * PeriodicLattice.fineScale 𝒯.L j) = r * 1
    have := pow_ne_zero j (L_ne_zero (𝒯 := 𝒯))
    rw [PeriodicLattice.fineScale]
    push_cast
    field_simp
  rw [hσ] at h
  rw [mem_centeredFineCell]
  exact h.symm
theorem eq_of_coarseToUnit_eq_add {y' y₀ : PeriodicLattice.GridPoint 4 S.coarseMesh}
    {d : Fin 4 → ℤ} (hd : ∀ μ, 2 * |d μ| < (𝒯.L : ℤ))
    (h : S.coarseToUnit y' = S.coarseToUnit y₀ + intPoint S.unitMesh d) : y' = y₀ := by
  obtain ⟨a, rfl⟩ := exists_eq_intPoint S.coarseMesh y'
  obtain ⟨b, rfl⟩ := exists_eq_intPoint S.coarseMesh y₀
  rw [coarseToUnit_intPoint, coarseToUnit_intPoint, ← intPoint_add] at h
  obtain ⟨k, hk, hN⟩ := S.even_multiple
  have hzero (μ : Fin 4) : d μ = 0 := by
    obtain ⟨n, hn⟩ := modEq_of_intPoint_eq S.unitMesh h μ
    have hp : (S.unitMesh.count : ℤ) = 2 * k * 𝒯.L := by
      change ((N : ℕ) : ℤ) = _
      rw [hN]
      push_cast
      ring
    simp only [Pi.add_apply] at hn
    rw [hp] at hn
    refine Int.eq_zero_of_abs_lt_dvd (m := (𝒯.L : ℤ)) ⟨a μ - b μ - n * (2 * k), ?_⟩ ?_
    · linear_combination -hn
    · have := hd μ
      have := abs_nonneg (d μ)
      omega
  have hd0 : intPoint S.unitMesh d = 0 := by
    have : d = 0 := funext hzero
    rw [this]
    simp [intPoint]
  rw [intPoint_add, hd0, add_zero] at h
  have h2 : S.coarseToUnit (intPoint S.coarseMesh a) = S.coarseToUnit (intPoint S.coarseMesh b) := by
    rw [coarseToUnit_intPoint, coarseToUnit_intPoint]
    exact h
  exact Subtype.ext
    (congrArg (fun z : PeriodicLattice.GridPoint 4 S.unitMesh => (z : PeriodicLattice.Torus 4 N)) h2)
theorem mem_centeredRegion_iff (R : DilationData 𝒯 S r) (hl : TwoLayered 𝒯 j)
    (y : PeriodicLattice.GridPoint 4 S.unitMesh) :
    y ∈ S.centeredRegion R.coarseTrace ↔
      R.dilateEquiv (y : PeriodicLattice.Torus 4 N) ∈ 𝒯.Ω (j + 1) := by
  obtain ⟨𝒞, h𝒞, hΩ⟩ := 𝒯.isCubeUnion_Ω (j + 1) hl.top_eq.ge
  have hcube {Q : Set 𝒯.Point} (hQ : Q ∈ 𝒞) : ∃ y₀ : PeriodicLattice.GridPoint 4 S.coarseMesh,
      Q = Torus.cubeAt (R.dilateEquiv (y₀ : PeriodicLattice.Torus 4 N)) (𝒯.scale (j + 1)) := by
    obtain ⟨c, hc, rfl⟩ := h𝒞 hQ
    have hc' : R.dilateEquiv (R.dilateEquiv.symm c) ∈
        Torus.spacingLattice 4 𝒯.side (𝒯.scale (j + 1)) := by
      rw [AddEquiv.apply_symm_apply]
      exact hc
    have hm := (mem_sublattice_iff R S.coarseMesh (scale_succ_eq_coarse R) _).2 hc'
    refine ⟨⟨_, hm⟩, ?_⟩
    simp only [AddEquiv.apply_symm_apply]
    rfl
  have hsub {Q : Set 𝒯.Point} (hQ : Q ∈ 𝒞) : Q ⊆ 𝒯.Ω (j + 1) := by
    rw [hΩ]
    exact subset_sUnion_of_mem hQ
  simp only [PeriodicLattice.Scales.centeredRegion, mem_iUnion, Finset.mem_coe, exists_prop]
  constructor
  · rintro ⟨y', hy', hy⟩
    have hp : R.dilateEquiv (y' : PeriodicLattice.Torus 4 N) ∈ 𝒯.Ω (j + 1) := hy'
    rw [hΩ] at hp
    obtain ⟨Q, hQ, hpQ⟩ := hp
    obtain ⟨y₀, rfl⟩ := hcube hQ
    have h1 : S.coarseToUnit y' ∈ S.centeredCoarseCell y₀ :=
      (mem_centeredCoarseCell_iff_cubeAt R _ _).2 hpQ
    obtain ⟨d, hd, h2⟩ := (mem_centeredCoarseCell _ _).1 h1
    have h3 := eq_of_coarseToUnit_eq_add hd h2
    subst h3
    exact hsub hQ ((mem_centeredCoarseCell_iff_cubeAt R _ _).1 hy)
  · intro hp
    rw [hΩ] at hp
    obtain ⟨Q, hQ, hpQ⟩ := hp
    obtain ⟨y₀, rfl⟩ := hcube hQ
    refine ⟨y₀, ?_, (mem_centeredCoarseCell_iff_cubeAt R _ _).2 hpQ⟩
    have h1 : S.coarseToUnit y₀ ∈ S.centeredCoarseCell y₀ := by
      refine (mem_centeredCoarseCell _ _).2 ⟨0, fun μ => ?_, ?_⟩
      · have := 𝒯.thirteen_le_L
        simp only [Pi.zero_apply, abs_zero]
        omega
      · simp [intPoint]
    exact hsub hQ ((mem_centeredCoarseCell_iff_cubeAt R _ _).1 h1)
theorem coarseBonds_eq_empty_of_lt (hl : TwoLayered 𝒯 j) {n : ℕ} (hn : n < j) :
    𝒯.coarseBonds n = ∅ := by
  ext c
  simp only [NestedRegions.coarseBonds, mem_ofPred_eq, mem_empty_iff_false, iff_false]
  intro hc
  split_ifs at hc with h0
  · obtain ⟨b, _, _, _, h1, _⟩ := hc
    exact h1 (by rw [hl.lower_eq_univ 1 (by omega)]; trivial)
  · exact hc.2.1 (by rw [hl.lower_eq_univ (n + 1) (by omega)]; trivial)
theorem exists_bond_of_eq_scale {T σ σ' : ℝ} (h : σ = σ') (c : Dirichlet.LatticeBond 4 T σ) :
    ∃ b : Dirichlet.LatticeBond 4 T σ', (b.source : Torus.PeriodicTorus 4 T) = c.source ∧
      b.dir = c.dir ∧
      (b.target : Torus.PeriodicTorus 4 T) = c.target := by
  subst h
  exact ⟨c, rfl, rfl, rfl⟩
theorem target_eq_of_eq_scale {T σ σ' : ℝ} (h : σ = σ') (c : Dirichlet.LatticeBond 4 T σ)
    (b : Dirichlet.LatticeBond 4 T σ') (ht : (b.source : Torus.PeriodicTorus 4 T) = c.source)
    (hd : b.dir = c.dir) :
    (b.target : Torus.PeriodicTorus 4 T) = c.target := by
  subst h
  have : b = c := by
    obtain ⟨t, μ⟩ := b
    obtain ⟨t', μ'⟩ := c
    have h1 : t = t' := Subtype.ext ht
    simp_all
  rw [this]
theorem mem_coarseBonds_level (hl : TwoLayered 𝒯 j) (c : 𝒯.BondAt j) :
    c ∈ 𝒯.coarseBonds j ↔
      (c.source : 𝒯.Point) ∉ 𝒯.Ω (j + 1) ∧ (c.target : 𝒯.Point) ∉ 𝒯.Ω (j + 1) := by
  by_cases h0 : j = 0
  · subst h0
    have hs : 𝒯.scale 0 = 𝒯.ξ := by simp [scale, Torus.scaleSpacing]
    simp only [NestedRegions.coarseBonds, mem_ofPred_eq, if_true, zero_add]
    constructor
    · rintro ⟨b, _, ht, hd, h1, h2⟩
      rw [← ht, ← target_eq_of_eq_scale hs c b ht hd]
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨b, ht, hd, hh⟩ := exists_bond_of_eq_scale hs c
      refine ⟨b, by rw [hl.bonds_eq_univ]; trivial, ht, hd, ?_, ?_⟩
      · rw [ht]
        exact h1
      · rw [hh]
        exact h2
  · simp only [NestedRegions.coarseBonds, mem_ofPred_eq, if_neg h0, hl.lower_eq_univ j le_rfl,
      mem_univ, true_or, true_and]
theorem mem_coarseBonds_succ (hl : TwoLayered 𝒯 j) (c : 𝒯.BondAt (j + 1)) :
    c ∈ 𝒯.coarseBonds (j + 1) ↔
      (c.source : 𝒯.Point) ∈ 𝒯.Ω (j + 1) ∨ (c.target : 𝒯.Point) ∈ 𝒯.Ω (j + 1) := by
  have h : 𝒯.Ω (j + 1 + 1) = ∅ := 𝒯.Ω_eq_empty _ (by rw [hl.top_eq]; omega)
  simp only [NestedRegions.coarseBonds, mem_ofPred_eq, Nat.succ_ne_zero, if_false, h,
    mem_empty_iff_false, not_false_eq_true, and_true]
theorem finsum_fineBlock_eq_sum (R : DilationData 𝒯 S r) (n : ℕ) (p : 𝒯.Point)
    (F : Finset (PeriodicLattice.GridPoint 4 S.fineMesh))
    (hF : ∀ x, x ∈ F ↔ R.dilateEquiv (x : PeriodicLattice.Torus 4 N) ∈
      Torus.cubeAt p (𝒯.scale n)) (G : 𝒯.FineSite → ℝ) :
    ∑ᶠ x ∈ 𝒯.fineBlock n p, G x = ∑ x ∈ F, G (R.fineSiteEquiv ⟨x⟩) := by
  let e : PeriodicLattice.GridPoint 4 S.fineMesh ≃ 𝒯.FineSite :=
    (PeriodicLattice.DilatedSite.equivSite S.fineMesh r).symm.trans R.fineSiteEquiv
  have hset : 𝒯.fineBlock n p =
      ((F.map e.toEmbedding : Finset 𝒯.FineSite) : Set 𝒯.FineSite) := by
    ext b
    obtain ⟨x, rfl⟩ := e.surjective b
    simp only [Finset.coe_map, Equiv.coe_toEmbedding, mem_image, Finset.mem_coe,
      EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
    rw [hF]
    rfl
  rw [hset, finsum_mem_coe_finset, Finset.sum_map]
  rfl
theorem pathBond_fineSiteEquiv (R : DilationData 𝒯 S r) (μ : Fin 4)
    (x : PeriodicLattice.GridPoint 4 S.fineMesh) (i : ℕ) :
    pathBond μ (R.fineSiteEquiv ⟨x⟩) i =
      ⟨R.fineSiteEquiv ⟨x + i • S.fineMesh.basisStep μ⟩, μ⟩ := by
  have h : R.fineSiteEquiv ⟨x⟩ + i • Dirichlet.unitStep 4 𝒯.side 𝒯.ξ μ =
      R.fineSiteEquiv ⟨x + i • S.fineMesh.basisStep μ⟩ := by
    apply Subtype.ext
    change R.dilateEquiv (x : PeriodicLattice.Torus 4 N) +
        i • (Dirichlet.unitStep 4 𝒯.side 𝒯.ξ μ : 𝒯.Point) =
      R.dilateEquiv ((x : PeriodicLattice.Torus 4 N) +
        i • PeriodicLattice.axisMultiple μ S.fineMesh.h)
    rw [map_add, map_nsmul, dilateEquiv_axisMultiple R S.fineMesh (σ := 𝒯.ξ) R.mesh_eq]
  rw [pathBond, h]
theorem bondAvg_level (R : DilationData 𝒯 S r) (A : 𝒯.FineBond → ℝ)
    (q : PeriodicLattice.Link 4 S.unitMesh) :
    bondAvg j A (linkEquivOf R S.unitMesh (scale_eq_unit R) q) =
      S.centeredFineFormAvg
        (PeriodicLattice.dilateFieldEquiv S.fineMesh r (Fin 4) (R.pullBond A)) q := by
  obtain ⟨μ, y⟩ := q
  have hb : 𝒯.fineBlock j (((linkEquivOf R S.unitMesh (scale_eq_unit R) (μ, y)).source :
      Dirichlet.LatticeSite 4 𝒯.side (𝒯.scale j)) : 𝒯.Point) =
      𝒯.fineBlock j (R.dilateEquiv (y : PeriodicLattice.Torus 4 N)) := rfl
  have hc : ((𝒯.L : ℝ) ^ (j * (4 + 1)))⁻¹ =
      PeriodicLattice.fineScale 𝒯.L j ^ 4 * PeriodicLattice.fineScale 𝒯.L j := by
    rw [PeriodicLattice.fineScale, ← pow_succ, inv_pow, ← pow_mul]
  rw [bondAvg, hb, finsum_fineBlock_eq_sum R j _ (S.centeredFineCell y)
    (fun x => mem_centeredFineCell_iff_cubeAt R x y)]
  change _ * _ = ∑ x ∈ S.centeredFineCell y, PeriodicLattice.fineScale 𝒯.L j ^ 4 *
    ∑ t ∈ Finset.range (𝒯.L ^ j), PeriodicLattice.fineScale 𝒯.L j *
      A ⟨R.fineSiteEquiv ⟨x + t • S.fineMesh.basisStep μ⟩, μ⟩
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_sum, hc, mul_assoc]
  congr 2
  exact Finset.sum_congr rfl fun i _ => by rw [pathBond_fineSiteEquiv]; rfl
theorem sum_range_mul_eq (a b : ℕ) (H : ℕ → ℝ) :
    ∑ i ∈ Finset.range (b * a), H i =
      ∑ t ∈ Finset.range a, ∑ t' ∈ Finset.range b, H (t * b + t') := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, Nat.mul_comm b a]
theorem unitToFine_basisStep (μ : Fin 4) :
    S.unitToFine (S.unitMesh.basisStep μ) = (𝒯.L ^ j) • S.fineMesh.basisStep μ := by
  refine site_ext S.fineMesh fun ν => ?_
  change PeriodicLattice.axisMultiple μ S.unitMesh.h ν =
    (𝒯.L ^ j) • PeriodicLattice.axisMultiple μ S.fineMesh.h ν
  by_cases h : ν = μ
  · subst h
    simp only [PeriodicLattice.axisMultiple, Pi.single_eq_same]
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
    congr 1
    change (1 : ℝ) = ((𝒯.L ^ j : ℕ) : ℝ) * PeriodicLattice.fineScale 𝒯.L j
    have := pow_ne_zero j (L_ne_zero (𝒯 := 𝒯))
    rw [PeriodicLattice.fineScale]
    push_cast
    field_simp
  · simp [PeriodicLattice.axisMultiple, Pi.single_eq_of_ne h]
theorem sum_centeredFineCell_translate (y : PeriodicLattice.GridPoint 4 S.unitMesh) (μ : Fin 4)
    (t : ℕ) (G : PeriodicLattice.GridPoint 4 S.fineMesh → ℝ) :
    ∑ x ∈ S.centeredFineCell (y + t • S.unitMesh.basisStep μ), G x =
      ∑ x ∈ S.centeredFineCell y, G (x + (t * 𝒯.L ^ j) • S.fineMesh.basisStep μ) := by
  have hι : S.unitToFine (y + t • S.unitMesh.basisStep μ) =
      S.unitToFine y + (t * 𝒯.L ^ j) • S.fineMesh.basisStep μ := by
    rw [map_add, map_nsmul, unitToFine_basisStep, smul_smul]
  symm
  refine Finset.sum_equiv (Equiv.addRight ((t * 𝒯.L ^ j) • S.fineMesh.basisStep μ)) (fun x => ?_)
    (fun _ _ => rfl)
  simp only [mem_centeredFineCell, hι, Equiv.coe_addRight]
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d, hd, by abel⟩
  · rintro ⟨d, hd, h⟩
    refine ⟨d, hd, ?_⟩
    have : x + (t * 𝒯.L ^ j) • S.fineMesh.basisStep μ =
        (S.unitToFine y + intPoint S.fineMesh d) + (t * 𝒯.L ^ j) • S.fineMesh.basisStep μ := by
      rw [h]
      abel
    exact add_right_cancel this
theorem mem_iUnion_fineCells_iff (x : PeriodicLattice.GridPoint 4 S.fineMesh)
    (y' : PeriodicLattice.GridPoint 4 S.coarseMesh) :
    (∃ y ∈ S.centeredCoarseCell y', x ∈ S.centeredFineCell y) ↔
      ∃ D : Fin 4 → ℤ, (∀ μ, 2 * |D μ| < ((𝒯.L ^ (j + 1) : ℕ) : ℤ)) ∧
        x = S.unitToFine (S.coarseToUnit y') + intPoint S.fineMesh D := by
  set P : ℤ := ((𝒯.L ^ j : ℕ) : ℤ) with hP
  set L : ℤ := (𝒯.L : ℤ) with hL
  have hPL : ((𝒯.L ^ (j + 1) : ℕ) : ℤ) = L * P := by
    rw [hP, hL]
    push_cast
    ring
  have hPpos : 0 < P := by
    have : 0 < 𝒯.L ^ j := Nat.pow_pos (by have := 𝒯.thirteen_le_L; omega)
    rw [hP]
    exact_mod_cast this
  rw [hPL]
  constructor
  · rintro ⟨y, hy, hx⟩
    obtain ⟨d', hd', rfl⟩ := (mem_centeredCoarseCell _ _).1 hy
    obtain ⟨d, hd, rfl⟩ := (mem_centeredFineCell _ _).1 hx
    refine ⟨(fun μ => P * d' μ) + d, fun μ => ?_, ?_⟩
    · have h1 := hd μ
      have h2 := hd' μ
      have h3 : |P * d' μ + d μ| ≤ P * |d' μ| + |d μ| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos hPpos]
      simp only [Pi.add_apply]
      have h4 : P * (2 * |d' μ| + 1) ≤ P * L := mul_le_mul_of_nonneg_left (by omega) hPpos.le
      nlinarith
    · rw [map_add, add_assoc, intPoint_add, unitToFine_intPoint]
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨cL, hcL⟩ := 𝒯.odd_L
    obtain ⟨cP, hcP⟩ := odd_L_pow (𝒯 := 𝒯) j
    have hL2 : L = 2 * cL + 1 := by
      rw [hL, hcL]
      push_cast
      ring
    have hP2 : P = 2 * cP + 1 := by
      rw [hP, hcP]
      push_cast
      ring
    let E : Fin 4 → ℤ := fun μ => D μ + (cL * P + cP)
    have hE (μ : Fin 4) : 0 ≤ E μ ∧ E μ < L * P := by
      have h1 := hD μ
      have h2 : L * P = 2 * (cL * P + cP) + 1 := by
        rw [hL2]
        linear_combination hP2
      rcases abs_cases (D μ) with ⟨h, _⟩ | ⟨h, _⟩ <;> constructor <;> simp only [E] <;> omega
    let a : Fin 4 → ℤ := fun μ => E μ / P - cL
    let b : Fin 4 → ℤ := fun μ => E μ % P - cP
    have hab (μ : Fin 4) : D μ = P * a μ + b μ := by
      have := Int.mul_ediv_add_emod (E μ) P
      simp only [a, b]
      simp only [E] at this ⊢
      linear_combination -this
    have hy : S.coarseToUnit y' + intPoint S.unitMesh a ∈ S.centeredCoarseCell y' :=
      (mem_centeredCoarseCell _ _).2 ⟨a, fun μ => ?_, rfl⟩
    refine ⟨_, hy, (mem_centeredFineCell _ _).2 ⟨b, fun μ => ?_, ?_⟩⟩
    · have h1 : 0 ≤ E μ % P := Int.emod_nonneg _ hPpos.ne'
      have h2 : E μ % P < P := Int.emod_lt_of_pos _ hPpos
      simp only [b]
      rcases abs_cases (E μ % P - (cP : ℤ)) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    · have hD' : D = (fun μ => P * a μ) + b := funext hab
      rw [hD', intPoint_add, map_add, unitToFine_intPoint, add_assoc]
    · have h1 : 0 ≤ E μ / P := Int.ediv_nonneg (hE μ).1 hPpos.le
      have h2 : E μ / P < L := Int.ediv_lt_of_lt_mul hPpos (hE μ).2
      simp only [a]
      rcases abs_cases (E μ / P - (cL : ℤ)) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
theorem disjoint_centeredFineCell {y₁ y₂ : PeriodicLattice.GridPoint 4 S.unitMesh} (h : y₁ ≠ y₂) :
    Disjoint (S.centeredFineCell y₁) (S.centeredFineCell y₂) := by
  rw [Finset.disjoint_left]
  intro x h₁ h₂
  obtain ⟨d₁, hd₁, hx₁⟩ := (mem_centeredFineCell _ _).1 h₁
  obtain ⟨d₂, hd₂, hx₂⟩ := (mem_centeredFineCell _ _).1 h₂
  obtain ⟨a₁, ha₁⟩ := exists_eq_intPoint S.unitMesh y₁
  obtain ⟨a₂, ha₂⟩ := exists_eq_intPoint S.unitMesh y₂
  have heq : intPoint S.fineMesh ((fun μ => ((𝒯.L ^ j : ℕ) : ℤ) * a₁ μ) + d₁) =
      intPoint S.fineMesh ((fun μ => ((𝒯.L ^ j : ℕ) : ℤ) * a₂ μ) + d₂) := by
    rw [intPoint_add, intPoint_add, ← unitToFine_intPoint, ← unitToFine_intPoint,
      ← ha₁, ← ha₂, ← hx₁, ← hx₂]
  have hzero (μ : Fin 4) : d₁ μ - d₂ μ = 0 := by
    obtain ⟨n, hn⟩ := modEq_of_intPoint_eq S.fineMesh heq μ
    simp only [Pi.add_apply] at hn
    have hp : (S.fineMesh.count : ℤ) = N * ((𝒯.L ^ j : ℕ) : ℤ) := by
      change ((N * 𝒯.L ^ j : ℕ) : ℤ) = _
      push_cast
      ring
    rw [hp] at hn
    refine Int.eq_zero_of_abs_lt_dvd (m := ((𝒯.L ^ j : ℕ) : ℤ))
      ⟨a₂ μ - a₁ μ + n * N, ?_⟩ ?_
    · linear_combination hn
    · have h1 := hd₁ μ
      have h2 := hd₂ μ
      rcases abs_cases (d₁ μ) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
        rcases abs_cases (d₂ μ) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
        rcases abs_cases (d₁ μ - d₂ μ) with ⟨e3, _⟩ | ⟨e3, _⟩ <;> omega
  have hd : d₁ = d₂ := funext fun μ => sub_eq_zero.1 (hzero μ)
  subst hd
  have h3 : S.unitToFine y₁ = S.unitToFine y₂ := add_right_cancel (hx₁.symm.trans hx₂)
  exact h (Subtype.ext
    (congrArg (fun z : PeriodicLattice.GridPoint 4 S.fineMesh => (z : PeriodicLattice.Torus 4 N)) h3))
theorem bondAvg_succ (R : DilationData 𝒯 S r) (A : 𝒯.FineBond → ℝ)
    (q : PeriodicLattice.Link 4 S.coarseMesh) :
    bondAvg (j + 1) A (linkEquivOf R S.coarseMesh (scale_succ_eq_coarse R) q) =
      S.centeredCoarseFormAvg (S.centeredFineFormAvg
        (PeriodicLattice.dilateFieldEquiv S.fineMesh r (Fin 4) (R.pullBond A))) q := by
  classical
  obtain ⟨μ, y'⟩ := q
  have hb : 𝒯.fineBlock (j + 1)
      (((linkEquivOf R S.coarseMesh (scale_succ_eq_coarse R) (μ, y')).source :
        Dirichlet.LatticeSite 4 𝒯.side (𝒯.scale (j + 1))) : 𝒯.Point) =
      𝒯.fineBlock (j + 1) (R.dilateEquiv (y' : PeriodicLattice.Torus 4 N)) := rfl
  have hmem (x : PeriodicLattice.GridPoint 4 S.fineMesh) :
      x ∈ (S.centeredCoarseCell y').biUnion S.centeredFineCell ↔
        R.dilateEquiv (x : PeriodicLattice.Torus 4 N) ∈
          Torus.cubeAt (R.dilateEquiv (y' : PeriodicLattice.Torus 4 N)) (𝒯.scale (j + 1)) := by
    have h := supNorm_sub_le_iff R S.fineMesh (odd_L_pow (𝒯 := 𝒯) (j + 1)) x
      (S.unitToFine (S.coarseToUnit y'))
    have hσ : r * (((𝒯.L ^ (j + 1) : ℕ) : ℝ) * S.fineMesh.h) = 𝒯.scale (j + 1) := by
      rw [scale_succ_eq_coarse R]
      change r * (((𝒯.L ^ (j + 1) : ℕ) : ℝ) * PeriodicLattice.fineScale 𝒯.L j) = r * 𝒯.L
      have := pow_ne_zero j (L_ne_zero (𝒯 := 𝒯))
      rw [PeriodicLattice.fineScale]
      push_cast
      rw [pow_succ]
      field_simp
    rw [hσ] at h
    rw [Finset.mem_biUnion]
    exact (mem_iUnion_fineCells_iff x y').trans h.symm
  set T : PeriodicLattice.GridPoint 4 S.fineMesh → ℝ := fun x =>
    ∑ i ∈ Finset.range (𝒯.L ^ (j + 1)),
      A ⟨R.fineSiteEquiv ⟨x + i • S.fineMesh.basisStep μ⟩, μ⟩ with hT
  have hleft : bondAvg (j + 1) A (linkEquivOf R S.coarseMesh (scale_succ_eq_coarse R) (μ, y')) =
      ((𝒯.L : ℝ) ^ ((j + 1) * (4 + 1)))⁻¹ *
        ∑ y ∈ S.centeredCoarseCell y', ∑ x ∈ S.centeredFineCell y, T x := by
    rw [bondAvg, hb, finsum_fineBlock_eq_sum R (j + 1) _ _ hmem, Finset.sum_biUnion
      (fun y₁ _ y₂ _ h => disjoint_centeredFineCell h)]
    congr 1
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun i _ => ?_
    rw [pathBond_fineSiteEquiv]
    rfl
  have hinner (y : PeriodicLattice.GridPoint 4 S.unitMesh) :
      ∑ t ∈ Finset.range 𝒯.L, (𝒯.L : ℝ)⁻¹ *
        S.centeredFineFormAvg
          (PeriodicLattice.dilateFieldEquiv S.fineMesh r (Fin 4) (R.pullBond A))
          (μ, y + t • S.unitMesh.basisStep μ) =
      (𝒯.L : ℝ)⁻¹ * (PeriodicLattice.fineScale 𝒯.L j ^ 4 * PeriodicLattice.fineScale 𝒯.L j) *
        ∑ x ∈ S.centeredFineCell y, T x := by
    have h1 (t : ℕ) : S.centeredFineFormAvg
        (PeriodicLattice.dilateFieldEquiv S.fineMesh r (Fin 4) (R.pullBond A))
        (μ, y + t • S.unitMesh.basisStep μ) =
        PeriodicLattice.fineScale 𝒯.L j ^ 4 * PeriodicLattice.fineScale 𝒯.L j *
          ∑ x ∈ S.centeredFineCell y, ∑ t' ∈ Finset.range (𝒯.L ^ j),
            A ⟨R.fineSiteEquiv ⟨x + (t * 𝒯.L ^ j + t') • S.fineMesh.basisStep μ⟩, μ⟩ := by
      change ∑ x ∈ S.centeredFineCell (y + t • S.unitMesh.basisStep μ),
        PeriodicLattice.fineScale 𝒯.L j ^ 4 *
          ∑ t' ∈ Finset.range (𝒯.L ^ j), PeriodicLattice.fineScale 𝒯.L j *
            A ⟨R.fineSiteEquiv ⟨x + t' • S.fineMesh.basisStep μ⟩, μ⟩ = _
      rw [sum_centeredFineCell_translate y μ t fun x => PeriodicLattice.fineScale 𝒯.L j ^ 4 *
        ∑ t' ∈ Finset.range (𝒯.L ^ j), PeriodicLattice.fineScale 𝒯.L j *
          A ⟨R.fineSiteEquiv ⟨x + t' • S.fineMesh.basisStep μ⟩, μ⟩, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.mul_sum, mul_assoc]
      congr 2
      refine Finset.sum_congr rfl fun t' _ => ?_
      rw [add_smul, add_assoc]
    have h2 (x : PeriodicLattice.GridPoint 4 S.fineMesh) : T x = ∑ t ∈ Finset.range 𝒯.L,
        ∑ t' ∈ Finset.range (𝒯.L ^ j),
          A ⟨R.fineSiteEquiv ⟨x + (t * 𝒯.L ^ j + t') • S.fineMesh.basisStep μ⟩, μ⟩ := by
      rw [hT]
      simp only
      rw [pow_succ, sum_range_mul_eq 𝒯.L (𝒯.L ^ j)
        fun i => A ⟨R.fineSiteEquiv ⟨x + i • S.fineMesh.basisStep μ⟩, μ⟩]
    simp only [h1, h2]
    have h3 : ∑ x ∈ S.centeredFineCell y, ∑ t ∈ Finset.range 𝒯.L,
        ∑ t' ∈ Finset.range (𝒯.L ^ j),
          A ⟨R.fineSiteEquiv ⟨x + (t * 𝒯.L ^ j + t') • S.fineMesh.basisStep μ⟩, μ⟩ =
        ∑ t ∈ Finset.range 𝒯.L, ∑ x ∈ S.centeredFineCell y,
          ∑ t' ∈ Finset.range (𝒯.L ^ j),
            A ⟨R.fineSiteEquiv ⟨x + (t * 𝒯.L ^ j + t') • S.fineMesh.basisStep μ⟩, μ⟩ :=
      Finset.sum_comm
    rw [h3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  have hright : S.centeredCoarseFormAvg (S.centeredFineFormAvg
      (PeriodicLattice.dilateFieldEquiv S.fineMesh r (Fin 4) (R.pullBond A))) (μ, y') =
      ∑ y ∈ S.centeredCoarseCell y', ((𝒯.L : ℝ) ^ 4)⁻¹ *
        ∑ t ∈ Finset.range 𝒯.L, (𝒯.L : ℝ)⁻¹ *
          S.centeredFineFormAvg
            (PeriodicLattice.dilateFieldEquiv S.fineMesh r (Fin 4) (R.pullBond A))
            (μ, y + t • S.unitMesh.basisStep μ) := rfl
  rw [hleft, hright, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hinner, ← mul_assoc, ← mul_assoc]
  congr 1
  have := pow_ne_zero j (L_ne_zero (𝒯 := 𝒯))
  have := L_ne_zero (𝒯 := 𝒯)
  rw [PeriodicLattice.fineScale]
  field_simp
  ring
theorem finsum_mem_eq_sum_filter {α β : Type} [Fintype α] (e : α ≃ β) (X : Set β) (Y : Set α)
    [DecidablePred (· ∈ Y)] (h : ∀ q, e q ∈ X ↔ q ∈ Y) (f : β → ℝ) :
    ∑ᶠ c ∈ X, f c = ∑ q with q ∈ Y, f (e q) := by
  rw [finsum_mem_def, ← finsum_comp_equiv e, finsum_eq_sum_of_fintype, Finset.sum_filter]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : q ∈ Y
  · rw [if_pos hq, indicator_of_mem ((h q).2 hq)]
  · rw [if_neg hq, indicator_of_notMem fun hc => hq ((h q).1 hc)]
theorem bondInner_avgOp_eq (h : RegionSequence.AvgOpByWeights) (R : DilationData 𝒯 S r)
    (hl : TwoLayered 𝒯 j) (A : 𝒯.FineBond → ℝ) :
    bondInner A (avgOp A) =
      centeredAvgPart S R.coarseTrace r ((𝒯.L : ℝ) * r) 1 (R.pullBond A) := by
  classical
  have hA : A ∈ 𝒯.oneForms := fun b hb => absurd (by rw [hl.bonds_eq_univ]; trivial) hb
  have hform := ((h 𝒯).2 A).2.1 A hA
  have hcomm : bondInner A (avgOp A) = bondInner (avgOp A) A := by
    simp only [bondInner, mul_comm]
  have hlow : ∑ n ∈ Finset.range j, ∑ᶠ c ∈ 𝒯.coarseBonds n,
      gaugeParam * 𝒯.scale n ^ (4 - 2) * |bondAvg n A c| ^ 2 = 0 :=
    Finset.sum_eq_zero fun n hn => by
      rw [coarseBonds_eq_empty_of_lt hl (Finset.mem_range.1 hn)]
      simp
  have hrow₁ (q : PeriodicLattice.Link 4 S.unitMesh) :
      linkEquivOf R S.unitMesh (scale_eq_unit R) q ∈ 𝒯.coarseBonds j ↔
        q ∈ PeriodicLattice.linksAvoiding (S.centeredRegion R.coarseTrace) := by
    rw [mem_coarseBonds_level hl, linkEquivOf_target]
    simp only [PeriodicLattice.linksAvoiding, mem_ofPred_eq, mem_centeredRegion_iff R hl]
    rfl
  have hrow₂ (q : PeriodicLattice.Link 4 S.coarseMesh) :
      linkEquivOf R S.coarseMesh (scale_succ_eq_coarse R) q ∈ 𝒯.coarseBonds (j + 1) ↔
        q ∈ PeriodicLattice.linksMeeting R.coarseTrace := by
    rw [mem_coarseBonds_succ hl, linkEquivOf_target]
    rfl
  rw [hcomm, hform, avgForm_self, hl.top_eq, Finset.sum_range_succ, Finset.sum_range_succ,
    hlow, zero_add, finsum_mem_eq_sum_filter (linkEquivOf R S.unitMesh (scale_eq_unit R)) _ _ hrow₁,
    finsum_mem_eq_sum_filter (linkEquivOf R S.coarseMesh (scale_succ_eq_coarse R)) _ _ hrow₂]
  simp only [bondAvg_level, bondAvg_succ]
  rw [centeredAvgPart, ← Finset.mul_sum, ← Finset.mul_sum, scale_eq_unit R, scale_succ_eq_coarse R]
  have h₁ : S.unitMesh.h = 1 := rfl
  have h₂ : S.coarseMesh.h = 𝒯.L := rfl
  have h₃ : gaugeParam = 1 := rfl
  rw [h₁, h₂, h₃]
  ring
end
theorem holds (h : RegionSequence.AvgOpByWeights) : BareDilation.AveragedFormReadsCentered := by
  intro L j N 𝒯 S r R hl A
  obtain rfl := R.blockFactor_eq
  exact bondInner_avgOp_eq h R hl A
end YangMills.Construction.BareDilation.AveragedFormReadsCentered
