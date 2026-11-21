import YangMills.Construction.SourcesAndGluing.StandingDataAndSigns
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace SourcesAndGluing
section Links
variable {L : ℕ}
theorem meshSize_pos (hL : 0 < L) (K : ℕ) : 0 < PeriodicLattice.meshSize L (K : ℤ) :=
  zpow_pos (by exact_mod_cast hL) _
theorem torusSide_eq_intCast_mul_meshSize (hL : 0 < L) (m K : ℕ) :
    PeriodicLattice.torusSide L m =
      ((2 * (L : ℤ) ^ (m + K) : ℤ) : ℝ) * PeriodicLattice.meshSize L (K : ℤ) := by
  simp only [PeriodicLattice.torusSide, PeriodicLattice.meshSize, Int.cast_mul, Int.cast_pow,
    Int.cast_ofNat, Int.cast_natCast, zpow_neg, zpow_natCast, pow_add]
  field_simp
theorem unitStep_ne_zero (hL : 0 < L) (m K : ℕ) (μ : Fin 4) :
    PeriodicLattice.unitStep L m (K : ℤ) μ ≠ 0 := by
  intro h
  have h1 : ((PeriodicLattice.unitStep L m (K : ℤ) μ : PeriodicLattice.Site L m (K : ℤ)) :
      PeriodicLattice.FourTorus L m) μ = 0 := by
    rw [h]
    rfl
  have h2 : ((PeriodicLattice.meshSize L (K : ℤ) : ℝ) :
      AddCircle (PeriodicLattice.torusSide L m)) = 0 := by
    simpa [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis] using h1
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).mp h2
  rw [torusSide_eq_intCast_mul_meshSize hL m K, zsmul_eq_mul, ← mul_assoc] at hn
  have h3 : (n : ℝ) * ((2 * (L : ℤ) ^ (m + K) : ℤ) : ℝ) = 1 :=
    mul_right_cancel₀ (meshSize_pos hL K).ne' (by rw [hn, one_mul])
  have h4 : n * (2 * (L : ℤ) ^ (m + K)) = 1 := by exact_mod_cast h3
  have h5 : 2 * (n * (L : ℤ) ^ (m + K)) = 1 := by linarith
  omega
theorem torusEuclidNorm_torusProj_le {S : ℝ} (v : Fin 4 → ℝ) :
    TorusMetric.torusEuclidNorm (TorusMetric.torusProj S v) ≤ TorusMetric.euclidNormVec v :=
  csInf_le ⟨0, by rintro _ ⟨w, -, rfl⟩; exact Real.sqrt_nonneg _⟩ ⟨v, rfl, rfl⟩
theorem torusEuclidNorm_target_sub_source_le (hL : 0 < L) {m K : ℕ}
    (b : PeriodicLattice.Bond L m (K : ℤ)) :
    TorusMetric.torusEuclidNorm ((b.target : PeriodicLattice.FourTorus L m) -
        (b.source : PeriodicLattice.FourTorus L m)) ≤
      PeriodicLattice.meshSize L (K : ℤ) := by
  have ha := meshSize_pos hL K
  obtain ⟨μ, h | h⟩ := b.isNeighbour
  · have hc : (b.target : PeriodicLattice.FourTorus L m) -
          (b.source : PeriodicLattice.FourTorus L m) =
        TorusMetric.torusProj (PeriodicLattice.torusSide L m)
          (Pi.single μ (PeriodicLattice.meshSize L (K : ℤ))) := by
      have h' := congrArg (fun d : PeriodicLattice.Site L m (K : ℤ) =>
        (d : PeriodicLattice.FourTorus L m)) h
      refine h'.trans (funext fun ν => ?_)
      by_cases hν : ν = μ
      · subst hν
        simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, TorusMetric.torusProj]
      · simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, TorusMetric.torusProj,
          Pi.single_eq_of_ne hν]
    rw [hc]
    refine (torusEuclidNorm_torusProj_le _).trans ?_
    rw [InfiniteLattice.euclidNormVec_single, abs_of_pos ha]
  · have hc : (b.target : PeriodicLattice.FourTorus L m) -
          (b.source : PeriodicLattice.FourTorus L m) =
        TorusMetric.torusProj (PeriodicLattice.torusSide L m)
          (Pi.single μ (-PeriodicLattice.meshSize L (K : ℤ))) := by
      have h' := congrArg (fun d : PeriodicLattice.Site L m (K : ℤ) =>
        (d : PeriodicLattice.FourTorus L m)) h
      refine h'.trans (funext fun ν => ?_)
      by_cases hν : ν = μ
      · subst hν
        simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, TorusMetric.torusProj]
      · simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, TorusMetric.torusProj,
          Pi.single_eq_of_ne hν]
    rw [hc]
    refine (torusEuclidNorm_torusProj_le _).trans ?_
    rw [InfiniteLattice.euclidNormVec_single, abs_neg, abs_of_pos ha]
theorem eq_unitStep_or_neg_of_torusEuclidNorm_le (hL : 0 < L) {m K : ℕ}
    (d : PeriodicLattice.Site L m (K : ℤ)) (hd : d ≠ 0)
    (h : TorusMetric.torusEuclidNorm (d : PeriodicLattice.FourTorus L m) ≤
      PeriodicLattice.meshSize L (K : ℤ)) :
    ∃ μ : Fin 4, d = PeriodicLattice.unitStep L m (K : ℤ) μ ∨
      d = -PeriodicLattice.unitStep L m (K : ℤ) μ := by
  have ha := meshSize_pos hL K
  set a := PeriodicLattice.meshSize L (K : ℤ) with ha_def
  obtain ⟨n, hn⟩ := d.2
  have hlift : TorusMetric.torusProj (PeriodicLattice.torusSide L m) (fun μ => (n μ : ℝ) * a) =
      (d : PeriodicLattice.FourTorus L m) := funext fun μ => (hn μ).symm
  have hne : (TorusMetric.euclidNormVec ''
      (TorusMetric.torusProj (PeriodicLattice.torusSide L m) ⁻¹'
        {(d : PeriodicLattice.FourTorus L m)})).Nonempty :=
    ⟨_, _, hlift, rfl⟩
  have hsqrt : 1 < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hlt : TorusMetric.torusEuclidNorm (d : PeriodicLattice.FourTorus L m) < a * Real.sqrt 2 :=
    h.trans_lt (by nlinarith)
  obtain ⟨_, ⟨v, hv, rfl⟩, hvlt⟩ := exists_lt_of_csInf_lt hne hlt
  have hv' : TorusMetric.torusProj (PeriodicLattice.torusSide L m) v =
      TorusMetric.torusProj (PeriodicLattice.torusSide L m) (fun μ => (n μ : ℝ) * a) :=
    hv.trans hlift.symm
  obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq hv'
  let N : Fin 4 → ℤ := fun μ => n μ + 2 * (L : ℤ) ^ (m + K) * k μ
  have hvN : ∀ μ, v μ = (N μ : ℝ) * a := fun μ => by
    rw [hk]
    simp only [Pi.add_apply, TestFunctions.latticeTranslate,
      torusSide_eq_intCast_mul_meshSize hL m K, N]
    push_cast
    ring
  have hsq : ∑ μ, v μ ^ 2 < 2 * a ^ 2 := by
    have h1 := (Real.sqrt_lt' (mul_pos ha (by positivity))).mp hvlt
    rw [mul_pow, Real.sq_sqrt (by norm_num)] at h1
    linarith
  have hsum : ∑ μ, N μ ^ 2 < 2 := by
    have h1 : (∑ μ, (N μ : ℝ) ^ 2) * a ^ 2 < 2 * a ^ 2 := by
      rw [Finset.sum_mul]
      refine lt_of_eq_of_lt (Finset.sum_congr rfl fun μ _ => ?_) hsq
      rw [hvN μ, mul_pow]
    have h2 : ∑ μ, (N μ : ℝ) ^ 2 < 2 := lt_of_mul_lt_mul_right h1 (by positivity)
    exact_mod_cast h2
  have hnn : 0 ≤ ∑ μ, N μ ^ 2 := Finset.sum_nonneg fun μ _ => sq_nonneg _
  have hcover : ∀ ν, (d : PeriodicLattice.FourTorus L m) ν =
      (((N ν : ℝ) * a : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) := fun ν => by
    rw [← hvN ν]
    exact (congrFun hv ν).symm
  rcases (by omega : ∑ μ, N μ ^ 2 = 0 ∨ ∑ μ, N μ ^ 2 = 1) with h0 | h1
  · exfalso
    apply hd
    refine Subtype.ext (funext fun ν => ?_)
    have hz : N ν ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun μ _ => sq_nonneg (N μ)).mp h0 ν (Finset.mem_univ ν)
    have hz' : N ν = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hz
    rw [hcover ν, hz']
    simp
  · obtain ⟨μ, h1 | h1⟩ := InfiniteLattice.int_vec_unit_of_sum_sq_eq_one N h1
    · refine ⟨μ, Or.inl (Subtype.ext (funext fun ν => ?_))⟩
      rw [hcover ν, h1]
      by_cases hν : ν = μ
      · subst hν
        simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, ha_def]
      · simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hν]
    · refine ⟨μ, Or.inr (Subtype.ext (funext fun ν => ?_))⟩
      rw [hcover ν, h1]
      by_cases hν : ν = μ
      · subst hν
        simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, ha_def]
      · simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hν]
end Links
namespace GluingSetup
variable (D : GluingSetup)
structure TorusLatticeIsometry where
  toFun : D.Torus → D.Torus
  isIsometry : D.IsTorusIsometry toFun
  image_eq : toFun '' (D.periodicLattice : Set D.Torus) = D.periodicLattice
structure R4LatticeIsometry where
  toFun : (Fin 4 → ℝ) → Fin 4 → ℝ
  isIsometry : IsR4Isometry toFun
  image_eq : toFun '' (D.gridPoints : Set (Fin 4 → ℝ)) = D.gridPoints
variable {D}
namespace TorusLatticeIsometry
variable (r : D.TorusLatticeIsometry)
def toSymmetry : PeriodicLattice.TorusLatticeSymmetry D.L D.m D.K :=
  ⟨r.toFun, r.isIsometry.2, r.image_eq⟩
def toEquiv : D.Torus ≃ D.Torus := Equiv.ofBijective r.toFun r.isIsometry.1
theorem isSublatticeIsometry_toEquiv :
    PeriodicLattice.IsSublatticeIsometry ((D.K : ℕ) : ℤ) r.toEquiv :=
  ⟨r.isIsometry.2, r.image_eq⟩
def pointMap (x : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ)) :
    PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ) :=
  r.toSymmetry.pointMap x
theorem isNeighbour_pointMap (b : D.PeriodicLink) :
    ∃ μ : Fin 4, r.pointMap b.target - r.pointMap b.source =
        PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) μ ∨
      r.pointMap b.target - r.pointMap b.source =
        -PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) μ := by
  have hL : 0 < D.L := by
    have h := D.isAdmissible.2
    omega
  refine eq_unitStep_or_neg_of_torusEuclidNorm_le hL _ ?_ ?_
  · intro h
    have h1 : r.toFun b.target = r.toFun b.source :=
      sub_eq_zero.mp (congrArg (fun d : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ) =>
        (d : PeriodicLattice.FourTorus D.L D.m)) h)
    have h2 : b.target = b.source := Subtype.ext (r.isIsometry.1.1 h1)
    obtain ⟨μ, h3 | h3⟩ := b.isNeighbour
    · rw [h2, sub_self] at h3
      exact unitStep_ne_zero hL _ _ μ h3.symm
    · rw [h2, sub_self] at h3
      exact unitStep_ne_zero hL _ _ μ (neg_eq_zero.mp h3.symm)
  · have h1 : TorusMetric.torusEuclidNorm (r.toFun b.target - r.toFun b.source) =
        TorusMetric.torusEuclidNorm ((b.target : D.Torus) - (b.source : D.Torus)) :=
      r.isIsometry.2 b.target b.source
    exact h1.le.trans (torusEuclidNorm_target_sub_source_le hL b)
def linkMap (b : D.PeriodicLink) : D.PeriodicLink :=
  ⟨r.pointMap b.source, r.pointMap b.target, r.isNeighbour_pointMap b⟩
def pullbackField (U : D.PeriodicLink → Matrices.ComplexMatrix2) :
    D.PeriodicLink → Matrices.ComplexMatrix2 :=
  fun b => U (r.linkMap b)
def actOn {E : Type*} (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → E) :
    (D.PeriodicLink → Matrices.ComplexMatrix2) → E :=
  F ∘ r.pullbackField
theorem linkMap_source (b : D.PeriodicLink) :
    ((r.linkMap b).source : D.Torus) = r.toFun b.source := rfl
theorem linkMap_target (b : D.PeriodicLink) :
    ((r.linkMap b).target : D.Torus) = r.toFun b.target := rfl
theorem bondPreimage_symm (b : D.PeriodicLink) :
    PeriodicLattice.bondPreimage r.toEquiv.symm b = r.linkMap b := by
  have h : ∃ b' : D.PeriodicLink, (b'.source : D.Torus) = r.toEquiv.symm.symm b.source ∧
      (b'.target : D.Torus) = r.toEquiv.symm.symm b.target := ⟨r.linkMap b, rfl, rfl⟩
  rw [PeriodicLattice.bondPreimage, dif_pos h]
  exact PeriodicLattice.Bond.ext (Subtype.ext h.choose_spec.1) (Subtype.ext h.choose_spec.2)
theorem pullbackField_eq (U : D.PeriodicLink → Matrices.ComplexMatrix2) :
    r.pullbackField U = PeriodicLattice.transportGaugeField r.toEquiv.symm U :=
  funext fun b => congrArg U (r.bondPreimage_symm b).symm
theorem actOn_eq {E : Type*} (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → E) :
    r.actOn F = PeriodicLattice.transportObservable r.toEquiv F :=
  funext fun U => congrArg F (r.pullbackField_eq U)
end TorusLatticeIsometry
namespace R4LatticeIsometry
variable (r : D.R4LatticeIsometry)
def toLatticeSymmetry : InfiniteLattice.LatticeSymmetry D.mesh :=
  ⟨r.toFun, r.isIsometry.2, r.image_eq⟩
def linkMap (b : InfiniteLattice.Link D.mesh) : InfiniteLattice.Link D.mesh :=
  r.toLatticeSymmetry.linkMap b
def pullbackField (U : D.GridField) : D.GridField :=
  r.toLatticeSymmetry.pullbackField U
def actOn {E : Type*} (F : D.GridField → E) : D.GridField → E :=
  F ∘ r.pullbackField
end R4LatticeIsometry
end GluingSetup
end SourcesAndGluing
end YangMills.Construction
end
