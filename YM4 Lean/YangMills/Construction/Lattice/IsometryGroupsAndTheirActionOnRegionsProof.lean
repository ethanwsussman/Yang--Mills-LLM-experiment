import YangMills.Construction.Lattice.LatticeIsometriesAsMapsOfPairsProof
import YangMills.Construction.TorusOrFourSpace.StandingSignsOfTheSupportAdaptedFamily
import YangMills.Construction.Lattice.ComponentBoxIndependentOfCube
import YangMills.Construction.Lattice.IsometryCovarianceOfHolonomiesAndActionsProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.PeriodicLattice.IsometryAction
variable {L m : ℕ}
theorem unitCast_cases (s : ℤˣ) : ((s : ℤ) : ℝ) = 1 ∨ ((s : ℤ) : ℝ) = -1 := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp
theorem unitCast_mul_self (s : ℤˣ) : ((s : ℤ) : ℝ) * ((s : ℤ) : ℝ) = 1 := by
  rcases unitCast_cases s with h | h <;> rw [h] <;> norm_num
theorem abs_unitCast (s : ℤˣ) : |((s : ℤ) : ℝ)| = 1 := by
  rcases unitCast_cases s with h | h <;> rw [h] <;> norm_num
theorem actOnVector_apply (r : SignedFrame) (x : Fin 4 → ℝ) (μ : Fin 4) :
    r.actOnVector x μ = ((r.2 μ : ℤ) : ℝ) * x (r.1 μ) := rfl
theorem actOnVector_add (r : SignedFrame) (x y : Fin 4 → ℝ) :
    r.actOnVector (x + y) = r.actOnVector x + r.actOnVector y := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.actOnVector_add <;> assumption
theorem actOnVector_sub (r : SignedFrame) (x y : Fin 4 → ℝ) :
    r.actOnVector (x - y) = r.actOnVector x - r.actOnVector y := by
  funext μ
  simp only [actOnVector_apply, Pi.sub_apply]
  ring
theorem actOnVector_neg (r : SignedFrame) (x : Fin 4 → ℝ) :
    r.actOnVector (-x) = -r.actOnVector x := by apply _root_.YangMills.Construction.AffineTorusIsometries.signedFrame_act_neg <;> assumption
def frameComp (r₁ r₂ : SignedFrame) : SignedFrame := (r₂.1 * r₁.1, fun μ => r₁.2 μ * r₂.2 (r₁.1 μ))
def frameInverse (r : SignedFrame) : SignedFrame := (r.1⁻¹, fun ν => r.2 (r.1⁻¹ ν))
theorem frameComp_actOnVector (r₁ r₂ : SignedFrame) (x : Fin 4 → ℝ) :
    (frameComp r₁ r₂).actOnVector x = r₁.actOnVector (r₂.actOnVector x) := by
  funext μ
  simp only [actOnVector_apply, frameComp, Units.val_mul, Int.cast_mul, Equiv.Perm.coe_mul,
    Function.comp_apply]
  ring
theorem frameInverse_actOnVector_actOnVector (r : SignedFrame) (x : Fin 4 → ℝ) :
    (frameInverse r).actOnVector (r.actOnVector x) = x := by apply _root_.YangMills.Construction.PeriodicSpace.SupportAdapted.actOnVector_frameInv_actOnVector <;> assumption
theorem actOnVector_frameInverse_actOnVector (r : SignedFrame) (x : Fin 4 → ℝ) :
    r.actOnVector ((frameInverse r).actOnVector x) = x := by apply _root_.YangMills.Construction.PeriodicSpace.SupportAdapted.actOnVector_actOnVector_frameInv <;> assumption
theorem actOnVector_one (x : Fin 4 → ℝ) : (1 : SignedFrame).actOnVector x = x := by
  funext μ
  simp [actOnVector_apply]
theorem supNormVec_actOnVector (r : SignedFrame) (v : Fin 4 → ℝ) :
    supNormVec (r.actOnVector v) = supNormVec v := by
  unfold supNormVec
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun μ _ => ?_
    rw [actOnVector_apply, abs_mul, abs_unitCast, one_mul]
    exact Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ (r.1 μ))
  · refine Finset.sup'_le _ _ fun μ _ => ?_
    have h := Finset.le_sup' (fun ν => |r.actOnVector v ν|) (Finset.mem_univ (r.1⁻¹ μ))
    have e : |r.actOnVector v (r.1⁻¹ μ)| = |v μ| := by
      rw [actOnVector_apply, abs_mul, abs_unitCast, one_mul]
      simp
    exact le_trans (le_of_eq e.symm) h
theorem l1NormVec_actOnVector (r : SignedFrame) (v : Fin 4 → ℝ) :
    l1NormVec (r.actOnVector v) = l1NormVec v := by
  unfold l1NormVec
  simp only [actOnVector_apply, abs_mul, abs_unitCast, one_mul]
  exact Equiv.sum_comp r.1 fun μ => |v μ|
theorem euclidNormVec_actOnVector (r : SignedFrame) (v : Fin 4 → ℝ) :
    euclidNormVec (r.actOnVector v) = euclidNormVec v := by
  unfold euclidNormVec
  congr 1
  have : ∀ μ, r.actOnVector v μ ^ 2 = v (r.1 μ) ^ 2 := fun μ => by
    rw [actOnVector_apply, mul_pow, sq ((r.2 μ : ℤ) : ℝ), unitCast_mul_self, one_mul]
  simp only [this]
  exact Equiv.sum_comp r.1 fun μ => v μ ^ 2
theorem toFourTorus_eq_torusProj (x : Fin 4 → ℝ) :
    toFourTorus L m x = torusProj (torusSide L m) x := rfl
theorem toFourTorus_surjective : Function.Surjective (toFourTorus L m) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.toFourTorus_surjective <;> assumption
theorem toFourTorus_add (x y : Fin 4 → ℝ) :
    toFourTorus L m (x + y) = toFourTorus L m x + toFourTorus L m y := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.toFourTorus_add <;> assumption
theorem torusEquiv_apply (r : SignedFrame) (x : FourTorus L m) (μ : Fin 4) :
    SignedFrame.torusEquiv L m r x μ = (r.2 μ : ℤ) • x (r.1 μ) := rfl
theorem torusEquiv_add (r : SignedFrame) (x y : FourTorus L m) :
    SignedFrame.torusEquiv L m r (x + y) =
      SignedFrame.torusEquiv L m r x + SignedFrame.torusEquiv L m r y := by
  funext μ
  simp [torusEquiv_apply]
theorem torusEquiv_sub (r : SignedFrame) (x y : FourTorus L m) :
    SignedFrame.torusEquiv L m r (x - y) =
      SignedFrame.torusEquiv L m r x - SignedFrame.torusEquiv L m r y := by
  funext μ
  simp [torusEquiv_apply, smul_sub]
theorem torusEquiv_toFourTorus (r : SignedFrame) (x : Fin 4 → ℝ) :
    SignedFrame.torusEquiv L m r (toFourTorus L m x) = toFourTorus L m (r.actOnVector x) := by
  funext μ
  simp only [torusEquiv_apply, toFourTorus, actOnVector_apply]
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
def affEquiv (r : SignedFrame) (t : FourTorus L m) : FourTorus L m ≃ FourTorus L m :=
  (SignedFrame.torusEquiv L m r).trans (Equiv.addRight t)
theorem affEquiv_apply (r : SignedFrame) (t x : FourTorus L m) :
    affEquiv r t x = SignedFrame.torusEquiv L m r x + t := rfl
theorem affEquiv_isInduced (r : SignedFrame) (v : Fin 4 → ℝ) :
    IsInducedByAffine (affEquiv r (toFourTorus L m v)) r v := by
  intro x
  rw [affEquiv_apply, torusEquiv_toFourTorus, toFourTorus_add]
theorem eq_affEquiv {σ : FourTorus L m ≃ FourTorus L m} {r : SignedFrame} {v : Fin 4 → ℝ}
    (h : IsInducedByAffine σ r v) : σ = affEquiv r (toFourTorus L m v) := by
  ext1 x
  obtain ⟨y, rfl⟩ := toFourTorus_surjective x
  rw [h y, affEquiv_apply, torusEquiv_toFourTorus, toFourTorus_add]
theorem meshSize_pos (hL : 0 < L) (j : ℤ) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem torusSide_pos (hL : 0 < L) (m : ℕ) : 0 < torusSide L m := by apply _root_.YangMills.SharedProofs.p34445 <;> assumption
theorem zero_mem_meshVectors (i : ℤ) : (0 : Fin 4 → ℝ) ∈ meshVectors L i :=
  ⟨0, fun μ => by simp⟩
theorem add_mem_meshVectors {i : ℤ} {v w : Fin 4 → ℝ} (hv : v ∈ meshVectors L i)
    (hw : w ∈ meshVectors L i) : v + w ∈ meshVectors L i := by
  obtain ⟨n, hn⟩ := hv
  obtain ⟨n', hn'⟩ := hw
  refine ⟨n + n', fun μ => ?_⟩
  simp only [Pi.add_apply, hn, hn', Int.cast_add, add_mul]
theorem neg_mem_meshVectors {i : ℤ} {v : Fin 4 → ℝ} (hv : v ∈ meshVectors L i) :
    -v ∈ meshVectors L i := by
  obtain ⟨n, hn⟩ := hv
  refine ⟨-n, fun μ => ?_⟩
  simp only [Pi.neg_apply, hn, Int.cast_neg, neg_mul]
theorem actOnVector_mem_meshVectors {i : ℤ} (r : SignedFrame) {v : Fin 4 → ℝ}
    (hv : v ∈ meshVectors L i) : r.actOnVector v ∈ meshVectors L i := by
  obtain ⟨n, hn⟩ := hv
  refine ⟨fun μ => (r.2 μ : ℤ) * n (r.1 μ), fun μ => ?_⟩
  simp only [actOnVector_apply, hn, Int.cast_mul]
  ring
theorem meshVectors_mono (hL : 0 < L) {i i' : ℤ} (h : i ≤ i') :
    meshVectors L i ⊆ meshVectors L i' := by
  rintro v ⟨n, hn⟩
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr h)
  obtain rfl : i' = i + d := by omega
  refine ⟨fun μ => n μ * (L : ℤ) ^ d, fun μ => ?_⟩
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [hn μ]
  simp only [meshSize, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [neg_add, zpow_add₀ hL', zpow_neg _ (d : ℤ), zpow_natCast]
  field_simp
theorem toFourTorus_mem_sublattice {j : ℤ} {v : Fin 4 → ℝ} (hv : v ∈ meshVectors L j) :
    toFourTorus L m v ∈ sublattice L m j := by
  obtain ⟨n, hn⟩ := hv
  exact ⟨n, fun μ => by simp only [toFourTorus, hn]⟩
theorem one_mem_latticeIsometries (i : ℤ) :
    (1 : Equiv.Perm (FourTorus L m)) ∈ latticeIsometries L m i :=
  ⟨1, 0, zero_mem_meshVectors i, fun x => by simp [actOnVector_one]⟩
theorem mul_mem_latticeIsometries {i : ℤ} {σ τ : Equiv.Perm (FourTorus L m)}
    (hσ : σ ∈ latticeIsometries L m i) (hτ : τ ∈ latticeIsometries L m i) :
    σ * τ ∈ latticeIsometries L m i := by
  obtain ⟨r₁, v₁, hv₁, h₁⟩ := hσ
  obtain ⟨r₂, v₂, hv₂, h₂⟩ := hτ
  refine ⟨frameComp r₁ r₂, r₁.actOnVector v₂ + v₁,
    add_mem_meshVectors (actOnVector_mem_meshVectors r₁ hv₂) hv₁, fun x => ?_⟩
  rw [Equiv.Perm.mul_apply, h₂ x, h₁, actOnVector_add, frameComp_actOnVector, add_assoc]
theorem symm_mem_latticeIsometries {i : ℤ} {σ : FourTorus L m ≃ FourTorus L m}
    (hσ : σ ∈ latticeIsometries L m i) : σ.symm ∈ latticeIsometries L m i := by
  obtain ⟨r, v, hv, h⟩ := hσ
  refine ⟨frameInverse r, -(frameInverse r).actOnVector v,
    neg_mem_meshVectors (actOnVector_mem_meshVectors _ hv), fun x => ?_⟩
  rw [Equiv.symm_apply_eq, h]
  congr 1
  rw [actOnVector_add, actOnVector_neg, actOnVector_frameInverse_actOnVector,
    actOnVector_frameInverse_actOnVector, neg_add_cancel_right]
theorem latticeIsometries_isSubgroup (i : ℤ) : ∃ H : Subgroup (Equiv.Perm (FourTorus L m)),
    (H : Set (Equiv.Perm (FourTorus L m))) = latticeIsometries L m i :=
  ⟨{ carrier := latticeIsometries L m i
     mul_mem' := fun ha hb => mul_mem_latticeIsometries ha hb
     one_mem' := one_mem_latticeIsometries i
     inv_mem' := fun h => symm_mem_latticeIsometries h }, rfl⟩
theorem torusSide_eq_mul_meshSize (hL : 0 < L) {i : ℤ} (hi : -(m : ℤ) ≤ i) :
    torusSide L m = ((2 * L ^ ((m : ℤ) + i).toNat : ℕ) : ℝ) * meshSize L i := by
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ (m : ℤ) + i by omega)
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [hk]
  obtain rfl : i = k - m := by omega
  simp only [Int.toNat_natCast, torusSide, meshSize]
  push_cast
  rw [neg_sub, zpow_sub₀ hL', zpow_natCast, zpow_natCast]
  field_simp
theorem latticeIsometries_finite (hL : 0 < L) {i : ℤ} (hi : -(m : ℤ) ≤ i) :
    (latticeIsometries L m i).Finite := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = 2 * L ^ ((m : ℤ) + i).toNat := ⟨_, rfl⟩
  have hside : torusSide L m = (N : ℝ) * meshSize L i := by
    rw [hN]; exact torusSide_eq_mul_meshSize hL hi
  have hNpos : 0 < N := by rw [hN]; positivity
  have hNz : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hNpos
  let f : SignedFrame × (Fin 4 → Fin N) → (FourTorus L m ≃ FourTorus L m) := fun p =>
    affEquiv p.1 (toFourTorus L m fun μ => ((p.2 μ : ℕ) : ℝ) * meshSize L i)
  refine (Set.finite_range f).subset ?_
  rintro σ ⟨r, v, ⟨n, hn⟩, h⟩
  have hlt : ∀ μ, (n μ % (N : ℤ)).toNat < N := fun μ => by
    have h1 := Int.emod_nonneg (n μ) hNz.ne'
    have h2 := Int.emod_lt_of_pos (n μ) hNz
    omega
  refine ⟨(r, fun μ => ⟨(n μ % (N : ℤ)).toNat, hlt μ⟩), ?_⟩
  rw [eq_affEquiv h]
  change affEquiv r _ = affEquiv r _
  congr 1
  funext μ
  simp only [toFourTorus]
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  refine ⟨-(n μ / (N : ℤ)), ?_⟩
  have h1 := Int.emod_nonneg (n μ) hNz.ne'
  have h3 : (((n μ % (N : ℤ)).toNat : ℕ) : ℝ) = ((n μ % (N : ℤ) : ℤ) : ℝ) := by
    have : (((n μ % (N : ℤ)).toNat : ℕ) : ℤ) = n μ % (N : ℤ) := Int.toNat_of_nonneg h1
    exact_mod_cast this
  rw [h3, hn μ, hside, Int.emod_def]
  push_cast
  simp only [zsmul_eq_mul]
  push_cast
  ring
theorem sInf_image_torusEquiv (N : (Fin 4 → ℝ) → ℝ)
    (hN : ∀ (r : SignedFrame) v, N (r.actOnVector v) = N v)
    (r : SignedFrame) (x : FourTorus L m) :
    sInf (N '' (torusProj (torusSide L m) ⁻¹' {SignedFrame.torusEquiv L m r x})) =
      sInf (N '' (torusProj (torusSide L m) ⁻¹' {x})) := by
  congr 1
  ext a
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : torusProj (torusSide L m) w = SignedFrame.torusEquiv L m r x := hw
    refine ⟨(frameInverse r).actOnVector w, ?_, hN _ _⟩
    change torusProj (torusSide L m) _ = x
    apply (SignedFrame.torusEquiv L m r).injective
    rw [← toFourTorus_eq_torusProj, torusEquiv_toFourTorus, actOnVector_frameInverse_actOnVector]
    exact hw'
  · rintro ⟨w, hw, rfl⟩
    have hw' : torusProj (torusSide L m) w = x := hw
    refine ⟨r.actOnVector w, ?_, hN _ _⟩
    change torusProj (torusSide L m) _ = SignedFrame.torusEquiv L m r x
    rw [← toFourTorus_eq_torusProj, ← torusEquiv_toFourTorus, toFourTorus_eq_torusProj, hw']
theorem affEquiv_sub (r : SignedFrame) (t x y : FourTorus L m) :
    affEquiv r t x - affEquiv r t y = SignedFrame.torusEquiv L m r (x - y) := by
  rw [affEquiv_apply, affEquiv_apply, torusEquiv_sub, add_sub_add_right_eq_sub]
theorem torusSupNorm_affEquiv_sub (r : SignedFrame) (t x y : FourTorus L m) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm (affEquiv r t x - affEquiv r t y) = _root_.YangMills.Construction.TorusMetric.torusSupNorm (x - y) := by
  rw [affEquiv_sub]
  exact sInf_image_torusEquiv supNormVec supNormVec_actOnVector r _
theorem affEquiv_preservesTorusMetrics (r : SignedFrame) (t : FourTorus L m) :
    PreservesTorusMetrics (affEquiv r t) := by
  have h2 : ∀ x y, torusL1Norm (affEquiv r t x - affEquiv r t y) = torusL1Norm (x - y) :=
    fun x y => by
      rw [affEquiv_sub]
      exact sInf_image_torusEquiv l1NormVec l1NormVec_actOnVector r _
  have h3 : ∀ x y, torusEuclidNorm (affEquiv r t x - affEquiv r t y) = torusEuclidNorm (x - y) :=
    fun x y => by
      rw [affEquiv_sub]
      exact sInf_image_torusEquiv euclidNormVec euclidNormVec_actOnVector r _
  refine ⟨_root_.YangMills.Construction.PeriodicLattice.IsometryAction.torusSupNorm_affEquiv_sub r t, h2, h3, fun A B => ?_, fun A B => ?_⟩
  · simp only [setSupDist, iInf_image, _root_.YangMills.Construction.PeriodicLattice.IsometryAction.torusSupNorm_affEquiv_sub]
  · simp only [setEuclidDist, iInf_image, h3]
theorem preservesSegmentLengths (σ : FourTorus L m ≃ FourTorus L m) :
    PreservesSegmentLengths σ := by
  intro r v h Γ
  have hp : ∀ (s : LiftedSegment) (u : ℝ),
      (affineImageSegment r v s).pointAt (torusSide L m) u = σ (s.pointAt (torusSide L m) u) := by
    intro s u
    change torusProj (torusSide L m) _ = σ (toFourTorus L m _)
    rw [h, toFourTorus_eq_torusProj]
    congr 1
    funext μ
    simp only [affineImageSegment, LiftedSegment.displacement, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul, actOnVector_apply]
    ring
  have hvec : ∀ s : LiftedSegment,
      (affineImageSegment r v s).displacement = r.actOnVector s.displacement := by
    intro s
    funext μ
    simp only [affineImageSegment, LiftedSegment.displacement, Pi.add_apply, Pi.sub_apply,
      actOnVector_apply]
    ring
  constructor
  · ext p
    constructor
    · intro hpm
      simp only [segmentsSupport, mem_iUnion, exists_prop] at hpm
      obtain ⟨s', hs', hq⟩ := hpm
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hs'
      obtain ⟨u, hu, rfl⟩ := hq
      exact ⟨_, mem_iUnion₂.2 ⟨s, hs, u, hu, rfl⟩, (hp s u).symm⟩
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨s, hs, u, hu, rfl⟩ := mem_iUnion₂.1 hq
      exact mem_iUnion₂.2 ⟨affineImageSegment r v s, List.mem_map_of_mem hs, u, hu, hp s u⟩
  · simp only [pathLength, List.map_map]
    congr 1
    apply List.map_congr_left
    intro s _
    change l1NormVec (affineImageSegment r v s).displacement = l1NormVec s.displacement
    rw [hvec, l1NormVec_actOnVector]
theorem realNormal_diagonal_dotProduct (μ ν : Fin 4) (lt : μ < ν) (s : ℤˣ) (x : Fin 4 → ℝ) :
    (InfiniteLattice.ReflectionClass.diagonal μ ν lt s).realNormal ⬝ᵥ x =
      x μ + ((s : ℤ) : ℝ) * x ν := by
  simp only [dotProduct, InfiniteLattice.ReflectionClass.realNormal,
    InfiniteLattice.ReflectionClass.intNormal, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Int.cast_add, Int.cast_mul, add_mul, Finset.sum_add_distrib, Pi.single_apply]
  simp [Finset.sum_ite_eq', mul_ite, ite_mul]
theorem latticeIsometriesContainGenerators (L m : ℕ) (i : ℤ) :
    LatticeIsometriesContainGenerators L m i := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨w, n, hn⟩
    refine ⟨1, fun μ => (n μ : ℝ) * meshSize L i, ⟨n, fun _ => rfl⟩, fun x => ?_⟩
    rw [actOnVector_one, toFourTorus_add]
    change toFourTorus L m x + w = _
    congr 1
    funext μ
    simp only [toFourTorus, hn]
  · intro r
    refine ⟨r, 0, zero_mem_meshVectors i, fun x => ?_⟩
    rw [add_zero]
    exact torusEquiv_toFourTorus r x
  · intro P
    obtain ⟨q, hq⟩ := P.level_mem
    refine ⟨(1, fun κ => if κ = P.axis then -1 else 1),
      fun κ => if κ = P.axis then 2 * P.level else 0,
      ⟨fun κ => if κ = P.axis then q else 0, fun κ => ?_⟩, fun x => ?_⟩
    · by_cases h : κ = P.axis
      · simp only [h, if_true, hq]
        ring
      · simp [h]
    · rw [toFourTorus_eq_torusProj, P.reflectEquiv_torusProj, toFourTorus_eq_torusProj]
      congr 1
      funext κ
      by_cases h : κ = P.axis
      · subst h
        simp [actOnVector_apply]
        ring
      · simp [actOnVector_apply, h]
  · intro μ ν lt s c hc
    obtain ⟨q, hq⟩ := hc
    have hne : μ ≠ ν := ne_of_lt lt
    have ht := unitCast_mul_self s
    obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = ((s : ℤ) : ℝ) := ⟨_, rfl⟩
    let r : SignedFrame := (Equiv.swap μ ν, fun κ => if κ = μ ∨ κ = ν then -s else 1)
    let v : Fin 4 → ℝ := fun κ => if κ = μ then c else if κ = ν then t * c else 0
    have hv : v ∈ meshVectors L i := by
      refine ⟨fun κ => if κ = μ then q else if κ = ν then (s : ℤ) * q else 0, fun κ => ?_⟩
      by_cases h1 : κ = μ
      · simp [v, h1, hq]
      · by_cases h2 : κ = ν
        · simp only [v, if_neg h1, if_pos h2, htdef, hq]
          push_cast
          ring
        · simp [v, h1, h2]
    refine ⟨affEquiv r (toFourTorus L m v), ⟨r, v, hv, affEquiv_isInduced r v⟩, fun x => ?_⟩
    have h := affEquiv_isInduced (L := L) (m := m) r v x
    rw [h]
    congr 1
    funext κ
    have hnn := InfiniteLattice.ReflectionClass.realNormal_dot_diagonal μ ν lt s
    simp only [InfiniteLattice.hyperplaneReflect, hnn, realNormal_diagonal_dotProduct]
    by_cases h1 : κ = μ
    · subst h1
      simp [actOnVector_apply, r, v, InfiniteLattice.ReflectionClass.realNormal,
        InfiniteLattice.ReflectionClass.intNormal, hne, ← htdef]
      ring
    · by_cases h2 : κ = ν
      · subst h2
        simp [actOnVector_apply, r, v, InfiniteLattice.ReflectionClass.realNormal,
          InfiniteLattice.ReflectionClass.intNormal, h1, ← htdef]
        rw [← htdef] at ht
        linear_combination (x κ) * ht
      · have e : Equiv.swap μ ν κ = κ := Equiv.swap_apply_of_ne_of_ne h1 h2
        simp [actOnVector_apply, r, v, InfiniteLattice.ReflectionClass.realNormal,
          InfiniteLattice.ReflectionClass.intNormal, h1, h2, e]
theorem pointOnAxis_self (μ : Fin 4) (t : ℝ) :
    pointOnAxis L m μ t μ = (t : AddCircle (torusSide L m)) := by
  simp [pointOnAxis]
theorem pointOnAxis_of_ne {μ ν : Fin 4} (h : ν ≠ μ) (t : ℝ) : pointOnAxis L m μ t ν = 0 := by
  simp [pointOnAxis, Pi.single_eq_of_ne h]
theorem pointOnAxis_add (μ : Fin 4) (a b : ℝ) :
    pointOnAxis L m μ (a + b) = pointOnAxis L m μ a + pointOnAxis L m μ b := by apply _root_.YangMills.Construction.TorusBound.LocalisationDomainTree.pointOnAxis_add <;> assumption
theorem pointOnAxis_zero (μ : Fin 4) : pointOnAxis L m μ 0 = 0 := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCells.pointOnAxis_zero <;> assumption
theorem torusEquiv_pointOnAxis (r : SignedFrame) (μ : Fin 4) (t : ℝ) :
    SignedFrame.torusEquiv L m r (pointOnAxis L m μ t) =
      pointOnAxis L m (r.1⁻¹ μ) (((r.2 (r.1⁻¹ μ) : ℤ) : ℝ) * t) := by
  funext ν
  rw [torusEquiv_apply]
  by_cases h : ν = r.1⁻¹ μ
  · subst h
    have e : r.1 (r.1⁻¹ μ) = μ := by simp
    rw [e, pointOnAxis_self, pointOnAxis_self, ← AddCircle.coe_zsmul, zsmul_eq_mul]
  · have e : r.1 ν ≠ μ := fun e => h (by rw [← e]; simp)
    rw [pointOnAxis_of_ne e, pointOnAxis_of_ne h, smul_zero]
theorem affEquiv_add_pointOnAxis (r : SignedFrame) (t x : FourTorus L m) (μ : Fin 4) (u : ℝ) :
    affEquiv r t (x + pointOnAxis L m μ u) =
      affEquiv r t x + pointOnAxis L m (r.1⁻¹ μ) (((r.2 (r.1⁻¹ μ) : ℤ) : ℝ) * u) := by
  rw [affEquiv_apply, affEquiv_apply, torusEquiv_add, torusEquiv_pointOnAxis]
  abel
theorem two_mul_meshSize_le (hL : 1 ≤ L) {j : ℤ} (hj : -(m : ℤ) ≤ j) :
    2 * meshSize L j ≤ torusSide L m := by
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h2 : meshSize L j ≤ (L : ℝ) ^ m := by
    unfold meshSize
    rw [← zpow_natCast]
    exact zpow_le_zpow_right₀ h1 (by omega)
  unfold torusSide
  linarith
theorem two_mul_meshSize_lt (hL : 1 < L) {j : ℤ} (hj : -(m : ℤ) < j) :
    2 * meshSize L j < torusSide L m := by
  have h1 : (1 : ℝ) < L := by exact_mod_cast hL
  have h2 : meshSize L j < (L : ℝ) ^ m := by
    unfold meshSize
    rw [← zpow_natCast]
    exact zpow_lt_zpow_right₀ h1 (by omega)
  unfold torusSide
  linarith
theorem addCircle_coe_ne_zero {S y : ℝ} (hS : 0 < S) (h0 : 0 < y) (h1 : y < S) :
    (y : AddCircle S) ≠ 0 := by apply _root_.YangMills.SharedProofs.p5311 <;> assumption
theorem base_eq_of_arcs {S a : ℝ} (ha : 0 < a) (hS : 2 * a ≤ S) {c c' : AddCircle S}
    (h1 : ∃ u ∈ Icc (0 : ℝ) a, c = c' + (u : AddCircle S))
    (h2 : ∃ w ∈ Icc (0 : ℝ) a, c' = c + (w : AddCircle S))
    (h3 : ∃ t ∈ Icc (0 : ℝ) a, c + ((a / 2 : ℝ) : AddCircle S) = c' + (t : AddCircle S)) :
    c = c' := by
  obtain ⟨u, ⟨hu0, hu1⟩, hu⟩ := h1
  obtain ⟨w, ⟨hw0, hw1⟩, hw⟩ := h2
  obtain ⟨t, ⟨ht0, ht1⟩, ht⟩ := h3
  have hS0 : 0 < S := by linarith
  have hz : ((u + w : ℝ) : AddCircle S) = 0 := by
    have : c' = c' + ((u + w : ℝ) : AddCircle S) := by
      rw [AddCircle.coe_add, ← add_assoc, ← hu]
      exact hw
    exact left_eq_add.1 this
  by_cases hpos : u + w = 0
  · have : u = 0 := by linarith
    rw [hu, this]
    simp
  · exfalso
    have hlt : u + w = S ∨ u + w < S := by
      rcases eq_or_lt_of_le (show u + w ≤ S by linarith) with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases hlt with hE | hlt
    · have hu' : u = a := by linarith
      have hS' : S = 2 * a := by linarith
      have hc : c = c' + (a : AddCircle S) := by rw [hu, hu']
      have hz2 : ((a + a / 2 - t : ℝ) : AddCircle S) = 0 := by
        have : c' + ((a + a / 2 : ℝ) : AddCircle S) = c' + (t : AddCircle S) := by
          rw [AddCircle.coe_add, ← add_assoc, ← hc]
          exact ht
        rw [AddCircle.coe_sub, add_left_cancel this, sub_self]
      exact addCircle_coe_ne_zero hS0 (by linarith) (by linarith) hz2
    · exact addCircle_coe_ne_zero hS0 (lt_of_le_of_ne (by linarith) (Ne.symm hpos)) hlt hz
def axisArc (x : FourTorus L m) (μ : Fin 4) (a : ℝ) : Set (FourTorus L m) :=
  {p | ∃ t ∈ Icc (0 : ℝ) a, p = x + pointOnAxis L m μ t}
theorem axisArc_injective (hL : 0 < L) {a : ℝ} (ha : 0 < a) (hS : 2 * a ≤ torusSide L m)
    {x x' : FourTorus L m} {μ μ' : Fin 4} (h : axisArc x μ a = axisArc x' μ' a) :
    x = x' ∧ μ = μ' := by
  have hS0 := torusSide_pos hL m
  have hne : (a : AddCircle (torusSide L m)) ≠ 0 := addCircle_coe_ne_zero hS0 ha (by linarith)
  have m0 : x ∈ axisArc x' μ' a := by
    rw [← h]
    exact ⟨0, ⟨le_rfl, ha.le⟩, by simp [pointOnAxis_zero]⟩
  have m1 : x + pointOnAxis L m μ a ∈ axisArc x' μ' a := by
    rw [← h]
    exact ⟨a, ⟨ha.le, le_rfl⟩, rfl⟩
  have mh : x + pointOnAxis L m μ (a / 2) ∈ axisArc x' μ' a := by
    rw [← h]
    exact ⟨a / 2, ⟨by linarith, by linarith⟩, rfl⟩
  have m0' : x' ∈ axisArc x μ a := by
    rw [h]
    exact ⟨0, ⟨le_rfl, ha.le⟩, by simp [pointOnAxis_zero]⟩
  obtain ⟨u, hu, e0⟩ := m0
  obtain ⟨u₁, hu₁, e1⟩ := m1
  obtain ⟨t, ht, eh⟩ := mh
  obtain ⟨w, hw, e0'⟩ := m0'
  have hμ : μ = μ' := by
    by_contra hc
    have a0 := congrFun e0 μ
    have a1 := congrFun e1 μ
    simp only [Pi.add_apply, pointOnAxis_of_ne hc, pointOnAxis_self, add_zero] at a0 a1
    rw [a0] at a1
    exact hne (left_eq_add.1 a1.symm ▸ rfl)
  subst hμ
  refine ⟨?_, rfl⟩
  funext ν
  by_cases hν : ν = μ
  · subst hν
    have a0 := congrFun e0 ν
    have a0' := congrFun e0' ν
    have ah := congrFun eh ν
    simp only [Pi.add_apply, pointOnAxis_self] at a0 a0' ah
    exact base_eq_of_arcs ha hS ⟨u, hu, a0⟩ ⟨w, hw, a0'⟩ ⟨t, ht, ah⟩
  · have a0 := congrFun e0 ν
    simpa only [Pi.add_apply, pointOnAxis_of_ne hν, add_zero] using a0
theorem unitStep_coe (j : ℤ) (μ : Fin 4) :
    (unitStep L m j μ : FourTorus L m) = pointOnAxis L m μ (meshSize L j) := rfl
theorem torusEquiv_mem_sublattice (r : SignedFrame) {j : ℤ} {x : FourTorus L m}
    (hx : x ∈ sublattice L m j) : SignedFrame.torusEquiv L m r x ∈ sublattice L m j := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨fun μ => (r.2 μ : ℤ) * n (r.1 μ), fun μ => ?_⟩
  rw [torusEquiv_apply, hn, ← AddCircle.coe_zsmul, zsmul_eq_mul]
  congr 1
  push_cast
  ring
theorem affEquiv_mem_sublattice (r : SignedFrame) {j : ℤ} {t x : FourTorus L m}
    (ht : t ∈ sublattice L m j) (hx : x ∈ sublattice L m j) :
    affEquiv r t x ∈ sublattice L m j :=
  add_mem (torusEquiv_mem_sublattice r hx) ht
theorem pointOnAxis_mem_sublattice (j : ℤ) (μ : Fin 4) :
    pointOnAxis L m μ (meshSize L j) ∈ sublattice L m j := (unitStep L m j μ).2
theorem pointOnAxis_neg_mem_sublattice (j : ℤ) (μ : Fin 4) :
    pointOnAxis L m μ (-meshSize L j) ∈ sublattice L m j := by
  have h := neg_mem (pointOnAxis_mem_sublattice (L := L) (m := m) j μ)
  have e : pointOnAxis L m μ (-meshSize L j) = -pointOnAxis L m μ (meshSize L j) := by
    rw [eq_neg_iff_add_eq_zero, ← pointOnAxis_add, neg_add_cancel, pointOnAxis_zero]
  rwa [e]
theorem pointOnAxis_neg (μ : Fin 4) (t : ℝ) : pointOnAxis L m μ (-t) = -pointOnAxis L m μ t := by apply _root_.YangMills.Construction.CellGrid.pointOnAxis_neg <;> assumption
variable {j : ℤ}
theorem bond_target_cases (b : Bond L m j) :
    ((b.target : FourTorus L m) = b.source + pointOnAxis L m b.axis (meshSize L j) ∧
        b.orientedLength = meshSize L j) ∨
      ((b.target : FourTorus L m) = b.source + pointOnAxis L m b.axis (-meshSize L j) ∧
        b.orientedLength = -meshSize L j) := by
  by_cases h : b.target - b.source = unitStep L m j b.axis
  · left
    refine ⟨?_, if_pos h⟩
    have := congrArg (Subtype.val) h
    rw [← unitStep_coe, ← this]
    simp
  · right
    refine ⟨?_, if_neg h⟩
    have hs : b.target - b.source = -unitStep L m j b.axis :=
      (b.isNeighbour.choose_spec).resolve_left h
    have := congrArg (Subtype.val) hs
    rw [pointOnAxis_neg, ← unitStep_coe]
    have e : (-(unitStep L m j b.axis : FourTorus L m)) =
        ((-unitStep L m j b.axis : Site L m j) : FourTorus L m) := rfl
    rw [e, ← this]
    simp
theorem edgeSet_eq_axisArc (hL : 0 < L) (b : Bond L m j) :
    ∃ x ∈ sublattice L m j, b.edgeSet = axisArc x b.axis (meshSize L j) ∧
      b.centre = x + pointOnAxis L m b.axis (meshSize L j / 2) := by
  have ha := meshSize_pos hL j
  rcases bond_target_cases b with ⟨hh, hs⟩ | ⟨hh, hs⟩
  · refine ⟨b.source, b.source.2, ?_, ?_⟩
    · ext p
      constructor
      · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
        refine ⟨t * meshSize L j, ⟨by positivity, by nlinarith⟩, ?_⟩
        rw [hs]
      · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
        refine ⟨t / meshSize L j, ⟨by positivity, (div_le_one ha).2 h1⟩, ?_⟩
        rw [hs, div_mul_cancel₀ _ ha.ne']
    · simp only [Bond.centre, hs]
  · refine ⟨b.target, b.target.2, ?_, ?_⟩
    · ext p
      constructor
      · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
        refine ⟨meshSize L j - t * meshSize L j, ⟨by nlinarith, by nlinarith⟩, ?_⟩
        rw [hs, hh, add_assoc, ← pointOnAxis_add]
        congr 2
        ring
      · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
        refine ⟨(meshSize L j - t) / meshSize L j,
          ⟨div_nonneg (by linarith) ha.le, (div_le_one ha).2 (by linarith)⟩, ?_⟩
        rw [hs, hh, add_assoc, ← pointOnAxis_add]
        congr 2
        field_simp
        ring
    · simp only [Bond.centre, hs]
      rw [hh, add_assoc, ← pointOnAxis_add]
      congr 2
      ring
theorem forwardFrom_axis (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (x : Site L m j) (μ : Fin 4) :
    (Bond.forwardFrom x μ).axis = μ := by
  by_contra hc
  have hS := two_mul_meshSize_le (m := m) hL hj
  have hS0 := torusSide_pos hL m
  have ha := meshSize_pos hL j
  have hne : (meshSize L j : AddCircle (torusSide L m)) ≠ 0 :=
    addCircle_coe_ne_zero hS0 ha (by linarith)
  have hspec := (Bond.forwardFrom x μ).isNeighbour.choose_spec
  change _ = unitStep L m j (Bond.forwardFrom x μ).axis ∨
    _ = -unitStep L m j (Bond.forwardFrom x μ).axis at hspec
  have hv : (Bond.forwardFrom x μ).target - (Bond.forwardFrom x μ).source = unitStep L m j μ := by
    simp [Bond.forwardFrom]
  rw [hv] at hspec
  rcases hspec with h | h
  · have := congrFun (congrArg Subtype.val h) μ
    simp only [unitStep_coe, pointOnAxis_self, pointOnAxis_of_ne (Ne.symm hc)] at this
    exact hne this
  · have := congrFun (congrArg Subtype.val h) μ
    have e : ((-unitStep L m j (Bond.forwardFrom x μ).axis : Site L m j) : FourTorus L m) =
      -pointOnAxis L m (Bond.forwardFrom x μ).axis (meshSize L j) := rfl
    rw [e] at this
    simp only [unitStep_coe, pointOnAxis_self, Pi.neg_apply, pointOnAxis_of_ne (Ne.symm hc),
      neg_zero] at this
    exact hne this
theorem forwardFrom_edgeSet (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (x : Site L m j) (μ : Fin 4) :
    (Bond.forwardFrom x μ).edgeSet = axisArc (x : FourTorus L m) μ (meshSize L j) ∧
      (Bond.forwardFrom x μ).centre =
        (x : FourTorus L m) + pointOnAxis L m μ (meshSize L j / 2) := by
  have hd := forwardFrom_axis hL hj x μ
  have ha := meshSize_pos hL j
  have hs : (Bond.forwardFrom x μ).orientedLength = meshSize L j := by
    unfold Bond.orientedLength
    rw [if_pos]
    rw [hd]
    simp [Bond.forwardFrom]
  constructor
  · ext p
    constructor
    · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
      refine ⟨t * meshSize L j, ⟨by positivity, by nlinarith⟩, ?_⟩
      rw [hs, hd]
      rfl
    · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
      refine ⟨t / meshSize L j, ⟨by positivity, (div_le_one ha).2 h1⟩, ?_⟩
      rw [hs, hd, div_mul_cancel₀ _ ha.ne']
      rfl
  · simp only [Bond.centre, hs, hd]
    rfl
theorem exists_reparam_of_sign (j : ℤ) (f : Fin 4) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ d ∈ sublattice L m j, ∃ φ : ℝ → ℝ,
      (∀ u ∈ Icc (0 : ℝ) (meshSize L j), φ u ∈ Icc (0 : ℝ) (meshSize L j)) ∧
      (∀ u ∈ Icc (0 : ℝ) (meshSize L j), ∃ u₀ ∈ Icc (0 : ℝ) (meshSize L j), φ u₀ = u) ∧
      (∀ u, pointOnAxis L m f (ε * u) = d + pointOnAxis L m f (φ u)) ∧
      φ (meshSize L j / 2) = meshSize L j / 2 := by
  rcases hε with rfl | rfl
  · refine ⟨0, zero_mem _, id, fun u hu => hu, fun u hu => ⟨u, hu, rfl⟩, fun u => ?_, rfl⟩
    simp
  · refine ⟨_, pointOnAxis_neg_mem_sublattice j f, fun u => meshSize L j - u, ?_, ?_,
      fun u => ?_, ?_⟩
    · rintro u ⟨h0, h1⟩
      exact ⟨by linarith, by linarith⟩
    · rintro u ⟨h0, h1⟩
      exact ⟨meshSize L j - u, ⟨by linarith, by linarith⟩, by ring⟩
    · rw [← pointOnAxis_add]
      congr 1
      ring
    · ring
theorem image_axisArc (r : SignedFrame) {t x : FourTorus L m} (ht : t ∈ sublattice L m j)
    (hx : x ∈ sublattice L m j) (μ : Fin 4) :
    ∃ x' ∈ sublattice L m j, ∃ μ' : Fin 4,
      affEquiv r t '' axisArc x μ (meshSize L j) = axisArc x' μ' (meshSize L j) ∧
      affEquiv r t (x + pointOnAxis L m μ (meshSize L j / 2)) =
        x' + pointOnAxis L m μ' (meshSize L j / 2) := by
  obtain ⟨d, hd, φ, h1, h2, h3, h4⟩ :=
    exists_reparam_of_sign (m := m) j (r.1⁻¹ μ) (unitCast_cases (r.2 (r.1⁻¹ μ)))
  refine ⟨affEquiv r t x + d, add_mem (affEquiv_mem_sublattice r ht hx) hd, r.1⁻¹ μ, ?_, ?_⟩
  · ext p
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨φ u, h1 u hu, ?_⟩
      rw [affEquiv_add_pointOnAxis, h3, add_assoc]
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨u₀, hu₀, rfl⟩ := h2 u hu
      refine ⟨_, ⟨u₀, hu₀, rfl⟩, ?_⟩
      rw [affEquiv_add_pointOnAxis, h3, add_assoc]
  · rw [affEquiv_add_pointOnAxis, h3, add_assoc, h4]
def axisSquare (x : FourTorus L m) (f g : Fin 4) (a : ℝ) : Set (FourTorus L m) :=
  {q | ∃ s ∈ Icc (0 : ℝ) a, ∃ t ∈ Icc (0 : ℝ) a,
    q = x + pointOnAxis L m f s + pointOnAxis L m g t}
theorem face_eq_axisSquare (p : Plaquette L m j) :
    p.face = axisSquare (p.origin : FourTorus L m) p.firstAxis p.secondAxis (meshSize L j) := rfl
theorem axisSquare_comm (x : FourTorus L m) (f g : Fin 4) (a : ℝ) :
    axisSquare x f g a = axisSquare x g f a := by
  ext q
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨t, ht, s, hs, add_right_comm _ _ _⟩
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨t, ht, s, hs, add_right_comm _ _ _⟩
theorem image_axisSquare (r : SignedFrame) {t x : FourTorus L m} (ht : t ∈ sublattice L m j)
    (hx : x ∈ sublattice L m j) {f g : Fin 4} (hfg : f ≠ g) :
    ∃ x' ∈ sublattice L m j, ∃ f' g' : Fin 4, f' ≠ g' ∧
      affEquiv r t '' axisSquare x f g (meshSize L j) = axisSquare x' f' g' (meshSize L j) ∧
      affEquiv r t (x + pointOnAxis L m f (meshSize L j / 2) +
          pointOnAxis L m g (meshSize L j / 2)) =
        x' + pointOnAxis L m f' (meshSize L j / 2) + pointOnAxis L m g' (meshSize L j / 2) := by
  obtain ⟨d, hd, φ, h1, h2, h3, h4⟩ :=
    exists_reparam_of_sign (m := m) j (r.1⁻¹ f) (unitCast_cases (r.2 (r.1⁻¹ f)))
  obtain ⟨d', hd', φ', h1', h2', h3', h4'⟩ :=
    exists_reparam_of_sign (m := m) j (r.1⁻¹ g) (unitCast_cases (r.2 (r.1⁻¹ g)))
  have key : ∀ s u, affEquiv r t (x + pointOnAxis L m f s + pointOnAxis L m g u) =
      affEquiv r t x + d + d' + pointOnAxis L m (r.1⁻¹ f) (φ s) +
        pointOnAxis L m (r.1⁻¹ g) (φ' u) := by
    intro s u
    rw [affEquiv_add_pointOnAxis, affEquiv_add_pointOnAxis, h3, h3']
    abel
  refine ⟨affEquiv r t x + d + d', add_mem (add_mem (affEquiv_mem_sublattice r ht hx) hd) hd',
    r.1⁻¹ f, r.1⁻¹ g, fun e => hfg (r.1⁻¹.injective e), ?_, ?_⟩
  · ext p
    constructor
    · rintro ⟨_, ⟨s, hs, u, hu, rfl⟩, rfl⟩
      exact ⟨φ s, h1 s hs, φ' u, h1' u hu, key s u⟩
    · rintro ⟨s, hs, u, hu, rfl⟩
      obtain ⟨s₀, hs₀, rfl⟩ := h2 s hs
      obtain ⟨u₀, hu₀, rfl⟩ := h2' u hu
      exact ⟨_, ⟨s₀, hs₀, u₀, hu₀, rfl⟩, key s₀ u₀⟩
  · rw [key, h4, h4']
theorem exists_plaquette_of_axisSquare {x : FourTorus L m} (hx : x ∈ sublattice L m j)
    {f g : Fin 4} (hfg : f ≠ g) :
    ∃ q : Plaquette L m j, q.face = axisSquare x f g (meshSize L j) ∧
      q.barycenter = x + pointOnAxis L m f (meshSize L j / 2) +
        pointOnAxis L m g (meshSize L j / 2) := by
  rcases lt_or_gt_of_ne hfg with h | h
  · exact ⟨⟨⟨x, hx⟩, f, g, h⟩, rfl, rfl⟩
  · exact ⟨⟨⟨x, hx⟩, g, f, h⟩, axisSquare_comm _ _ _ _, add_right_comm _ _ _⟩
theorem axisSquare_coord {a : ℝ} {x p : FourTorus L m} {f g ν : Fin 4} (hfg : f ≠ g)
    (hp : p ∈ axisSquare x f g a) (hν : ν = f ∨ ν = g) :
    ∃ w ∈ Icc (0 : ℝ) a, p ν = x ν + (w : AddCircle (torusSide L m)) := by
  obtain ⟨s, hs, u, hu, rfl⟩ := hp
  rcases hν with rfl | rfl
  · refine ⟨s, hs, ?_⟩
    simp [pointOnAxis_self, pointOnAxis_of_ne hfg]
  · refine ⟨u, hu, ?_⟩
    simp [pointOnAxis_self, pointOnAxis_of_ne hfg.symm]
theorem axisSquare_coord_of_ne {a : ℝ} {x p : FourTorus L m} {f g ν : Fin 4}
    (hp : p ∈ axisSquare x f g a) (h1 : ν ≠ f) (h2 : ν ≠ g) : p ν = x ν := by
  obtain ⟨s, hs, u, hu, rfl⟩ := hp
  simp [pointOnAxis_of_ne h1, pointOnAxis_of_ne h2]
theorem axisSquare_injective (hL : 0 < L) {a : ℝ} (ha : 0 < a) (hS : 2 * a ≤ torusSide L m)
    {x x' : FourTorus L m} {f g f' g' : Fin 4} (hfg : f ≠ g) (hfg' : f' ≠ g')
    (h : axisSquare x f g a = axisSquare x' f' g' a) :
    x = x' ∧ ((f = f' ∧ g = g') ∨ (f = g' ∧ g = f')) := by
  have hS0 := torusSide_pos hL m
  have hne : (a : AddCircle (torusSide L m)) ≠ 0 := addCircle_coe_ne_zero hS0 ha (by linarith)
  have mem0 : x ∈ axisSquare x f g a :=
    ⟨0, ⟨le_rfl, ha.le⟩, 0, ⟨le_rfl, ha.le⟩, by simp [pointOnAxis_zero]⟩
  have mem0' : x' ∈ axisSquare x f g a := by
    rw [h]
    exact ⟨0, ⟨le_rfl, ha.le⟩, 0, ⟨le_rfl, ha.le⟩, by simp [pointOnAxis_zero]⟩
  have memf : x + pointOnAxis L m f a ∈ axisSquare x f g a :=
    ⟨a, ⟨ha.le, le_rfl⟩, 0, ⟨le_rfl, ha.le⟩, by simp [pointOnAxis_zero]⟩
  have memg : x + pointOnAxis L m g a ∈ axisSquare x f g a :=
    ⟨0, ⟨le_rfl, ha.le⟩, a, ⟨ha.le, le_rfl⟩, by simp [pointOnAxis_zero]⟩
  have inF : ∀ e, (e = f ∨ e = g) → x + pointOnAxis L m e a ∈ axisSquare x f g a →
      e = f' ∨ e = g' := by
    intro e _ he
    by_contra hc
    push Not at hc
    rw [h] at he
    have q0 : x ∈ axisSquare x' f' g' a := h ▸ mem0
    have c0 := axisSquare_coord_of_ne q0 hc.1 hc.2
    have c1 := axisSquare_coord_of_ne he hc.1 hc.2
    simp only [Pi.add_apply, pointOnAxis_self] at c1
    rw [c0] at c1
    exact hne (left_eq_add.1 c1.symm ▸ rfl)
  have hf := inF f (Or.inl rfl) memf
  have hg := inF g (Or.inr rfl) memg
  have hdir : (f = f' ∧ g = g') ∨ (f = g' ∧ g = f') := by
    rcases hf with hf | hf <;> rcases hg with hg | hg
    · exact absurd (hf.trans hg.symm) hfg
    · exact Or.inl ⟨hf, hg⟩
    · exact Or.inr ⟨hf, hg⟩
    · exact absurd (hf.trans hg.symm) hfg
  refine ⟨?_, hdir⟩
  have q0 : x ∈ axisSquare x' f' g' a := h ▸ mem0
  funext ν
  by_cases hν : ν = f ∨ ν = g
  · have hν' : ν = f' ∨ ν = g' := by
      rcases hdir with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hν with hν | hν <;> simp [hν, e1, e2]
    obtain ⟨u, hu, e0⟩ := axisSquare_coord hfg' q0 hν'
    obtain ⟨w, hw, e1⟩ := axisSquare_coord hfg mem0' hν
    have memh : x + pointOnAxis L m ν (a / 2) ∈ axisSquare x f g a := by
      rcases hν with rfl | rfl
      · exact ⟨a / 2, ⟨by linarith, by linarith⟩, 0, ⟨le_rfl, ha.le⟩,
          by simp [pointOnAxis_zero]⟩
      · exact ⟨0, ⟨le_rfl, ha.le⟩, a / 2, ⟨by linarith, by linarith⟩,
          by simp [pointOnAxis_zero]⟩
    rw [h] at memh
    obtain ⟨t, ht, e2⟩ := axisSquare_coord hfg' memh hν'
    simp only [Pi.add_apply, pointOnAxis_self] at e2
    exact base_eq_of_arcs ha hS ⟨u, hu, e0⟩ ⟨w, hw, e1⟩ ⟨t, ht, e2⟩
  · push Not at hν
    have hν' : ν ≠ f' ∧ ν ≠ g' := by
      rcases hdir with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact ⟨e1 ▸ hν.1, e2 ▸ hν.2⟩
      · exact ⟨e2 ▸ hν.2, e1 ▸ hν.1⟩
    exact axisSquare_coord_of_ne q0 hν'.1 hν'.2
theorem face_injective (hL : 0 < L) (hj : -(m : ℤ) ≤ j) {p q : Plaquette L m j}
    (h : p.face = q.face) : p = q := by
  rw [face_eq_axisSquare, face_eq_axisSquare] at h
  obtain ⟨hx, hd⟩ := axisSquare_injective hL (meshSize_pos hL j) (two_mul_meshSize_le hL hj)
    p.firstAxis_lt_secondAxis.ne q.firstAxis_lt_secondAxis.ne h
  rcases hd with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Plaquette.ext (Subtype.ext hx) e1 e2
  · exfalso
    have h1 := p.firstAxis_lt_secondAxis
    have h2 := q.firstAxis_lt_secondAxis
    rw [e1, e2] at h1
    exact lt_asymm h1 h2
theorem image_family_eq_self {α : Type*} (σ : α ≃ α) {F : Set (Set α)}
    (h1 : ∀ S ∈ F, σ '' S ∈ F) (h2 : ∀ S ∈ F, σ.symm '' S ∈ F) :
    (fun S => σ '' S) '' F = F := by
  ext S
  constructor
  · rintro ⟨S', hS', rfl⟩
    exact h1 S' hS'
  · intro hS
    exact ⟨σ.symm '' S, h2 S hS, σ.image_symm_image S⟩
theorem image_cubeAround (r : SignedFrame) (t : FourTorus L m) {y y' : Site L m j}
    (h : (y' : FourTorus L m) = affEquiv r t y) : affEquiv r t '' cubeAround y = cubeAround y' := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change _root_.YangMills.Construction.TorusMetric.torusSupNorm (affEquiv r t x - (y' : FourTorus L m)) ≤ _
    rw [h, _root_.YangMills.Construction.PeriodicLattice.IsometryAction.torusSupNorm_affEquiv_sub]
    exact hx
  · intro hz
    refine ⟨(affEquiv r t).symm z, ?_, by simp⟩
    change _root_.YangMills.Construction.TorusMetric.torusSupNorm _ ≤ _
    have hz' : _root_.YangMills.Construction.TorusMetric.torusSupNorm (z - (y' : FourTorus L m)) ≤ meshSize L j / 2 := hz
    rw [h] at hz'
    have e := _root_.YangMills.Construction.PeriodicLattice.IsometryAction.torusSupNorm_affEquiv_sub r t ((affEquiv r t).symm z) y
    rw [Equiv.apply_symm_apply] at e
    rwa [← e]
theorem image_mem_bondEdgeSets (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (r : SignedFrame)
    {t : FourTorus L m} (ht : t ∈ sublattice L m j) {S : Set (FourTorus L m)}
    (hS : S ∈ bondEdgeSets L m j) : affEquiv r t '' S ∈ bondEdgeSets L m j := by
  obtain ⟨b, rfl⟩ := hS
  obtain ⟨x, hx, e1, -⟩ := edgeSet_eq_axisArc hL b
  obtain ⟨x', hx', μ', e2, -⟩ := image_axisArc r ht hx b.axis
  refine ⟨Bond.forwardFrom ⟨x', hx'⟩ μ', ?_⟩
  rw [(forwardFrom_edgeSet hL hj ⟨x', hx'⟩ μ').1, e1, e2]
theorem exists_plaquette_image (r : SignedFrame) {t : FourTorus L m}
    (ht : t ∈ sublattice L m j) (p : Plaquette L m j) :
    ∃ q : Plaquette L m j, q.face = affEquiv r t '' p.face ∧
      q.barycenter = affEquiv r t p.barycenter := by
  obtain ⟨x', hx', f', g', hfg, e1, e2⟩ :=
    image_axisSquare r ht p.origin.2 p.firstAxis_lt_secondAxis.ne
  obtain ⟨q, hq1, hq2⟩ := exists_plaquette_of_axisSquare hx' hfg
  exact ⟨q, by rw [hq1, face_eq_axisSquare, e1], by rw [hq2, ← e2]; rfl⟩
theorem exists_bond_image (r : SignedFrame) {t : FourTorus L m} (ht : t ∈ sublattice L m j)
    (b : Bond L m j) :
    ∃ c : Bond L m j, (c.source : FourTorus L m) = affEquiv r t b.source ∧
      (c.target : FourTorus L m) = affEquiv r t b.target := by
  have hε := unitCast_cases (r.2 (r.1⁻¹ b.axis))
  have hsub : ∀ y : FourTorus L m, y = b.source + pointOnAxis L m b.axis (meshSize L j) ∨
      y = b.source + pointOnAxis L m b.axis (-meshSize L j) →
      y = b.target →
      (affEquiv r t y - affEquiv r t b.source =
          pointOnAxis L m (r.1⁻¹ b.axis) (meshSize L j) ∨
        affEquiv r t y - affEquiv r t b.source =
          pointOnAxis L m (r.1⁻¹ b.axis) (-meshSize L j)) := by
    intro y hy _
    rcases hy with rfl | rfl <;> rw [affEquiv_add_pointOnAxis, add_sub_cancel_left] <;>
      rcases hε with h | h <;> rw [h] <;> simp
  have hy : (b.target : FourTorus L m) = b.source + pointOnAxis L m b.axis (meshSize L j) ∨
      (b.target : FourTorus L m) = b.source + pointOnAxis L m b.axis (-meshSize L j) := by
    rcases bond_target_cases b with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨⟨⟨affEquiv r t b.source, affEquiv_mem_sublattice r ht b.source.2⟩,
    ⟨affEquiv r t b.target, affEquiv_mem_sublattice r ht b.target.2⟩, r.1⁻¹ b.axis, ?_⟩,
    rfl, rfl⟩
  rcases hsub _ hy rfl with h | h
  · left
    exact Subtype.ext h
  · right
    apply Subtype.ext
    change _ = -pointOnAxis L m _ _
    rw [← pointOnAxis_neg]
    exact h
theorem bondImage_ends (r : SignedFrame) {t : FourTorus L m} (ht : t ∈ sublattice L m j)
    (b : Bond L m j) :
    ((bondImage (affEquiv r t) b).source : FourTorus L m) = affEquiv r t b.source ∧
      ((bondImage (affEquiv r t) b).target : FourTorus L m) = affEquiv r t b.target := by
  have h : ∃ b' : Bond L m j, (b'.source : FourTorus L m) = (affEquiv r t).symm.symm b.source ∧
      (b'.target : FourTorus L m) = (affEquiv r t).symm.symm b.target := exists_bond_image r ht b
  unfold bondImage bondPreimage
  rw [dif_pos h]
  exact h.choose_spec
theorem pointOnAxis_signed_injective (hL : 1 < L) (hj : -(m : ℤ) < j) {d d' : Fin 4}
    {u u' : ℝ} (hu : u = meshSize L j ∨ u = -meshSize L j)
    (hu' : u' = meshSize L j ∨ u' = -meshSize L j)
    (h : pointOnAxis L m d u = pointOnAxis L m d' u') : d = d' ∧ u = u' := by
  have hL0 : 0 < L := by omega
  have ha := meshSize_pos hL0 j
  have hS := two_mul_meshSize_lt (m := m) hL hj
  have hS0 := torusSide_pos hL0 m
  have hne : (meshSize L j : AddCircle (torusSide L m)) ≠ 0 :=
    addCircle_coe_ne_zero hS0 ha (by linarith)
  have hne2 : ((2 * meshSize L j : ℝ) : AddCircle (torusSide L m)) ≠ 0 :=
    addCircle_coe_ne_zero hS0 (by linarith) hS
  have hu0 : (u : AddCircle (torusSide L m)) ≠ 0 := by
    rcases hu with rfl | rfl
    · exact hne
    · rw [AddCircle.coe_neg]
      exact neg_ne_zero.2 hne
  have hd : d = d' := by
    by_contra hc
    have := congrFun h d
    rw [pointOnAxis_self, pointOnAxis_of_ne hc] at this
    exact hu0 this
  subst hd
  refine ⟨rfl, ?_⟩
  have e := congrFun h d
  rw [pointOnAxis_self, pointOnAxis_self] at e
  rcases hu with rfl | rfl <;> rcases hu' with rfl | rfl
  · rfl
  · exfalso
    apply hne2
    have : ((meshSize L j + meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
      rw [AddCircle.coe_add]
      nth_rewrite 1 [e]
      rw [AddCircle.coe_neg]
      simp
    rwa [← two_mul] at this
  · exfalso
    apply hne2
    have : ((meshSize L j + meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
      rw [AddCircle.coe_add]
      nth_rewrite 2 [← e]
      rw [AddCircle.coe_neg]
      simp
    rwa [← two_mul] at this
  · rfl
theorem bondImage_edgeSet (hL : 1 < L) (hj : -(m : ℤ) < j) (r : SignedFrame)
    {t : FourTorus L m} (ht : t ∈ sublattice L m j) (b : Bond L m j) :
    (bondImage (affEquiv r t) b).edgeSet = affEquiv r t '' b.edgeSet := by
  obtain ⟨e1, e2⟩ := bondImage_ends r ht b
  obtain ⟨c, hc⟩ : ∃ c, c = bondImage (affEquiv r t) b := ⟨_, rfl⟩
  rw [← hc] at e1 e2 ⊢
  have hsl : ∀ d : Bond L m j, (d.target : FourTorus L m) =
      d.source + pointOnAxis L m d.axis d.orientedLength ∧
      (d.orientedLength = meshSize L j ∨ d.orientedLength = -meshSize L j) := by
    intro d
    rcases bond_target_cases d with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact ⟨by rw [h', h], Or.inl h'⟩
    · exact ⟨by rw [h', h], Or.inr h'⟩
  obtain ⟨hb, hb'⟩ := hsl b
  obtain ⟨hc1, hc'⟩ := hsl c
  have himg : (c.target : FourTorus L m) = c.source + pointOnAxis L m (r.1⁻¹ b.axis)
      (((r.2 (r.1⁻¹ b.axis) : ℤ) : ℝ) * b.orientedLength) := by
    rw [e2, e1, hb, affEquiv_add_pointOnAxis]
  have hε := unitCast_cases (r.2 (r.1⁻¹ b.axis))
  have hu : ((r.2 (r.1⁻¹ b.axis) : ℤ) : ℝ) * b.orientedLength = meshSize L j ∨
      ((r.2 (r.1⁻¹ b.axis) : ℤ) : ℝ) * b.orientedLength = -meshSize L j := by
    rcases hε with h | h <;> rcases hb' with h' | h' <;> rw [h, h'] <;> simp
  have heq : pointOnAxis L m (r.1⁻¹ b.axis)
      (((r.2 (r.1⁻¹ b.axis) : ℤ) : ℝ) * b.orientedLength) =
      pointOnAxis L m c.axis c.orientedLength := by
    have := hc1.symm.trans himg
    exact (add_left_cancel this).symm
  obtain ⟨d1, d2⟩ := pointOnAxis_signed_injective hL hj hu hc' heq
  ext p
  constructor
  · rintro ⟨u, hu', rfl⟩
    refine ⟨_, ⟨u, hu', rfl⟩, ?_⟩
    rw [affEquiv_add_pointOnAxis, e1, ← d1, ← d2]
    congr 2
    ring
  · rintro ⟨_, ⟨u, hu', rfl⟩, rfl⟩
    refine ⟨u, hu', ?_⟩
    rw [affEquiv_add_pointOnAxis, e1, ← d1, ← d2]
    congr 2
    ring
theorem affEquiv_mapsCellsAndCubes (hL : 1 < L) (hj : -(m : ℤ) ≤ j) {r r' : SignedFrame}
    {t t' : FourTorus L m} (ht : t ∈ sublattice L m j) (ht' : t' ∈ sublattice L m j)
    (hs : (affEquiv r t).symm = affEquiv r' t') :
    MapsCellsAndCubes (affEquiv r t) j := by
  have hL0 : 0 < L := by omega
  have ha := meshSize_pos hL0 j
  have hS := two_mul_meshSize_le (m := m) hL0 hj
  have hpl : ∀ p : Plaquette L m j,
      (plaquetteImage (affEquiv r t) p).face = affEquiv r t '' p.face := by
    intro p
    have h : ∃ p' : Plaquette L m j, p'.face = affEquiv r t '' p.face := by
      obtain ⟨q, hq, -⟩ := exists_plaquette_image r ht p
      exact ⟨q, hq⟩
    unfold plaquetteImage
    rw [dif_pos h]
    exact h.choose_spec
  refine ⟨?_, ?_, ?_, bondImage_ends r ht, fun hj' b => bondImage_edgeSet hL hj' r ht b, hpl,
    ?_, ?_, fun y y' h => image_cubeAround r t h, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact affEquiv_mem_sublattice r ht hy
    · intro hx
      refine ⟨(affEquiv r t).symm x, ?_, by simp⟩
      rw [hs]
      exact affEquiv_mem_sublattice r' ht' hx
  · refine image_family_eq_self _ (fun S hS' => image_mem_bondEdgeSets hL0 hj r ht hS')
      fun S hS' => ?_
    rw [hs]
    exact image_mem_bondEdgeSets hL0 hj r' ht' hS'
  · have hsq : ∀ (r : SignedFrame) (t : FourTorus L m), t ∈ sublattice L m j →
        ∀ S ∈ plaquetteFaces L m j, affEquiv r t '' S ∈ plaquetteFaces L m j := by
      rintro r t ht _ ⟨p, rfl⟩
      obtain ⟨q, hq, -⟩ := exists_plaquette_image r ht p
      exact ⟨q, hq⟩
    refine image_family_eq_self _ (hsq r t ht) fun S hS' => ?_
    rw [hs]
    exact hsq r' t' ht' S hS'
  · intro b b' h
    obtain ⟨x₁, -, e₁, e₂⟩ := edgeSet_eq_axisArc hL0 b'
    obtain ⟨x, hx, e₃, e₄⟩ := edgeSet_eq_axisArc hL0 b
    obtain ⟨x', -, μ', e₅, e₆⟩ := image_axisArc r ht hx b.axis
    rw [e₁, e₃, e₅] at h
    obtain ⟨h₁, h₂⟩ := axisArc_injective hL0 ha hS h
    rw [e₂, e₄, e₆, h₁, h₂]
  · intro p
    obtain ⟨q, hq₁, hq₂⟩ := exists_plaquette_image r ht p
    have : plaquetteImage (affEquiv r t) p = q := face_injective hL0 hj (by rw [hpl, hq₁])
    rw [this, hq₂]
  · have hc : ∀ (r : SignedFrame) (t : FourTorus L m), t ∈ sublattice L m j →
        ∀ Q ∈ standardCubePartition L m j, affEquiv r t '' Q ∈ standardCubePartition L m j := by
      rintro r t ht _ ⟨y, rfl⟩
      exact ⟨⟨affEquiv r t y, affEquiv_mem_sublattice r ht y.2⟩, (image_cubeAround r t rfl).symm⟩
    refine image_family_eq_self _ (hc r t ht) fun S hS' => ?_
    rw [hs]
    exact hc r' t' ht' S hS'
theorem image_sUnion_of_iff {α : Type*} (σ : α ≃ α) {S S' : Set (Set α)}
    (h : ∀ Q, σ '' Q ∈ S' ↔ Q ∈ S) : σ '' ⋃₀ S = ⋃₀ S' := by
  ext x
  constructor
  · rintro ⟨y, ⟨Q, hQ, hy⟩, rfl⟩
    exact ⟨σ '' Q, (h Q).2 hQ, mem_image_of_mem σ hy⟩
  · rintro ⟨Q', hQ', hx⟩
    refine ⟨σ.symm x, ⟨σ.symm '' Q', (h _).1 (by rwa [σ.image_symm_image]), ?_⟩, by simp⟩
    exact mem_image_of_mem _ hx
theorem image_sInter_of_iff {α : Type*} (σ : α ≃ α) {S S' : Set (Set α)}
    (h : ∀ Q, σ '' Q ∈ S' ↔ Q ∈ S) : σ '' ⋂₀ S = ⋂₀ S' := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ Q' hQ'
    have h1 := hy (σ.symm '' Q') ((h _).1 (by rwa [σ.image_symm_image]))
    have h2 : σ y ∈ σ '' (σ.symm '' Q') := mem_image_of_mem _ h1
    rwa [σ.image_symm_image] at h2
  · intro hx
    refine ⟨σ.symm x, fun Q hQ => ?_, by simp⟩
    have h1 := hx (σ '' Q) ((h Q).2 hQ)
    obtain ⟨y, hy, rfl⟩ := h1
    simpa using hy
theorem isChain_map_iff_of_iff {α : Type*} {R R' : α → α → Prop} (f : α → α)
    (h : ∀ a b, R (f a) (f b) ↔ R' a b) : ∀ c : List α, (c.map f).IsChain R ↔ c.IsChain R'
  | [] => by simp
  | [a] => by simp
  | a :: b :: l => by
    have ih := isChain_map_iff_of_iff f h (b :: l)
    simp only [List.map_cons, List.isChain_cons_cons] at ih ⊢
    rw [h, ih]
section Transport
variable {σ : FourTorus L m ≃ FourTorus L m}
theorem partition_iff_symm
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (Q : Set (FourTorus L m)) :
    σ.symm '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j := by
  have := hP (σ.symm '' Q)
  rw [σ.image_symm_image] at this
  exact this.symm
theorem image_mem_partitionCubesIn_iff
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (X Q : Set (FourTorus L m)) : σ '' Q ∈ partitionCubesIn j (σ '' X) ↔ Q ∈ partitionCubesIn j X :=
  and_congr (hP Q) (image_subset_image_iff σ.injective)
theorem exists_partitionCube_image_iff
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (X : Set (FourTorus L m)) (p : Set (FourTorus L m) → Prop) :
    (∃ Q' ∈ partitionCubesIn j (σ '' X), p Q') ↔ ∃ Q ∈ partitionCubesIn j X, p (σ '' Q) := by
  constructor
  · rintro ⟨Q', h, hp⟩
    refine ⟨σ.symm '' Q', (image_mem_partitionCubesIn_iff hP X _).1 (by rwa [σ.image_symm_image]),
      ?_⟩
    rwa [σ.image_symm_image]
  · rintro ⟨Q, h, hp⟩
    exact ⟨_, (image_mem_partitionCubesIn_iff hP X Q).2 h, hp⟩
theorem cubesMeet_image_iff (σ : FourTorus L m ≃ FourTorus L m) (Q Q' : Set (FourTorus L m)) :
    CubesMeet (σ '' Q) (σ '' Q') ↔ CubesMeet Q Q' := by
  unfold CubesMeet
  rw [← image_inter σ.injective, image_nonempty]
theorem image_complementRegion
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (X : Set (FourTorus L m)) : σ '' complementRegion j X = complementRegion j (σ '' X) :=
  image_sUnion_of_iff σ fun Q =>
    and_congr (hP Q) (not_congr (image_mem_partitionCubesIn_iff hP X Q))
theorem image_addCubeLayer
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (X : Set (FourTorus L m)) : σ '' addCubeLayer j X = addCubeLayer j (σ '' X) := by
  refine image_sUnion_of_iff σ fun Q => and_congr (hP Q) ?_
  rw [exists_partitionCube_image_iff hP]
  simp only [cubesMeet_image_iff]
theorem image_peelCubeLayer
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (X : Set (FourTorus L m)) : σ '' peelCubeLayer j X = peelCubeLayer j (σ '' X) := by
  refine image_sUnion_of_iff σ fun Q =>
    and_congr (image_mem_partitionCubesIn_iff hP X Q) (not_congr ?_)
  rw [← image_complementRegion hP, exists_partitionCube_image_iff hP]
  simp only [cubesMeet_image_iff]
theorem image_layerEnlargement
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (X : Set (FourTorus L m)) (n : ℤ) :
    σ '' layerEnlargement j X n = layerEnlargement j (σ '' X) n := by
  have h1 : Function.Semiconj (fun S : Set (FourTorus L m) => σ '' S) (addCubeLayer j)
      (addCubeLayer j) := image_addCubeLayer hP
  have h2 : Function.Semiconj (fun S : Set (FourTorus L m) => σ '' S) (peelCubeLayer j)
      (peelCubeLayer j) := image_peelCubeLayer hP
  cases n with
  | ofNat n => exact h1.iterate_right n X
  | negSucc n => exact h2.iterate_right (n + 1) X
theorem image_cubeHull
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (Y : Set (FourTorus L m)) : σ '' cubeHull j Y = cubeHull j (σ '' Y) := by
  refine image_sUnion_of_iff σ fun Q => and_congr (hP Q) ?_
  unfold CubeIntersects
  rw [← image_inter σ.injective, image_nonempty]
theorem isPartitionRegion_image
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    {X : Set (FourTorus L m)} (h : IsPartitionRegion j X) : IsPartitionRegion j (σ '' X) := by
  obtain ⟨C, hC, rfl⟩ := h
  refine ⟨(fun Q => σ '' Q) '' C, ?_, image_sUnion_of_iff σ fun Q => ?_⟩
  · rintro _ ⟨Q, hQ, rfl⟩
    exact (hP Q).2 (hC hQ)
  · exact (σ.injective.image_injective).mem_set_image
theorem isPartitionRegion_image_iff
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (X : Set (FourTorus L m)) : IsPartitionRegion j (σ '' X) ↔ IsPartitionRegion j X := by
  refine ⟨fun h => ?_, isPartitionRegion_image hP⟩
  have := isPartitionRegion_image (σ := σ.symm) (partition_iff_symm hP) h
  rwa [σ.symm_image_image] at this
theorem isCubeChainIn_map_iff
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (X : Set (FourTorus L m)) (c : List (Set (FourTorus L m))) :
    IsCubeChainIn j (σ '' X) (c.map fun Q => σ '' Q) ↔ IsCubeChainIn j X c := by
  unfold IsCubeChainIn
  rw [isChain_map_iff_of_iff _ (cubesMeet_image_iff σ)]
  simp only [List.forall_mem_map, image_mem_partitionCubesIn_iff hP]
theorem chainConnectedIn_image
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    {X Q Q' : Set (FourTorus L m)} (h : ChainConnectedIn j X Q Q') :
    ChainConnectedIn j (σ '' X) (σ '' Q) (σ '' Q') := by
  obtain ⟨c, hc, h1, h2⟩ := h
  refine ⟨c.map fun Q => σ '' Q, (isCubeChainIn_map_iff hP X c).2 hc, ?_, ?_⟩
  · rw [List.head?_map, h1]
    rfl
  · rw [List.getLast?_map, h2]
    rfl
theorem chainConnectedIn_image_iff
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (X Q Q' : Set (FourTorus L m)) :
    ChainConnectedIn j (σ '' X) (σ '' Q) (σ '' Q') ↔ ChainConnectedIn j X Q Q' := by
  refine ⟨fun h => ?_, chainConnectedIn_image hP⟩
  have := chainConnectedIn_image (σ := σ.symm) (partition_iff_symm hP) h
  simpa only [σ.symm_image_image] using this
theorem image_mem_regionComponents
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    {X C : Set (FourTorus L m)} (h : C ∈ regionComponents j X) :
    σ '' C ∈ regionComponents j (σ '' X) := by
  obtain ⟨Q, hQ, rfl⟩ := h
  exact ⟨σ '' Q, (image_mem_partitionCubesIn_iff hP X Q).2 hQ,
    image_sUnion_of_iff σ fun Q' => chainConnectedIn_image_iff hP X Q Q'⟩
theorem image_mem_regionComponents_iff
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (X C : Set (FourTorus L m)) :
    σ '' C ∈ regionComponents j (σ '' X) ↔ C ∈ regionComponents j X := by
  refine ⟨fun h => ?_, image_mem_regionComponents hP⟩
  have := image_mem_regionComponents (σ := σ.symm) (partition_iff_symm hP) h
  simpa only [σ.symm_image_image] using this
theorem image_regionComponents
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (X : Set (FourTorus L m)) :
    (fun C => σ '' C) '' regionComponents j X = regionComponents j (σ '' X) := by
  ext C
  constructor
  · rintro ⟨C', h, rfl⟩
    exact image_mem_regionComponents hP h
  · intro h
    refine ⟨σ.symm '' C, (image_mem_regionComponents_iff hP X _).1 (by rwa [σ.image_symm_image]),
      ?_⟩
    exact σ.image_symm_image C
theorem regionsMeet_image_iff
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (X X' : Set (FourTorus L m)) : RegionsMeet j (σ '' X) (σ '' X') ↔ RegionsMeet j X X' := by
  unfold RegionsMeet
  rw [exists_partitionCube_image_iff hP X]
  simp only [exists_partitionCube_image_iff hP X', cubesMeet_image_iff]
end Transport
theorem affEquiv_coord (r : SignedFrame) (t x : FourTorus L m) (μ : Fin 4) :
    affEquiv r t x (r.1⁻¹ μ) = (r.2 (r.1⁻¹ μ) : ℤ) • x μ + t (r.1⁻¹ μ) := by
  have e : r.1 (r.1⁻¹ μ) = μ := by simp
  rw [affEquiv_apply, Pi.add_apply, torusEquiv_apply, e]
theorem unit_zsmul_injective (s : ℤˣ) {A : Type*} [AddCommGroup A] {a b : A}
    (h : (s : ℤ) • a = (s : ℤ) • b) : a = b := by
  have e : ∀ c : A, (s : ℤ) • (s : ℤ) • c = c := fun c => by
    have e1 : (s : ℤ) * (s : ℤ) = 1 := by
      rw [← Units.val_mul, Int.units_mul_self]
      rfl
    rw [smul_smul, e1, one_smul]
  rw [← e a, h, e b]
theorem isCubeFace_image (r : SignedFrame) {t : FourTorus L m} (ht : t ∈ sublattice L m j)
    {F Q : Set (FourTorus L m)} (h : IsCubeFace j F Q) :
    IsCubeFace j (affEquiv r t '' F) (affEquiv r t '' Q) := by
  obtain ⟨y, rfl, μ, ε, hε, rfl⟩ := h
  have hs := unitCast_cases (r.2 (r.1⁻¹ μ))
  have hz : ∀ c : ℝ, (r.2 (r.1⁻¹ μ) : ℤ) • (c : AddCircle (torusSide L m)) =
      ((((r.2 (r.1⁻¹ μ) : ℤ) : ℝ) * c : ℝ) : AddCircle (torusSide L m)) := fun c => by
    rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
  have hc : (((((r.2 (r.1⁻¹ μ) : ℤ) : ℝ) * ε) * meshSize L j / 2 : ℝ) :
        AddCircle (torusSide L m)) =
      (r.2 (r.1⁻¹ μ) : ℤ) • ((ε * meshSize L j / 2 : ℝ) : AddCircle (torusSide L m)) := by
    rw [hz]
    congr 1
    ring
  refine ⟨⟨affEquiv r t y, affEquiv_mem_sublattice r ht y.2⟩, image_cubeAround r t rfl, r.1⁻¹ μ,
    ((r.2 (r.1⁻¹ μ) : ℤ) : ℝ) * ε, ?_, ?_⟩
  · rcases hs with h | h <;> rcases hε with h' | h' <;> rw [h, h'] <;> simp
  · ext p
    constructor
    · rintro ⟨x, ⟨hxQ, hx⟩, rfl⟩
      refine ⟨mem_image_of_mem _ hxQ, ?_⟩
      change _ = affEquiv r t y (r.1⁻¹ μ) + _
      rw [hc, affEquiv_coord, affEquiv_coord, hx, smul_add]
      abel
    · rintro ⟨⟨x, hxQ, rfl⟩, hx⟩
      refine ⟨x, ⟨hxQ, ?_⟩, rfl⟩
      have hx' : affEquiv r t x (r.1⁻¹ μ) = affEquiv r t y (r.1⁻¹ μ) +
          (((((r.2 (r.1⁻¹ μ) : ℤ) : ℝ) * ε) * meshSize L j / 2 : ℝ) :
            AddCircle (torusSide L m)) := hx
      rw [hc, affEquiv_coord, affEquiv_coord, add_right_comm, add_left_inj, ← smul_add] at hx'
      exact unit_zsmul_injective _ hx'
theorem cubesShareFace_image (r : SignedFrame) {t : FourTorus L m} (ht : t ∈ sublattice L m j)
    {Q Q' : Set (FourTorus L m)} (h : CubesShareFace j Q Q') :
    CubesShareFace j (affEquiv r t '' Q) (affEquiv r t '' Q') := by
  unfold CubesShareFace at h ⊢
  rw [← image_inter (affEquiv r t).injective]
  exact ⟨isCubeFace_image r ht h.1, isCubeFace_image r ht h.2⟩
theorem cubesShareFace_image_iff {r r' : SignedFrame} {t t' : FourTorus L m}
    (ht : t ∈ sublattice L m j) (ht' : t' ∈ sublattice L m j)
    (hs : (affEquiv r t).symm = affEquiv r' t') (Q Q' : Set (FourTorus L m)) :
    CubesShareFace j (affEquiv r t '' Q) (affEquiv r t '' Q') ↔ CubesShareFace j Q Q' := by
  refine ⟨fun h => ?_, cubesShareFace_image r ht⟩
  have := cubesShareFace_image r' ht' h
  rw [← hs] at this
  simpa only [(affEquiv r t).symm_image_image] using this
def realAffine (r : SignedFrame) (v : Fin 4 → ℝ) : (Fin 4 → ℝ) ≃ (Fin 4 → ℝ) where
  toFun x := r.actOnVector x + v
  invFun y := (frameInverse r).actOnVector (y - v)
  left_inv x := by simp [frameInverse_actOnVector_actOnVector]
  right_inv y := by simp [actOnVector_frameInverse_actOnVector]
theorem realAffine_apply (r : SignedFrame) (v x : Fin 4 → ℝ) :
    realAffine r v x = r.actOnVector x + v := rfl
theorem realAffine_symm (r : SignedFrame) (v : Fin 4 → ℝ) :
    (realAffine r v).symm = realAffine (frameInverse r) (-(frameInverse r).actOnVector v) := by
  ext1 y
  change (frameInverse r).actOnVector (y - v) = _
  rw [actOnVector_sub, realAffine_apply, sub_eq_add_neg]
def imageLower (r : SignedFrame) (v a b : Fin 4 → ℝ) : Fin 4 → ℝ := fun μ =>
  if ((r.2 μ : ℤ) : ℝ) = 1 then a (r.1 μ) + v μ else -b (r.1 μ) + v μ
def imageUpper (r : SignedFrame) (v a b : Fin 4 → ℝ) : Fin 4 → ℝ := fun μ =>
  if ((r.2 μ : ℤ) : ℝ) = 1 then b (r.1 μ) + v μ else -a (r.1 μ) + v μ
theorem realAffine_image_boxOfIntervals (r : SignedFrame) (v a b : Fin 4 → ℝ) :
    realAffine r v '' TorusBox.boxOfIntervals a b =
      TorusBox.boxOfIntervals (imageLower r v a b) (imageUpper r v a b) := by
  have hm1 : (-1 : ℝ) ≠ 1 := by norm_num
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ μ _
    have h := hx (r.1 μ) (mem_univ _)
    obtain ⟨h1, h2⟩ := h
    rcases unitCast_cases (r.2 μ) with e | e
    · simp only [imageLower, imageUpper, e, if_true, realAffine_apply, Pi.add_apply,
        actOnVector_apply, mem_Icc]
      constructor <;> linarith
    · simp only [imageLower, imageUpper, e, if_neg hm1, realAffine_apply, Pi.add_apply,
        actOnVector_apply, mem_Icc]
      constructor <;> linarith
  · intro hy
    refine ⟨(realAffine r v).symm y, fun ν _ => ?_, by simp⟩
    have h := hy (r.1⁻¹ ν) (mem_univ _)
    have e0 : r.1 (r.1⁻¹ ν) = ν := by simp
    have hval : (realAffine r v).symm y ν =
        ((r.2 (r.1⁻¹ ν) : ℤ) : ℝ) * (y (r.1⁻¹ ν) - v (r.1⁻¹ ν)) := rfl
    rw [hval]
    obtain ⟨h1, h2⟩ := h
    rcases unitCast_cases (r.2 (r.1⁻¹ ν)) with e | e
    · simp only [imageLower, imageUpper, e, if_true, e0] at h1 h2
      rw [e]
      constructor <;> linarith
    · simp only [imageLower, imageUpper, e, if_neg hm1, e0] at h1 h2
      rw [e]
      constructor <;> linarith
def imageCorner (r : SignedFrame) (v y : Fin 4 → ℝ) (c : ℝ) : Fin 4 → ℝ :=
  imageLower r v y fun μ => y μ + c
theorem realAffine_image_cornerCube (r : SignedFrame) (v y : Fin 4 → ℝ) (c : ℝ) :
    realAffine r v '' cornerCube y c = cornerCube (imageCorner r v y c) c := by
  unfold cornerCube
  rw [realAffine_image_boxOfIntervals]
  congr 1
  funext μ
  have hm1 : (-1 : ℝ) ≠ 1 := by norm_num
  rcases unitCast_cases (r.2 μ) with e | e
  · simp only [imageCorner, imageLower, imageUpper, e, if_true]
    ring
  · simp only [imageCorner, imageLower, imageUpper, e, if_neg hm1]
    ring
section Boxes
variable {σ : FourTorus L m ≃ FourTorus L m} {r : SignedFrame} {v : Fin 4 → ℝ}
theorem torusProj_realAffine (h : IsInducedByAffine σ r v) (x : Fin 4 → ℝ) :
    torusProj (torusSide L m) (realAffine r v x) = σ (torusProj (torusSide L m) x) := (h x).symm
theorem torusProj_image_realAffine_image (h : IsInducedByAffine σ r v) (A : Set (Fin 4 → ℝ)) :
    torusProj (torusSide L m) '' (realAffine r v '' A) =
      σ '' (torusProj (torusSide L m) '' A) := by
  rw [image_image, image_image]
  exact image_congr fun x _ => torusProj_realAffine h x
theorem isPartitionBox_image
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (h : IsInducedByAffine σ r v) {X : Set (FourTorus L m)} (hX : IsPartitionBox j X) :
    IsPartitionBox j (σ '' X) := by
  obtain ⟨hR, ⟨c⟩⟩ := hX
  have hm1 : (-1 : ℝ) ≠ 1 := by norm_num
  refine ⟨isPartitionRegion_image hP hR,
    ⟨⟨imageLower r v c.lower c.upper, imageUpper r v c.lower c.upper, fun μ => ?_, ?_, ?_⟩⟩⟩
  · have := c.lower_le_upper (r.1 μ)
    rcases unitCast_cases (r.2 μ) with e | e
    · simp only [imageLower, imageUpper, e, if_true]
      linarith
    · simp only [imageLower, imageUpper, e, if_neg hm1]
      linarith
  · rw [← realAffine_image_boxOfIntervals]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    rw [torusProj_realAffine h, torusProj_realAffine h] at hxy
    rw [c.injOn_proj hx hy (σ.injective hxy)]
  · rw [← realAffine_image_boxOfIntervals, torusProj_image_realAffine_image h, c.image_proj]
theorem isPartitionBox_image_iff {r' : SignedFrame} {v' : Fin 4 → ℝ}
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (h : IsInducedByAffine σ r v) (h' : IsInducedByAffine σ.symm r' v')
    (X : Set (FourTorus L m)) : IsPartitionBox j (σ '' X) ↔ IsPartitionBox j X := by
  refine ⟨fun hX => ?_, isPartitionBox_image hP h⟩
  have := isPartitionBox_image (partition_iff_symm hP) h' hX
  rwa [σ.symm_image_image] at this
theorem liesInCornerCube_image (h : IsInducedByAffine σ r v) {C : Set (FourTorus L m)}
    {y : Fin 4 → ℝ} (hy : LiesInCornerCube L m j C y) :
    LiesInCornerCube L m j (σ '' C) (imageCorner r v y (100 * meshSize L j)) := by
  unfold LiesInCornerCube at hy ⊢
  rw [← realAffine_image_cornerCube, torusProj_image_realAffine_image h]
  exact image_mono hy
theorem isSmallRegionComponent_image
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (h : IsInducedByAffine σ r v) {X C : Set (FourTorus L m)}
    (hC : IsSmallRegionComponent j X C) : IsSmallRegionComponent j (σ '' X) (σ '' C) := by
  obtain ⟨h1, h2, y, hy⟩ := hC
  exact ⟨image_mem_regionComponents hP h1, h2, _, liesInCornerCube_image h hy⟩
theorem isSmallRegionComponent_image_iff {r' : SignedFrame} {v' : Fin 4 → ℝ}
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (h : IsInducedByAffine σ r v) (h' : IsInducedByAffine σ.symm r' v')
    (X C : Set (FourTorus L m)) :
    IsSmallRegionComponent j (σ '' X) (σ '' C) ↔ IsSmallRegionComponent j X C := by
  refine ⟨fun hC => ?_, isSmallRegionComponent_image hP h⟩
  have := isSmallRegionComponent_image (partition_iff_symm hP) h' hC
  simpa only [σ.symm_image_image] using this
theorem liftToCornerCube_image (h : IsInducedByAffine σ r v) (C : Set (FourTorus L m))
    (y : Fin 4 → ℝ) :
    liftToCornerCube j (σ '' C) (imageCorner r v y (100 * meshSize L j)) =
      realAffine r v '' liftToCornerCube j C y := by
  unfold liftToCornerCube
  rw [← realAffine_image_cornerCube]
  ext w
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hw⟩
    refine ⟨z, ⟨hz, ?_⟩, rfl⟩
    rw [torusProj_realAffine h] at hw
    exact (σ.injective.mem_set_image).1 hw
  · rintro ⟨z, ⟨hz, hc⟩, rfl⟩
    refine ⟨mem_image_of_mem _ hz, ?_⟩
    rw [torusProj_realAffine h]
    exact mem_image_of_mem _ hc
theorem exists_boxOfIntervals_image_iff (r : SignedFrame) (v : Fin 4 → ℝ) (P : Set (Fin 4 → ℝ)) :
    (∃ a b, realAffine r v '' P = TorusBox.boxOfIntervals a b) ↔
      ∃ a b, P = TorusBox.boxOfIntervals a b := by
  constructor
  · rintro ⟨a, b, e⟩
    have e' : P = (realAffine r v).symm '' TorusBox.boxOfIntervals a b := by
      rw [← e, (realAffine r v).symm_image_image]
    rw [realAffine_symm, realAffine_image_boxOfIntervals] at e'
    exact ⟨_, _, e'⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨_, _, realAffine_image_boxOfIntervals r v a b⟩
theorem realAffine_image_boundingBox (r : SignedFrame) (v : Fin 4 → ℝ) (A : Set (Fin 4 → ℝ)) :
    realAffine r v '' boundingBox A = boundingBox (realAffine r v '' A) :=
  image_sInter_of_iff (realAffine r v) fun P =>
    and_congr (image_subset_image_iff (realAffine r v).injective)
      (exists_boxOfIntervals_image_iff r v P)
theorem image_componentBox
    (hG : ComponentBoxIndependentOfCube)
    (hodd : Odd L) (h13 : 13 ≤ L) (hm : 0 < m) (hj : -(m : ℤ) ≤ j)
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (h : IsInducedByAffine σ r v) {X C : Set (FourTorus L m)} (hX : IsPartitionRegion j X)
    (hC : IsSmallRegionComponent j X C) : σ '' componentBox j C = componentBox j (σ '' C) := by
  obtain ⟨h1, h2, y₀, hy₀⟩ := hC
  have hy : LiesInCornerCube L m j C (Classical.epsilon (LiesInCornerCube L m j C)) :=
    Classical.epsilon_spec ⟨y₀, hy₀⟩
  have hy' := liesInCornerCube_image h hy
  obtain ⟨-, -, -, -, e⟩ := hG L m hodd h13 hm j hj h2 (σ '' X) (σ '' C)
    (isPartitionRegion_image hP hX) (image_mem_regionComponents hP h1) _ _ hy' hy'
  rw [e, liftToCornerCube_image h, ← realAffine_image_boundingBox,
    torusProj_image_realAffine_image h]
  rfl
theorem image_boxingOnce
    (hG : ComponentBoxIndependentOfCube)
    (hodd : Odd L) (h13 : 13 ≤ L) (hm : 0 < m) (hj : -(m : ℤ) ≤ j) {r' : SignedFrame}
    {v' : Fin 4 → ℝ}
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (h : IsInducedByAffine σ r v) (h' : IsInducedByAffine σ.symm r' v')
    {X : Set (FourTorus L m)} (hX : IsPartitionRegion j X) :
    σ '' boxingOnce j X = boxingOnce j (σ '' X) := by
  unfold boxingOnce
  rw [image_union]
  congr 1
  refine image_sUnion_of_iff σ fun Q => ?_
  constructor
  · rintro ⟨C', hC', e⟩
    have hC : IsSmallRegionComponent j X (σ.symm '' C') :=
      (isSmallRegionComponent_image_iff hP h h' X _).1 (by rwa [σ.image_symm_image])
    refine ⟨_, hC, ?_⟩
    apply σ.injective.image_injective
    rw [image_componentBox hG hodd h13 hm hj hP h hX hC, σ.image_symm_image]
    exact e
  · rintro ⟨C, hC, rfl⟩
    exact ⟨_, isSmallRegionComponent_image hP h hC,
      (image_componentBox hG hodd h13 hm hj hP h hX hC).symm⟩
theorem image_boxClosure
    (hG : ComponentBoxIndependentOfCube)
    (hB : ComponentBoxesAreRegions L m j)
    (hodd : Odd L) (h13 : 13 ≤ L) (hm : 0 < m) (hj : -(m : ℤ) ≤ j) {r' : SignedFrame}
    {v' : Fin 4 → ℝ}
    (hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j)
    (h : IsInducedByAffine σ r v) (h' : IsInducedByAffine σ.symm r' v')
    {X : Set (FourTorus L m)} (hX : IsPartitionRegion j X) :
    σ '' boxClosure j X = boxClosure j (σ '' X) := by
  have hreg : ∀ n : ℕ, IsPartitionRegion j ((boxingOnce j)^[n] X) := by
    intro n
    induction n with
    | zero => exact hX
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (hB _ ih).2.1
  have hit : ∀ n : ℕ, σ '' (boxingOnce j)^[n] X = (boxingOnce j)^[n] (σ '' X) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        image_boxingOnce hG hodd h13 hm hj hP h h' (hreg n), ih]
  have hset : {n | (boxingOnce j)^[n + 1] (σ '' X) = (boxingOnce j)^[n] (σ '' X)} =
      {n | (boxingOnce j)^[n + 1] X = (boxingOnce j)^[n] X} := by
    ext n
    change (boxingOnce j)^[n + 1] (σ '' X) = (boxingOnce j)^[n] (σ '' X) ↔
      (boxingOnce j)^[n + 1] X = (boxingOnce j)^[n] X
    rw [← hit, ← hit]
    exact σ.injective.image_injective.eq_iff
  unfold boxClosure
  rw [hset]
  exact hit _
end Boxes
theorem latticeIsometryGroupAction (hCubes : StandardPartitionCubeGeometry)
    (hG : ComponentBoxIndependentOfCube) :
    LatticeIsometryGroupActionStatement := by
  intro L m i hs hm hi
  obtain ⟨hodd, h13⟩ := hs
  have hL1 : 1 < L := by omega
  have hL0 : 0 < L := by omega
  refine ⟨⟨latticeIsometries_isSubgroup i, latticeIsometries_finite hL0 hi⟩, ?_,
    fun i' hii => ?_, latticeIsometriesContainGenerators L m i, ?_⟩
  · rintro σ ⟨r, v, -, h⟩
    refine ⟨?_, preservesSegmentLengths σ⟩
    rw [eq_affEquiv h]
    exact affEquiv_preservesTorusMetrics r _
  · rintro σ ⟨r, v, hv, h⟩
    exact ⟨r, v, meshVectors_mono hL0 hii hv, h⟩
  · intro σ hσ j hij
    obtain ⟨r, v, hv, h⟩ := id hσ
    obtain ⟨r', v', hv', h'⟩ := symm_mem_latticeIsometries hσ
    have hj : -(m : ℤ) ≤ j := hi.trans hij
    have ht := toFourTorus_mem_sublattice (m := m) (meshVectors_mono hL0 hij hv)
    have ht' := toFourTorus_mem_sublattice (m := m) (meshVectors_mono hL0 hij hv')
    have hsymm : (affEquiv r (toFourTorus L m v)).symm = affEquiv r' (toFourTorus L m v') := by
      rw [← eq_affEquiv h, ← eq_affEquiv h']
    have hcarry := affEquiv_mapsCellsAndCubes hL1 hj ht ht' hsymm
    have hadj := cubesShareFace_image_iff ht ht' hsymm
    rw [← eq_affEquiv h] at hcarry hadj
    have hP : ∀ Q, σ '' Q ∈ standardCubePartition L m j ↔ Q ∈ standardCubePartition L m j := by
      have hpart := hcarry.2.2.2.2.2.2.2.2.2
      intro Q
      constructor
      · intro hq
        rw [← hpart] at hq
        obtain ⟨Q', hQ', e⟩ := hq
        rwa [← σ.injective.image_injective e]
      · intro hq
        rw [← hpart]
        exact ⟨Q, hq, rfl⟩
    have hB := (hCubes L m hodd h13 hm j hj).2.2.2.2
    refine ⟨hcarry, isPartitionRegion_image_iff hP,
      fun Q _ Q' _ => ⟨cubesMeet_image_iff σ Q Q', hadj Q Q'⟩,
      fun X X' _ _ => regionsMeet_image_iff hP X X',
      fun X _ c => ⟨isCubeChainIn_map_iff hP X c, ?_⟩,
      fun X hX => ⟨image_complementRegion hP X, image_regionComponents hP X,
        image_layerEnlargement hP X, isPartitionBox_image_iff hP h h' X,
        isSmallRegionComponent_image_iff hP h h' X,
        fun C hC => image_componentBox hG hodd h13 hm hj hP h hX hC,
        image_boxClosure hG hB hodd h13 hm hj hP h h' hX⟩, image_cubeHull hP⟩
    unfold IsFaceChainIn
    rw [isChain_map_iff_of_iff _ hadj]
    simp only [List.forall_mem_map, image_mem_partitionCubesIn_iff hP]
end YangMills.Construction.PeriodicLattice.IsometryAction
