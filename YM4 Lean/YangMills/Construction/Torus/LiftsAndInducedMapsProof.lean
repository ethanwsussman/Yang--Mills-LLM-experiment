import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.Torus.GeometryTransportLiftAndDilationOfTestPairsProof
import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLatticeProof
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctionsProof
import YangMills.Construction.SourcesAndGluing.LatticeSimilarities
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set Function TorusMetric PeriodicLattice TestFunctions
open AmbientPoints (euclidNormVec_eq_norm torusEuclidNorm_eq_norm torusEuclidNorm_torusProj_le
  exists_torusProj_eq_euclidNormVec_eq)
open InfiniteLattice (AmbientSpace)
open scoped Topology
namespace TorusLifts
namespace LiftsAndDescendedMaps
variable {ℓ : ℝ}
theorem torusProj_add (x y : AmbientSpace) : torusProj ℓ (x + y) = torusProj ℓ x + torusProj ℓ y := by apply _root_.YangMills.Construction.AffineTorusIsometries.torusProj_add' <;> assumption
theorem torusProj_sub (x y : AmbientSpace) : torusProj ℓ (x - y) = torusProj ℓ x - torusProj ℓ y := by apply _root_.YangMills.Construction.AffineTorusIsometries.torusProj_sub' <;> assumption
theorem torusProj_zero : torusProj ℓ (0 : AmbientSpace) = 0 := by apply _root_.YangMills.Construction.AffineTorusIsometries.torusProj_zero' <;> assumption
theorem torusProj_sub_latticeTranslate (v : AmbientSpace) (k : Fin 4 → ℤ) :
    torusProj ℓ (v - latticeTranslate ℓ k) = torusProj ℓ v := by apply _root_.YangMills.Construction.TestFunctions.PairTransport.torusProj_sub_latticeTranslate <;> assumption
theorem latticeTranslate_neg (k : Fin 4 → ℤ) : latticeTranslate ℓ (-k) = -latticeTranslate ℓ k := by apply _root_.YangMills.Construction.ReflectionPositivity.CutoffMirrors.TorusMetricSpace.latticeTranslate_neg <;> assumption
theorem latticeTranslate_mul_side (c : ℝ) (k : Fin 4 → ℤ) :
    latticeTranslate (c * ℓ) k = c • latticeTranslate ℓ k := by
  funext μ
  simp [latticeTranslate, mul_assoc]
theorem euclidNormVec_sub_comm (x y : AmbientSpace) : euclidNormVec (x - y) = euclidNormVec (y - x) := by apply _root_.YangMills.SharedProofs.p26380 <;> assumption
theorem euclidNormVec_smul (c : ℝ) (v : AmbientSpace) : euclidNormVec (c • v) = |c| * euclidNormVec v := by apply _root_.YangMills.Construction.UnitSpacing.euclidNormVec_smul <;> assumption
theorem abs_apply_le_euclidNormVec (v : AmbientSpace) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.SharedProofs.p10398 <;> assumption
theorem isLeast_norm_lifts (x y : AmbientSpace) :
    IsLeast (range fun k : Fin 4 → ℤ => euclidNormVec (x - y - latticeTranslate ℓ k))
      (torusEuclidNorm (torusProj ℓ x - torusProj ℓ y)) := by
  constructor
  · obtain ⟨b, hb, hb'⟩ := exists_torusProj_eq_euclidNormVec_eq (torusProj ℓ x - torusProj ℓ y)
    have h : torusProj ℓ b = torusProj ℓ (x - y) := by rw [hb, torusProj_sub]
    obtain ⟨k, hk⟩ := exists_latticeTranslate_of_torusProj_eq h
    refine ⟨-k, ?_⟩
    show euclidNormVec (x - y - latticeTranslate ℓ (-k)) = _
    rw [latticeTranslate_neg, sub_neg_eq_add, ← hk, hb']
  · rintro _ ⟨k, rfl⟩
    have h : torusProj ℓ x - torusProj ℓ y = torusProj ℓ (x - y - latticeTranslate ℓ k) := by
      rw [torusProj_sub_latticeTranslate, torusProj_sub]
    show torusEuclidNorm (torusProj ℓ x - torusProj ℓ y) ≤ euclidNormVec (x - y - latticeTranslate ℓ k)
    rw [h]
    exact torusEuclidNorm_torusProj_le _
theorem isLeast_norm_lifts_vec (d : AmbientSpace) :
    IsLeast (range fun k : Fin 4 → ℤ => euclidNormVec (d - latticeTranslate ℓ k))
      (torusEuclidNorm (torusProj ℓ d)) := by
  have h := isLeast_norm_lifts (ℓ := ℓ) d 0
  simpa [torusProj_zero] using h
theorem finite_shorter_translates (hℓ : 0 < ℓ) (d : AmbientSpace) :
    {k : Fin 4 → ℤ | euclidNormVec (d - latticeTranslate ℓ k) ≤ euclidNormVec d}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * euclidNormVec d / ℓ)
  refine (Set.Finite.pi' fun _ : Fin 4 => Set.finite_Icc (-(N : ℤ)) N).subset ?_
  intro k hk μ
  have hk' : euclidNormVec (d - latticeTranslate ℓ k) ≤ euclidNormVec d := hk
  have h1 := abs_le.mp ((abs_apply_le_euclidNormVec (d - latticeTranslate ℓ k) μ).trans hk')
  have h2 := abs_le.mp (abs_apply_le_euclidNormVec d μ)
  have h3 : (d - latticeTranslate ℓ k) μ = d μ - ℓ * (k μ : ℝ) := by simp [latticeTranslate]
  rw [h3] at h1
  have h4 : |ℓ * (k μ : ℝ)| ≤ 2 * euclidNormVec d :=
    abs_le.mpr ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩
  rw [abs_mul, abs_of_pos hℓ] at h4
  have h5 : |(k μ : ℝ)| ≤ (N : ℝ) := by
    refine le_trans ?_ hN
    rw [le_div_iff₀ hℓ, mul_comm]
    exact h4
  have h6 := abs_le.mp h5
  constructor
  · have := h6.1
    exact_mod_cast this
  · have := h6.2
    exact_mod_cast this
theorem torusDistEqMinOverLifts_of_pos (hℓ : 0 < ℓ) : TorusDistEqMinOverLifts ℓ := by
  rintro _ _ x y rfl rfl
  refine ⟨isLeast_norm_lifts x y, finite_shorter_translates hℓ _, ?_, ?_⟩
  · rw [← torusProj_sub]
    exact torusEuclidNorm_torusProj_le _
  · obtain ⟨k, hk⟩ := (isLeast_norm_lifts (ℓ := ℓ) x y).1
    refine ⟨y + latticeTranslate ℓ k, torusProj_add_latticeTranslate ℓ y k, ?_⟩
    rw [← sub_sub]
    exact hk
abbrev torusL2Metric (ℓ : ℝ) : MetricSpace (Torus4 ℓ) :=
  MetricSpace.induced (fun u => (WithLp.toLp 2 u : PiLp 2 fun _ : Fin 4 => AddCircle ℓ))
    (WithLp.toLp_injective 2) inferInstance
theorem continuous_id_torusL2Metric (ℓ : ℝ) :
    Continuous[inferInstance,
      (torusL2Metric ℓ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace]
      (id : Torus4 ℓ → Torus4 ℓ) :=
  continuous_induced_rng.2 (PiLp.continuous_toLp 2 _)
theorem continuous_torusProj : Continuous (torusProj ℓ) := by apply _root_.YangMills.Construction.TestPairs.continuous_torusProj <;> assumption
theorem torusDistIsMetric_of_pos (hℓ : 0 < ℓ) : TorusDistIsMetric ℓ := by
  have : Fact (0 < ℓ) := ⟨hℓ⟩
  refine ⟨torusL2Metric ℓ, fun u v => ?_, ?_, ?_⟩
  · show dist (WithLp.toLp 2 u : PiLp 2 fun _ : Fin 4 => AddCircle ℓ) (WithLp.toLp 2 v) = _
    rw [dist_eq_norm, ← WithLp.toLp_sub, torusEuclidNorm_eq_norm]
  · exact continuous_induced_rng.2 ((PiLp.continuous_toLp 2 _).comp continuous_torusProj)
  · exact @Function.Surjective.compactSpace (Torus4 ℓ) (Torus4 ℓ) inferInstance
      (torusL2Metric ℓ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace id
      (continuous_id_torusL2Metric ℓ) inferInstance surjective_id
theorem straightPathsLipschitz_holds : StraightPathsLipschitz ℓ := by
  rintro _ _ x y' rfl rfl h
  refine ⟨by simp [straightPath], by simp [straightPath], fun t _ t' _ => ?_⟩
  rw [straightPath, straightPath, ← torusProj_sub]
  have hv : (x + t • (y' - x)) - (x + t' • (y' - x)) = (t - t') • (y' - x) := by
    funext μ
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hv]
  refine (torusEuclidNorm_torusProj_le _).trans_eq ?_
  rw [euclidNormVec_smul, euclidNormVec_sub_comm, h]
theorem unit_cast_mul_self (e : ℤˣ) : (((e : ℤˣ) : ℤ) : ℝ) * (((e : ℤˣ) : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or e with h | h <;> simp [h]
theorem signedCoordinateEquiv_apply (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) (x : AmbientSpace)
    (μ : Fin 4) : signedCoordinateEquiv π s x μ = (((s μ : ℤˣ) : ℤ) : ℝ) * x (π μ) := rfl
variable {S : Equiv.Perm AmbientSpace}
theorem perm_apply_inv_apply (S : Equiv.Perm AmbientSpace) (x : AmbientSpace) : S (S⁻¹ x) = x := by
  rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
theorem perm_inv_apply_apply (S : Equiv.Perm AmbientSpace) (x : AmbientSpace) : S⁻¹ (S x) = x := by
  rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
theorem hyperoctahedral_map_add (hS : S ∈ hyperoctahedralGroupEuclidean) (x y : AmbientSpace) :
    S (x + y) = S x + S y := by apply _root_.YangMills.Construction.SourcesAndGluing.map_add_of_mem_hyperoctahedral <;> assumption
theorem hyperoctahedral_map_sub (hS : S ∈ hyperoctahedralGroupEuclidean) (x y : AmbientSpace) :
    S (x - y) = S x - S y := by
  obtain ⟨π, s, rfl⟩ := hS
  funext μ
  simp [signedCoordinateEquiv_apply, mul_sub]
theorem exists_map_latticeTranslate (hS : S ∈ hyperoctahedralGroupEuclidean) (ℓ : ℝ) (k : Fin 4 → ℤ) :
    ∃ k', S (latticeTranslate ℓ k) = latticeTranslate ℓ k' := by
  obtain ⟨π, s, rfl⟩ := hS
  refine ⟨fun μ => (s μ : ℤ) * k (π μ), ?_⟩
  funext μ
  simp only [signedCoordinateEquiv_apply, latticeTranslate]
  push_cast
  ring
theorem exists_latticeTranslate_map_eq (hS : S ∈ hyperoctahedralGroupEuclidean) (ℓ : ℝ)
    (k : Fin 4 → ℤ) : ∃ k', S (latticeTranslate ℓ k') = latticeTranslate ℓ k := by
  obtain ⟨k', hk'⟩ := exists_map_latticeTranslate (inv_mem hS) ℓ k
  refine ⟨k', ?_⟩
  rw [← hk', perm_apply_inv_apply]
theorem euclidNormVec_hyperoctahedral (hS : S ∈ hyperoctahedralGroupEuclidean) (x : AmbientSpace) :
    euclidNormVec (S x) = euclidNormVec x := by
  obtain ⟨π, s, rfl⟩ := hS
  unfold euclidNormVec
  congr 1
  rw [← Equiv.sum_comp π fun μ => x μ ^ 2]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [signedCoordinateEquiv_apply, mul_pow, sq (((s μ : ℤˣ) : ℤ) : ℝ), unit_cast_mul_self, one_mul]
theorem exists_isSignedPermOn (hS : S ∈ hyperoctahedralGroupEuclidean) :
    ∃ σ ε, IsSignedPermOn S σ ε := by
  obtain ⟨π, s, rfl⟩ := hS
  refine ⟨π⁻¹, fun μ => s (π⁻¹ μ), fun μ => ?_⟩
  funext ν
  by_cases h : π ν = μ
  · subst h
    simp [signedCoordinateEquiv_apply]
  · have h' : ν ≠ π.symm μ := fun e => h (by rw [e]; simp)
    simp [signedCoordinateEquiv_apply, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
theorem isSignedPermOn_axisPerm_axisSigns (hS : S ∈ hyperoctahedralGroupEuclidean) :
    IsSignedPermOn S (axisPerm S) (axisSigns S) := by
  have h : ∃ ε, IsSignedPermOn S (axisPerm S) ε :=
    Classical.epsilon_spec (exists_isSignedPermOn hS)
  exact Classical.epsilon_spec h
def signedPermMatrix (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun μ ν => if π μ = ν then (((s μ : ℤˣ) : ℤ) : ℝ) else 0
theorem signedPermMatrix_mem_orthogonalGroup (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) :
    signedPermMatrix π s ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext μ μ'
  rw [Matrix.mul_apply, Finset.sum_eq_single (π μ)]
  · by_cases h : μ = μ'
    · subst h
      simp [signedPermMatrix, unit_cast_mul_self]
    · have h' : π μ' ≠ π μ := fun e => h (π.injective e).symm
      simp [signedPermMatrix, h', Matrix.one_apply_ne h]
  · intro ν _ hν
    simp [signedPermMatrix, hν.symm]
  · simp
theorem signedCoordinateEquiv_eq_mulVec (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) (x : AmbientSpace) :
    signedCoordinateEquiv π s x = Matrix.mulVec (signedPermMatrix π s) x := by
  funext μ
  simp [signedCoordinateEquiv_apply, Matrix.mulVec, dotProduct, signedPermMatrix]
theorem image_integerLattice_subset (hS : S ∈ hyperoctahedralGroupEuclidean) :
    S '' integerLattice ⊆ integerLattice := by
  obtain ⟨π, s, rfl⟩ := hS
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  refine ⟨fun μ => (s μ : ℤ) * k (π μ), ?_⟩
  funext μ
  simp [signedCoordinateEquiv_apply]
theorem image_integerLattice (hS : S ∈ hyperoctahedralGroupEuclidean) :
    S '' integerLattice = integerLattice := by
  refine (image_integerLattice_subset hS).antisymm fun z hz => ?_
  exact ⟨S⁻¹ z, image_integerLattice_subset (inv_mem hS) ⟨z, hz, rfl⟩,
    perm_apply_inv_apply S z⟩
theorem hyperoctahedralEuclideanProperties_holds : HyperoctahedralEuclideanProperties := by
  intro S hS
  refine ⟨isSignedPermOn_axisPerm_axisSigns hS, ?_, image_integerLattice hS⟩
  obtain ⟨π, s, rfl⟩ := hS
  exact ⟨signedPermMatrix π s, signedPermMatrix_mem_orthogonalGroup π s,
    signedCoordinateEquiv_eq_mulVec π s⟩
variable {ℓ' : ℝ} {f : AmbientSpace → AmbientSpace}
theorem descends_descendedMap
    (h : ∀ z k, ∃ k', f (z + latticeTranslate ℓ k) = f z + latticeTranslate ℓ' k') :
    Descends ℓ ℓ' f (descendedMap ℓ ℓ' f) := by
  funext z
  obtain ⟨k, hk⟩ := exists_latticeTranslate_of_torusProj_eq (torusProj_liftPoint (torusProj ℓ z))
  obtain ⟨k', hk'⟩ := h z k
  simp only [comp_apply, descendedMap]
  rw [hk, hk', torusProj_add_latticeTranslate]
theorem descendedMap_torusProj
    (h : ∀ z k, ∃ k', f (z + latticeTranslate ℓ k) = f z + latticeTranslate ℓ' k') (x : AmbientSpace) :
    descendedMap ℓ ℓ' f (torusProj ℓ x) = torusProj ℓ' (f x) :=
  congrFun (descends_descendedMap h) x
theorem eq_of_descends {Φ Φ' : Torus4 ℓ → Torus4 ℓ'} (h : Descends ℓ ℓ' f Φ)
    (h' : Descends ℓ ℓ' f Φ') : Φ = Φ' := by
  funext u
  obtain ⟨x, rfl⟩ := torusProj_surjective ℓ u
  exact (congrFun h x).trans (congrFun h' x).symm
variable {L : ℕ} {b : ℤ} {w : AmbientSpace}
theorem scaledMotion_apply (z : AmbientSpace) :
    scaledMotion L b S w z = (L : ℝ) ^ b • S z + w := rfl
theorem scaledMotion_add (hS : S ∈ hyperoctahedralGroupEuclidean) (x z : AmbientSpace) :
    scaledMotion L b S w (x + z) = scaledMotion L b S w x + (L : ℝ) ^ b • S z := by
  rw [scaledMotion_apply, scaledMotion_apply, hyperoctahedral_map_add hS, smul_add]
  abel
theorem scaledMotion_sub_scaledMotion (hS : S ∈ hyperoctahedralGroupEuclidean) (x y : AmbientSpace) :
    scaledMotion L b S w x - scaledMotion L b S w y = (L : ℝ) ^ b • S (x - y) := by
  rw [scaledMotion_apply, scaledMotion_apply, hyperoctahedral_map_sub hS, smul_sub]
  abel
theorem scaledMotion_add_latticeTranslate (hS : S ∈ hyperoctahedralGroupEuclidean) (z : AmbientSpace)
    (k : Fin 4 → ℤ) :
    ∃ k', scaledMotion L b S w (z + latticeTranslate ℓ k) =
      scaledMotion L b S w z + latticeTranslate ((L : ℝ) ^ b * ℓ) k' := by
  obtain ⟨k', hk'⟩ := exists_map_latticeTranslate hS ℓ k
  exact ⟨k', by rw [scaledMotion_add hS, hk', latticeTranslate_mul_side]⟩
theorem inverse_add_latticeTranslate (hS : S ∈ hyperoctahedralGroupEuclidean)
    {Ψ : AmbientSpace → AmbientSpace}
    (hl : LeftInverse Ψ (scaledMotion L b S w)) (hr : RightInverse Ψ (scaledMotion L b S w))
    (z : AmbientSpace) (k : Fin 4 → ℤ) :
    ∃ k', Ψ (z + latticeTranslate ((L : ℝ) ^ b * ℓ) k) = Ψ z + latticeTranslate ℓ k' := by
  obtain ⟨k', hk'⟩ := exists_latticeTranslate_map_eq hS ℓ k
  refine ⟨k', ?_⟩
  have h : scaledMotion L b S w (Ψ z + latticeTranslate ℓ k') =
      z + latticeTranslate ((L : ℝ) ^ b * ℓ) k := by
    rw [scaledMotion_add hS, hk', hr z, latticeTranslate_mul_side]
  rw [← h, hl]
theorem torusEuclidNorm_torusProj_scaled (hc : 0 < (L : ℝ) ^ b)
    (hS : S ∈ hyperoctahedralGroupEuclidean) (d : AmbientSpace) :
    torusEuclidNorm (torusProj ((L : ℝ) ^ b * ℓ) ((L : ℝ) ^ b • S d)) =
      (L : ℝ) ^ b * torusEuclidNorm (torusProj ℓ d) := by
  have key : ∀ k k' : Fin 4 → ℤ, S (latticeTranslate ℓ k') = latticeTranslate ℓ k →
      euclidNormVec ((L : ℝ) ^ b • S d - latticeTranslate ((L : ℝ) ^ b * ℓ) k) =
        (L : ℝ) ^ b * euclidNormVec (d - latticeTranslate ℓ k') := by
    intro k k' h
    rw [latticeTranslate_mul_side, ← h, ← smul_sub, ← hyperoctahedral_map_sub hS,
      euclidNormVec_smul, abs_of_pos hc, euclidNormVec_hyperoctahedral hS]
  apply le_antisymm
  · obtain ⟨k', hk'⟩ := (isLeast_norm_lifts_vec (ℓ := ℓ) d).1
    obtain ⟨k, hk⟩ := exists_map_latticeTranslate hS ℓ k'
    have h1 := (isLeast_norm_lifts_vec (ℓ := (L : ℝ) ^ b * ℓ) ((L : ℝ) ^ b • S d)).2 ⟨k, rfl⟩
    refine h1.trans_eq ?_
    show euclidNormVec _ = _
    rw [key k k' hk]
    congr 1
  · obtain ⟨k, hk⟩ := (isLeast_norm_lifts_vec (ℓ := (L : ℝ) ^ b * ℓ) ((L : ℝ) ^ b • S d)).1
    obtain ⟨k', hk'⟩ := exists_latticeTranslate_map_eq hS ℓ k
    have h1 := (isLeast_norm_lifts_vec (ℓ := ℓ) d).2 ⟨k', rfl⟩
    have hk2 : euclidNormVec ((L : ℝ) ^ b • S d - latticeTranslate ((L : ℝ) ^ b * ℓ) k) =
        torusEuclidNorm (torusProj ((L : ℝ) ^ b * ℓ) ((L : ℝ) ^ b • S d)) := hk
    rw [← hk2, key k k' hk']
    exact mul_le_mul_of_nonneg_left h1 hc.le
theorem zpow_mul_torusSide_mem {m : ℕ} (hL : 0 < L) (hb : 1 ≤ (m : ℤ) + b) :
    (L : ℝ) ^ b * torusSide L m ∈ torusSides L := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hn : (((m : ℤ) + b).toNat : ℤ) = (m : ℤ) + b := Int.toNat_of_nonneg (by omega)
  refine ⟨((m : ℤ) + b).toNat, by omega, ?_⟩
  simp only [torusSide]
  rw [← zpow_natCast (L : ℝ) ((m : ℤ) + b).toNat, hn, zpow_add₀ hL', zpow_natCast]
  ring
theorem descends_inverse {m : ℕ} (hS : S ∈ hyperoctahedralGroupEuclidean)
    {Ψ : AmbientSpace → AmbientSpace}
    (hl : LeftInverse Ψ (scaledMotion L b S w)) (hr : RightInverse Ψ (scaledMotion L b S w)) :
    Descends ((L : ℝ) ^ b * torusSide L m) (torusSide L m) Ψ
        (descendedMap ((L : ℝ) ^ b * torusSide L m) (torusSide L m) Ψ) ∧
      LeftInverse (descendedMap ((L : ℝ) ^ b * torusSide L m) (torusSide L m) Ψ)
        (descendedMap (torusSide L m) ((L : ℝ) ^ b * torusSide L m) (scaledMotion L b S w)) ∧
      RightInverse (descendedMap ((L : ℝ) ^ b * torusSide L m) (torusSide L m) Ψ)
        (descendedMap (torusSide L m) ((L : ℝ) ^ b * torusSide L m) (scaledMotion L b S w)) := by
  have hf := scaledMotion_add_latticeTranslate (ℓ := torusSide L m) (L := L) (b := b) (w := w) hS
  have hΨ := inverse_add_latticeTranslate (ℓ := torusSide L m) hS hl hr
  refine ⟨descends_descendedMap hΨ, fun u => ?_, fun u => ?_⟩
  · obtain ⟨x, rfl⟩ := torusProj_surjective (torusSide L m) u
    rw [descendedMap_torusProj hf, descendedMap_torusProj hΨ, hl x]
  · obtain ⟨x, rfl⟩ := torusProj_surjective ((L : ℝ) ^ b * torusSide L m) u
    rw [descendedMap_torusProj hΨ, descendedMap_torusProj hf, hr x]
theorem scaledMotionDescends_holds {m : ℕ} (hL : 0 < L) (hb : 1 ≤ (m : ℤ) + b)
    (hS : S ∈ hyperoctahedralGroupEuclidean) : ScaledMotionDescends L m b S w := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hc : 0 < (L : ℝ) ^ b := zpow_pos hL' b
  have hf := scaledMotion_add_latticeTranslate (ℓ := torusSide L m) (L := L) (b := b) (w := w) hS
  let g : AmbientSpace → AmbientSpace := fun z => S⁻¹ (((L : ℝ) ^ b)⁻¹ • (z - w))
  have hgl : LeftInverse g (scaledMotion L b S w) := by
    intro z
    simp only [g, scaledMotion_apply, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hc.ne',
      one_smul, perm_inv_apply_apply]
  have hgr : RightInverse g (scaledMotion L b S w) := by
    intro z
    simp only [g, scaledMotion_apply, perm_apply_inv_apply, smul_smul,
      mul_inv_cancel₀ hc.ne', one_smul, sub_add_cancel]
  obtain ⟨-, hl, hr⟩ := descends_inverse (m := m) hS hgl hgr
  refine ⟨zpow_mul_torusSide_mem hL hb, descends_descendedMap hf, fun Φ hΦ => eq_of_descends hΦ
    (descends_descendedMap hf), bijective_iff_has_inverse.mpr ⟨_, hl, hr⟩,
    bijective_iff_has_inverse.mpr ⟨g, hgl, hgr⟩, fun Ψ h1 h2 => descends_inverse hS h1 h2,
    fun u v => ?_, fun u z => ?_⟩
  · obtain ⟨x, rfl⟩ := torusProj_surjective (torusSide L m) u
    obtain ⟨y, rfl⟩ := torusProj_surjective (torusSide L m) v
    rw [descendedMap_torusProj hf, descendedMap_torusProj hf, ← torusProj_sub, ← torusProj_sub,
      scaledMotion_sub_scaledMotion hS, torusEuclidNorm_torusProj_scaled hc hS]
  · obtain ⟨x, rfl⟩ := torusProj_surjective (torusSide L m) u
    rw [← torusProj_add, descendedMap_torusProj hf, descendedMap_torusProj hf, ← torusProj_add,
      scaledMotion_add hS]
variable {m : ℕ} {j : ℤ}
theorem projectPoint_add (x y : InfiniteLattice.LatticePoint (meshSize L j)) :
    InfiniteLattice.projectPoint L m j (x + y) =
      InfiniteLattice.projectPoint L m j x + InfiniteLattice.projectPoint L m j y := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.projectPoint_add <;> assumption
theorem projectPoint_surjective (L m : ℕ) (j : ℤ) :
    Surjective (InfiniteLattice.projectPoint L m j) := by apply _root_.YangMills.Construction.LatticeCovering.projectPoint_surjective <;> assumption
theorem projectLink_surjective (L m : ℕ) (j : ℤ) :
    Surjective (InfiniteLattice.projectLink L m j) := by
  intro q
  obtain ⟨z, hz⟩ := projectPoint_surjective L m j q.source
  obtain ⟨μ, h | h⟩ := q.isNeighbour
  · refine ⟨⟨z, z + InfiniteLattice.axisStep _ μ, μ, Or.inl (by abel)⟩,
      PeriodicLattice.Bond.ext hz ?_⟩
    show InfiniteLattice.projectPoint L m j (z + InfiniteLattice.axisStep _ μ) = q.target
    rw [projectPoint_add, hz, InfiniteLattice.projectPoint_axisStep, ← h]
    abel
  · refine ⟨⟨z, z + -InfiniteLattice.axisStep _ μ, μ, Or.inr (by abel)⟩,
      PeriodicLattice.Bond.ext hz ?_⟩
    show InfiniteLattice.projectPoint L m j (z + -InfiniteLattice.axisStep _ μ) = q.target
    rw [projectPoint_add, hz, InfiniteLattice.projectPoint_neg, InfiniteLattice.projectPoint_axisStep,
      ← neg_inj, ← h]
    abel
theorem torusProj_single (μ : Fin 4) (t : ℝ) :
    torusProj (torusSide L m) (Pi.single μ t) = pointOnAxis L m μ t := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.torusProj_single <;> assumption
theorem projectionOfLattice_holds (L m K : ℕ) : ProjectionOfLattice L m K := by
  refine ⟨?_, fun q => ⟨rfl, rfl, ?_, PeriodicLattice.Bond.ext rfl rfl⟩,
    projectLink_surjective L m _, fun p => ?_, fun q => ?_, fun p => ?_⟩
  · ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (InfiniteLattice.projectPoint L m (K : ℤ) ⟨x, hx⟩).2
    · intro ht
      obtain ⟨z, hz⟩ := projectPoint_surjective L m (K : ℤ) ⟨t, ht⟩
      exact ⟨z, z.2, congrArg Subtype.val hz⟩
  · rintro ⟨μ, h⟩
    refine ⟨μ, ?_⟩
    show InfiniteLattice.projectPoint L m (K : ℤ) q.terminal -
      InfiniteLattice.projectPoint L m (K : ℤ) q.initial = _
    rw [← InfiniteLattice.projectPoint_sub, h, InfiniteLattice.projectPoint_axisStep]
  · simp only [plaquetteVertexSet, PeriodicLattice.Plaquette.vertices, Set.image_insert_eq,
      Set.image_singleton, projectPlaquette, projectPoint_add, InfiniteLattice.projectPoint_axisStep]
  · obtain ⟨z, hz⟩ := projectPoint_surjective L m (K : ℤ) q.origin
    exact ⟨⟨z, q.firstAxis, q.secondAxis, q.firstAxis_lt_secondAxis⟩,
      PeriodicLattice.Plaquette.ext hz rfl rfl⟩
  · simp only [InfiniteLattice.ElementaryPlaquette.center, torusProj_add, torusProj_single]
    rfl
end LiftsAndDescendedMaps
open LiftsAndDescendedMaps in
theorem LiftsAndDescendedMaps.statement_holds : LiftsAndDescendedMaps.Statement := by
  intro s
  have hL : 0 < s.L := by
    have := s.isAdmissible.2
    omega
  have hℓ : 0 < torusSide s.L s.m := by
    unfold torusSide
    positivity
  exact ⟨torusDistEqMinOverLifts_of_pos hℓ, torusDistIsMetric_of_pos hℓ, straightPathsLipschitz_holds,
    hyperoctahedralEuclideanProperties_holds, fun b S w hb hS => scaledMotionDescends_holds hL hb hS,
    projectionOfLattice_holds s.L s.m s.K⟩
end TorusLifts
end YangMills.Construction
end
