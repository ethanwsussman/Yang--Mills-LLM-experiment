import YangMills.Construction.RunningCouplingSlope.KernelsNearTheCellsAreBoundedProof
import YangMills.Construction.Continuum.IsometriesAndModuliOnFourSpaceProof
import YangMills.Construction.Continuum.TuplesInTheTwoScalesOfClasses
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TorusTransport.TupleVectors.TwoScaleMembership
open YangMills.Construction.TorusMetric Matrix
theorem continuous_of_motion {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s) :
    Continuous s := by apply _root_.YangMills.Construction.ToriLimits.EuclideanSymmetryFacts.continuous_of_isEuclideanMotion <;> assumption
def motionHomeomorph {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s) :
    (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) where
  toEquiv := hs.toPerm
  continuous_toFun := continuous_of_motion hs
  continuous_invFun := continuous_of_motion hs.symm
theorem tsupport_comp_motion_symm {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s)
    (g : (Fin 4 → ℝ) → ℝ) : tsupport (g ∘ hs.toPerm.symm) = s '' tsupport g := by
  have e : tsupport (g ∘ hs.toPerm.symm) = hs.toPerm.symm ⁻¹' tsupport g :=
    tsupport_comp_eq_preimage g (motionHomeomorph hs).symm
  rw [e]
  ext x
  constructor
  · intro h
    exact ⟨_, h, hs.toPerm.apply_symm_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    have : hs.toPerm.symm (s y) = y := hs.toPerm.symm_apply_apply y
    simpa [Set.mem_preimage, this] using hy
theorem motionsPreserveTuples_holds (D : TransportData) (h : MotionFacts.MotionInvariance D) :
    MotionsPreserveTuples D := by
  intro s hs t ht
  obtain ⟨-, hk, hd, -, -⟩ := (mem_sepTuples_iff D _ t).mp ht
  refine ⟨fun _ => rfl, ?_, fun i => tsupport_comp_motion_symm hs (t.2 i),
    fun i => IsCompact.image (hk i) (continuous_of_motion hs), fun i k hik =>
      (Set.disjoint_image_iff hs.bijective.injective).mpr (hd hik)⟩
  rcases ht with rfl | ht
  · rw [actAny_nilTuple]
    exact nilTuple_mem_sepTuples D _
  · obtain ⟨n, f, hf, rfl⟩ := Set.mem_iUnion.mp ht
    have hm : (familyComp f hs.toPerm.symm : Domain.euclidean.FnFamily D n ℝ) ∈
        Domain.euclidean.sepC1Families D n :=
      ((h _ hs.symm).2.2 n).1.subset ⟨f, hf.1, rfl⟩
    exact Or.inr (Set.mem_iUnion.mpr
      ⟨n, familyComp f hs.toPerm.symm, ⟨hm, fun _ => Set.subset_univ _⟩, rfl⟩)
theorem dotProduct_self_eq_one_of_unit {n : Fin 4 → ℝ} (hn : euclidNorm n = 1) :
    n ⬝ᵥ n = 1 := by apply _root_.YangMills.Construction.TorusTransport.MotionFacts.dotProduct_self_eq_one <;> assumption
theorem reflector_mem_orthogonalGroup {n : Fin 4 → ℝ} (hn : euclidNorm n = 1) :
    (1 - (2 : ℝ) • vecMulVec n n) ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  have hT : (1 - (2 : ℝ) • vecMulVec n n)ᵀ = 1 - (2 : ℝ) • vecMulVec n n := by
    simp [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_vecMulVec]
  have hM : vecMulVec n n * vecMulVec n n = vecMulVec n n := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply]
    have e : ∑ k, n i * n k * (n k * n j) = n i * n j * (n ⬝ᵥ n) := by
      simp only [dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, dotProduct_self_eq_one_of_unit hn, mul_one]
  rw [Matrix.mem_orthogonalGroup_iff]
  rw [hT]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, hM]
  module
theorem reflectionsAreInvolutive_holds (D : TransportData) : ReflectionsAreInvolutive D := by
  intro n c hn θ hθ
  have hnn := dotProduct_self_eq_one_of_unit hn
  have hmot : IsEuclideanMotion θ := by
    refine ⟨_, reflector_mem_orthogonalGroup hn, (2 * c) • n, funext fun x => ?_⟩
    rw [hθ, orthoAffine, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Matrix.vecMulVec_mulVec]
    ext μ
    simp [scalarProd, dotProduct, Pi.smul_apply, MulOpposite.smul_eq_mul_unop]
    ring
  have hinv : ∀ x, θ (θ x) = x := by
    intro x
    have e : scalarProd n (θ x) = 2 * c - scalarProd n x := by
      rw [hθ, scalarProd, dotProduct_sub, dotProduct_smul, hnn]
      simp only [smul_eq_mul]
      ring
    rw [hθ (θ x), e, hθ x]
    ext μ
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsymm : hmot.toPerm.symm = hmot.toPerm := by
    ext1 y
    rw [Equiv.symm_apply_eq]
    exact (hinv y).symm
  refine ⟨hmot, hsymm, fun t _ => ?_⟩
  have e : familyAct hmot t.2 = familyComp t.2 θ := by
    funext i
    change t.2 i ∘ hmot.toPerm.symm = t.2 i ∘ θ
    rw [hsymm]
    rfl
  simp only [actAny, compAny, e]
theorem cubeClassSubsetAdmissible_holds (D : TransportData) : CubeClassSubsetAdmissible D := by
  intro w d R hw hd hR
  refine ⟨?_, ?_⟩
  · rintro t (rfl | ⟨ht, hb, hs⟩)
    · exact nilTuple_mem_admissibleSepTuples D hd hR
    · rcases id ht with rfl | h
      · exact nilTuple_mem_admissibleSepTuples D hd hR
      · obtain ⟨n, f, -, rfl⟩ := Set.mem_iUnion.mp h
        refine Or.inr (Set.mem_iUnion.mpr ⟨n, f, ⟨ht, fun i => ?_, hs⟩, rfl⟩)
        obtain ⟨x, hx, -⟩ := hb i
        exact ⟨x, hx.2⟩
  · rintro t (rfl | ⟨-, hb, -⟩) i
    · exact i.elim0
    · obtain ⟨x, hx, hc⟩ := hb i
      exact hx.2.trans hc
theorem exists_uniform_lower_bound_of_finite {P : Type*} [Finite P] (δ : P → ℝ≥0∞)
    (h : ∀ p, 0 < δ p) : ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ p, ENNReal.ofReal d ≤ δ p := by
  have h1 : ∀ p, ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ ENNReal.ofReal e ≤ δ p := by
    intro p
    by_cases hp : δ p = ∞
    · exact ⟨1, one_pos, le_rfl, hp ▸ le_top⟩
    · refine ⟨min 1 (δ p).toReal, lt_min one_pos (ENNReal.toReal_pos (h p).ne' hp),
        min_le_left _ _, ?_⟩
      calc ENNReal.ofReal (min 1 (δ p).toReal) ≤ ENNReal.ofReal (δ p).toReal :=
            ENNReal.ofReal_le_ofReal (min_le_right _ _)
        _ = δ p := ENNReal.ofReal_toReal hp
  choose e he0 he1 he using h1
  rcases isEmpty_or_nonempty P with hP | hP
  · exact ⟨1, one_pos, le_rfl, fun p => hP.elim p⟩
  · obtain ⟨p₀, hp₀⟩ := Finite.exists_min e
    exact ⟨e p₀, he0 p₀, he1 p₀, fun p => (ENNReal.ofReal_le_ofReal (hp₀ p)).trans (he p)⟩
theorem exists_common_ball_of_finite {P : Type*} [Finite P] (A : P → Set (Fin 4 → ℝ))
    (h : ∀ p, IsCompact (A p)) : ∃ R : ℝ, 0 < R ∧ ∀ p, A p ⊆ ballR4 0 R := by
  have hc : Continuous euclidNormVec := by
    unfold euclidNormVec
    fun_prop
  have h1 : ∀ p, ∃ b, ∀ x ∈ A p, euclidNormVec x ≤ b := fun p => by
    obtain ⟨b, hb⟩ := (h p).bddAbove_image hc.continuousOn
    exact ⟨b, fun x hx => hb ⟨x, hx, rfl⟩⟩
  choose b hb using h1
  obtain ⟨M, hM⟩ := (Set.finite_range b).bddAbove
  refine ⟨max M 1, lt_max_of_lt_right one_pos, fun p x hx => ?_⟩
  change euclidNormVec (x - 0) ≤ _
  rw [sub_zero]
  exact ((hb p x hx).trans (hM ⟨p, rfl⟩)).trans (le_max_left _ _)
theorem maxNorm_le_euclidNorm (y : Fin 4 → ℝ) : maxNorm y ≤ euclidNorm y := by apply _root_.YangMills.DeltaSharedProofs.p501598 <;> assumption
theorem finiteSetsInCommonCubeClass_holds (D : TransportData)
    (hf : ∀ S S' : Set (Fin 4 → ℝ), IsCompact S → IsCompact S' → Disjoint S S' →
      0 < Domain.euclidean.setDist D S S') : FiniteSetsInCommonCubeClass D := by
  intro T hT hsub
  have : Finite T := hT.to_subtype
  have hmem := fun t : T => (mem_sepTuples_iff D _ t.1).mp (hsub t.2)
  obtain ⟨R, hR, hball⟩ := exists_common_ball_of_finite (P := Σ t : T, Fin t.1.1)
    (fun p => entrySupp D (p.1.1.2 p.2)) (fun p => (hmem p.1).2.1 p.2)
  obtain ⟨d, hd, hd1, hdist⟩ := exists_uniform_lower_bound_of_finite
    (P := Σ t : T, {ik : Fin t.1.1 × Fin t.1.1 // ik.1 ≠ ik.2})
    (fun p => Domain.euclidean.setDist D (entrySupp D (p.1.1.2 p.2.1.1))
      (entrySupp D (p.1.1.2 p.2.1.2)))
    (fun p => hf _ _ ((hmem p.1).2.1 _) ((hmem p.1).2.1 _) ((hmem p.1).2.2.1 p.2.2))
  obtain ⟨N, hN⟩ := exists_nat_gt (R + 1 / 2)
  have hw : R + 1 / 2 < (((N.succPNat : ℕ+) : ℕ) : ℝ) := by
    simp only [Nat.succPNat_coe, Nat.cast_succ]
    linarith
  have hw0 : 0 < (((N.succPNat : ℕ+) : ℕ) : ℝ) := by linarith
  have hL : (D.L : ℝ) ≠ 0 := by
    have : 13 ≤ D.L := D.isAdmissible.2
    exact Nat.cast_ne_zero.mpr (by omega)
  have hk : ∀ k : ℕ+, ∃ z : ℤ, (((N.succPNat : ℕ+) : ℕ) : ℝ) =
      (D.L : ℝ) ^ (-((k : ℕ) : ℤ)) * (z : ℝ) := by
    intro k
    refine ⟨((N.succPNat : ℕ) : ℤ) * (D.L : ℤ) ^ (k : ℕ), ?_⟩
    rw [_root_.zpow_neg, zpow_natCast]
    push_cast
    field_simp
  refine ⟨N.succPNat, d, R, hw0, hd, hR, ?_, hk, ?_, hd1⟩
  · intro t ht
    refine Or.inr ⟨hsub ht, fun i => ⟨0, ⟨(hmem ⟨t, ht⟩).2.1 i, hball ⟨⟨t, ht⟩, i⟩⟩, ?_⟩,
      fun i k hik => hdist ⟨⟨t, ht⟩, ⟨(i, k), hik⟩⟩⟩
    intro y hy
    have h₁ : euclidNormVec (y - 0) ≤ R := hy
    rw [sub_zero] at h₁
    have h₂ := maxNorm_le_euclidNorm y
    change maxNorm y < _
    have h₃ : euclidNormVec y = euclidNorm y := rfl
    linarith
  · exact hk D.K
theorem statement_holds (h₁ : MotionFacts.Statement)
    (h₂ : SupportFacts.AllSupportFacts) : Statement := by
  intro D
  have hd := finiteSetsInCommonCubeClass_holds D (h₂ D).2.2.2.2.2.2.2.1
  refine ⟨motionsPreserveTuples_holds D (h₁ D).1, reflectionsAreInvolutive_holds D, ?_,
    cubeClassSubsetAdmissible_holds D, hd⟩
  intro t ht
  obtain ⟨w, d, R, hw, hd', hR, hT, -⟩ :=
    hd {t} (Set.finite_singleton t) (Set.singleton_subset_iff.mpr ht)
  exact ⟨d, R, hd', hR, (cubeClassSubsetAdmissible_holds D _ d R hw hd' hR).1 (hT rfl)⟩
end YangMills.Construction.TorusTransport.TupleVectors.TwoScaleMembership
end
