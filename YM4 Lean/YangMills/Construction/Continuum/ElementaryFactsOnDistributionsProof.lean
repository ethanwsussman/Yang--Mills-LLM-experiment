import YangMills.Construction.Continuum.ElementaryFactsOnDistributions
import Mathlib
set_option autoImplicit false
open Filter Topology TopologicalSpace
open scoped ComplexConjugate ContDiff
noncomputable section
namespace YangMills.Construction.DistributionBasics
open ReflectionSpaces.Euclidean
variable {n : ℕ}
theorem mem_testFunctionSpace_iff {U : Opens (Coord n)} {φ : Coord n → ℂ} :
    φ ∈ testFunctionSpace U ↔ ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U :=
  Iff.rfl
theorem nonempty_derivIndex (n ν : ℕ) : Nonempty (DerivIndex n ν) :=
  ⟨⟨0, fun i => absurd i.2 (by simp)⟩⟩
theorem cNorm_mono {ν μ : ℕ} (hνμ : ν ≤ μ) (φ : Coord n → ℂ) :
    cNorm ν φ ≤ cNorm μ φ := by
  have := nonempty_derivIndex n ν
  refine ciSup_le fun p => ?_
  have hlt : (p.1 : ℕ) < μ + 1 := by have := p.1.2; omega
  exact le_ciSup (f := fun q : DerivIndex n μ => TestFunctions.uniformNorm (partialDeriv q.2 φ))
    (Set.finite_range _).bddAbove ⟨⟨p.1, hlt⟩, p.2⟩
theorem tsupport_sub_subset_of_isClosed {f g : Coord n → ℂ} {S : Set (Coord n)} (hS : IsClosed S)
    (hf : tsupport f ⊆ S) (hg : tsupport g ⊆ S) : tsupport (f - g) ⊆ S := by
  refine closure_minimal (fun x hx => ?_) hS
  by_contra hxS
  have hf0 : f x = 0 := by
    by_contra h
    exact hxS (hf (subset_tsupport _ (Function.mem_support.2 h)))
  have hg0 : g x = 0 := by
    by_contra h
    exact hxS (hg (subset_tsupport _ (Function.mem_support.2 h)))
  exact (Function.mem_support.1 hx) (by simp [hf0, hg0])
theorem finiteCombinationsClosed_holds (U : Opens (Coord n)) : FiniteCombinationsClosed U := by
  intro ι s c T
  refine ⟨⟨∑ i ∈ s, c i • (T i).form, ?_⟩, rfl⟩
  intro S hS hSU
  have h : ∀ i, ∃ (ν : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ φ : testFunctionSpace U,
      tsupport (φ : Coord n → ℂ) ⊆ S → ‖(T i).form φ‖ ≤ C * cNorm ν (φ : Coord n → ℂ) :=
    fun i => (T i).bound S hS hSU
  choose ν C hC hb using h
  refine ⟨s.sup ν, ∑ i ∈ s, ‖c i‖ * C i,
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (hC i), fun φ hφ => ?_⟩
  rw [LinearMap.sum_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [LinearMap.smul_apply, norm_smul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact (hb i φ hφ).trans
    (mul_le_mul_of_nonneg_left (cNorm_mono (Finset.le_sup hi) _) (hC i))
theorem isSeqContinuous_of_distribution {U : Opens (Coord n)} (T : Distribution U) :
    IsSeqContinuous T := by
  intro G φ h
  obtain ⟨⟨S, hS, hSU, hφS, hGS⟩, hlim⟩ := h
  obtain ⟨ν, C, hC, hb⟩ := T.bound S hS hSU
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ t, ‖T.form (G t) - T.form φ‖ ≤
      C * cNorm ν ((G t : Coord n → ℂ) - (φ : Coord n → ℂ)) := by
    intro t
    rw [← map_sub]
    exact hb (G t - φ) (tsupport_sub_subset_of_isClosed hS.isClosed (hGS t) hφS)
  have hC0 := (hlim ν).const_mul C
  rw [mul_zero] at hC0
  exact squeeze_zero (fun _ => norm_nonneg _) hbound hC0
theorem restrictPreservesOrder_of_distribution {U : Opens (Coord n)} (T : Distribution U) :
    RestrictPreservesOrder T := by
  intro U' h ν₀ hT S hS hSU'
  obtain ⟨C, hC, hb⟩ := hT S hS (hSU'.trans h)
  exact ⟨C, hC, fun φ hφ => hb (inclusionMap h φ) hφ⟩
theorem sign_mul_self {ε : Fin n → ℝ} (hε : ∀ j, ε j = 1 ∨ ε j = -1) (j : Fin n) :
    ε j * ε j = 1 := by
  rcases hε j with h | h <;> rw [h] <;> norm_num
def signedPermEquiv (σ : Equiv.Perm (Fin n)) (ε : Fin n → ℝ) (hε : ∀ j, ε j = 1 ∨ ε j = -1) :
    Coord n ≃L[ℝ] Coord n :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x i => ε (σ.symm i) * x (σ.symm i)
      map_add' := fun x y => by
        funext i
        simp [mul_add]
      map_smul' := fun a x => by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring
      invFun := fun y j => ε j * y (σ j)
      left_inv := fun x => by
        funext j
        show ε j * (ε (σ.symm (σ j)) * x (σ.symm (σ j))) = x j
        rw [Equiv.symm_apply_apply, ← mul_assoc, sign_mul_self hε, one_mul]
      right_inv := fun y => by
        funext i
        show ε (σ.symm i) * (ε (σ.symm i) * y (σ (σ.symm i))) = y i
        rw [Equiv.apply_symm_apply, ← mul_assoc, sign_mul_self hε, one_mul] }
theorem signedPermEquiv_apply (σ : Equiv.Perm (Fin n)) (ε : Fin n → ℝ)
    (hε : ∀ j, ε j = 1 ∨ ε j = -1) (x : Coord n) (i : Fin n) :
    signedPermEquiv σ ε hε x i = ε (σ.symm i) * x (σ.symm i) :=
  rfl
theorem mulVec_eq_signedPermEquiv {P : Matrix (Fin n) (Fin n) ℝ} (σ : Equiv.Perm (Fin n))
    (ε : Fin n → ℝ) (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (hP : ∀ i j, P i j = if i = σ j then ε j else 0) (x : Coord n) :
    P.mulVec x = signedPermEquiv σ ε hε x := by
  funext i
  rw [signedPermEquiv_apply]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (σ.symm i)]
  · rw [hP]
    simp
  · intro j _ hj
    rw [hP, if_neg, zero_mul]
    intro h
    exact hj (by rw [h]; simp)
  · simp
theorem signedPermEquiv_single (σ : Equiv.Perm (Fin n)) (ε : Fin n → ℝ)
    (hε : ∀ j, ε j = 1 ∨ ε j = -1) (j : Fin n) :
    signedPermEquiv σ ε hε (Pi.single j 1) = ε j • (Pi.single (σ j) 1 : Coord n) := by
  funext i
  rw [signedPermEquiv_apply]
  show ε (σ.symm i) * (Pi.single j (1 : ℝ) : Coord n) (σ.symm i) =
    ε j * (Pi.single (σ j) (1 : ℝ) : Coord n) i
  by_cases h : i = σ j
  · subst h
    simp
  · have h' : σ.symm i ≠ j := fun e => h (by rw [← e]; simp)
    simp [h, h']
def affineHomeomorph (A : Coord n ≃L[ℝ] Coord n) (b : Coord n) : Coord n ≃ₜ Coord n :=
  A.toHomeomorph.trans (Homeomorph.addRight b)
theorem affineHomeomorph_apply (A : Coord n ≃L[ℝ] Coord n) (b x : Coord n) :
    affineHomeomorph A b x = A x + b :=
  rfl
theorem contDiff_affineHomeomorph (A : Coord n ≃L[ℝ] Coord n) (b : Coord n) :
    ContDiff ℝ ∞ (affineHomeomorph A b) :=
  A.contDiff.add contDiff_const
theorem contDiff_affineHomeomorph_symm (A : Coord n ≃L[ℝ] Coord n) (b : Coord n) :
    ContDiff ℝ ∞ (affineHomeomorph A b).symm := by
  have h : ((affineHomeomorph A b).symm : Coord n → Coord n) = fun y => A.symm (y - b) := by
    funext y
    rw [Homeomorph.symm_apply_eq, affineHomeomorph_apply]
    simp
  rw [h]
  exact A.symm.contDiff.comp (contDiff_id.sub contDiff_const)
theorem tsupport_comp_homeomorph (κ : ℂ ≃L[ℝ] ℂ) (ψ : Coord n ≃ₜ Coord n) (φ : Coord n → ℂ) :
    tsupport (fun x => κ (φ (ψ x))) = ψ ⁻¹' tsupport φ := by
  have h1 : (fun x => κ (φ (ψ x))) = (κ ∘ φ) ∘ ψ := rfl
  have h2 : Function.support (κ ∘ φ) = Function.support φ := by
    ext x
    simp [Function.mem_support]
  rw [h1, tsupport_comp_eq_preimage, tsupport, h2, tsupport]
theorem comp_mem_testFunctionSpace (κ : ℂ ≃L[ℝ] ℂ) (ψ : Coord n ≃ₜ Coord n)
    (hψ : ContDiff ℝ ∞ ψ) {V U : Opens (Coord n)} (hVU : ∀ x, ψ x ∈ V ↔ x ∈ U)
    {φ : Coord n → ℂ} (hφ : φ ∈ testFunctionSpace V) :
    (fun x => κ (φ (ψ x))) ∈ testFunctionSpace U := by
  obtain ⟨h1, h2, h3⟩ := mem_testFunctionSpace_iff.1 hφ
  refine mem_testFunctionSpace_iff.2 ⟨κ.contDiff.comp (h1.comp hψ), ?_, ?_⟩
  · show IsCompact _
    rw [tsupport_comp_homeomorph]
    exact ψ.isCompact_preimage.2 h2
  · rw [tsupport_comp_homeomorph]
    exact fun x hx => (hVU x).1 (h3 hx)
def compTest (κ : ℂ ≃L[ℝ] ℂ) (ψ : Coord n ≃ₜ Coord n) (hψ : ContDiff ℝ ∞ ψ)
    {V U : Opens (Coord n)} (hVU : ∀ x, ψ x ∈ V ↔ x ∈ U) (φ : testFunctionSpace V) :
    testFunctionSpace U :=
  ⟨fun x => κ ((φ : Coord n → ℂ) (ψ x)), comp_mem_testFunctionSpace κ ψ hψ hVU φ.2⟩
theorem partialDeriv_compTest (σ : Equiv.Perm (Fin n)) (ε : Fin n → ℝ)
    (hε : ∀ j, ε j = 1 ∨ ε j = -1) (b : Coord n) (κ : ℂ ≃L[ℝ] ℂ) {k : ℕ} (c : Fin k → Fin n)
    {f : Coord n → ℂ} (hf : ContDiff ℝ ∞ f) (x : Coord n) :
    partialDeriv c (fun y => κ (f (affineHomeomorph (signedPermEquiv σ ε hε) b y))) x =
      (∏ j, ε (c j)) • κ (partialDeriv (σ ∘ c) f (affineHomeomorph (signedPermEquiv σ ε hε) b x)) := by
  set A := signedPermEquiv σ ε hε with hA
  have hg : ContDiff ℝ ∞ (fun z => f (z + b)) := hf.comp (contDiff_id.add contDiff_const)
  have hk : ((k : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have key : iteratedFDeriv ℝ k (fun y => f (A y + b)) x =
      (iteratedFDeriv ℝ k f (A x + b)).compContinuousLinearMap
        fun _ => (A : Coord n →L[ℝ] Coord n) := by
    have h := ContinuousLinearMap.iteratedFDeriv_comp_right (A : Coord n →L[ℝ] Coord n) hg x hk
    rw [iteratedFDeriv_comp_add_right] at h
    exact h
  have e2 := ContinuousLinearEquiv.iteratedFDeriv_comp_left (𝕜 := ℝ)
    (f := fun y => f (A y + b)) (x := x) κ (i := k)
  have hv : (fun j => A (Pi.single (c j) 1)) =
      fun j => ε (c j) • (Pi.single (σ (c j)) 1 : Coord n) :=
    funext fun j => signedPermEquiv_single σ ε hε (c j)
  show iteratedFDeriv ℝ k (κ ∘ fun y => f (A y + b)) x (fun j => Pi.single (c j) 1) =
    (∏ j, ε (c j)) • κ (iteratedFDeriv ℝ k f (A x + b) fun j => Pi.single (σ (c j)) 1)
  rw [e2, key]
  show κ (iteratedFDeriv ℝ k f (A x + b) fun j => A (Pi.single (c j) 1)) = _
  rw [hv, ContinuousMultilinearMap.map_smul_univ, map_smul]
theorem cNorm_compTest (σ : Equiv.Perm (Fin n)) (ε : Fin n → ℝ)
    (hε : ∀ j, ε j = 1 ∨ ε j = -1) (b : Coord n) (κ : ℂ ≃L[ℝ] ℂ) (hκ : ∀ z, ‖κ z‖ = ‖z‖)
    (ν : ℕ) {f : Coord n → ℂ} (hf : ContDiff ℝ ∞ f) :
    cNorm ν (fun y => κ (f (affineHomeomorph (signedPermEquiv σ ε hε) b y))) = cNorm ν f := by
  have hs : Function.Surjective
      (fun p : DerivIndex n ν => (⟨p.1, σ ∘ p.2⟩ : DerivIndex n ν)) := by
    rintro ⟨k, c⟩
    refine ⟨⟨k, σ.symm ∘ c⟩, ?_⟩
    have : σ ∘ σ.symm ∘ c = c := by
      funext i
      simp
    simp only [this]
  refine Eq.trans (iSup_congr fun p => ?_)
    (hs.iSup_comp (fun p : DerivIndex n ν => TestFunctions.uniformNorm (partialDeriv p.2 f)))
  unfold TestFunctions.uniformNorm
  refine Eq.trans (iSup_congr fun x => ?_)
    ((affineHomeomorph (signedPermEquiv σ ε hε) b).surjective.iSup_comp
      (fun y => ‖partialDeriv (σ ∘ p.2) f y‖))
  rw [partialDeriv_compTest σ ε hε b κ p.2 hf x, norm_smul, hκ, norm_prod]
  have : ∏ j, ‖ε (p.2 j)‖ = 1 := Finset.prod_eq_one fun j _ => by
    rcases hε (p.2 j) with h | h <;> simp [h]
  rw [this, one_mul]
theorem preservesSupportNormLimit_of_comp (κ : ℂ ≃L[ℝ] ℂ) (ψ : Coord n ≃ₜ Coord n)
    (hψs : ContDiff ℝ ∞ ψ.symm)
    (hn : ∀ (ν : ℕ) (f : Coord n → ℂ), ContDiff ℝ ∞ f →
      cNorm ν (fun y => κ (f (ψ y))) = cNorm ν f)
    {V U : Opens (Coord n)} (hVU : ∀ x, ψ x ∈ V ↔ x ∈ U)
    (Φ : testFunctionSpace V → testFunctionSpace U)
    (hΦ : ∀ (φ : testFunctionSpace V) (x : Coord n),
      (Φ φ : Coord n → ℂ) x = κ ((φ : Coord n → ℂ) (ψ x))) :
    PreservesSupportNormLimit ψ Φ := by
  have hfun : ∀ φ : testFunctionSpace V,
      (Φ φ : Coord n → ℂ) = fun x => κ ((φ : Coord n → ℂ) (ψ x)) :=
    fun φ => funext (hΦ φ)
  have hsymm : ∀ y, ψ.symm y ∈ U ↔ y ∈ V := fun y => by
    rw [← hVU (ψ.symm y)]
    simp
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro φ φ' h
    apply Subtype.ext
    funext y
    have h1 := congrFun (congrArg (fun F : testFunctionSpace U => (F : Coord n → ℂ)) h) (ψ.symm y)
    simp only [hΦ] at h1
    simpa using κ.injective h1
  · intro G
    refine ⟨⟨_, comp_mem_testFunctionSpace κ.symm ψ.symm hψs hsymm G.2⟩, ?_⟩
    apply Subtype.ext
    funext x
    show (Φ _ : Coord n → ℂ) x = _
    rw [hΦ]
    simp
  · intro φ
    rw [hfun, tsupport_comp_homeomorph]
  · intro ν φ
    rw [hfun]
    exact hn ν _ φ.2.1
  · intro G φ h
    obtain ⟨⟨S, hS, hSU, hφS, hGS⟩, hlim⟩ := h
    refine ⟨⟨ψ ⁻¹' S, ψ.isCompact_preimage.2 hS, fun x hx => (hVU x).1 (hSU hx), ?_, fun t => ?_⟩,
      fun ν => ?_⟩
    · rw [hfun, tsupport_comp_homeomorph]
      exact Set.preimage_mono hφS
    · rw [hfun, tsupport_comp_homeomorph]
      exact Set.preimage_mono (hGS t)
    · have hsub : ∀ t, cNorm ν ((G t : Coord n → ℂ) - (φ : Coord n → ℂ)) =
          cNorm ν ((Φ (G t) : Coord n → ℂ) - (Φ φ : Coord n → ℂ)) := by
        intro t
        have e : (Φ (G t) : Coord n → ℂ) - (Φ φ : Coord n → ℂ) =
            fun x => κ (((G t : Coord n → ℂ) - (φ : Coord n → ℂ)) (ψ x)) := by
          funext x
          simp [hΦ]
        rw [e]
        exact (hn ν _ ((G t).2.1.sub φ.2.1)).symm
      exact (hlim ν).congr hsub
def compTestLinear (ψ : Coord n ≃ₜ Coord n) (hψ : ContDiff ℝ ∞ ψ) {V U : Opens (Coord n)}
    (hVU : ∀ x, ψ x ∈ V ↔ x ∈ U) : testFunctionSpace V →ₗ[ℂ] testFunctionSpace U where
  toFun := compTest (ContinuousLinearEquiv.refl ℝ ℂ) ψ hψ hVU
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def compTestConjLinear (ψ : Coord n ≃ₜ Coord n) (hψ : ContDiff ℝ ∞ ψ) {V U : Opens (Coord n)}
    (hVU : ∀ x, ψ x ∈ V ↔ x ∈ U) : testFunctionSpace V →ₛₗ[starRingEnd ℂ] testFunctionSpace U where
  toFun := compTest Complex.conjCLE ψ hψ hVU
  map_add' φ χ := by
    apply Subtype.ext
    funext x
    simp [compTest]
  map_smul' c φ := by
    apply Subtype.ext
    funext x
    simp [compTest]
theorem testFunctionPullback_of_signed (σ : Equiv.Perm (Fin n)) (ε : Fin n → ℝ)
    (hε : ∀ j, ε j = 1 ∨ ε j = -1) (b : Coord n) {V U : Opens (Coord n)}
    (hVU : ∀ x, affineHomeomorph (signedPermEquiv σ ε hε) b x ∈ V ↔ x ∈ U) :
    TestFunctionPullback (affineHomeomorph (signedPermEquiv σ ε hε) b) V U := by
  have hψ := contDiff_affineHomeomorph (signedPermEquiv σ ε hε) b
  have hψs := contDiff_affineHomeomorph_symm (signedPermEquiv σ ε hε) b
  refine ⟨⟨compTestLinear _ hψ hVU, fun φ => rfl, ?_⟩,
    ⟨compTestConjLinear _ hψ hVU, fun φ x => rfl, ?_⟩⟩
  · exact preservesSupportNormLimit_of_comp (ContinuousLinearEquiv.refl ℝ ℂ) _ hψs
      (fun ν f hf => cNorm_compTest σ ε hε b _ (fun _ => rfl) ν hf) hVU _ fun φ x => rfl
  · exact preservesSupportNormLimit_of_comp Complex.conjCLE _ hψs
      (fun ν f hf => cNorm_compTest σ ε hε b _ (fun z => by simp) ν hf) hVU _ fun φ x => rfl
theorem distributionPullback_of_signed (σ : Equiv.Perm (Fin n)) (ε : Fin n → ℝ)
    (hε : ∀ j, ε j = 1 ∨ ε j = -1) (b : Coord n) {V U : Opens (Coord n)}
    (hVU : ∀ x, affineHomeomorph (signedPermEquiv σ ε hε) b x ∈ V ↔ x ∈ U)
    (T : Distribution U) :
    DistributionPullback (affineHomeomorph (signedPermEquiv σ ε hε) b) V T := by
  have hψ := contDiff_affineHomeomorph (signedPermEquiv σ ε hε) b
  set ψ := affineHomeomorph (signedPermEquiv σ ε hε) b with hψdef
  let Φ : testFunctionSpace V →ₗ[ℂ] testFunctionSpace U := compTestLinear ψ hψ hVU
  have hsub : ∀ S : Set (Coord n), S ⊆ V → ψ ⁻¹' S ⊆ U :=
    fun S hSV x hx => (hVU x).1 (hSV hx)
  have hbound : ∀ (ν : ℕ) (S : Set (Coord n)), HasOrderBound T.form (ψ ⁻¹' S) ν →
      HasOrderBound (T.form ∘ₗ Φ) S ν := by
    rintro ν S ⟨C, hC, hb⟩
    refine ⟨C, hC, fun φ hφ => ?_⟩
    have hs : tsupport (Φ φ : Coord n → ℂ) ⊆ ψ ⁻¹' S := by
      have e : (Φ φ : Coord n → ℂ) =
          fun x => ContinuousLinearEquiv.refl ℝ ℂ ((φ : Coord n → ℂ) (ψ x)) := rfl
      rw [e, tsupport_comp_homeomorph]
      exact Set.preimage_mono hφ
    have h1 := hb (Φ φ) hs
    have h2 : cNorm ν (Φ φ : Coord n → ℂ) = cNorm ν (φ : Coord n → ℂ) :=
      cNorm_compTest σ ε hε b (ContinuousLinearEquiv.refl ℝ ℂ) (fun _ => rfl) ν φ.2.1
    rw [h2] at h1
    exact h1
  refine ⟨⟨T.form ∘ₗ Φ, fun S hS hSV => ?_⟩, fun φ => ⟨(Φ φ).2, rfl⟩,
    fun ν₀ h S hS hSV => ?_⟩
  · obtain ⟨ν, h⟩ := T.bound (ψ ⁻¹' S) (ψ.isCompact_preimage.2 hS) (hsub S hSV)
    exact ⟨ν, hbound ν S h⟩
  · exact hbound ν₀ S (h _ (ψ.isCompact_preimage.2 hS) (hsub S hSV))
theorem signedAffine_eq_affineHomeomorph {P : Matrix (Fin n) (Fin n) ℝ} (σ : Equiv.Perm (Fin n))
    (ε : Fin n → ℝ) (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (hP : ∀ i j, P i j = if i = σ j then ε j else 0) (b : Coord n) :
    signedAffine P b = affineHomeomorph (signedPermEquiv σ ε hε) b := by
  funext x
  rw [affineHomeomorph_apply, signedAffine, mulVec_eq_signedPermEquiv σ ε hε hP]
theorem elementaryFacts_holds : ElementaryFacts := by
  intro n _ U
  refine ⟨finiteCombinationsClosed_holds U,
    fun T => ⟨isSeqContinuous_of_distribution T, restrictPreservesOrder_of_distribution T⟩, ?_⟩
  rintro P ⟨σ, ε, hε, hP⟩ b
  rw [signedAffine_eq_affineHomeomorph σ ε hε hP b]
  refine ⟨(affineHomeomorph (signedPermEquiv σ ε hε) b).isOpenMap _ U.isOpen, fun V hV => ?_⟩
  have hVU : ∀ x, affineHomeomorph (signedPermEquiv σ ε hε) b x ∈ V ↔ x ∈ U := by
    intro x
    have h : affineHomeomorph (signedPermEquiv σ ε hε) b x ∈ (V : Set (Coord n)) ↔
        affineHomeomorph (signedPermEquiv σ ε hε) b x ∈
          affineHomeomorph (signedPermEquiv σ ε hε) b '' (U : Set (Coord n)) := by rw [hV]
    rw [(affineHomeomorph (signedPermEquiv σ ε hε) b).injective.mem_set_image] at h
    exact h
  exact ⟨testFunctionPullback_of_signed σ ε hε b hVU,
    fun T => distributionPullback_of_signed σ ε hε b hVU T⟩
end YangMills.Construction.DistributionBasics
end
