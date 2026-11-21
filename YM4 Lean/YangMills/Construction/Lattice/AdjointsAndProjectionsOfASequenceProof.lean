import YangMills.Construction.Lattice.AdjointsAndProjectionsOfASequence
import YangMills.Construction.Lattice.FactsOfTheFormExtensionProof
import Mathlib
set_option autoImplicit false
open YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators
noncomputable section
namespace YangMills.Construction.SeparatedSequences.AdjointsAndProjections
section FiniteDimensional
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
def IsInnerForm (ip : V → V → ℝ) : Prop :=
  ∃ B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ, (∀ f g, B f g = ip f g) ∧ ∀ f, f ≠ 0 → 0 < ip f f
omit [FiniteDimensional ℝ W] in
theorem exists_isAdjointFor {ipV : V → V → ℝ} {ipW : W → W → ℝ} (hV : IsInnerForm ipV)
    (hW : IsInnerForm ipW) (T : V →ₗ[ℝ] W) :
    ∃ T' : W →ₗ[ℝ] V, FiniteDimReal.IsAdjointFor ipV ipW T T' := by
  obtain ⟨B, hB, hpos⟩ := hV
  obtain ⟨C, hC, -⟩ := hW
  have hinj : Function.Injective (B : V →ₗ[ℝ] Module.Dual ℝ V) := by
    refine (injective_iff_map_eq_zero _).mpr fun f hf => ?_
    by_contra hne
    have h := hpos f hne
    rw [← hB, hf] at h
    simp at h
  let e : V ≃ₗ[ℝ] Module.Dual ℝ V :=
    LinearMap.linearEquivOfInjective (B : V →ₗ[ℝ] Module.Dual ℝ V) hinj
      Subspace.dual_finrank_eq.symm
  refine ⟨e.symm.toLinearMap ∘ₗ T.dualMap ∘ₗ C, fun f g => ?_⟩
  have h : B (e.symm (T.dualMap (C g))) = T.dualMap (C g) := e.apply_symm_apply _
  rw [← hC, ← hB]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [h]
  rfl
theorem exists_isOrthogonalProjectionFor {ip : V → V → ℝ} (hV : IsInnerForm ip)
    (S : Submodule ℝ V) : ∃ P : V →ₗ[ℝ] V, RealInnerForms.IsOrthogonalProjectionFor ip S P := by
  have hS : IsInnerForm (fun a b : S => ip a b) := by
    obtain ⟨B, hB, hpos⟩ := hV
    refine ⟨B.compl₁₂ S.subtype S.subtype, fun a b => ?_, fun a ha => ?_⟩
    · simp [hB]
    · exact hpos a (by simpa using ha)
  obtain ⟨T', hT'⟩ := exists_isAdjointFor hS hV S.subtype
  obtain ⟨B, hB, -⟩ := hV
  refine ⟨S.subtype ∘ₗ T', fun f => ⟨(T' f).2, fun w hw => ?_⟩⟩
  have h : ip f w = ip (T' f) w := hT' ⟨w, hw⟩ f
  rw [← hB, map_sub, LinearMap.sub_apply, hB, hB]
  simpa using sub_eq_zero.mpr h
omit [FiniteDimensional ℝ V] in
theorem isInnerForm_of_weighted_coordinates {ι : ℕ → Type} [∀ n, Finite (ι n)] (t : ℕ) (c : ℕ → ℝ)
    (hc : ∀ n, 0 < c n) (v : ∀ n, V →ₗ[ℝ] (ι n → ℝ))
    (hv : ∀ f, (∀ n ≤ t, ∀ i, v n f i = 0) → f = 0) (ip : V → V → ℝ)
    (hip : ∀ f g, ip f g = ∑ n ∈ Finset.range (t + 1), c n * ∑ᶠ i, v n f i * v n g i) :
    IsInnerForm ip := by
  let _ : ∀ n, Fintype (ι n) := fun n => Fintype.ofFinite _
  have hip' : ∀ f g, ip f g = ∑ n ∈ Finset.range (t + 1), c n * ∑ i, v n f i * v n g i := by
    intro f g
    rw [hip]
    simp only [finsum_eq_sum_of_fintype]
  refine ⟨LinearMap.mk₂ ℝ ip ?_ ?_ ?_ ?_, fun f g => rfl, fun f hf => ?_⟩
  · intro f f' g
    simp only [hip', map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  · intro r f g
    simp only [hip', map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun i _ => by ring
  · intro f g g'
    simp only [hip', map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  · intro r f g
    simp only [hip', map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun i _ => by ring
  · have hex : ∃ n ≤ t, ∃ i, v n f i ≠ 0 := by
      by_contra hno
      push Not at hno
      exact hf (hv f hno)
    obtain ⟨n, hn, i, hi⟩ := hex
    rw [hip']
    refine Finset.sum_pos' (fun k _ => mul_nonneg (hc k).le
      (Finset.sum_nonneg fun j _ => mul_self_nonneg _)) ⟨n, ?_, ?_⟩
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
    · refine mul_pos (hc n) (Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, ?_, ?_⟩)
      · exact Finset.mem_univ i
      · exact mul_self_pos.mpr hi
end FiniteDimensional
variable (D : BaseParameters) (Ω : ℕ → Set D.Torus) (φ : BondFrame)
theorem finestMesh_pos : 0 < finestMeshInLevelUnits D.L D.t := by apply _root_.YangMills.Construction.SeparatedSequences.OneExtensionProof.finestMesh_pos <;> assumption
theorem levelMeshRatio_pos (n : ℕ) : 0 < D.levelMeshRatio n := by apply _root_.YangMills.Construction.SeparatedSequences.OneExtensionProof.levelMeshRatio_pos <;> assumption
def pointEvaluation (n : ℕ) : D.CoarseZeroForms Ω →ₗ[ℝ] (↥(D.layerSites Ω n) → ℝ) where
  toFun ω y := BaseParameters.pointValue ω (y.1 : D.Torus)
  map_add' ω ω' := by
    funext y
    simp only [Pi.add_apply, BaseParameters.pointValue_add]
  map_smul' r ω := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      BaseParameters.pointValue_smul]
def linkValueMap (n : ℕ) : D.CoarseOneForms Ω φ →ₗ[ℝ] (↥(D.layerBondSet Ω φ n) → ℝ) where
  toFun B c := BaseParameters.principalBondValue B ⟨n, c.1⟩
  map_add' B B' := by
    funext c
    simp only [Pi.add_apply, BaseParameters.principalBondValue_add]
  map_smul' r B := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      BaseParameters.principalBondValue_smul]
theorem isInnerForm_restrictedZeroInner : IsInnerForm (D.restrictedZeroInner Ω) := by
  have : Finite (BareSite D.L D.m D.K) := BaseParameters.instFiniteLatticeSite D 0
  refine isInnerForm_of_weighted_coordinates (ι := fun _ => BareSite D.L D.m D.K) 0
    (fun _ => finestMeshInLevelUnits D.L D.t ^ 4) (fun _ => pow_pos (finestMesh_pos D) 4)
    (fun _ => (zeroFormsOn D.K (Ω 0)).subtype) (fun f hf => ?_) _ fun f g => ?_
  · exact Subtype.ext (funext fun i => hf 0 le_rfl i)
  · simp [BaseParameters.restrictedZeroInner, latticeInner]
theorem isInnerForm_restrictedOneInner : IsInnerForm (D.restrictedOneInner Ω φ) := by
  have : Finite (BareBond D.L D.m D.K) := BaseParameters.instFiniteLevelBond D 0
  refine isInnerForm_of_weighted_coordinates (ι := fun _ => BareBond D.L D.m D.K) 0
    (fun _ => finestMeshInLevelUnits D.L D.t ^ 4) (fun _ => pow_pos (finestMesh_pos D) 4)
    (fun _ => (oneFormsOn D.K (Ω 0) φ).subtype) (fun f hf => ?_) _ fun f g => ?_
  · exact Subtype.ext (funext fun i => hf 0 le_rfl i)
  · simp [BaseParameters.restrictedOneInner, latticeInner]
theorem isInnerForm_coarseZeroInner : IsInnerForm (D.coarseZeroInner Ω) := by
  refine isInnerForm_of_weighted_coordinates D.t
    (fun n => D.levelMeshRatio n ^ BaseParameters.dimension)
    (fun n => pow_pos (levelMeshRatio_pos D n) _) (pointEvaluation D Ω) (fun ω hω => ?_) _
    fun ω ω' => rfl
  funext y
  obtain ⟨p, hp, hmem, hy⟩ := D.exists_levelSite Ω y
  have h := hω p.1 hp ⟨p.2, hmem⟩
  simp only [pointEvaluation, LinearMap.coe_mk, AddHom.coe_mk, hy,
    BaseParameters.pointValue, y.2, dif_pos] at h
  simpa using h
theorem isInnerForm_coarseOneInner : IsInnerForm (D.coarseOneInner Ω φ) := by
  refine isInnerForm_of_weighted_coordinates D.t
    (fun n => D.levelMeshRatio n ^ BaseParameters.dimension)
    (fun n => pow_pos (levelMeshRatio_pos D n) _) (linkValueMap D Ω φ) (fun B hB => ?_) _
    fun B B' => rfl
  funext c
  obtain ⟨⟨n, b⟩, hc⟩ := c
  have h := hB n hc.1 ⟨b, hc.2⟩
  simp only [linkValueMap, LinearMap.coe_mk, AddHom.coe_mk,
    BaseParameters.principalBondValue, dif_pos hc] at h
  simpa using h
theorem holds : Statement := by
  intro D Ω φ
  have hZero := isInnerForm_restrictedZeroInner D Ω
  have hOne := isInnerForm_restrictedOneInner D Ω φ
  have hCoarseZero := isInnerForm_coarseZeroInner D Ω
  have hCoarseOne := isInnerForm_coarseOneInner D Ω φ
  have hWholeZero := isInnerForm_coarseZeroInner D (D.withWholeTorus Ω)
  have hWholeOne := isInnerForm_coarseOneInner D (D.withWholeTorus Ω) φ
  exact
    { zero_adjoint := Classical.epsilon_spec (exists_isAdjointFor hZero hCoarseZero _)
      one_adjoint := Classical.epsilon_spec (exists_isAdjointFor hOne hCoarseOne _)
      gauge_projection := Classical.epsilon_spec (exists_isOrthogonalProjectionFor hZero _)
      coarse_zero_projection :=
        Classical.epsilon_spec (exists_isOrthogonalProjectionFor hWholeZero _)
      coarse_one_projection :=
        Classical.epsilon_spec (exists_isOrthogonalProjectionFor hWholeOne _) }
end YangMills.Construction.SeparatedSequences.AdjointsAndProjections
end
