import YangMills.Construction.PeriodicOperators.SumsOfExponentialsProof
import YangMills.Construction.InfiniteLattice.AllMirrorsAtSpacingOneProof
import YangMills.Construction.InfiniteLattice.BondsAndCutPlaquettesAtAMirrorProof
import YangMills.Construction.InfiniteLattice.DilationToSpacingOneProof
import YangMills.Construction.ReflectionPositivity.SimpleTransitivityOnTheSlabsProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies.Properties
open YangMills.Construction.InfiniteLattice YangMills.Construction.NormalFamilies
open YangMills.Construction.PeriodicLattice (coordVec)
def intNormals : Fin 16 → Fin 4 → ℤ :=
  ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1],
    ![1, 1, 0, 0], ![1, -1, 0, 0], ![1, 0, 1, 0], ![1, 0, -1, 0], ![1, 0, 0, 1], ![1, 0, 0, -1],
    ![0, 1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, 1], ![0, 1, 0, -1], ![0, 0, 1, 1], ![0, 0, 1, -1]]
def castVec (u : Fin 4 → ℤ) : AmbientSpace := fun κ => (u κ : ℝ)
theorem intNormals_injective : Function.Injective intNormals := by
  have h : ∀ i j, intNormals i = intNormals j → i = j := by decide +kernel
  exact fun i j => h i j
theorem exists_intNormals_eq_single : ∀ μ : Fin 4, ∃ i, intNormals i = Pi.single μ 1 := by
  decide +kernel
theorem exists_intNormals_eq_single_add : ∀ μ lam : Fin 4, μ < lam →
    ∃ i, intNormals i = Pi.single μ 1 + Pi.single lam 1 := by
  decide +kernel
theorem exists_intNormals_eq_single_sub : ∀ μ lam : Fin 4, μ < lam →
    ∃ i, intNormals i = Pi.single μ 1 - Pi.single lam 1 := by
  decide +kernel
theorem intNormals_cases : ∀ i, (∃ μ : Fin 4, intNormals i = Pi.single μ 1) ∨
    ∃ μ lam : Fin 4, μ < lam ∧ (intNormals i = Pi.single μ 1 + Pi.single lam 1 ∨
      intNormals i = Pi.single μ 1 - Pi.single lam 1) := by
  decide +kernel
theorem intNormals_dotProduct_self : ∀ i,
    intNormals i ⬝ᵥ intNormals i = if i.val < 4 then 1 else 2 := by
  decide +kernel
theorem intNormals_apply_cases : ∀ i ρ, intNormals i ρ = 0 ∨ intNormals i ρ = 1 ∨
    intNormals i ρ = -1 := by
  decide +kernel
theorem exists_intNormals_ne_zero : ∀ i, ∃ μ, intNormals i μ ≠ 0 := by
  decide +kernel
theorem intNormals_apply_first_nonzero : ∀ i μ, intNormals i μ ≠ 0 →
    (∀ κ, κ < μ → intNormals i κ = 0) → intNormals i μ = 1 := by
  decide +kernel
theorem castVec_injective : Function.Injective castVec := by
  intro u v h
  funext κ
  simpa [castVec] using congrFun h κ
theorem castVec_dotProduct (u v : Fin 4 → ℤ) :
    castVec u ⬝ᵥ castVec v = ((u ⬝ᵥ v : ℤ) : ℝ) := by
  simp [castVec, dotProduct]
theorem coordVec_eq_castVec (μ : Fin 4) :
    coordVec μ = castVec (Pi.single μ 1) := by
  funext κ
  by_cases h : κ = μ
  · subst h
    simp [coordVec, castVec]
  · simp [coordVec, castVec, Pi.single_eq_of_ne h]
theorem castVec_add (u v : Fin 4 → ℤ) : castVec (u + v) = castVec u + castVec v := by apply _root_.YangMills.Construction.PeriodicOperators.ExponentialSums.castVec_add <;> assumption
theorem castVec_sub (u v : Fin 4 → ℤ) : castVec (u - v) = castVec u - castVec v := by
  funext κ
  simp [castVec]
theorem exists_castVec_intNormals_of_mem {n : AmbientSpace} (hn : n ∈ normalSet) :
    ∃ i, n = castVec (intNormals i) := by
  rcases hn with ⟨μ, rfl⟩ | ⟨μ, lam, hlt, rfl | rfl⟩
  · obtain ⟨i, hi⟩ := exists_intNormals_eq_single μ
    exact ⟨i, by rw [hi, coordVec_eq_castVec]⟩
  · obtain ⟨i, hi⟩ := exists_intNormals_eq_single_add μ lam hlt
    exact ⟨i, by rw [hi, castVec_add, coordVec_eq_castVec, coordVec_eq_castVec]⟩
  · obtain ⟨i, hi⟩ := exists_intNormals_eq_single_sub μ lam hlt
    exact ⟨i, by rw [hi, castVec_sub, coordVec_eq_castVec, coordVec_eq_castVec]⟩
theorem castVec_intNormals_mem (i : Fin 16) : castVec (intNormals i) ∈ normalSet := by
  rcases intNormals_cases i with ⟨μ, h⟩ | ⟨μ, lam, hlt, h | h⟩
  · exact Or.inl ⟨μ, by rw [h, coordVec_eq_castVec]⟩
  · exact Or.inr ⟨μ, lam, hlt, Or.inl (by
      rw [h, castVec_add, coordVec_eq_castVec, coordVec_eq_castVec])⟩
  · exact Or.inr ⟨μ, lam, hlt, Or.inr (by
      rw [h, castVec_sub, coordVec_eq_castVec, coordVec_eq_castVec])⟩
theorem normSq_castVec_intNormals (i : Fin 16) :
    normSq (castVec (intNormals i)) = if i.val < 4 then 1 else 2 := by
  rw [normSq_eq_dotProduct, castVec_dotProduct, intNormals_dotProduct_self]
  split_ifs <;> simp
theorem castVec_intNormals_injective : Function.Injective fun i => castVec (intNormals i) :=
  castVec_injective.comp intNormals_injective
theorem normSq_eq_one_or_two {n : AmbientSpace} (hn : n ∈ normalSet) :
    normSq n = 1 ∨ normSq n = 2 := by
  obtain ⟨i, rfl⟩ := exists_castVec_intNormals_of_mem hn
  rw [normSq_castVec_intNormals]
  split_ifs <;> simp
theorem normSq_ne_zero {n : AmbientSpace} (hn : n ∈ normalSet) : normSq n ≠ 0 := by
  rcases normSq_eq_one_or_two hn with h | h <;> rw [h] <;> norm_num
theorem dotProduct_self_ne_zero {n : AmbientSpace} (hn : n ∈ normalSet) : n ⬝ᵥ n ≠ 0 := by
  rw [← normSq_eq_dotProduct]
  exact normSq_ne_zero hn
theorem dotProduct_dualVector {n : AmbientSpace} (hn : n ∈ normalSet) :
    n ⬝ᵥ dualVector n = 1 := by apply _root_.YangMills.Construction.NormalFamilies.dotProduct_dualVector <;> assumption
theorem dotProduct_coordVec (x : AmbientSpace) (μ : Fin 4) : x ⬝ᵥ coordVec μ = x μ := by
  simp [coordVec, dotProduct, Pi.single_apply]
theorem coordVec_dotProduct (x : AmbientSpace) (μ : Fin 4) : coordVec μ ⬝ᵥ x = x μ := by
  simp [coordVec, dotProduct, Pi.single_apply]
theorem apply_firstNonzeroIndex {n : AmbientSpace} (hn : n ∈ normalSet) :
    n (firstNonzeroIndex n) = 1 := by
  obtain ⟨i, rfl⟩ := exists_castVec_intNormals_of_mem hn
  have hex : ∃ μ, castVec (intNormals i) μ ≠ 0 := by
    obtain ⟨μ, hμ⟩ := exists_intNormals_ne_zero i
    exact ⟨μ, by simpa [castVec] using hμ⟩
  obtain ⟨h₁, h₂⟩ := firstNonzeroIndex_spec hex
  have h₃ := intNormals_apply_first_nonzero i (firstNonzeroIndex (castVec (intNormals i)))
    (by simpa [castVec] using h₁) (fun κ hκ => by simpa [castVec] using h₂ κ hκ)
  simp [castVec, h₃]
theorem dotProduct_firstNonzeroBasisVec {n : AmbientSpace} (hn : n ∈ normalSet) :
    n ⬝ᵥ firstNonzeroBasisVec n = 1 := by
  rw [firstNonzeroBasisVec, dotProduct_coordVec, apply_firstNonzeroIndex hn]
theorem apply_cases {n : AmbientSpace} (hn : n ∈ normalSet) (ρ : Fin 4) :
    n ρ = 0 ∨ n ρ = 1 ∨ n ρ = -1 := by
  obtain ⟨i, rfl⟩ := exists_castVec_intNormals_of_mem hn
  rcases intNormals_apply_cases i ρ with h | h | h <;> simp [castVec, h]
theorem exists_int_linearHeight {n : AmbientSpace} (hn : n ∈ normalSet) {x : AmbientSpace}
    (hx : x ∈ latticeSubgroup 1) : ∃ k : ℤ, linearHeight n x = (k : ℝ) := by
  obtain ⟨i, rfl⟩ := exists_castVec_intNormals_of_mem hn
  obtain ⟨m, hm⟩ := hx
  have hxm : x = castVec m := by
    funext μ
    simp [castVec, hm]
  exact ⟨_, by rw [linearHeight, hxm, castVec_dotProduct]⟩
theorem ncard_val_lt_four : {i : Fin 16 | i.val < 4}.ncard = 4 := by
  have h : {i : Fin 16 | i.val < 4} = ↑(Finset.univ.filter fun i : Fin 16 => i.val < 4) := by
    ext i
    simp
  rw [h, Set.ncard_coe_finset]
  rfl
theorem ncard_not_val_lt_four : {i : Fin 16 | ¬ i.val < 4}.ncard = 12 := by
  have h : {i : Fin 16 | ¬ i.val < 4} = ↑(Finset.univ.filter fun i : Fin 16 => ¬ i.val < 4) := by
    ext i
    simp
  rw [h, Set.ncard_coe_finset]
  rfl
theorem normalSet_eq_image :
    normalSet = (fun i => castVec (intNormals i)) '' (univ : Set (Fin 16)) := by
  ext n
  constructor
  · intro hn
    obtain ⟨i, rfl⟩ := exists_castVec_intNormals_of_mem hn
    exact ⟨i, mem_univ i, rfl⟩
  · rintro ⟨i, -, rfl⟩
    exact castVec_intNormals_mem i
theorem normSq_one_eq_image :
    {n ∈ normalSet | normSq n = 1} =
      (fun i => castVec (intNormals i)) '' {i : Fin 16 | i.val < 4} := by
  ext n
  constructor
  · rintro ⟨hn, hq⟩
    obtain ⟨i, rfl⟩ := exists_castVec_intNormals_of_mem hn
    refine ⟨i, ?_, rfl⟩
    rw [normSq_castVec_intNormals] at hq
    by_contra h
    have h' : ¬ i.val < 4 := h
    rw [if_neg h'] at hq
    norm_num at hq
  · rintro ⟨i, hi, rfl⟩
    have hi' : i.val < 4 := hi
    refine ⟨castVec_intNormals_mem i, ?_⟩
    rw [normSq_castVec_intNormals, if_pos hi']
theorem normSq_two_eq_image :
    {n ∈ normalSet | normSq n = 2} =
      (fun i => castVec (intNormals i)) '' {i : Fin 16 | ¬ i.val < 4} := by
  ext n
  constructor
  · rintro ⟨hn, hq⟩
    obtain ⟨i, rfl⟩ := exists_castVec_intNormals_of_mem hn
    refine ⟨i, ?_, rfl⟩
    rw [normSq_castVec_intNormals] at hq
    intro h
    rw [if_pos h] at hq
    norm_num at hq
  · rintro ⟨i, hi, rfl⟩
    refine ⟨castVec_intNormals_mem i, ?_⟩
    rw [normSq_castVec_intNormals, if_neg hi]
theorem normalSet_counts_holds : normalSet_counts := by
  refine ⟨?_, ?_, ?_, fun n hn => ⟨dotProduct_dualVector hn, dotProduct_firstNonzeroBasisVec hn,
    apply_cases hn, fun x hx => exists_int_linearHeight hn hx⟩⟩
  · rw [normalSet_eq_image, ncard_image_of_injective _ castVec_intNormals_injective, ncard_univ]
    simp
  · rw [normSq_one_eq_image, ncard_image_of_injective _ castVec_intNormals_injective,
      ncard_val_lt_four]
  · rw [normSq_two_eq_image, ncard_image_of_injective _ castVec_intNormals_injective,
      ncard_not_val_lt_four]
theorem dotProduct_reflectAcross {n : AmbientSpace} (hn : n ∈ normalSet) (c : ℝ)
    (x : AmbientSpace) : n ⬝ᵥ reflectAcross n c x = 2 * c - n ⬝ᵥ x := by apply _root_.YangMills.Construction.InfiniteLattice.SlabTransitivity.dotProduct_reflectAcross <;> assumption
theorem isOrthogonalReflection_reflectAcross {n : AmbientSpace} (hn : n ∈ normalSet) (c : ℝ) :
    IsOrthogonalReflection (reflectAcross n c) (levelHyperplane n c) := by
  intro x
  refine ⟨?_, fun y hy z hz => ?_⟩
  · change n ⬝ᵥ ((1 / 2 : ℝ) • (x + reflectAcross n c x)) = c
    rw [dotProduct_smul, dotProduct_add, dotProduct_reflectAcross hn, smul_eq_mul]
    ring
  · have hy' : n ⬝ᵥ y = c := hy
    have hz' : n ⬝ᵥ z = c := hz
    have h : reflectAcross n c x - x = (-(2 * (n ⬝ᵥ x - c))) • dualVector n := by
      rw [reflectAcross, neg_smul]
      abel
    rw [h, smul_dotProduct, dualVector, smul_dotProduct, dotProduct_sub, hy', hz']
    simp
theorem euclidNormVec_reflectAcross_sub {n : AmbientSpace} (hn : n ∈ normalSet) (c : ℝ)
    (x y : AmbientSpace) :
    TorusMetric.euclidNormVec (reflectAcross n c x - reflectAcross n c y) =
      TorusMetric.euclidNormVec (x - y) := by
  rw [reflectAcross_eq_hyperplaneReflect]
  exact euclidNormVec_hyperplaneReflect_sub (dotProduct_self_ne_zero hn) c x y
theorem reflectAcross_comp_self {n : AmbientSpace} (hn : n ∈ normalSet) (c : ℝ) :
    reflectAcross n c ∘ reflectAcross n c = id := by
  funext x
  rw [reflectAcross_eq_hyperplaneReflect]
  exact hyperplaneReflect_hyperplaneReflect (dotProduct_self_ne_zero hn) c x
theorem reflectAcross_zero_apply_firstNonzeroIndex {n : AmbientSpace} (hn : n ∈ normalSet)
    (c : ℝ) : reflectAcross n c 0 (firstNonzeroIndex n) = 2 * c * (normSq n)⁻¹ := by
  simp [reflectAcross, dualVector, apply_firstNonzeroIndex hn]
theorem isAllowedLevel_of_image {n : AmbientSpace} (hn : n ∈ normalSet) {c : ℝ}
    (h : reflectAcross n c '' (latticeSubgroup 1 : Set AmbientSpace) =
      (latticeSubgroup 1 : Set AmbientSpace)) :
    IsAllowedLevel 1 n c := by
  have h0 : reflectAcross n c 0 ∈ (latticeSubgroup 1 : Set AmbientSpace) := by
    rw [← h]
    exact ⟨0, (latticeSubgroup 1).zero_mem, rfl⟩
  obtain ⟨m, hm⟩ := h0
  have hv := hm (firstNonzeroIndex n)
  rw [reflectAcross_zero_apply_firstNonzeroIndex hn] at hv
  constructor
  · intro hq
    refine ⟨m (firstNonzeroIndex n), ?_⟩
    rw [hq] at hv
    linarith
  · intro hq
    refine ⟨m (firstNonzeroIndex n), ?_⟩
    rw [hq] at hv
    linarith
theorem image_eq_of_isAllowedLevel {n : AmbientSpace} (hn : n ∈ normalSet) {c : ℝ}
    (h : IsAllowedLevel 1 n c) :
    reflectAcross n c '' (latticeSubgroup 1 : Set AmbientSpace) =
      (latticeSubgroup 1 : Set AmbientSpace) :=
  (⟨n, hn, c, h⟩ : NormalLevelPair 1).reflectSymmetry.image_eq
theorem reflectAcross_props_holds : reflectAcross_props := fun _ hn c =>
  ⟨isOrthogonalReflection_reflectAcross hn c, euclidNormVec_reflectAcross_sub hn c,
    dotProduct_reflectAcross hn c, reflectAcross_comp_self hn c,
    isAllowedLevel_of_image hn, image_eq_of_isAllowedLevel hn⟩
theorem realNormal_mem (F : ReflectionClass) : F.realNormal ∈ normalSet := by apply _root_.YangMills.Construction.UnitSpacing.realNormal_mem_normalSet <;> assumption
theorem isAllowedLevel_of_latticeMirror (Q : LatticeMirror 1) :
    IsAllowedLevel 1 Q.cls.realNormal Q.level := by
  obtain ⟨F, c, hc⟩ := Q
  cases F with
  | axial μ =>
    refine ⟨fun _ => hc, fun hq => ?_⟩
    rw [normSq_eq_dotProduct, ReflectionClass.realNormal_dot_axial] at hq
    norm_num at hq
  | diagonal μ lam hlt s =>
    refine ⟨fun hq => ?_, fun _ => hc⟩
    rw [normSq_eq_dotProduct, ReflectionClass.realNormal_dot_diagonal] at hq
    norm_num at hq
theorem levelPairs_eq_latticeMirrors_holds : levelPairs_eq_latticeMirrors := by
  refine ⟨?_, fun P => isOrthogonalReflection_reflectAcross P.normal_mem P.level,
    fun P hq => ?_⟩
  · ext H
    constructor
    · rintro ⟨P, rfl⟩
      refine ⟨P.toLatticeMirror, ?_⟩
      change {x | P.toLatticeMirror.cls.realNormal ⬝ᵥ x = P.level} = _
      rw [P.toLatticeMirror_realNormal]
      rfl
    · rintro ⟨Q, rfl⟩
      exact ⟨⟨Q.cls.realNormal, realNormal_mem Q.cls, Q.level,
        isAllowedLevel_of_latticeMirror Q⟩, rfl⟩
  · obtain ⟨k, hk⟩ := P.allowed.2 hq
    refine ⟨(k : ℝ) • firstNonzeroBasisVec P.normal,
      ⟨Pi.single (firstNonzeroIndex P.normal) k, fun μ => ?_⟩, ?_⟩
    · by_cases h : μ = firstNonzeroIndex P.normal
      · subst h
        simp [firstNonzeroBasisVec, coordVec]
      · simp [firstNonzeroBasisVec, coordVec, Pi.single_eq_of_ne h]
    · rw [dotProduct_smul, dotProduct_firstNonzeroBasisVec P.normal_mem, hk]
      simp
def reflectLinear (n : AmbientSpace) : AmbientSpace →ₗ[ℝ] AmbientSpace where
  toFun x := x - (2 * (n ⬝ᵥ x)) • dualVector n
  map_add' x y := by
    funext κ
    simp only [dotProduct_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' t x := by
    funext κ
    simp only [dotProduct_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
theorem reflectLinear_apply (n x : AmbientSpace) :
    reflectLinear n x = x - (2 * (n ⬝ᵥ x)) • dualVector n := rfl
theorem reflectAcross_linearPart_holds : reflectAcross_linearPart := by
  intro n hn
  refine ⟨reflectLinear n, reflectLinear_apply n, fun c => ⟨(2 * c) • dualVector n, fun x => ?_⟩,
    fun x hx => ?_, ?_⟩
  · funext κ
    simp only [reflectAcross, reflectLinear_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  · rw [reflectLinear_apply, hx]
    simp
  · have h : (2 * (n ⬝ᵥ n)) • dualVector n = (2 : ℝ) • n := by
      rw [dualVector, smul_smul, ← normSq_eq_dotProduct, mul_assoc,
        mul_inv_cancel₀ (normSq_ne_zero hn), mul_one]
    rw [reflectLinear_apply, h, two_smul]
    abel
theorem halfSpace_partition_holds : halfSpace_partition := by
  intro P
  refine ⟨fun ε F h₁ _ h₃ => ⟨h₁, h₃⟩, inter_subset_left, inter_subset_right,
    sdiff_inter_self, ?_⟩
  exact (union_sdiff_cancel (union_subset (fun b hb => hb.1) fun b hb => hb.1)).symm
theorem normSq_coordVec (μ : Fin 4) : normSq (coordVec μ) = 1 := by apply _root_.YangMills.Construction.TransferOperators.normSq_coordVec <;> assumption
theorem normSq_coordVec_add {μ lam : Fin 4} (h : μ ≠ lam) :
    normSq (coordVec μ + coordVec lam) = 2 := by apply _root_.YangMills.Construction.NormalFamilies.LevelCuts.normSq_coordVec_add <;> assumption
theorem isLinearMap_reflectAcross_zero (n : AmbientSpace) :
    IsLinearMap ℝ (reflectAcross n 0) := by
  constructor
  · intro x y
    funext κ
    simp only [reflectAcross, dotProduct_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  · intro t x
    funext κ
    simp only [reflectAcross, dotProduct_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
theorem reflectAcross_coordVec_zero (μ : Fin 4) (x : AmbientSpace) :
    reflectAcross (coordVec μ) 0 x = Function.update x μ (-x μ) := by
  funext κ
  simp only [reflectAcross, dualVector, normSq_coordVec, coordVec_dotProduct]
  by_cases h : κ = μ
  · subst h
    simp [coordVec]
    ring
  · simp [coordVec, Pi.single_eq_of_ne h, Function.update_of_ne h]
theorem reflectAcross_coordVec_sub_zero {μ lam : Fin 4} (hne : μ ≠ lam) (x : AmbientSpace) :
    reflectAcross (coordVec μ - coordVec lam) 0 x = x ∘ Equiv.swap μ lam := by apply _root_.YangMills.Construction.InfiniteLattice.UnitMeshReflectionPositivity.reflectAcross_coordVec_sub <;> assumption
theorem reflectAcross_coordVec_add_zero {μ lam : Fin 4} (hne : μ ≠ lam) (x : AmbientSpace) :
    reflectAcross (coordVec μ + coordVec lam) 0 x =
      Function.update (Function.update x μ (-x lam)) lam (-x μ) := by
  funext κ
  simp only [reflectAcross, dualVector, normSq_coordVec_add hne, add_dotProduct,
    coordVec_dotProduct]
  by_cases h : κ = lam
  · subst h
    simp [coordVec, Pi.single_eq_of_ne hne.symm]
    ring
  · by_cases h' : κ = μ
    · subst h'
      simp [coordVec, Pi.single_eq_of_ne hne, Function.update_of_ne h]
      ring
    · simp [coordVec, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h',
        Function.update_of_ne h, Function.update_of_ne h']
theorem reflectAcross_coordVec_add_zero_eq_comp {μ lam : Fin 4} (hne : μ ≠ lam) :
    reflectAcross (coordVec μ + coordVec lam) 0 =
      reflectAcross (coordVec μ) 0 ∘ reflectAcross (coordVec lam) 0 ∘
        reflectAcross (coordVec μ - coordVec lam) 0 := by
  funext x
  simp only [Function.comp_apply]
  rw [reflectAcross_coordVec_add_zero hne, reflectAcross_coordVec_sub_zero hne,
    reflectAcross_coordVec_zero, reflectAcross_coordVec_zero]
  funext κ
  by_cases h : κ = lam
  · subst h
    simp [Function.update_of_ne hne.symm]
  · by_cases h' : κ = μ
    · subst h'
      simp [Function.update_of_ne h]
    · simp [Function.update_of_ne h, Function.update_of_ne h',
        Equiv.swap_apply_of_ne_of_ne h' h]
def originReflections : Set (AmbientSpace ≃ₗ[ℝ] AmbientSpace) :=
  {w | ∃ n ∈ normalSet, ⇑w = reflectAcross n 0}
def permLinearEquiv (σ : Equiv.Perm (Fin 4)) : AmbientSpace ≃ₗ[ℝ] AmbientSpace where
  toFun x := x ∘ σ
  invFun x := x ∘ σ.symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    funext μ
    simp
  right_inv x := by
    funext μ
    simp
theorem permLinearEquiv_swap_mem_closure {μ lam : Fin 4} (hne : μ ≠ lam) :
    permLinearEquiv (Equiv.swap μ lam) ∈ Subgroup.closure originReflections := by
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine Subgroup.subset_closure ⟨coordVec μ - coordVec lam,
      Or.inr ⟨μ, lam, hlt, Or.inr rfl⟩, ?_⟩
    funext x
    rw [reflectAcross_coordVec_sub_zero hne]
    rfl
  · rw [Equiv.swap_comm]
    refine Subgroup.subset_closure ⟨coordVec lam - coordVec μ,
      Or.inr ⟨lam, μ, hlt, Or.inr rfl⟩, ?_⟩
    funext x
    rw [reflectAcross_coordVec_sub_zero hne.symm]
    rfl
theorem permLinearEquiv_mem_closure (σ : Equiv.Perm (Fin 4)) :
    permLinearEquiv σ ∈ Subgroup.closure originReflections := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
    have h : permLinearEquiv 1 = 1 := LinearEquiv.ext fun x => rfl
    rw [h]
    exact one_mem _
  | swap_mul f μ lam hne hf =>
    have h : permLinearEquiv (Equiv.swap μ lam * f) =
        permLinearEquiv f * permLinearEquiv (Equiv.swap μ lam) := LinearEquiv.ext fun x => rfl
    rw [h]
    exact mul_mem hf (permLinearEquiv_swap_mem_closure hne)
def signFlipHom : (Fin 4 → ℤˣ) →* (AmbientSpace ≃ₗ[ℝ] AmbientSpace) where
  toFun := signFlip
  map_one' := LinearEquiv.ext fun x => by
    funext μ
    change (((1 : Fin 4 → ℤˣ) μ : ℤ) : ℝ) * x μ = x μ
    simp
  map_mul' ε ε' := LinearEquiv.ext fun x => by
    funext μ
    change ((((ε * ε') μ : ℤˣ) : ℤ) : ℝ) * x μ = ((ε μ : ℤ) : ℝ) * (((ε' μ : ℤ) : ℝ) * x μ)
    simp [mul_assoc]
theorem mulSingle_mem_comap_signFlipHom (μ : Fin 4) (t : ℤˣ) :
    Pi.mulSingle μ t ∈ (Subgroup.closure originReflections).comap signFlipHom := by
  rcases Int.units_eq_one_or t with rfl | rfl
  · rw [Pi.mulSingle_one]
    exact one_mem _
  · refine Subgroup.subset_closure ⟨coordVec μ, Or.inl ⟨μ, rfl⟩, ?_⟩
    funext x
    rw [reflectAcross_coordVec_zero]
    funext κ
    change (((Pi.mulSingle μ (-1 : ℤˣ) : Fin 4 → ℤˣ) κ : ℤ) : ℝ) * x κ = _
    by_cases h : κ = μ
    · subst h
      simp
    · simp [Pi.mulSingle_eq_of_ne h, Function.update_of_ne h]
theorem signFlip_mem_closure (ε : Fin 4 → ℤˣ) :
    signFlip ε ∈ Subgroup.closure originReflections := by
  have h : ∏ μ, Pi.mulSingle μ (ε μ) ∈ (Subgroup.closure originReflections).comap signFlipHom :=
    Subgroup.prod_mem _ fun μ _ => mulSingle_mem_comap_signFlipHom μ (ε μ)
  rw [Finset.univ_prod_mulSingle] at h
  exact h
theorem hyperoctahedralLinearGroup_le_closure :
    hyperoctahedralLinearGroup ≤ Subgroup.closure originReflections := by
  intro w hw
  obtain ⟨σ, ε, h⟩ := (mem_hyperoctahedralLinearGroup_iff w).mp hw
  have hw' : w = signFlip ε * permLinearEquiv σ :=
    LinearEquiv.ext fun x => funext fun μ => h x μ
  rw [hw']
  exact mul_mem (signFlip_mem_closure ε) (permLinearEquiv_mem_closure σ)
theorem mem_hyperoctahedralLinearGroup_of_mem_originReflections
    {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace} (hw : w ∈ originReflections) :
    w ∈ hyperoctahedralLinearGroup := by
  obtain ⟨n, hn, hw⟩ := hw
  rw [mem_hyperoctahedralLinearGroup_iff]
  rcases hn with ⟨μ, rfl⟩ | ⟨μ, lam, hlt, rfl | rfl⟩
  · refine ⟨1, fun κ => if κ = μ then -1 else 1, fun x κ => ?_⟩
    rw [hw, reflectAcross_coordVec_zero]
    by_cases h : κ = μ
    · subst h
      simp
    · simp [h]
  · have hne : μ ≠ lam := hlt.ne
    refine ⟨Equiv.swap μ lam, fun κ => if κ = μ ∨ κ = lam then -1 else 1, fun x κ => ?_⟩
    rw [hw, reflectAcross_coordVec_add_zero hne]
    by_cases h : κ = lam
    · subst h
      simp
    · by_cases h' : κ = μ
      · subst h'
        simp [Function.update_of_ne h]
      · simp [h, h', Equiv.swap_apply_of_ne_of_ne h' h]
  · have hne : μ ≠ lam := hlt.ne
    refine ⟨Equiv.swap μ lam, 1, fun x κ => ?_⟩
    rw [hw, reflectAcross_coordVec_sub_zero hne]
    simp
theorem reflectAcross_zero_props_holds : reflectAcross_zero_props := by
  refine ⟨fun n _ => isLinearMap_reflectAcross_zero n, reflectAcross_coordVec_zero,
    fun μ lam hlt x => reflectAcross_coordVec_sub_zero hlt.ne x,
    fun μ lam hlt x => reflectAcross_coordVec_add_zero hlt.ne x,
    fun μ lam hlt => reflectAcross_coordVec_add_zero_eq_comp hlt.ne, ?_⟩
  refine le_antisymm ?_ hyperoctahedralLinearGroup_le_closure
  rw [Subgroup.closure_le]
  exact fun w hw => mem_hyperoctahedralLinearGroup_of_mem_originReflections hw
theorem statement_holds : Statement :=
  ⟨normalSet_counts_holds, reflectAcross_props_holds, levelPairs_eq_latticeMirrors_holds,
    reflectAcross_linearPart_holds, halfSpace_partition_holds, reflectAcross_zero_props_holds⟩
end YangMills.Construction.NormalFamilies.Properties
