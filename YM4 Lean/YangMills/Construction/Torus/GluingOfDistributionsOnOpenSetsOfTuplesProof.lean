import YangMills.Construction.Torus.FiniteSmoothPartitionsOfUnity
import YangMills.Construction.Torus.GluingOfDistributionsOnOpenSetsOfTuples
import YangMills.Construction.Torus.NormOfAProductAndMultiplesOfTensors
import YangMills.Construction.Torus.RestrictionsSumsProductsAndTensorsOfTestFunctions
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints.DistribGlue
variable {s : Conventions.StandingParameters} {E : Ambient} {p : ℕ}
theorem linearCombFacts_of_open (hR : TestFnOperations)
    (hp : 1 ≤ p) {W : Set (Tuple s E p)} (hW : IsOpen W) : LinearCombFacts W :=
  ((hR s E p hp).2.1 W hW).2.1
theorem smoothMulFacts_of_open (hR : TestFnOperations)
    (hp : 1 ≤ p) {W : Set (Tuple s E p)} (hW : IsOpen W) : SmoothMulFacts W :=
  ((hR s E p hp).2.1 W hW).2.2.2
theorem zero_mem_testFns (hP : SmoothPartitionOfUnityStatement)
    (hR : TestFnOperations) (hp : 1 ≤ p)
    {W : Set (Tuple s E p)} (hW : IsOpen W) : (0 : Tuple s E p → ℂ) ∈ testFns W := by
  obtain ⟨ψ, hψ, -⟩ := (hP s E p hp).2 ∅ W isCompact_empty hW (Set.empty_subset _)
  have h := (linearCombFacts_of_open hR hp hW ψ hψ ψ hψ 0 0).1
  simpa using h
theorem add_mem_testFns (hR : TestFnOperations) (hp : 1 ≤ p)
    {W : Set (Tuple s E p)} (hW : IsOpen W) {u v : Tuple s E p → ℂ}
    (hu : u ∈ testFns W) (hv : v ∈ testFns W) : u + v ∈ testFns W := by
  have h := (linearCombFacts_of_open hR hp hW u hu v hv 1 1).1
  simpa using h
theorem smul_mem_testFns (hR : TestFnOperations) (hp : 1 ≤ p)
    {W : Set (Tuple s E p)} (hW : IsOpen W) {u : Tuple s E p → ℂ} (c : ℂ)
    (hu : u ∈ testFns W) : c • u ∈ testFns W := by
  have h := (linearCombFacts_of_open hR hp hW u hu u hu c 0).1
  simpa using h
theorem mul_mem_testFns (hR : TestFnOperations) (hp : 1 ≤ p)
    {W : Set (Tuple s E p)} (hW : IsOpen W) {ψ u : Tuple s E p → ℂ}
    (hψ : ψ ∈ testFns W) (hu : IsSmoothFn u) : ψ * u ∈ testFns W :=
  (smoothMulFacts_of_open hR hp hW ψ u hψ.1 hu).2.2.1 (Or.inl hψ)
theorem mul_mem_testFns_inter (hR : TestFnOperations)
    (hp : 1 ≤ p) {W W' : Set (Tuple s E p)} (hW : IsOpen W) (hW' : IsOpen W')
    {ψ u : Tuple s E p → ℂ} (hψ : ψ ∈ testFns W') (hu : u ∈ testFns W) :
    ψ * u ∈ testFns (W ∩ W') :=
  (smoothMulFacts_of_open hR hp hW ψ u hψ.1 hu.1).2.2.2 W' hW' hu hψ
theorem cnNorm_mono {m m' : ℕ} (h : m ≤ m') (u : Tuple s E p → ℂ) :
    cnNorm m u ≤ cnNorm m' u :=
  iSup_mono fun _ => iSup_le fun hα => le_iSup_of_le (le_trans hα h) le_rfl
theorem isCn_of_isSmoothFn {u : Tuple s E p → ℂ} (hu : IsSmoothFn u) (m : ℕ) :
    IsCn (m : ℕ∞) u :=
  ⟨hu.1, fun n _ => hu.2 n le_top⟩
open Classical in
def extendByZero {W : Set (Tuple s E p)} (T : testFns W → ℂ) (v : Tuple s E p → ℂ) : ℂ :=
  if h : v ∈ testFns W then T ⟨v, h⟩ else 0
theorem extendByZero_of_mem {W : Set (Tuple s E p)} (T : testFns W → ℂ) {v : Tuple s E p → ℂ}
    (h : v ∈ testFns W) : _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero T v = T ⟨v, h⟩ :=
  dif_pos h
theorem extendByZero_add {W : Set (Tuple s E p)} {T : testFns W → ℂ} (hT : IsComplexLinearForm T)
    {u v : Tuple s E p → ℂ} (hu : u ∈ testFns W) (hv : v ∈ testFns W)
    (huv : u + v ∈ testFns W) : _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero T (u + v) = _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero T u + _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero T v := by
  rw [extendByZero_of_mem T huv, extendByZero_of_mem T hu, extendByZero_of_mem T hv]
  exact hT.1 ⟨u, hu⟩ ⟨v, hv⟩ ⟨u + v, huv⟩ rfl
theorem extendByZero_smul {W : Set (Tuple s E p)} {T : testFns W → ℂ} (hT : IsComplexLinearForm T)
    (c : ℂ) {u : Tuple s E p → ℂ} (hu : u ∈ testFns W) (hcu : c • u ∈ testFns W) :
    _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero T (c • u) = c * _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero T u := by
  rw [extendByZero_of_mem T hcu, extendByZero_of_mem T hu]
  exact hT.2 c ⟨u, hu⟩ ⟨c • u, hcu⟩ rfl
theorem sum_mem_and_extendByZero_sum (hP : SmoothPartitionOfUnityStatement)
    (hR : TestFnOperations) (hp : 1 ≤ p)
    {W : Set (Tuple s E p)} (hW : IsOpen W) {T : testFns W → ℂ} (hT : IsComplexLinearForm T)
    {ι : Type} (t : Finset ι) (v : ι → Tuple s E p → ℂ) (hv : ∀ i, v i ∈ testFns W) :
    ∑ i ∈ t, v i ∈ testFns W ∧ _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero T (∑ i ∈ t, v i) = ∑ i ∈ t, _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero T (v i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h0 := zero_mem_testFns (s := s) (E := E) hP hR hp hW
    refine ⟨by simpa using h0, ?_⟩
    simp only [Finset.sum_empty]
    rw [extendByZero_of_mem T h0]
    have h := hT.2 0 ⟨0, h0⟩ ⟨0, h0⟩ (by simp)
    simpa using h
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hm := add_mem_testFns hR hp hW (hv i) ih.1
    exact ⟨hm, by rw [extendByZero_add hT (hv i) ih.1 hm, ih.2]⟩
section Partitions
variable {Γ : Type} {O : Γ → Set (Tuple s E p)}
def IsLocalPartition (O : Γ → Set (Tuple s E p)) (K : Set (Tuple s E p)) {r : ℕ} (g : Fin r → Γ)
    (ψ : Fin r → Tuple s E p → ℂ) : Prop :=
  (∀ a, ψ a ∈ testFns (O (g a))) ∧
    ∃ N : Set (Tuple s E p), IsNhdOfSet N K ∧ ∀ y ∈ N, ∑ a, ψ a y = 1
theorem exists_isLocalPartition (hP : SmoothPartitionOfUnityStatement) (hp : 1 ≤ p)
    (O : Γ → Set (Tuple s E p)) (hO : ∀ γ, IsOpen (O γ)) {K : Set (Tuple s E p)}
    (hK : IsCompact K) (hKU : K ⊆ ⋃ γ, O γ) :
    ∃ (r : ℕ) (g : Fin r → Γ) (ψ : Fin r → Tuple s E p → ℂ), IsLocalPartition O K g ψ := by
  classical
  rcases isEmpty_or_nonempty Γ with hΓ | ⟨⟨γ₀⟩⟩
  · have hKe : K = ∅ := by
      rw [Set.iUnion_of_empty] at hKU
      exact Set.subset_empty_iff.1 hKU
    refine ⟨0, Fin.elim0, Fin.elim0, fun a => a.elim0, ∅, ⟨∅, isOpen_empty, ?_, subset_rfl⟩,
      by simp⟩
    simp [hKe]
  · obtain ⟨t, ht⟩ := hK.elim_finite_subcover O hO hKU
    have hr : 1 ≤ (insert γ₀ t).card := Finset.card_pos.2 ⟨γ₀, Finset.mem_insert_self _ _⟩
    let e := (insert γ₀ t).equivFin
    have hcov : K ⊆ ⋃ a, O (e.symm a).1 := by
      intro y hy
      obtain ⟨γ, hγ, hyγ⟩ : ∃ γ ∈ t, y ∈ O γ := by simpa using ht hy
      have hm : γ ∈ insert γ₀ t := Finset.mem_insert_of_mem hγ
      refine Set.mem_iUnion.2 ⟨e ⟨γ, hm⟩, ?_⟩
      simpa using hyγ
    obtain ⟨ψ, h1, -, N, hN, hsum⟩ := (hP s E p hp).1 _ hr K (fun a => O (e.symm a).1) hK
      (fun a => hO _) hcov
    exact ⟨_, fun a => (e.symm a).1, ψ, h1, N, hN, hsum⟩
theorem sum_mul_eq_self {K : Set (Tuple s E p)} {r : ℕ} {ψ : Fin r → Tuple s E p → ℂ}
    (hN : ∃ N : Set (Tuple s E p), IsNhdOfSet N K ∧ ∀ y ∈ N, ∑ a, ψ a y = 1)
    {u : Tuple s E p → ℂ} (hu : closedSupport u ⊆ K) : ∑ a, ψ a * u = u := by
  obtain ⟨N, ⟨U, -, hKU, hUN⟩, h1⟩ := hN
  funext y
  simp only [Finset.sum_apply, Pi.mul_apply]
  by_cases hy : u y = 0
  · simp [hy]
  · have hy' : y ∈ closedSupport u := subset_closure (show y ∈ {y | u y ≠ 0} from hy)
    rw [← Finset.sum_mul, h1 y (hUN (hKU (hu hy'))), one_mul]
def patchedValue (T : ∀ γ, testFns (O γ) → ℂ) {r : ℕ} (g : Fin r → Γ)
    (ψ : Fin r → Tuple s E p → ℂ) (u : Tuple s E p → ℂ) : ℂ :=
  ∑ a, _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero (T (g a)) (ψ a * u)
theorem patchedValue_eq (hP : SmoothPartitionOfUnityStatement)
    (hR : TestFnOperations) (hp : 1 ≤ p)
    (hO : ∀ γ, IsOpen (O γ)) {T : ∀ γ, testFns (O γ) → ℂ}
    (hT : ∀ γ, IsComplexLinearForm (T γ))
    (hOv : ∀ (γ γ' : Γ) (v : testFns (O γ ∩ O γ')),
      restrictDistrib Set.inter_subset_left (T γ) v =
        restrictDistrib Set.inter_subset_right (T γ') v)
    {K K' : Set (Tuple s E p)} {r r' : ℕ} {g : Fin r → Γ} {g' : Fin r' → Γ}
    {ψ : Fin r → Tuple s E p → ℂ} {ψ' : Fin r' → Tuple s E p → ℂ}
    (hd : IsLocalPartition O K g ψ) (hd' : IsLocalPartition O K' g' ψ')
    {u : Tuple s E p → ℂ} (hu : IsSmoothFn u) (huK : closedSupport u ⊆ K)
    (huK' : closedSupport u ⊆ K') :
    patchedValue T g ψ u = patchedValue T g' ψ' u := by
  have hm0 : ∀ b, ψ' b * u ∈ testFns (O (g' b)) := fun b =>
    mul_mem_testFns hR hp (hO _) (hd'.1 b) hu
  have hm2 : ∀ a b, ψ a * (ψ' b * u) ∈ testFns (O (g' b) ∩ O (g a)) := fun a b =>
    mul_mem_testFns_inter hR hp (hO _) (hO _) (hd.1 a) (hm0 b)
  have hm1 : ∀ a b, ψ a * (ψ' b * u) ∈ testFns (O (g a)) := fun a b =>
    testFns_mono Set.inter_subset_right (hm2 a b)
  have hm3 : ∀ a b, ψ a * (ψ' b * u) ∈ testFns (O (g' b)) := fun a b =>
    testFns_mono Set.inter_subset_left (hm2 a b)
  have e1 : ∀ a, _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero (T (g a)) (ψ a * u) =
      ∑ b, _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero (T (g a)) (ψ a * (ψ' b * u)) := by
    intro a
    have h : ψ a * u = ∑ b, ψ a * (ψ' b * u) := by
      rw [← Finset.mul_sum, sum_mul_eq_self hd'.2 huK']
    rw [h]
    exact (sum_mem_and_extendByZero_sum hP hR hp (hO _) (hT _) Finset.univ _ (hm1 a)).2
  have e2 : ∀ b, _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero (T (g' b)) (ψ' b * u) =
      ∑ a, _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero (T (g' b)) (ψ a * (ψ' b * u)) := by
    intro b
    have hs : closedSupport (ψ' b * u) ⊆ K :=
      ((smoothMulFacts_of_open hR hp (hO (g' b)) (ψ' b) u (hd'.1 b).1 hu).2.1.trans
        Set.inter_subset_right).trans huK
    have h : ψ' b * u = ∑ a, ψ a * (ψ' b * u) := (sum_mul_eq_self hd.2 hs).symm
    conv_lhs => rw [h]
    exact (sum_mem_and_extendByZero_sum hP hR hp (hO _) (hT _) Finset.univ _
      fun a => hm3 a b).2
  have e3 : ∀ a b, _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero (T (g a)) (ψ a * (ψ' b * u)) =
      _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero (T (g' b)) (ψ a * (ψ' b * u)) := by
    intro a b
    rw [extendByZero_of_mem _ (hm1 a b), extendByZero_of_mem _ (hm3 a b)]
    exact (hOv (g' b) (g a) ⟨_, hm2 a b⟩).symm
  calc patchedValue T g ψ u
      = ∑ a, ∑ b, _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero (T (g a)) (ψ a * (ψ' b * u)) :=
        Finset.sum_congr rfl fun a _ => e1 a
    _ = ∑ a, ∑ b, _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero (T (g' b)) (ψ a * (ψ' b * u)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => e3 a b
    _ = ∑ b, ∑ a, _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero (T (g' b)) (ψ a * (ψ' b * u)) := Finset.sum_comm
    _ = patchedValue T g' ψ' u := Finset.sum_congr rfl fun b _ => (e2 b).symm
theorem patchedValue_add (hR : TestFnOperations)
    (hp : 1 ≤ p) (hO : ∀ γ, IsOpen (O γ)) {T : ∀ γ, testFns (O γ) → ℂ}
    (hT : ∀ γ, IsComplexLinearForm (T γ)) {r : ℕ} {g : Fin r → Γ} {ψ : Fin r → Tuple s E p → ℂ}
    (hψ : ∀ a, ψ a ∈ testFns (O (g a))) {u v : Tuple s E p → ℂ}
    (hu : IsSmoothFn u) (hv : IsSmoothFn v) :
    patchedValue T g ψ (u + v) = patchedValue T g ψ u + patchedValue T g ψ v := by
  unfold patchedValue
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h1 := mul_mem_testFns hR hp (hO _) (hψ a) hu
  have h2 := mul_mem_testFns hR hp (hO _) (hψ a) hv
  rw [mul_add]
  exact extendByZero_add (hT _) h1 h2 (add_mem_testFns hR hp (hO _) h1 h2)
theorem patchedValue_smul (hR : TestFnOperations)
    (hp : 1 ≤ p) (hO : ∀ γ, IsOpen (O γ)) {T : ∀ γ, testFns (O γ) → ℂ}
    (hT : ∀ γ, IsComplexLinearForm (T γ)) {r : ℕ} {g : Fin r → Γ} {ψ : Fin r → Tuple s E p → ℂ}
    (hψ : ∀ a, ψ a ∈ testFns (O (g a))) (c : ℂ) {u : Tuple s E p → ℂ}
    (hu : IsSmoothFn u) : patchedValue T g ψ (c • u) = c * patchedValue T g ψ u := by
  unfold patchedValue
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h1 := mul_mem_testFns hR hp (hO _) (hψ a) hu
  have h2 : ψ a * c • u = c • (ψ a * u) := by
    funext y
    simp [mul_left_comm]
  rw [h2]
  exact extendByZero_smul (hT _) c h1 (smul_mem_testFns hR hp (hO _) c h1)
theorem orderBoundsOn_of_patchedValue
    (hR : TestFnOperations)
    (hL : ProductNorms.ProductBoundsClaim) (hp : 1 ≤ p)
    (hO : ∀ γ, IsOpen (O γ)) {T : ∀ γ, testFns (O γ) → ℂ} {r : ℕ} {g : Fin r → Γ}
    {ψ : Fin r → Tuple s E p → ℂ} (hψ : ∀ a, ψ a ∈ testFns (O (g a)))
    {m : ℕ} (ms : Fin r → ℕ) (hm : ∀ a, ms a ≤ m)
    (hs : ∀ a, OrderBoundsOn (T (g a)) (closedSupport (ψ a)) (ms a))
    {Ω K : Set (Tuple s E p)} (hΩ : IsOpen Ω) (S : testFns Ω → ℂ)
    (hS : ∀ u : testFns Ω, closedSupport u.1 ⊆ K → S u = patchedValue T g ψ u.1) :
    OrderBoundsOn S K m := by
  choose C hC using hs
  have hfin : ∀ a, cnNorm (ms a) (ψ a) < ⊤ := fun a =>
    (((hR s E p hp).2.1 (O (g a)) (hO _)).2.2.1 (ψ a) (hψ a)).2.2.2 (ms a)
  let c : Fin r → ℝ≥0 := fun a => C a * 2 ^ ms a * (cnNorm (ms a) (ψ a)).toNNReal
  refine ⟨∑ a, c a, fun u huK => ?_⟩
  rw [hS u huK]
  have key : ∀ a, ENNReal.ofReal ‖_root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero (T (g a)) (ψ a * u.1)‖ ≤
      (c a : ℝ≥0∞) * cnNorm m u.1 := by
    intro a
    have hmem := mul_mem_testFns hR hp (hO _) (hψ a) u.2.1
    have hsupp : closedSupport (ψ a * u.1) ⊆ closedSupport (ψ a) :=
      (smoothMulFacts_of_open hR hp (hO (g a)) (ψ a) u.1 (hψ a).1 u.2.1).2.1.trans
        Set.inter_subset_left
    rw [extendByZero_of_mem _ hmem]
    have h1 := hC a ⟨_, hmem⟩ hsupp
    have hufin : cnNorm (ms a) u.1 < ⊤ :=
      (((hR s E p hp).2.1 Ω hΩ).2.2.1 u.1 u.2).2.2.2 (ms a)
    have h2 : cnNorm (ms a) (ψ a * u.1) ≤
        2 ^ ms a * cnNorm (ms a) (ψ a) * cnNorm (ms a) u.1 :=
      ((hL s E p hp (ms a)).1 (ψ a) u.1 (isCn_of_isSmoothFn (hψ a).1 _)
        (isCn_of_isSmoothFn u.2.1 _) (hfin a) hufin).2
    have h3 := cnNorm_mono (hm a) u.1
    calc ENNReal.ofReal ‖T (g a) ⟨ψ a * u.1, hmem⟩‖
        ≤ (C a : ℝ≥0∞) * cnNorm (ms a) (ψ a * u.1) := h1
      _ ≤ (C a : ℝ≥0∞) * (2 ^ ms a * cnNorm (ms a) (ψ a) * cnNorm m u.1) := by
          gcongr
          exact h2.trans (by gcongr)
      _ = (c a : ℝ≥0∞) * cnNorm m u.1 := by
          simp only [c, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat,
            ENNReal.coe_toNNReal (hfin a).ne]
          ring
  calc ENNReal.ofReal ‖patchedValue T g ψ u.1‖
      ≤ ∑ a, ENNReal.ofReal ‖_root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero (T (g a)) (ψ a * u.1)‖ := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _]
        exact ENNReal.ofReal_le_ofReal (norm_sum_le _ _)
    _ ≤ ∑ a, (c a : ℝ≥0∞) * cnNorm m u.1 := Finset.sum_le_sum fun a _ => key a
    _ = ((∑ a, c a : ℝ≥0) : ℝ≥0∞) * cnNorm m u.1 := by
        rw [ENNReal.ofNNReal_finsetSum, Finset.sum_mul]
end Partitions
theorem distributionsGlueUniquely_holds (hP : SmoothPartitionOfUnityStatement)
    (hR : TestFnOperations)
    (hL : ProductNorms.ProductBoundsClaim) : DistributionsGlueUniquely := by
  intro s E p hp Ω hΩ Γ O hO hU T hT hOv
  subst hU
  have hlin : ∀ γ, IsComplexLinearForm (T γ) := fun γ => (hT γ).1
  have hex : ∀ u : testFns (⋃ γ, O γ), ∃ (r : ℕ) (g : Fin r → Γ)
      (ψ : Fin r → Tuple s E p → ℂ), IsLocalPartition O (closedSupport u.1) g ψ := fun u =>
    exists_isLocalPartition hP hp O hO u.2.2.1 u.2.2.2
  choose r g ψ hd using hex
  obtain ⟨S, hSdef⟩ : ∃ S : testFns (⋃ γ, O γ) → ℂ,
      ∀ u, S u = patchedValue T (g u) (ψ u) u.1 := ⟨_, fun _ => rfl⟩
  have hS : ∀ {r' : ℕ} (g' : Fin r' → Γ) (ψ' : Fin r' → Tuple s E p → ℂ)
      (K : Set (Tuple s E p)), IsLocalPartition O K g' ψ' →
      ∀ u : testFns (⋃ γ, O γ), closedSupport u.1 ⊆ K → S u = patchedValue T g' ψ' u.1 :=
    fun g' ψ' K hd' u hu => (hSdef u).trans
      (patchedValue_eq hP hR hp hO hlin hOv (hd u) hd' u.2.1 subset_rfl hu)
  have hSlin : IsComplexLinearForm S := by
    refine ⟨fun u v w hw => ?_, fun c u w hw => ?_⟩
    · obtain ⟨r', g', ψ', hd'⟩ := exists_isLocalPartition hP hp O hO
        (u.2.2.1.union v.2.2.1) (Set.union_subset u.2.2.2 v.2.2.2)
      have hsupp : closedSupport w.1 ⊆ closedSupport u.1 ∪ closedSupport v.1 := by
        have h := (linearCombFacts_of_open hR hp hΩ u.1 u.2 v.1 v.2 1 1).2
        rw [hw]
        simpa using h
      rw [hS g' ψ' _ hd' w hsupp, hS g' ψ' _ hd' u Set.subset_union_left,
        hS g' ψ' _ hd' v Set.subset_union_right, hw]
      exact patchedValue_add hR hp hO hlin hd'.1 u.2.1 v.2.1
    · obtain ⟨r', g', ψ', hd'⟩ := exists_isLocalPartition hP hp O hO u.2.2.1 u.2.2.2
      have hsupp : closedSupport w.1 ⊆ closedSupport u.1 := by
        have h := (linearCombFacts_of_open hR hp hΩ u.1 u.2 u.1 u.2 c 0).2
        rw [hw]
        simpa using h
      rw [hS g' ψ' _ hd' w hsupp, hS g' ψ' _ hd' u subset_rfl, hw]
      exact patchedValue_smul hR hp hO hlin hd'.1 c u.2.1
  have hSdist : IsDistrib S := by
    refine ⟨hSlin, fun K hK hKΩ => ?_⟩
    obtain ⟨r', g', ψ', hd'⟩ := exists_isLocalPartition hP hp O hO hK hKΩ
    have hm : ∀ a, ∃ m, OrderBoundsOn (T (g' a)) (closedSupport (ψ' a)) m := fun a =>
      (hT (g' a)).2 _ (hd'.1 a).2.1 (hd'.1 a).2.2
    choose ms hms using hm
    exact ⟨Finset.univ.sup ms, orderBoundsOn_of_patchedValue hR hL hp hO hd'.1 ms
      (fun a => Finset.le_sup (Finset.mem_univ a)) hms hΩ S (fun u hu => hS g' ψ' K hd' u hu)⟩
  have hSres : ∀ γ, restrictDistrib (Set.subset_iUnion O γ) S = T γ := by
    intro γ
    funext u
    have huΩ : u.1 ∈ testFns (⋃ γ, O γ) := testFns_mono (Set.subset_iUnion O γ) u.2
    obtain ⟨r', g', ψ', hd'⟩ := exists_isLocalPartition hP hp O hO u.2.2.1
      (u.2.2.2.trans (Set.subset_iUnion O γ))
    have hm : ∀ a, ψ' a * u.1 ∈ testFns (O γ ∩ O (g' a)) := fun a =>
      mul_mem_testFns_inter hR hp (hO _) (hO _) (hd'.1 a) u.2
    have hm1 : ∀ a, ψ' a * u.1 ∈ testFns (O γ) := fun a =>
      testFns_mono Set.inter_subset_left (hm a)
    have hm2 : ∀ a, ψ' a * u.1 ∈ testFns (O (g' a)) := fun a =>
      testFns_mono Set.inter_subset_right (hm a)
    calc restrictDistrib (Set.subset_iUnion O γ) S u
        = patchedValue T g' ψ' u.1 := hS g' ψ' _ hd' ⟨u.1, huΩ⟩ subset_rfl
      _ = ∑ a, _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero (T γ) (ψ' a * u.1) := Finset.sum_congr rfl fun a _ => by
          rw [extendByZero_of_mem _ (hm2 a), extendByZero_of_mem _ (hm1 a)]
          exact (hOv γ (g' a) ⟨_, hm a⟩).symm
      _ = _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero (T γ) (∑ a, ψ' a * u.1) :=
          (sum_mem_and_extendByZero_sum hP hR hp (hO _) (hlin _) Finset.univ _ hm1).2.symm
      _ = _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero (T γ) u.1 := by rw [sum_mul_eq_self hd'.2 subset_rfl]
      _ = T γ u := extendByZero_of_mem _ u.2
  have huniq : ∀ S' : testFns (⋃ γ, O γ) → ℂ, IsDistrib S' →
      (∀ γ, restrictDistrib (Set.subset_iUnion O γ) S' = T γ) → S' = S := by
    intro S' hS' hres
    funext u
    obtain ⟨r', g', ψ', hd'⟩ := exists_isLocalPartition hP hp O hO u.2.2.1 u.2.2.2
    have hm : ∀ a, ψ' a * u.1 ∈ testFns (O (g' a)) := fun a =>
      mul_mem_testFns hR hp (hO _) (hd'.1 a) u.2.1
    have hmΩ : ∀ a, ψ' a * u.1 ∈ testFns (⋃ γ, O γ) := fun a =>
      testFns_mono (Set.subset_iUnion O (g' a)) (hm a)
    calc S' u = _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero S' u.1 := (extendByZero_of_mem _ u.2).symm
      _ = _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero S' (∑ a, ψ' a * u.1) := by rw [sum_mul_eq_self hd'.2 subset_rfl]
      _ = ∑ a, _root_.YangMills.Construction.AmbientPoints.DistribGlue.extendByZero S' (ψ' a * u.1) :=
          (sum_mem_and_extendByZero_sum hP hR hp hΩ hS'.1 Finset.univ _ hmΩ).2
      _ = patchedValue T g' ψ' u.1 := Finset.sum_congr rfl fun a _ => by
          rw [extendByZero_of_mem _ (hmΩ a), extendByZero_of_mem _ (hm a), ← hres (g' a)]
          rfl
      _ = S u := (hS g' ψ' _ hd' u subset_rfl).symm
  refine ⟨ExistsUnique.intro S ⟨hSdist, hSres⟩ fun S' h => huniq S' h.1 h.2, ?_⟩
  intro m₀ hm₀ S' hS' hres
  rw [huniq S' hS' hres]
  refine ⟨hSdist, fun K hK hKΩ => ?_⟩
  obtain ⟨r', g', ψ', hd'⟩ := exists_isLocalPartition hP hp O hO hK hKΩ
  exact orderBoundsOn_of_patchedValue hR hL hp hO hd'.1 (fun _ => m₀) (fun _ => le_rfl)
    (fun a => (hm₀ (g' a)).2 _ (hd'.1 a).2.1 (hd'.1 a).2.2) hΩ S
    (fun u hu => hS g' ψ' K hd' u hu)
end YangMills.Construction.AmbientPoints.DistribGlue
end
