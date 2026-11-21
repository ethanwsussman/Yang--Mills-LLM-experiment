import YangMills.Construction.Lattice.BareBaseSitesOfTheSchemesProof
import YangMills.Construction.Lattice.LengthsOfThePathsOfADoubleBlock
import YangMills.Construction.Towers.BlocksOfATower
import YangMills.Construction.Towers.IterateOfTheAveragingMapsNearTheTrivialConfigurationProof
import YangMills.Construction.Towers.RelationAndBoundsOfTheIteratesOfTheLinearMaps
import YangMills.Construction.Towers.RelationsOfTheLinearMapsOfAStep
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.IterateBounds
theorem ofReal_norm_le_maxOperatorNorm {ι : Type*} (f : ι → Matrices.ComplexMatrix2) (i : ι) :
    ENNReal.ofReal ‖f i‖ ≤ maxOperatorNorm f :=
  le_iSup (fun i => ENNReal.ofReal (Matrices.ComplexMatrix2.operatorNorm (f i))) i
theorem ofReal_norm_add_le_add (X Y : Matrices.ComplexMatrix2) :
    ENNReal.ofReal ‖X + Y‖ ≤ ENNReal.ofReal ‖X‖ + ENNReal.ofReal ‖Y‖ :=
  (ENNReal.ofReal_le_ofReal (norm_add_le X Y)).trans ENNReal.ofReal_add_le
theorem ofReal_norm_sub_le_add (X Y : Matrices.ComplexMatrix2) :
    ENNReal.ofReal ‖X - Y‖ ≤ ENNReal.ofReal ‖X‖ + ENNReal.ofReal ‖Y‖ :=
  (ENNReal.ofReal_le_ofReal (norm_sub_le X Y)).trans ENNReal.ofReal_add_le
theorem ofReal_norm_finset_sum_le {ι : Type*} (s : Finset ι) (f : ι → Matrices.ComplexMatrix2) :
    ENNReal.ofReal ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ENNReal.ofReal ‖f i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (ofReal_norm_add_le_add _ _).trans (add_le_add le_rfl ih)
theorem ofReal_norm_smul_sum_le_of_card {ι : Type*} (s : Finset ι) (w : ℝ) (hw : 0 ≤ w)
    (hwc : w * s.card ≤ 1) (f : ι → Matrices.ComplexMatrix2) (C : ℝ≥0∞)
    (h : ∀ i ∈ s, ENNReal.ofReal ‖f i‖ ≤ C) :
    ENNReal.ofReal ‖(w : ℂ) • ∑ i ∈ s, f i‖ ≤ C := by
  by_cases hC : C = ⊤
  · simp [hC]
  have hc : ∀ i ∈ s, ‖f i‖ ≤ C.toReal := fun i hi =>
    (ENNReal.ofReal_le_iff_le_toReal hC).1 (h i hi)
  rw [ENNReal.ofReal_le_iff_le_toReal hC, norm_smul]
  have hsum : ‖∑ i ∈ s, f i‖ ≤ s.card * C.toReal := by
    calc ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ s, C.toReal := Finset.sum_le_sum hc
      _ = s.card * C.toReal := by simp
  have hwn : ‖(w : ℂ)‖ = w := by simp [abs_of_nonneg hw]
  rw [hwn]
  calc w * ‖∑ i ∈ s, f i‖ ≤ w * (s.card * C.toReal) := mul_le_mul_of_nonneg_left hsum hw
    _ = (w * s.card) * C.toReal := by ring
    _ ≤ 1 * C.toReal := mul_le_mul_of_nonneg_right hwc ENNReal.toReal_nonneg
    _ = C.toReal := one_mul _
theorem ofReal_norm_list_sum_le_length_mul {β : Type*} (A : β → Matrices.ComplexMatrix2)
    (Γ : List β) :
    ENNReal.ofReal ‖(Γ.map A).sum‖ ≤ (Γ.length : ℝ≥0∞) * maxOperatorNorm A := by
  induction Γ with
  | nil => simp
  | cons b Γ ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    calc ENNReal.ofReal ‖A b + (Γ.map A).sum‖
        ≤ ENNReal.ofReal ‖A b‖ + ENNReal.ofReal ‖(Γ.map A).sum‖ := ofReal_norm_add_le_add _ _
      _ ≤ maxOperatorNorm A + (Γ.length : ℝ≥0∞) * maxOperatorNorm A :=
          add_le_add (ofReal_norm_le_maxOperatorNorm A b) ih
      _ = ((Γ.length + 1 : ℕ) : ℝ≥0∞) * maxOperatorNorm A := by push_cast; ring
theorem ofReal_norm_weight_smul_finsum_le {L : ℕ} (hL : 0 < L) {ι : Type*} {S : Set ι}
    (hS : S.Finite) (hc : S.ncard ≤ L ^ 4) (f : ι → Matrices.ComplexMatrix2) (C : ℝ≥0∞)
    (h : ∀ x ∈ S, ENNReal.ofReal ‖f x‖ ≤ C) :
    ENNReal.ofReal ‖PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ S, f x‖ ≤ C := by
  rw [finsum_mem_eq_finite_toFinset_sum f hS]
  have hw : (L : ℝ) ^ (-4 : ℤ) = ((L : ℝ) ^ 4)⁻¹ := by rw [zpow_neg]; norm_cast
  refine ofReal_norm_smul_sum_le_of_card hS.toFinset ((L : ℝ) ^ (-4 : ℤ)) (by positivity) ?_ f C
    fun i hi => h i (hS.mem_toFinset.1 hi)
  have hcard : (hS.toFinset.card : ℝ) ≤ (L : ℝ) ^ 4 := by
    rw [← Set.ncard_eq_toFinset_card S hS]
    exact_mod_cast hc
  rw [hw]
  calc ((L : ℝ) ^ 4)⁻¹ * hS.toFinset.card ≤ ((L : ℝ) ^ 4)⁻¹ * (L : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = 1 := inv_mul_cancel₀ (by positivity)
theorem ofReal_smul_mem_hermitianTraceless (w : ℝ) {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    (w : ℂ) • X ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
  have h : (w : ℂ) • X = w • X := by
    ext i j
    simp
  rw [h]
  exact Matrices.ComplexMatrix2.hermitianTraceless.smul_mem w hX
theorem list_map_sum_mem_hermitianTraceless {β : Type*} (A : β → Matrices.ComplexMatrix2)
    (h : ∀ b, A b ∈ Matrices.ComplexMatrix2.hermitianTraceless) (Γ : List β) :
    (Γ.map A).sum ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
  induction Γ with
  | nil => simp
  | cons b Γ ih => simpa using Matrices.ComplexMatrix2.hermitianTraceless.add_mem (h b) ih
theorem weight_smul_finsum_mem_hermitianTraceless (L : ℕ) {ι : Type*} {S : Set ι}
    (hS : S.Finite) (f : ι → Matrices.ComplexMatrix2)
    (h : ∀ x ∈ S, f x ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ S, f x ∈
      Matrices.ComplexMatrix2.hermitianTraceless := by
  refine ofReal_smul_mem_hermitianTraceless ((L : ℝ) ^ (-4 : ℤ)) ?_
  rw [finsum_mem_eq_finite_toFinset_sum f hS]
  exact Matrices.ComplexMatrix2.hermitianTraceless.sum_mem fun i hi => h i (hS.mem_toFinset.1 hi)
section Levels
variable {L n k : ℕ}
theorem apply_mem_hermitianTraceless {j : ℕ} {B : Edge L n k j → Matrices.ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) (b : Edge L n k j) :
    B b ∈ Matrices.ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.SmoothingIterProof.edgeForm_apply_mem <;> assumption
theorem mem_vertexFunctionSpace_of_forall {j : ℕ} {l : Vertex L n k j → Matrices.ComplexMatrix2}
    (h : ∀ x, l x ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    l ∈ vertexFunctionSpace L n k j :=
  Submodule.mem_pi.2 fun x _ => h x
theorem sitesInBlock_finite_and_ncard_le (hBlk : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    (y : Vertex L n k (j + 1)) :
    (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).Finite ∧
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).ncard ≤ L ^ 4 := by
  obtain ⟨-, -, hcard, -⟩ := ((hBlk L k (j + 1) hL (by omega) (by omega) (by omega)).1 n hn).1 y
  have hpos : 0 < L := by have := hL.2; omega
  have hfin : (PeriodicLattice.unitBlock y).Finite :=
    Set.finite_of_ncard_pos (by rw [hcard]; positivity)
  have hsub : Subtype.val '' (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) ⊆
      PeriodicLattice.unitBlock y := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hfinS : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).Finite :=
    Set.Finite.of_finite_image (hfin.subset hsub) Subtype.val_injective.injOn
  refine ⟨hfinS, ?_⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, ← hcard]
  exact Set.ncard_le_ncard hsub hfin
theorem crossingSmoothing_mem (hRev : AxisPathReversal.MainStatement)
    (hBlk : BlockStructure) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ}
    (hj : j < k) {B : Edge L n k j → Matrices.ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j) :
    crossingSmoothing L n k j B ∈ edgeFormSpace L n k (j + 1) := by
  refine ⟨fun c _ => ?_, fun c => ?_⟩
  · exact weight_smul_finsum_mem_hermitianTraceless L
      (sitesInBlock_finite_and_ncard_le hBlk hL hn hj c.source).1 _
      fun x _ => list_map_sum_mem_hermitianTraceless B (apply_mem_hermitianTraceless hB) _
  · have h1 := (((hRev L hL k).1 n hn).1 j hj.le).1 B hB
    have h2 := (((hRev L hL k).1 n hn).2 j hj c B h1).1
    simp only [crossingSmoothing]
    rw [h2, smul_neg]
theorem ofReal_norm_crossingSmoothing_le (hLen : PeriodicLattice.DoubleBlockPathLengths)
    (hBlk : BlockStructure) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ}
    (hj : j < k) (B : Edge L n k j → Matrices.ComplexMatrix2) (c : Edge L n k (j + 1)) :
    ENNReal.ofReal ‖crossingSmoothing L n k j B c‖ ≤ (L : ℝ≥0∞) * maxOperatorNorm B := by
  obtain ⟨hfin, hcard⟩ := sitesInBlock_finite_and_ncard_le hBlk hL hn hj c.source
  have hpos : 0 < L := by have := hL.2; omega
  refine ofReal_norm_weight_smul_finsum_le hpos hfin hcard _ _ fun x hx => ?_
  have hlen := (hLen L n k j hL hn hj).crossing c x hx
  have h := ofReal_norm_list_sum_le_length_mul B (PeriodicLattice.crossingPath c x)
  rw [hlen] at h
  exact h
theorem ofReal_norm_contourFormAverage_le (hLen : PeriodicLattice.DoubleBlockPathLengths)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    (B : Edge L n k j → Matrices.ComplexMatrix2) (y : Vertex L n k (j + 1)) (x : Vertex L n k j)
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) :
    ENNReal.ofReal ‖PeriodicLattice.contourFormAverage B y x‖ ≤
      2 * ((L : ℝ≥0∞) - 1) * maxOperatorNorm B := by
  refine ofReal_norm_smul_sum_le_of_card Finset.univ _ (by positivity) ?_ _ _ fun σ _ => ?_
  · rw [Finset.card_univ]
    exact inv_mul_le_one
  · have h := ofReal_norm_list_sum_le_length_mul B (PeriodicLattice.orderedContour y x σ)
    refine h.trans ?_
    have hlen := (hLen L n k j hL hn hj).contour y x hx σ
    have hc : ((PeriodicLattice.orderedContour y x σ).length : ℝ≥0∞) ≤ 2 * ((L : ℝ≥0∞) - 1) := by
      calc ((PeriodicLattice.orderedContour y x σ).length : ℝ≥0∞)
          ≤ ((2 * (L - 1) : ℕ) : ℝ≥0∞) := by
            exact_mod_cast hlen
        _ = 2 * ((L : ℝ≥0∞) - 1) := by
            rw [Nat.cast_mul, ENNReal.natCast_sub]
            simp
    gcongr
theorem ofReal_norm_cubeContourAverage_le (hLen : PeriodicLattice.DoubleBlockPathLengths)
    (hBlk : BlockStructure) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ}
    (hj : j < k) (B : Edge L n k j → Matrices.ComplexMatrix2) (y : Vertex L n k (j + 1)) :
    ENNReal.ofReal ‖cubeContourAverage L n k j B y‖ ≤
      2 * ((L : ℝ≥0∞) - 1) * maxOperatorNorm B := by
  obtain ⟨hfin, hcard⟩ := sitesInBlock_finite_and_ncard_le hBlk hL hn hj y
  have hpos : 0 < L := by have := hL.2; omega
  exact ofReal_norm_weight_smul_finsum_le hpos hfin hcard _ _ fun x hx =>
    ofReal_norm_contourFormAverage_le hLen hL hn hj B y x hx
theorem cubeContourAverage_mem (hBlk : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    {B : Edge L n k j → Matrices.ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j)
    (y : Vertex L n k (j + 1)) :
    cubeContourAverage L n k j B y ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
  refine weight_smul_finsum_mem_hermitianTraceless L
    (sitesInBlock_finite_and_ncard_le hBlk hL hn hj y).1 _ fun x _ => ?_
  refine ofReal_smul_mem_hermitianTraceless _
    (Matrices.ComplexMatrix2.hermitianTraceless.sum_mem fun σ _ => ?_)
  exact list_map_sum_mem_hermitianTraceless B (apply_mem_hermitianTraceless hB) _
theorem bondFormSumAlong_sub {j : ℕ} (A A' : Edge L n k j → Matrices.ComplexMatrix2)
    (Γ : List (Edge L n k j)) :
    PeriodicLattice.bondFormSumAlong (A - A') Γ =
      PeriodicLattice.bondFormSumAlong A Γ - PeriodicLattice.bondFormSumAlong A' Γ := by
  induction Γ with
  | nil => simp [PeriodicLattice.bondFormSumAlong]
  | cons b Γ ih =>
    simp only [PeriodicLattice.bondFormSumAlong, List.map_cons, List.sum_cons,
      Pi.sub_apply] at ih ⊢
    rw [ih]
    abel
theorem contourFormAverage_sub {i j : ℕ} (A A' : Edge L n k j → Matrices.ComplexMatrix2)
    (y : Vertex L n k i) (x : Vertex L n k j) :
    PeriodicLattice.contourFormAverage (A - A') y x =
      PeriodicLattice.contourFormAverage A y x - PeriodicLattice.contourFormAverage A' y x := by
  simp only [PeriodicLattice.contourFormAverage, bondFormSumAlong_sub, Finset.sum_sub_distrib,
    smul_sub]
theorem linearSmoothing_sub (hBlk : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    (A A' : Edge L n k j → Matrices.ComplexMatrix2) :
    linearSmoothing L n k j (A - A') = linearSmoothing L n k j A - linearSmoothing L n k j A' := by
  funext c
  obtain ⟨hfin, -⟩ := sitesInBlock_finite_and_ncard_le hBlk hL hn hj c.source
  show PeriodicLattice.inverseFourthPowerWeight L • PeriodicLattice.linearBlockSum (A - A') c =
    PeriodicLattice.inverseFourthPowerWeight L • PeriodicLattice.linearBlockSum A c -
      PeriodicLattice.inverseFourthPowerWeight L • PeriodicLattice.linearBlockSum A' c
  rw [← smul_sub]
  congr 1
  unfold PeriodicLattice.linearBlockSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [contourFormAverage_sub, contourFormAverage_sub, bondFormSumAlong_sub]
  abel
theorem coe_toSublattice (hL : 0 < L) {i i' : ℤ} (hi : i ≤ i') (y : PeriodicLattice.Site L n i) :
    ((PeriodicLattice.Site.toSublattice y i' : PeriodicLattice.Site L n i') :
      PeriodicLattice.FourTorus L n) = y := by apply _root_.YangMills.SharedProofs.p9023 <;> assumption
theorem toSublattice_self (hL : 0 < L) {i : ℤ} (y : PeriodicLattice.Site L n i) :
    PeriodicLattice.Site.toSublattice y i = y :=
  Subtype.ext (coe_toSublattice hL le_rfl y)
theorem toSublattice_toSublattice (hL : 0 < L) {i i' : ℤ} (hi : i ≤ i') (i'' : ℤ)
    (y : PeriodicLattice.Site L n i) :
    PeriodicLattice.Site.toSublattice (PeriodicLattice.Site.toSublattice y i') i'' =
      PeriodicLattice.Site.toSublattice y i'' := by
  unfold PeriodicLattice.Site.toSublattice
  have h := coe_toSublattice hL hi y
  unfold PeriodicLattice.Site.toSublattice at h
  rw [h]
theorem restrictVertexFunction_apply {i j : ℕ} (l : Vertex L n k j → Matrices.ComplexMatrix2)
    (x : Vertex L n k i) :
    restrictVertexFunction i l x =
      l (PeriodicLattice.Site.toSublattice x (PeriodicLattice.levelDepth k j)) := rfl
theorem cubeContourAverageIter_apply (m : ℕ) (B : Edge L n k 0 → Matrices.ComplexMatrix2)
    (x : Vertex L n k m) :
    cubeContourAverageIter L n k m B x =
      ∑ i ∈ Finset.range m, cubeContourAverage L n k i (crossingSmoothingIter L n k i B)
        (PeriodicLattice.Site.toSublattice x (PeriodicLattice.levelDepth k (i + 1))) := by
  simp only [cubeContourAverageIter, Finset.sum_apply, restrictVertexFunction_apply]
theorem cubeContourAverageIter_succ (hL : 0 < L) (m : ℕ)
    (B : Edge L n k 0 → Matrices.ComplexMatrix2) :
    cubeContourAverageIter L n k (m + 1) B =
      cubeContourAverage L n k m (crossingSmoothingIter L n k m B) +
        restrictVertexFunction (m + 1) (cubeContourAverageIter L n k m B) := by
  funext x
  have hx : PeriodicLattice.levelDepth k (m + 1) ≤ PeriodicLattice.levelDepth k m := by
    simp only [PeriodicLattice.levelDepth]
    push_cast
    omega
  rw [Pi.add_apply, restrictVertexFunction_apply, cubeContourAverageIter_apply,
    cubeContourAverageIter_apply, Finset.sum_range_succ, toSublattice_self hL, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [toSublattice_toSublattice hL hx]
theorem crossingSmoothingIter_mem (hRev : AxisPathReversal.MainStatement)
    (hBlk : BlockStructure) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {B : Edge L n k 0 → Matrices.ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k 0) :
    ∀ m, m ≤ k → crossingSmoothingIter L n k m B ∈ edgeFormSpace L n k m
  | 0, _ => hB
  | m + 1, h => crossingSmoothing_mem hRev hBlk hL hn (by omega)
      (crossingSmoothingIter_mem hRev hBlk hL hn hB m (by omega))
theorem cubeContourAverageIter_mem (hRev : AxisPathReversal.MainStatement)
    (hBlk : BlockStructure) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {B : Edge L n k 0 → Matrices.ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k 0) {m : ℕ}
    (hm : m ≤ k) :
    cubeContourAverageIter L n k m B ∈ vertexFunctionSpace L n k m := by
  refine mem_vertexFunctionSpace_of_forall fun x => ?_
  rw [cubeContourAverageIter_apply]
  refine Matrices.ComplexMatrix2.hermitianTraceless.sum_mem fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  exact cubeContourAverage_mem hBlk hL hn (by omega)
    (crossingSmoothingIter_mem hRev hBlk hL hn hB i (by omega)) _
theorem linearSmoothingIter_eq (hStep : TrivialLinearization.OneStepIdentitiesHold)
    (hRev : AxisPathReversal.MainStatement) (hBlk : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {B : Edge L n k 0 → Matrices.ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k 0) :
    ∀ m, m ≤ k → linearSmoothingIter L n k m B =
      crossingSmoothingIter L n k m B - vertexCoboundary (cubeContourAverageIter L n k m B)
  | 0, _ => by
    funext b
    simp [linearSmoothingIter, crossingSmoothingIter, cubeContourAverageIter, vertexCoboundary,
      PeriodicLattice.iterateFromBare]
  | m + 1, h => by
    have hpos : 0 < L := by have := hL.2; omega
    have ih := linearSmoothingIter_eq hStep hRev hBlk hL hn hB m (by omega)
    obtain ⟨h1, h2⟩ := hStep L hL n k m hn (by omega)
    have e1 := h1 _ (crossingSmoothingIter_mem hRev hBlk hL hn hB m (by omega))
    have e2 := (h2 _ (cubeContourAverageIter_mem hRev hBlk hL hn hB (m := m) (by omega))).1
    calc linearSmoothingIter L n k (m + 1) B
        = linearSmoothing L n k m (linearSmoothingIter L n k m B) := rfl
      _ = linearSmoothing L n k m (crossingSmoothingIter L n k m B -
            vertexCoboundary (cubeContourAverageIter L n k m B)) := by rw [ih]
      _ = linearSmoothing L n k m (crossingSmoothingIter L n k m B) -
            linearSmoothing L n k m (vertexCoboundary (cubeContourAverageIter L n k m B)) :=
          linearSmoothing_sub hBlk hL hn (by omega) _ _
      _ = crossingSmoothing L n k m (crossingSmoothingIter L n k m B) -
            vertexCoboundary (cubeContourAverage L n k m (crossingSmoothingIter L n k m B)) -
            vertexCoboundary (restrictVertexFunction (m + 1) (cubeContourAverageIter L n k m B)) := by
          rw [e1, e2]
      _ = crossingSmoothingIter L n k (m + 1) B -
            vertexCoboundary (cubeContourAverageIter L n k (m + 1) B) := by
          rw [cubeContourAverageIter_succ hpos]
          funext b
          show _ = crossingSmoothing L n k m (crossingSmoothingIter L n k m B) b - _
          simp only [Pi.sub_apply, Pi.add_apply, vertexCoboundary]
          abel
theorem maxOperatorNorm_crossingSmoothingIter_le (hLen : PeriodicLattice.DoubleBlockPathLengths)
    (hBlk : BlockStructure) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (B : Edge L n k 0 → Matrices.ComplexMatrix2) :
    ∀ m, m ≤ k → maxOperatorNorm (crossingSmoothingIter L n k m B) ≤
      (L : ℝ≥0∞) ^ m * maxOperatorNorm B
  | 0, _ => by
    simp [crossingSmoothingIter, PeriodicLattice.iterateFromBare]
  | m + 1, h => by
    have ih := maxOperatorNorm_crossingSmoothingIter_le hLen hBlk hL hn B m (by omega)
    refine iSup_le fun c => ?_
    refine (ofReal_norm_crossingSmoothing_le hLen hBlk hL hn (j := m) (by omega) _ c).trans ?_
    calc (L : ℝ≥0∞) * maxOperatorNorm (crossingSmoothingIter L n k m B)
        ≤ (L : ℝ≥0∞) * ((L : ℝ≥0∞) ^ m * maxOperatorNorm B) := by gcongr
      _ = (L : ℝ≥0∞) ^ (m + 1) * maxOperatorNorm B := by rw [pow_succ]; ring
theorem maxOperatorNorm_cubeContourAverageIter_le
    (hLen : PeriodicLattice.DoubleBlockPathLengths)
    (hBlk : BlockStructure) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (B : Edge L n k 0 → Matrices.ComplexMatrix2) {m : ℕ} (hm : m ≤ k) :
    maxOperatorNorm (cubeContourAverageIter L n k m B) ≤
      ∑ i ∈ Finset.range m, 2 * ((L : ℝ≥0∞) - 1) * (L : ℝ≥0∞) ^ i * maxOperatorNorm B := by
  refine iSup_le fun x => ?_
  show ENNReal.ofReal ‖cubeContourAverageIter L n k m B x‖ ≤ _
  rw [cubeContourAverageIter_apply]
  refine (ofReal_norm_finset_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' := Finset.mem_range.1 hi
  refine (ofReal_norm_cubeContourAverage_le hLen hBlk hL hn (j := i) (by omega) _ _).trans ?_
  have h := maxOperatorNorm_crossingSmoothingIter_le hLen hBlk hL hn B i (by omega)
  calc 2 * ((L : ℝ≥0∞) - 1) * maxOperatorNorm (crossingSmoothingIter L n k i B)
      ≤ 2 * ((L : ℝ≥0∞) - 1) * ((L : ℝ≥0∞) ^ i * maxOperatorNorm B) := by gcongr
    _ = 2 * ((L : ℝ≥0∞) - 1) * (L : ℝ≥0∞) ^ i * maxOperatorNorm B := by ring
end Levels
theorem sum_two_mul_sub_one_mul_pow_add_two_le {a : ℝ≥0∞} (ha : 1 ≤ a) (m : ℕ) :
    ∑ i ∈ Finset.range m, 2 * (a - 1) * a ^ i + 2 ≤ 2 * a ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    calc ∑ i ∈ Finset.range m, 2 * (a - 1) * a ^ i + 2 * (a - 1) * a ^ m + 2
        = (∑ i ∈ Finset.range m, 2 * (a - 1) * a ^ i + 2) + 2 * (a - 1) * a ^ m := by ring
      _ ≤ 2 * a ^ m + 2 * (a - 1) * a ^ m := by gcongr
      _ = 2 * a ^ m * (1 + (a - 1)) := by ring
      _ = 2 * a ^ (m + 1) := by rw [add_tsub_cancel_of_le ha, pow_succ]; ring
theorem sum_two_mul_sub_one_mul_pow_mul_le {a : ℝ≥0∞} (ha : 1 ≤ a) (m : ℕ) (S : ℝ≥0∞) :
    ∑ i ∈ Finset.range m, 2 * (a - 1) * a ^ i * S ≤ 2 * a ^ m * S := by
  rw [← Finset.sum_mul]
  gcongr
  exact le_self_add.trans (sum_two_mul_sub_one_mul_pow_add_two_le ha m)
theorem iterateIdentitiesStatement_holds (hStep : TrivialLinearization.OneStepIdentitiesHold)
    (hRev : AxisPathReversal.MainStatement)
    (hLen : PeriodicLattice.DoubleBlockPathLengths)
    (hBlk : BlockStructure) : IterateIdentitiesStatement := by
  intro L hL n k m hn hm B hB
  have ha : (1 : ℝ≥0∞) ≤ (L : ℝ≥0∞) := by
    have := hL.2
    exact_mod_cast (by omega : 1 ≤ L)
  have hrel := linearSmoothingIter_eq hStep hRev hBlk hL hn hB m hm
  have hQ := maxOperatorNorm_crossingSmoothingIter_le hLen hBlk hL hn B m hm
  have hN := maxOperatorNorm_cubeContourAverageIter_le hLen hBlk hL hn B hm
  have hS := sum_two_mul_sub_one_mul_pow_mul_le ha m (maxOperatorNorm B)
  refine ⟨hrel, hQ, hN, hS, ?_⟩
  rw [hrel]
  refine iSup_le fun b => ?_
  have hd : ENNReal.ofReal ‖vertexCoboundary (cubeContourAverageIter L n k m B) b‖ ≤
      2 * (2 * (L : ℝ≥0∞) ^ m * maxOperatorNorm B) := by
    have hx := fun x =>
      (ofReal_norm_le_maxOperatorNorm (cubeContourAverageIter L n k m B) x).trans (hN.trans hS)
    calc ENNReal.ofReal ‖vertexCoboundary (cubeContourAverageIter L n k m B) b‖
        ≤ ENNReal.ofReal ‖cubeContourAverageIter L n k m B b.target‖ +
            ENNReal.ofReal ‖cubeContourAverageIter L n k m B b.source‖ :=
          ofReal_norm_sub_le_add _ _
      _ ≤ 2 * (L : ℝ≥0∞) ^ m * maxOperatorNorm B + 2 * (L : ℝ≥0∞) ^ m * maxOperatorNorm B :=
          add_le_add (hx _) (hx _)
      _ = 2 * (2 * (L : ℝ≥0∞) ^ m * maxOperatorNorm B) := by ring
  calc ENNReal.ofReal ‖(crossingSmoothingIter L n k m B -
        vertexCoboundary (cubeContourAverageIter L n k m B)) b‖
      ≤ ENNReal.ofReal ‖crossingSmoothingIter L n k m B b‖ +
          ENNReal.ofReal ‖vertexCoboundary (cubeContourAverageIter L n k m B) b‖ :=
        ofReal_norm_sub_le_add _ _
    _ ≤ (L : ℝ≥0∞) ^ m * maxOperatorNorm B + 2 * (2 * (L : ℝ≥0∞) ^ m * maxOperatorNorm B) :=
        add_le_add ((ofReal_norm_le_maxOperatorNorm _ b).trans hQ) hd
    _ = 5 * (L : ℝ≥0∞) ^ m * maxOperatorNorm B := by ring
end YangMills.Construction.Tower.IterateBounds
end
