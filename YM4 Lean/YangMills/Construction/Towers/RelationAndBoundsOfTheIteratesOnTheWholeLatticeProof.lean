import YangMills.Construction.Towers.BlocksStraightPathsContoursAndPivotBondsOfATowerProof
import YangMills.Construction.Towers.DilationCarriesValuesAtAStepOfTheWholeSpaceProof
import YangMills.Construction.Towers.RelationAndBoundsOfTheIteratesOfTheLinearMapsProof
import YangMills.Construction.Towers.RelationAndBoundsOfTheIteratesOnTheWholeLattice
import YangMills.Construction.Towers.RelationsOfTheLinearMapsOfAStepOfTheWholeLattice
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
namespace Tower.FullSpace.IterateBounds
def magnitude (X : Matrices.ComplexMatrix2) : ℝ≥0∞ := ENNReal.ofReal ‖X‖
theorem magnitude_add_le (X Y : Matrices.ComplexMatrix2) :
    magnitude (X + Y) ≤ magnitude X + magnitude Y := by apply _root_.YangMills.Construction.Tower.IterateBounds.ofReal_norm_add_le_add <;> assumption
theorem magnitude_sub_le (X Y : Matrices.ComplexMatrix2) :
    magnitude (X - Y) ≤ magnitude X + magnitude Y := by apply _root_.YangMills.Construction.Tower.IterateBounds.ofReal_norm_sub_le_add <;> assumption
theorem magnitude_zero : magnitude 0 = 0 := by simp [magnitude]
theorem magnitude_list_sum_le (l : List Matrices.ComplexMatrix2) (M : ℝ≥0∞)
    (h : ∀ X ∈ l, magnitude X ≤ M) :
    magnitude l.sum ≤ l.length * M := by
  induction l with
  | nil => simp [magnitude_zero]
  | cons X l ih =>
    rw [List.sum_cons, List.length_cons]
    calc magnitude (X + l.sum) ≤ magnitude X + magnitude l.sum := magnitude_add_le _ _
      _ ≤ M + l.length * M :=
        add_le_add (h X (by simp)) (ih fun Y hY => h Y (by simp [hY]))
      _ = ((l.length + 1 : ℕ) : ℝ≥0∞) * M := by push_cast; ring
theorem magnitude_finset_sum_le {ι : Type*} (s : Finset ι) (f : ι → Matrices.ComplexMatrix2) :
    magnitude (∑ i ∈ s, f i) ≤ ∑ i ∈ s, magnitude (f i) := by apply _root_.YangMills.Construction.Tower.IterateBounds.ofReal_norm_finset_sum_le <;> assumption
theorem magnitude_finset_sum_le_card_mul {ι : Type*} (s : Finset ι)
    (f : ι → Matrices.ComplexMatrix2) (M : ℝ≥0∞)
    (h : ∀ i ∈ s, magnitude (f i) ≤ M) : magnitude (∑ i ∈ s, f i) ≤ s.card * M :=
  (magnitude_finset_sum_le s f).trans ((Finset.sum_le_sum h).trans (by simp))
theorem magnitude_le_maxOperatorNorm {ι : Type*} (f : ι → Matrices.ComplexMatrix2) (i : ι) :
    magnitude (f i) ≤ maxOperatorNorm f := by apply _root_.YangMills.Construction.Tower.IterateBounds.ofReal_norm_le_maxOperatorNorm <;> assumption
theorem magnitude_inv_nat_smul_le (c : ℕ) (Y : Matrices.ComplexMatrix2) (M : ℝ≥0∞)
    (h : magnitude Y ≤ c * M) :
    magnitude ((((c : ℝ)⁻¹ : ℝ) : ℂ) • Y) ≤ M := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp [magnitude_zero]
  · have hc' : (0 : ℝ) < c := by exact_mod_cast hc
    have hn : ‖(((c : ℝ)⁻¹ : ℝ) : ℂ)‖ = (c : ℝ)⁻¹ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have e : magnitude ((((c : ℝ)⁻¹ : ℝ) : ℂ) • Y) = ENNReal.ofReal (c : ℝ)⁻¹ * magnitude Y := by
      unfold magnitude
      rw [norm_smul, hn, ENNReal.ofReal_mul (by positivity)]
    have one : ENNReal.ofReal (c : ℝ)⁻¹ * (c : ℝ≥0∞) = 1 := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
        inv_mul_cancel₀ hc'.ne', ENNReal.ofReal_one]
    rw [e]
    calc ENNReal.ofReal (c : ℝ)⁻¹ * magnitude Y ≤ ENNReal.ofReal (c : ℝ)⁻¹ * (c * M) := by gcongr
      _ = M := by rw [← mul_assoc, one, one_mul]
theorem inverseFourthPowerWeight_eq_inv (L : ℕ) :
    PeriodicLattice.inverseFourthPowerWeight L = ((((L ^ 4 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := by
  have e : (L : ℝ) ^ (-4 : ℤ) = (((L ^ 4 : ℕ) : ℝ))⁻¹ := by
    rw [zpow_neg]; norm_num
  unfold PeriodicLattice.inverseFourthPowerWeight
  rw [e]
theorem magnitude_weighted_finsum_le {ι : Type*} (L : ℕ) (S : Set ι) (hS : S.Finite)
    (hc : S.ncard = L ^ 4) (f : ι → Matrices.ComplexMatrix2) (M : ℝ≥0∞)
    (h : ∀ x ∈ S, magnitude (f x) ≤ M) :
    magnitude (PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ S, f x) ≤ M := by
  rw [inverseFourthPowerWeight_eq_inv]
  refine magnitude_inv_nat_smul_le (L ^ 4) _ M ?_
  rw [finsum_mem_eq_finite_toFinset_sum f hS]
  have key := magnitude_finset_sum_le_card_mul hS.toFinset f M fun i hi => h i (hS.mem_toFinset.1 hi)
  rwa [← Set.ncard_eq_toFinset_card S hS, hc] at key
theorem latticeSubgroup_meshAt_succ_subset (L k j : ℕ) (hL : L ≠ 0) :
    (InfiniteLattice.latticeSubgroup (meshAt L k (j + 1)) : Set AmbientSpace) ⊆
      InfiniteLattice.latticeSubgroup (meshAt L k j) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  have e : meshAt L k (j + 1) = L * meshAt L k j := by
    unfold meshAt
    rw [show (((j + 1 : ℕ) : ℤ) - (k : ℤ)) = 1 + ((j : ℤ) - (k : ℤ)) by push_cast; ring,
      zpow_add₀ hL', zpow_one]
  rintro x ⟨n, hn⟩
  refine ⟨fun μ => n μ * L, fun μ => ?_⟩
  rw [hn μ, e]
  push_cast
  ring
theorem latticeSubgroup_meshAt_subset_of_le (L k i j : ℕ) (hL : L ≠ 0) (hij : i ≤ j) :
    (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) ⊆
      InfiniteLattice.latticeSubgroup (meshAt L k i) := by
  induction j, hij using Nat.le_induction with
  | base => exact subset_rfl
  | succ j _ ih => exact (latticeSubgroup_meshAt_succ_subset L k j hL).trans ih
theorem coe_toFiner {a : ℝ} (a' : ℝ) (y : InfiniteLattice.LatticePoint a)
    (h : (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup a') :
    ((toFiner a' y : InfiniteLattice.LatticePoint a') : AmbientSpace) = y := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.coe_toFiner <;> assumption
theorem coe_shifted {L k j : ℕ} (hL : L ≠ 0) (c : Edge L k (j + 1))
    (x : Vertex L k j) :
    ((shifted c x : Vertex L k j) : AmbientSpace) =
      (x : AmbientSpace) + ((c.terminal : AmbientSpace) - (c.initial : AmbientSpace)) := by
  have hm : (((c.terminal - c.initial : Vertex L k (j + 1))) : AmbientSpace) ∈
      InfiniteLattice.latticeSubgroup (meshAt L k j) :=
    latticeSubgroup_meshAt_succ_subset L k j hL (c.terminal - c.initial).2
  have e := coe_toFiner (meshAt L k j) (c.terminal - c.initial) hm
  show ((x + toFiner (meshAt L k j) (c.terminal - c.initial) : Vertex L k j) : AmbientSpace) = _
  rw [AddSubgroup.coe_add, e, AddSubgroup.coe_sub]
theorem cubeVertices_finite_ncard (hZ : BlockStructure) {L k j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (y : Vertex L k (j + 1)) :
    (cubeVertices L (meshAt L k j) y).Finite ∧
      (cubeVertices L (meshAt L k j) y).ncard = L ^ 4 := by
  have hb : BlockEqOffsetImage L k (j + 1) y :=
    (hZ L k (j + 1) hL (by omega) (by omega) (by omega)).2.1 y
  have hc : (cube L (meshAt L k j) y).ncard = L ^ 4 := hb.2.2.1
  have hsub : cube L (meshAt L k j) y ⊆
      (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) := hb.2.2.2
  have hL0 : L ^ 4 ≠ 0 := pow_ne_zero 4 (by have := hL.2; omega)
  have hfin : (cube L (meshAt L k j) y).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hc]; exact hL0)
  refine ⟨hfin.preimage Subtype.val_injective.injOn, ?_⟩
  have e := Set.ncard_preimage_of_injective_subset_range
    (f := (Subtype.val : Vertex L k j → AmbientSpace)) (s := cube L (meshAt L k j) y)
    Subtype.val_injective (by simpa using hsub)
  exact e.trans hc
theorem length_crossingPath (hZ : BlockStructure) {L k j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (c : Edge L k (j + 1))
    (x : Vertex L k j) (hx : x ∈ cubeVertices L (meshAt L k j) c.initial) :
    (crossingPath c x).length = L := by
  obtain ⟨μ, hμ⟩ := c.isAdjacent
  have ht : BlockTranslateAlongBond L k (j + 1) c μ :=
    (hZ L k (j + 1) hL (by omega) (by omega) (by omega)).2.2.2.1 c μ hμ
  have hL0 : L ≠ 0 := by have := hL.2; omega
  exact (ht.2 x (shifted c x) hx (coe_shifted hL0 c x)).2.2.1
theorem length_stepsInOrder {a : ℝ} (ν : Fin 4 → ℤ) (x : InfiniteLattice.LatticePoint a)
    (l : List (Fin 4)) :
    (stepsInOrder ν x l).length = (l.map fun μ => (ν μ).natAbs).sum := by apply _root_.YangMills.Construction.Tower.FullSpace.CubesAndPaths.length_stepsInOrder <;> assumption
theorem two_mul_sum_natAbs_le (ν : Fin 4 → ℤ) (b : ℕ) (h : ∀ μ, 2 * (ν μ).natAbs ≤ b)
    (l : List (Fin 4)) : 2 * (l.map fun μ => (ν μ).natAbs).sum ≤ l.length * b := by
  induction l with
  | nil => simp
  | cons μ l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have e : (l.length + 1) * b = l.length * b + b := by ring
    have := h μ
    rw [e]
    omega
theorem cubeOffset_isCubeOffset (L : ℕ) {a a' : ℝ} (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a') (hx : x ∈ cubeVertices L a' y) :
    IsCubeOffset L y x (cubeOffset L y x) := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingOfValues.cubeOffset_spec <;> assumption
theorem length_contour_le (L : ℕ) {a a' : ℝ} (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a') (hx : x ∈ cubeVertices L a' y) (σ : ContourOrder L y x) :
    (contour L y x σ).length ≤ 2 * (L - 1) := by
  have hν := (cubeOffset_isCubeOffset L y x hx).2
  have hb : ∀ μ, 2 * (cubeOffset L y x μ).natAbs ≤ L - 1 := fun μ => by
    have := hν μ
    rw [Int.abs_eq_natAbs] at this
    omega
  unfold contour
  rw [length_stepsInOrder]
  have h2 := two_mul_sum_natAbs_le (cubeOffset L y x) (L - 1) hb
    ((List.finRange (offsetSupport L y x).card).map
      fun i => ((σ i : offsetSupport L y x) : Fin 4))
  have hlen : ((List.finRange (offsetSupport L y x).card).map
      fun i => ((σ i : offsetSupport L y x) : Fin 4)).length ≤ 4 := by
    simpa using Finset.card_le_univ (offsetSupport L y x)
  have h3 := Nat.mul_le_mul_right (L - 1) hlen
  omega
theorem magnitude_sumAlong_le {a : ℝ} (B : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (Γ : List (InfiniteLattice.Link a)) :
    magnitude (sumAlong B Γ) ≤ Γ.length * maxOperatorNorm B := by
  have key := magnitude_list_sum_le (Γ.map B) (maxOperatorNorm B) fun X hX => by
    obtain ⟨b, _, rfl⟩ := List.mem_map.1 hX
    exact magnitude_le_maxOperatorNorm B b
  simpa [sumAlong] using key
theorem magnitude_contourAverage_le (L : ℕ) {a a' : ℝ} (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a') (hx : x ∈ cubeVertices L a' y)
    (B : InfiniteLattice.Link a' → Matrices.ComplexMatrix2) :
    magnitude (contourAverage L B y x) ≤ ((2 * (L - 1) : ℕ) : ℝ≥0∞) * maxOperatorNorm B := by
  unfold contourAverage
  refine magnitude_inv_nat_smul_le _ _ _ ?_
  refine (magnitude_finset_sum_le_card_mul _ _ (((2 * (L - 1) : ℕ) : ℝ≥0∞) * maxOperatorNorm B)
    fun σ _ => ?_).trans (le_of_eq ?_)
  · refine (magnitude_sumAlong_le B _).trans ?_
    have := length_contour_le L y x hx σ
    gcongr
  · rw [Finset.card_univ]
theorem maxOperatorNorm_crossingSmoothing_le (hZ : BlockStructure) {L k j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    (B : Edge L k j → Matrices.ComplexMatrix2) :
    maxOperatorNorm (crossingSmoothing (a := meshAt L k (j + 1)) L B) ≤ L * maxOperatorNorm B := by
  refine iSup_le fun c => ?_
  obtain ⟨hf, hc⟩ := cubeVertices_finite_ncard hZ hL hj c.initial
  change magnitude (PeriodicLattice.inverseFourthPowerWeight L •
    ∑ᶠ x ∈ cubeVertices L (meshAt L k j) c.initial, edgeFormPathSum B (crossingPath c x)) ≤ _
  refine magnitude_weighted_finsum_le L _ hf hc _ _ fun x hx => ?_
  have key := magnitude_sumAlong_le B (crossingPath c x)
  rwa [length_crossingPath hZ hL hj c x hx] at key
theorem maxOperatorNorm_cubeContourAverage_le (hZ : BlockStructure) {L k j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    (B : Edge L k j → Matrices.ComplexMatrix2) :
    maxOperatorNorm (cubeContourAverage (a := meshAt L k (j + 1)) L B) ≤
      ((2 * (L - 1) : ℕ) : ℝ≥0∞) * maxOperatorNorm B := by
  refine iSup_le fun y => ?_
  obtain ⟨hf, hc⟩ := cubeVertices_finite_ncard hZ hL hj y
  change magnitude (PeriodicLattice.inverseFourthPowerWeight L •
    ∑ᶠ x ∈ cubeVertices L (meshAt L k j) y, contourAverage L B y x) ≤ _
  exact magnitude_weighted_finsum_le L _ hf hc _ _ fun x hx =>
    magnitude_contourAverage_le L y x hx B
theorem maxOperatorNorm_restrict_le {a : ℝ} (a' : ℝ)
    (l : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2) :
    maxOperatorNorm (restrictVertexFunction a' l) ≤ maxOperatorNorm l :=
  iSup_le fun x => magnitude_le_maxOperatorNorm l (toFiner a x)
theorem maxOperatorNorm_finset_sum_le {ι κ : Type*} (s : Finset κ)
    (f : κ → ι → Matrices.ComplexMatrix2) :
    maxOperatorNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, maxOperatorNorm (f i) := by
  refine iSup_le fun x => ?_
  change magnitude ((∑ i ∈ s, f i) x) ≤ _
  rw [Finset.sum_apply]
  exact (magnitude_finset_sum_le s _).trans
    (Finset.sum_le_sum fun i _ => magnitude_le_maxOperatorNorm (f i) x)
theorem maxOperatorNorm_vertexCoboundary_le {a : ℝ}
    (l : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2) :
    maxOperatorNorm (vertexCoboundary l) ≤ 2 * maxOperatorNorm l := by
  refine iSup_le fun b => ?_
  change magnitude (l b.terminal - l b.initial) ≤ _
  refine (magnitude_sub_le _ _).trans ?_
  rw [two_mul]
  exact add_le_add (magnitude_le_maxOperatorNorm l _) (magnitude_le_maxOperatorNorm l _)
theorem maxOperatorNorm_sub_le {ι : Type*} (f g : ι → Matrices.ComplexMatrix2) :
    maxOperatorNorm (f - g) ≤ maxOperatorNorm f + maxOperatorNorm g := by
  refine iSup_le fun x => ?_
  change magnitude (f x - g x) ≤ _
  exact (magnitude_sub_le _ _).trans
    (add_le_add (magnitude_le_maxOperatorNorm f x) (magnitude_le_maxOperatorNorm g x))
theorem apply_mem_hermitianTraceless {a : ℝ}
    {B : InfiniteLattice.Link a → Matrices.ComplexMatrix2} (hB : B ∈ edgeFormSpace a)
    (b : InfiniteLattice.Link a) : B b ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
  have hB' : (∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented →
      B b ∈ Matrices.ComplexMatrix2.hermitianTraceless) ∧
      ∀ b : InfiniteLattice.Link a, B b.opposite = -B b := hB
  obtain ⟨μ, h | h⟩ := b.isAdjacent
  · exact hB'.1 b ⟨μ, h⟩
  · have hp : b.opposite.IsPositivelyOriented := ⟨μ, by
      show b.initial - b.terminal = _
      rw [← neg_sub, h, neg_neg]⟩
    have key := Matrices.ComplexMatrix2.hermitianTraceless.neg_mem (hB'.1 _ hp)
    rwa [hB'.2 b, neg_neg] at key
theorem sumAlong_mem {a : ℝ} {B : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (h : ∀ b, B b ∈ Matrices.ComplexMatrix2.hermitianTraceless)
    (Γ : List (InfiniteLattice.Link a)) :
    sumAlong B Γ ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
  induction Γ with
  | nil => simp [sumAlong]
  | cons b Γ ih =>
    have e : sumAlong B (b :: Γ) = B b + sumAlong B Γ := by simp [sumAlong]
    rw [e]
    exact Matrices.ComplexMatrix2.hermitianTraceless.add_mem (h b) ih
theorem ofReal_smul_mem (r : ℝ) {X : Matrices.ComplexMatrix2}
    (h : X ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    (r : ℂ) • X ∈ Matrices.ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.IterateBounds.ofReal_smul_mem_hermitianTraceless <;> assumption
theorem finsum_mem_hermitianTraceless {ι : Type*} (S : Set ι) (f : ι → Matrices.ComplexMatrix2)
    (h : ∀ x ∈ S, f x ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    ∑ᶠ x ∈ S, f x ∈ Matrices.ComplexMatrix2.hermitianTraceless :=
  finsum_mem_induction (· ∈ Matrices.ComplexMatrix2.hermitianTraceless)
    Matrices.ComplexMatrix2.hermitianTraceless.zero_mem
    (fun _ _ => Matrices.ComplexMatrix2.hermitianTraceless.add_mem) h
theorem inverseFourthPowerWeight_smul_mem (L : ℕ) {X : Matrices.ComplexMatrix2}
    (h : X ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    PeriodicLattice.inverseFourthPowerWeight L • X ∈
      Matrices.ComplexMatrix2.hermitianTraceless := by
  rw [inverseFourthPowerWeight_eq_inv]
  exact ofReal_smul_mem _ h
theorem contourAverage_mem (L : ℕ) {a a' : ℝ}
    {B : InfiniteLattice.Link a' → Matrices.ComplexMatrix2}
    (h : ∀ b, B b ∈ Matrices.ComplexMatrix2.hermitianTraceless)
    (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a') :
    contourAverage L B y x ∈ Matrices.ComplexMatrix2.hermitianTraceless :=
  ofReal_smul_mem _ (Matrices.ComplexMatrix2.hermitianTraceless.sum_mem fun _ _ =>
    sumAlong_mem h _)
theorem crossingSmoothing_mem (hF : AxisPathReversal.MainStatement) {L k j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    {B : Edge L k j → Matrices.ComplexMatrix2}
    (hB : B ∈ edgeFormSpace (meshAt L k j)) :
    crossingSmoothing (a := meshAt L k (j + 1)) L B ∈ edgeFormSpace (meshAt L k (j + 1)) := by
  have hs := (hF L hL k).2
  have h1 := (hs.1 j hj.le).1 B hB
  refine ⟨fun c _ => ?_, fun c => ?_⟩
  · exact inverseFourthPowerWeight_smul_mem L
      (finsum_mem_hermitianTraceless _ _ fun x _ =>
        sumAlong_mem (apply_mem_hermitianTraceless hB) _)
  · have h2 := (hs.2 j hj c B h1).1
    change PeriodicLattice.inverseFourthPowerWeight L •
        ∑ᶠ z ∈ cubeVertices L (meshAt L k j) c.opposite.initial,
          edgeFormPathSum B (crossingPath c.opposite z) =
      -(PeriodicLattice.inverseFourthPowerWeight L •
        ∑ᶠ x ∈ cubeVertices L (meshAt L k j) c.initial, edgeFormPathSum B (crossingPath c x))
    rw [h2, smul_neg]
theorem cubeContourAverage_mem {L k j : ℕ} {B : Edge L k j → Matrices.ComplexMatrix2}
    (hB : B ∈ edgeFormSpace (meshAt L k j)) :
    cubeContourAverage (a := meshAt L k (j + 1)) L B ∈
      vertexFunctionSpace (meshAt L k (j + 1)) :=
  fun y _ => inverseFourthPowerWeight_smul_mem L
    (finsum_mem_hermitianTraceless _ _ fun x _ =>
      contourAverage_mem L (apply_mem_hermitianTraceless hB) y x)
theorem sumAlong_sub {a : ℝ} (F G : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (Γ : List (InfiniteLattice.Link a)) :
    sumAlong (F - G) Γ = sumAlong F Γ - sumAlong G Γ := by
  induction Γ with
  | nil => simp [sumAlong]
  | cons b Γ ih =>
    simp only [sumAlong, List.map_cons, List.sum_cons, Pi.sub_apply] at ih ⊢
    rw [ih]
    abel
theorem contourAverage_sub (L : ℕ) {a a' : ℝ}
    (F G : InfiniteLattice.Link a' → Matrices.ComplexMatrix2)
    (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a') :
    contourAverage L (F - G) y x = contourAverage L F y x - contourAverage L G y x := by
  simp only [contourAverage, sumAlong_sub, Finset.sum_sub_distrib, smul_sub]
theorem linearSmoothing_sub (L : ℕ) {a a' : ℝ}
    (F G : InfiniteLattice.Link a' → Matrices.ComplexMatrix2)
    (c : InfiniteLattice.Link a) (hf : (cubeVertices L a' c.initial).Finite) :
    linearSmoothing L (F - G) c = linearSmoothing L F c - linearSmoothing L G c := by
  simp only [linearSmoothing]
  rw [finsum_mem_eq_finite_toFinset_sum _ hf, finsum_mem_eq_finite_toFinset_sum _ hf,
    finsum_mem_eq_finite_toFinset_sum _ hf, ← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [contourAverage_sub, sumAlong_sub]
  abel
theorem vertexCoboundary_add {a : ℝ} (f g : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2) :
    vertexCoboundary (f + g) = vertexCoboundary f + vertexCoboundary g := by
  funext b
  simp only [vertexCoboundary, Pi.add_apply]
  abel
theorem restrict_self {a : ℝ} (l : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2) :
    restrictVertexFunction a l = l := by
  funext x
  show l (toFiner a x) = l x
  congr 1
  exact Subtype.ext (coe_toFiner a x x.2)
theorem restrict_restrict {a a' a'' : ℝ}
    (h₁ : (InfiniteLattice.latticeSubgroup a'' : Set AmbientSpace) ⊆
      InfiniteLattice.latticeSubgroup a')
    (h₂ : (InfiniteLattice.latticeSubgroup a' : Set AmbientSpace) ⊆
      InfiniteLattice.latticeSubgroup a)
    (l : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2) :
    restrictVertexFunction a'' (restrictVertexFunction a' l) = restrictVertexFunction a'' l := by
  funext x
  show l (toFiner a (toFiner a' x)) = l (toFiner a x)
  congr 1
  have e : ((toFiner a' x : InfiniteLattice.LatticePoint a') : AmbientSpace) = x :=
    coe_toFiner a' x (h₁ x.2)
  refine Subtype.ext ?_
  rw [coe_toFiner a _ (h₂ (toFiner a' x).2), e, coe_toFiner a x (h₂ (h₁ x.2))]
theorem restrict_finset_sum {a : ℝ} (a' : ℝ) {ι : Type*} (s : Finset ι)
    (f : ι → InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2) :
    restrictVertexFunction a' (∑ i ∈ s, f i) = ∑ i ∈ s, restrictVertexFunction a' (f i) := by
  funext x
  simp [restrictVertexFunction, Finset.sum_apply]
theorem cubeContourAverageIter_succ {L k m : ℕ} (hL : L ≠ 0)
    (B : Edge L k 0 → Matrices.ComplexMatrix2) :
    cubeContourAverageIter L k (m + 1) B =
      cubeContourAverage (a := meshAt L k (m + 1)) L (crossingSmoothingIter L k m B) +
        restrictVertexFunction (meshAt L k (m + 1)) (cubeContourAverageIter L k m B) := by
  unfold cubeContourAverageIter
  have e : ∑ i ∈ Finset.range m, restrictVertexFunction (meshAt L k (m + 1))
        (cubeContourAverage L (a := meshAt L k (i + 1)) (crossingSmoothingIter L k i B)) =
      ∑ i ∈ Finset.range m, restrictVertexFunction (meshAt L k (m + 1))
        (restrictVertexFunction (meshAt L k m)
          (cubeContourAverage L (a := meshAt L k (i + 1))
            (crossingSmoothingIter L k i B))) :=
    Finset.sum_congr rfl fun i hi =>
      (restrict_restrict (latticeSubgroup_meshAt_succ_subset L k m hL)
        (latticeSubgroup_meshAt_subset_of_le L k (i + 1) m hL (Finset.mem_range.1 hi)) _).symm
  rw [Finset.sum_range_succ, restrict_self, restrict_finset_sum, e]
  exact add_comm _ _
theorem crossingSmoothingIter_mem (hF : AxisPathReversal.MainStatement) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) {B : Edge L k 0 → Matrices.ComplexMatrix2}
    (hB : B ∈ edgeFormSpace (meshAt L k 0)) (m : ℕ) (hm : m ≤ k) :
    crossingSmoothingIter L k m B ∈ edgeFormSpace (meshAt L k m) := by
  induction m with
  | zero => exact hB
  | succ m ih => exact crossingSmoothing_mem hF hL hm (ih (by omega))
theorem cubeContourAverageIter_mem (hF : AxisPathReversal.MainStatement) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) {B : Edge L k 0 → Matrices.ComplexMatrix2}
    (hB : B ∈ edgeFormSpace (meshAt L k 0)) (m : ℕ) (hm : m ≤ k) :
    cubeContourAverageIter L k m B ∈ vertexFunctionSpace (meshAt L k m) := by
  unfold cubeContourAverageIter
  refine (vertexFunctionSpace (meshAt L k m)).sum_mem fun i hi => ?_
  have hi' : i < m := Finset.mem_range.1 hi
  have h := cubeContourAverage_mem (crossingSmoothingIter_mem hF hL hB i (by omega))
  exact fun x _ => h _ (Set.mem_univ _)
theorem linearSmoothingIter_eq (hStep : TrivialLinearization.OneStepIdentitiesHold)
    (hZ : BlockStructure) (hF : AxisPathReversal.MainStatement) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) {B : Edge L k 0 → Matrices.ComplexMatrix2}
    (hB : B ∈ edgeFormSpace (meshAt L k 0)) (m : ℕ) (hm : m ≤ k) :
    linearSmoothingIter L k m B =
      crossingSmoothingIter L k m B - vertexCoboundary (cubeContourAverageIter L k m B) := by
  have hL0 : L ≠ 0 := by have := hL.2; omega
  induction m with
  | zero =>
    have e : cubeContourAverageIter L k 0 B = 0 := by simp [cubeContourAverageIter]
    rw [e]
    funext b
    simp [vertexCoboundary, linearSmoothingIter, crossingSmoothingIter, composeFromZero]
  | succ m ih =>
    have hj : m < k := hm
    have hs := hStep L hL k m hj
    have e1 := hs.1 _ (crossingSmoothingIter_mem hF hL hB m hj.le)
    have e2 := (hs.2 _ (cubeContourAverageIter_mem hF hL hB m hj.le)).1
    have e0 : linearSmoothingIter L k (m + 1) B =
        linearSmoothing (a := meshAt L k (m + 1)) L (linearSmoothingIter L k m B) := rfl
    have e3 : crossingSmoothingIter L k (m + 1) B =
        crossingSmoothing (a := meshAt L k (m + 1)) L (crossingSmoothingIter L k m B) := rfl
    rw [e0, ih (by omega), e3, cubeContourAverageIter_succ hL0, vertexCoboundary_add]
    funext c
    rw [linearSmoothing_sub L _ _ c (cubeVertices_finite_ncard hZ hL hj c.initial).1, e1, e2]
    simp only [Pi.sub_apply, Pi.add_apply]
    abel
theorem maxOperatorNorm_crossingSmoothingIter_le (hZ : BlockStructure) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (B : Edge L k 0 → Matrices.ComplexMatrix2)
    (m : ℕ) (hm : m ≤ k) :
    maxOperatorNorm (crossingSmoothingIter L k m B) ≤ (L : ℝ≥0∞) ^ m * maxOperatorNorm B := by
  induction m with
  | zero =>
    have e : crossingSmoothingIter L k 0 B = B := rfl
    rw [e, pow_zero, one_mul]
  | succ m ih =>
    have e : crossingSmoothingIter L k (m + 1) B =
        crossingSmoothing (a := meshAt L k (m + 1)) L (crossingSmoothingIter L k m B) := rfl
    rw [e]
    calc _ ≤ (L : ℝ≥0∞) * maxOperatorNorm (crossingSmoothingIter L k m B) :=
          maxOperatorNorm_crossingSmoothing_le hZ hL hm _
      _ ≤ (L : ℝ≥0∞) * ((L : ℝ≥0∞) ^ m * maxOperatorNorm B) := by gcongr; exact ih (by omega)
      _ = (L : ℝ≥0∞) ^ (m + 1) * maxOperatorNorm B := by rw [pow_succ]; ring
theorem natCast_two_mul_sub_one {L : ℕ} (hL : 1 ≤ L) :
    ((2 * (L - 1) : ℕ) : ℝ≥0∞) = 2 * ((L : ℝ≥0∞) - 1) := by
  obtain ⟨l, rfl⟩ : ∃ l, L = l + 1 := ⟨L - 1, by omega⟩
  have e : (((l + 1 : ℕ) : ℝ≥0∞) - 1) = l := by
    push_cast
    exact ENNReal.add_sub_cancel_right ENNReal.one_ne_top
  rw [e]
  simp
theorem maxOperatorNorm_cubeContourAverageIter_le (hZ : BlockStructure) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (B : Edge L k 0 → Matrices.ComplexMatrix2)
    (m : ℕ) (hm : m ≤ k) :
    maxOperatorNorm (cubeContourAverageIter L k m B) ≤
      ∑ i ∈ Finset.range m, 2 * ((L : ℝ≥0∞) - 1) * (L : ℝ≥0∞) ^ i * maxOperatorNorm B := by
  refine (maxOperatorNorm_finset_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' : i < m := Finset.mem_range.1 hi
  have hL1 : 1 ≤ L := by have := hL.2; omega
  calc _ ≤ maxOperatorNorm (cubeContourAverage (a := meshAt L k (i + 1)) L
        (crossingSmoothingIter L k i B)) := maxOperatorNorm_restrict_le _ _
    _ ≤ ((2 * (L - 1) : ℕ) : ℝ≥0∞) * maxOperatorNorm (crossingSmoothingIter L k i B) :=
        maxOperatorNorm_cubeContourAverage_le hZ hL (by omega) _
    _ ≤ ((2 * (L - 1) : ℕ) : ℝ≥0∞) * ((L : ℝ≥0∞) ^ i * maxOperatorNorm B) := by
        gcongr
        exact maxOperatorNorm_crossingSmoothingIter_le hZ hL B i (by omega)
    _ = 2 * ((L : ℝ≥0∞) - 1) * (L : ℝ≥0∞) ^ i * maxOperatorNorm B := by
        rw [natCast_two_mul_sub_one hL1]; ring
theorem sum_two_mul_geom_add_two (l m : ℕ) :
    ∑ i ∈ Finset.range m, 2 * l * (l + 1) ^ i + 2 = 2 * (l + 1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    calc _ = (∑ i ∈ Finset.range m, 2 * l * (l + 1) ^ i + 2) + 2 * l * (l + 1) ^ m := by ring
      _ = 2 * (l + 1) ^ (m + 1) := by rw [ih]; ring
theorem sum_geom_le_two_mul_pow {L : ℕ} (hL : 1 ≤ L) (m : ℕ) (S : ℝ≥0∞) :
    ∑ i ∈ Finset.range m, 2 * ((L : ℝ≥0∞) - 1) * (L : ℝ≥0∞) ^ i * S ≤
      2 * (L : ℝ≥0∞) ^ m * S := by
  obtain ⟨l, rfl⟩ : ∃ l, L = l + 1 := ⟨L - 1, by omega⟩
  have e : (((l + 1 : ℕ) : ℝ≥0∞) - 1) = l := by
    push_cast
    exact ENNReal.add_sub_cancel_right ENNReal.one_ne_top
  rw [e, ← Finset.sum_mul]
  have h2 : ∑ i ∈ Finset.range m, 2 * l * (l + 1) ^ i ≤ 2 * (l + 1) ^ m := by
    have := sum_two_mul_geom_add_two l m
    omega
  have h3 : ∑ i ∈ Finset.range m, 2 * (l : ℝ≥0∞) * ((l + 1 : ℕ) : ℝ≥0∞) ^ i ≤
      2 * ((l + 1 : ℕ) : ℝ≥0∞) ^ m := by
    exact_mod_cast h2
  gcongr
theorem iterateIdentitiesStatement_holds (hStep : TrivialLinearization.OneStepIdentitiesHold)
    (hZ : BlockStructure) (hF : AxisPathReversal.MainStatement) :
    IterateIdentitiesStatement := by
  intro L hL k m hm B hB
  have hL1 : 1 ≤ L := by have := hL.2; omega
  have hrel := linearSmoothingIter_eq hStep hZ hF hL hB m hm
  have hQ := maxOperatorNorm_crossingSmoothingIter_le hZ hL B m hm
  have hn := maxOperatorNorm_cubeContourAverageIter_le hZ hL B m hm
  have hs := sum_geom_le_two_mul_pow hL1 m (maxOperatorNorm B)
  refine ⟨hrel, hQ, hn, hs, ?_⟩
  rw [hrel]
  calc _ ≤ maxOperatorNorm (crossingSmoothingIter L k m B) +
        maxOperatorNorm (vertexCoboundary (cubeContourAverageIter L k m B)) :=
          maxOperatorNorm_sub_le _ _
    _ ≤ (L : ℝ≥0∞) ^ m * maxOperatorNorm B + 2 * (2 * (L : ℝ≥0∞) ^ m * maxOperatorNorm B) := by
        refine add_le_add hQ ((maxOperatorNorm_vertexCoboundary_le _).trans ?_)
        gcongr
        exact hn.trans hs
    _ = 5 * (L : ℝ≥0∞) ^ m * maxOperatorNorm B := by ring
end Tower.FullSpace.IterateBounds
end YangMills.Construction
end
