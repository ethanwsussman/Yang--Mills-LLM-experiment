import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsPropertyProof
import YangMills.Construction.Towers.BlocksCorridorsPivotBondsAndPaths
import YangMills.Construction.Towers.LinearMapsOfTheWholeLatticeAreOnto
import YangMills.Construction.Towers.LinearMapsOnFormsSupportedOnPivotBondsOfTheWholeLattice
import YangMills.Construction.Towers.PivotBondOfABondOfEitherOrientationAtTheSideInfinity
import YangMills.Construction.Towers.ReverseOfAStraightPathOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.Surjectivity
open YangMills.Construction.Tower.TrivialLinearization (pivotScale)
theorem opposite_opposite {a : ℝ} (b : InfiniteLattice.Link a) : b.opposite.opposite = b := rfl
theorem isPositivelyOriented_or_opposite {a : ℝ} (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem pivotScale_smul_cube_smul (L : ℕ) (hL : L ≠ 0) (M : Matrices.ComplexMatrix2) :
    pivotScale L • (((L : ℝ) ^ 3) • M) = M := by
  have h : ((L : ℝ) ^ (-3 : ℤ)) * (L : ℝ) ^ 3 = 1 := by
    have hL' : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL
    rw [zpow_neg, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact inv_mul_cancel₀ (pow_ne_zero _ hL')
  have hc : ((((L : ℝ) ^ (-3 : ℤ) : ℝ) : ℂ)) * ((((L : ℝ) ^ 3 : ℝ)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, h, Complex.ofReal_one]
  ext p q
  simp only [Matrix.smul_apply, pivotScale, Complex.real_smul, smul_eq_mul]
  rw [← mul_assoc, hc, one_mul]
theorem pivotLink_injective {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) {k j : ℕ}
    (hj : j < k)
    (hPivot : PivotLinkOfAnyOrientation)
    (hCubes : CubesCorridorsPivotEdgesAndPaths)
    {c c' : Edge L k (j + 1)}
    (h : pivotLink L (meshAt L k j) c = pivotLink L (meshAt L k j) c') : c = c' := by
  have hdisj := (hCubes L hL k (j + 1) 1 (by omega) (by omega) (by omega) le_rfl
    (by omega)).1.pairwise_disjoint_cube
  have hc := (hPivot L hL k j hj c).isPivotLink.1
  have hc' := (hPivot L hL k j hj c').isPivotLink.1
  rw [← h] at hc'
  have same : ∀ y y' : Vertex L k (j + 1), ∀ x : InfiniteLattice.AmbientSpace,
      x ∈ cube L (meshAt L k j) y → x ∈ cube L (meshAt L k j) y' → y = y' := by
    intro y y' x hx hx'
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) hx hx'
  exact InfiniteLattice.Link.ext (same _ _ _ hc.1 hc'.1) (same _ _ _ hc.2 hc'.2)
def pivotSpread (L k j : ℕ) (C : Edge L k (j + 1) → Matrices.ComplexMatrix2) :
    Edge L k j → Matrices.ComplexMatrix2 :=
  open Classical in
  fun b => if h : ∃ c : Edge L k (j + 1), pivotLink L (meshAt L k j) c = b then
    ((L : ℝ) ^ 3) • C (Classical.choose h) else 0
theorem pivotSpread_pivotLink {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) {k j : ℕ}
    (hj : j < k)
    (hPivot : PivotLinkOfAnyOrientation)
    (hCubes : CubesCorridorsPivotEdgesAndPaths)
    (C : Edge L k (j + 1) → Matrices.ComplexMatrix2) (c : Edge L k (j + 1)) :
    pivotSpread L k j C (pivotLink L (meshAt L k j) c) = ((L : ℝ) ^ 3) • C c := by
  have h : ∃ c' : Edge L k (j + 1),
      pivotLink L (meshAt L k j) c' = pivotLink L (meshAt L k j) c := ⟨c, rfl⟩
  unfold pivotSpread
  rw [dif_pos h, pivotLink_injective hL hj hPivot hCubes (Classical.choose_spec h)]
theorem pivotSpread_of_not_pivot {L k j : ℕ} (C : Edge L k (j + 1) → Matrices.ComplexMatrix2)
    (b : Edge L k j)
    (h : ¬∃ c : Edge L k (j + 1), pivotLink L (meshAt L k j) c = b) :
    pivotSpread L k j C b = 0 := by
  unfold pivotSpread
  rw [dif_neg h]
theorem pivotSpread_mem {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) {k j : ℕ}
    (hj : j < k)
    (hPivot : PivotLinkOfAnyOrientation)
    (hCubes : CubesCorridorsPivotEdgesAndPaths)
    {C : Edge L k (j + 1) → Matrices.ComplexMatrix2}
    (hC : C ∈ edgeFormSpace (meshAt L k (j + 1))) :
    pivotSpread L k j C ∈ edgeFormSpace (meshAt L k j) := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · by_cases h : ∃ c : Edge L k (j + 1), pivotLink L (meshAt L k j) c = b
    · obtain ⟨c, rfl⟩ := h
      rw [pivotSpread_pivotLink hL hj hPivot hCubes]
      exact SMulMemClass.smul_mem _
        (hC.1 c (((hPivot L hL k j hj c).isPositivelyOriented_iff).mp hb))
    · rw [pivotSpread_of_not_pivot C b h]
      exact zero_mem _
  · by_cases h : ∃ c : Edge L k (j + 1), pivotLink L (meshAt L k j) c = b
    · obtain ⟨c, rfl⟩ := h
      rw [← (hPivot L hL k j hj c).pivotLink_opposite, pivotSpread_pivotLink hL hj hPivot hCubes,
        pivotSpread_pivotLink hL hj hPivot hCubes, hC.2 c, smul_neg]
    · have h' : ¬∃ c : Edge L k (j + 1),
          pivotLink L (meshAt L k j) c = b.opposite := by
        rintro ⟨c, hc⟩
        refine h ⟨c.opposite, ?_⟩
        rw [(hPivot L hL k j hj c).pivotLink_opposite, hc, opposite_opposite]
      rw [pivotSpread_of_not_pivot C b h, pivotSpread_of_not_pivot C _ h', neg_zero]
theorem pivotSpread_eq_zero_off {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    {k j : ℕ} (hj : j < k)
    (hPivot : PivotLinkOfAnyOrientation)
    (C : Edge L k (j + 1) → Matrices.ComplexMatrix2) (b : Edge L k j)
    (hb : b.IsPositivelyOriented)
    (hoff : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented → b ≠ pivotLink L (meshAt L k j) c) :
    pivotSpread L k j C b = 0 := by
  refine pivotSpread_of_not_pivot C b ?_
  rintro ⟨c, rfl⟩
  exact hoff c (((hPivot L hL k j hj c).isPositivelyOriented_iff).mp hb) rfl
theorem crossingSmoothing_opposite {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    {k j : ℕ} (hj : j < k)
    (hReverse : AxisPathReversal.MainStatement)
    {B : Edge L k j → Matrices.ComplexMatrix2} (hB : B ∈ edgeFormSpace (meshAt L k j))
    (c : Edge L k (j + 1)) :
    crossingSmoothing L B c.opposite = -crossingSmoothing L B c := by
  have hr := (hReverse L hL k).2
  have h := (hr.2 j hj c B ((hr.1 j (by omega)).1 B hB)).1
  unfold crossingSmoothing
  rw [h, smul_neg]
theorem linearSmoothing_opposite {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    {k j : ℕ} (hj : j < k)
    (hReverse : AxisPathReversal.MainStatement)
    {B : Edge L k j → Matrices.ComplexMatrix2} (hB : B ∈ edgeFormSpace (meshAt L k j))
    (c : Edge L k (j + 1)) :
    linearSmoothing L B c.opposite = -linearSmoothing L B c := by
  have hr := (hReverse L hL k).2
  exact (hr.2 j hj c B ((hr.1 j (by omega)).1 B hB)).2
theorem eq_of_eq_on_positive {a : ℝ} {F G : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hF : ∀ c, F c.opposite = -F c) (hG : ∀ c, G c.opposite = -G c)
    (h : ∀ c : InfiniteLattice.Link a, c.IsPositivelyOriented → F c = G c) : F = G := by
  funext c
  rcases isPositivelyOriented_or_opposite c with hc | hc
  · exact h c hc
  · have := h _ hc
    rw [hF, hG] at this
    exact neg_injective this
theorem step_surjective {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) {k j : ℕ}
    (hj : j < k)
    (hStep : LinearizationFacts.pivotFormsStatement)
    (hReverse : AxisPathReversal.MainStatement)
    (hPivot : PivotLinkOfAnyOrientation)
    (hCubes : CubesCorridorsPivotEdgesAndPaths)
    {C : Edge L k (j + 1) → Matrices.ComplexMatrix2}
    (hC : C ∈ edgeFormSpace (meshAt L k (j + 1))) :
    ∃ B ∈ edgeFormSpace (meshAt L k j), linearSmoothing L B = C ∧ crossingSmoothing L B = C := by
  have hB := pivotSpread_mem hL hj hPivot hCubes hC
  have hL0 : L ≠ 0 := by
    have := hL.2
    omega
  have hval := (hStep L hL k j hj _ hB (pivotSpread_eq_zero_off hL hj hPivot C)).2.2
  have hcross : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
      crossingSmoothing L (pivotSpread L k j C) c = C c := by
    intro c hc
    rw [(hval c hc).2, pivotSpread_pivotLink hL hj hPivot hCubes,
      pivotScale_smul_cube_smul L hL0]
  refine ⟨_, hB, ?_, ?_⟩
  · refine eq_of_eq_on_positive (linearSmoothing_opposite hL hj hReverse hB) hC.2 fun c hc => ?_
    rw [(hval c hc).1, hcross c hc]
  · exact eq_of_eq_on_positive (crossingSmoothing_opposite hL hj hReverse hB) hC.2 hcross
theorem composeFromZero_surjective {F : ℕ → Type*} (S : ∀ j, Set (F j))
    (step : ∀ j, F j → F (j + 1)) (k : ℕ)
    (hstep : ∀ j, j < k → ∀ C ∈ S (j + 1), ∃ B ∈ S j, step j B = C) (m : ℕ) (hm : m ≤ k) :
    ∀ C ∈ S m, ∃ B ∈ S 0, composeFromZero step m B = C := by
  induction m with
  | zero => exact fun C hC => ⟨C, hC, rfl⟩
  | succ m ih =>
    intro C hC
    obtain ⟨B', hB', rfl⟩ := hstep m (by omega) C hC
    obtain ⟨B, hB, rfl⟩ := ih (by omega) B' hB'
    exact ⟨B, hB, rfl⟩
theorem surjectivity
    (hStep : LinearizationFacts.pivotFormsStatement)
    (hReverse : AxisPathReversal.MainStatement)
    (hPivot : PivotLinkOfAnyOrientation)
    (hCubes : CubesCorridorsPivotEdgesAndPaths) :
    LinearizationFacts.surjectivityStatement := by
  intro L hL k j m hj hm
  have onto : ∀ i, i < k → ∀ C ∈ edgeFormSpace (meshAt L k (i + 1)),
      ∃ B ∈ edgeFormSpace (meshAt L k i), linearSmoothing L B = C ∧ crossingSmoothing L B = C :=
    fun i hi C hC => step_surjective hL hi hStep hReverse hPivot hCubes hC
  refine ⟨fun C hC => ?_, fun C hC => ?_, ?_, ?_⟩
  · obtain ⟨B, hB, h, -⟩ := onto j hj C hC
    exact ⟨B, hB, h⟩
  · obtain ⟨B, hB, -, h⟩ := onto j hj C hC
    exact ⟨B, hB, h⟩
  · exact composeFromZero_surjective (F := fun i => Edge L k i → Matrices.ComplexMatrix2)
      (fun i => (edgeFormSpace (meshAt L k i) : Set _)) (fun _ => linearSmoothing L) k
      (fun i hi C hC => by
        obtain ⟨B, hB, h, -⟩ := onto i hi C hC
        exact ⟨B, hB, h⟩) m hm
  · exact composeFromZero_surjective (F := fun i => Edge L k i → Matrices.ComplexMatrix2)
      (fun i => (edgeFormSpace (meshAt L k i) : Set _)) (fun _ => crossingSmoothing L) k
      (fun i hi C hC => by
        obtain ⟨B, hB, -, h⟩ := onto i hi C hC
        exact ⟨B, hB, h⟩) m hm
end YangMills.Construction.Tower.FullSpace.Surjectivity
end
