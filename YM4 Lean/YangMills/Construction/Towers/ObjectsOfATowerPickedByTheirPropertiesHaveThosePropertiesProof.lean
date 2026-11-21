import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.Towers.BlocksStraightPathsContoursAndPivotBondsOfATowerProof
import YangMills.Construction.Towers.BondsOfADoubleBlockAndTheirImageInATorusProof
import YangMills.Construction.Towers.ObjectsOfATowerPickedByTheirPropertiesHaveThoseProperties
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
noncomputable section
namespace Tower.SelectedObjects
theorem eq_zero_of_torusEuclidNorm_eq_zero {S : ℝ} {x : TorusMetric.Torus4 S}
    (h : TorusMetric.torusEuclidNorm x = 0) : x = 0 := by
  have hne : (TorusMetric.euclidNormVec '' (TorusMetric.torusProj S ⁻¹' {x})).Nonempty := by
    have hs : ∀ μ, ∃ t : ℝ, (t : AddCircle S) = x μ := fun μ =>
      QuotientAddGroup.mk_surjective (x μ)
    choose v hv using hs
    exact ⟨_, v, funext hv, rfl⟩
  funext μ
  have hle : ‖x μ‖ ≤ TorusMetric.torusEuclidNorm x := by
    refine le_csInf hne ?_
    rintro _ ⟨v, hv, rfl⟩
    have hvμ : (v μ : AddCircle S) = x μ := congrFun hv μ
    rw [← hvμ]
    calc ‖(v μ : AddCircle S)‖ ≤ ‖v μ‖ := QuotientAddGroup.norm_mk_le_norm
      _ = Real.sqrt (v μ ^ 2) := by rw [Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
      _ ≤ TorusMetric.euclidNormVec v :=
        Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun ν => v ν ^ 2)
          (fun ν _ => sq_nonneg _) (Finset.mem_univ μ))
  rw [h] at hle
  exact norm_le_zero_iff.1 hle
theorem torusEuclidNorm_zero {S : ℝ} :
    TorusMetric.torusEuclidNorm (0 : TorusMetric.Torus4 S) = 0 := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_zero <;> assumption
theorem isDistancePreserving_injective {L n : ℕ}
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hf : IsDistancePreserving f) : Function.Injective f := by
  intro a b hab
  have h := hf a b
  rw [hab, sub_self] at h
  have h0 : TorusMetric.torusEuclidNorm (a - b) = 0 := h.symm.trans torusEuclidNorm_zero
  exact sub_eq_zero.1 (eq_zero_of_torusEuclidNorm_eq_zero h0)
theorem fullSpace_isDistancePreserving_injective {f : AmbientSpace → AmbientSpace}
    (hf : FullSpace.IsDistancePreserving f) : Function.Injective f := by
  intro a b hab
  have h := hf a b
  rw [hab, sub_self] at h
  have h0 : ∑ μ, (a - b) μ ^ 2 = 0 := by
    have h1 : Real.sqrt (∑ μ, (a - b) μ ^ 2) = 0 := by
      simpa [TorusMetric.euclidNormVec] using h.symm
    exact (Real.sqrt_eq_zero (Finset.sum_nonneg fun μ _ => sq_nonneg _)).1 h1
  funext μ
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun μ _ => sq_nonneg ((a - b) μ))).1 h0 μ
    (Finset.mem_univ μ)
  exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)
theorem imagesOnSide_of_distancePreserving {L n k j : ℕ}
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hf : IsDistancePreserving f) (hl : MapsSublatticeOnto k j f) (hb : MapsEdgesOnto k j f) :
    ImagesOnSide L n k j f := by
  have inj := isDistancePreserving_injective hf
  have hmap : ∀ x : Vertex L n k j,
      ((vertexImage (k := k) (j := j) f x : Vertex L n k j) : PeriodicLattice.FourTorus L n) =
        f x := by
    intro x
    have hx : f x ∈ (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k j) :
        Set (PeriodicLattice.FourTorus L n)) := by
      rw [← hl]
      exact ⟨x, x.2, rfl⟩
    exact Classical.epsilon_spec
      (p := fun x' : Vertex L n k j => (x' : PeriodicLattice.FourTorus L n) = f x)
      ⟨⟨f x, hx⟩, rfl⟩
  have hinv : ∀ x : Vertex L n k j,
      f (vertexPreimage (k := k) (j := j) f x : Vertex L n k j) = x := by
    intro x
    have hx : (x : PeriodicLattice.FourTorus L n) ∈ f '' (PeriodicLattice.sublattice L n
        (PeriodicLattice.levelDepth k j) : Set (PeriodicLattice.FourTorus L n)) := by
      rw [hl]
      exact x.2
    obtain ⟨z, hz, hzx⟩ := hx
    exact Classical.epsilon_spec (p := fun x' : Vertex L n k j => f x' = x) ⟨⟨z, hz⟩, hzx⟩
  have hmapu : ∀ x x' : Vertex L n k j,
      (x' : PeriodicLattice.FourTorus L n) = f x → x' = vertexImage (k := k) (j := j) f x :=
    fun x x' h => Subtype.ext (h.trans (hmap x).symm)
  have hinvu : ∀ x x' : Vertex L n k j,
      f x' = x → x' = vertexPreimage (k := k) (j := j) f x :=
    fun x x' h => Subtype.ext (inj (h.trans (hinv x).symm))
  have hmb : ∀ b : Edge L n k j,
      (edgeImage (k := k) (j := j) f b).source = vertexImage (k := k) (j := j) f b.source ∧
        (edgeImage (k := k) (j := j) f b).target = vertexImage (k := k) (j := j) f b.target := by
    intro b
    obtain ⟨b', h1, h2⟩ := hb.1 b
    exact Classical.epsilon_spec (p := fun b' : Edge L n k j =>
      b'.source = vertexImage (k := k) (j := j) f b.source ∧
        b'.target = vertexImage (k := k) (j := j) f b.target)
      ⟨b', hmapu _ _ h1, hmapu _ _ h2⟩
  have hib : ∀ b : Edge L n k j,
      (edgePreimage (k := k) (j := j) f b).source = vertexPreimage (k := k) (j := j) f b.source ∧
        (edgePreimage (k := k) (j := j) f b).target =
          vertexPreimage (k := k) (j := j) f b.target := by
    intro b
    obtain ⟨b', h1, h2⟩ := hb.2 b
    exact Classical.epsilon_spec (p := fun b' : Edge L n k j =>
      b'.source = vertexPreimage (k := k) (j := j) f b.source ∧
        b'.target = vertexPreimage (k := k) (j := j) f b.target)
      ⟨b', hinvu _ _ h1.symm, hinvu _ _ h2.symm⟩
  exact
    { vertexImage_coe := hmap
      vertexImage_unique := hmapu
      apply_vertexPreimage := hinv
      vertexPreimage_unique := hinvu
      edgeImage_endpoints := hmb
      edgeImage_unique := fun b b' h1 h2 =>
        PeriodicLattice.Bond.ext (h1.trans (hmb b).1.symm) (h2.trans (hmb b).2.symm)
      edgePreimage_endpoints := hib
      edgePreimage_unique := fun b b' h1 h2 =>
        PeriodicLattice.Bond.ext (h1.trans (hib b).1.symm) (h2.trans (hib b).2.symm) }
theorem imagesAtInfinity_of_distancePreserving {L k j : ℕ} {f : AmbientSpace → AmbientSpace}
    (hf : FullSpace.IsDistancePreserving f)
    (hl : FullSpace.MapsSublatticeOnto (meshAt L k j) f)
    (hb : FullSpace.MapsLinksOnto (meshAt L k j) f) : ImagesAtInfinity L k j f := by
  have inj := fullSpace_isDistancePreserving_injective hf
  have hmap : ∀ x : FullSpace.Vertex L k j,
      ((FullSpace.vertexImage f x : FullSpace.Vertex L k j) : AmbientSpace) = f x := by
    intro x
    have hx : f x ∈ (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) := by
      rw [← hl]
      exact ⟨x, x.2, rfl⟩
    exact Classical.epsilon_spec
      (p := fun x' : FullSpace.Vertex L k j => (x' : AmbientSpace) = f x) ⟨⟨f x, hx⟩, rfl⟩
  have hinv : ∀ x : FullSpace.Vertex L k j,
      f (FullSpace.vertexPreimage f x : FullSpace.Vertex L k j) = x := by
    intro x
    have hx : (x : AmbientSpace) ∈
        f '' (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) := by
      rw [hl]
      exact x.2
    obtain ⟨z, hz, hzx⟩ := hx
    exact Classical.epsilon_spec (p := fun x' : FullSpace.Vertex L k j => f x' = x)
      ⟨⟨z, hz⟩, hzx⟩
  have hmapu : ∀ x x' : FullSpace.Vertex L k j,
      (x' : AmbientSpace) = f x → x' = FullSpace.vertexImage f x :=
    fun x x' h => Subtype.ext (h.trans (hmap x).symm)
  have hinvu : ∀ x x' : FullSpace.Vertex L k j, f x' = x → x' = FullSpace.vertexPreimage f x :=
    fun x x' h => Subtype.ext (inj (h.trans (hinv x).symm))
  have hmb : ∀ b : FullSpace.Edge L k j,
      (FullSpace.edgeImage f b).initial = FullSpace.vertexImage f b.initial ∧
        (FullSpace.edgeImage f b).terminal = FullSpace.vertexImage f b.terminal := by
    intro b
    obtain ⟨b', h1, h2⟩ := hb.1 b
    exact Classical.epsilon_spec (p := fun b' : FullSpace.Edge L k j =>
      b'.initial = FullSpace.vertexImage f b.initial ∧
        b'.terminal = FullSpace.vertexImage f b.terminal)
      ⟨b', hmapu _ _ h1, hmapu _ _ h2⟩
  have hib : ∀ b : FullSpace.Edge L k j,
      (FullSpace.edgePreimage f b).initial = FullSpace.vertexPreimage f b.initial ∧
        (FullSpace.edgePreimage f b).terminal = FullSpace.vertexPreimage f b.terminal := by
    intro b
    obtain ⟨b', h1, h2⟩ := hb.2 b
    exact Classical.epsilon_spec (p := fun b' : FullSpace.Edge L k j =>
      b'.initial = FullSpace.vertexPreimage f b.initial ∧
        b'.terminal = FullSpace.vertexPreimage f b.terminal)
      ⟨b', hinvu _ _ h1.symm, hinvu _ _ h2.symm⟩
  exact
    { vertexImage_coe := hmap
      vertexImage_unique := hmapu
      apply_vertexPreimage := hinv
      vertexPreimage_unique := hinvu
      edgeImage_endpoints := hmb
      edgeImage_unique := fun b b' h1 h2 =>
        InfiniteLattice.Link.ext (h1.trans (hmb b).1.symm) (h2.trans (hmb b).2.symm)
      edgePreimage_endpoints := hib
      edgePreimage_unique := fun b b' h1 h2 =>
        InfiniteLattice.Link.ext (h1.trans (hib b).1.symm) (h2.trans (hib b).2.symm) }
section Steps
variable {a : ℝ}
theorem mem_forwardSteps (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (n : ℕ)
    (b : InfiniteLattice.Link a) :
    b ∈ FullSpace.forwardSteps x μ n ↔ ∃ i : ℕ, i < n ∧
      b = InfiniteLattice.Link.forwardFrom (x + i • InfiniteLattice.axisStep a μ) μ := by apply _root_.YangMills.Construction.Tower.FullSpace.CubesAndPaths.mem_forwardSteps <;> assumption
theorem mem_backwardSteps (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (n : ℕ)
    (b : InfiniteLattice.Link a) :
    b ∈ FullSpace.backwardSteps x μ n ↔ ∃ i : ℕ, i < n ∧
      b = FullSpace.backwardLink (x - i • InfiniteLattice.axisStep a μ) μ := by
  induction n generalizing x with
  | zero => simp [FullSpace.backwardSteps]
  | succ n ih =>
    have key : ∀ i : ℕ, x - InfiniteLattice.axisStep a μ - i • InfiniteLattice.axisStep a μ =
        x - (i + 1) • InfiniteLattice.axisStep a μ := fun i => by
      rw [add_nsmul, one_nsmul]
      abel
    simp only [FullSpace.backwardSteps, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, Nat.succ_pos n, by simp⟩
      · exact ⟨i + 1, Nat.succ_lt_succ hi, by rw [key]⟩
    · rintro ⟨i, hi, rfl⟩
      cases i with
      | zero => left; simp
      | succ i => right; exact ⟨i, by omega, by rw [key]⟩
theorem opposite_forwardFrom (z : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    (InfiniteLattice.Link.forwardFrom z μ).opposite =
      FullSpace.backwardLink (z + InfiniteLattice.axisStep a μ) μ :=
  InfiniteLattice.Link.ext rfl (add_sub_cancel_right z _).symm
theorem opposite_backwardLink (z : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    (FullSpace.backwardLink z μ).opposite =
      InfiniteLattice.Link.forwardFrom (z - InfiniteLattice.axisStep a μ) μ :=
  InfiniteLattice.Link.ext rfl (sub_add_cancel z _).symm
theorem opposite_opposite (b : InfiniteLattice.Link a) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_opposite <;> assumption
theorem opposite_mem_backwardSteps {x : InfiniteLattice.LatticePoint a} {μ : Fin 4} {n : ℕ}
    {b : InfiniteLattice.Link a} (hb : b ∈ FullSpace.forwardSteps x μ n) :
    b.opposite ∈ FullSpace.backwardSteps (x + n • InfiniteLattice.axisStep a μ) μ n := by
  obtain ⟨i, hi, rfl⟩ := (mem_forwardSteps x μ n b).1 hb
  obtain ⟨d, rfl⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  refine (mem_backwardSteps _ μ _ _).2 ⟨d, by omega, ?_⟩
  rw [opposite_forwardFrom, add_nsmul, add_nsmul, one_nsmul]
  congr 1
  abel
theorem opposite_mem_forwardSteps {x : InfiniteLattice.LatticePoint a} {μ : Fin 4} {n : ℕ}
    {b : InfiniteLattice.Link a} (hb : b ∈ FullSpace.backwardSteps x μ n) :
    b.opposite ∈ FullSpace.forwardSteps (x - n • InfiniteLattice.axisStep a μ) μ n := by
  obtain ⟨i, hi, rfl⟩ := (mem_backwardSteps x μ n b).1 hb
  obtain ⟨d, rfl⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  refine (mem_forwardSteps _ μ _ _).2 ⟨d, by omega, ?_⟩
  rw [opposite_backwardLink, add_nsmul, add_nsmul, one_nsmul]
  congr 1
  abel
theorem isAxisDisplacement_of_coe {x x' : InfiniteLattice.LatticePoint a} {μ : Fin 4} {q : ℤ}
    (h : (x' : AmbientSpace) - (x : AmbientSpace) = Pi.single μ ((q : ℝ) * a)) :
    FullSpace.IsAxisDisplacement x x' μ q := by
  apply Subtype.ext
  refine h.trans ?_
  funext ν
  by_cases hν : ν = μ
  · subst hν
    simp [InfiniteLattice.axisStep]
  · simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne hν]
theorem isAxisDisplacement_symm {x x' : InfiniteLattice.LatticePoint a} {μ : Fin 4} {q : ℤ}
    (h : FullSpace.IsAxisDisplacement x x' μ q) : FullSpace.IsAxisDisplacement x' x μ (-q) := by
  unfold FullSpace.IsAxisDisplacement at h ⊢
  rw [neg_smul, ← h, neg_sub]
end Steps
theorem coe_toFiner {a a' : ℝ}
    (h : InfiniteLattice.latticeSubgroup a ≤ InfiniteLattice.latticeSubgroup a')
    (y : InfiniteLattice.LatticePoint a) :
    ((FullSpace.toFiner a' y : InfiniteLattice.LatticePoint a') : AmbientSpace) = y :=
  Classical.epsilon_spec (p := fun x : InfiniteLattice.LatticePoint a' => (x : AmbientSpace) = y)
    ⟨⟨y, h y.2⟩, rfl⟩
theorem meshAt_eq_mul_pred {L k j : ℕ} (hL : 0 < L) (hj : 1 ≤ j) :
    meshAt L k j = (L : ℝ) * meshAt L k (j - 1) := by apply _root_.YangMills.Construction.Tower.FullSpace.DoubleCubeImage.meshAt_eq_mul_pred <;> assumption
theorem coe_axisStep_eq {L k j : ℕ} (hL : 0 < L) (hj : 1 ≤ j) (μ : Fin 4) :
    ((InfiniteLattice.axisStep (meshAt L k j) μ : FullSpace.Vertex L k j) : AmbientSpace) =
      Pi.single μ ((((L : ℤ) : ℝ)) * meshAt L k (j - 1)) := by
  rw [Int.cast_natCast, ← meshAt_eq_mul_pred hL hj]
  rfl
theorem exists_axisDisplacement {L k j : ℕ} (hL : 0 < L) (hj : 1 ≤ j)
    (c : FullSpace.Edge L k j) {x x' : FullSpace.Vertex L k (j - 1)}
    (hx : (x' : AmbientSpace) - (x : AmbientSpace) =
      (c.terminal : AmbientSpace) - (c.initial : AmbientSpace)) :
    ∃ q : Fin 4 × ℤ, FullSpace.IsAxisDisplacement x x' q.1 q.2 := by
  obtain ⟨μ, h | h⟩ := c.isAdjacent
  · refine ⟨(μ, (L : ℤ)), isAxisDisplacement_of_coe ?_⟩
    rw [hx]
    exact (congrArg Subtype.val h).trans (coe_axisStep_eq hL hj μ)
  · refine ⟨(μ, -(L : ℤ)), isAxisDisplacement_of_coe ?_⟩
    rw [hx, Int.cast_neg, neg_mul, Pi.single_neg, ← coe_axisStep_eq hL hj μ]
    exact congrArg Subtype.val h
theorem coe_shifted {L k j : ℕ}
    (hn : InfiniteLattice.latticeSubgroup (meshAt L k j) ≤
      InfiniteLattice.latticeSubgroup (meshAt L k (j - 1)))
    (c : FullSpace.Edge L k j) (x : FullSpace.Vertex L k (j - 1)) :
    ((FullSpace.shifted c x : FullSpace.Vertex L k (j - 1)) : AmbientSpace) =
      (x : AmbientSpace) + ((c.terminal : AmbientSpace) - (c.initial : AmbientSpace)) := by
  unfold FullSpace.shifted
  rw [AddSubgroup.coe_add, coe_toFiner hn]
  rfl
theorem existsUnique_pivotLink_of_corridors {L k j : ℕ} (hL : 0 < L) (hj : 1 ≤ j)
    (hn : InfiniteLattice.latticeSubgroup (meshAt L k j) ≤
      InfiniteLattice.latticeSubgroup (meshAt L k (j - 1)))
    (st : FullSpace.StepsEdgesAndCorridors L k j)
    (hS : AxisPathUniqueness.OnFullSpace L k (j - 1)) (c : FullSpace.Edge L k j) :
    ∃! b : FullSpace.Edge L k (j - 1), FullSpace.IsPivotLink L (meshAt L k (j - 1)) c b := by
  obtain ⟨μ, h | h⟩ := c.isAdjacent
  · obtain ⟨b, hb, hu⟩ := st.existsUnique_corridorEdge c μ h
    exact ⟨b, ⟨hb.2, hb.1⟩, fun b' hb' => hu b' ⟨hb'.2, hb'.1⟩⟩
  · have hr : c.opposite.terminal - c.opposite.initial =
        InfiniteLattice.axisStep (meshAt L k j) μ := by
      show c.initial - c.terminal = _
      rw [← neg_sub, h, neg_neg]
    obtain ⟨b, hb, hu⟩ := st.existsUnique_corridorEdge c.opposite μ hr
    have hd : FullSpace.IsAxisDisplacement
        (FullSpace.toFiner (meshAt L k (j - 1)) c.initial)
        (FullSpace.toFiner (meshAt L k (j - 1)) c.terminal) μ (-(L : ℤ)) := by
      refine isAxisDisplacement_of_coe ?_
      rw [coe_toFiner hn, coe_toFiner hn, Int.cast_neg, neg_mul, Pi.single_neg,
        ← coe_axisStep_eq hL hj μ]
      exact congrArg Subtype.val h
    have hd' := isAxisDisplacement_symm hd
    rw [neg_neg] at hd'
    have hP := (hS.2 _ _ μ μ _ _ hd hd).2
    have hP' := (hS.2 _ _ μ μ _ _ hd' hd').2
    have hneg : ¬ (0 : ℤ) ≤ -(L : ℤ) := by omega
    rw [FullSpace.signedSteps, if_neg hneg, neg_neg, Int.toNat_natCast] at hP
    rw [FullSpace.signedSteps, if_pos (Int.natCast_nonneg L), Int.toNat_natCast] at hP'
    have hx1 : FullSpace.toFiner (meshAt L k (j - 1)) c.terminal +
        L • InfiniteLattice.axisStep (meshAt L k (j - 1)) μ =
        FullSpace.toFiner (meshAt L k (j - 1)) c.initial := by
      have hd'' : FullSpace.toFiner (meshAt L k (j - 1)) c.initial -
          FullSpace.toFiner (meshAt L k (j - 1)) c.terminal =
          L • InfiniteLattice.axisStep (meshAt L k (j - 1)) μ := by
        rw [← natCast_zsmul]
        exact hd'
      rw [← hd'']
      abel
    have hx2 : FullSpace.toFiner (meshAt L k (j - 1)) c.initial -
        L • InfiniteLattice.axisStep (meshAt L k (j - 1)) μ =
        FullSpace.toFiner (meshAt L k (j - 1)) c.terminal := by
      rw [← hx1]
      abel
    refine ⟨b.opposite, ⟨⟨hb.2.2, hb.2.1⟩, ?_⟩, fun b' hb' => ?_⟩
    · have h1 := hb.1
      rw [show FullSpace.axisPath (FullSpace.toFiner (meshAt L k (j - 1)) c.opposite.initial)
        (FullSpace.toFiner (meshAt L k (j - 1)) c.opposite.terminal) = _ from hP'] at h1
      have h2 := opposite_mem_backwardSteps h1
      rw [hx1] at h2
      rw [hP]
      exact h2
    · have h1 := hb'.2
      rw [hP] at h1
      have h2 := opposite_mem_forwardSteps h1
      rw [hx2, ← hP'] at h2
      have h3 : b'.opposite = b := hu _ ⟨h2, hb'.1.2, hb'.1.1⟩
      rw [← h3, opposite_opposite]
theorem existsUnique_cubeOffset_of_mem {L : ℕ} {a a' : ℝ} (ha : a' ≠ 0)
    (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a')
    (hx : x ∈ FullSpace.cubeVertices L a' y) :
    ∃! ν : Fin 4 → ℤ, FullSpace.IsCubeOffset L y x ν := by
  obtain ⟨ν, hν, hxν⟩ := hx
  refine ⟨ν, ⟨sub_eq_of_eq_add' hxν, by simpa using hν⟩, ?_⟩
  rintro ν' ⟨h1, -⟩
  have h2 := h1.symm.trans (sub_eq_of_eq_add' hxν)
  rw [Finset.univ_sum_single (fun μ => ((ν' μ : ℝ) * a')),
    Finset.univ_sum_single (fun μ => ((ν μ : ℝ) * a'))] at h2
  funext μ
  exact Int.cast_injective (mul_right_cancel₀ ha (congrFun h2 μ))
theorem image_cubeVertices {L k j : ℕ} (hp : FullSpace.CubesOfOrderPartition L k j 1)
    (y : FullSpace.Vertex L k j) :
    Subtype.val '' FullSpace.cubeVertices L (meshAt L k (j - 1)) y =
      FullSpace.cube L (meshAt L k (j - 1)) y := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hpm
    have hmem : p ∈ ⋃ y' : FullSpace.Vertex L k j,
        FullSpace.cubeOfOrder L (meshAt L k (j - 1)) 1 y' := Set.mem_iUnion.2 ⟨y, hpm⟩
    rw [hp.iUnion_cube] at hmem
    exact ⟨⟨p, hmem⟩, hpm, rfl⟩
theorem ncard_cubeVertices {L k j : ℕ} (hp : FullSpace.CubesOfOrderPartition L k j 1)
    (y : FullSpace.Vertex L k j) :
    (FullSpace.cubeVertices L (meshAt L k (j - 1)) y).ncard = L ^ 4 := by
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, image_cubeVertices hp]
  exact hp.cube_ncard y
theorem linkHolonomy_mem {a : ℝ} {U : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    {Γ : List (InfiniteLattice.Link a)}
    (h : ∀ b ∈ Γ, U b ∈ PeriodicLattice.complexGaugeGroup) :
    FullSpace.linkHolonomy U Γ ∈ PeriodicLattice.complexGaugeGroup := by
  induction Γ with
  | nil => simp [FullSpace.linkHolonomy, Matrices.ComplexMatrix2.unitDeterminant]
  | cons b Γ ih =>
    have h1 : (U b).det = 1 := h b (List.mem_cons_self ..)
    have h2 : (FullSpace.linkHolonomy U Γ).det = 1 :=
      ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb')
    show (FullSpace.linkHolonomy U (b :: Γ)).det = 1
    rw [show FullSpace.linkHolonomy U (b :: Γ) = U b * FullSpace.linkHolonomy U Γ by
      simp [FullSpace.linkHolonomy], Matrix.det_mul, h1, h2, one_mul]
theorem isNearLogMean_comp_equiv_iff {n : ℕ} {ι : Type*} [Fintype ι] (e : Fin n ≃ ι)
    (F : ι → Matrices.ComplexMatrix2) (W : Matrices.ComplexMatrix2) :
    Averaging.IsNearComplexLogMean (F ∘ e) W ↔ IsNearLogMean F W := by
  unfold Averaging.IsNearComplexLogMean IsNearLogMean Matrices.ComplexMatrix2.IsLogMean
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, i, h4⟩
    refine ⟨⟨h1, fun i => by simpa using h2 (e.symm i), ?_⟩, e i, h4⟩
    rw [← e.sum_comp]
    exact h3
  · rintro ⟨⟨h1, h2, h3⟩, i, h4⟩
    refine ⟨⟨h1, fun i => h2 (e i), ?_⟩, e.symm i, by simpa using h4⟩
    rw [← e.sum_comp] at h3
    exact h3
theorem familyDiameter_comp_equiv {n : ℕ} {ι : Type*} [Fintype ι] (e : Fin n ≃ ι)
    (F : ι → Matrices.ComplexMatrix2) :
    Matrices.ComplexMatrix2.familyDiameter (F ∘ e) = Matrices.ComplexMatrix2.familyDiameter F :=
  (e.prodCongr e).iSup_comp
    (g := fun p : ι × ι => Matrices.ComplexMatrix2.operatorNorm (F p.1 * (F p.2)⁻¹ - 1))
theorem isNearLogMean_complexLogMean {ι : Type*} [Fintype ι] [Nonempty ι]
    (hm : ∀ n : ℕ, 1 ≤ n → Averaging.ComplexLogMeanProperties n)
    (F : ι → Matrices.ComplexMatrix2)
    (hF : ∀ i, F i ∈ PeriodicLattice.complexGaugeGroup)
    (hd : Matrices.ComplexMatrix2.familyDiameter F < Averaging.centreOfMassDiameter) :
    IsNearLogMean F (PeriodicLattice.complexLogMean F) ∧
      ∀ W, IsNearLogMean F W → W = PeriodicLattice.complexLogMean F := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hV : F ∘ e ∈ Averaging.smallComplexFamilies (Fintype.card ι) :=
    ⟨fun i => hF _, by rw [familyDiameter_comp_equiv]; exact hd⟩
  obtain ⟨W, hW, hu⟩ := (hm _ Fintype.card_pos).existsUnique _ hV
  have hs : IsNearLogMean F (PeriodicLattice.complexLogMean F) :=
    Classical.epsilon_spec (p := IsNearLogMean F) ⟨W, (isNearLogMean_comp_equiv_iff e F W).1 hW⟩
  exact ⟨hs, fun W' hW' =>
    (hu W' ((isNearLogMean_comp_equiv_iff e F W').2 hW')).trans
      (hu _ ((isNearLogMean_comp_equiv_iff e F _).2 hs)).symm⟩
theorem nonempty_contourOrder {L : ℕ} {a a' : ℝ} (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a') : Nonempty (FullSpace.ContourOrder L y x) :=
  ⟨(Finset.equivFin (FullSpace.offsetSupport L y x)).symm⟩
section Domain
variable {L k j : ℕ}
theorem contourHolonomies_mem (pt : FullSpace.PathsStayInCubes L k j)
    {c : FullSpace.Edge L k j}
    {U : FullSpace.Edge L k (j - 1) → Matrices.ComplexMatrix2}
    (hU : U ∈ FullSpace.complexDomain L c)
    {y : FullSpace.Vertex L k j}
    (hy : y ∈ ({c.initial, c.terminal} : Set (FullSpace.Vertex L k j)))
    {x : FullSpace.Vertex L k (j - 1)}
    (hx : x ∈ FullSpace.cubeVertices L (meshAt L k (j - 1)) y)
    (σ : FullSpace.ContourOrder L y x) :
    FullSpace.contourHolonomies L U y x σ ∈ PeriodicLattice.complexGaugeGroup := by
  have hblock : ∀ p : AmbientSpace, p ∈ FullSpace.cube L (meshAt L k (j - 1)) y →
      p ∈ FullSpace.doubleCube L (meshAt L k (j - 1)) c := by
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Or.inl hp
    · exact Or.inr hp
  refine linkHolonomy_mem fun b hb => hU.1.1 b ?_
  have hΓ : FullSpace.contour L y x σ ∈ FullSpace.contourSet L y x := ⟨σ, rfl⟩
  exact ⟨hblock _ (pt.contour_vertex_mem y x hx _ hΓ b.initial
      (Or.inr (Or.inr ⟨b, hb, Or.inl rfl⟩))),
    hblock _ (pt.contour_vertex_mem y x hx _ hΓ b.terminal
      (Or.inr (Or.inr ⟨b, hb, Or.inr rfl⟩)))⟩
theorem familyDiameter_contourHolonomies_lt {c : FullSpace.Edge L k j}
    {U : FullSpace.Edge L k (j - 1) → Matrices.ComplexMatrix2}
    (hU : U ∈ FullSpace.complexDomain L c)
    {y : FullSpace.Vertex L k j}
    (hy : y ∈ ({c.initial, c.terminal} : Set (FullSpace.Vertex L k j)))
    {x : FullSpace.Vertex L k (j - 1)}
    (hx : x ∈ FullSpace.cubeVertices L (meshAt L k (j - 1)) y) :
    Matrices.ComplexMatrix2.familyDiameter (FullSpace.contourHolonomies L U y x) <
      Averaging.centreOfMassDiameter := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact hU.2.1 x hx
  · exact hU.2.2 x hx
theorem transportAlong_mem_of_domain (hn : InfiniteLattice.latticeSubgroup (meshAt L k j) ≤
      InfiniteLattice.latticeSubgroup (meshAt L k (j - 1)))
    (hp : FullSpace.CubesOfOrderPartition L k j 1) (pt : FullSpace.PathsStayInCubes L k j)
    {c : FullSpace.Edge L k j} {U : FullSpace.Edge L k (j - 1) → Matrices.ComplexMatrix2}
    (hU : U ∈ FullSpace.complexDomain L c) :
    FullSpace.transportAlong U c ∈ PeriodicLattice.complexGaugeGroup := by
  have hx0 : ((FullSpace.toFiner (meshAt L k (j - 1)) c.initial :
      FullSpace.Vertex L k (j - 1)) : AmbientSpace) ∈
        FullSpace.cube L (meshAt L k (j - 1)) c.initial := by
    rw [coe_toFiner hn]
    exact hp.center_mem c.initial
  have ht : FullSpace.shifted c (FullSpace.toFiner (meshAt L k (j - 1)) c.initial) =
      FullSpace.toFiner (meshAt L k (j - 1)) c.terminal := by
    apply Subtype.ext
    rw [coe_shifted hn, coe_toFiner hn, coe_toFiner hn]
    abel
  refine linkHolonomy_mem fun b hb => hU.1.1 b ?_
  have hb' : b ∈ FullSpace.crossingPath c (FullSpace.toFiner (meshAt L k (j - 1)) c.initial) := by
    unfold FullSpace.crossingPath
    rw [ht]
    exact hb
  exact ⟨pt.crossing_vertex_mem c _ hx0 _ (Or.inr (Or.inr ⟨b, hb', Or.inl rfl⟩)),
    pt.crossing_vertex_mem c _ hx0 _ (Or.inr (Or.inr ⟨b, hb', Or.inr rfl⟩))⟩
end Domain
theorem cubesAtInfinity_of {L k j : ℕ} (hL : 0 < L) (hj : 1 ≤ j)
    (hn : InfiniteLattice.latticeSubgroup (meshAt L k j) ≤
      InfiniteLattice.latticeSubgroup (meshAt L k (j - 1)))
    (hp : FullSpace.CubesOfOrderPartition L k j 1) (st : FullSpace.StepsEdgesAndCorridors L k j)
    (pt : FullSpace.PathsStayInCubes L k j)
    (hS : AxisPathUniqueness.OnFullSpace L k (j - 1))
    (hm : ∀ n : ℕ, 1 ≤ n → Averaging.ComplexLogMeanProperties n) :
    CubesAtInfinity L k j := by
  have hpos : meshAt L k (j - 1) ≠ 0 :=
    (zpow_pos (Nat.cast_pos.2 hL) _).ne'
  have hmean : ∀ (c : FullSpace.Edge L k j)
      (U : FullSpace.Edge L k (j - 1) → Matrices.ComplexMatrix2),
      U ∈ FullSpace.complexDomain L c →
      ∀ y ∈ ({c.initial, c.terminal} : Set (FullSpace.Vertex L k j)),
      ∀ x ∈ FullSpace.cubeVertices L (meshAt L k (j - 1)) y,
        IsNearLogMean (FullSpace.contourHolonomies L U y x)
            (FullSpace.complexContourMean L U y x) ∧
          ∀ W, IsNearLogMean (FullSpace.contourHolonomies L U y x) W →
            W = FullSpace.complexContourMean L U y x := fun c U hU y hy x hx =>
    haveI := nonempty_contourOrder (L := L) y x
    isNearLogMean_complexLogMean hm _ (contourHolonomies_mem pt hU hy hx)
      (familyDiameter_contourHolonomies_lt hU hy hx)
  exact
    { toFiner_coe := coe_toFiner hn
      axis_endpoints := fun c => exists_axisDisplacement hL hj c (by
        rw [coe_toFiner hn, coe_toFiner hn])
      axis_shifted := fun c x _ => exists_axisDisplacement hL hj c (by
        rw [coe_shifted hn]
        abel)
      shifted_mem := fun c x hx => by
        have h := hp.cube_add c.initial (c.terminal - c.initial)
        rw [add_sub_cancel] at h
        show ((FullSpace.shifted c x : FullSpace.Vertex L k (j - 1)) : AmbientSpace) ∈
          FullSpace.cubeOfOrder L (meshAt L k (j - 1)) 1 c.terminal
        rw [h, coe_shifted hn]
        exact ⟨x, hx, rfl⟩
      existsUnique_pivotLink := existsUnique_pivotLink_of_corridors hL hj hn st hS
      existsUnique_cubeOffset := fun y x hx => existsUnique_cubeOffset_of_mem hpos y x hx
      cubeVertices_finite := fun y => Set.finite_of_ncard_pos (by
        rw [ncard_cubeVertices hp]
        exact pow_pos hL 4)
      cubeVertices_ncard := ncard_cubeVertices hp
      complexContourMean_isNearLogMean := hmean
      complexContourMean_mem := fun c U hU y hy x hx => (hmean c U hU y hy x hx).1.1.1
      transportAlong_mem := fun c U hU => transportAlong_mem_of_domain hn hp pt hU }
theorem statement_holds (h₁ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (h₂ : FullSpace.CubesCorridorsPivotEdgesAndPaths)
    (h₃ : AxisPathUniqueness.AxisPathsUnique) (h₄ : Averaging.ComplexLogMeanOfSmallFamilies) :
    Statement := by
  intro L hs
  have hL : 0 < L := by
    have := hs.2
    omega
  refine ⟨fun k j hjk => ⟨fun n hn => ?_, ?_⟩, fun k j hj hjk => ?_⟩
  · obtain ⟨-, -, -, hside, -⟩ := h₁ L hL hs k
    refine ⟨⟨fun _ _ => Matrices.ComplexMatrix2.specialUnitary.one_mem, fun _ _ => by simp⟩,
      fun _ => Matrices.ComplexMatrix2.specialUnitary.one_mem, fun f hf hl => ?_⟩
    exact imagesOnSide_of_distancePreserving hf hl ((hside n hn j hjk f hf hl).2 j le_rfl).2.1
  · obtain ⟨-, -, -, -, hwhole, -⟩ := h₁ L hL hs k
    refine ⟨⟨fun _ => Matrices.ComplexMatrix2.specialUnitary.one_mem, fun _ => by simp⟩,
      fun _ => Matrices.ComplexMatrix2.specialUnitary.one_mem, fun f hf hl => ?_⟩
    exact imagesAtInfinity_of_distancePreserving hf hl ((hwhole j hjk f hf hl).2.1 j le_rfl).2.1
  · obtain ⟨hp, -, st, pt⟩ := h₂ L hs k j 1 (by omega) hj hjk le_rfl hj
    obtain ⟨-, hnest, -⟩ := h₁ L hL hs k
    exact cubesAtInfinity_of hL hj (hnest (j - 1) j (by omega) hjk) hp st pt
      (h₃ L hs k (j - 1) (by omega)).2 h₄.2.2.2.1
end Tower.SelectedObjects
end
end YangMills.Construction
