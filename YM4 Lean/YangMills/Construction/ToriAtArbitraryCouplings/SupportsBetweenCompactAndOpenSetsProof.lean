import YangMills.Construction.PassageToTheLimit.PartitionOfUnityOfClassC1WithSmallPiecesProof
import YangMills.Construction.ToriAtArbitraryCouplings.SupportsBetweenCompactAndOpenSets
import YangMills.Construction.ToriAtArbitraryCouplings.TheEuclideanDistanceAndTheCoveringMapProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
open YangMills.Construction.MetricNotions (IsCompactWrt IsOpenWrt)
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace SupportsBetweenCompactOpen
section Metric
variable {X : Type} [MetricSpace X]
private theorem isOpenWrt_dist_iff (U : Set X) : IsOpenWrt (dist : X → X → ℝ) U ↔ IsOpen U := by
  rw [Metric.isOpen_iff]
  refine forall₂_congr fun x _ => ?_
  constructor
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, fun y hy => h y (by rwa [dist_comm, ← Metric.mem_ball])⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, fun y hy => h (by rwa [Metric.mem_ball, dist_comm])⟩
private theorem isCompact_of_isCompactWrt {Z : Set X}
    (hZ : IsCompactWrt (dist : X → X → ℝ) Z) : IsCompact Z := by
  refine isCompact_of_finite_subcover fun {ι} U hU hcov => ?_
  obtain ⟨𝒰, hsub, hfin, hcov'⟩ := hZ (Set.range U)
    (by rintro _ ⟨i, rfl⟩; exact (isOpenWrt_dist_iff _).2 (hU i)) (by rwa [Set.sUnion_range])
  classical
  have hpick : ∀ V ∈ 𝒰, ∃ i, U i = V := fun V hV => hsub hV
  choose g hg using hpick
  refine ⟨hfin.toFinset.attach.image fun V => g V.1 (hfin.mem_toFinset.1 V.2), fun x hx => ?_⟩
  obtain ⟨V, hV, hxV⟩ := hcov' hx
  refine Set.mem_iUnion₂.2 ⟨g V hV, Finset.mem_image.2
    ⟨⟨V, hfin.mem_toFinset.2 hV⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
  rw [hg V hV]
  exact hxV
private theorem IsCompact.exists_uniform_margin {P W : Set X} (hP : IsCompact P) (hW : IsOpen W)
    (hPW : P ⊆ W) : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ P, ∀ y, dist x y < δ → y ∈ W := by
  obtain ⟨δ, hδ, hsub⟩ := hP.exists_thickening_subset_open hW hPW
  exact ⟨δ, hδ, fun x hx y hy =>
    hsub (Metric.mem_thickening_iff.2 ⟨x, hx, by rwa [dist_comm]⟩)⟩
private theorem exists_pos_lower_bound {ι : Type} [Finite ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ f i := by
  rcases isEmpty_or_nonempty ι with he | he
  · exact ⟨1, one_pos, fun i => (he.false i).elim⟩
  · obtain ⟨i, hi⟩ := Finite.exists_min f
    exact ⟨f i, hf i, hi⟩
private theorem exists_disjoint_open_shrink {n : ℕ} {P W : Fin n → Set X}
    (hP : ∀ i, IsCompact (P i))
    (hdis : Pairwise (Function.onFun Disjoint P)) (hW : ∀ i, IsOpen (W i))
    (hPW : ∀ i, P i ⊆ W i) :
    ∃ W' : Fin n → Set X, (∀ i, IsOpen (W' i)) ∧ (∀ i, P i ⊆ W' i) ∧ (∀ i, W' i ⊆ W i) ∧
      Pairwise (Function.onFun Disjoint W') := by
  have hpair : ∀ p : Fin n × Fin n, ∃ δ : ℝ, 0 < δ ∧ (p.1 ≠ p.2 →
      Disjoint (Metric.thickening δ (P p.1)) (Metric.thickening δ (P p.2))) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨1, one_pos, fun h => (h hp).elim⟩
    · obtain ⟨δ, hδ, h⟩ := Disjoint.exists_thickenings (hdis hp) (hP p.1) (hP p.2).isClosed
      exact ⟨δ, hδ, fun _ => h⟩
  choose δ hδ hδ' using hpair
  obtain ⟨ε, hε, hle⟩ := exists_pos_lower_bound δ hδ
  refine ⟨fun i => W i ∩ Metric.thickening ε (P i),
    fun i => (hW i).inter Metric.isOpen_thickening,
    fun i => subset_inter (hPW i) (Metric.self_subset_thickening hε _),
    fun i => inter_subset_left, ?_⟩
  intro i k hik
  exact Disjoint.mono (inter_subset_right.trans (Metric.thickening_mono (hle (i, k)) _))
    (inter_subset_right.trans (Metric.thickening_mono (hle (i, k)) _)) (hδ' (i, k) hik)
end Metric
section Distance
variable {X : Type} {d : X → X → ℝ}
private structure IsMetricFn (d : X → X → ℝ) : Prop where
  self_eq_zero : ∀ x, d x x = 0
  symm : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x z ≤ d x y + d y z
  eq_of_eq_zero : ∀ x y, d x y = 0 → x = y
private abbrev IsMetricFn.toMetricSpace (h : IsMetricFn d) : MetricSpace X :=
  { dist := d
    dist_self := h.self_eq_zero
    dist_comm := h.symm
    dist_triangle := h.triangle
    eq_of_dist_eq_zero := fun {x y} => h.eq_of_eq_zero x y }
private theorem exists_margin (h : IsMetricFn d) {P W : Set X} (hP : IsCompactWrt d P)
    (hW : IsOpenWrt d W) (hPW : P ⊆ W) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ P, ∀ y, d x y < δ → y ∈ W := by
  let := h.toMetricSpace
  exact IsCompact.exists_uniform_margin (isCompact_of_isCompactWrt hP)
    ((isOpenWrt_dist_iff W).1 hW) hPW
private theorem exists_bound_of_isCompactWrt (h : IsMetricFn d) {P : Set X}
    (hP : IsCompactWrt d P) (c : X) :
    ∃ r : ℝ, ∀ x ∈ P, d c x ≤ r := by
  let := h.toMetricSpace
  obtain ⟨r, hr⟩ := Metric.isBounded_iff_subset_closedBall c |>.1
    (isCompact_of_isCompactWrt hP).isBounded
  refine ⟨r, fun x hx => ?_⟩
  have hx' : dist x c ≤ r := Metric.mem_closedBall.1 (hr hx)
  rwa [dist_comm] at hx'
private theorem exists_disjoint_shrink (h : IsMetricFn d) {n : ℕ} {P W : Fin n → Set X}
    (hP : ∀ i, IsCompactWrt d (P i)) (hdis : Pairwise (Function.onFun Disjoint P))
    (hW : ∀ i, IsOpenWrt d (W i)) (hPW : ∀ i, P i ⊆ W i) :
    ∃ W' : Fin n → Set X, (∀ i, IsOpenWrt d (W' i)) ∧ (∀ i, P i ⊆ W' i) ∧ (∀ i, W' i ⊆ W i) ∧
      Pairwise (Function.onFun Disjoint W') := by
  let := h.toMetricSpace
  obtain ⟨W', h1, h2, h3, h4⟩ := exists_disjoint_open_shrink
    (fun i => isCompact_of_isCompactWrt (hP i))
    hdis (fun i => (isOpenWrt_dist_iff (W i)).1 (hW i)) hPW
  exact ⟨W', fun i => (isOpenWrt_dist_iff (W' i)).2 (h1 i), h2, h3, h4⟩
end Distance
private def meshCell (η : ℚ) (k : Fin 4 → ℤ) : Set (Fin 4 → ℝ) :=
  Set.pi univ fun μ => Icc (((k μ : ℚ) * η : ℚ) : ℝ) ((((k μ : ℚ) + 1) * η : ℚ) : ℝ)
private theorem meshCell_isRationalBox {η : ℚ} (hη : 0 < η) (k : Fin 4 → ℤ) :
    IsRationalBox (meshCell η k) :=
  ⟨fun μ => (k μ : ℚ) * η, fun μ => ((k μ : ℚ) + 1) * η,
    fun μ => mul_lt_mul_of_pos_right (by linarith) hη, rfl⟩
private theorem mem_meshCell_iff {η : ℚ} {k : Fin 4 → ℤ} {u : Fin 4 → ℝ} :
    u ∈ meshCell η k ↔ ∀ μ, (k μ : ℝ) * η ≤ u μ ∧ u μ ≤ ((k μ : ℝ) + 1) * η := by
  rw [meshCell, Set.mem_pi]
  refine forall_congr' fun μ => ?_
  simp
private theorem mem_meshCell_floor {η : ℚ} (hη : 0 < η) (u : Fin 4 → ℝ) :
    u ∈ meshCell η (fun μ => ⌊u μ / (η : ℝ)⌋) := by
  have h : (0 : ℝ) < η := by exact_mod_cast hη
  refine mem_meshCell_iff.2 fun μ => ⟨?_, ?_⟩
  · exact (le_div_iff₀ h).1 (Int.floor_le (u μ / (η : ℝ)))
  · exact (div_le_iff₀ h).1 (Int.lt_floor_add_one (u μ / (η : ℝ))).le
private theorem abs_sub_le_of_mem_meshCell {η : ℚ} {k : Fin 4 → ℤ} {u v : Fin 4 → ℝ}
    (hu : u ∈ meshCell η k) (hv : v ∈ meshCell η k) (μ : Fin 4) : |u μ - v μ| ≤ η := by
  obtain ⟨a, b⟩ := mem_meshCell_iff.1 hu μ
  obtain ⟨c, e⟩ := mem_meshCell_iff.1 hv μ
  rw [abs_le]
  constructor <;> linarith
private theorem euclidNormVec_le_two_mul {w : Fin 4 → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ μ, |w μ| ≤ c) : euclidNormVec w ≤ 2 * c := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.euclidNormVec_le <;> assumption
private theorem abs_apply_le_euclidNormVec (w : Fin 4 → ℝ) (μ : Fin 4) :
    |w μ| ≤ euclidNormVec w := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem finite_meshCells_meeting {η : ℚ} (hη : 0 < η) {K : Set (Fin 4 → ℝ)} {R : ℝ}
    (hK : ∀ u ∈ K, ∀ μ, |u μ| ≤ R) : {k : Fin 4 → ℤ | ∃ u ∈ K, u ∈ meshCell η k}.Finite := by
  have h : (0 : ℝ) < η := by exact_mod_cast hη
  obtain ⟨N, hN⟩ := exists_nat_ge (R / (η : ℝ) + 1)
  have hN' : R + η ≤ N * η := by
    have h1 := mul_le_mul_of_nonneg_right hN h.le
    have h2 : (R / (η : ℝ) + 1) * η = R + η := by field_simp
    linarith
  refine (Set.finite_Icc (fun _ => -(N : ℤ)) (fun _ => (N : ℤ))).subset ?_
  rintro k ⟨u, hu, hk⟩
  refine ⟨fun μ => ?_, fun μ => ?_⟩
  · obtain ⟨a, b⟩ := mem_meshCell_iff.1 hk μ
    obtain ⟨c, e⟩ := abs_le.1 (hK u hu μ)
    have h3 : (-(N : ℝ)) ≤ k μ := le_of_mul_le_mul_right (by linarith) h
    exact_mod_cast h3
  · obtain ⟨a, b⟩ := mem_meshCell_iff.1 hk μ
    obtain ⟨c, e⟩ := abs_le.1 (hK u hu μ)
    have h3 : (k μ : ℝ) ≤ N := le_of_mul_le_mul_right (by linarith) h
    exact_mod_cast h3
private theorem exists_meshCells_between {X : Type} {d : X → X → ℝ} (π : (Fin 4 → ℝ) → X)
    (hπ : ∀ u v, d (π u) (π v) ≤ euclidNormVec (u - v)) {K : Set (Fin 4 → ℝ)} {R : ℝ}
    (hK : ∀ u ∈ K, ∀ μ, |u μ| ≤ R) {P W : Set X} (hPK : P ⊆ π '' K) {δ : ℝ}
    (hW : ∀ x ∈ P, ∀ y, d x y < δ → y ∈ W) {η : ℚ} (hη : 0 < η) (h2 : 2 * (η : ℝ) < δ) :
    ∃ B : Set (Fin 4 → ℤ), B.Finite ∧ P ⊆ ⋃ k ∈ B, π '' meshCell η k ∧
      (⋃ k ∈ B, π '' meshCell η k) ⊆ W := by
  have h : (0 : ℝ) < η := by exact_mod_cast hη
  refine ⟨{k | ∃ u ∈ K, π u ∈ P ∧ u ∈ meshCell η k},
    (finite_meshCells_meeting hη hK).subset ?_, ?_, ?_⟩
  · rintro k ⟨u, hu, -, hk⟩
    exact ⟨u, hu, hk⟩
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := hPK hx
    exact mem_iUnion₂.2 ⟨_, ⟨u, hu, hx, mem_meshCell_floor hη u⟩, u, mem_meshCell_floor hη u, rfl⟩
  · intro y hy
    obtain ⟨k, ⟨u, -, hPu, huk⟩, v, hv, rfl⟩ := mem_iUnion₂.1 hy
    exact hW _ hPu _ (lt_of_le_of_lt (hπ u v) (lt_of_le_of_lt
      (euclidNormVec_le_two_mul h.le fun μ => abs_sub_le_of_mem_meshCell huk hv μ) h2))
private theorem exists_rat_mesh {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    ∃ η : ℚ, 0 < η ∧ 2 * (η : ℝ) < δ ∧ (η : ℝ) < c := by
  obtain ⟨η, h0, h1⟩ := exists_rat_btwn (lt_min (half_pos hδ) hc)
  refine ⟨η, by exact_mod_cast h0, ?_, lt_of_lt_of_le h1 (min_le_right _ _)⟩
  have := lt_of_lt_of_le h1 (min_le_left _ _)
  linarith
private theorem length_pos (s : TorusSide) : 0 < s.length := by apply _root_.YangMills.Construction.ToriAtArbitraryCouplings.DistanceAndProjection.length_pos <;> assumption
private theorem isMetricFn_pointDist (s : TorusSide) (E : Ambient) :
    IsMetricFn (s.pointDist E) := by
  cases E
  · exact ⟨fun x => AmbientPoints.torusEuclidNorm_sub_self x,
      fun x y => AmbientPoints.torusEuclidNorm_sub_comm x y,
      fun x y z => AmbientPoints.torusEuclidNorm_sub_le x y z,
      fun x y => AmbientPoints.eq_of_torusEuclidNorm_sub_eq_zero x y⟩
  · exact ⟨fun x => AmbientPoints.euclidNormVec_sub_self x,
      fun x y => AmbientPoints.euclidNormVec_sub_comm x y,
      fun x y z => AmbientPoints.euclidNormVec_sub_le x y z,
      fun x y => AmbientPoints.eq_of_euclidNormVec_sub_eq_zero x y⟩
private theorem injOn_proj_meshCell (s : TorusSide) {η : ℚ} (hc : (η : ℝ) < s.length)
    (k : Fin 4 → ℤ) : InjOn s.proj (meshCell η k) := by
  have hℓ := length_pos s
  intro u hu v hv h
  funext μ
  have hμ : ((u μ : ℝ) : AddCircle (PeriodicLattice.torusSide s.L s.m)) = (v μ : ℝ) :=
    congrFun h μ
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1
    (show ((u μ - v μ : ℝ) : AddCircle (PeriodicLattice.torusSide s.L s.m)) = 0 by
      rw [AddCircle.coe_sub, hμ, sub_self])
  have hab := abs_sub_le_of_mem_meshCell hu hv μ
  rw [← hn, zsmul_eq_mul, abs_mul] at hab
  have hn0 : n = 0 := by
    by_contra h0
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs h0
    have h3 : |PeriodicLattice.torusSide s.L s.m| = s.length := abs_of_pos hℓ
    rw [h3] at hab
    nlinarith
  rw [hn0] at hn
  exact sub_eq_zero.1 (by simpa using hn.symm)
private theorem exists_short_lift (s : TorusSide) (x : s.asMirrorData.Torus) :
    ∃ u : Fin 4 → ℝ, (∀ μ, |u μ| ≤ s.length) ∧ s.proj u = x := by
  have hℓ := length_pos s
  choose b hb hb' using fun μ => exists_coe_eq_abs_eq_norm (x μ)
  refine ⟨b, fun μ => ?_, funext hb⟩
  rw [hb']
  have h1 : ‖x μ‖ ≤ |PeriodicLattice.torusSide s.L s.m| / 2 :=
    AddCircle.norm_le_half_period _ (ne_of_gt hℓ)
  have h3 : |PeriodicLattice.torusSide s.L s.m| = s.length := abs_of_pos hℓ
  rw [h3] at h1
  linarith
private theorem exists_support_between (s : TorusSide) (E : Ambient) {P W : Set (s.Point E)}
    (hP : s.IsCompactWrt E P) (hW : s.IsOpenWrt E W) (hPW : P ⊆ W) :
    ∃ Q ∈ s.supportFamily E, P ⊆ Q ∧ Q ⊆ W := by
  obtain ⟨δ, hδ, hm⟩ := exists_margin (isMetricFn_pointDist s E) hP hW hPW
  obtain ⟨η, h0, h2, hc⟩ := exists_rat_mesh hδ (length_pos s)
  cases E
  · obtain ⟨B, hB, h1, h3⟩ := exists_meshCells_between (d := s.pointDist .torus) s.proj
      (fun u v => by
        have h := AmbientPoints.torusEuclidNorm_torusProj_le
          (S := PeriodicLattice.torusSide s.L s.m) (u - v)
        exact h)
      (K := {u | ∀ μ, |u μ| ≤ s.length}) (fun u hu => hu)
      (fun x _ => by
        obtain ⟨u, hu, hx⟩ := exists_short_lift s x
        exact ⟨u, hu, hx⟩) hm h0 h2
    refine ⟨_, ⟨meshCell η '' B, hB.image _, ?_, biUnion_image.symm⟩, h1, h3⟩
    rintro _ ⟨k, -, rfl⟩
    exact ⟨meshCell_isRationalBox h0 k, injOn_proj_meshCell s hc k⟩
  · obtain ⟨r, hr⟩ := exists_bound_of_isCompactWrt (isMetricFn_pointDist s .euclidean) hP
      (0 : Fin 4 → ℝ)
    obtain ⟨B, hB, h1, h3⟩ := exists_meshCells_between (X := Fin 4 → ℝ)
      (d := s.pointDist .euclidean) id
      (fun u v => le_refl _) (K := P) (R := r)
      (fun u hu μ => by
        have h := abs_apply_le_euclidNormVec (0 - u) μ
        have h' : euclidNormVec (0 - u) ≤ r := hr u hu
        simpa using h.trans h')
      (fun x hx => ⟨x, hx, rfl⟩) hm h0 h2
    simp only [image_id] at h1 h3
    refine ⟨_, ⟨meshCell η '' B, hB.image _, ?_, (sUnion_image _ _).symm⟩, h1, h3⟩
    rintro _ ⟨k, -, rfl⟩
    exact meshCell_isRationalBox h0 k
theorem statement_holds : Statement := by
  intro s E
  refine ⟨fun P W hP hW hPW => exists_support_between s E hP hW hPW,
    fun n P W hP hdis hW hPW => ?_⟩
  obtain ⟨W', hW', hPW', hsub, hdis'⟩ :=
    exists_disjoint_shrink (isMetricFn_pointDist s E) hP hdis hW hPW
  choose Q hQ hQ1 hQ2 using fun i => exists_support_between s E (hP i) (hW' i) (hPW' i)
  exact ⟨Q, hQ, fun i => ⟨hQ1 i, (hQ2 i).trans (hsub i)⟩,
    fun i k hik => Disjoint.mono (hQ2 i) (hQ2 k) (hdis' hik)⟩
end SupportsBetweenCompactOpen
end YangMills.Construction.ToriAtArbitraryCouplings
end
