import YangMills.Construction.Torus.BallOfTheTorusAndTheBallOverItProof
import YangMills.Construction.Torus.ProjectionToTheTorusDoesNotIncreaseVolume
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set TorusMetric TestFunctions
open TorusCovering
  (ProjectionProperties IntegralProperties VolumeProperties IsBddMeasurable periodVec)
namespace TorusMeasure.TranslatedLatticeCells
variable {s : Conventions.StandingParameters}
theorem torusSide_pos (s : Conventions.StandingParameters) : 0 < PeriodicLattice.torusSide s.L s.m := by
  have hL : 0 < s.L := by
    have := s.isAdmissible.2
    omega
  unfold PeriodicLattice.torusSide
  positivity
theorem euclidNormVec_eq_norm (v : Fin 4 → ℝ) :
    euclidNormVec v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 4))‖ := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_eq_norm <;> assumption
theorem euclidNormVec_neg (v : Fin 4 → ℝ) : euclidNormVec (-v) = euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem euclidNormVec_add_le (v v' : Fin 4 → ℝ) :
    euclidNormVec (v + v') ≤ euclidNormVec v + euclidNormVec v' := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem euclidNormVec_zero : euclidNormVec 0 = 0 := by simp [euclidNormVec]
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem proj_map_add (v v' : Fin 4 → ℝ) :
    proj s (v + v') = proj s v + proj s v' := by apply _root_.YangMills.Construction.TorusMeasure.BallProjection.proj_map_add <;> assumption
theorem proj_map_zero : proj s 0 = 0 := by
  funext μ
  simp [proj, torusProj]
theorem proj_map_neg (v : Fin 4 → ℝ) : proj s (-v) = -proj s v := by
  funext μ
  simp [proj, torusProj]
theorem proj_map_sub (v v' : Fin 4 → ℝ) :
    proj s (v - v') = proj s v - proj s v' := by apply _root_.YangMills.Construction.TorusMeasure.BallProjection.proj_map_sub <;> assumption
theorem proj_exists_preimage (p : s.Torus) : ∃ v, proj s v = p :=
  torusProj_surjective (PeriodicLattice.torusSide s.L s.m) p
theorem proj_add_latticeTranslate_eq (v : Fin 4 → ℝ) (k : Fin 4 → ℤ) :
    proj s (v + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) = proj s v :=
  torusProj_add_latticeTranslate _ _ _
theorem exists_latticeTranslate_of_proj_eq {v v' : Fin 4 → ℝ}
    (h : proj s v = proj s v') :
    ∃ k, v = v' + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k :=
  exists_latticeTranslate_of_torusProj_eq h
theorem int_eq_zero_of_abs_mul_lt {ρ : ℝ} (hρ : 0 < ρ) {k : ℤ} (h : |ρ * (k : ℝ)| < ρ) : k = 0 := by
  rw [abs_mul, abs_of_pos hρ] at h
  have h1 : |(k : ℝ)| < 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  have h2 : |k| < 1 := by exact_mod_cast h1
  exact Int.abs_lt_one_iff.1 h2
theorem exists_lift_norm_eq_pointNorm (H : ProjectionProperties s) (p : s.Torus) :
    ∃ v, proj s v = p ∧ euclidNormVec v = pointNorm p := by apply _root_.YangMills.Construction.TorusMeasure.BallProjection.exists_lift_normVec_eq_pointNorm <;> assumption
theorem pointNorm_proj_le (H : ProjectionProperties s) (v : Fin 4 → ℝ) :
    pointNorm (proj s v) ≤ euclidNormVec v := by
  obtain ⟨_, _, _, hlift, _, _, _, _, _, hleast⟩ := H
  exact (hleast _).2 ⟨v, (hlift _ _).2 rfl, rfl⟩
theorem pointNorm_nonneg (H : ProjectionProperties s) (p : s.Torus) : 0 ≤ pointNorm p := by
  obtain ⟨v, -, he⟩ := exists_lift_norm_eq_pointNorm H p
  exact he ▸ euclidNormVec_nonneg v
theorem pointNorm_neg_le (H : ProjectionProperties s) (p : s.Torus) :
    pointNorm (-p) ≤ pointNorm p := by
  obtain ⟨v, rfl, he⟩ := exists_lift_norm_eq_pointNorm H p
  rw [← he, ← proj_map_neg, ← euclidNormVec_neg]
  exact pointNorm_proj_le H _
theorem pointNorm_neg (H : ProjectionProperties s) (p : s.Torus) :
    pointNorm (-p) = pointNorm p :=
  le_antisymm (pointNorm_neg_le H p) (by simpa using pointNorm_neg_le H (-p))
theorem pointNorm_add_le (H : ProjectionProperties s) (p q : s.Torus) :
    pointNorm (p + q) ≤ pointNorm p + pointNorm q := by
  obtain ⟨v, rfl, he⟩ := exists_lift_norm_eq_pointNorm H p
  obtain ⟨v', rfl, he'⟩ := exists_lift_norm_eq_pointNorm H q
  rw [← he, ← he', ← proj_map_add]
  exact (pointNorm_proj_le H _).trans (euclidNormVec_add_le _ _)
theorem pointDist_eq_pointNorm_sub (p q : s.Torus) : pointDist p q = pointNorm (p - q) := rfl
theorem pointDist_symm (H : ProjectionProperties s) (p q : s.Torus) :
    pointDist q p = pointDist p q := by
  rw [pointDist_eq_pointNorm_sub, pointDist_eq_pointNorm_sub, ← neg_sub p q, pointNorm_neg H]
theorem pointDist_triangle (H : ProjectionProperties s) (p q r : s.Torus) :
    pointDist p q ≤ pointDist p r + pointDist r q := by
  simp only [pointDist_eq_pointNorm_sub]
  have h : p - q = (p - r) + (r - q) := by abel
  rw [h]
  exact pointNorm_add_le H _ _
theorem distanceProperties_holds (H : ProjectionProperties s) : DistanceProperties s :=
  ⟨fun p q r => ⟨pointDist_symm H p q, pointDist_triangle H p q r⟩, pointNorm_proj_le H⟩
abbrev centeredCube (a : ℝ) : Set (Fin 4 → ℝ) := Set.pi univ fun _ : Fin 4 => Ico (-(a / 2)) (a / 2)
theorem euclidNormVec_le_of_mem_centeredCube {a : ℝ} (ha : 0 < a) {τ : Fin 4 → ℝ}
    (hτ : τ ∈ centeredCube a) : euclidNormVec τ ≤ a := by
  have h : ∀ μ, τ μ ^ 2 ≤ a ^ 2 / 4 := by
    intro μ
    obtain ⟨h1, h2⟩ := hτ μ (mem_univ μ)
    nlinarith [mul_nonneg (sub_nonneg.2 h2.le) (by linarith : 0 ≤ a / 2 + τ μ)]
  unfold euclidNormVec
  refine Real.sqrt_le_iff.2 ⟨ha.le, ?_⟩
  rw [Fin.sum_univ_four]
  linarith [h 0, h 1, h 2, h 3]
theorem exists_int_shift_mem_centeredCube {a : ℝ} (ha : 0 < a) (v : Fin 4 → ℝ) :
    ∃ k : Fin 4 → ℤ, (fun μ => v μ - a * (k μ : ℝ)) ∈ centeredCube a := by
  refine ⟨fun μ => ⌊v μ / a + 1 / 2⌋, fun μ _ => ?_⟩
  have h1 := Int.floor_le (v μ / a + 1 / 2)
  have h2 := Int.lt_floor_add_one (v μ / a + 1 / 2)
  have hv : v μ = a * (v μ / a) := by field_simp
  constructor
  · have := mul_lt_mul_of_pos_left h2 ha
    simp only
    nlinarith
  · have := mul_le_mul_of_nonneg_left h1 ha.le
    simp only
    nlinarith
theorem pointNorm_le_torusSide (H : ProjectionProperties s) (p : s.Torus) :
    pointNorm p ≤ PeriodicLattice.torusSide s.L s.m := by
  have hℓ := torusSide_pos s
  obtain ⟨v, rfl⟩ := proj_exists_preimage p
  obtain ⟨k, hk⟩ := exists_int_shift_mem_centeredCube hℓ v
  have h : proj s v =
      proj s ((fun μ => v μ - PeriodicLattice.torusSide s.L s.m * (k μ : ℝ))) := by
    rw [← proj_add_latticeTranslate_eq (s := s)
      (fun μ => v μ - PeriodicLattice.torusSide s.L s.m * (k μ : ℝ)) k]
    congr 1
    funext μ
    simp [latticeTranslate]
  rw [h]
  exact (pointNorm_proj_le H _).trans (euclidNormVec_le_of_mem_centeredCube hℓ hk)
theorem torusVolume_nonneg_of_set (E : Set s.Torus) : 0 ≤ torusVolume E := by
  unfold torusVolume torusIntegral
  exact MeasureTheory.integral_nonneg fun v =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
theorem torusCell_eq_image {a : ℝ} {z : s.Torus} {v : Fin 4 → ℝ} (hv : proj s v = z) :
    torusCell a z = proj s '' Set.pi univ fun μ => Ico (v μ - a / 2) (v μ + a / 2) := by
  subst hv
  ext p
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨v + τ, fun μ _ => ?_, (proj_map_add _ _)⟩
    obtain ⟨h1, h2⟩ := hτ μ (mem_univ μ)
    constructor
    · simp only [Pi.add_apply]
      linarith
    · simp only [Pi.add_apply]
      linarith
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w - v, fun μ _ => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := hw μ (mem_univ μ)
      constructor
      · simp only [Pi.sub_apply]
        linarith
      · simp only [Pi.sub_apply]
        linarith
    · simp [proj_map_sub]
theorem proj_injOn_cube {a : ℝ} (haℓ : a ≤ PeriodicLattice.torusSide s.L s.m) (v : Fin 4 → ℝ) :
    InjOn (proj s) (Set.pi univ fun μ => Ico (v μ - a / 2) (v μ + a / 2)) := by
  intro w hw w' hw' h
  obtain ⟨k, hk⟩ := exists_latticeTranslate_of_proj_eq h
  have hℓ := torusSide_pos s
  have hzero : ∀ μ, k μ = 0 := by
    intro μ
    have hμ : w μ = w' μ + PeriodicLattice.torusSide s.L s.m * (k μ : ℝ) := congrFun hk μ
    obtain ⟨h1, h2⟩ := hw μ (mem_univ μ)
    obtain ⟨h3, h4⟩ := hw' μ (mem_univ μ)
    refine int_eq_zero_of_abs_mul_lt hℓ (abs_lt.2 ⟨?_, ?_⟩) <;> linarith
  rw [hk]
  funext μ
  simp [latticeTranslate, hzero μ]
theorem cellProperties_holds (H : ProjectionProperties s) (U : TorusProjection.VolumeNonincreasing)
    {a : ℝ} (ha : 0 < a) (haℓ : a ≤ PeriodicLattice.torusSide s.L s.m) : CellProperties s a := by
  intro z
  obtain ⟨v, hv⟩ := proj_exists_preimage z
  have hS : IsNullMeasurableR4 (Set.pi univ fun μ : Fin 4 => Ico (v μ - a / 2) (v μ + a / 2)) :=
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet
  obtain ⟨hm, -, heq⟩ := U s _ hS
  have hvol : volumeR4 (Set.pi univ fun μ : Fin 4 => Ico (v μ - a / 2) (v μ + a / 2)) =
      ENNReal.ofReal (a ^ 4) := by
    unfold volumeR4
    rw [Real.volume_pi_Ico, Fin.prod_univ_four]
    have h : ∀ μ, v μ + a / 2 - (v μ - a / 2) = a := fun μ => by ring
    simp only [h]
    rw [← ENNReal.ofReal_mul ha.le, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [← torusCell_eq_image hv] at hm heq
  refine ⟨⟨0, fun μ _ => ?_, ?_⟩, hm, ?_, ?_⟩
  · constructor <;> simp <;> linarith
  · simp [proj_map_zero]
  · have h := heq (proj_injOn_cube haℓ v)
    rw [hvol] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (torusVolume_nonneg_of_set _) (by positivity)).1 h
  · rintro _ ⟨τ, hτ, rfl⟩
    rw [pointDist_eq_pointNorm_sub]
    simp only [add_sub_cancel_left]
    exact (pointNorm_proj_le H _).trans (euclidNormVec_le_of_mem_centeredCube ha hτ)
def latticePt (s : Conventions.StandingParameters) (a : ℝ) (k : Fin 4 → ℤ) : s.Torus :=
  proj s fun μ => a * (k μ : ℝ)
theorem mem_cellLattice {a : ℝ} {y : s.Torus} : y ∈ cellLattice s a ↔ ∃ k, y = latticePt s a k := by
  constructor
  · rintro ⟨v, ⟨k, hk⟩, rfl⟩
    exact ⟨k, congrArg _ (funext hk)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨_, ⟨k, fun _ => rfl⟩, rfl⟩
theorem latticePt_add (a : ℝ) (k k' : Fin 4 → ℤ) :
    latticePt s a (k + k') = latticePt s a k + latticePt s a k' := by
  unfold latticePt
  rw [← proj_map_add]
  congr 1
  funext μ
  simp [mul_add]
theorem latticePt_neg (a : ℝ) (k : Fin 4 → ℤ) :
    latticePt s a (-k) = -latticePt s a k := by
  unfold latticePt
  rw [← proj_map_neg]
  congr 1
  funext μ
  simp
theorem latticePt_zero (a : ℝ) : latticePt s a 0 = 0 := by
  unfold latticePt
  rw [← proj_map_zero (s := s)]
  congr 1
  funext μ
  simp
def cellLatticeSubgroup (s : Conventions.StandingParameters) (a : ℝ) : AddSubgroup s.Torus where
  carrier := cellLattice s a
  add_mem' := by
    intro y y' hy hy'
    obtain ⟨k, rfl⟩ := mem_cellLattice.1 hy
    obtain ⟨k', rfl⟩ := mem_cellLattice.1 hy'
    exact mem_cellLattice.2 ⟨k + k', (latticePt_add a k k').symm⟩
  zero_mem' := mem_cellLattice.2 ⟨0, (latticePt_zero a).symm⟩
  neg_mem' := by
    intro y hy
    obtain ⟨k, rfl⟩ := mem_cellLattice.1 hy
    exact mem_cellLattice.2 ⟨-k, (latticePt_neg a k).symm⟩
theorem exists_nat_of_torusSide_div {a : ℝ} (ha : 0 < a) {n : ℤ}
    (h : PeriodicLattice.torusSide s.L s.m / a = n) :
    ∃ N : ℕ, 0 < N ∧ (N : ℤ) = n ∧ PeriodicLattice.torusSide s.L s.m = a * (N : ℝ) := by
  have hn : (0 : ℝ) < n := h ▸ div_pos (torusSide_pos s) ha
  have hn' : 0 < n := by exact_mod_cast hn
  lift n to ℕ using hn'.le
  refine ⟨n, by exact_mod_cast hn', rfl, ?_⟩
  have := (div_eq_iff ha.ne').1 h
  rw [this]
  push_cast
  ring
def latticePtOfFin (s : Conventions.StandingParameters) (a : ℝ) (N : ℕ) (j : Fin 4 → Fin N) : s.Torus :=
  latticePt s a fun μ => (((j μ : ℕ) : ℤ))
theorem latticePtOfFin_injective {a : ℝ} (ha : 0 < a) {N : ℕ}
    (hside : PeriodicLattice.torusSide s.L s.m = a * (N : ℝ)) :
    Function.Injective (latticePtOfFin s a N) := by
  intro j j' h
  obtain ⟨d, hd⟩ := exists_latticeTranslate_of_proj_eq h
  have hℓ := torusSide_pos s
  have hzero : ∀ μ, d μ = 0 := by
    intro μ
    have hμ : a * ((j μ : ℕ) : ℝ) = a * ((j' μ : ℕ) : ℝ) +
        PeriodicLattice.torusSide s.L s.m * (d μ : ℝ) := by
      have := congrFun hd μ
      simpa [latticeTranslate] using this
    have hx : ((j μ : ℕ) : ℝ) < N := by exact_mod_cast (j μ).isLt
    have hx' : ((j' μ : ℕ) : ℝ) < N := by exact_mod_cast (j' μ).isLt
    have h0 : (0 : ℝ) ≤ ((j μ : ℕ) : ℝ) := Nat.cast_nonneg _
    have h0' : (0 : ℝ) ≤ ((j' μ : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 := mul_lt_mul_of_pos_left hx ha
    have h2 := mul_lt_mul_of_pos_left hx' ha
    have h3 := mul_nonneg ha.le h0
    have h4 := mul_nonneg ha.le h0'
    refine int_eq_zero_of_abs_mul_lt hℓ (abs_lt.2 ⟨?_, ?_⟩) <;> rw [hside] at hμ ⊢ <;> linarith
  funext μ
  have hμ : a * ((j μ : ℕ) : ℝ) = a * ((j' μ : ℕ) : ℝ) +
      PeriodicLattice.torusSide s.L s.m * (d μ : ℝ) := by
    simpa [latticeTranslate] using congrFun hd μ
  have h1 : a * ((j μ : ℕ) : ℝ) = a * ((j' μ : ℕ) : ℝ) := by
    rw [hμ, hzero μ]
    simp
  have h2 : ((j μ : ℕ) : ℝ) = ((j' μ : ℕ) : ℝ) := mul_left_cancel₀ ha.ne' h1
  exact Fin.ext (by exact_mod_cast h2)
theorem range_latticePtOfFin {a : ℝ} {N : ℕ} (hN : 0 < N)
    (hside : PeriodicLattice.torusSide s.L s.m = a * (N : ℝ)) :
    range (latticePtOfFin s a N) = cellLattice s a := by
  ext y
  constructor
  · rintro ⟨j, rfl⟩
    exact mem_cellLattice.2 ⟨_, rfl⟩
  · intro hy
    obtain ⟨k, rfl⟩ := mem_cellLattice.1 hy
    have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
    have hNp : (0 : ℤ) < N := by exact_mod_cast hN
    have hlt : ∀ μ, (k μ % (N : ℤ)).toNat < N := by
      intro μ
      have h1 := Int.emod_nonneg (k μ) hNz
      have h2 := Int.emod_lt_of_pos (k μ) hNp
      omega
    refine ⟨fun μ => ⟨(k μ % (N : ℤ)).toNat, hlt μ⟩, ?_⟩
    unfold latticePtOfFin latticePt
    rw [← proj_add_latticeTranslate_eq (s := s) _ (fun μ => k μ / (N : ℤ))]
    congr 1
    funext μ
    have hnn := Int.emod_nonneg (k μ) hNz
    have hc : (((k μ % (N : ℤ)).toNat : ℤ)) = k μ % (N : ℤ) := Int.toNat_of_nonneg hnn
    have hd : k μ = (N : ℤ) * (k μ / (N : ℤ)) + ((k μ % (N : ℤ)).toNat : ℤ) := by
      rw [hc, Int.emod_def]
      ring
    have hd' : (k μ : ℝ) = (N : ℝ) * ((k μ / (N : ℤ) : ℤ) : ℝ) +
        (((k μ % (N : ℤ)).toNat : ℕ) : ℝ) := by exact_mod_cast hd
    simp only [latticeTranslate, Pi.add_apply, hside]
    rw [hd']
    simp only [Int.cast_natCast]
    ring
theorem cellLattice_finite_ncard {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 0 < N)
    (hside : PeriodicLattice.torusSide s.L s.m = a * (N : ℝ)) :
    (cellLattice s a).Finite ∧ (cellLattice s a).ncard = N ^ 4 := by
  rw [← range_latticePtOfFin hN hside]
  refine ⟨Set.finite_range _, ?_⟩
  rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective (latticePtOfFin_injective ha hside)]
  simp [Nat.card_eq_fintype_card]
theorem torusCells_pairwiseDisjoint {a : ℝ} (ha : 0 < a) {N : ℕ}
    (hside : PeriodicLattice.torusSide s.L s.m = a * (N : ℝ)) (c : s.Torus) :
    (cellLattice s a).PairwiseDisjoint (fun y => torusCell a (y + c)) := by
  intro y hy y' hy' hne
  refine Set.disjoint_left.2 ?_
  rintro p ⟨τ, hτ, hp⟩ ⟨τ', hτ', hp'⟩
  apply hne
  obtain ⟨k, rfl⟩ := mem_cellLattice.1 hy
  obtain ⟨k', rfl⟩ := mem_cellLattice.1 hy'
  have hsum : latticePt s a k + c + proj s τ =
      latticePt s a k' + c + proj s τ' := hp.trans hp'.symm
  have h : proj s ((fun μ => a * (k μ : ℝ)) + τ) =
      proj s ((fun μ => a * (k' μ : ℝ)) + τ') := by
    rw [proj_map_add, proj_map_add]
    refine add_right_cancel (b := c) ?_
    change latticePt s a k + proj s τ + c = latticePt s a k' + proj s τ' + c
    rw [add_right_comm, hsum, add_right_comm]
  obtain ⟨d, hd⟩ := exists_latticeTranslate_of_proj_eq h
  have hz : ∀ μ, k μ - k' μ - (N : ℤ) * d μ = 0 := by
    intro μ
    have hμ : a * (k μ : ℝ) + τ μ = a * (k' μ : ℝ) + τ' μ +
        PeriodicLattice.torusSide s.L s.m * (d μ : ℝ) := by
      simpa [latticeTranslate] using congrFun hd μ
    rw [hside] at hμ
    obtain ⟨h1, h2⟩ := hτ μ (mem_univ μ)
    obtain ⟨h3, h4⟩ := hτ' μ (mem_univ μ)
    have e : a * (((k μ - k' μ - (N : ℤ) * d μ : ℤ)) : ℝ) = τ' μ - τ μ := by
      push_cast
      linarith
    refine int_eq_zero_of_abs_mul_lt ha ?_
    rw [e]
    exact abs_lt.2 ⟨by linarith, by linarith⟩
  unfold latticePt
  rw [← proj_add_latticeTranslate_eq (s := s) (fun μ => a * (k' μ : ℝ)) d]
  congr 1
  funext μ
  have hk : (k μ : ℝ) = (k' μ : ℝ) + (N : ℝ) * (d μ : ℝ) := by
    have : k μ = k' μ + (N : ℤ) * d μ := by linarith [hz μ]
    exact_mod_cast this
  simp only [latticeTranslate, Pi.add_apply, hside]
  rw [hk]
  ring
theorem iUnion_torusCells_eq_univ {a : ℝ} (ha : 0 < a) (c : s.Torus) :
    ⋃ y ∈ cellLattice s a, torusCell a (y + c) = univ := by
  refine eq_univ_of_forall fun p => ?_
  obtain ⟨v, hv⟩ := proj_exists_preimage (p - c)
  obtain ⟨k, hk⟩ := exists_int_shift_mem_centeredCube ha v
  simp only [mem_iUnion]
  refine ⟨latticePt s a k, mem_cellLattice.2 ⟨k, rfl⟩, _, hk, ?_⟩
  have h : proj s v =
      latticePt s a k + proj s (fun μ => v μ - a * (k μ : ℝ)) := by
    unfold latticePt
    rw [← proj_map_add]
    congr 1
    funext μ
    simp
  change latticePt s a k + c + proj s (fun μ => v μ - a * (k μ : ℝ)) = p
  rw [add_right_comm, ← h, hv]
  abel
theorem finite_disjoint_iUnion_props (V : VolumeProperties s) {ι : Type} [Fintype ι]
    (E : ι → Set s.Torus)
    (hE : ∀ i, IsMeasurableTorusSet (E i)) (hd : Pairwise (Function.onFun Disjoint E)) :
    IsMeasurableTorusSet (⋃ i, E i) ∧ torusVolume (⋃ i, E i) = ∑ i, torusVolume (E i) ∧
      ∀ g : s.Torus → ℝ, IsBddMeasurable g →
        setTorusIntegral (⋃ i, E i) g = ∑ i, setTorusIntegral (E i) g := by
  let e := Fintype.equivFin ι
  obtain ⟨_, hV, _, _⟩ := V
  have hall := hV (Fintype.card ι) (E ∘ e.symm) (fun i => hE _)
    (fun i j hij => hd (e.symm.injective.ne hij))
  have hU : (⋃ i, (E ∘ e.symm) i) = ⋃ i, E i := e.symm.surjective.iUnion_comp E
  rw [hU] at hall
  obtain ⟨h1, h2, h3⟩ := hall
  exact ⟨h1, h2.trans (e.symm.sum_comp fun i => torusVolume (E i)), fun g hg =>
    (h3 g hg).trans (e.symm.sum_comp fun i => setTorusIntegral (E i) g)⟩
theorem iUnion_torusCells_props (V : VolumeProperties s) {a : ℝ} (hc : CellProperties s a)
    (hfin : (cellLattice s a).Finite)
    (hdis : ∀ c : s.Torus, (cellLattice s a).PairwiseDisjoint (fun y => torusCell a (y + c)))
    (c : s.Torus) {A : Set s.Torus} (hA : A ⊆ cellLattice s a) :
    IsMeasurableTorusSet (⋃ y ∈ A, torusCell a (y + c)) ∧
      torusVolume (⋃ y ∈ A, torusCell a (y + c)) = a ^ 4 * (A.ncard : ℝ) := by
  have : Fintype A := (hfin.subset hA).fintype
  obtain ⟨h1, h2, -⟩ := finite_disjoint_iUnion_props V (fun y : A => torusCell a ((y : s.Torus) + c))
    (fun y => (hc _).2.1) (fun y y' hne => hdis c (hA y.2) (hA y'.2) (Subtype.coe_injective.ne hne))
  have hU : (⋃ y : A, torusCell a ((y : s.Torus) + c)) = ⋃ y ∈ A, torusCell a (y + c) :=
    iUnion_coe_set A fun y : A => torusCell a ((y : s.Torus) + c)
  rw [hU] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  have hv : ∀ y : A, torusVolume (torusCell a ((y : s.Torus) + c)) = a ^ 4 := fun y => (hc _).2.2.1
  simp only [hv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  ring
theorem closedWrapBall_eq_image (H : ProjectionProperties s) (x : s.Torus) (r : ℝ) {v : Fin 4 → ℝ}
    (hv : proj s v = x) : closedWrapBall x r = proj s '' closedBallR4 v r := by
  ext p
  constructor
  · intro hp
    obtain ⟨v₀, h0, he⟩ := exists_lift_norm_eq_pointNorm H (p - x)
    refine ⟨v + v₀, ?_, ?_⟩
    · change euclidNormVec (v + v₀ - v) ≤ r
      rw [add_sub_cancel_left, he]
      exact hp
    · rw [proj_map_add, hv, h0]
      abel
  · rintro ⟨w, hw, rfl⟩
    change pointNorm (proj s w - x) ≤ r
    rw [← hv, ← proj_map_sub]
    exact (pointNorm_proj_le H _).trans hw
theorem omega4_nonneg : 0 ≤ omega4 := by
  unfold omega4
  positivity
theorem volumeR4_closedBallR4 (v : Fin 4 → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volumeR4 (closedBallR4 v r) = ENNReal.ofReal (omega4 * r ^ 4) := by
  have hb : closedBallR4 v r = (WithLp.toLp 2 : (Fin 4 → ℝ) → EuclideanSpace ℝ (Fin 4)) ⁻¹'
      Metric.closedBall (WithLp.toLp 2 v) r := by
    ext y
    simp only [closedBallR4, Set.mem_ofPred_eq, mem_preimage, mem_closedBall_iff_norm,
      euclidNormVec_eq_norm, WithLp.toLp_sub]
  unfold volumeR4
  rw [hb, (PiLp.volume_preserving_toLp (Fin 4)).measure_preimage
    Metric.isClosed_closedBall.measurableSet.nullMeasurableSet, EuclideanSpace.volume_closedBall]
  have hG : Real.Gamma ((4 : ℝ) / 2 + 1) = 2 := by
    have h := Real.Gamma_nat_eq_factorial 2
    norm_num at h ⊢
  have hp : Real.sqrt Real.pi ^ 4 = Real.pi ^ 2 := by
    have h := Real.sq_sqrt Real.pi_pos.le
    calc Real.sqrt Real.pi ^ 4 = (Real.sqrt Real.pi ^ 2) ^ 2 := by ring
      _ = Real.pi ^ 2 := by rw [h]
  simp only [Fintype.card_fin, Nat.cast_ofNat, hG, hp]
  rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold omega4
  ring
theorem isClosed_closedWrapBall (H : ProjectionProperties s) (x : s.Torus) (r : ℝ) :
    @IsClosed _ (euclidTopology s) (closedWrapBall x r) := by
  refine @IsClosed.mk _ (euclidTopology s) _ ?_
  change PeriodicLattice.IsMetricOpen _
  intro p hp
  have hlt : r < pointNorm (p - x) := not_le.1 hp
  refine ⟨pointNorm (p - x) - r, sub_pos.2 hlt, fun w hw hwx => ?_⟩
  have hw' : pointNorm (w - p) < pointNorm (p - x) - r := hw
  have hwx' : pointNorm (w - x) ≤ r := hwx
  have htri : pointNorm (p - x) ≤ pointNorm (p - w) + pointNorm (w - x) :=
    pointDist_triangle H p x w
  have hcomm : pointNorm (w - p) = pointNorm (p - w) := pointDist_symm H p w
  linarith
theorem closedWrapBallProperties_holds (H : ProjectionProperties s)
    (U : TorusProjection.VolumeNonincreasing) : ClosedWrapBallProperties s := by
  intro x r hr
  obtain ⟨v, hv⟩ := proj_exists_preimage x
  have hS : IsNullMeasurableR4 (closedBallR4 v r) := by
    have hcl : IsClosed (closedBallR4 v r) :=
      isClosed_le (continuous_euclidNormVec.comp (continuous_id.sub continuous_const))
        continuous_const
    exact hcl.measurableSet.nullMeasurableSet
  obtain ⟨hm, hle, -⟩ := U s _ hS
  rw [← closedWrapBall_eq_image H x r hv] at hm hle
  rw [volumeR4_closedBallR4 v hr.le] at hle
  refine ⟨rfl, fun v' hv' => ⟨closedWrapBall_eq_image H x r ?_, volumeR4_closedBallR4 v' hr.le⟩,
    isClosed_closedWrapBall H x r, hm,
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg omega4_nonneg (by positivity))).1 hle,
    fun _ => rfl⟩
  obtain ⟨_, _, _, hlift, _⟩ := H
  exact (hlift _ _).1 hv'
theorem latticePointCountInBall_holds (H : ProjectionProperties s) (V : VolumeProperties s)
    (hW : ClosedWrapBallProperties s) {a : ℝ} (ha : 0 < a) (hc : CellProperties s a)
    (hfin : (cellLattice s a).Finite)
    (hdis : ∀ c : s.Torus, (cellLattice s a).PairwiseDisjoint (fun y => torusCell a (y + c))) :
    LatticePointCountInBall s a := by
  intro c x r hr
  have hA : {y | y ∈ cellLattice s a ∧ pointDist (y + c) x ≤ r} ⊆ cellLattice s a :=
    fun y hy => hy.1
  obtain ⟨hm, hvol⟩ := iUnion_torusCells_props V hc hfin hdis c hA
  rw [← hvol]
  obtain ⟨-, -, -, hbm, hbv, -⟩ := hW x (r + a) (by positivity)
  obtain ⟨hmono, -⟩ := V
  refine (hmono _ _ hm hbm ?_).trans hbv
  intro p hp
  simp only [mem_iUnion] at hp
  obtain ⟨y, hy, hp⟩ := hp
  have h1 := pointDist_triangle H p x (y + c)
  have h2 := (hc (y + c)).2.2.2 p hp
  have h3 : pointDist (y + c) x ≤ r := hy.2
  change pointDist p x ≤ r + a
  linarith
theorem lipschitzBoundedMeasurable_holds (H : ProjectionProperties s) :
    LipschitzBoundedMeasurable s := by
  rintro f ⟨C, hC, hf⟩
  constructor
  · refine ⟨‖f 0‖ + C * PeriodicLattice.torusSide s.L s.m, fun p => ?_⟩
    have h1 := hf p 0
    have h2 : pointDist p 0 ≤ PeriodicLattice.torusSide s.L s.m := by
      rw [pointDist_eq_pointNorm_sub, sub_zero]
      exact pointNorm_le_torusSide H p
    have h3 := norm_sub_norm_le (f p) (f 0)
    have h4 := mul_le_mul_of_nonneg_left h2 hC
    linarith
  · have hcont : Continuous (f ∘ proj s) := by
      refine continuous_iff_continuousAt.2 fun v₀ => ?_
      refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
      have hlim : Filter.Tendsto (fun v => C * euclidNormVec (v - v₀)) (nhds v₀) (nhds 0) := by
        have hc : Continuous fun v : Fin 4 → ℝ => C * euclidNormVec (v - v₀) :=
          continuous_const.mul (continuous_euclidNormVec.comp (continuous_id.sub continuous_const))
        have h := hc.tendsto v₀
        simpa [euclidNormVec_zero] using h
      refine squeeze_zero (fun _ => norm_nonneg _) (fun v => ?_) hlim
      have h1 := hf (proj s v) (proj s v₀)
      have h2 : pointDist (proj s v) (proj s v₀) ≤ euclidNormVec (v - v₀) := by
        rw [pointDist_eq_pointNorm_sub, ← proj_map_sub]
        exact pointNorm_proj_le H _
      exact h1.trans (mul_le_mul_of_nonneg_left h2 hC)
    exact hcont.measurable.nullMeasurable
theorem lipConstTorus_spec (H : ProjectionProperties s) {f : s.Torus → ℝ}
    (hf : IsLipschitzFor pointDist f) :
    0 ≤ lipConstTorus (ℓ := PeriodicLattice.torusSide s.L s.m) f ∧
      ∀ x y, ‖f x - f y‖ ≤ lipConstTorus (ℓ := PeriodicLattice.torusSide s.L s.m) f * pointDist x y := by
  have hne : {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * pointDist x y}.Nonempty := hf
  have h0 : 0 ≤ sInf {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * pointDist x y} :=
    le_csInf hne fun C hC => hC.1
  refine ⟨h0, fun x y => ?_⟩
  change ‖f x - f y‖ ≤ sInf {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * pointDist x y} *
    pointDist x y
  have hd : 0 ≤ pointDist x y := pointNorm_nonneg H _
  rcases hd.eq_or_lt with hd0 | hd0
  · obtain ⟨C, hC⟩ := hne
    have := hC.2 x y
    rw [← hd0] at this ⊢
    simpa using this
  · rw [← div_le_iff₀ hd0]
    exact le_csInf hne fun C hC => (div_le_iff₀ hd0).2 (hC.2 x y)
theorem abs_sub_setTorusIntegral_le (I : IntegralProperties s) {E : Set s.Torus}
    (hE : IsMeasurableTorusSet E) {f : s.Torus → ℝ} (hf : IsBddMeasurable f) {c B : ℝ}
    (hcB : ∀ p ∈ E, |c - f p| ≤ B) :
    |c * torusVolume E - setTorusIntegral E f| ≤ B * torusVolume E := by
  have hp : IsBddMeasurable (E.indicator (1 : s.Torus → ℝ)) := by
    refine ⟨⟨1, fun p => ?_⟩, (isMeasurableTorusSet_iff_indicator E).1 hE⟩
    by_cases hpE : p ∈ E <;> simp [hpE]
  have hq := (I _ _ hp hf 0 0).2.1
  have hlin : ∀ α : ℝ,
      torusIntegral (fun p => α * E.indicator (1 : s.Torus → ℝ) p + 0 * E.indicator (1 : s.Torus → ℝ) p) =
        α * torusVolume E := by
    intro α
    have h := (I _ _ hp hp α 0).2.2.1
    rw [h]
    simp [torusVolume]
  have hup : setTorusIntegral E f ≤ (c + B) * torusVolume E := by
    rw [← hlin]
    refine (I _ _ hq (I _ _ hp hp (c + B) 0).1 0 0).2.2.2 fun p => ?_
    by_cases hpE : p ∈ E
    · have := abs_le.1 (hcB p hpE)
      simp only [hpE, Set.indicator_of_mem, Pi.one_apply]
      linarith [this.1]
    · simp [hpE]
  have hlo : (c - B) * torusVolume E ≤ setTorusIntegral E f := by
    rw [← hlin]
    refine (I _ _ (I _ _ hp hp (c - B) 0).1 hq 0 0).2.2.2 fun p => ?_
    by_cases hpE : p ∈ E
    · have := abs_le.1 (hcB p hpE)
      simp only [hpE, Set.indicator_of_mem, Pi.one_apply]
      linarith [this.2]
    · simp [hpE]
  exact abs_le.2 ⟨by linarith, by linarith⟩
theorem sum_subtype_eq_toFinset_sum {A : Set s.Torus} (hfin : A.Finite) [Fintype A]
    (g : s.Torus → ℝ) :
    ∑ y : A, g y = ∑ y ∈ hfin.toFinset, g y := by
  rw [← finsum_eq_sum_of_fintype, finsum_set_coe_eq_finsum_mem A,
    finsum_mem_eq_finite_toFinset_sum _ hfin]
theorem riemannSumApprox_holds (H : ProjectionProperties s) (I : IntegralProperties s)
    (V : VolumeProperties s) (hW : ClosedWrapBallProperties s) (hL : LipschitzBoundedMeasurable s)
    {a : ℝ} (ha : 0 < a) (hc : CellProperties s a) (hfin : (cellLattice s a).Finite)
    (hdis : ∀ c : s.Torus, (cellLattice s a).PairwiseDisjoint (fun y => torusCell a (y + c)))
    (hcov : ∀ c : s.Torus, ⋃ y ∈ cellLattice s a, torusCell a (y + c) = univ) :
    RiemannSumApprox s a := by
  classical
  intro c x r f hr hf hvan
  have hfb : IsBddMeasurable f := hL f hf
  obtain ⟨hC, hlip⟩ := lipConstTorus_spec H hf
  set C := lipConstTorus (ℓ := PeriodicLattice.torusSide s.L s.m) f with hCdef
  set T := hfin.toFinset with hT
  have : Fintype (cellLattice s a) := hfin.fintype
  obtain ⟨-, -, hint⟩ := finite_disjoint_iUnion_props V
    (fun y : cellLattice s a => torusCell a ((y : s.Torus) + c))
    (fun y => (hc _).2.1) (fun y y' hne => hdis c y.2 y'.2 (Subtype.coe_injective.ne hne))
  have hU : (⋃ y : cellLattice s a, torusCell a ((y : s.Torus) + c)) = univ := by
    rw [← hcov c]
    exact iUnion_coe_set (cellLattice s a) fun y : cellLattice s a => torusCell a ((y : s.Torus) + c)
  have hintf : torusIntegral f = ∑ y ∈ T, setTorusIntegral (torusCell a (y + c)) f := by
    have h := hint f hfb
    rw [hU, sum_subtype_eq_toFinset_sum hfin fun y => setTorusIntegral (torusCell a (y + c)) f] at h
    rw [← h]
    simp [setTorusIntegral]
  have hsum : ∑ᶠ y ∈ cellLattice s a, f (y + c) = ∑ y ∈ T, f (y + c) :=
    finsum_mem_eq_finite_toFinset_sum _ hfin
  set A : Set s.Torus := {y | y ∈ cellLattice s a ∧ ∃ w ∈ torusCell a (y + c), f w ≠ 0} with hAdef
  have hAsub : A ⊆ cellLattice s a := fun y hy => hy.1
  have hAfin : A.Finite := hfin.subset hAsub
  obtain ⟨hAm, hAv⟩ := iUnion_torusCells_props V hc hfin hdis c hAsub
  have hterm : ∀ y ∈ T, |f (y + c) * a ^ 4 - setTorusIntegral (torusCell a (y + c)) f| ≤
      if y ∈ hAfin.toFinset then a * C * a ^ 4 else 0 := by
    intro y hy
    have hyL : y ∈ cellLattice s a := hfin.mem_toFinset.1 hy
    obtain ⟨hz, hm, hv, hd⟩ := hc (y + c)
    by_cases hyA : y ∈ hAfin.toFinset
    · rw [if_pos hyA]
      have h := abs_sub_setTorusIntegral_le I hm hfb (c := f (y + c)) (B := a * C) (fun p hp => ?_)
      · rwa [hv] at h
      · have h1 := hlip (y + c) p
        rw [Real.norm_eq_abs, pointDist_symm H p (y + c)] at h1
        have h2 := mul_le_mul_of_nonneg_left (hd p hp) hC
        linarith
    · rw [if_neg hyA]
      have hzero : ∀ p ∈ torusCell a (y + c), f p = 0 := by
        intro p hp
        by_contra hne
        exact hyA (hAfin.mem_toFinset.2 ⟨hyL, p, hp, hne⟩)
      have h := abs_sub_setTorusIntegral_le I hm hfb (c := f (y + c)) (B := 0) (fun p hp => ?_)
      · rwa [hv, zero_mul] at h
      · rw [hzero p hp, hzero _ hz]
        simp
  have hsub : (⋃ y ∈ A, torusCell a (y + c)) ⊆ closedWrapBall x (r + 2 * a) := by
    intro p hp
    simp only [mem_iUnion] at hp
    obtain ⟨y, ⟨-, w, hw, hfw⟩, hp⟩ := hp
    have hwx : pointDist w x ≤ r := by
      by_contra hcon
      exact hfw (hvan w hcon)
    have h1 := pointDist_triangle H p x w
    have h2 := pointDist_triangle H p w (y + c)
    have h3 := (hc (y + c)).2.2.2 p hp
    have h4 := (hc (y + c)).2.2.2 w hw
    have h5 := pointDist_symm H w (y + c)
    change pointDist p x ≤ r + 2 * a
    linarith
  obtain ⟨-, -, -, hbm, hbv, -⟩ := hW x (r + 2 * a) (by positivity)
  obtain ⟨hmono, -⟩ := V
  have hvolA : a ^ 4 * (A.ncard : ℝ) ≤ omega4 * (r + 2 * a) ^ 4 := by
    rw [← hAv]
    exact (hmono _ _ hAm hbm hsub).trans hbv
  have hAT : hAfin.toFinset ⊆ T := by
    intro y hy
    exact hfin.mem_toFinset.2 (hAfin.mem_toFinset.1 hy).1
  have hcard : ∑ y ∈ T, (if y ∈ hAfin.toFinset then a * C * a ^ 4 else 0) =
      a * C * (a ^ 4 * (A.ncard : ℝ)) := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hAT, Finset.sum_const, nsmul_eq_mul,
      ← Set.ncard_eq_toFinset_card A hAfin]
    ring
  calc |a ^ 4 * (∑ᶠ y ∈ cellLattice s a, f (y + c)) - torusIntegral f|
      = |∑ y ∈ T, (f (y + c) * a ^ 4 - setTorusIntegral (torusCell a (y + c)) f)| := by
        rw [hsum, hintf, Finset.sum_sub_distrib, Finset.mul_sum]
        congr 2
        exact Finset.sum_congr rfl fun y _ => mul_comm _ _
    _ ≤ ∑ y ∈ T, |f (y + c) * a ^ 4 - setTorusIntegral (torusCell a (y + c)) f| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ T, (if y ∈ hAfin.toFinset then a * C * a ^ 4 else 0) :=
        Finset.sum_le_sum hterm
    _ = a * C * (a ^ 4 * (A.ncard : ℝ)) := hcard
    _ ≤ a * C * (omega4 * (r + 2 * a) ^ 4) :=
        mul_le_mul_of_nonneg_left hvolA (mul_nonneg ha.le hC)
    _ = omega4 * a * (r + 2 * a) ^ 4 * C := by ring
theorem cellsAndBallsStatement_holds (h₁ : TorusCovering.CoveringIntegralVolumeStatement)
    (h₂ : TorusProjection.VolumeNonincreasing) : CellsAndBallsStatement := by
  intro s
  obtain ⟨H, I, V, -⟩ := h₁ s
  have hW := closedWrapBallProperties_holds H h₂
  have hL := lipschitzBoundedMeasurable_holds H
  refine ⟨distanceProperties_holds H, hW, hL, fun a n ha hn => ?_⟩
  obtain ⟨N, hN, rfl, hside⟩ := exists_nat_of_torusSide_div ha hn
  have haℓ : a ≤ PeriodicLattice.torusSide s.L s.m := by
    have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [hside]
    nlinarith
  have hc := cellProperties_holds H h₂ ha haℓ
  obtain ⟨hfin, hcard⟩ := cellLattice_finite_ncard ha hN hside
  have hdis := torusCells_pairwiseDisjoint (s := s) ha hside
  have hcov := iUnion_torusCells_eq_univ (s := s) ha
  refine ⟨hc, ⟨⟨cellLatticeSubgroup s a, rfl⟩, hfin, by exact_mod_cast hcard, fun c =>
    ⟨hdis c, hcov c⟩⟩, latticePointCountInBall_holds H V hW ha hc hfin hdis,
    riemannSumApprox_holds H I V hW hL ha hc hfin hdis hcov⟩
end TorusMeasure.TranslatedLatticeCells
end YangMills.Construction
end
