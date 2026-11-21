import YangMills.Construction.RotationInvariance.DivisibilityOfTheTopFrequency
import YangMills.Construction.RotationInvariance.HalvingOfZeroSets
import YangMills.Construction.RotationInvariance.SelectionAtALabelledConfigurationMappedToItselfByARotation
import Mathlib
set_option autoImplicit false
open Complex (I)
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.MaxFrequencyDivisible
open RealPlane
def unitVec (t : ℝ) : RealPlane := !₂[Real.cos t, Real.sin t]
theorem unitVec_zero (t : ℝ) : unitVec t 0 = Real.cos t := by simp [unitVec]
theorem unitVec_one (t : ℝ) : unitVec t 1 = Real.sin t := by simp [unitVec]
theorem unitVec_add_two_pi (t : ℝ) : unitVec (t + 2 * Real.pi) = unitVec t := by
  simp [unitVec]
theorem planeInner_eq (x y : RealPlane) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by apply _root_.YangMills.Construction.ForwardTube.inner_eq_coord_sum <;> assumption
theorem inner_unitVec (s t : ℝ) :
    inner ℝ (unitVec s) (unitVec t) = Real.cos (s - t) := by
  rw [planeInner_eq, Real.cos_sub]
  simp only [unitVec_zero, unitVec_one]
theorem norm_unitVec (t : ℝ) : ‖unitVec t‖ = 1 := by
  have h : ‖unitVec t‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_unitVec, sub_self, Real.cos_zero]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h
theorem rotate_smul_unitVec (s ρ t : ℝ) :
    rotate s (ρ • unitVec t) = ρ • unitVec (t + s) := by
  ext i
  fin_cases i
  · simp [RealPlane.rotate, unitVec, Real.cos_add]
    ring
  · simp [RealPlane.rotate, unitVec, Real.sin_add]
    ring
theorem unitVec_sub_two_cos_smul (ϑ α : ℝ) :
    unitVec α - (2 * Real.cos (ϑ - α)) • unitVec ϑ =
      unitVec (2 * ϑ - Real.pi - α) := by
  obtain ⟨δ, rfl⟩ : ∃ δ, α = ϑ - δ := ⟨ϑ - α, by ring⟩
  have hangle : 2 * ϑ - Real.pi - (ϑ - δ) = ϑ + δ - Real.pi := by ring
  have hdiff : ϑ - (ϑ - δ) = δ := by ring
  rw [hangle, hdiff]
  ext i
  fin_cases i
  · simp [unitVec, Real.cos_add, Real.cos_sub]
    ring
  · simp [unitVec, Real.sin_add, Real.sin_sub]
    ring
theorem exists_smul_quarterRotation_of_inner_eq_zero (ϑ : ℝ) (v : RealPlane)
    (h : inner ℝ (unitVec ϑ) v = 0) :
    ∃ c : ℝ, c • unitVec (ϑ + Real.pi / 2) = v := by
  rw [planeInner_eq, unitVec_zero, unitVec_one] at h
  have e := Real.sin_sq_add_cos_sq ϑ
  refine ⟨-(v 0) * Real.sin ϑ + v 1 * Real.cos ϑ, ?_⟩
  ext i
  fin_cases i
  · simp [unitVec, Real.cos_add_pi_div_two]
    linear_combination (-Real.cos ϑ) * h + v 0 * e
  · simp [unitVec, Real.sin_add_pi_div_two]
    linear_combination (-Real.sin ϑ) * h + v 1 * e
theorem isLine_normalSet (ϑ : ℝ) (u : RealPlane) :
    IsLine {y | inner ℝ (unitVec ϑ) (y - u) = 0} := by
  have hne : unitVec (ϑ + Real.pi / 2) ≠ 0 := fun h => by
    simpa [h] using norm_unitVec (ϑ + Real.pi / 2)
  refine ⟨AffineSubspace.mk' u (Submodule.span ℝ {unitVec (ϑ + Real.pi / 2)}), ?_, ?_⟩
  · ext y
    simp only [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, Set.mem_ofPred_eq,
      Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      have hangle : ϑ - (ϑ + Real.pi / 2) = -(Real.pi / 2) := by ring
      rw [← hc, inner_smul_right, inner_unitVec, hangle, Real.cos_neg, Real.cos_pi_div_two,
        mul_zero]
    · exact exists_smul_quarterRotation_of_inner_eq_zero ϑ (y - u)
  · rw [AffineSubspace.direction_mk', finrank_span_singleton hne]
theorem isUnitNormal_normalSet (ϑ : ℝ) (u : RealPlane) :
    IsUnitNormal {y | inner ℝ (unitVec ϑ) (y - u) = 0} (unitVec ϑ) := by
  refine ⟨norm_unitVec ϑ, ?_⟩
  intro a ha b hb
  have hsplit : b - a = (b - u) - (a - u) := by abel
  have ha' : inner ℝ (unitVec ϑ) (a - u) = 0 := ha
  have hb' : inner ℝ (unitVec ϑ) (b - u) = 0 := hb
  rw [hsplit, inner_sub_right, ha', hb', sub_zero]
def polygonVertex (k : ℕ) (u : RealPlane) (ρ γ : ℝ) (a : ℤ) : RealPlane :=
  u + ρ • unitVec (γ + (a : ℝ) * (Real.pi / k))
theorem polygonVertex_add_period {k : ℕ} (hk : 1 ≤ k) (u : RealPlane) (ρ γ : ℝ) (a : ℤ) :
    polygonVertex k u ρ γ (a + 2 * k) = polygonVertex k u ρ γ a := by
  have hk0 : (k : ℝ) ≠ 0 := by
    have : 0 < k := hk
    positivity
  have hangle : γ + ((a + 2 * k : ℤ) : ℝ) * (Real.pi / k) =
      γ + (a : ℝ) * (Real.pi / k) + 2 * Real.pi := by
    push_cast
    field_simp
    ring
  simp only [polygonVertex]
  rw [hangle, unitVec_add_two_pi]
theorem dvd_sub_of_polygonVertex_eq {k : ℕ} (hk : 1 ≤ k) {u : RealPlane} {ρ γ : ℝ} (hρ : 0 < ρ)
    {a a' : ℤ} (h : polygonVertex k u ρ γ a = polygonVertex k u ρ γ a') :
    (2 * k : ℤ) ∣ a - a' := by
  have hk0 : (k : ℝ) ≠ 0 := by
    have : 0 < k := hk
    positivity
  have hvec : unitVec (γ + (a : ℝ) * (Real.pi / k)) =
      unitVec (γ + (a' : ℝ) * (Real.pi / k)) :=
    smul_right_injective _ hρ.ne' (add_left_cancel h)
  have hc := congrArg (fun v : RealPlane => v 0) hvec
  have hs := congrArg (fun v : RealPlane => v 1) hvec
  simp only [unitVec_zero, unitVec_one] at hc hs
  obtain ⟨n, hn⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp (Real.Angle.cos_sin_inj hc hs)
  refine ⟨n, ?_⟩
  have e : Real.pi / k * k = Real.pi := div_mul_cancel₀ _ hk0
  have hreal : ((a - a' : ℤ) : ℝ) = ((2 * k * n : ℤ) : ℝ) := by
    apply mul_left_cancel₀ Real.pi_ne_zero
    push_cast
    linear_combination (k : ℝ) * hn - ((a : ℝ) - a') * e
  exact_mod_cast hreal
theorem inner_polygonVertex (k : ℕ) (u : RealPlane) (ρ γ ϑ : ℝ) (a : ℤ) :
    inner ℝ (unitVec ϑ) (polygonVertex k u ρ γ a - u) =
      ρ * Real.cos (ϑ - (γ + (a : ℝ) * (Real.pi / k))) := by
  rw [polygonVertex, add_sub_cancel_left, inner_smul_right, inner_unitVec]
theorem reflectAcross_polygonVertex (k : ℕ) (u : RealPlane) (ρ γ : ℝ) (a₀ a : ℤ) :
    reflectAcross
        (unitVec (γ + (2 * (a₀ : ℝ) + 1) * (Real.pi / k / 2) + Real.pi / 2)) u
        (polygonVertex k u ρ γ a) = polygonVertex k u ρ γ (2 * a₀ + 1 - a) := by
  rw [reflectAcross, inner_polygonVertex]
  have hcombine := unitVec_sub_two_cos_smul
    (γ + (2 * (a₀ : ℝ) + 1) * (Real.pi / k / 2) + Real.pi / 2) (γ + (a : ℝ) * (Real.pi / k))
  have hangle : 2 * (γ + (2 * (a₀ : ℝ) + 1) * (Real.pi / k / 2) + Real.pi / 2) - Real.pi -
      (γ + (a : ℝ) * (Real.pi / k)) = γ + ((2 * a₀ + 1 - a : ℤ) : ℝ) * (Real.pi / k) := by
    push_cast
    ring
  rw [hangle] at hcombine
  rw [polygonVertex, polygonVertex, ← hcombine, smul_sub, smul_smul]
  have hcoef : (2 * (ρ * Real.cos (γ + (2 * (a₀ : ℝ) + 1) * (Real.pi / k / 2) + Real.pi / 2 -
      (γ + (a : ℝ) * (Real.pi / k))))) =
      ρ * (2 * Real.cos (γ + (2 * (a₀ : ℝ) + 1) * (Real.pi / k / 2) + Real.pi / 2 -
      (γ + (a : ℝ) * (Real.pi / k)))) := by ring
  rw [hcoef]
  abel
def vertexArc (p : ℤ → RealPlane) (φ : realLabels) (a₀ : ℤ) (j : ℕ) :
    Set (RealPlane × realLabels) :=
  (fun a => (p a, φ)) '' Set.Ioc a₀ (a₀ + j)
theorem isDistinctLabelledSet_vertexArc {k j : ℕ} {p : ℤ → RealPlane}
    (hp : ∀ a a' : ℤ, p a = p a' → (2 * k : ℤ) ∣ a - a') (hj : j ≤ 2 * k) (φ : realLabels)
    (a₀ : ℤ) : IsDistinctLabelledSet j (vertexArc p φ a₀ j) := by
  have hinj : Set.InjOn (fun a => (p a, φ)) (Set.Ioc a₀ (a₀ + j)) := by
    intro a ha a' ha' h
    have hd := hp a a' (congrArg Prod.fst h)
    have h1 := ha.1
    have h2 := ha.2
    have h3 := ha'.1
    have h4 := ha'.2
    have h0 : a - a' = 0 := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by omega, by omega⟩)
    omega
  refine ⟨?_, ?_⟩
  · rw [vertexArc, hinj.encard_image, ← Finset.coe_Ioc, Set.encard_coe_eq_coe_finsetCard,
      Int.card_Ioc]
    simp
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩ h
    have h' : p a = p a' := h
    simp only [h']
theorem injective_of_range_encard {α : Type*} {n : ℕ} (f : Fin n → α)
    (h : (Set.range f).encard = n) : Function.Injective f := by
  classical
  have hr : Set.range f = ↑(Finset.univ.image f) := by simp
  rw [hr, Set.encard_coe_eq_coe_finsetCard] at h
  have hc : (Finset.univ.image f).card = (Finset.univ : Finset (Fin n)).card := by
    simpa using h
  have hi := Finset.card_image_iff.mp hc
  rw [Finset.coe_univ] at hi
  exact Set.injOn_univ.mp hi
theorem range_encard_of_injective {α : Type*} {n : ℕ} {f : Fin n → α}
    (hf : Function.Injective f) : (Set.range f).encard = n := by
  classical
  have hr : Set.range f = ↑(Finset.univ.image f) := by simp
  rw [hr, Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hf]
  simp
theorem isDistinctLabelledSet_graph {n : ℕ} (c : LabelledPoints n)
    (hc : c.points ∈ injectivePointTuples n) : IsDistinctLabelledSet n c.graph := by
  have hi : Function.Injective fun i => (c.points i, c.labelVec i) :=
    fun i j h => hc (congrArg Prod.fst h)
  refine ⟨range_encard_of_injective hi, ?_⟩
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h
  have hij : i = j := hc h
  rw [hij]
theorem points_injective_of_enumerates {n : ℕ} {Y : Set (RealPlane × realLabels)}
    {c : LabelledPoints n} (hc : Enumerates Y c) :
    c.points ∈ injectivePointTuples n := by
  obtain ⟨hY, rfl⟩ := hc
  have hi := injective_of_range_encard _ hY.card_eq
  show Function.Injective _
  intro i j h
  apply hi
  exact hY.fst_injOn ⟨i, rfl⟩ ⟨j, rfl⟩ h
theorem configHarmonic_eq_of_graph_eq (hHarmonics : DistinctHarmonics.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) (h : ℤ) {n : ℕ}
    (hn : 2 ≤ n) {c c' : LabelledPoints n} (hc : c.points ∈ injectivePointTuples n)
    (hc' : c'.points ∈ injectivePointTuples n) (hp : c'.graph = c.graph) :
    configHarmonic S d.angle h c' = configHarmonic S d.angle h c := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 1 + 1 := ⟨n - 2, by omega⟩
  have hmem : ∀ i, ∃ j, (c.points j, c.labelVec j) = (c'.points i, c'.labelVec i) := by
    intro i
    have hi : (c'.points i, c'.labelVec i) ∈ c'.graph := ⟨i, rfl⟩
    rw [hp] at hi
    exact hi
  choose σ hσ using hmem
  have hinj : Function.Injective σ := by
    intro i j hij
    apply hc'
    have hi := congrArg Prod.fst (hσ i)
    have hj := congrArg Prod.fst (hσ j)
    simp only at hi hj
    rw [← hi, ← hj, hij]
  let ς : Equiv.Perm (Fin (q + 1 + 1)) :=
    Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hinj)
  have hpos : permuteTuple ς c.points = c'.points :=
    funext fun i => congrArg Prod.fst (hσ i)
  have hlab : permuteTuple ς c.labelVec = c'.labelVec :=
    funext fun i => congrArg Prod.snd (hσ i)
  obtain ⟨-, -, hPermutation, -⟩ := hHarmonics m S d (q + 1) (by omega) h c.labelVec
  have hEq := hPermutation ς c.points hc
  rw [hpos, hlab] at hEq
  exact hEq
theorem labelledSetHarmonic_eq (hHarmonics : DistinctHarmonics.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) (h : ℤ) {n : ℕ}
    (hn : 2 ≤ n) {Y : Set (RealPlane × realLabels)} {c : LabelledPoints n}
    (hc : Enumerates Y c) :
    labelledSetHarmonic S d.angle h n Y = configHarmonic S d.angle h c := by
  have hex : ∃ v, ∃ c' : LabelledPoints n, Enumerates Y c' ∧
      configHarmonic S d.angle h c' = v := ⟨_, c, hc, rfl⟩
  obtain ⟨c', hc', hv⟩ := Classical.epsilon_spec hex
  show Classical.epsilon _ = _
  rw [← hv]
  exact configHarmonic_eq_of_graph_eq hHarmonics d h hn
    (points_injective_of_enumerates hc) (points_injective_of_enumerates hc')
    (hc'.2.symm.trans hc.2)
def zeroLabel : realLabels :=
  ⟨fun _ => 0, by
    show ContDiff ℝ 1 _ ∧ HasCompactSupport _
    exact ⟨contDiff_const, HasCompactSupport.zero⟩⟩
theorem exists_config_harmonic_ne_zero (hHarmonics : DistinctHarmonics.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) {n : ℕ} (hn : 2 ≤ n)
    (htop : 1 ≤ maxFrequency S d.angle n) :
    ∃ c : LabelledPoints n, c.points ∈ injectivePointTuples n ∧
      configHarmonic S d.angle (-(maxFrequency S d.angle n : ℤ)) c ≠ 0 := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 1 + 1 := ⟨n - 2, by omega⟩
  obtain ⟨-, -, -, -, -, -, -, hTop, -⟩ :=
    hHarmonics m S d (q + 1) (by omega) 0 (fun _ => zeroLabel)
  obtain ⟨φ, y, hy, hne⟩ := hTop htop
  exact ⟨⟨y, fun i => (φ i).1, fun i => (φ i).2⟩, hy, hne⟩
theorem dvd_two_mul_of_exp_eq_one {k h : ℕ} (hk : 1 ≤ k)
    (hexp : Complex.exp (4 * I * ((-(h : ℤ) : ℤ) : ℂ) * ((Real.pi / k : ℝ) : ℂ)) = 1) :
    k ∣ 2 * h := by
  have hk0 : (k : ℂ) ≠ 0 := by
    have : k ≠ 0 := by omega
    exact_mod_cast this
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  push_cast at hn
  have e : (Real.pi : ℂ) / k * k = Real.pi := div_mul_cancel₀ _ hk0
  have hfactor : (2 * (Real.pi : ℂ) * I * k) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero) hk0
  have hc : (2 * (h : ℂ)) = -(n : ℂ) * k := by
    apply mul_left_cancel₀ hfactor
    linear_combination (-(k : ℂ) ^ 2) * hn + (-4 * I * (h : ℂ) * k) * e
  have hz : (2 * (h : ℤ)) = -n * k := by exact_mod_cast hc
  have hd : (k : ℤ) ∣ ((2 * h : ℕ) : ℤ) := ⟨-n, by push_cast; rw [hz]; ring⟩
  exact Int.natCast_dvd_natCast.mp hd
theorem isVanishingSet_fullArc (hHarmonics : DistinctHarmonics.Holds)
    (hSelection : RotationFixedSelection.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) {k : ℕ} (hk : 1 ≤ k)
    (hnd : ¬ k ∣ 2 * maxFrequency S d.angle (2 * k)) (φ : realLabels)
    (u : RealPlane) (ρ γ : ℝ) (a₀ : ℤ) (hρ : 0 < ρ) :
    IsVanishingSet S d.angle k (vertexArc (polygonVertex k u ρ γ) φ a₀ (2 * k)) := by
  have hA : IsDistinctLabelledSet (2 * k) (vertexArc (polygonVertex k u ρ γ) φ a₀ (2 * k)) :=
    isDistinctLabelledSet_vertexArc (fun _ _ h => dvd_sub_of_polygonVertex_eq hk hρ h) le_rfl φ a₀
  refine ⟨⟨2 * k, le_rfl, hA⟩, ?_⟩
  intro Y hY hsub
  have hYeq : vertexArc (polygonVertex k u ρ γ) φ a₀ (2 * k) = Y :=
    (Set.finite_of_encard_eq_coe hA.card_eq).eq_of_subset_of_encard_le hsub
      (by rw [hY.card_eq, hA.card_eq])
  subst hYeq
  let c : LabelledPoints (2 * k) :=
    ⟨fun i => polygonVertex k u ρ γ (a₀ + 1 + ((i : ℕ) : ℤ)), fun _ => φ.1, fun _ => φ.2⟩
  have hpairs : vertexArc (polygonVertex k u ρ γ) φ a₀ (2 * k) = c.graph := by
    ext x
    constructor
    · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
      have h2' : a ≤ a₀ + 2 * k := by exact_mod_cast h2
      refine ⟨⟨(a - a₀ - 1).toNat, by omega⟩, ?_⟩
      have hidx : a₀ + 1 + (((a - a₀ - 1).toNat : ℕ) : ℤ) = a := by omega
      show (polygonVertex k u ρ γ (a₀ + 1 + (((a - a₀ - 1).toNat : ℕ) : ℤ)), φ) = _
      rw [hidx]
    · rintro ⟨i, rfl⟩
      have hi := i.2
      refine ⟨a₀ + 1 + ((i : ℕ) : ℤ), ⟨by omega, ?_⟩, rfl⟩
      push_cast
      omega
  have hen : Enumerates (vertexArc (polygonVertex k u ρ γ) φ a₀ (2 * k)) c := ⟨hA, hpairs⟩
  have hcd := points_injective_of_enumerates hen
  have hval : topLabelledHarmonic S d.angle k (vertexArc (polygonVertex k u ρ γ) φ a₀ (2 * k)) =
      configHarmonic S d.angle (-(maxFrequency S d.angle (2 * k) : ℤ)) c :=
    labelledSetHarmonic_eq hHarmonics d _ (by omega) hen
  rw [hval]
  have hpos : 0 < 2 * k := by omega
  let next : Fin (2 * k) → Fin (2 * k) := fun i => ⟨(i + 1) % (2 * k), Nat.mod_lt _ hpos⟩
  have hnext : ∀ i : Fin (2 * k), ((next i : Fin (2 * k)) : ℕ) =
      if (i : ℕ) + 1 = 2 * k then 0 else (i : ℕ) + 1 := by
    intro i
    have hi := i.2
    show ((i : ℕ) + 1) % (2 * k) = _
    split_ifs with h
    · rw [h, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  have hinj : Function.Injective next := by
    intro i j hij
    have h' := congrArg Fin.val hij
    rw [hnext, hnext] at h'
    have hi := i.2
    have hj := j.2
    apply Fin.ext
    split_ifs at h' <;> omega
  let ς : Equiv.Perm (Fin (2 * k)) :=
    Equiv.ofBijective next (Finite.injective_iff_bijective.mp hinj)
  have hstep : ∀ a : ℤ, u + rotate (Real.pi / k) (polygonVertex k u ρ γ a - u) =
      polygonVertex k u ρ γ (a + 1) := by
    intro a
    have hangle : γ + (a : ℝ) * (Real.pi / k) + Real.pi / k =
        γ + ((a + 1 : ℤ) : ℝ) * (Real.pi / k) := by
      push_cast
      ring
    rw [polygonVertex, add_sub_cancel_left, rotate_smul_unitVec, hangle, polygonVertex]
  have hrot : ∀ i, u + rotate (Real.pi / k) (c.points i - u) = c.points (ς i) := by
    intro i
    have hv := hnext i
    show u + rotate (Real.pi / k) (polygonVertex k u ρ γ (a₀ + 1 + ((i : ℕ) : ℤ)) - u) =
      polygonVertex k u ρ γ (a₀ + 1 + (((next i : Fin (2 * k)) : ℕ) : ℤ))
    rw [hstep, hv]
    split_ifs with h
    · have hidx : a₀ + 1 + ((i : ℕ) : ℤ) + 1 = (a₀ + 1 + ((0 : ℕ) : ℤ)) + 2 * k := by
        push_cast
        omega
      rw [hidx, polygonVertex_add_period hk]
    · have hidx : a₀ + 1 + ((i : ℕ) : ℤ) + 1 = a₀ + 1 + (((i : ℕ) + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [hidx]
  have hsel := hSelection m S d (2 * k) (by omega) c hcd (Real.pi / k) u ς hrot (fun _ => rfl)
    (-(maxFrequency S d.angle (2 * k) : ℤ))
  rcases mul_eq_zero.mp hsel with h1 | h2
  · exact absurd (dvd_two_mul_of_exp_eq_one hk (sub_eq_zero.mp h1).symm) hnd
  · exact h2
theorem sin_pos_of_odd_half_step {w b κ : ℝ} (hw : 0 < w) (hb : 1 ≤ b) (hbκ : b ≤ κ)
    (hπ : w * κ = Real.pi) : 0 < Real.sin ((2 * b - 1) * (w / 2)) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos (by linarith) (half_pos hw)
  · have hgap : 0 < w * (κ - b + 1 / 2) := mul_pos hw (by linarith)
    nlinarith
theorem isVanishingSet_halfArc (hHalving : VanishingSetHalving.HalvesVanishingSets)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) {k : ℕ} (hk : 1 ≤ k)
    (φ : realLabels) {j : ℕ} (hj2 : 2 ≤ j) (hj : j ≤ 2 * k)
    (hV : ∀ (u : RealPlane) (ρ γ : ℝ) (a₀ : ℤ), 0 < ρ →
      IsVanishingSet S d.angle k (vertexArc (polygonVertex k u ρ γ) φ a₀ j))
    (u : RealPlane) (ρ γ : ℝ) (a₀ : ℤ) (hρ : 0 < ρ) :
    IsVanishingSet S d.angle k (vertexArc (polygonVertex k u ρ γ) φ a₀ ((j + 1) / 2)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hw : 0 < Real.pi / (k : ℝ) := div_pos Real.pi_pos hk0
  have hwk : Real.pi / (k : ℝ) * k = Real.pi := div_mul_cancel₀ _ hk0.ne'
  have hj'k : (j + 1) / 2 ≤ k := by omega
  have hjj : j ≤ 2 * ((j + 1) / 2) := by omega
  obtain ⟨j', hj'⟩ : ∃ j', j' = (j + 1) / 2 := ⟨_, rfl⟩
  rw [← hj'] at hj'k hjj ⊢
  obtain ⟨ϑ, hϑ⟩ : ∃ ϑ, ϑ = γ + (2 * (a₀ : ℝ) + 1) * (Real.pi / k / 2) + Real.pi / 2 :=
    ⟨_, rfl⟩
  obtain ⟨l, hl_eq⟩ : ∃ l : Set RealPlane,
      l = {y | inner ℝ (unitVec ϑ) (y - u) = 0} := ⟨_, rfl⟩
  have hl : IsLine l := hl_eq ▸ isLine_normalSet ϑ u
  have hν : IsUnitNormal l (unitVec ϑ) := hl_eq ▸ isUnitNormal_normalSet ϑ u
  have hu : u ∈ l := by
    rw [hl_eq]
    show inner ℝ (unitVec ϑ) (u - u) = 0
    simp
  have hside : IsOpenSide l (posSide (unitVec ϑ) u) := ⟨u, hu, _, hν, rfl⟩
  have hrefl : lineReflection l = reflectAcross (unitVec ϑ) u :=
    lineReflection_eq hl hu hν
  have hQ' : IsDistinctLabelledSetIn j' (posSide (unitVec ϑ) u)
      (vertexArc (polygonVertex k u ρ γ) φ a₀ j') := by
    refine ⟨isDistinctLabelledSet_vertexArc (fun _ _ h => dvd_sub_of_polygonVertex_eq hk hρ h)
      (by omega) φ a₀, ?_⟩
    rintro _ ⟨_, ⟨a, ⟨h1, h2⟩, rfl⟩, rfl⟩
    show 0 < inner ℝ (unitVec ϑ) (polygonVertex k u ρ γ a - u)
    rw [inner_polygonVertex]
    refine mul_pos hρ ?_
    have hb1 : (1 : ℝ) ≤ (a : ℝ) - a₀ := by
      have : (a₀ : ℤ) + 1 ≤ a := h1
      have hcast : ((a₀ : ℝ) + 1) ≤ a := by exact_mod_cast this
      linarith
    have hbk : (a : ℝ) - a₀ ≤ k := by
      have hint : a ≤ a₀ + k := by omega
      have hcast : (a : ℝ) ≤ a₀ + k := by exact_mod_cast hint
      linarith
    have hangle : ϑ - (γ + (a : ℝ) * (Real.pi / k)) =
        Real.pi / 2 - (2 * ((a : ℝ) - a₀) - 1) * (Real.pi / k / 2) := by
      rw [hϑ]
      ring
    rw [hangle, Real.cos_pi_div_two_sub]
    exact sin_pos_of_odd_half_step hw hb1 hbk hwk
  have hsub : vertexArc (polygonVertex k u ρ γ) φ (a₀ - j') j ⊆
      reflectLabelled l (vertexArc (polygonVertex k u ρ γ) φ a₀ j') ∪
        vertexArc (polygonVertex k u ρ γ) φ a₀ j' := by
    rintro _ ⟨a, ⟨h1, h2⟩, rfl⟩
    by_cases ha : a ≤ a₀
    · left
      refine ⟨(polygonVertex k u ρ γ (2 * a₀ + 1 - a), φ),
        ⟨2 * a₀ + 1 - a, ⟨by omega, by omega⟩, rfl⟩, ?_⟩
      show (lineReflection l (polygonVertex k u ρ γ (2 * a₀ + 1 - a)), φ) =
        (polygonVertex k u ρ γ a, φ)
      have hidx : 2 * a₀ + 1 - (2 * a₀ + 1 - a) = a := by ring
      rw [hrefl, hϑ, reflectAcross_polygonVertex, hidx]
    · right
      exact ⟨a, ⟨by omega, by omega⟩, rfl⟩
  exact (hHalving m S d k hk l _ hl hside j' hj'k _ _ hQ' hsub (hV u ρ γ (a₀ - j') hρ)).1
theorem isVanishingSet_singleArc (hHalving : VanishingSetHalving.HalvesVanishingSets)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) {k : ℕ} (hk : 1 ≤ k)
    (φ : realLabels) (j : ℕ) :
    1 ≤ j → j ≤ 2 * k →
      (∀ (u : RealPlane) (ρ γ : ℝ) (a₀ : ℤ), 0 < ρ →
        IsVanishingSet S d.angle k (vertexArc (polygonVertex k u ρ γ) φ a₀ j)) →
      ∀ (u : RealPlane) (ρ γ : ℝ) (a₀ : ℤ), 0 < ρ →
        IsVanishingSet S d.angle k (vertexArc (polygonVertex k u ρ γ) φ a₀ 1) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h1 h2 hV
    by_cases hj1 : j = 1
    · subst hj1
      exact hV
    · exact ih ((j + 1) / 2) (by omega) (by omega) (by omega)
        (isVanishingSet_halfArc hHalving d hk φ (by omega) h2 hV)
theorem holds_of (hHalving : VanishingSetHalving.HalvesVanishingSets)
    (hHarmonics : DistinctHarmonics.Holds)
    (hSelection : RotationFixedSelection.Holds) :
    Holds := by
  intro m S d k hk
  by_contra hnd
  have htop : 1 ≤ maxFrequency S d.angle (2 * k) := by
    rcases Nat.eq_zero_or_pos (maxFrequency S d.angle (2 * k)) with h0 | h0
    · rw [h0] at hnd
      exact absurd (by simp) hnd
    · exact h0
  obtain ⟨c, hc, hne⟩ :=
    exists_config_harmonic_ne_zero hHarmonics d (by omega : 2 ≤ 2 * k) htop
  have hi₀ : 0 < 2 * k := by omega
  have hV := isVanishingSet_singleArc hHalving d hk (c.labelVec ⟨0, hi₀⟩) (2 * k) (by omega)
    le_rfl
    (fun u ρ γ a₀ hρ =>
      isVanishingSet_fullArc hHarmonics hSelection d hk hnd _ u ρ γ a₀ hρ)
  have hz := hV (c.points ⟨0, hi₀⟩ - unitVec 0) 1 0 (-1) one_pos
  have hsub : vertexArc (polygonVertex k (c.points ⟨0, hi₀⟩ - unitVec 0) 1 0)
      (c.labelVec ⟨0, hi₀⟩) (-1) 1 ⊆ c.graph := by
    rintro _ ⟨a, ⟨h1, h2⟩, rfl⟩
    have ha : a = 0 := by
      push_cast at h2
      omega
    subst ha
    refine ⟨⟨0, hi₀⟩, ?_⟩
    show (c.points ⟨0, hi₀⟩, c.labelVec ⟨0, hi₀⟩) = (polygonVertex k _ 1 0 0, _)
    simp [polygonVertex]
  have hzero := hz.harmonic_vanishes c.graph (isDistinctLabelledSet_graph c hc) hsub
  have hval : topLabelledHarmonic S d.angle k c.graph =
      configHarmonic S d.angle (-(maxFrequency S d.angle (2 * k) : ℤ)) c :=
    labelledSetHarmonic_eq hHarmonics d _ (by omega) ⟨isDistinctLabelledSet_graph c hc, rfl⟩
  exact hne (hval.symm.trans hzero)
end YangMills.Construction.EuclideanFunctionals.MaxFrequencyDivisible
end
