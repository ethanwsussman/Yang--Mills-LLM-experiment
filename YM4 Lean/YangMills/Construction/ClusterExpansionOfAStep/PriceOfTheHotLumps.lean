import YangMills.Construction.ClusterExpansionOfAStep.HullsOfHotLumps
import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace TorusLumps
open BlockAverages LumpContours TorusFields
section Energy
variable {ℓ : StepParameters} {n : ℕ} [NeZero n] {r : ℕ} {W : TorusField n} {Y : Finset (TorusSite n)}
open Classical in
theorem card_hot_le_sum_componentEnergy (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (hr : 2 ^ 16 ≤ r)
    (hsub : thickening (2 * r) (torusHotSites ℓ W) ⊆ Y) {P : Finset (Finset (TorusSite n))}
    (hP : P ⊆ chainComponents r Y) :
    ℓ.threshold ^ 2 / 8 * (((torusHotLumps ℓ W).filter (· ⊆ P.biUnion id)).card : ℝ) ≤
      ∑ X ∈ P, componentEnergy ℓ W X := by
  set H := (torusHotLumps ℓ W).filter (· ⊆ P.biUnion id) with hH
  have hch : ∀ l ∈ H, ∃ p : TorusPlaquette n, p.2.1 < p.2.2 ∧ ℓ.threshold ≤ curvature W p.1 p.2.1 p.2.2 ∧
      ∃ z ∈ plaquetteVertices p.1 p.2.1 p.2.2, l = torusLumpOf ℓ z := by
    intro l hl
    obtain ⟨x, μ, ν, h1, h2, z, hz, h3⟩ :=
      (mem_torusHotLumps_iff ℓ hfit hLn W l).mp (Finset.mem_filter.mp hl).1
    exact ⟨(x, μ, ν), h1, h2, z, hz, h3⟩
  choose! f hf1 hf2 hf3 using hch
  have hfib : ∀ a ∈ H.image f, (H.filter fun l => f l = a).card ≤ 4 := by
    intro a _
    have hsubs : (H.filter fun l => f l = a) ⊆
        (plaquetteVertices a.1 a.2.1 a.2.2).toFinset.image (torusLumpOf ℓ) := by
      intro l hl
      obtain ⟨hlH, hfa⟩ := Finset.mem_filter.mp hl
      obtain ⟨z, hz, hlz⟩ := hf3 l hlH
      rw [hfa] at hz
      exact Finset.mem_image.mpr ⟨z, List.mem_toFinset.mpr hz, hlz.symm⟩
    refine (Finset.card_le_card hsubs).trans (Finset.card_image_le.trans ?_)
    exact (List.toFinset_card_le _).trans (by simp [plaquetteVertices])
  have hcard : H.card ≤ 4 * (H.image f).card := Finset.card_le_mul_card_image H 4 hfib
  have hsubQ : H.image f ⊆ P.biUnion (nearPlaquettes ℓ W) := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hlhot, hlP⟩ := Finset.mem_filter.mp hl
    obtain ⟨z, hz, hlz⟩ := hf3 l hl
    have hzl : z ∈ l := by rw [hlz]; exact mem_torusLumpOf_self z
    obtain ⟨X, hXP, hzX⟩ := Finset.mem_biUnion.mp (hlP hzl)
    have hX := hP hXP
    have hlX := subset_of_mem_torusHotLumps_of_mem hfit hLn hr hsub hX hlhot hzl hzX
    refine Finset.mem_biUnion.mpr ⟨X, hXP, Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf1 l hl, fun _ _ => Finset.mem_univ _⟩, z, hz, ?_⟩⟩
    exact subset_thickening_self _ _ (mem_lumpCore.mpr ⟨l, hlhot, hlX, hzl⟩)
  have hpair : (↑P : Set (Finset (TorusSite n))).PairwiseDisjoint (nearPlaquettes ℓ W) := by
    intro X hX X' hX' hne
    rw [Function.onFun, Finset.disjoint_left]
    exact fun p hp hp' => hne (eq_of_mem_nearPlaquettes hsub hr (hP hX) (hP hX') hp hp')
  have hsum : ∑ X ∈ P, componentEnergy ℓ W X =
      ∑ p ∈ P.biUnion (nearPlaquettes ℓ W), plaquetteEnergy W p.1 p.2.1 p.2.2 := by
    rw [Finset.sum_biUnion hpair]
    rfl
  rw [hsum]
  have hQ : ((H.image f).card : ℝ) * (ℓ.threshold ^ 2 / 2) ≤
      ∑ p ∈ H.image f, plaquetteEnergy W p.1 p.2.1 p.2.2 := by
    rw [← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun p hp => ?_
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    rw [plaquetteEnergy_eq_curvature_sq]
    have h1 := hf2 l hl
    have h2 := hfit.σ_pos
    nlinarith
  have hle : ∑ p ∈ H.image f, plaquetteEnergy W p.1 p.2.1 p.2.2 ≤
      ∑ p ∈ P.biUnion (nearPlaquettes ℓ W), plaquetteEnergy W p.1 p.2.1 p.2.2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubQ fun p _ _ => plaquetteEnergy_nonneg W _ _ _
  have hc : (H.card : ℝ) ≤ 4 * ((H.image f).card : ℝ) := by exact_mod_cast hcard
  nlinarith
open Classical in
theorem excessLength_eq_zero (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (hr : 2 ^ 16 ≤ r)
    {P : Finset (Finset (TorusSite n))}
    (hP : ∀ X ∈ P, X = thickening (2 * r) (lumpCore ℓ W X)) :
    excessLength ℓ r (P.biUnion id) W = 0 := by
  have hempty : P.biUnion id \ thickening (4 * r)
      (((torusHotLumps ℓ W).filter (· ⊆ P.biUnion id)).image lumpCenter) = ∅ := by
    rw [Finset.sdiff_eq_empty_iff_subset]
    intro z hz
    obtain ⟨X, hX, hzX⟩ := Finset.mem_biUnion.mp hz
    have hz2 : z ∈ X := hzX
    rw [hP X hX] at hz2
    obtain ⟨x, hx, hzx⟩ := (mem_thickening _ _ _).mp hz2
    obtain ⟨l, hl, hlX, hxl⟩ := mem_lumpCore.mp hx
    have hlP : l ⊆ P.biUnion id := fun u hu => Finset.mem_biUnion.mpr ⟨X, hX, hlX hu⟩
    refine (mem_thickening _ _ _).mpr ⟨lumpCenter l, Finset.mem_image.mpr
      ⟨l, Finset.mem_filter.mpr ⟨hl, hlP⟩, rfl⟩, ?_⟩
    obtain ⟨_, _, _, _, _, u, _, hlu⟩ := (mem_torusHotLumps_iff ℓ hfit hLn W l).mp hl
    have hm : ∃ m : TorusSite n, ∀ y ∈ l, supDist y m ≤ 2 ^ 14 := by
      rw [hlu]
      exact exists_centre_of_torusLumpOf hfit hLn u
    have hmid : ∀ y ∈ l, supDist y (lumpCenter l) ≤ 2 ^ 14 := by
      unfold lumpCenter
      rw [dif_pos hm]
      exact hm.choose_spec
    have := supDist_triangle z x (lumpCenter l)
    have := hmid x hxl
    omega
  unfold excessLength
  rw [hempty]
  have h0 : 0 ∈ {k | ∃ C : Finset (TorusSite n), C.card = k ∧
      (∅ : Finset (TorusSite n)) ⊆ thickening (4 * r) C} :=
    ⟨∅, by simp, by simp⟩
  exact Nat.le_zero.mp (Nat.sInf_le h0)
end Energy
section Measurability
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
open Classical in
def hotPlaquettes (ℓ : StepParameters) (W : TorusField n) : Finset (TorusPlaquette n) :=
  Finset.univ.filter fun p => p.2.1 < p.2.2 ∧ ℓ.threshold ≤ curvature W p.1 p.2.1 p.2.2
theorem torusHotLumps_eq_of_hotPlaquettes_eq (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n)
    {W W' : TorusField n} (h : hotPlaquettes ℓ W = hotPlaquettes ℓ W') :
    torusHotLumps ℓ W = torusHotLumps ℓ W' := by
  classical
  have hiff : ∀ (x : TorusSite n) (μ ν : Fin 4), μ < ν →
      (ℓ.threshold ≤ curvature W x μ ν ↔ ℓ.threshold ≤ curvature W' x μ ν) := by
    intro x μ ν hlt
    have h1 : (x, μ, ν) ∈ hotPlaquettes ℓ W ↔ (x, μ, ν) ∈ hotPlaquettes ℓ W' := by rw [h]
    simpa [hotPlaquettes, hlt] using h1
  ext l
  rw [mem_torusHotLumps_iff ℓ hfit hLn, mem_torusHotLumps_iff ℓ hfit hLn]
  constructor
  · rintro ⟨x, μ, ν, h1, h2, h3⟩
    exact ⟨x, μ, ν, h1, (hiff x μ ν h1).mp h2, h3⟩
  · rintro ⟨x, μ, ν, h1, h2, h3⟩
    exact ⟨x, μ, ν, h1, (hiff x μ ν h1).mpr h2, h3⟩
theorem measurableSet_hotPlaquettes_eq (A : Finset (TorusPlaquette n)) :
    MeasurableSet {W : TorusField n | hotPlaquettes ℓ W = A} := by
  classical
  have : {W : TorusField n | hotPlaquettes ℓ W = A} =
      ⋂ p : TorusPlaquette n, {W : TorusField n |
        (p.2.1 < p.2.2 ∧ ℓ.threshold ≤ curvature W p.1 p.2.1 p.2.2) ↔ p ∈ A} := by
    ext W
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.ext_iff, hotPlaquettes, Finset.mem_filter,
      Finset.mem_univ, true_and]
  rw [this]
  refine MeasurableSet.iInter fun p => ?_
  have hc := continuous_curvature (n := n) p.1 p.2.1 p.2.2
  by_cases hlt : p.2.1 < p.2.2
  · by_cases hp : p ∈ A
    · simp only [hp, iff_true, hlt, true_and]
      exact (isClosed_le continuous_const hc).measurableSet
    · simp only [hp, iff_false, not_le, hlt, true_and]
      exact (isOpen_lt hc continuous_const).measurableSet
  · by_cases hp : p ∈ A
    · simp [hp, hlt]
    · simp [hp, hlt]
theorem measurableSet_torusHotLumps_eq (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n)
    (H : Finset (Finset (TorusSite n))) :
    MeasurableSet {W : TorusField n | torusHotLumps ℓ W = H} := by
  classical
  have : {W : TorusField n | torusHotLumps ℓ W = H} =
      ⋃ A ∈ {A : Finset (TorusPlaquette n) | ∃ W', hotPlaquettes ℓ W' = A ∧ torusHotLumps ℓ W' = H},
        {W : TorusField n | hotPlaquettes ℓ W = A} := by
    ext W
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro h
      exact ⟨_, ⟨W, rfl, h⟩, rfl⟩
    · rintro ⟨A, ⟨W', h1, h2⟩, h3⟩
      rw [← h2]
      exact torusHotLumps_eq_of_hotPlaquettes_eq hfit hLn (h3.trans h1.symm)
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun A _ => measurableSet_hotPlaquettes_eq A
theorem measurable_of_eqOn_torusHotLumps_fibres (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n)
    {F : TorusField n → ℝ}
    (hF : ∀ W₀ : TorusField n, ∃ g : TorusField n → ℝ, Measurable g ∧
      ∀ W, torusHotLumps ℓ W = torusHotLumps ℓ W₀ → F W = g W) :
    Measurable F := by
  classical
  intro s hs
  have : F ⁻¹' s = ⋃ W₀ ∈ {W₀ : TorusField n | True},
      ({W | torusHotLumps ℓ W = torusHotLumps ℓ W₀} ∩ F ⁻¹' s) := by
    ext W
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, exists_prop,
      true_and]
    exact ⟨fun h => ⟨W, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  have h2 : F ⁻¹' s = ⋃ H ∈ {H : Finset (Finset (TorusSite n)) | ∃ W₀ : TorusField n,
      torusHotLumps ℓ W₀ = H}, ({W | torusHotLumps ℓ W = H} ∩ F ⁻¹' s) := by
    ext W
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, exists_prop]
    exact ⟨fun h => ⟨_, ⟨W, rfl⟩, rfl, h⟩, fun ⟨_, _, _, h⟩ => h⟩
  rw [h2]
  refine MeasurableSet.biUnion (Set.to_countable _) ?_
  rintro H ⟨W₀, rfl⟩
  obtain ⟨g, hg, hgF⟩ := hF W₀
  have h3 : {W | torusHotLumps ℓ W = torusHotLumps ℓ W₀} ∩ F ⁻¹' s =
      {W | torusHotLumps ℓ W = torusHotLumps ℓ W₀} ∩ g ⁻¹' s := by
    ext W
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    exact and_congr_right fun h => by rw [hgF W h]
  rw [h3]
  exact (measurableSet_torusHotLumps_eq hfit hLn _).inter (hg hs)
end Measurability
section Perturbation
variable {ℓ : StepParameters} {n : ℕ} [NeZero n] {r : ℕ}
theorem mem_torusHotSites_of_mem_plaquetteVertices (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n)
    {W : TorusField n} {x : TorusSite n} {μ ν : Fin 4}
    (hlt : μ < ν) (hs : ℓ.threshold ≤ curvature W x μ ν) {z : TorusSite n}
    (hz : z ∈ plaquetteVertices x μ ν) :
    z ∈ torusHotSites ℓ W :=
  mem_torusHotSites_iff.mpr ⟨torusLumpOf ℓ z,
    (mem_torusHotLumps_iff ℓ hfit hLn W _).mpr ⟨x, μ, ν, hlt, hs, z, hz, rfl⟩,
    mem_torusLumpOf_self z⟩
omit [NeZero n] in
theorem base_mem_plaquetteVertices (x : TorusSite n) (μ ν : Fin 4) : x ∈ plaquetteVertices x μ ν := by
  simp [plaquetteVertices]
theorem eventually_torusHotLumps_perturb_eq (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (hr : 1 ≤ r)
    {W : TorusField n} {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (hfar : ∀ l, ∀ z ∈ torusHotSites ℓ W, r ≤ supDist (c l).1 z) :
    ∀ᶠ σ in nhds (0 : Fin k → ℝ), torusHotLumps ℓ (perturb c X σ W) = torusHotLumps ℓ W := by
  classical
  have hall : ∀ p : TorusPlaquette n, ∀ᶠ σ in nhds (0 : Fin k → ℝ),
      ((p.2.1 < p.2.2 ∧ ℓ.threshold ≤ curvature (perturb c X σ W) p.1 p.2.1 p.2.2) ↔
        (p.2.1 < p.2.2 ∧ ℓ.threshold ≤ curvature W p.1 p.2.1 p.2.2)) := by
    rintro ⟨x, μ, ν⟩
    simp only
    by_cases hlt : μ < ν
    · simp only [hlt, true_and]
      by_cases hs : ℓ.threshold ≤ curvature W x μ ν
      · have hcorner : ∀ z ∈ plaquetteVertices x μ ν, ∀ l, (c l).1 ≠ z := by
          intro z hz l he
          have h1 := hfar l z (mem_torusHotSites_of_mem_plaquetteVertices hfit hLn hlt hs hz)
          rw [he, supDist_self] at h1
          omega
        have m1 : x ∈ plaquetteVertices x μ ν := by simp [plaquetteVertices]
        have m2 : x + TorusFields.unitStep n μ ∈ plaquetteVertices x μ ν := by simp [plaquetteVertices]
        have m3 : x + TorusFields.unitStep n ν ∈ plaquetteVertices x μ ν := by simp [plaquetteVertices]
        have hoff : ∀ σ : Fin k → ℝ, holonomy (perturb c X σ W) x μ ν = holonomy W x μ ν := by
          intro σ
          refine holonomy_perturb_of_ne c X σ W x μ ν ?_ ?_ ?_ ?_ <;> intro l he
          · exact hcorner _ m1 l (congrArg Prod.fst he)
          · exact hcorner _ m2 l (congrArg Prod.fst he)
          · exact hcorner _ m3 l (congrArg Prod.fst he)
          · exact hcorner _ m1 l (congrArg Prod.fst he)
        refine Filter.Eventually.of_forall fun σ => ?_
        unfold curvature
        rw [hoff]
      · have hcont : Continuous fun σ : Fin k → ℝ => curvature (perturb c X σ W) x μ ν :=
          (continuous_curvature x μ ν).comp (continuous_perturb c X W)
        have hlt0 : curvature (perturb c X 0 W) x μ ν < ℓ.threshold := by
          rw [perturb_zero]
          exact not_le.mp hs
        filter_upwards [hcont.continuousAt.eventually (gt_mem_nhds hlt0)] with σ hσ
        exact iff_of_false (not_le.mpr hσ) hs
    · exact Filter.Eventually.of_forall fun σ => by simp [hlt]
  have hev : ∀ᶠ σ in nhds (0 : Fin k → ℝ), hotPlaquettes ℓ (perturb c X σ W) = hotPlaquettes ℓ W := by
    have := Filter.eventually_all.mpr hall
    filter_upwards [this] with σ hσ
    ext p
    simp only [hotPlaquettes, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hσ p
  filter_upwards [hev] with σ hσ
  exact torusHotLumps_eq_of_hotPlaquettes_eq hfit hLn hσ
end Perturbation
end TorusLumps
end YangMills.Construction
end
