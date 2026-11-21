import YangMills.Construction.ReflectionPositivity.FactsOnSeparatedTuplesAndIsometriesOfOneTorusProof
import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOfFourSpaceAndTheirFunctionals
import YangMills.Construction.Continuum.ActionOfIsometriesOnDisjointTuples
import YangMills.Construction.Continuum.ChoicesOfDenseSetsAndTheCountableFamily
import YangMills.Construction.Continuum.ExistenceOfAStableChoice
import Mathlib
set_option autoImplicit false
open Matrix Set Topology
noncomputable section
namespace YangMills.Construction.DisjointTuples
open TestFunctions PeriodicLattice TorusMetric
namespace StableChoice
theorem continuous_partialDerivR4 {f : RealFun} (hf : IsC1R4 f) (μ : Fin 4) :
    Continuous (partialDerivR4 μ f) := by
  have h : partialDerivR4 μ f = fun x => fderiv ℝ f x (Pi.single μ 1) :=
    funext (EuclideanTuples.partialDerivR4_eq_fderiv hf μ)
  rw [h]
  exact (ContDiff.continuous_fderiv hf (by norm_num)).clm_apply continuous_const
theorem partialDerivR4_sub {f g : RealFun} (hf : IsC1R4 f) (hg : IsC1R4 g) (μ : Fin 4)
    (x : Fin 4 → ℝ) : partialDerivR4 μ (f - g) x = partialDerivR4 μ f x - partialDerivR4 μ g x := by
  have hfg : IsC1R4 (f - g) := ContDiff.sub hf hg
  rw [EuclideanTuples.partialDerivR4_eq_fderiv hfg, EuclideanTuples.partialDerivR4_eq_fderiv hf,
    EuclideanTuples.partialDerivR4_eq_fderiv hg,
    fderiv_sub ((hf.differentiable (by norm_num)) x) ((hg.differentiable (by norm_num)) x)]
  rfl
theorem partialDerivR4_eq_zero_of_not_mem {Q : Set (Fin 4 → ℝ)} (hQ : IsClosed Q) {f : RealFun}
    (hf : f ∈ c1ZeroOff Q) (μ : Fin 4) {x : Fin 4 → ℝ} (hx : x ∉ Q) :
    partialDerivR4 μ f x = 0 := by
  rw [EuclideanTuples.partialDerivR4_eq_fderiv hf.1]
  have hev : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hQ.isOpen_compl.mem_nhds hx] with y hy using hf.2 y hy
  rw [hev.fderiv_eq]
  simp
theorem c1NormR4_le {f : RealFun} {c : ℝ} (h0 : ∀ x, ‖f x‖ ≤ c)
    (h1 : ∀ μ x, ‖partialDerivR4 μ f x‖ ≤ c) : c1NormR4 f ≤ c := by
  unfold c1NormR4
  exact max_le (ciSup_le h0) (ciSup_le fun μ => ciSup_le (h1 μ))
theorem exists_countable_dense_subset_c1ZeroOff (Q : ratBoxUnions) :
    ∃ D : Set RealFun, D ⊆ c1ZeroOff Q ∧ D.Countable ∧
      IsDenseInC1ZeroOff Q D := by
  have hc : IsCompact (Q : Set (Fin 4 → ℝ)) := isCompact_of_mem_ratBoxUnions Q.2
  have hcl : IsClosed (Q : Set (Fin 4 → ℝ)) := hc.isClosed
  have : CompactSpace (Q : Set (Fin 4 → ℝ)) := isCompact_iff_compactSpace.1 hc
  let J : c1ZeroOff Q → C((Q : Set (Fin 4 → ℝ)), ℝ × (Fin 4 → ℝ)) := fun f =>
    ⟨fun x => (f.1 x, fun μ => partialDerivR4 μ f.1 x),
      (f.2.1.continuous.comp continuous_subtype_val).prodMk
        (continuous_pi fun μ => (continuous_partialDerivR4 f.2.1 μ).comp continuous_subtype_val)⟩
  obtain ⟨t, ht, htc, htd⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (range J)).exists_countable_dense_subset
  have hpre : ∀ y : t, ∃ f, J f = y := fun y => ht y.2
  choose g hg using hpre
  have := htc.to_subtype
  refine ⟨range fun y : t => (g y).1, ?_, countable_range _, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact (g y).2
  · intro f hf ε hε
    obtain ⟨b, hb, hd⟩ := Metric.mem_closure_iff.1 (htd ⟨⟨f, hf⟩, rfl⟩) (ε / 2) (half_pos hε)
    refine ⟨(g ⟨b, hb⟩).1, ⟨⟨b, hb⟩, rfl⟩, ?_⟩
    have hJ : J (g ⟨b, hb⟩) = b := hg ⟨b, hb⟩
    generalize g ⟨b, hb⟩ = u₀ at hJ ⊢
    obtain ⟨u, hu⟩ := u₀
    have hpt : ∀ x : (Q : Set (Fin 4 → ℝ)), dist (J ⟨f, hf⟩ x) (J ⟨u, hu⟩ x) ≤ ε / 2 := fun x => by
      rw [hJ]
      exact (ContinuousMap.dist_apply_le_dist x).trans hd.le
    have hle : c1NormR4 (u - f) ≤ ε / 2 := by
      apply c1NormR4_le
      · intro x
        by_cases hx : x ∈ (Q : Set (Fin 4 → ℝ))
        · have h := hpt ⟨x, hx⟩
          rw [Prod.dist_eq] at h
          have h1 : dist (f x) (u x) ≤ ε / 2 := (le_max_left _ _).trans h
          rw [Real.dist_eq, abs_sub_comm] at h1
          exact h1
        · have e : (u - f) x = 0 := by simp [hu.2 x hx, hf.2 x hx]
          rw [e, norm_zero]
          exact (half_pos hε).le
      · intro μ x
        rw [partialDerivR4_sub hu.1 hf.1]
        by_cases hx : x ∈ (Q : Set (Fin 4 → ℝ))
        · have h := hpt ⟨x, hx⟩
          rw [Prod.dist_eq] at h
          have h2 : dist (fun κ => partialDerivR4 κ f x) (fun κ => partialDerivR4 κ u x) ≤ ε / 2 :=
            (le_max_right _ _).trans h
          have h3 := (dist_pi_le_iff (half_pos hε).le).1 h2 μ
          rw [Real.dist_eq, abs_sub_comm] at h3
          exact h3
        · rw [partialDerivR4_eq_zero_of_not_mem hcl hu μ hx,
            partialDerivR4_eq_zero_of_not_mem hcl hf μ hx]
          simpa using (half_pos hε).le
    exact hle.trans_lt (half_lt_self hε)
theorem countable_setOf_isRatBox : {B : Set (Fin 4 → ℝ) | IsRatBox B}.Countable := by
  refine (countable_range fun p : (Fin 4 → ℚ) × (Fin 4 → ℚ) =>
    (univ.pi fun κ => Icc (p.1 κ : ℝ) (p.2 κ))).mono ?_
  rintro B ⟨s, t, -, rfl⟩
  exact ⟨(s, t), rfl⟩
theorem countable_ratBoxUnions : ratBoxUnions.Countable := by
  refine ((countable_ofPred_finite_subset countable_setOf_isRatBox).image sUnion).mono ?_
  rintro Q ⟨𝓑, hf, hB, rfl⟩
  exact ⟨𝓑, ⟨hf, hB⟩, rfl⟩
theorem isRatBox_image_translate {c : Fin 4 → ℚ} {B : Set (Fin 4 → ℝ)}
    (hB : IsRatBox B) : IsRatBox (translate (fun μ => (c μ : ℝ)) '' B) := by
  obtain ⟨s, t, hst, rfl⟩ := hB
  refine ⟨s + c, t + c, fun κ => by simpa using hst κ, ?_⟩
  ext y
  simp only [mem_image, mem_univ_pi, mem_Icc, Pi.add_apply, Rat.cast_add]
  constructor
  · rintro ⟨x, hx, rfl⟩ κ
    have e : translate (fun μ => (c μ : ℝ)) x κ = x κ + c κ := rfl
    rw [e]
    exact ⟨by linarith [(hx κ).1], by linarith [(hx κ).2]⟩
  · intro hy
    refine ⟨fun κ => y κ - c κ, fun κ => ⟨by linarith [(hy κ).1], by linarith [(hy κ).2]⟩, ?_⟩
    funext κ
    show y κ - c κ + c κ = y κ
    ring
theorem isRatBox_image_signedPerm {w : Matrix (Fin 4) (Fin 4) ℝ}
    (hw : w ∈ signedPermMatrices) {B : Set (Fin 4 → ℝ)} (hB : IsRatBox B) :
    IsRatBox ((fun x => w *ᵥ x) '' B) := by
  classical
  obtain ⟨ς, ε, hε, h⟩ := hw
  obtain ⟨s, t, hst, rfl⟩ := hB
  have hne : ∀ μ, ε μ = -1 → ε μ ≠ 1 := fun μ e => by rw [e]; norm_num
  refine ⟨fun μ => if ε μ = 1 then s (ς μ) else -t (ς μ),
    fun μ => if ε μ = 1 then t (ς μ) else -s (ς μ), fun μ => ?_, ?_⟩
  · show (if ε μ = 1 then s (ς μ) else -t (ς μ)) < (if ε μ = 1 then t (ς μ) else -s (ς μ))
    split_ifs
    · exact hst _
    · exact neg_lt_neg (hst _)
  ext y
  simp only [mem_image, mem_univ_pi, mem_Icc]
  constructor
  · rintro ⟨x, hx, rfl⟩ μ
    rw [h x μ]
    rcases hε μ with e | e
    · rw [if_pos e, if_pos e, e, one_mul]
      exact hx (ς μ)
    · rw [if_neg (hne μ e), if_neg (hne μ e), e]
      push_cast
      exact ⟨by linarith [(hx (ς μ)).2], by linarith [(hx (ς μ)).1]⟩
  · intro hy
    refine ⟨fun ν => ε (ς.symm ν) * y (ς.symm ν), fun κ => ?_, ?_⟩
    · obtain ⟨μ, rfl⟩ := ς.surjective κ
      simp only [Equiv.symm_apply_apply]
      have hμ := hy μ
      rcases hε μ with e | e
      · rw [if_pos e, if_pos e] at hμ
        rw [e, one_mul]
        exact hμ
      · rw [if_neg (hne μ e), if_neg (hne μ e)] at hμ
        push_cast at hμ
        rw [e]
        exact ⟨by linarith [hμ.2], by linarith [hμ.1]⟩
    · funext μ
      rw [h _ μ]
      simp only [Equiv.symm_apply_apply]
      rcases hε μ with e | e <;> rw [e] <;> ring
theorem image_mem_ratBoxUnions {g : (Fin 4 → ℝ) → Fin 4 → ℝ}
    (hg : ∀ B, IsRatBox B → IsRatBox (g '' B)) {Q : Set (Fin 4 → ℝ)}
    (hQ : Q ∈ ratBoxUnions) : g '' Q ∈ ratBoxUnions := by
  obtain ⟨𝓑, hf, hB, rfl⟩ := hQ
  refine ⟨image g '' 𝓑, hf.image _, ?_, image_sUnion⟩
  rintro _ ⟨B, hB', rfl⟩
  exact hg B (hB B hB')
def generators (L : ℕ) : Set ((Fin 4 → ℝ) → Fin 4 → ℝ) :=
  (fun w : Matrix (Fin 4) (Fin 4) ℝ => fun x => w *ᵥ x) '' signedPermMatrices ∪
    translate '' {v | ∀ μ, v μ ∈ powerDenominators L}
theorem countable_generators (L : ℕ) : (generators L).Countable := by
  have hW : signedPermMatrices.Countable :=
    (countable_range SignedFrame.toMatrix).mono fun w hw => by
      obtain ⟨r, rfl⟩ := (mem_signedPermMatrices_iff w).1 hw
      exact ⟨r, rfl⟩
  have hZ : (powerDenominators L).Countable :=
    countable_iUnion fun n => (countable_range fun k : ℤ => (L : ℝ) ^ (-(n : ℤ)) * k).mono (by
      rintro x ⟨k, rfl⟩
      exact ⟨k, rfl⟩)
  have hV : {v : Fin 4 → ℝ | ∀ μ, v μ ∈ powerDenominators L}.Countable :=
    (countable_univ_pi (s := fun _ : Fin 4 => powerDenominators L) fun _ => hZ).mono (by
      intro v hv μ _
      exact hv μ)
  exact (hW.image _).union (hV.image _)
theorem exists_rat_of_mem_powerDenominators {L : ℕ} {x : ℝ} (hx : x ∈ powerDenominators L) :
    ∃ q : ℚ, (q : ℝ) = x := by
  obtain ⟨n, k, rfl⟩ := mem_iUnion.1 hx
  exact ⟨(L : ℚ) ^ (-(n : ℤ)) * k, by push_cast; rfl⟩
theorem isSpaceIsometry_translate (v : Fin 4 → ℝ) :
    InfiniteLattice.IsSpaceIsometry (translate v) := by apply _root_.YangMills.Construction.SeparatedTuples.isEuclidIsometry_translate <;> assumption
theorem isSpaceIsometry_signedPerm {w : Matrix (Fin 4) (Fin 4) ℝ} (hw : w ∈ signedPermMatrices) :
    InfiniteLattice.IsSpaceIsometry fun x => w *ᵥ x := by
  obtain ⟨ς, ε, hε, h⟩ := hw
  intro x y
  unfold InfiniteLattice.euclidDist euclidNormVec
  congr 1
  have e : ∀ μ, (w *ᵥ x - w *ᵥ y) μ ^ 2 = (x - y) (ς μ) ^ 2 := fun μ => by
    rw [Pi.sub_apply, Pi.sub_apply, h x μ, h y μ]
    rcases hε μ with e | e <;> rw [e] <;> ring
  simp_rw [e]
  exact Equiv.sum_comp ς fun ν => (x - y) ν ^ 2
theorem mem_O4_of_mem_signedPermMatrices {w : Matrix (Fin 4) (Fin 4) ℝ}
    (hw : w ∈ signedPermMatrices) : w ∈ O4 := by apply _root_.YangMills.Construction.ReflectionPositivity.TorusTuples.SeparationAndSymmetry.mem_orthogonalGroup_of_mem_signedPermMatrices <;> assumption
theorem generator_isometry_and_isRatBox {L : ℕ} {g : (Fin 4 → ℝ) → Fin 4 → ℝ}
    (hg : g ∈ generators L) :
    (∃ (r₀ : Matrix (Fin 4) (Fin 4) ℝ) (c : Fin 4 → ℝ), InfiniteLattice.IsSpaceIsometry g ∧
      r₀ ∈ O4 ∧ g = affineEuclid r₀ c) ∧
    ∀ B, IsRatBox B → IsRatBox (g '' B) := by
  rcases hg with ⟨w, hw, rfl⟩ | ⟨v, hv, rfl⟩
  · refine ⟨⟨w, 0, isSpaceIsometry_signedPerm hw, mem_O4_of_mem_signedPermMatrices hw, ?_⟩,
      fun B hB => isRatBox_image_signedPerm hw hB⟩
    funext x
    simp [affineEuclid]
  · refine ⟨⟨1, v, isSpaceIsometry_translate v, one_mem _, ?_⟩, fun B hB => ?_⟩
    · funext x
      simp [affineEuclid, translate]
    · choose c hc using fun μ => exists_rat_of_mem_powerDenominators (hv μ)
      have e : v = fun μ => (c μ : ℝ) := funext fun μ => (hc μ).symm
      rw [e]
      exact isRatBox_image_translate hB
theorem generator_maps_c1ZeroOff (h : IsometryAction.IsometryActionFacts) {L : ℕ}
    {g : (Fin 4 → ℝ) → Fin 4 → ℝ} (hg : g ∈ generators L) {Q : Set (Fin 4 → ℝ)}
    (hQ : Q ∈ ratBoxUnions) {f : RealFun} (hf : f ∈ c1ZeroOff Q) :
    g '' Q ∈ ratBoxUnions ∧ pushFun g f ∈ c1ZeroOff (g '' Q) := by
  obtain ⟨⟨r₀, c, hiso, hr₀, hgr⟩, hbox⟩ := generator_isometry_and_isRatBox hg
  have hgQ := image_mem_ratBoxUnions hbox hQ
  refine ⟨hgQ, ?_⟩
  obtain ⟨h1, h2, h3⟩ := (mem_c1ZeroOff_iff hQ).1 hf
  obtain ⟨hc, hs⟩ := (h.1 g c r₀ hiso hr₀ hgr).1 f ⟨h1, h2⟩
  refine (mem_c1ZeroOff_iff hgQ).2 ⟨hc.1, hc.2, ?_⟩
  rw [hs]
  exact image_mono h3
def applyWord {L : ℕ} (l : List (generators L)) (φ : RealFun) : RealFun :=
  l.foldr (fun g h => pushFun g.1 h) φ
def wordOrbit (L : ℕ) (D0 : ratBoxUnions → Set RealFun) : Set RealFun :=
  ⋃ (Q : ratBoxUnions) (l : List (generators L)), applyWord l '' D0 Q
theorem countable_wordOrbit (L : ℕ) {D0 : ratBoxUnions → Set RealFun}
    (h : ∀ Q, (D0 Q).Countable) : (wordOrbit L D0).Countable := by
  have := countable_ratBoxUnions.to_subtype
  have := (countable_generators L).to_subtype
  exact countable_iUnion fun Q => countable_iUnion fun l => (h Q).image _
end StableChoice
open StableChoice in
theorem symmetricDenseChoiceExists_of_isometryActionFacts
    (h : IsometryAction.IsometryActionFacts) : SymmetricDenseChoiceExists := by
  intro L _ _
  choose D0 h0s h0c h0d using exists_countable_dense_subset_c1ZeroOff
  let D : ratBoxUnions → Set RealFun := fun Q => c1ZeroOff Q ∩ wordOrbit L D0
  have step : ∀ g ∈ generators L, ∀ φ ∈ iUnionFamily D,
      pushFun g φ ∈ iUnionFamily D := by
    intro g hg φ hφ
    obtain ⟨Q, hQ, hO⟩ := mem_iUnion.1 hφ
    obtain ⟨Q', hO⟩ := mem_iUnion.1 hO
    obtain ⟨l, φ₀, hφ₀, rfl⟩ := mem_iUnion.1 hO
    obtain ⟨hgQ, hmem⟩ := generator_maps_c1ZeroOff h hg Q.2 hQ
    refine mem_iUnion.2 ⟨⟨g '' Q, hgQ⟩, hmem, ?_⟩
    exact mem_iUnion.2 ⟨Q', mem_iUnion.2 ⟨⟨g, hg⟩ :: l, φ₀, hφ₀, rfl⟩⟩
  refine ⟨D, ⟨⟨fun Q => inter_subset_left,
    fun Q => (countable_wordOrbit L h0c).mono inter_subset_right,
    fun Q f hf ε hε => ?_⟩, fun φ hφ w hw => step _ (Or.inl ⟨w, hw, rfl⟩) φ hφ,
    fun φ hφ v hv => step _ (Or.inr ⟨v, hv, rfl⟩) φ hφ⟩⟩
  obtain ⟨g, hg, hn⟩ := h0d Q f hf ε hε
  exact ⟨g, ⟨h0s Q hg, mem_iUnion.2 ⟨Q, mem_iUnion.2 ⟨[], g, hg, rfl⟩⟩⟩, hn⟩
end YangMills.Construction.DisjointTuples
