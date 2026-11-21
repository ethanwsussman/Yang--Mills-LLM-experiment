import YangMills.Construction.ChessboardTori.CoveringMapOnTheCellsOfAGridProof
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefined
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.QuotientGeometry
open Kind
open WellPosedness
open TorusMetric (euclidNormVec torusEuclidNorm torusProj exists_coe_eq_abs_eq_norm
  addCircle_norm_coe_le_abs)
variable (P : Params) (K : Kind)
theorem torusProj_eq_zero_iff (x : Fin 4 → ℝ) :
    torusProj P.side x = 0 ↔ x ∈ InfiniteLattice.latticeSubgroup P.side := by
  constructor
  · intro h
    have h' : ∀ μ, ∃ n : ℤ, n • P.side = x μ := fun μ =>
      AddCircle.coe_eq_zero_iff _ |>.1 (congrFun h μ)
    choose n hn using h'
    exact ⟨n, fun μ => by rw [← hn μ, zsmul_eq_mul]⟩
  · rintro ⟨n, hn⟩
    funext μ
    exact (AddCircle.coe_eq_zero_iff _).2 ⟨n μ, by rw [hn μ, zsmul_eq_mul]⟩
theorem quotMap_add (x y : Fin 4 → ℝ) :
    K.quotMap P (x + y) = K.quotMap P x + K.quotMap P y := by
  cases K with
  | euclidean => rfl
  | torus => rfl
theorem quotMap_surjective : Function.Surjective (K.quotMap P) := by
  cases K with
  | euclidean => exact fun p => ⟨p, rfl⟩
  | torus =>
    intro p
    have h : ∀ μ, ∃ v : ℝ, (v : AddCircle P.side) = p μ := fun μ =>
      QuotientAddGroup.mk_surjective (p μ)
    choose b hb using h
    exact ⟨b, funext hb⟩
theorem quotMap_eq_zero_iff (x : Fin 4 → ℝ) : K.quotMap P x = 0 ↔ x ∈ K.periodGroup P := by
  cases K with
  | euclidean => exact (AddSubgroup.mem_bot).symm
  | torus => exact torusProj_eq_zero_iff P x
def quotAddHom : (Fin 4 → ℝ) →+ K.Pt P :=
  AddMonoidHom.mk' (K.quotMap P) (quotMap_add P K)
theorem quotMap_sub (x y : Fin 4 → ℝ) :
    K.quotMap P (x - y) = K.quotMap P x - K.quotMap P y :=
  map_sub (quotAddHom P K) x y
theorem quotMap_eq_iff (x y : Fin 4 → ℝ) :
    K.quotMap P x = K.quotMap P y ↔ x - y ∈ K.periodGroup P := by
  rw [← quotMap_eq_zero_iff, quotMap_sub, sub_eq_zero]
theorem euclidNormVec_le_of_abs_le {a b : Fin 4 → ℝ} (h : ∀ μ, |a μ| ≤ |b μ|) :
    euclidNormVec a ≤ euclidNormVec b := by apply _root_.YangMills.Construction.ChessboardTori.ProjOnGridCellsProof.euclidNormVec_mono <;> assumption
theorem exists_nearest_period (z : Fin 4 → ℝ) :
    ∃ γ ∈ K.periodGroup P, ∀ γ' ∈ K.periodGroup P,
      euclidNormVec (z - γ) ≤ euclidNormVec (z - γ') := by
  cases K with
  | euclidean =>
    refine ⟨0, zero_mem _, fun γ' hγ' => ?_⟩
    have : γ' = 0 := AddSubgroup.mem_bot.1 hγ'
    rw [this]
  | torus =>
    choose b hb hb' using fun μ => exists_coe_eq_abs_eq_norm ((z μ : AddCircle P.side))
    have hzb : z - b ∈ Kind.torus.periodGroup P := by
      refine (quotMap_eq_iff P Kind.torus z b).1 ?_
      exact (funext fun μ => (hb μ).symm)
    refine ⟨z - b, hzb, fun γ' hγ' => ?_⟩
    rw [sub_sub_cancel]
    refine euclidNormVec_le_of_abs_le fun μ => ?_
    have hw : Kind.torus.quotMap P (z - γ') = Kind.torus.quotMap P z :=
      (quotMap_eq_iff P Kind.torus _ _).2 (by
        rw [sub_sub_cancel_left]
        exact neg_mem hγ')
    have hw' : (((z - γ') μ : ℝ) : AddCircle P.side) = (z μ : AddCircle P.side) := congrFun hw μ
    rw [hb' μ, ← hw']
    exact addCircle_norm_coe_le_abs _
theorem translateNorms_has_least (x y : Fin 4 → ℝ) :
    ∃ r, IsLeast (translateNorms P K x y) r := by
  obtain ⟨γ, hγ, h⟩ := exists_nearest_period P K (x - y)
  refine ⟨_, ⟨γ, hγ, rfl⟩, ?_⟩
  rintro _ ⟨γ', hγ', rfl⟩
  exact h γ' hγ'
theorem translateNorms_add_period_left (x y γ : Fin 4 → ℝ) (hγ : γ ∈ K.periodGroup P) :
    translateNorms P K (x + γ) y = translateNorms P K x y := by
  ext r
  constructor
  · rintro ⟨γ', hγ', rfl⟩
    exact ⟨γ' - γ, sub_mem hγ' hγ, by congr 1; abel⟩
  · rintro ⟨γ', hγ', rfl⟩
    exact ⟨γ' + γ, add_mem hγ' hγ, by congr 1; abel⟩
theorem translateNorms_add_period_right (x y γ : Fin 4 → ℝ) (hγ : γ ∈ K.periodGroup P) :
    translateNorms P K x (y + γ) = translateNorms P K x y := by
  ext r
  constructor
  · rintro ⟨γ', hγ', rfl⟩
    exact ⟨γ + γ', add_mem hγ hγ', by congr 1; abel⟩
  · rintro ⟨γ', hγ', rfl⟩
    exact ⟨γ' - γ, sub_mem hγ' hγ, by congr 1; abel⟩
theorem quotDist_set_eq (x y : Fin 4 → ℝ) :
    {r | ∃ a a', IsLift P K (K.quotMap P x) a ∧ IsLift P K (K.quotMap P y) a' ∧
      ∃ γ ∈ K.periodGroup P, r = euclidNormVec (a - a' - γ)} = translateNorms P K x y := by
  ext r
  constructor
  · rintro ⟨a, a', ha, ha', γ, hγ, rfl⟩
    have h1 : a - x ∈ K.periodGroup P := (quotMap_eq_iff P K a x).1 ha
    have h2 : a' - y ∈ K.periodGroup P := (quotMap_eq_iff P K a' y).1 ha'
    exact ⟨γ - (a - x) + (a' - y), add_mem (sub_mem hγ h1) h2, by congr 1; abel⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨x, y, rfl, rfl, γ, hγ, rfl⟩
theorem quotDist_isLeast (x y : Fin 4 → ℝ) :
    IsLeast (translateNorms P K x y)
      (quotDist P K (K.quotMap P x) (K.quotMap P y)) := by
  obtain ⟨r, hr⟩ := translateNorms_has_least P K x y
  have h : quotDist P K (K.quotMap P x) (K.quotMap P y) = r := by
    unfold quotDist
    rw [quotDist_set_eq]
    exact hr.csInf_eq
  rw [h]
  exact hr
theorem quotDist_nonneg (p q : K.Pt P) : 0 ≤ quotDist P K p q := by
  obtain ⟨x, rfl⟩ := quotMap_surjective P K p
  obtain ⟨y, rfl⟩ := quotMap_surjective P K q
  obtain ⟨γ, -, h⟩ := (quotDist_isLeast P K x y).1
  rw [h]
  exact Real.sqrt_nonneg _
theorem quotDist_euclidean (p q : Fin 4 → ℝ) :
    quotDist P Kind.euclidean p q = euclidNormVec (p - q) := by
  obtain ⟨γ, hγ, h⟩ := (quotDist_isLeast P Kind.euclidean p q).1
  have hγ0 : γ = 0 := AddSubgroup.mem_bot.1 hγ
  rw [hγ0, sub_zero] at h
  exact h
theorem quotDist_torus (p q : P.Torus) :
    quotDist P Kind.torus p q = torusEuclidNorm (p - q) ∧
      IsLeast (euclidNormVec '' (torusProj P.side ⁻¹' {p - q})) (quotDist P Kind.torus p q) := by
  obtain ⟨x, rfl⟩ := quotMap_surjective P Kind.torus p
  obtain ⟨y, rfl⟩ := quotMap_surjective P Kind.torus q
  have hs : euclidNormVec '' (torusProj P.side ⁻¹' {Kind.torus.quotMap P x -
      Kind.torus.quotMap P y}) = translateNorms P Kind.torus x y := by
    ext r
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' : Kind.torus.quotMap P w = Kind.torus.quotMap P (x - y) :=
        (show torusProj P.side w = _ from hw).trans (quotMap_sub P Kind.torus x y).symm
      have hγ : x - y - w ∈ Kind.torus.periodGroup P :=
        (quotMap_eq_iff P Kind.torus _ _).1 hw'.symm
      exact ⟨x - y - w, hγ, by rw [sub_sub_cancel]⟩
    · rintro ⟨γ, hγ, rfl⟩
      refine ⟨x - y - γ, ?_, rfl⟩
      have h0 : Kind.torus.quotMap P (x - y - γ) = Kind.torus.quotMap P (x - y) :=
        (quotMap_eq_iff P Kind.torus _ _).2 (by
          rw [sub_sub_cancel_left]
          exact neg_mem hγ)
      exact h0.trans (quotMap_sub P Kind.torus x y)
  have hl := quotDist_isLeast P Kind.torus x y
  rw [← hs] at hl
  exact ⟨hl.csInf_eq.symm, hl⟩
theorem isGammaPeriodic_comp_quotMap (u : K.Pt P → ℝ) :
    IsGammaPeriodic P K (u ∘ K.quotMap P) := by
  intro x γ hγ
  have h : K.quotMap P (x + γ) = K.quotMap P x :=
    (quotMap_eq_iff P K _ _).2 (by rw [add_sub_cancel_left]; exact hγ)
  simp only [Function.comp_apply, h]
theorem isGammaPeriodic_partialDerivR4 (F : (Fin 4 → ℝ) → ℝ) (hF : IsGammaPeriodic P K F)
    (μ : Fin 4) : IsGammaPeriodic P K (TestFunctions.partialDerivR4 μ F) := by
  intro x γ hγ
  have h : (fun t : ℝ => F (x + γ + t • Pi.single μ (1 : ℝ))) =
      fun t : ℝ => F (x + t • Pi.single μ (1 : ℝ)) := by
    funext t
    rw [show x + γ + t • Pi.single μ (1 : ℝ) = x + t • Pi.single μ (1 : ℝ) + γ by abel]
    exact hF _ γ hγ
  simp only [TestFunctions.partialDerivR4, h]
theorem existsUnique_descent (g : (Fin 4 → ℝ) → ℝ) (hg : IsGammaPeriodic P K g) :
    ∃! v : K.Pt P → ℝ, v ∘ K.quotMap P = g := by
  have hsurj := quotMap_surjective P K
  choose l hl using hsurj
  have h0 : (fun p => g (l p)) ∘ K.quotMap P = g := by
    funext x
    have hγ : l (K.quotMap P x) - x ∈ K.periodGroup P :=
      (quotMap_eq_iff P K _ _).1 (hl _)
    have := hg x _ hγ
    rw [add_sub_cancel] at this
    exact this
  refine ⟨fun p => g (l p), h0, fun v hv => ?_⟩
  exact (quotMap_surjective P K).injective_comp_right (hv.trans h0.symm)
theorem partialDeriv_comp_quotMap (u : K.Pt P → ℝ) (μ : Fin 4) :
    partialDeriv P K μ u ∘ K.quotMap P =
      TestFunctions.partialDerivR4 μ (u ∘ K.quotMap P) := by
  have h := (existsUnique_descent P K _
    (isGammaPeriodic_partialDerivR4 P K _ (isGammaPeriodic_comp_quotMap P K u) μ)).exists
  exact Classical.epsilon_spec h
theorem lipConstQ_isLeast (u : K.Pt P → ℝ) (hu : IsLipschitzQ P K u) :
    IsLeast (lipschitzBounds P K u) (lipConstQ P K u) := by
  have hne : (lipschitzBounds P K u).Nonempty := by
    obtain ⟨C, h0, h⟩ := hu
    exact ⟨C, h0, h⟩
  have hbdd : BddBelow (lipschitzBounds P K u) := ⟨0, fun C hC => hC.1⟩
  change IsLeast (lipschitzBounds P K u) (sInf (lipschitzBounds P K u))
  refine ⟨⟨le_csInf hne fun C hC => hC.1, fun p q => ?_⟩, fun C hC => csInf_le hbdd hC⟩
  rcases (quotDist_nonneg P K p q).eq_or_lt with hd | hd
  · obtain ⟨C, hC⟩ := hne
    have := hC.2 p q
    rw [← hd, mul_zero] at this
    rw [← hd, mul_zero]
    exact this
  · rw [← div_le_iff₀ hd]
    refine le_csInf hne fun C hC => ?_
    rw [div_le_iff₀ hd]
    exact hC.2 p q
theorem wellPosed : WellPosed := by
  intro P K
  refine ⟨⟨quotMap_add P K, quotMap_surjective P K, quotMap_eq_zero_iff P K⟩,
    quotMap_surjective P K, ?_, translateNorms_has_least P K, ?_, ?_, quotDist_isLeast P K,
    quotDist_euclidean P, quotDist_torus P, ?_, ?_, ?_⟩
  · intro x y
    constructor
    · rintro ⟨p, hx, hy⟩
      exact (quotMap_eq_iff P K x y).1 (Eq.trans hx (Eq.symm hy))
    · intro h
      exact ⟨_, rfl, ((quotMap_eq_iff P K x y).2 h).symm⟩
  · intro x y γ hγ r
    rw [translateNorms_add_period_left P K x y γ hγ, translateNorms_add_period_right P K x y γ hγ]
    exact ⟨Iff.rfl, Iff.rfl⟩
  · intro p q
    refine ⟨quotDist P K p q, ?_, ?_⟩
    · intro x y hx hy
      have h := quotDist_isLeast P K x y
      have hx2 : K.quotMap P x = p := hx
      have hy2 : K.quotMap P y = q := hy
      rw [hx2, hy2] at h
      exact h
    · intro r hr
      obtain ⟨x, hx⟩ := quotMap_surjective P K p
      obtain ⟨y, hy⟩ := quotMap_surjective P K q
      have h := quotDist_isLeast P K x y
      rw [hx, hy] at h
      exact (hr x y hx hy).unique h
  · intro u _
    refine ⟨isGammaPeriodic_comp_quotMap P K u, fun μ => ⟨?_, ?_, partialDeriv_comp_quotMap P K u μ⟩⟩
    · exact isGammaPeriodic_partialDerivR4 P K _ (isGammaPeriodic_comp_quotMap P K u) μ
    · exact existsUnique_descent P K _
        (isGammaPeriodic_partialDerivR4 P K _ (isGammaPeriodic_comp_quotMap P K u) μ)
  · have := P.one_le_M
    linarith
  · intro u hu
    have h := lipConstQ_isLeast P K u hu
    exact ⟨⟨_, h⟩, h⟩
end YangMills.Construction.PeriodicSpace.QuotientGeometry
