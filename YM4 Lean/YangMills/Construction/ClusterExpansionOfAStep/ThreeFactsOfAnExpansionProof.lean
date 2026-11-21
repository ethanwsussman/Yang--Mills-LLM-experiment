import YangMills.Construction.ClusterExpansionOfAStep.ThreeFactsOfAnExpansion
import YangMills.Construction.ClusterExpansionOfAStep.TwoActionsAlongMovesForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.TorusLumps
open BlockAverages TorusFields TorusMirror LumpContours
section Action
theorem blockFit_nonneg {F : BlockFrame} {j : ℕ} (X : F.GaugeField j) (X' : F.GaugeField (j + 1))
    (c : F.Site (j + 1) × Fin 4) : 0 ≤ blockFit X X' c := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.blockFit_nonneg <;> assumption
theorem wilsonAction_nonneg {F : BlockFrame} (S : Finset F.Cell) (U : F.GaugeField 0) :
    0 ≤ BlockAverages.wilsonAction S U := by
  unfold BlockAverages.wilsonAction
  refine Finset.sum_nonneg fun p _ => ?_
  have h := sq_norm_unitQuaternion_sub_one (plaquetteHolonomy U p)
  nlinarith [sq_nonneg ‖((plaquetteHolonomy U p : UnitQuaternion) : ℍ[ℝ]) - 1‖]
theorem minimalAction_nonneg {F : BlockFrame} {a : ℝ} (ha : 0 ≤ a) (S : Finset F.Cell) :
    ∀ (j : ℕ) (X : F.GaugeField j), 0 ≤ minimalAction a S j X
  | 0, U => wilsonAction_nonneg S U
  | j + 1, V => by
    refine Real.iInf_nonneg fun W => ?_
    exact add_nonneg (minimalAction_nonneg ha S j W)
      (mul_nonneg ha (Finset.sum_nonneg fun c _ => blockFit_nonneg _ _ _))
theorem actionAtLevel_nonneg {n : ℕ} [NeZero n] {a : ℝ} (ha : 0 ≤ a) (L : ℕ) :
    ∀ (t : ℕ) (S : Finset (TorusSite n)) (W : TorusField n), 0 ≤ actionAtLevel a L t S W
  | 0, _, W => Finset.sum_nonneg fun _ _ => plaquetteEnergy_nonneg W _ _ _
  | _ + 1, _, _ => minimalAction_nonneg ha _ _ _
end Action
section Bounds
variable {ℓ : StepParameters} {t : ℕ} {x : ℝ} {D : TorusFunctional} {f : LocalDensity} {n : ℕ}
theorem StepParameters.weight_zero (ℓ : StepParameters) : ℓ.weight 0 = 1 := by
  simp [StepParameters.weight]
theorem curvature_trivialField (x : TorusSite n) (μ ν : Fin 4) :
    curvature (trivialField n) x μ ν = 0 := by
  simp [curvature, holonomy_trivialField]
theorem mixedDeriv_of_fin_zero (G : TorusField n → ℝ) (W : TorusField n) (c : Fin 0 → TorusBond n)
    (X : Fin 0 → imaginaryQuaternions) : mixedDeriv G W c X = G W := by
  unfold mixedDeriv
  rw [iteratedFDeriv_zero_apply, perturb_zero]
theorem abs_centered_le_of_isCold [NeZero n] (hfit : ℓ.Admissible) (hc : ColdExpansion ℓ t x D f)
    (hn : ℓ.n₀ ≤ n) (y : TorusSite n) (W : TorusField n) (hW : IsCold ℓ.threshold W) :
    |centered f n y W| ≤ ℓ.E := by
  have hn2 : 2 < n := by have := hfit.n₀_ge; omega
  have hflat : IsCold ℓ.threshold (trivialField n) := fun x μ ν _ => by
    rw [curvature_trivialField]
    exact hfit.σ_pos
  have hag : FieldsAgreeNear W (trivialField n) y y 0 := by
    intro b hb
    exfalso
    have h1 := hb.1 b.2
    have h2 := hb.2 b.2
    simp only [Nat.cast_zero, abs_nonpos_iff] at h1
    simp [h1] at h2
  have h := hc.local_density n n hn hn y y W (trivialField n) 0 (by omega) (by omega) hW hflat hag 0
    (fun l => l.elim0) (fun l => l.elim0) (by omega) (fun l => l.elim0) (fun l => l.elim0)
  rw [mixedDeriv_of_fin_zero, mixedDeriv_of_fin_zero, StepParameters.weight_zero, div_one] at h
  simpa [centered] using h
theorem supDist_le_half [NeZero n] (x y : TorusSite n) : _root_.YangMills.Construction.TorusFields.supDist x y ≤ n / 2 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.supDist_le_half_card <;> assumption
theorem isCold_of_isHullState_empty [NeZero n] (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) {r : ℕ}
    {W : TorusField n} (hY : IsHullState ℓ r W ∅) : IsCold ℓ.threshold W := by
  intro x μ ν hlt
  by_contra h
  have h1 := mem_torusHotSites_of_mem_plaquetteVertices hfit hLn hlt (not_lt.mp h)
    (base_mem_plaquetteVertices x μ ν)
  have h2 := hY.1 ((mem_thickening _ _ _).mpr ⟨x, h1, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩)
  simp at h2
variable {Λ : LabelSpace}
  {Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
  {Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ}
  {φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
theorem n₀_le_of_isBlockTorusSide (hfit : ℓ.Admissible) (hs : IsBlockTorusSide ℓ n) : ℓ.n₀ ≤ n := by
  have h1 := hs.2
  have h2 : 1 * ℓ.n₀ ≤ ℓ.side * ℓ.n₀ :=
    Nat.mul_le_mul_right _ (by have := hfit.L_ge; omega)
  omega
theorem abs_density_le_of_far_from_hull [NeZero n] (hfit : ℓ.Admissible) (hE : 1 ≤ ℓ.E)
    (hfl : 4 * ℓ.n₀ + 2 ^ 16 ≤ clusterRange x)
    (hc : ColdExpansion ℓ t x D f) (hh : HullExpansion ℓ t x D f Λ Dq Φ φ)
    (hs : IsBlockTorusSide ℓ n) (W : TorusField n)
    (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω) (y : TorusSite n)
    (hY : IsHullState ℓ (clusterRange x) W Y)
    (hnz : ∀ X ∈ chainComponents (clusterRange x) Y, Φ n W Y ω X ≠ 0)
    (hfar : ∀ z ∈ Y, (clusterRange x : ℝ) / 4 ≤ _root_.YangMills.Construction.TorusFields.supDist y z) : |φ n y W Y ω| ≤ 2 * ℓ.E := by
  by_cases hYe : Y = ∅
  · subst hYe
    rw [hh.empty n hs W ω y hY]
    have := abs_centered_le_of_isCold hfit hc (n₀_le_of_isBlockTorusSide hfit hs) y W
      (isCold_of_isHullState_empty hfit hs.1 hY)
    linarith
  obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hYe
  set r := clusterRange x with hr
  set m := r / 4 - 2 with hm
  have hn₀ := hfit.n₀_ge
  have hm1 : 4 * m + 8 ≤ r := by omega
  have hm2 : r ≤ 4 * m + 11 := by omega
  have hm3 : 2 ≤ m := by omega
  have hmr : (m : ℝ) + 2 ≤ (r : ℝ) / 4 := by
    have : ((4 * m + 8 : ℕ) : ℝ) ≤ r := by exact_mod_cast hm1
    push_cast at this
    linarith
  have hside : 2 * m + 2 < n := by
    have h1 := hfar z hz
    have h2 := _root_.YangMills.Construction.TorusLumps.supDist_le_half y z
    have h3 : (r : ℝ) ≤ ((4 * _root_.YangMills.Construction.TorusFields.supDist y z : ℕ) : ℝ) := by
      push_cast
      linarith
    have h4 : r ≤ 4 * _root_.YangMills.Construction.TorusFields.supDist y z := by exact_mod_cast h3
    omega
  have : NeZero (4 * m) := ⟨by omega⟩
  have hcold : IsCold ℓ.threshold (mirrorField m y W) := by
    refine isCold_mirrorField (by omega) y W hfit.σ_pos fun a μ ν hlt hcorn => ?_
    by_contra hcon
    have h1 := mem_torusHotSites_of_mem_plaquetteVertices hfit hs.1 hlt (not_lt.mp hcon)
      (base_mem_plaquetteVertices (y + siteOfInt a) μ ν)
    have h2 := hY.1 ((mem_thickening _ _ _).mpr ⟨_, h1, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩)
    have h3 := hfar _ h2
    have hbox := hcorn 0 (by simp [plaquetteOffsets])
    rw [add_zero] at hbox
    have h4 : _root_.YangMills.Construction.TorusFields.supDist y (y + siteOfInt a) ≤ m := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le y a m fun i => by
      have := hbox i
      rw [abs_le] at this
      omega
    have h5 : (_root_.YangMills.Construction.TorusFields.supDist y (y + siteOfInt a) : ℝ) ≤ m := by exact_mod_cast h4
    linarith
  have hnotY : ∀ h, OffsetInBox m h → y + siteOfInt h ∉ Y := by
    intro h hh' hmem
    have h3 := hfar _ hmem
    have h4 : _root_.YangMills.Construction.TorusFields.supDist y (y + siteOfInt h) ≤ m := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le y h m fun i => by
      have := hh' i
      rw [abs_le] at this
      omega
    have h5 : (_root_.YangMills.Construction.TorusFields.supDist y (y + siteOfInt h) : ℝ) ≤ m := by exact_mod_cast h4
    linarith
  let ω' : (∅ : Finset (TorusSite (4 * m))) → Λ.Ω := fun u => absurd u.2 (Finset.notMem_empty _)
  have hagree : StatesAgreeNear ℓ W (mirrorField m y W) Y ∅ ω ω' y 0 m := by
    refine ⟨hside, by omega, fun b hb => ?_, fun h hh' => ?_, fun h _ _ hz' _ => ?_, ?_⟩
    · simp only [bondFrom, zero_add]
      exact (mirrorField_siteOfInt hm3 y W b hb).symm
    · simp [hnotY h hh']
    · exact absurd hz' (Finset.notMem_empty _)
    · rintro ⟨h, hh', hmem⟩
      exact absurd hmem (hnotY h hh')
  have hmfl : (r : ℝ) / 64 ≤ m := by
    have : (r : ℝ) ≤ ((4 * m + 11 : ℕ) : ℝ) := by exact_mod_cast hm2
    push_cast at this
    have hm4 : (2 : ℝ) ≤ m := by exact_mod_cast hm3
    linarith
  have hf := hh.forget_cold n (4 * m) hs (by omega) W (mirrorField m y W) Y ω ω' y 0 m hY hcold hnz
    hmfl hagree
  have hone := abs_centered_le_of_isCold hfit hc (n := 4 * m) (by omega) 0 (mirrorField m y W) hcold
  have hexp : Real.exp (-ℓ.decayRate * m) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have h1 : 0 ≤ ℓ.decayRate := by
      unfold StepParameters.decayRate
      exact div_nonneg hfit.rt_pos.le (by norm_num)
    have h2 : (0 : ℝ) ≤ m := by positivity
    nlinarith
  have := abs_sub_abs_le_abs_sub (φ n y W Y ω) (centered f (4 * m) 0 (mirrorField m y W))
  linarith
theorem lintegral_glueLabel {Ω : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [SigmaFinite μ] [NeZero n] {Y Y' : Finset (TorusSite n)} (h : Y' = Y) (G : (Y → Ω) → ENNReal)
    (ω₀ : Y → Ω) :
    ∫⁻ ν, G (glueLabel Y Y' ω₀ ν) ∂(Measure.pi fun _ : Y' => μ) =
      ∫⁻ ω, G ω ∂(Measure.pi fun _ : Y => μ) := by
  subst h
  have : ∀ ν : Y' → Ω, glueLabel Y' Y' ω₀ ν = ν := by
    intro ν
    funext z
    simp [glueLabel, z.2]
  simp only [this]
theorem functional_le_trivial_mul [NeZero n] (hfit : ℓ.Admissible) (hE : 1 ≤ ℓ.E) (hx : 0 < x)
    (hfl : 4 * ℓ.n₀ + 2 ^ 16 ≤ clusterRange x) (hc : ColdExpansion ℓ t x D f)
    (hh : HullExpansion ℓ t x D f Λ Dq Φ φ) (hs : IsBlockTorusSide ℓ n) (W : TorusField n) :
    D n W ≤ D n (trivialField n) * 2 ^ Fintype.card (TorusSite n) *
      Real.exp (2 * ℓ.E * Fintype.card (TorusSite n)) := by
  classical
  have hflat : IsCold ℓ.threshold (trivialField n) := fun x μ ν _ => by
    rw [curvature_trivialField]
    exact hfit.σ_pos
  have hD1 : 0 < D n (trivialField n) :=
    hc.positive n (n₀_le_of_isBlockTorusSide hfit hs) _ hflat
  set c : ℝ := D n (trivialField n) * Real.exp (2 * ℓ.E * Fintype.card (TorusSite n)) with hcdef
  have hc0 : 0 ≤ c := by positivity
  have key : ∀ Y ∈ Finset.univ.filter (IsHullState ℓ (clusterRange x) W),
      ∫⁻ ω, ENNReal.ofReal (Dq n W Y ω) ∂(Measure.pi fun _ : Y => Λ.μ) ≤ ENNReal.ofReal c := by
    intro Y hYm
    have hY : IsHullState ℓ (clusterRange x) W Y := (Finset.mem_filter.mp hYm).2
    by_cases hne : Nonempty (Y → Λ.Ω)
    · obtain ⟨ω₀⟩ := hne
      set P := chainComponents (clusterRange x) Y with hP
      have hU : P.biUnion id = Y := biUnion_chainComponents
      have hp := hh.price n hs W Y ω₀ P hY subset_rfl
        (fun X hX => absurd (Finset.mem_sdiff.mp hX).1 (Finset.mem_sdiff.mp hX).2)
      let G : (Y → Λ.Ω) → ENNReal := fun ω =>
        if ∃ X ∈ P, Φ n W Y ω X = 0 then 0 else
          ENNReal.ofReal ((∏ X ∈ P, Φ n W Y ω X) *
            Real.exp (∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
                ∃ z ∈ P.biUnion id, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) < (clusterRange x : ℝ) / 4),
              φ n y W Y ω))
      have hG : ∫⁻ ω, G ω ∂(Measure.pi fun _ : Y => Λ.μ) ≤ 1 := by
        rw [← lintegral_glueLabel Λ.μ hU G ω₀]
        refine hp.trans ?_
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        rw [Real.exp_le_one_iff]
        have h1 := hfit.κ_pos
        have h2 := hfit.κ₁_pos
        have h3 : 0 ≤ x * ℓ.κ * ℓ.threshold ^ 2 *
            (((torusHotLumps ℓ W).filter (· ⊆ P.biUnion id)).card : ℝ) := by
          positivity
        have h4 : 0 ≤ ℓ.κ₁ * x * ℓ.threshold ^ 2 *
            (excessLength ℓ (clusterRange x) (P.biUnion id) W : ℝ) := by
          positivity
        linarith
      have hpt : ∀ ω, ENNReal.ofReal (Dq n W Y ω) ≤ ENNReal.ofReal c * G ω := by
        intro ω
        by_cases hz : ∃ X ∈ P, Φ n W Y ω X = 0
        · obtain ⟨X, hX, h0⟩ := hz
          rw [hh.form n hs W Y ω hY, Finset.prod_eq_zero hX h0, mul_zero]
          simp
        · have hGω : G ω = ENNReal.ofReal ((∏ X ∈ P, Φ n W Y ω X) *
              Real.exp (∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
                  ∃ z ∈ P.biUnion id, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) < (clusterRange x : ℝ) / 4),
                φ n y W Y ω)) := by
            simp only [G]
            rw [if_neg hz]
          push Not at hz
          rw [hGω, ← ENNReal.ofReal_mul hc0]
          apply ENNReal.ofReal_le_ofReal
          rw [hh.form n hs W Y ω hY]
          set near := Finset.univ.filter (fun y : TorusSite n =>
                  ∃ z ∈ P.biUnion id, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) < (clusterRange x : ℝ) / 4) with hnear
          have hsplit : ∑ y, φ n y W Y ω = ∑ y ∈ near, φ n y W Y ω +
              ∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
                ¬ ∃ z ∈ P.biUnion id, (supDist y z : ℝ) < (clusterRange x : ℝ) / 4),
                φ n y W Y ω :=
            (Finset.sum_filter_add_sum_filter_not _ _ _).symm
          have hfarsum : ∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
                ¬ ∃ z ∈ P.biUnion id, (supDist y z : ℝ) < (clusterRange x : ℝ) / 4),
                φ n y W Y ω ≤ 2 * ℓ.E * Fintype.card (TorusSite n) := by
            have h1 : ∀ y ∈ Finset.univ.filter (fun y : TorusSite n =>
                ¬ ∃ z ∈ P.biUnion id, (supDist y z : ℝ) < (clusterRange x : ℝ) / 4),
                φ n y W Y ω ≤ 2 * ℓ.E := by
              intro y hy
              have hy2 := (Finset.mem_filter.mp hy).2
              push Not at hy2
              rw [hU] at hy2
              exact (le_abs_self _).trans
                (abs_density_le_of_far_from_hull hfit hE hfl hc hh hs W Y ω y hY hz hy2)
            have h2 := Finset.sum_le_card_nsmul _ _ _ h1
            rw [nsmul_eq_mul] at h2
            have h3 : ((Finset.univ.filter (fun y : TorusSite n =>
                ¬ ∃ z ∈ P.biUnion id, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) < (clusterRange x : ℝ) / 4)).card : ℝ) ≤
                Fintype.card (TorusSite n) := by
              exact_mod_cast Finset.card_le_univ _
            have h4 : 0 ≤ 2 * ℓ.E := by linarith
            nlinarith
          have hA : 0 ≤ x * actionAtLevel ℓ.coupling ℓ.side t
              (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W :=
            mul_nonneg hx.le (actionAtLevel_nonneg (by linarith [hfit.a_ge]) _ _ _ _)
          have hprod : 0 ≤ ∏ X ∈ P, Φ n W Y ω X :=
            Finset.prod_nonneg fun X _ => hh.factor_nonneg n hs W Y ω X
          have hexp : Real.exp (-x * actionAtLevel ℓ.coupling ℓ.side t
                (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W +
              ∑ y, φ n y W Y ω) ≤
              Real.exp (2 * ℓ.E * Fintype.card (TorusSite n)) *
                Real.exp (∑ y ∈ near, φ n y W Y ω) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            rw [hsplit]
            linarith
          calc D n (trivialField n) * _ * _ ≤ D n (trivialField n) *
                (Real.exp (2 * ℓ.E * Fintype.card (TorusSite n)) *
                Real.exp (∑ y ∈ near, φ n y W Y ω)) * ∏ X ∈ P, Φ n W Y ω X := by gcongr
            _ = c * ((∏ X ∈ P, Φ n W Y ω X) * Real.exp (∑ y ∈ near, φ n y W Y ω)) := by
              rw [hcdef]
              ring
      calc ∫⁻ ω, ENNReal.ofReal (Dq n W Y ω) ∂(Measure.pi fun _ : Y => Λ.μ)
          ≤ ∫⁻ ω, ENNReal.ofReal c * G ω ∂(Measure.pi fun _ : Y => Λ.μ) := lintegral_mono hpt
        _ = ENNReal.ofReal c * ∫⁻ ω, G ω ∂(Measure.pi fun _ : Y => Λ.μ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal c * 1 := by gcongr
        _ = ENNReal.ofReal c := mul_one _
    · have : IsEmpty (Y → Λ.Ω) := not_nonempty_iff.mp hne
      simp
  have hsum := hh.sum n hs W
  have hle : ENNReal.ofReal (D n W) ≤ ENNReal.ofReal (2 ^ Fintype.card (TorusSite n) * c) := by
    rw [← hsum]
    refine (Finset.sum_le_card_nsmul _ _ _ key).trans ?_
    rw [nsmul_eq_mul, show ENNReal.ofReal (2 ^ Fintype.card (TorusSite n) * c) =
      ENNReal.ofReal (2 ^ Fintype.card (TorusSite n)) * ENNReal.ofReal c from
      ENNReal.ofReal_mul (by positivity)]
    have hcard : (Finset.univ.filter (IsHullState ℓ (clusterRange x) W)).card ≤
        2 ^ Fintype.card (TorusSite n) := by
      refine (Finset.card_le_univ _).trans ?_
      rw [Fintype.card_finset]
    have : ((Finset.univ.filter (IsHullState ℓ (clusterRange x) W)).card : ENNReal) ≤
        ((2 ^ Fintype.card (TorusSite n) : ℕ) : ENNReal) := by exact_mod_cast hcard
    have h2e : ((2 ^ Fintype.card (TorusSite n) : ℕ) : ENNReal) =
        ENNReal.ofReal ((2 : ℝ) ^ Fintype.card (TorusSite n)) := by
      rw [show ((2 : ℝ) ^ Fintype.card (TorusSite n)) = ((2 ^ Fintype.card (TorusSite n) : ℕ) : ℝ) by
        push_cast; rfl, ENNReal.ofReal_natCast]
    rw [h2e] at this
    exact mul_le_mul' this (le_refl _)
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  rw [hcdef] at h2
  nlinarith
end Bounds
theorem expansionBasicBounds : ExpansionBasicBounds := by
  intro ℓ t x D f Λ Dq Φ φ hfit hE hx hfl hc hh
  exact ⟨fun n _ hn y W hW => abs_centered_le_of_isCold hfit hc hn y W hW,
    fun n _ hs W Y ω y hY hnz hfar =>
      abs_density_le_of_far_from_hull hfit hE hfl hc hh hs W Y ω y hY hnz hfar,
    fun n _ hs W => functional_le_trivial_mul hfit hE hx hfl hc hh hs W⟩
end YangMills.Construction.TorusLumps
end
