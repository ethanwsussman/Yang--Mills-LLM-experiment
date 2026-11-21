import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.GasDensitiesForget
import YangMills.Construction.ClusterExpansionOfAStep.OrderOfFiniteSets
import YangMills.Construction.ClusterExpansionOfAStep.OrderOfTheBlocks
import YangMills.Construction.ClusterExpansionOfAStep.RatiosOfXi
import YangMills.Construction.ClusterExpansionOfAStep.SetsEqualInBoxes
import YangMills.Construction.ClusterExpansionOfAStep.SumOfTheGasDensities
import YangMills.Construction.ClusterExpansionOfAStep.TwoSystemsOfTheGas
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTwoMoves
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction
open Dobrushin StepGas StepSettings RenormalizationStepParameters StepFloors TorusFields MarkedIntegrals BlockOrder RandomOrder
namespace ClusterExpansionOfAStep
variable {R : StepSetup}
theorem readsComponentsAt_indicator_compl_noSpinMeets {n : ℕ} [NeZero n] (G : GasGround R n) (Y : TorusSite n)
    (hE : MeasurableSet (G.NoSpinMeets Y)) :
    G.ReadsComponentsAt Y ((G.NoSpinMeets Y)ᶜ.indicator 1) where
  measurable := measurable_one.indicator hE.compl
  abs_le_one σ := by
    by_cases hσ : σ ∈ (G.NoSpinMeets Y)ᶜ
    · simp [Set.indicator_of_mem hσ]
    · simp [Set.indicator_of_notMem hσ]
  eq_of_agree σ σ' h := by
    have : σ ∈ (G.NoSpinMeets Y)ᶜ ↔ σ' ∈ (G.NoSpinMeets Y)ᶜ := by
      simp only [GasGround.NoSpinMeets, Set.mem_compl_iff, Set.mem_setOf_eq, not_iff_not]
      constructor
      · intro h1 i hi
        rw [← h i hi]
        exact h1 i hi
      · intro h1 i hi
        rw [h i hi]
        exact h1 i hi
    by_cases hσ : σ ∈ (G.NoSpinMeets Y)ᶜ
    · rw [Set.indicator_of_mem hσ, Set.indicator_of_mem (this.mp hσ)]
      rfl
    · rw [Set.indicator_of_notMem hσ, Set.indicator_of_notMem (fun h' => hσ (this.mpr h'))]
  eq_zero_of_none σ hσ := Set.indicator_of_notMem (by simpa using hσ) _
theorem indicator_compl_noSpinMeets_eq_of_componentsMatch {n n' : ℕ} [NeZero n] [NeZero n']
    (G : GasGround R n) (G' : GasGround R n') (Y : TorusSite n)
    (Y' : TorusSite n') (N : ℕ) (σ : G.Config) (σ' : G'.Config) (h : ComponentsMatch G G' Y Y' N σ σ') :
    ((G.NoSpinMeets Y)ᶜ.indicator (1 : G.Config → ℝ)) σ =
      ((G'.NoSpinMeets Y')ᶜ.indicator (1 : G'.Config → ℝ)) σ' := by
  have key : σ ∈ (G.NoSpinMeets Y)ᶜ ↔ σ' ∈ (G'.NoSpinMeets Y')ᶜ := by
    simp only [GasGround.NoSpinMeets, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall]
    constructor
    · rintro ⟨i, hi, hσ⟩
      obtain ⟨i', hi', -, s, s', -, hs', -⟩ := h.1 i hi hσ
      exact ⟨i', hi', by rw [hs']; simp⟩
    · rintro ⟨i', hi', hσ⟩
      obtain ⟨i, hi, -, s, s', hs, -, -⟩ := h.2 i' hi' hσ
      exact ⟨i, hi, by rw [hs]; simp⟩
  by_cases hσ : σ ∈ (G.NoSpinMeets Y)ᶜ
  · rw [Set.indicator_of_mem hσ, Set.indicator_of_mem (key.mp hσ)]
    rfl
  · rw [Set.indicator_of_notMem hσ, Set.indicator_of_notMem (fun h' => hσ (key.mpr h'))]
theorem abs_log_sub_log_le_two_mul {a b : ℝ} (ha : 1 / 2 ≤ a) (hb : 1 / 2 ≤ b) :
    |Real.log a - Real.log b| ≤ 2 * |a - b| := by apply _root_.YangMills.Construction.SecondOrderMoves.abs_log_sub_log_le <;> assumption
theorem siteOfInt_injective_of_offsetInBox {n : ℕ} [NeZero n] (Y : TorusSite n) (N : ℕ) (hN : 2 * N + 2 < n)
    (h h' : Fin 4 → ℤ) (hh : OffsetInBox N h) (hh' : OffsetInBox N h')
    (e : Y + siteOfInt h = Y + siteOfInt h') : h = h' := by exact _root_.YangMills.Construction.CongruentBoxes.eq_of_add_siteOfInt_eq (n := n) (y := Y) hN hh hh' e
theorem gasDensityForgets (hTwo : ExpectationsCloseOfGroundsAgreeNear) (hS : LogPartitionEqSumDensities)
    (hC : GasColumnsSmall) (hX : PartitionRatioBounds) (hO : RandomOrderFacts)
    (hF : IntegrableOfLowerRankSet) (hFl : EventuallyFloorConditions) : GasDensityForgets := by
  obtain ⟨r₁, hr₁, h₁⟩ := hTwo
  obtain ⟨r₂, hr₂, h₂⟩ := hS
  obtain ⟨r₃, hr₃, h₃⟩ := hC
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (r₃ c)), fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (hr₃ c)),
    fun T hT hle => ?_⟩
  obtain ⟨y₁, hy₁⟩ := h₁ T hT (hle.trans (min_le_left _ _))
  obtain ⟨y₂, hy₂⟩ := h₂ T hT (hle.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨y₃, hy₃⟩ := h₃ T hT (hle.trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨y₄, hy₄⟩ := hFl T hT 1 1 one_pos one_pos
  have hκ₁ : 0 < T.κ₁ := lt_min (div_pos hT.κ_pos (by norm_num))
    (div_pos hT.cE_pos (by have := hT.σ_pos; positivity))
  have hch : 0 < T.gasRate := by
    have h1 : 0 < T.κ * T.threshold ^ 2 := mul_pos hT.κ_pos (pow_pos hT.σ_pos 2)
    have h2 : 0 < T.κ₁ * T.threshold ^ 2 := mul_pos hκ₁ (pow_pos hT.σ_pos 2)
    exact mul_pos (by norm_num) (lt_min hT.cE_pos (lt_min h1 h2))
  refine ⟨max (max y₁ y₂) (max (max y₃ y₄) (2 / T.gasRate)),
    fun y hy R hRT hx' n n' _ _ G G' Y Y' N hG hG' hN hA => ?_⟩
  have hyy₁ : y₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hyy₂ : y₂ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hyy₃ : y₃ ≤ y := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hy
  have hyy₄ : y₄ ≤ y := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hy
  have hyy₅ : 2 / T.gasRate ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
  have hx2 : 2 ≤ T.gasRate * R.coupling := by
    have h1 : 2 / T.gasRate ≤ R.coupling := hyy₅.trans hRT.le_coupling
    rw [div_le_iff₀ hch] at h1
    linarith
  have hrt := hT.rt_pos
  by_cases hNm : 16 * R.frameReach ≤ N
  swap
  · obtain ⟨-, b₁⟩ := hy₂ y hyy₂ R hRT hx' n G hG
    obtain ⟨-, b₂⟩ := hy₂ y hyy₂ R hRT hx' n' G' hG'
    have hfl := (hy₄ R.coupling (hyy₄.trans hRT.le_coupling)).gas_powers
    have hm : (N : ℝ) ≤ 16 * (R.frameReach : ℝ) := by exact_mod_cast (not_le.mp hNm).le
    have hexp : Real.exp (-(6 * T.gasRate * R.coupling)) ≤
        Real.exp (-(T.gasRate * R.coupling) - T.rt * N / 2 ^ 8) := by
      refine Real.exp_le_exp.mpr ?_
      have h5 : T.rt * N ≤ 16 * T.rt * (R.frameReach : ℝ) := by nlinarith
      have h6 : 16 * T.rt * (R.frameReach : ℝ) ≤ T.gasRate * R.coupling := by
        have := hfl.1
        have h7 := hfl.2.1
        have : 16 * T.rt * (R.frameReach : ℝ) + 16 * T.rt ≤ R.coupling ^ (1 / 90 : ℝ) := hfl.1
        nlinarith
      nlinarith
    rw [abs_le]
    constructor
    · have := (b₂ Y').1
      have := (b₁ Y).1
      have h8 := (b₂ Y').2
      linarith
    · have := (b₁ Y).2
      have := (b₂ Y').1
      have h8 := (b₁ Y).2
      linarith
  set δ := Real.exp (-(2 * T.gasRate * R.coupling) - T.rt * N / 2 ^ 8) with hδ
  have hδ0 : 0 < δ := Real.exp_pos _
  have hlog : ∀ (m : ℕ) [NeZero m] (H : GasGround R m) (Z : TorusSite m) (A : Finset (TorusSite m)),
      H.IsAdmissibleGround →
      1 / 2 ≤ H.xi (insert Z A) / H.xi A ∧
      Real.log (H.xi A) - Real.log (H.xi (insert Z A)) = -Real.log (H.xi (insert Z A) / H.xi A) ∧
      H.expectation A ((H.NoSpinMeets Z)ᶜ.indicator 1) = 1 - H.xi (insert Z A) / H.xi A := by
    intro m _ H Z A hH
    have hall := hy₃ y hyy₃ R hRT hx' m H hH
    obtain ⟨xm, xpos, -, xlaw, xrat⟩ := hX R m H T.gasRate hall
    obtain ⟨h₀, hs⟩ := hall (fun j => j.1.Touches A)
    haveI : IsProbabilityMeasure (H.gibbsLaw A) := hs.isProbabilityMeasure
    refine ⟨?_, ?_, ?_⟩
    · have h1 := (xrat A Z).1
      have h2 : Real.exp (-(7 * T.gasRate * R.coupling)) ≤ 1 / 2 := by
        have h0 : Real.exp (-(7 * T.gasRate * R.coupling)) ≤ Real.exp (-1) :=
          Real.exp_le_exp.mpr (by nlinarith)
        have h3 : Real.exp (-1) ≤ 1 / 2 := by
          rw [Real.exp_neg, inv_eq_one_div]
          exact one_div_le_one_div_of_le (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
        linarith
      linarith
    · rw [Real.log_div (xpos _).ne' (xpos _).ne']
      ring
    · unfold GasGround.expectation
      rw [integral_indicator_one (xm Z).compl, measureReal_compl (xm Z), probReal_univ, xlaw]
  have pt : ∀ (m m' : ℕ) [NeZero m] [NeZero m'] (H : GasGround R m) (H' : GasGround R m') (Z : TorusSite m)
      (Z' : TorusSite m'), H.IsAdmissibleGround → H'.IsAdmissibleGround → GroundsAgreeNear H H' Z Z' N →
      ∀ (A : Finset (TorusSite m)) (A' : Finset (TorusSite m')),
      BlockSetsAgreeNear A A' Z Z' N →
      |(Real.log (H.xi A) - Real.log (H.xi (insert Z A))) -
        (Real.log (H'.xi A') - Real.log (H'.xi (insert Z' A')))| ≤ 2 * δ := by
    intro m m' _ _ H H' Z Z' hH hH' hagree A A' hAA
    obtain ⟨hρ, hl, hm⟩ := hlog m H Z A hH
    obtain ⟨hρ', hl', hm'⟩ := hlog m' H' Z' A' hH'
    obtain ⟨xm, -⟩ := hX R m H T.gasRate (hy₃ y hyy₃ R hRT hx' m H hH)
    obtain ⟨xm', -⟩ := hX R m' H' T.gasRate (hy₃ y hyy₃ R hRT hx' m' H' hH')
    have h2 := hy₁ y hyy₁ R hRT hx' m m' H H' Z Z' N A A' _ _ hH hH' hNm hagree hAA
      (readsComponentsAt_indicator_compl_noSpinMeets H Z (xm Z))
      (readsComponentsAt_indicator_compl_noSpinMeets H' Z' (xm' Z'))
      (fun σ σ' hσ => indicator_compl_noSpinMeets_eq_of_componentsMatch H H' Z Z' N σ σ' hσ)
    rw [hm, hm'] at h2
    rw [hl, hl']
    have h3 := abs_log_sub_log_le_two_mul hρ' hρ
    have h4 : |H'.xi (insert Z' A') / H'.xi A' - H.xi (insert Z A) / H.xi A| ≤ δ := by
      have : H'.xi (insert Z' A') / H'.xi A' - H.xi (insert Z A) / H.xi A =
          (1 - H.xi (insert Z A) / H.xi A) - (1 - H'.xi (insert Z' A') / H'.xi A') := by ring
      rw [this]
      exact h2
    have h5 : -Real.log (H.xi (insert Z A) / H.xi A) - -Real.log (H'.xi (insert Z' A') / H'.xi A') =
        Real.log (H'.xi (insert Z' A') / H'.xi A') - Real.log (H.xi (insert Z A) / H.xi A) := by ring
    rw [h5]
    linarith
  classical
  have hrefl : ∀ (m : ℕ) [NeZero m] (H : GasGround R m) (Z : TorusSite m), 2 * N + 2 < m →
      GroundsAgreeNear H H Z Z N :=
    fun m _ H Z hs => ⟨hs, hs, fun _ _ => rfl, fun _ _ => Iff.rfl, fun _ _ => rfl⟩
  let K : Type := ↥(Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(N : ℤ)) (N : ℤ))
  have hK : ∀ k : K, OffsetInBox N k.1 := by
    intro k i
    have := Fintype.mem_piFinset.mp k.2 i
    rw [Finset.mem_Icc] at this
    exact abs_le.mpr this
  have hK' : ∀ h, OffsetInBox N h → h ∈ (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
    intro h hh
    refine Fintype.mem_piFinset.mpr fun i => ?_
    rw [Finset.mem_Icc]
    exact abs_le.mp (hh i)
  have h0 : OffsetInBox N (0 : Fin 4 → ℤ) := fun i => by simp
  let k₀ : K := ⟨0, hK' 0 h0⟩
  obtain ⟨hp₁, -, hi₁, hmap₁⟩ := hO n
  obtain ⟨hp₂, -, hi₂, hmap₂⟩ := hO n'
  have hU : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  let π : Measure (K → ℝ) := Measure.pi fun _ : K => volume.restrict (Set.Icc (0 : ℝ) 1)
  haveI : IsProbabilityMeasure π := by
    simp only [π]
    infer_instance
  have side : ∀ (m : ℕ) [NeZero m] (H : GasGround R m) (Z : TorusSite m), H.IsAdmissibleGround → 2 * N + 2 < m →
      ∀ (F : Finset (TorusSite m) → ℝ),
      (∀ (A A' : Finset (TorusSite m)), BlockSetsAgreeNear A A' Z Z N → |F A - F A'| ≤ 2 * δ) →
      IsProbabilityMeasure (randomOrderLaw m) →
      (∀ (f : Finset (TorusSite m) → ℝ) (Y : TorusSite m),
        Integrable (fun u => f (precedingBlocks u Y)) (randomOrderLaw m)) →
      (∀ (K : Type) [Fintype K] (κ : K → TorusSite m), Function.Injective κ →
        Measure.map (fun u : TorusSite m → ℝ => u ∘ κ) (randomOrderLaw m) =
          Measure.pi fun _ : K => volume.restrict (Set.Icc (0 : ℝ) 1)) →
      |∫ u, F (precedingBlocks u Z) ∂randomOrderLaw m -
        ∫ v, F ((Finset.univ.filter fun k : K => v k < v k₀).image fun k => Z + siteOfInt k.1) ∂π| ≤ 2 * δ := by
    intro m _ H Z hH hs F hFF hp hi hmap
    haveI := hp
    let κ : K → TorusSite m := fun k => Z + siteOfInt k.1
    have hκ : Function.Injective κ := by
      intro a b hab
      exact Subtype.ext (siteOfInt_injective_of_offsetInBox Z N hs _ _ (hK a) (hK b) hab)
    have hm : Measurable fun u : TorusSite m → ℝ => u ∘ κ :=
      measurable_pi_iff.mpr fun k => measurable_pi_apply (κ k)
    have hψ : Integrable (fun v : K → ℝ => F ((Finset.univ.filter fun k : K => v k < v k₀).image κ)) π :=
      hF K k₀ fun B => F (B.image κ)
    have hψ' : Integrable (fun v : K → ℝ => F ((Finset.univ.filter fun k : K => v k < v k₀).image κ))
        (Measure.map (fun u : TorusSite m → ℝ => u ∘ κ) (randomOrderLaw m)) := by
      rw [hmap K κ hκ]
      exact hψ
    have e1 : ∫ v, F ((Finset.univ.filter fun k : K => v k < v k₀).image κ) ∂π =
        ∫ u, F ((Finset.univ.filter fun k : K => (u ∘ κ) k < (u ∘ κ) k₀).image κ) ∂randomOrderLaw m := by
      simp only [π]
      rw [← hmap K κ hκ, integral_map hm.aemeasurable hψ'.aestronglyMeasurable]
    have hψ'' : Integrable (fun u : TorusSite m → ℝ =>
        F ((Finset.univ.filter fun k : K => (u ∘ κ) k < (u ∘ κ) k₀).image κ)) (randomOrderLaw m) :=
      hψ'.comp_aemeasurable hm.aemeasurable
    change |∫ u, F (precedingBlocks u Z) ∂randomOrderLaw m -
        ∫ v, F ((Finset.univ.filter fun k : K => v k < v k₀).image κ) ∂π| ≤ 2 * δ
    rw [e1, ← integral_sub (hi F Z) hψ'']
    have := norm_integral_le_of_norm_le_const (μ := randomOrderLaw m) (C := 2 * δ)
      (f := fun u => F (precedingBlocks u Z) -
        F ((Finset.univ.filter fun k : K => (u ∘ κ) k < (u ∘ κ) k₀).image κ))
      (Filter.Eventually.of_forall fun u => ?_)
    · rw [Real.norm_eq_abs] at this
      simpa using this
    · rw [Real.norm_eq_abs]
      refine hFF _ _ fun h hh => ?_
      have hz : κ k₀ = Z := by
        have h00 : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite m) = 0 := by
          funext i
          simp [siteOfInt]
        change Z + siteOfInt (0 : Fin 4 → ℤ) = Z
        rw [h00, add_zero]
      simp only [precedingBlocks, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Function.comp]
      rw [hz]
      constructor
      · intro hlt
        exact ⟨⟨h, hK' h hh⟩, hlt, rfl⟩
      · rintro ⟨k, hk, hke⟩
        rw [← hke]
        exact hk
  have s₁ := side n G Y hG hA.lt_extent
    (fun A => Real.log (G.xi A) - Real.log (G.xi (insert Y A)))
    (fun A A' hh => pt n n G G Y Y hG hG (hrefl n G Y hA.lt_extent) A A' hh) hp₁ hi₁ hmap₁
  have s₂ := side n' G' Y' hG' hA.lt_extent'
    (fun A => Real.log (G'.xi A) - Real.log (G'.xi (insert Y' A)))
    (fun A A' hh => pt n' n' G' G' Y' Y' hG' hG' (hrefl n' G' Y' hA.lt_extent') A A' hh) hp₂ hi₂ hmap₂
  have s₃ : |∫ v, (Real.log (G.xi ((Finset.univ.filter fun k : K => v k < v k₀).image fun k => Y + siteOfInt k.1)) -
        Real.log (G.xi (insert Y ((Finset.univ.filter fun k : K => v k < v k₀).image
          fun k => Y + siteOfInt k.1)))) ∂π -
      ∫ v, (Real.log (G'.xi ((Finset.univ.filter fun k : K => v k < v k₀).image fun k => Y' + siteOfInt k.1)) -
        Real.log (G'.xi (insert Y' ((Finset.univ.filter fun k : K => v k < v k₀).image
          fun k => Y' + siteOfInt k.1)))) ∂π| ≤
      2 * δ := by
    have i₁ := hF K k₀ fun B => Real.log (G.xi (B.image fun k => Y + siteOfInt k.1)) -
      Real.log (G.xi (insert Y (B.image fun k => Y + siteOfInt k.1)))
    have i₂ := hF K k₀ fun B => Real.log (G'.xi (B.image fun k => Y' + siteOfInt k.1)) -
      Real.log (G'.xi (insert Y' (B.image fun k => Y' + siteOfInt k.1)))
    rw [← integral_sub i₁ i₂]
    have := norm_integral_le_of_norm_le_const (μ := π) (C := 2 * δ)
      (f := fun v => (Real.log (G.xi ((Finset.univ.filter fun k : K => v k < v k₀).image
          fun k => Y + siteOfInt k.1)) -
        Real.log (G.xi (insert Y ((Finset.univ.filter fun k : K => v k < v k₀).image
          fun k => Y + siteOfInt k.1)))) -
        (Real.log (G'.xi ((Finset.univ.filter fun k : K => v k < v k₀).image fun k => Y' + siteOfInt k.1)) -
        Real.log (G'.xi (insert Y' ((Finset.univ.filter fun k : K => v k < v k₀).image
          fun k => Y' + siteOfInt k.1)))))
      (Filter.Eventually.of_forall fun v => ?_)
    · rw [Real.norm_eq_abs] at this
      simpa using this
    · rw [Real.norm_eq_abs]
      refine pt n n' G G' Y Y' hG hG' hA _ _ fun h hh => ?_
      have hinj : ∀ (m : ℕ) [NeZero m] (Z : TorusSite m), 2 * N + 2 < m → ∀ (v : K → ℝ),
          (Z + siteOfInt h ∈ (Finset.univ.filter fun k : K => v k < v k₀).image fun k => Z + siteOfInt k.1) ↔
            v ⟨h, hK' h hh⟩ < v k₀ := by
        intro m _ Z hs v
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨k, hk, hke⟩
          have : k = ⟨h, hK' h hh⟩ := Subtype.ext (siteOfInt_injective_of_offsetInBox Z N hs _ _ (hK k) hh hke)
          rwa [this] at hk
        · intro hlt
          exact ⟨_, hlt, rfl⟩
      rw [hinj n Y hA.lt_extent, hinj n' Y' hA.lt_extent']
  unfold GasGround.blockDensity
  have e6 : 6 * δ ≤ Real.exp (-(T.gasRate * R.coupling) - T.rt * N / 2 ^ 8) := by
    have h1 : Real.exp (-(T.gasRate * R.coupling) - T.rt * N / 2 ^ 8) = δ * Real.exp (T.gasRate * R.coupling) := by
      rw [hδ, ← Real.exp_add]
      congr 1
      ring
    have h2 : (6 : ℝ) ≤ Real.exp (T.gasRate * R.coupling) := by
      have h3 : Real.exp 2 ≤ Real.exp (T.gasRate * R.coupling) := Real.exp_le_exp.mpr hx2
      have h4 : (6 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp (1 : ℝ)
        have h5 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]
          norm_num
        have h6 : (2.7 : ℝ) ≤ Real.exp 1 := by
          have := Real.exp_one_gt_d9
          linarith
        rw [h5]
        nlinarith
      linarith
    rw [h1]
    nlinarith
  have tri : ∀ a b c d : ℝ, |a - d| ≤ |a - b| + |b - c| + |d - c| := by
    intro a b c d
    have h1 : |a - d| ≤ |a - b| + |b - d| := abs_sub_le a b d
    have h2 : |b - d| ≤ |b - c| + |c - d| := abs_sub_le b c d
    have h3 : |c - d| = |d - c| := abs_sub_comm c d
    linarith
  have := tri _ _ _ _ |>.trans (add_le_add (add_le_add s₁ s₃) s₂)
  linarith
end ClusterExpansionOfAStep
end YangMills.Construction
end
