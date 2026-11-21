import YangMills.Construction.Towers.AsymptoticsOfTheMassiveCoefficient
import YangMills.Construction.Towers.FormulaForTheMassiveCoefficient
import YangMills.Construction.Towers.TheCoefficientOfTheMassiveDeterminants
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower
open Massive ConstantSymbols
theorem massiveStiffnessAsymptotics_holds
    (hForm : MassiveStiffnessFormula)
    (hAsym : MassiveCoefficientAsymptotics) :
    MassiveStiffnessAsymptotics := by
  obtain ⟨σ₁, σ₂, t₁, t₂, e₁, e₂, hTr, hf⟩ := hForm
  have an := fun (L : ℕ) (hs : Conventions.IsAdmissibleBlockingFactor L) (hL : 0 < L) =>
    hAsym σ₁ σ₂ t₁ t₂ hTr (massiveStiffness hL) (fun z hz => (hf L hs hL z hz).2)
  have same : ∀ (L L' : ℕ), Conventions.IsAdmissibleBlockingFactor L →
      Conventions.IsAdmissibleBlockingFactor L' →
      ∀ (hL : 0 < L) (hL' : 0 < L') (z : ℝ), 0 < z →
        uvDeviation hL z = uvDeviation hL' z := by
    intro L L' hs hs' hL hL' z hz
    have ev : massiveStiffness hL =ᶠ[𝓝 z] massiveStiffness hL' := by
      filter_upwards [Ioi_mem_nhds hz] with y hy
      exact Complex.ofReal_injective ((hf L hs hL y hy).2.trans (hf L' hs' hL' y hy).2.symm)
    have d₁ := ev.deriv
    have d₂ := d₁.deriv
    simp only [uvDeviation, massiveStiffnessDeriv, massiveStiffnessDeriv2]
    rw [ev.eq_of_nhds, d₁.eq_of_nhds, d₂.eq_of_nhds]
  have sup : ∃ C, IsUVSupremum C := by
    have hs₀ : Conventions.IsAdmissibleBlockingFactor 13 := ⟨by decide, le_rfl⟩
    have hL₀ : 0 < 13 := by norm_num
    obtain ⟨C, hC⟩ := (an 13 hs₀ hL₀).2
    refine ⟨sSup (uvDeviation hL₀ '' Set.Ioc 0 1), fun L hs hL => ?_⟩
    have himage : uvDeviation hL '' Set.Ioc 0 1 = uvDeviation hL₀ '' Set.Ioc 0 1 :=
      Set.image_congr fun z hz => same L 13 hs hs₀ hL hL₀ z hz.1
    rw [himage]
    refine isLUB_csSup ⟨_, 1, ⟨one_pos, le_rfl⟩, rfl⟩ ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hC z hz.1 hz.2
  have hC : IsUVSupremum uvConstant := Classical.epsilon_spec sup
  exact ⟨⟨σ₁, σ₂, t₁, t₂, e₁, e₂, hTr, fun L hs hL z hz => hf L hs hL z hz⟩,
    fun L hs hL => (an L hs hL).1, hC,
    fun L hs hL z hz hz1 => (hC L hs hL).1 ⟨z, ⟨hz, hz1⟩, rfl⟩⟩
end YangMills.Construction.Tower
end
