import YangMills.Construction.Towers.FormulasOfThePlaneWaveFunctions
import YangMills.Construction.Towers.RelationsOfThePlaneWaveFunctions
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower.PlaneWaveCalculus
open YangMills.Construction.Tower.PlaneWaves
theorem weightRelationsHold_of_symbolFormulas
    (hFormulas : YangMills.Construction.Tower.PlaneWaveSymbolFormulas.Holds) :
    WeightRelationsHold := by
  intro L hL k hk
  have hF := hFormulas L hL k hk
  have hL0 : (L : ℝ) ≠ 0 := by
    have hL2 := hL.2
    exact_mod_cast (by omega : L ≠ 0)
  have hmesh : YangMills.Construction.Tower.finestMesh L k * (L : ℝ) ^ k = 1 := by
    unfold YangMills.Construction.Tower.finestMesh YangMills.Construction.Tower.meshAt
    rw [← zpow_natCast, ← zpow_add₀ hL0]
    simp
  have hmeshC : meshC L k * (L : ℂ) ^ k = 1 := by
    unfold meshC
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hmesh
  have hmesh0 : meshC L k ≠ 0 := left_ne_zero_of_mul_eq_one hmeshC
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q μ
    have hg := hF.geom_sum_eq (q μ)
    obtain ⟨x, hx⟩ : ∃ x, x = Complex.exp (Complex.I * meshC L k * q μ) := ⟨_, rfl⟩
    have hterms : ∑ l ∈ Finset.range (L ^ k),
        Complex.exp (Complex.I * meshC L k * (l : ℂ) * q μ) =
          ∑ l ∈ Finset.range (L ^ k), x ^ l := by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hx, ← Complex.exp_nat_mul]
      congr 1
      ring
    have hpow : x ^ (L ^ k) = Complex.exp (Complex.I * q μ) := by
      rw [hx, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      linear_combination (Complex.I * q μ) * hmeshC
    have hgeom : (∑ l ∈ Finset.range (L ^ k), x ^ l) * (x - 1) = x ^ (L ^ k) - 1 :=
      geom_sum_mul x _
    rw [hterms] at hg
    have hu : edgeWeight L k q μ =
        meshC L k * (∑ l ∈ Finset.range (L ^ k), x ^ l) * PlaneWaves.vertexWeight L k q := by
      rw [hg]
      rfl
    have hd : forwardSymbol L k q μ = (meshC L k)⁻¹ * (x - 1) := by
      rw [hx]
      rfl
    have hc : unitSymbol q μ = x ^ (L ^ k) - 1 := by
      rw [hpow]
      rfl
    rw [hu, hd, hc, ← hgeom]
    field_simp
  · intro κ m _
    funext μ
    show Complex.exp (Complex.I * (κ μ + 2 * (Real.pi : ℂ) * (m μ : ℂ))) - 1 =
      Complex.exp (Complex.I * κ μ) - 1
    have h : Complex.I * (κ μ + 2 * (Real.pi : ℂ) * (m μ : ℂ)) =
        Complex.I * κ μ + (m μ : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      ring
    rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · intro q
    unfold PlaneWaves.vertexWeight
    refine Finset.prod_congr rfl fun ν _ => ?_
    exact hF.dirichletSum_neg (q ν)
  · intro q
    have hreal : ∀ s : Finset (Fin 4),
        (∏ ν ∈ s, dirichletSum L k (YangMills.Construction.PeriodicOperators.toComplexVec q ν)).im = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        have hs : (dirichletSum L k (YangMills.Construction.PeriodicOperators.toComplexVec q a)).im = 0 :=
          hF.dirichletSum_im (q a)
        rw [Finset.prod_insert ha, Complex.mul_im, ih, hs]
        simp
    exact hreal Finset.univ
end YangMills.Construction.Tower.PlaneWaveCalculus
