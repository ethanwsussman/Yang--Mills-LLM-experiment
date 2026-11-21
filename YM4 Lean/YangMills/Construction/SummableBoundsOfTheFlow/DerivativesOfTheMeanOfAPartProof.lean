import YangMills.Construction.ColdChainAtEveryLevel.SitesOfAPatch
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAWeightedMean
import YangMills.Construction.ColdStepAtMirrorFrames.RimMeanIsAWeightedMean
import YangMills.Construction.SummableBoundsOfTheFlow.PartsOfAnExponentHaveTheirSizes
import Mathlib
import YangMills.Construction.SummableBoundsOfTheFlow.ExplicitCumulantsOfMeans
import YangMills.Construction.SummableBoundsOfTheFlow.LawOfACutIsAProbability
import YangMills.Construction.Towers.EntriesOfTheAbelianKernelsProof
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction
open MeasureTheory BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
variable {F : BlockFrame}
structure PartFamily (ψ : ExponentParts F) (ρ lam x v : ℝ) (Ψ : StepVariable (finiteCells F) → ℝ) (Y : F.Cell)
    (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (A H : (Fin k → ℝ) → StepVariable (finiteCells F) → ℝ) : Prop where
  eq_potential : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → A 0 η = Ψ η
  deriv_exponent : ∀ (j : ℕ) (l : Fin (j + 1) → Fin k), j + 1 ≤ 3 → ∀ η : StepVariable (finiteCells F),
    (∀ b, ‖η b‖ < ρ) → paramIteratedDeriv A (fun i => Pi.single (l i) 1) 0 η =
      v * exponentDerivSum ψ V (c ∘ l) (X ∘ l) η
  deriv_observable : ∀ (j : ℕ) (l : Fin j → Fin k), j ≤ 3 → ∀ η : StepVariable (finiteCells F),
    (∀ b, ‖η b‖ < ρ) →
    paramIteratedDeriv H (fun i => Pi.single (l i) 1) 0 η = partCentredDeriv ψ lam x Y V (c ∘ l) (X ∘ l) η
def PartMeanDerivBound (N : ℕ) (κ lam : ℝ) (Cq : ℕ → ℝ) (Kc : ℝ) : Prop :=
      ∀ (F : BlockFrame) (ρ x v : ℝ) (p : ℝ → ℝ) (ψ : ExponentParts F) (V : F.GaugeField F.top)
        (Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ) (K : ↥(chordBonds (finiteCells F)) →
          ↥(chordBonds (finiteCells F)) → ℝ) (Y : F.Cell) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
        (X : Fin k → imaginaryQuaternions) (A H : (Fin k → ℝ) → StepVariable (finiteCells F) → ℝ)
        (B : Set (Fin k → ℝ)) (M : ℝ),
        0 < ρ → 0 < x → IsCutoff ρ p → 0 ≤ v → v ≤ 1 → k ≤ 3 →
        (∀ z : F.Cell,
          (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤ N) →
        IsUniformlyConvexDecaying ρ (x * lam / 4) κ (chordBondDist F) Ψ K →
        (∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
          |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * lam / 4) * ‖e‖) →
        IsOpen B → (0 : Fin k → ℝ) ∈ B →
        IsDominatedSmoothFamily (cutoffLaw F ρ p) 3 B M A → IsDominatedSmoothFamily (cutoffLaw F ρ p) 3 B M H →
        PartFamily ψ ρ lam x v Ψ Y V c X A H →
        (∀ (j : ℕ) (l : Fin j → Fin k), j ≤ 3 →
          ExponentPartsSizes ρ lam x κ p Cq ψ Ψ Y V (c ∘ l) (X ∘ l)) →
        |iteratedFDeriv ℝ k (fun s => gibbsMean (cutoffLaw F ρ p) (A s) (H s)) 0 (fun l => Pi.single l 1)| ≤
          Kc * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c))
def partMeanDerivBoundStatement : Prop :=
  ∀ (N : ℕ) (κ lam : ℝ) (Cq : ℕ → ℝ), 0 < κ → 0 < lam → (∀ q, 0 ≤ Cq q) →
    ∃ Kc : ℝ, 0 ≤ Kc ∧ PartMeanDerivBound N κ lam Cq Kc
end Interpolation
end YangMills.Construction
end

noncomputable section
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Cumulants ConvexObservables
namespace Interpolation
namespace PartMeanDeriv
variable {F : BlockFrame}
theorem cutoffWeight_mul_exp_eq_ballDensity {ρ : ℝ} {p : ℝ → ℝ} {A₀ Ψ : StepVariable (finiteCells F) → ℝ}
    (hA : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → A₀ η = Ψ η) (η : StepVariable (finiteCells F)) :
    cutoffWeight ρ p η * Real.exp (- A₀ η) = ballDensity (cutoffFactor ρ p) Ψ η := by
  unfold ballDensity radialWeightProd cutoffWeight
  by_cases h : ∀ b, ‖η b‖ < ρ
  · rw [hA η h]
  · push_neg at h
    obtain ⟨b, hb⟩ := h
    have h0 : ∏ b : ↥(chordBonds (finiteCells F)), cutoffFactor ρ p ‖η b‖ = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ b) (by simp [cutoffFactor, not_lt.mpr hb])
    rw [h0]
    simp
theorem cutoffMean_eq_ballExpectation {ρ : ℝ} {p : ℝ → ℝ} {A₀ Ψ : StepVariable (finiteCells F) → ℝ}
    (hA : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → A₀ η = Ψ η)
    (g : StepVariable (finiteCells F) → ℝ) :
    cutoffMean ρ p A₀ g = ballExpectation (cutoffFactor ρ p) Ψ g := by
  unfold cutoffMean ballExpectation
  simp_rw [cutoffWeight_mul_exp_eq_ballDensity hA]
theorem ballDensity_eq_zero_of_not_mem {ι : Type} [Fintype ι] {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ}
    {η : BondField ι} (h : ¬ ∀ b, ‖η b‖ < ρ) : ballDensity (cutoffFactor ρ p) Ψ η = 0 := by
  push_neg at h
  obtain ⟨b, hb⟩ := h
  unfold ballDensity radialWeightProd
  have h0 : ∏ b, cutoffFactor ρ p ‖η b‖ = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ b) (by simp [cutoffFactor, not_lt.mpr hb])
  rw [h0]
  simp
theorem ballExpectation_congr {ι : Type} [Fintype ι] {ρ : ℝ} {p : ℝ → ℝ} {Ψ g g' : BondField ι → ℝ}
    (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → g η = g' η) :
    ballExpectation (cutoffFactor ρ p) Ψ g = ballExpectation (cutoffFactor ρ p) Ψ g' := by
  unfold ballExpectation
  congr 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun η => ?_
  by_cases hη : ∀ b, ‖η b‖ < ρ
  · simp only [h η hη]
  · simp only [ballDensity_eq_zero_of_not_mem hη, mul_zero]
theorem cumulantFromMoments_congr {ι : Type} [Fintype ι] {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ} {M : ℕ}
    {H H' : Fin M → BondField ι → ℝ}
    (h : ∀ i, ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → H i η = H' i η) :
    cumulantFromMoments (cutoffFactor ρ p) Ψ H = cumulantFromMoments (cutoffFactor ρ p) Ψ H' := by
  unfold cumulantFromMoments
  refine Finset.sum_congr rfl fun π _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun J _ => ?_
  exact ballExpectation_congr fun η hη => Finset.prod_congr rfl fun l _ => h l η hη
theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem cellSupDist_triangle (x y z : F.Cell) : cellSupDist x z ≤ cellSupDist x y + cellSupDist y z := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
theorem bondSpan_le_of_forall {Y : F.Cell} {k : ℕ} {c : Fin k → F.Site F.top × Fin 4} {S : ℕ}
    (h : ∀ i, cellSupDist Y (c i).1 ≤ S) : bondSpan Y c ≤ 2 * S := by
  refine max_le (Finset.sup_le fun l _ => ?_) (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_)
  · have : cellSupDist Y (c l).1 ≤ S := h l
    show cellSupDist Y (c l).1 ≤ 2 * S
    omega
  · have h1 := cellSupDist_triangle (c l).1 Y (c l').1
    have h2 := h l
    have h3 := h l'
    rw [cellSupDist_comm (c l).1 Y] at h1
    show cellSupDist (c l).1 (c l').1 ≤ 2 * S
    omega
theorem cellSupDist_le_bondSpan (Y : F.Cell) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (l : Fin k) :
    cellSupDist Y (c l).1 ≤ bondSpan Y c :=
  le_max_of_le_left (Finset.le_sup (f := fun l : Fin k => siteSupDist Y (c l).1) (Finset.mem_univ l))
theorem cellSupDist_le_cellsDiameter {M : ℕ} (Z : Fin M → F.Cell) (i j : Fin M) :
    cellSupDist (Z i) (Z j) ≤ cellsDiameter Z :=
  (Finset.le_sup (f := fun j => cellSupDist (Z i) (Z j)) (Finset.mem_univ j)).trans
    (Finset.le_sup (f := fun i => Finset.univ.sup fun j => cellSupDist (Z i) (Z j)) (Finset.mem_univ i))
theorem exp_three_mul_le {κ : ℝ} (hκ : 0 < κ) {n s D d : ℕ} (h : n ≤ 2 * (s + D + d)) :
    Real.exp (-(2 ^ 5 * κ * s)) * Real.exp (-(2 ^ 4 * κ * D)) * Real.exp (-(κ / 8 * d)) ≤
      Real.exp (-(κ / 2 ^ 6 * n)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have a1 : (n : ℝ) ≤ 2 * (s + D + d) := by exact_mod_cast h
  have s0 : (0 : ℝ) ≤ s := by positivity
  have D0 : (0 : ℝ) ≤ D := by positivity
  have d0 : (0 : ℝ) ≤ d := by positivity
  have h1 := mul_le_mul_of_nonneg_left a1 hκ.le
  nlinarith [mul_nonneg hκ.le s0, mul_nonneg hκ.le D0, mul_nonneg hκ.le d0]
theorem forall_fin_two_of {P : Fin 2 → Prop} (h0 : P 0) (h1 : P 1) : ∀ i, P i := by
  intro i
  fin_cases i
  · exact h0
  · exact h1
theorem forall_fin_three_of {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i, P i := by
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
theorem forall_fin_four_of {P : Fin 4 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) : ∀ i, P i := by apply _root_.YangMills.Construction.Tower.AbelianKernelEntries.fin_four_forall <;> assumption
structure SizedDerivatives (ρ x κ T : ℝ) (p : ℝ → ℝ) (Cq : ℕ → ℝ) (Ψ : StepVariable (finiteCells F) → ℝ)
    (Y : F.Cell) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (OH : ∀ j, (Fin j → Fin k) → StepVariable (finiteCells F) → ℝ)
    (OA : ∀ j, (Fin (j + 1) → Fin k) → StepVariable (finiteCells F) → ℝ) : Prop where
  cumulant_bound : ∀ (M : ℕ) (H : Fin M → StepVariable (finiteCells F) → ℝ) (Z : Fin M → F.Cell) (h : Fin M → ℝ),
    2 ≤ M → M ≤ 9 → (∀ i, ContDiffOn ℝ 1 (H i) {η | ∀ b, ‖η b‖ < ρ}) → (∀ i, 0 ≤ h i) →
    (∀ i, HasLocalSize ρ (cutoffFactor ρ p) Ψ Cq x κ (h i)
      (fun b => (cellSupDist (enclosingCell b.1.1) (Z i) : ℝ)) (H i)) →
    |cumulantFromMoments (cutoffFactor ρ p) Ψ H| ≤
      T * (∏ i, (sizeConstantSum Cq M * h i)) * Real.exp (-(κ / 8 * cellsDiameter Z))
  smooth_obs : ∀ (j : ℕ) (l : Fin j → Fin k), j ≤ 3 → ContDiffOn ℝ 1 (OH j l) {η | ∀ b, ‖η b‖ < ρ}
  smooth_exp : ∀ (j : ℕ) (l : Fin (j + 1) → Fin k), j + 1 ≤ 3 → ContDiffOn ℝ 1 (OA j l) {η | ∀ b, ‖η b‖ < ρ}
  size_obs : ∀ (j : ℕ) (l : Fin j → Fin k), j ≤ 3 →
    HasLocalSize ρ (cutoffFactor ρ p) Ψ Cq x κ (Real.exp (-(2 ^ 5 * κ * bondSpan Y (c ∘ l))))
      (fun b => (cellSupDist (enclosingCell b.1.1) Y : ℝ)) (OH j l)
  size_exp : ∀ (j : ℕ) (l : Fin (j + 1) → Fin k), j + 1 ≤ 3 →
    HasLocalSize ρ (cutoffFactor ρ p) Ψ Cq x κ (Real.exp (-(2 ^ 4 * κ * bondSpan (c (l 0)).1 (c ∘ l))))
      (fun b => (cellSupDist (enclosingCell b.1.1) (c (l 0)).1 : ℝ)) (OA j l)
  mean_bound : ∀ (j : ℕ) (l : Fin j → Fin k), j ≤ 3 →
    |ballExpectation (cutoffFactor ρ p) Ψ (OH j l)| ≤ Cq 1 * Real.exp (-(2 ^ 5 * κ * bondSpan Y (c ∘ l)))
section Terms
variable {ρ x κ T : ℝ} {p : ℝ → ℝ} {Cq : ℕ → ℝ} {Ψ : StepVariable (finiteCells F) → ℝ} {Y : F.Cell}
  {k : ℕ} {c : Fin k → F.Site F.top × Fin 4}
  {OH : ∀ j, (Fin j → Fin k) → StepVariable (finiteCells F) → ℝ}
  {OA : ∀ j, (Fin (j + 1) → Fin k) → StepVariable (finiteCells F) → ℝ}
theorem cumulant_le_of_sizes {M : ℕ} (hS : SizedDerivatives ρ x κ T p Cq Ψ Y c OH OA) (hT : 0 ≤ T)
    (hc : 0 ≤ sizeConstantSum Cq M) (hM2 : 2 ≤ M) (hM9 : M ≤ 9)
    (H : Fin M → StepVariable (finiteCells F) → ℝ) (Z : Fin M → F.Cell) (h : Fin M → ℝ) {e : ℝ}
    (hsm : ∀ i, ContDiffOn ℝ 1 (H i) {η | ∀ b, ‖η b‖ < ρ}) (h0 : ∀ i, 0 ≤ h i)
    (hsz : ∀ i, HasLocalSize ρ (cutoffFactor ρ p) Ψ Cq x κ (h i)
      (fun b => (cellSupDist (enclosingCell b.1.1) (Z i) : ℝ)) (H i))
    (hfin : (∏ i, h i) * Real.exp (-(κ / 8 * cellsDiameter Z)) ≤ e) :
    |cumulantFromMoments (cutoffFactor ρ p) Ψ H| ≤ T * sizeConstantSum Cq M ^ M * e := by
  refine (hS.cumulant_bound M H Z h hM2 hM9 hsm h0 hsz).trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin, mul_assoc, mul_assoc, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hT
  apply mul_le_mul_of_nonneg_left hfin (pow_nonneg hc M)
theorem cumulant_two_le (hκ : 0 < κ) (hS : SizedDerivatives ρ x κ T p Cq Ψ Y c OH OA) (hT : 0 ≤ T)
    (hc : 0 ≤ sizeConstantSum Cq 2)
    {j₀ j₁ : ℕ} (l₀ : Fin j₀ → Fin k) (l₁ : Fin (j₁ + 1) → Fin k) (h₀ : j₀ ≤ 3) (h₁ : j₁ + 1 ≤ 3)
    (hcov : ∀ i, (∃ a, l₀ a = i) ∨ (∃ a, l₁ a = i)) :
    |cumulantFromMoments (cutoffFactor ρ p) Ψ ![OH j₀ l₀, OA j₁ l₁]| ≤
      T * sizeConstantSum Cq 2 ^ 2 * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c)) := by
  set z₁ := (c (l₁ 0)).1 with hz₁
  set Z : Fin 2 → F.Cell := ![Y, z₁] with hZ
  refine cumulant_le_of_sizes hS hT hc (by norm_num) (by norm_num) _ Z
    ![Real.exp (-(2 ^ 5 * κ * bondSpan Y (c ∘ l₀))), Real.exp (-(2 ^ 4 * κ * bondSpan z₁ (c ∘ l₁)))]
    (forall_fin_two_of (hS.smooth_obs j₀ l₀ h₀) (hS.smooth_exp j₁ l₁ h₁))
    (forall_fin_two_of (Real.exp_pos _).le (Real.exp_pos _).le)
    (forall_fin_two_of (hS.size_obs j₀ l₀ h₀) (hS.size_exp j₁ l₁ h₁)) ?_
  rw [Fin.prod_univ_two]
  have hd : cellSupDist Y z₁ ≤ cellsDiameter Z := cellSupDist_le_cellsDiameter Z 0 1
  refine exp_three_mul_le hκ (bondSpan_le_of_forall fun i => ?_)
  rcases hcov i with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · have := cellSupDist_le_bondSpan Y (c ∘ l₀) a
    simp only [Function.comp] at this
    omega
  · have h1 := cellSupDist_le_bondSpan z₁ (c ∘ l₁) a
    simp only [Function.comp] at h1
    have h2 := cellSupDist_triangle Y z₁ (c (l₁ a)).1
    omega
theorem cumulant_three_le (hκ : 0 < κ) (hS : SizedDerivatives ρ x κ T p Cq Ψ Y c OH OA) (hT : 0 ≤ T)
    (hc : 0 ≤ sizeConstantSum Cq 3)
    {j₀ j₁ j₂ : ℕ} (l₀ : Fin j₀ → Fin k) (l₁ : Fin (j₁ + 1) → Fin k) (l₂ : Fin (j₂ + 1) → Fin k) (h₀ : j₀ ≤ 3)
    (h₁ : j₁ + 1 ≤ 3) (h₂ : j₂ + 1 ≤ 3)
    (hcov : ∀ i, (∃ a, l₀ a = i) ∨ (∃ a, l₁ a = i) ∨ (∃ a, l₂ a = i)) :
    |cumulantFromMoments (cutoffFactor ρ p) Ψ ![OH j₀ l₀, OA j₁ l₁, OA j₂ l₂]| ≤
      T * sizeConstantSum Cq 3 ^ 3 * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c)) := by
  set z₁ := (c (l₁ 0)).1 with hz₁
  set z₂ := (c (l₂ 0)).1 with hz₂
  set Z : Fin 3 → F.Cell := ![Y, z₁, z₂] with hZ
  refine cumulant_le_of_sizes hS hT hc (by norm_num) (by norm_num) _ Z
    ![Real.exp (-(2 ^ 5 * κ * bondSpan Y (c ∘ l₀))), Real.exp (-(2 ^ 4 * κ * bondSpan z₁ (c ∘ l₁))),
      Real.exp (-(2 ^ 4 * κ * bondSpan z₂ (c ∘ l₂)))]
    (forall_fin_three_of (hS.smooth_obs j₀ l₀ h₀) (hS.smooth_exp j₁ l₁ h₁) (hS.smooth_exp j₂ l₂ h₂))
    (forall_fin_three_of (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le)
    (forall_fin_three_of (hS.size_obs j₀ l₀ h₀) (hS.size_exp j₁ l₁ h₁) (hS.size_exp j₂ l₂ h₂)) ?_
  rw [Fin.prod_univ_three]
  have hd1 : cellSupDist Y z₁ ≤ cellsDiameter Z := cellSupDist_le_cellsDiameter Z 0 1
  have hd2 : cellSupDist Y z₂ ≤ cellsDiameter Z := cellSupDist_le_cellsDiameter Z 0 2
  have e : Real.exp (-(2 ^ 4 * κ * bondSpan z₁ (c ∘ l₁))) * Real.exp (-(2 ^ 4 * κ * bondSpan z₂ (c ∘ l₂))) =
      Real.exp (-(2 ^ 4 * κ * ((bondSpan z₁ (c ∘ l₁) + bondSpan z₂ (c ∘ l₂) : ℕ) : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  show Real.exp (-(2 ^ 5 * κ * bondSpan Y (c ∘ l₀))) * Real.exp (-(2 ^ 4 * κ * bondSpan z₁ (c ∘ l₁))) *
      Real.exp (-(2 ^ 4 * κ * bondSpan z₂ (c ∘ l₂))) * _ ≤ _
  rw [mul_assoc (Real.exp (-(2 ^ 5 * κ * bondSpan Y (c ∘ l₀)))), e]
  refine exp_three_mul_le hκ (bondSpan_le_of_forall fun i => ?_)
  rcases hcov i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · have := cellSupDist_le_bondSpan Y (c ∘ l₀) a
    simp only [Function.comp] at this
    omega
  · have h1 := cellSupDist_le_bondSpan z₁ (c ∘ l₁) a
    simp only [Function.comp] at h1
    have h2 := cellSupDist_triangle Y z₁ (c (l₁ a)).1
    omega
  · have h1 := cellSupDist_le_bondSpan z₂ (c ∘ l₂) a
    simp only [Function.comp] at h1
    have h2 := cellSupDist_triangle Y z₂ (c (l₂ a)).1
    omega
theorem cumulant_four_le (hκ : 0 < κ) (hS : SizedDerivatives ρ x κ T p Cq Ψ Y c OH OA) (hT : 0 ≤ T)
    (hc : 0 ≤ sizeConstantSum Cq 4)
    {j₀ j₁ j₂ j₃ : ℕ} (l₀ : Fin j₀ → Fin k) (l₁ : Fin (j₁ + 1) → Fin k) (l₂ : Fin (j₂ + 1) → Fin k)
    (l₃ : Fin (j₃ + 1) → Fin k) (h₀ : j₀ ≤ 3) (h₁ : j₁ + 1 ≤ 3) (h₂ : j₂ + 1 ≤ 3) (h₃ : j₃ + 1 ≤ 3)
    (hcov : ∀ i, (∃ a, l₀ a = i) ∨ (∃ a, l₁ a = i) ∨ (∃ a, l₂ a = i) ∨ (∃ a, l₃ a = i)) :
    |cumulantFromMoments (cutoffFactor ρ p) Ψ ![OH j₀ l₀, OA j₁ l₁, OA j₂ l₂, OA j₃ l₃]| ≤
      T * sizeConstantSum Cq 4 ^ 4 * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c)) := by
  set z₁ := (c (l₁ 0)).1 with hz₁
  set z₂ := (c (l₂ 0)).1 with hz₂
  set z₃ := (c (l₃ 0)).1 with hz₃
  set Z : Fin 4 → F.Cell := ![Y, z₁, z₂, z₃] with hZ
  refine cumulant_le_of_sizes hS hT hc (by norm_num) (by norm_num) _ Z
    ![Real.exp (-(2 ^ 5 * κ * bondSpan Y (c ∘ l₀))), Real.exp (-(2 ^ 4 * κ * bondSpan z₁ (c ∘ l₁))),
      Real.exp (-(2 ^ 4 * κ * bondSpan z₂ (c ∘ l₂))), Real.exp (-(2 ^ 4 * κ * bondSpan z₃ (c ∘ l₃)))]
    (forall_fin_four_of (hS.smooth_obs j₀ l₀ h₀) (hS.smooth_exp j₁ l₁ h₁) (hS.smooth_exp j₂ l₂ h₂)
      (hS.smooth_exp j₃ l₃ h₃))
    (forall_fin_four_of (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le)
    (forall_fin_four_of (hS.size_obs j₀ l₀ h₀) (hS.size_exp j₁ l₁ h₁) (hS.size_exp j₂ l₂ h₂)
      (hS.size_exp j₃ l₃ h₃)) ?_
  rw [Fin.prod_univ_four]
  have hd1 : cellSupDist Y z₁ ≤ cellsDiameter Z := cellSupDist_le_cellsDiameter Z 0 1
  have hd2 : cellSupDist Y z₂ ≤ cellsDiameter Z := cellSupDist_le_cellsDiameter Z 0 2
  have hd3 : cellSupDist Y z₃ ≤ cellsDiameter Z := cellSupDist_le_cellsDiameter Z 0 3
  have e : Real.exp (-(2 ^ 4 * κ * bondSpan z₁ (c ∘ l₁))) * Real.exp (-(2 ^ 4 * κ * bondSpan z₂ (c ∘ l₂))) *
      Real.exp (-(2 ^ 4 * κ * bondSpan z₃ (c ∘ l₃))) =
      Real.exp (-(2 ^ 4 * κ * ((bondSpan z₁ (c ∘ l₁) + bondSpan z₂ (c ∘ l₂) + bondSpan z₃ (c ∘ l₃) : ℕ) : ℝ))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  show Real.exp (-(2 ^ 5 * κ * bondSpan Y (c ∘ l₀))) * Real.exp (-(2 ^ 4 * κ * bondSpan z₁ (c ∘ l₁))) *
      Real.exp (-(2 ^ 4 * κ * bondSpan z₂ (c ∘ l₂))) * Real.exp (-(2 ^ 4 * κ * bondSpan z₃ (c ∘ l₃))) * _ ≤ _
  rw [mul_assoc (Real.exp (-(2 ^ 5 * κ * bondSpan Y (c ∘ l₀))) * Real.exp (-(2 ^ 4 * κ * bondSpan z₁ (c ∘ l₁)))),
    mul_assoc (Real.exp (-(2 ^ 5 * κ * bondSpan Y (c ∘ l₀)))),
    ← mul_assoc (Real.exp (-(2 ^ 4 * κ * bondSpan z₁ (c ∘ l₁)))), e]
  refine exp_three_mul_le hκ (bondSpan_le_of_forall fun i => ?_)
  rcases hcov i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · have := cellSupDist_le_bondSpan Y (c ∘ l₀) a
    simp only [Function.comp] at this
    omega
  · have h1 := cellSupDist_le_bondSpan z₁ (c ∘ l₁) a
    simp only [Function.comp] at h1
    have h2 := cellSupDist_triangle Y z₁ (c (l₁ a)).1
    omega
  · have h1 := cellSupDist_le_bondSpan z₂ (c ∘ l₂) a
    simp only [Function.comp] at h1
    have h2 := cellSupDist_triangle Y z₂ (c (l₂ a)).1
    omega
  · have h1 := cellSupDist_le_bondSpan z₃ (c ∘ l₃) a
    simp only [Function.comp] at h1
    have h2 := cellSupDist_triangle Y z₃ (c (l₃ a)).1
    omega
theorem exp_mul_le_of_le_two_mul {κ : ℝ} (hκ : 0 < κ) {n s : ℕ} (h : n ≤ 2 * s) :
    Real.exp (-(2 ^ 5 * κ * s)) ≤ Real.exp (-(κ / 2 ^ 6 * n)) := by
  apply Real.exp_le_exp.mpr
  have a1 : (n : ℝ) ≤ 2 * s := by exact_mod_cast h
  have s0 : (0 : ℝ) ≤ s := by positivity
  have h1 := mul_le_mul_of_nonneg_left a1 hκ.le
  nlinarith [mul_nonneg hκ.le s0]
theorem mean_le_of_cover (hκ : 0 < κ) (hS : SizedDerivatives ρ x κ T p Cq Ψ Y c OH OA) (hq : 0 ≤ Cq 1)
    {j : ℕ} (l : Fin j → Fin k) (hj : j ≤ 3) (hcov : ∀ i, ∃ a, l a = i) :
    |ballExpectation (cutoffFactor ρ p) Ψ (OH j l)| ≤ Cq 1 * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c)) := by
  refine (hS.mean_bound j l hj).trans (mul_le_mul_of_nonneg_left ?_ hq)
  refine exp_mul_le_of_le_two_mul hκ (bondSpan_le_of_forall fun i => ?_)
  obtain ⟨a, rfl⟩ := hcov i
  exact cellSupDist_le_bondSpan Y (c ∘ l) a
end Terms
section Means
theorem gibbsCovariance_eq_cumulant (hExp : lowOrderCumulantFormulas) {ι : Type} [Fintype ι] {r : ℝ → ℝ}
    {Ψ : BondField ι → ℝ} {μ : Measure (BondField ι)} {A₀ : BondField ι → ℝ}
    (hm : ∀ g, gibbsMean μ A₀ g = ballExpectation r Ψ g) (f g : BondField ι → ℝ) :
    gibbsCovariance μ A₀ f g = cumulantFromMoments r Ψ ![f, g] := by
  rw [(hExp ι r Ψ).1 ![f, g]]
  unfold gibbsCovariance
  simp only [hm]
  rfl
theorem gibbsCumulantThree_eq_cumulant (hExp : lowOrderCumulantFormulas) {ι : Type} [Fintype ι] {r : ℝ → ℝ}
    {Ψ : BondField ι → ℝ} {μ : Measure (BondField ι)} {A₀ : BondField ι → ℝ}
    (hm : ∀ g, gibbsMean μ A₀ g = ballExpectation r Ψ g) (f g h : BondField ι → ℝ) :
    gibbsCumulantThree μ A₀ f g h = cumulantFromMoments r Ψ ![f, g, h] := by
  rw [(hExp ι r Ψ).2.1 ![f, g, h]]
  unfold gibbsCumulantThree
  simp only [hm]
  rfl
theorem gibbsCumulantFour_eq_cumulant (hExp : lowOrderCumulantFormulas) {ι : Type} [Fintype ι] {r : ℝ → ℝ}
    {Ψ : BondField ι → ℝ} {μ : Measure (BondField ι)} {A₀ : BondField ι → ℝ}
    (hm : ∀ g, gibbsMean μ A₀ g = ballExpectation r Ψ g) (f g h l : BondField ι → ℝ) :
    gibbsCumulantFour μ A₀ f g h l = cumulantFromMoments r Ψ ![f, g, h, l] := by
  rw [(hExp ι r Ψ).2.2 ![f, g, h, l]]
  unfold gibbsCumulantFour
  simp only [hm]
  rfl
end Means
section Main
variable {ρ x κ T : ℝ} {p : ℝ → ℝ} {Cq : ℕ → ℝ} {Ψ : StepVariable (finiteCells F) → ℝ} {Y : F.Cell}
  {k : ℕ} {c : Fin k → F.Site F.top × Fin 4}
  {OH : ∀ j, (Fin j → Fin k) → StepVariable (finiteCells F) → ℝ}
  {OA : ∀ j, (Fin (j + 1) → Fin k) → StepVariable (finiteCells F) → ℝ}
  {μ : Measure (StepVariable (finiteCells F))} {A₀ : StepVariable (finiteCells F) → ℝ}
theorem gibbsMean_le (hκ : 0 < κ) (hS : SizedDerivatives ρ x κ T p Cq Ψ Y c OH OA) (hq : 0 ≤ Cq 1)
    (hm : ∀ g, gibbsMean μ A₀ g = ballExpectation (cutoffFactor ρ p) Ψ g) {j : ℕ} (l : Fin j → Fin k) (hj : j ≤ 3)
    {f : StepVariable (finiteCells F) → ℝ}
    (hf : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → f η = OH j l η)
    (hcov : ∀ i, ∃ a, l a = i) :
    |gibbsMean μ A₀ f| ≤ Cq 1 * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c)) := by
  rw [hm, ballExpectation_congr hf]
  exact mean_le_of_cover hκ hS hq l hj hcov
theorem gibbsCovariance_le (hExp : lowOrderCumulantFormulas) (hκ : 0 < κ)
    (hS : SizedDerivatives ρ x κ T p Cq Ψ Y c OH OA) (hT : 0 ≤ T) (hc : 0 ≤ sizeConstantSum Cq 2)
    (hm : ∀ g, gibbsMean μ A₀ g = ballExpectation (cutoffFactor ρ p) Ψ g) {j₀ j₁ : ℕ} (l₀ : Fin j₀ → Fin k)
    (l₁ : Fin (j₁ + 1) → Fin k) (h₀ : j₀ ≤ 3) (h₁ : j₁ + 1 ≤ 3) {f g : StepVariable (finiteCells F) → ℝ}
    (hf : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → f η = OH j₀ l₀ η)
    (hg : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → g η = OA j₁ l₁ η)
    (hcov : ∀ i, (∃ a, l₀ a = i) ∨ (∃ a, l₁ a = i)) :
    |gibbsCovariance μ A₀ f g| ≤ T * sizeConstantSum Cq 2 ^ 2 * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c)) := by
  rw [gibbsCovariance_eq_cumulant hExp hm,
    cumulantFromMoments_congr (H' := ![OH j₀ l₀, OA j₁ l₁]) (forall_fin_two_of hf hg)]
  exact cumulant_two_le hκ hS hT hc l₀ l₁ h₀ h₁ hcov
theorem gibbsCumulantThree_le (hExp : lowOrderCumulantFormulas) (hκ : 0 < κ)
    (hS : SizedDerivatives ρ x κ T p Cq Ψ Y c OH OA) (hT : 0 ≤ T) (hc : 0 ≤ sizeConstantSum Cq 3)
    (hm : ∀ g, gibbsMean μ A₀ g = ballExpectation (cutoffFactor ρ p) Ψ g) {j₀ j₁ j₂ : ℕ} (l₀ : Fin j₀ → Fin k)
    (l₁ : Fin (j₁ + 1) → Fin k) (l₂ : Fin (j₂ + 1) → Fin k) (h₀ : j₀ ≤ 3) (h₁ : j₁ + 1 ≤ 3) (h₂ : j₂ + 1 ≤ 3)
    {f g h : StepVariable (finiteCells F) → ℝ}
    (hf : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → f η = OH j₀ l₀ η)
    (hg : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → g η = OA j₁ l₁ η)
    (hh : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → h η = OA j₂ l₂ η)
    (hcov : ∀ i, (∃ a, l₀ a = i) ∨ (∃ a, l₁ a = i) ∨ (∃ a, l₂ a = i)) :
    |gibbsCumulantThree μ A₀ f g h| ≤ T * sizeConstantSum Cq 3 ^ 3 * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c)) := by
  rw [gibbsCumulantThree_eq_cumulant hExp hm,
    cumulantFromMoments_congr (H' := ![OH j₀ l₀, OA j₁ l₁, OA j₂ l₂]) (forall_fin_three_of hf hg hh)]
  exact cumulant_three_le hκ hS hT hc l₀ l₁ l₂ h₀ h₁ h₂ hcov
theorem gibbsCumulantFour_le (hExp : lowOrderCumulantFormulas) (hκ : 0 < κ)
    (hS : SizedDerivatives ρ x κ T p Cq Ψ Y c OH OA) (hT : 0 ≤ T) (hc : 0 ≤ sizeConstantSum Cq 4)
    (hm : ∀ g, gibbsMean μ A₀ g = ballExpectation (cutoffFactor ρ p) Ψ g) {j₀ j₁ j₂ j₃ : ℕ} (l₀ : Fin j₀ → Fin k)
    (l₁ : Fin (j₁ + 1) → Fin k) (l₂ : Fin (j₂ + 1) → Fin k) (l₃ : Fin (j₃ + 1) → Fin k) (h₀ : j₀ ≤ 3)
    (h₁ : j₁ + 1 ≤ 3) (h₂ : j₂ + 1 ≤ 3) (h₃ : j₃ + 1 ≤ 3) {f g h e : StepVariable (finiteCells F) → ℝ}
    (hf : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → f η = OH j₀ l₀ η)
    (hg : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → g η = OA j₁ l₁ η)
    (hh : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → h η = OA j₂ l₂ η)
    (he : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → e η = OA j₃ l₃ η)
    (hcov : ∀ i, (∃ a, l₀ a = i) ∨ (∃ a, l₁ a = i) ∨ (∃ a, l₂ a = i) ∨ (∃ a, l₃ a = i)) :
    |gibbsCumulantFour μ A₀ f g h e| ≤ T * sizeConstantSum Cq 4 ^ 4 * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c)) := by
  rw [gibbsCumulantFour_eq_cumulant hExp hm,
    cumulantFromMoments_congr (H' := ![OH j₀ l₀, OA j₁ l₁, OA j₂ l₂, OA j₃ l₃]) (forall_fin_four_of hf hg hh he)]
  exact cumulant_four_le hκ hS hT hc l₀ l₁ l₂ l₃ h₀ h₁ h₂ h₃ hcov
theorem basisVectors_one {k : ℕ} (a : Fin k) :
    (![Pi.single a 1] : Fin 1 → Fin k → ℝ) = fun i => Pi.single ((![a] : Fin 1 → Fin k) i) 1 := by
  funext i
  fin_cases i
  rfl
theorem basisVectors_two {k : ℕ} (a b : Fin k) :
    (![Pi.single a 1, Pi.single b 1] : Fin 2 → Fin k → ℝ) =
      fun i => Pi.single ((![a, b] : Fin 2 → Fin k) i) 1 := by
  funext i
  fin_cases i <;> rfl
theorem basisVectors_three {k : ℕ} (a b c : Fin k) :
    (![Pi.single a 1, Pi.single b 1, Pi.single c 1] : Fin 3 → Fin k → ℝ) =
      fun i => Pi.single ((![a, b, c] : Fin 3 → Fin k) i) 1 := by
  funext i
  fin_cases i <;> rfl
theorem iteratedFDeriv_mean_le_of_sized [IsFiniteMeasure μ] (hExp : lowOrderCumulantFormulas)
    (hDer : GibbsMeanThirdOrderExpansion)
    (hκ : 0 < κ) (hS : SizedDerivatives ρ x κ T p Cq Ψ Y c OH OA) (hT : 0 ≤ T) (hq : 0 ≤ Cq 1)
    (hc2 : 0 ≤ sizeConstantSum Cq 2) (hc3 : 0 ≤ sizeConstantSum Cq 3) (hc4 : 0 ≤ sizeConstantSum Cq 4) (hk : k ≤ 3)
    {Mb : ℝ} {B : Set (Fin k → ℝ)} {A H : (Fin k → ℝ) → StepVariable (finiteCells F) → ℝ}
    (hBo : IsOpen B) (hB0 : (0 : Fin k → ℝ) ∈ B) (hμ0 : μ ≠ 0) (hdA : IsDominatedSmoothFamily μ 3 B Mb A)
    (hdH : IsDominatedSmoothFamily μ 3 B Mb H)
    (hm : ∀ g, gibbsMean μ (A 0) g = ballExpectation (cutoffFactor ρ p) Ψ g)
    (dH : ∀ (j : ℕ) (l : Fin j → Fin k), j ≤ 3 → ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      paramIteratedDeriv H (fun i => Pi.single (l i) 1) 0 η = OH j l η)
    (dA : ∀ (j : ℕ) (l : Fin (j + 1) → Fin k), j + 1 ≤ 3 → ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      paramIteratedDeriv A (fun i => Pi.single (l i) 1) 0 η = OA j l η) :
    |iteratedFDeriv ℝ k (fun s => gibbsMean μ (A s) (H s)) 0 (fun l => Pi.single l 1)| ≤
      (Cq 1 + 7 * (T * sizeConstantSum Cq 2 ^ 2) + 6 * (T * sizeConstantSum Cq 3 ^ 3) +
        T * sizeConstantSum Cq 4 ^ 4) * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c)) := by
  have hE0 : 0 ≤ Real.exp (-(κ / 2 ^ 6 * bondSpan Y c)) := (Real.exp_pos _).le
  set K₂ := T * sizeConstantSum Cq 2 ^ 2 with hK₂
  set K₃ := T * sizeConstantSum Cq 3 ^ 3 with hK₃
  set K₄ := T * sizeConstantSum Cq 4 ^ 4 with hK₄
  have hK₂0 : 0 ≤ K₂ * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c)) := by positivity
  have hK₃0 : 0 ≤ K₃ * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c)) := by positivity
  have hK₄0 : 0 ≤ K₄ * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c)) := by positivity
  have hq0 : 0 ≤ Cq 1 * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c)) := by positivity
  have hForm := (hDer _ μ k B Mb A H hBo hμ0 hdA hdH).2 0 hB0
  have dH0 : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → H 0 η = OH 0 Fin.elim0 η := by
    intro η hη
    have := dH 0 Fin.elim0 (by norm_num) η hη
    simpa [paramIteratedDeriv] using this
  have dH1 : ∀ a : Fin k, ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      paramIteratedDeriv H ![Pi.single a 1] 0 η = OH 1 ![a] η := fun a η hη => by
    rw [basisVectors_one]
    exact dH 1 ![a] (by norm_num) η hη
  have dH2 : ∀ a b : Fin k, ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      paramIteratedDeriv H ![Pi.single a 1, Pi.single b 1] 0 η = OH 2 ![a, b] η := fun a b η hη => by
    rw [basisVectors_two]
    exact dH 2 ![a, b] (by norm_num) η hη
  have dH3 : ∀ a b c : Fin k, ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      paramIteratedDeriv H ![Pi.single a 1, Pi.single b 1, Pi.single c 1] 0 η = OH 3 ![a, b, c] η :=
    fun a b c η hη => by
    rw [basisVectors_three]
    exact dH 3 ![a, b, c] (by norm_num) η hη
  have dA1 : ∀ a : Fin k, ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      paramIteratedDeriv A ![Pi.single a 1] 0 η = OA 0 ![a] η := fun a η hη => by
    rw [basisVectors_one]
    exact dA 0 ![a] (by norm_num) η hη
  have dA2 : ∀ a b : Fin k, ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      paramIteratedDeriv A ![Pi.single a 1, Pi.single b 1] 0 η = OA 1 ![a, b] η := fun a b η hη => by
    rw [basisVectors_two]
    exact dA 1 ![a, b] (by norm_num) η hη
  have dA3 : ∀ a b c : Fin k, ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      paramIteratedDeriv A ![Pi.single a 1, Pi.single b 1, Pi.single c 1] 0 η = OA 2 ![a, b, c] η :=
    fun a b c η hη => by
    rw [basisVectors_three]
    exact dA 2 ![a, b, c] (by norm_num) η hη
  obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  · rw [iteratedFDeriv_zero_apply]
    have t := gibbsMean_le hκ hS hq hm Fin.elim0 (by norm_num) dH0 (fun i => i.elim0)
    refine t.trans ?_
    rw [add_mul, add_mul, add_mul]
    linarith
  · have hvec : (fun l : Fin 1 => (Pi.single l 1 : Fin 1 → ℝ)) = ![Pi.single 0 1] := by
      funext i
      fin_cases i
      rfl
    rw [hvec, (hForm (Pi.single 0 1) (Pi.single 0 1) (Pi.single 0 1)).1]
    have t1 := gibbsMean_le hκ hS hq hm ![0] (by norm_num) (dH1 0) (by decide)
    have t2 := gibbsCovariance_le hExp hκ hS hT hc2 hm Fin.elim0 ![0] (by norm_num) (by norm_num) dH0 (dA1 0)
      (by decide)
    obtain ⟨a1, b1⟩ := abs_le.mp t1
    obtain ⟨a2, b2⟩ := abs_le.mp t2
    rw [abs_le, add_mul, add_mul, add_mul]
    constructor <;> linarith
  · have hvec : (fun l : Fin 2 => (Pi.single l 1 : Fin 2 → ℝ)) = ![Pi.single 0 1, Pi.single 1 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hvec, (hForm (Pi.single 1 1) (Pi.single 0 1) (Pi.single 0 1)).2.1]
    have t1 := gibbsMean_le hκ hS hq hm ![0, 1] (by norm_num) (dH2 0 1) (by decide)
    have t2 := gibbsCovariance_le hExp hκ hS hT hc2 hm ![1] ![0] (by norm_num) (by norm_num) (dH1 1) (dA1 0)
      (by decide)
    have t3 := gibbsCovariance_le hExp hκ hS hT hc2 hm ![0] ![1] (by norm_num) (by norm_num) (dH1 0) (dA1 1)
      (by decide)
    have t4 := gibbsCovariance_le hExp hκ hS hT hc2 hm Fin.elim0 ![0, 1] (by norm_num) (by norm_num) dH0
      (dA2 0 1) (by decide)
    have t5 := gibbsCumulantThree_le hExp hκ hS hT hc3 hm Fin.elim0 ![1] ![0] (by norm_num) (by norm_num)
      (by norm_num) dH0 (dA1 1) (dA1 0) (by decide)
    obtain ⟨a1, b1⟩ := abs_le.mp t1
    obtain ⟨a2, b2⟩ := abs_le.mp t2
    obtain ⟨a3, b3⟩ := abs_le.mp t3
    obtain ⟨a4, b4⟩ := abs_le.mp t4
    obtain ⟨a5, b5⟩ := abs_le.mp t5
    rw [abs_le, add_mul, add_mul, add_mul]
    constructor <;> linarith
  · have hvec : (fun l : Fin 3 => (Pi.single l 1 : Fin 3 → ℝ)) =
        ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hvec, (hForm (Pi.single 2 1) (Pi.single 1 1) (Pi.single 0 1)).2.2]
    have t1 := gibbsMean_le hκ hS hq hm ![0, 1, 2] (by norm_num) (dH3 0 1 2) (by decide)
    have t2 := gibbsCovariance_le hExp hκ hS hT hc2 hm ![1, 2] ![0] (by norm_num) (by norm_num) (dH2 1 2)
      (dA1 0) (by decide)
    have t3 := gibbsCovariance_le hExp hκ hS hT hc2 hm ![0, 2] ![1] (by norm_num) (by norm_num) (dH2 0 2)
      (dA1 1) (by decide)
    have t4 := gibbsCovariance_le hExp hκ hS hT hc2 hm ![0, 1] ![2] (by norm_num) (by norm_num) (dH2 0 1)
      (dA1 2) (by decide)
    have t5 := gibbsCovariance_le hExp hκ hS hT hc2 hm ![2] ![0, 1] (by norm_num) (by norm_num) (dH1 2)
      (dA2 0 1) (by decide)
    have t6 := gibbsCovariance_le hExp hκ hS hT hc2 hm ![1] ![0, 2] (by norm_num) (by norm_num) (dH1 1)
      (dA2 0 2) (by decide)
    have t7 := gibbsCovariance_le hExp hκ hS hT hc2 hm ![0] ![1, 2] (by norm_num) (by norm_num) (dH1 0)
      (dA2 1 2) (by decide)
    have t8 := gibbsCumulantThree_le hExp hκ hS hT hc3 hm ![2] ![1] ![0] (by norm_num) (by norm_num)
      (by norm_num) (dH1 2) (dA1 1) (dA1 0) (by decide)
    have t9 := gibbsCumulantThree_le hExp hκ hS hT hc3 hm ![1] ![2] ![0] (by norm_num) (by norm_num)
      (by norm_num) (dH1 1) (dA1 2) (dA1 0) (by decide)
    have t10 := gibbsCumulantThree_le hExp hκ hS hT hc3 hm ![0] ![2] ![1] (by norm_num) (by norm_num)
      (by norm_num) (dH1 0) (dA1 2) (dA1 1) (by decide)
    have t11 := gibbsCovariance_le hExp hκ hS hT hc2 hm Fin.elim0 ![0, 1, 2] (by norm_num) (by norm_num) dH0
      (dA3 0 1 2) (by decide)
    have t12 := gibbsCumulantThree_le hExp hκ hS hT hc3 hm Fin.elim0 ![1, 2] ![0] (by norm_num) (by norm_num)
      (by norm_num) dH0 (dA2 1 2) (dA1 0) (by decide)
    have t13 := gibbsCumulantThree_le hExp hκ hS hT hc3 hm Fin.elim0 ![0, 2] ![1] (by norm_num) (by norm_num)
      (by norm_num) dH0 (dA2 0 2) (dA1 1) (by decide)
    have t14 := gibbsCumulantThree_le hExp hκ hS hT hc3 hm Fin.elim0 ![0, 1] ![2] (by norm_num) (by norm_num)
      (by norm_num) dH0 (dA2 0 1) (dA1 2) (by decide)
    have t15 := gibbsCumulantFour_le hExp hκ hS hT hc4 hm Fin.elim0 ![2] ![1] ![0] (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) dH0 (dA1 2) (dA1 1) (dA1 0) (by decide)
    obtain ⟨a1, b1⟩ := abs_le.mp t1
    obtain ⟨a2, b2⟩ := abs_le.mp t2
    obtain ⟨a3, b3⟩ := abs_le.mp t3
    obtain ⟨a4, b4⟩ := abs_le.mp t4
    obtain ⟨a5, b5⟩ := abs_le.mp t5
    obtain ⟨a6, b6⟩ := abs_le.mp t6
    obtain ⟨a7, b7⟩ := abs_le.mp t7
    obtain ⟨a8, b8⟩ := abs_le.mp t8
    obtain ⟨a9, b9⟩ := abs_le.mp t9
    obtain ⟨a10, b10⟩ := abs_le.mp t10
    obtain ⟨a11, b11⟩ := abs_le.mp t11
    obtain ⟨a12, b12⟩ := abs_le.mp t12
    obtain ⟨a13, b13⟩ := abs_le.mp t13
    obtain ⟨a14, b14⟩ := abs_le.mp t14
    obtain ⟨a15, b15⟩ := abs_le.mp t15
    rw [abs_le, add_mul, add_mul, add_mul]
    constructor <;> linarith
end Main
end PartMeanDeriv
open PartMeanDeriv in
theorem partMeanDerivBound (hCum : cumulantDecayBound)
    (hExp : lowOrderCumulantFormulas) (hDer : GibbsMeanDifferentiation)
    (hRim : CutoffMeanIsGibbsMean) (hLaw : normalizedBallLawIsProbabilityStatement) :
    partMeanDerivBoundStatement := by
  intro N κ lam Cq hκ hlam hCq
  obtain ⟨T, hT, hTb⟩ := hCum N κ lam hκ hlam
  have hc : ∀ M, 0 ≤ sizeConstantSum Cq M := fun M => by
    unfold sizeConstantSum
    have : 0 ≤ ∑ q ∈ Finset.range (2 * M + 1), Cq q := Finset.sum_nonneg fun q _ => hCq q
    linarith
  refine ⟨Cq 1 + 7 * (T * sizeConstantSum Cq 2 ^ 2) + 6 * (T * sizeConstantSum Cq 3 ^ 3) +
    T * sizeConstantSum Cq 4 ^ 4, ?_, ?_⟩
  · have h1 := hCq 1
    have h3 := hc 3
    positivity
  intro F ρ x v p ψ V Ψ K Y k c X A H B Mb hρ hx hcut hv0 hv1 hk hfew hconv hslope hBo hB0 hdA hdH hfam hsz
  obtain ⟨hfin, hμ0, hμb, hμm⟩ := hRim F ρ p hρ hcut
  have := hfin
  have hm : ∀ g, gibbsMean (cutoffLaw F ρ p) (A 0) g = ballExpectation (cutoffFactor ρ p) Ψ g := fun g =>
    (hμm _ _).symm.trans (cutoffMean_eq_ballExpectation hfam.eq_potential g)
  have hcum := hTb F ↥(chordBonds (finiteCells F)) (fun b => enclosingCell b.1.1) ρ x p Ψ K hρ hx hcut hfew
    hconv hslope
  have hΨc : Continuous Ψ := hconv.smooth.continuous
  obtain ⟨hprob, hmeanI, -, -, -, -, -, -, -, -, -⟩ := hLaw _ ρ p Ψ hρ hcut hΨc
  have hS : SizedDerivatives ρ x κ T p Cq Ψ Y c
      (fun j l => partCentredDeriv ψ lam x Y V (c ∘ l) (X ∘ l))
      (fun j l η => v * exponentDerivSum ψ V (c ∘ l) (X ∘ l) η) := by
    refine ⟨fun M H Z h hM2 hM9 hsm hh hsz' => ?_, fun j l hj => (hsz j l hj).smooth_centred,
      fun j l hj => contDiffOn_const.mul (hsz (j + 1) l hj).smooth_sum,
      fun j l hj => (hsz j l hj).size_centred,
      fun j l hj => (hsz (j + 1) l hj).size_sum v 0 hv0 hv1, fun j l hj => ?_⟩
    · exact (hcum M H Z h (fun _ => Cq) hM2 hM9 hsm hh (fun _ q => hCq q) hsz').2
    · have hmom := (hsz j l hj).moment_centred
      have h1 := hmom.2
      simp only [pow_one] at h1
      rw [← hmeanI] at h1
      rw [← hmeanI]
      exact (abs_integral_le_integral_abs).trans h1
  exact iteratedFDeriv_mean_le_of_sized hExp hDer.2 hκ hS hT (hCq 1) (hc 2) (hc 3) (hc 4) hk hBo hB0 hμ0 hdA hdH hm
    (fun j l hj η hη => hfam.deriv_observable j l hj η hη) (fun j l hj η hη => hfam.deriv_exponent j l hj η hη)
end Interpolation
end YangMills.Construction
end
