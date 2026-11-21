import YangMills.Construction.ColdStepAtMirrorFrames.ResponsesNearAFlatTopProof
import YangMills.Construction.ColdStepAtMirrorFrames.EmbeddedVariables
import YangMills.Construction.ColdStepAtMirrorFrames.EnergiesCompareOnPairedVariables
import YangMills.Construction.ColdStepAtMirrorFrames.ExponentsFromSlopesProof
import YangMills.Construction.ColdStepAtMirrorFrames.LieCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsOfATorus
import YangMills.Construction.ColdStepAtMirrorFrames.RayOfSlopesIsSmooth
import YangMills.Construction.ColdStepAtMirrorFrames.SlopesBetweenCompare
import YangMills.Construction.ColdStepAtMirrorFrames.WeightsOfATorus
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeBetweenComparesOnTwoToriProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages Interpolation
namespace ColdStepAtMirrorFrames
variable {F F' : BlockFrame}
private theorem value_bound_arith {Ct C S R x Q S₁ S₂ A b : ℝ} (hR0 : 0 ≤ R) (hR1 : R ≤ 1) (hCt : 1 ≤ Ct)
    (hC : 0 ≤ C) (hS : 1 ≤ S) (hM : (18 * C * S ^ 2 + 3 * S) * R ≤ 1) (hx : 0 ≤ x) (hQ : 0 ≤ Q)
    (h₁ : 0 ≤ S₁) (h₂ : 0 ≤ S₂) (hA : A ≤ 6 * C * R ^ 256) (hb : b ≤ Ct * R ^ 256)
    (hRS : R * S₁ ≤ S) (hSS : (R ^ 33 * S₁) * (R ^ 33 * S₂) ≤ S ^ 2 * Q) :
    b * S₁ + x * (A * S₁ * S₂) ≤ Ct / 3 * R ^ 4 * (x * Q + 1) := by
  have hu : 0 ≤ 18 * C * S ^ 2 * R := by positivity
  have hv : 0 ≤ 3 * S * R := by positivity
  have e1 : 3 * S * R ≤ 1 := by linarith
  have e2 : 18 * C * S ^ 2 * R ≤ 1 := by linarith
  have hCt0 : 0 ≤ Ct := by linarith
  have p250 : R ^ 250 ≤ 1 := pow_le_one₀ hR0 hR1
  have p185 : R ^ 185 ≤ 1 := pow_le_one₀ hR0 hR1
  have t1 : b * S₁ ≤ Ct / 3 * R ^ 4 := by
    calc b * S₁ ≤ (Ct * R ^ 256) * S₁ := mul_le_mul_of_nonneg_right hb h₁
      _ = Ct * R ^ 255 * (R * S₁) := by ring
      _ ≤ Ct * R ^ 255 * S := mul_le_mul_of_nonneg_left hRS (mul_nonneg hCt0 (pow_nonneg hR0 _))
      _ = Ct / 3 * R ^ 4 * ((3 * S * R) * R ^ 250) := by ring
      _ ≤ Ct / 3 * R ^ 4 * (1 * 1) := by gcongr
      _ = Ct / 3 * R ^ 4 := by ring
  have t2 : A * S₁ * S₂ ≤ Ct / 3 * R ^ 4 * Q := by
    calc A * S₁ * S₂ ≤ (6 * C * R ^ 256) * S₁ * S₂ := by gcongr
      _ = 6 * C * R ^ 190 * ((R ^ 33 * S₁) * (R ^ 33 * S₂)) := by ring
      _ ≤ 6 * C * R ^ 190 * (S ^ 2 * Q) :=
        mul_le_mul_of_nonneg_left hSS (mul_nonneg (by positivity) (pow_nonneg hR0 _))
      _ = 1 / 3 * R ^ 4 * Q * ((18 * C * S ^ 2 * R) * R ^ 185) := by ring
      _ ≤ 1 / 3 * R ^ 4 * Q * (1 * 1) := by gcongr
      _ = 1 * (1 / 3 * R ^ 4 * Q) := by ring
      _ ≤ Ct * (1 / 3 * R ^ 4 * Q) := by gcongr
      _ = Ct / 3 * R ^ 4 * Q := by ring
  have t3 : x * (A * S₁ * S₂) ≤ x * (Ct / 3 * R ^ 4 * Q) := mul_le_mul_of_nonneg_left t2 hx
  calc b * S₁ + x * (A * S₁ * S₂) ≤ Ct / 3 * R ^ 4 + x * (Ct / 3 * R ^ 4 * Q) := add_le_add t1 t3
    _ = Ct / 3 * R ^ 4 * (x * Q + 1) := by ring
private theorem gradient_bound_arith {Ct C S R x y S₁ S₂ A b E : ℝ} (hR0 : 0 ≤ R) (hR1 : R ≤ 1) (hCt : 1 ≤ Ct)
    (hC : 0 ≤ C) (hS : 1 ≤ S) (hM : (36 * C * S + 3) * R ≤ 1) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h₁ : 0 ≤ S₁) (h₂ : 0 ≤ S₂) (hA : A ≤ 6 * C * R ^ 256) (hb : b ≤ Ct * R ^ 256)
    (hR₁ : R ^ 33 * S₁ ≤ S * y) (hR₂ : R ^ 33 * S₂ ≤ S * y) (hE : R ^ 4 ≤ E) :
    b + x * (A * S₂) + x * (A * S₁) ≤ Ct / 3 * R ^ 4 * (x * y + 1) * E := by
  have hu : 0 ≤ 36 * C * S * R := by positivity
  have e1 : 3 * R ≤ 1 := by linarith
  have e2 : 36 * C * S * R ≤ 1 := by linarith
  have p247 : R ^ 247 ≤ 1 := pow_le_one₀ hR0 hR1
  have p214 : R ^ 214 ≤ 1 := pow_le_one₀ hR0 hR1
  have t1 : b ≤ Ct / 3 * R ^ 8 := by
    calc b ≤ Ct * R ^ 256 := hb
      _ = Ct / 3 * R ^ 8 * ((3 * R) * R ^ 247) := by ring
      _ ≤ Ct / 3 * R ^ 8 * (1 * 1) := by gcongr
      _ = Ct / 3 * R ^ 8 := by ring
  have t2 : ∀ u : ℝ, 0 ≤ u → R ^ 33 * u ≤ S * y → A * u ≤ 6 * C * R ^ 223 * (S * y) := fun u hu0 hu1 => by
    calc A * u ≤ (6 * C * R ^ 256) * u := by gcongr
      _ = 6 * C * R ^ 223 * (R ^ 33 * u) := by ring
      _ ≤ 6 * C * R ^ 223 * (S * y) :=
        mul_le_mul_of_nonneg_left hu1 (mul_nonneg (by positivity) (pow_nonneg hR0 _))
  have t3 : x * (A * S₂) + x * (A * S₁) ≤ x * (12 * C * R ^ 223 * (S * y)) := by
    have a1 := mul_le_mul_of_nonneg_left (t2 S₂ h₂ hR₂) hx
    have a2 := mul_le_mul_of_nonneg_left (t2 S₁ h₁ hR₁) hx
    nlinarith
  have t4 : x * (12 * C * R ^ 223 * (S * y)) ≤ Ct / 3 * R ^ 8 * (x * y) := by
    calc x * (12 * C * R ^ 223 * (S * y)) = 1 / 3 * R ^ 8 * (x * y) * ((36 * C * S * R) * R ^ 214) := by ring
      _ ≤ 1 / 3 * R ^ 8 * (x * y) * (1 * 1) := by gcongr
      _ = 1 * (1 / 3 * R ^ 8 * (x * y)) := by ring
      _ ≤ Ct * (1 / 3 * R ^ 8 * (x * y)) := by gcongr
      _ = Ct / 3 * R ^ 8 * (x * y) := by ring
  calc b + x * (A * S₂) + x * (A * S₁) ≤ Ct / 3 * R ^ 8 + Ct / 3 * R ^ 8 * (x * y) := by linarith
    _ = Ct / 3 * R ^ 4 * (x * y + 1) * R ^ 4 := by ring
    _ ≤ Ct / 3 * R ^ 4 * (x * y + 1) * E := by gcongr
private theorem chartedSlope_zero (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (b : F.Site F.depth × Fin 4) : chartedSlope a w V b 0 = 0 := by
  simp [chartedSlope]
private theorem pushforwardField_zero {ι β : Type} [Fintype ι] [DecidableEq β] (j : ι → β) :
    pushforwardField j (0 : BondField ι) = 0 := by
  funext b
  simp [pushforwardField]
private theorem bondPartialDeriv_smul {ι : Type} [Fintype ι] [DecidableEq ι] (g : BondField ι → ℝ) (k : ι)
    (ξ : BondField ι) (c : ℝ) (e : BondVector) : bondPartialDeriv g k ξ (c • e) = c * bondPartialDeriv g k ξ e := by
  unfold bondPartialDeriv bondVariation
  rw [Pi.single_smul, map_smul, smul_eq_mul]
private theorem sum_ite_eq_sum_image {β ι : Type} [Fintype β] [DecidableEq β] {P : β → Prop}
    [∀ b, Decidable (P b)] (B : Finset ι) (j : ι → β) (hj : Function.Injective j)
    (hB : ∀ k ∈ B, P (j k)) (f : β → ℝ) (hf : ∀ b, P b → (∀ k ∈ B, j k ≠ b) → f b = 0) :
    (∑ b, if P b then f b else 0) = ∑ k ∈ B, f (j k) := by
  calc (∑ b, if P b then f b else 0) = ∑ b ∈ B.image j, if P b then f b else 0 := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun b _ hb => ?_).symm
        split_ifs with h
        · exact hf b h fun k hk e => hb (Finset.mem_image.2 ⟨k, hk, e⟩)
        · rfl
    _ = ∑ k ∈ B, (if P (j k) then f (j k) else 0) := Finset.sum_image fun _ _ _ _ h => hj h
    _ = ∑ k ∈ B, f (j k) := Finset.sum_congr rfl fun k hk => if_pos (hB k hk)
private theorem interpolatedSlopePart_eq (hE : PushforwardFieldProperties) (hLC : ImaginaryCoordinatesIsometric) {ι : Type}
    [Fintype ι] [DecidableEq ι] {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j)
    {z : F.Cell} {B : Finset ι} (hB : ∀ k, k ∈ B ↔ enclosingCell (j k).1.1 = z) {s a ρA x ρ : ℝ} {m : ℕ}
    {V : F.GaugeField F.top} {g : BondField ι → ℝ}
    (hsl : ∀ ζ ∈ openPolyball ι ρ, ∀ (k : ι) (u : BondVector),
      chartedSlope a (shiftCoordinates (fun y i => interpolatedFrame s a ρA m (y, i) V) (pushforwardField j ζ)) V (j k).1 (toImaginary u) =
        bondPartialDeriv g k ζ u)
    {ξ : BondField ι} (hξ : ξ ∈ openPolyball ι ρ) :
    interpolatedSlopePart s a ρA x m z V (pushforwardField j ξ) = x * radialSlopeIntegral B g ξ := by
  obtain ⟨_, hsm, _, hval, hoff, _⟩ := hE _ _ j hj
  have hlie : toImaginary (0 : BondVector) = 0 := by
    have := hLC.2.1 0 (0 : BondVector)
    simpa using this
  have hball : ∀ v ∈ Set.Icc (0 : ℝ) 1, v • ξ ∈ openPolyball ι ρ := fun v hv b => by
    have h1 : ‖(v • ξ) b‖ = |v| * ‖ξ b‖ := by simp [norm_smul]
    have h2 : |v| ≤ 1 := by rw [abs_of_nonneg hv.1]; exact hv.2
    have h3 := hξ b
    rw [h1]
    nlinarith [norm_nonneg (ξ b), abs_nonneg v]
  unfold interpolatedSlopePart radialSlopeIntegral
  congr 1
  refine (sum_ite_eq_sum_image (P := fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z) B j hj
    (fun k hk => (hB k).1 hk) _ fun b hb hne => ?_).trans ?_
  · have h0 : pushforwardField j ξ b = 0 := hoff ξ b fun k hk => hne k ((hB k).2 (by rw [hk]; exact hb)) hk
    simp only [h0, hlie, chartedSlope_zero]
    simp
  · refine Finset.sum_congr rfl fun k _ => intervalIntegral.integral_congr fun v hv => ?_
    have hv' : v ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le zero_le_one] at hv
      exact hv
    have := hsl (v • ξ) (hball v hv') k (ξ k)
    rw [hsm] at this
    show chartedSlope a (interpolatedCoords s a ρA m V (v • pushforwardField j ξ)) V (j k).1 (toImaginary (pushforwardField j ξ (j k))) = _
    rw [hval]
    exact this
private theorem isAdmissibleChartPoint_of_shift (hSh : ChartLipschitz.ChartedFieldLipschitz) (hLC : ImaginaryCoordinatesIsometric) {L : ℕ}
    {s₀ B τ σc : ℝ} {G : BlockFrame} {U : G.GaugeField G.top} {w : G.Site G.depth → Fin 4 → imaginaryQuaternions}
    (hsz : ∀ b ∈ chordBonds (finiteCells G), ‖w b.1 b.2‖ ≤ B)
    (hcold : IsSmallCurvature σc (chartedField w U)) (hτ : 0 ≤ τ) (hB : B + τ ≤ 1 / (64 * (L : ℝ)))
    (hc : σc + 4 * τ ≤ s₀) {Δ : StepVariable (finiteCells G)} (hΔ : ∀ b, ‖Δ b‖ ≤ τ) :
    IsAdmissibleChartPoint L s₀ (shiftCoordinates w Δ) U := by
  have hco : ∀ z i, ‖stepCoordinates Δ z i‖ ≤ τ := by
    intro z i
    unfold stepCoordinates
    split_ifs with h
    · rw [hLC.2.2.1]
      exact hΔ _
    · simpa using hτ
  refine ⟨fun b hb => ?_, fun p hp => ?_⟩
  · show ‖w b.1 b.2 + stepCoordinates Δ b.1 b.2‖ ≤ _
    exact (norm_add_le _ _).trans ((add_le_add (hsz b hb) (hco _ _)).trans hB)
  · have h1 := (hSh.2 G (shiftCoordinates w Δ) w U τ (fun z i => by
      show ‖w z i + stepCoordinates Δ z i - w z i‖ ≤ τ
      rw [add_sub_cancel_left]
      exact hco z i) hτ).2 p
    have h2 := hcold p hp
    linarith
private theorem norm_pushforwardField_le (hE : PushforwardFieldProperties) {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β] {j : ι → β} (hj : Function.Injective j) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {ξ : BondField ι} (hξ : ξ ∈ openPolyball ι ρ) (b : β) : ‖pushforwardField j ξ b‖ ≤ ρ := by
  obtain ⟨_, _, _, hval, hoff, _⟩ := hE _ _ j hj
  by_cases h : ∃ k, j k = b
  · obtain ⟨k, rfl⟩ := h
    rw [hval]
    exact (hξ k).le
  · rw [hoff ξ b (not_exists.1 h)]
    simpa using hρ
private theorem sup_natAbs_le_of_withinRadius {r : ℕ} {h : Fin 4 → ℤ} (hh : WithinRadius r h) :
    (Finset.univ.sup fun i => (h i).natAbs) ≤ r := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NearUniformTop.offsetSupNorm_le_of_withinRadius <;> assumption
private theorem isFineBondInBox_of_withinRadius (hO : TorusOffsetsAboutCell) {Y : F.Cell} {q r r' : ℕ} (hodd : Odd F.blockSide)
    (hs : ∀ i, 2 * q + 2 < F.extent i) (hr : r + 1 ≤ r') (hrq : r' ≤ q) {h o : Fin 4 → ℤ} {i : Fin 4}
    (hh : WithinRadius r h) (ho : o ∈ centredCube F.blockSide) (hb : fineBondAt Y h o i ∈ chordBonds (finiteCells F)) :
    IsFineBondWithinRadius Y r' h o i := by
  obtain ⟨c1, _, c3, _, _, c6, c7, _⟩ := hO F q Y hodd hs
  have hq : WithinRadius q h := fun l => (hh l).trans (by exact_mod_cast (by omega : r ≤ q))
  have d := c3 h hq
  have e := (c1 h o i ho).1
  have hd1 : cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) ≤ r := by
    rw [e, d.2]
    exact sup_natAbs_le_of_withinRadius hh
  unfold IsFineBondWithinRadius
  refine ⟨ho, hb, fun l => (hh l).trans (by exact_mod_cast (by omega : r ≤ r')), by omega, ?_⟩
  have h6 := c6 (fineBondAt Y h o i).1 i
  rw [c7] at hd1 ⊢
  omega
private theorem offset_eq_of_site_eq (hO : TorusOffsetsAboutCell) {Y : F.Cell} {q : ℕ} (hodd : Odd F.blockSide)
    (hs : ∀ i, 2 * q + 2 < F.extent i) {g o u : Fin 4 → ℤ} (hg : WithinRadius q g) (ho : WithinRadius q o)
    (hu : u ∈ centredCube F.blockSide) (e : Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top g = Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) : g = o := by
  obtain ⟨_, c2, _⟩ := hO F q Y hodd hs
  have : (fineBondAt Y g u 0).1 = (fineBondAt Y o u 0).1 := by
    simp only [fineBondAt]
    rw [e]
  exact (c2 g o u u 0 0 hg ho hu hu this).1
private theorem agreeOnBall_mono {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell}
    {q r : ℕ} (h : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q) (hr : r ≤ q) :
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r := by apply _root_.YangMills.SharedProofs.p37458 <;> assumption
private def PairedEnergyBoundsAt (a : ℝ) (L : ℕ) (c : ColdChainParameters) (C : ℝ) : Prop :=
  ∀ (F F' : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (q r₂ : ℕ) (θ ρ₂ : ℝ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (j : ι → ↥(chordBonds (finiteCells F))) (j' : ι → ↥(chordBonds (finiteCells F'))),
    IsBlockTorus L F → IsBlockTorus L F' → F'.depth = F.depth →
    0 ≤ θ → 0 < ρ₂ → 1 ≤ r₂ → r₂ ≤ q → (∀ i, 2 * q + 2 < F.extent i) → (∀ i, 2 * q + 2 < F'.extent i) →
    Function.Injective j → Function.Injective j' → AreOffsetPaired Y Y' q j j' →
    (∀ ξ ∈ openPolyball ι ρ₂, ∀ Δ : StepVariable (finiteCells F), (∀ b, ‖Δ b‖ ≤ θ) →
      IsAdmissibleChartPoint L c.s₀ (shiftCoordinates (shiftCoordinates w (pushforwardField j ξ)) Δ) V) →
    (∀ ξ ∈ openPolyball ι ρ₂, IsAdmissibleChartPoint L c.s₀ (shiftCoordinates w' (pushforwardField j' ξ)) V') →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r₂ → CoordinatesCloseOnBall L Y Y' r₂ θ w w' →
    ContDiffOn ℝ 3 (fun ξ => chartedEnergyAt a w V (pushforwardField j ξ)) (openPolyball ι ρ₂) ∧
    ContDiffOn ℝ 3 (fun ξ => chartedEnergyAt a w' V' (pushforwardField j' ξ)) (openPolyball ι ρ₂) ∧
    (∀ ξ ∈ openPolyball ι ρ₂, ∀ (k : ι) (u : BondVector),
      chartedSlope a (shiftCoordinates w (pushforwardField j ξ)) V (j k).1 (toImaginary u) =
        bondPartialDeriv (fun ξ => chartedEnergyAt a w V (pushforwardField j ξ)) k ξ u ∧
      chartedSlope a (shiftCoordinates w' (pushforwardField j' ξ)) V' (j' k).1 (toImaginary u) =
        bondPartialDeriv (fun ξ => chartedEnergyAt a w' V' (pushforwardField j' ξ)) k ξ u) ∧
    ∀ (ρ₁ hh : ℝ), 0 < hh → 0 < ρ₁ → ρ₁ + hh ≤ ρ₂ → ∀ ξ ∈ openPolyball ι ρ₁,
      ∀ (k l : ι) (h o : Fin 4 → ℤ) (i : Fin 4) (u u' : BondVector),
        IsFineBondWithinRadius Y (r₂ / 2) h o i → (j k).1 = fineBondAt Y h o i → (j' k).1 = fineBondAt Y' h o i →
        |secondDerivAlong (fun ξ => chartedEnergyAt a w' V' (pushforwardField j' ξ)) ξ (bondVariation k u) (bondVariation l u') -
          secondDerivAlong (fun ξ => chartedEnergyAt a w V (pushforwardField j ξ)) ξ (bondVariation k u) (bondVariation l u')| ≤
          (2 * (C * (θ + Real.exp (-(c.δ₂ * ((L : ℝ) * ((r₂ : ℝ) / 2) - 2 * L - 1))))) / hh + 2 * C * hh) *
            ‖u‖ * ‖u'‖
private theorem exp_radius_bounds {δ κ C R : ℝ} {L q r₂ : ℕ} (hδ : 0 < δ) (_hκ0 : 0 < κ) (hκ : κ ≤ δ / 2 ^ 16)
    (hC : 0 < C) (hL : 2 ^ 40 ≤ L) (hq : 64 ≤ q) (hr : r₂ = q - q / 8) (hR : R = Real.exp (-(κ * q))) :
    Real.exp (-(δ / 2 ^ 8 * q)) ≤ R ^ 256 ∧
    Real.exp (-(δ / 2 ^ 6 * q)) ≤ Real.exp (-(δ / 2 ^ 8 * q)) * Real.exp (-(δ / 2 ^ 8 * q)) ∧
    (2 * (C * (Real.exp (-(δ / 2 ^ 6 * q)) + Real.exp (-(δ * ((L : ℝ) * ((r₂ : ℝ) / 2) - 2 * L - 1)))))) /
        Real.exp (-(δ / 2 ^ 8 * q)) + 2 * C * Real.exp (-(δ / 2 ^ 8 * q)) ≤ 6 * C * R ^ 256 := by
  set hh := Real.exp (-(δ / 2 ^ 8 * q)) with hhh
  set θ := Real.exp (-(δ / 2 ^ 6 * q)) with hθ
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hq64 : (64 : ℝ) ≤ q := by exact_mod_cast hq
  have hhpos : 0 < hh := Real.exp_pos _
  have h1 : hh ≤ R ^ 256 := by
    rw [hR, ← Real.exp_nat_mul, hhh]
    refine Real.exp_le_exp.2 ?_
    have : 2 ^ 8 * (κ * q) ≤ δ / 2 ^ 8 * q := by
      have : 2 ^ 8 * κ ≤ δ / 2 ^ 8 := by
        have := mul_le_mul_of_nonneg_left hκ (by norm_num : (0 : ℝ) ≤ 2 ^ 8)
        calc 2 ^ 8 * κ ≤ 2 ^ 8 * (δ / 2 ^ 16) := this
          _ = δ / 2 ^ 8 := by ring
      calc 2 ^ 8 * (κ * q) = (2 ^ 8 * κ) * q := by ring
        _ ≤ δ / 2 ^ 8 * q := mul_le_mul_of_nonneg_right this hq0
    push_cast
    linarith
  have h2 : θ ≤ hh * hh := by
    rw [hθ, hhh, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_nonneg hδ.le hq0]
  have hr₂ : (7 : ℝ) / 8 * q ≤ r₂ := by
    have : 7 * q ≤ 8 * r₂ := by omega
    have h' : (7 : ℝ) * q ≤ 8 * r₂ := by exact_mod_cast this
    linarith
  have hL' : (2 : ℝ) ^ 40 ≤ L := by exact_mod_cast hL
  have h3 : Real.exp (-(δ * ((L : ℝ) * ((r₂ : ℝ) / 2) - 2 * L - 1))) ≤ θ := by
    rw [hθ]
    refine Real.exp_le_exp.2 ?_
    have a1 : (q : ℝ) / 4 ≤ (r₂ : ℝ) / 2 - 2 := by linarith
    have a2 : (L : ℝ) * ((q : ℝ) / 4) ≤ (L : ℝ) * ((r₂ : ℝ) / 2 - 2) :=
      mul_le_mul_of_nonneg_left a1 (Nat.cast_nonneg _)
    have a3 : (8 : ℝ) * ((q : ℝ) / 4) ≤ (L : ℝ) * ((q : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right (by norm_num at hL' ⊢; linarith) (by positivity)
    have a4 : (q : ℝ) / 2 ^ 6 ≤ (L : ℝ) * ((r₂ : ℝ) / 2) - 2 * L - 1 := by
      norm_num at a2 a3 ⊢
      nlinarith
    have := mul_le_mul_of_nonneg_left a4 hδ.le
    linarith
  refine ⟨h1, h2, ?_⟩
  have h4 : (2 * (C * (θ + Real.exp (-(δ * ((L : ℝ) * ((r₂ : ℝ) / 2) - 2 * L - 1)))))) / hh ≤ 4 * C * hh := by
    rw [div_le_iff₀ hhpos]
    have : θ + Real.exp (-(δ * ((L : ℝ) * ((r₂ : ℝ) / 2) - 2 * L - 1))) ≤ 2 * (hh * hh) := by linarith
    have := mul_le_mul_of_nonneg_left this hC.le
    nlinarith
  have h5 : 6 * C * hh ≤ 6 * C * R ^ 256 := mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith
private theorem tail_bounds {ι : Type} [Fintype ι] [DecidableEq ι] {G : BlockFrame}
    {j : ι → ↥(chordBonds (finiteCells G))} {z : G.Cell} {B : Finset ι} {ρ κ x B₀ A C S Ct R : ℝ} {q : ℕ}
    {Dv : BondField ι → ℝ} (hκ0 : 0 < κ) (hρ1 : ρ ≤ 1) (hR : R = Real.exp (-(κ * q))) (hR0 : 0 ≤ R)
    (hR1 : R ≤ 1) (hCt : 1 ≤ Ct) (hC : 0 < C) (hS1 : 1 ≤ S)
    (hRM : (36 * C * S + 18 * C * S ^ 2 + 3 * S + 3) * R ≤ 1) (hx0 : 0 < x) (hAle : A ≤ 6 * C * R ^ 256)
    (hb : x * B₀ ≤ Ct * R ^ 256) (hB₀0 : 0 ≤ B₀) (hA0 : 0 ≤ A) (hj : Function.Injective j)
    (hd : ∀ l, blockDist G (bondBlock G (j l)) z ≤ 2 * q)
    (hWz : ∑ b : ↥(chordBonds (finiteCells G)), Real.exp (-(κ / 2 * blockDist G (bondBlock G b) z)) ≤ S)
    {ξ : BondField ι} (hξ : ξ ∈ openPolyball ι ρ)
    (hv : |Dv ξ| ≤ x * ∑ k ∈ B, ‖ξ k‖ * (B₀ + A * ∑ l, ‖ξ l‖) + 0)
    (hgr : ∀ l, bondGradNorm Dv l ξ ≤
      x * ((if l ∈ B then B₀ + A * ∑ l', ‖ξ l'‖ else 0) + A * ∑ k ∈ B, ‖ξ k‖) + 0) :
    |Dv ξ| ≤ Ct / 3 * R ^ 4 * (x * weightedSqNormNear κ (fun k => bondBlock G (j k)) (blockDist G) z ξ + 1) ∧
    ∀ l, bondGradNorm Dv l ξ ≤
      Ct / 3 * R ^ 4 * (x * Real.sqrt (weightedSqNormNear κ (fun k => bondBlock G (j k)) (blockDist G) z ξ) + 1) *
        Real.exp (-(2 * κ * blockDist G (bondBlock G (j l)) z)) := by
  obtain ⟨Q, hQd⟩ : ∃ Q, Q = weightedSqNormNear κ (fun k => bondBlock G (j k)) (blockDist G) z ξ := ⟨_, rfl⟩
  rw [← hQd]
  have hQ0 : 0 ≤ Q := by
    rw [hQd]
    exact Finset.sum_nonneg fun _ _ => by positivity
  have hterm : ∀ l, R ^ 64 * ‖ξ l‖ ^ 2 ≤ Q := fun l => by
    have h1 : R ^ 64 ≤ Real.exp (-(2 ^ 5 * κ * blockDist G (bondBlock G (j l)) z)) := by
      rw [hR, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.2 ?_
      have h2 := mul_le_mul_of_nonneg_left (hd l) (by positivity : 0 ≤ 2 ^ 5 * κ)
      push_cast
      nlinarith only [h2]
    rw [hQd]
    unfold weightedSqNormNear
    refine le_trans (mul_le_mul_of_nonneg_right h1 (by positivity)) ?_
    exact Finset.single_le_sum (f := fun l => Real.exp (-(2 ^ 5 * κ * blockDist G (bondBlock G (j l))
      z)) * ‖ξ l‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ l)
  have hroot : ∀ l, R ^ 32 * ‖ξ l‖ ≤ Real.sqrt Q := fun l => by
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    have e : (R ^ 32 * ‖ξ l‖) ^ 2 = R ^ 64 * ‖ξ l‖ ^ 2 := by ring
    rw [e]
    exact hterm l
  have hcard : (Fintype.card ι : ℝ) * R ≤ S := by
    have h1 : ∀ i : ι, R ≤ Real.exp (-(κ / 2 * blockDist G (bondBlock G (j i)) z)) := fun i => by
      rw [hR]
      refine Real.exp_le_exp.2 ?_
      have h2 := mul_le_mul_of_nonneg_left (hd i) (by positivity : 0 ≤ κ / 2)
      nlinarith only [h2]
    have h2 : (Fintype.card ι : ℝ) * R = ∑ _i : ι, R := by simp
    rw [h2]
    calc ∑ _i : ι, R
        ≤ ∑ i : ι, Real.exp (-(κ / 2 * blockDist G (bondBlock G (j i)) z)) :=
          Finset.sum_le_sum fun i _ => h1 i
      _ = ∑ b ∈ Finset.univ.image j, Real.exp (-(κ / 2 * blockDist G (bondBlock G b) z)) :=
          (Finset.sum_image (f := fun b => Real.exp (-(κ / 2 * blockDist G (bondBlock G b) z)))
            fun _ _ _ _ h => hj h).symm
      _ ≤ ∑ b : ↥(chordBonds (finiteCells G)), Real.exp (-(κ / 2 * blockDist G (bondBlock G b) z)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => (Real.exp_pos _).le
      _ ≤ S := hWz
  obtain ⟨S₁, hS₁⟩ : ∃ S₁, S₁ = ∑ k ∈ B, ‖ξ k‖ := ⟨_, rfl⟩
  obtain ⟨S₂, hS₂⟩ : ∃ S₂, S₂ = ∑ l, ‖ξ l‖ := ⟨_, rfl⟩
  have h₁ : 0 ≤ S₁ := by rw [hS₁]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h₂ : 0 ≤ S₂ := by rw [hS₂]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h12 : S₁ ≤ S₂ := by
    rw [hS₁, hS₂]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => norm_nonneg _
  have hRS₂ : R * S₂ ≤ S := by
    have h1 : S₂ ≤ Fintype.card ι := by
      rw [hS₂]
      calc ∑ l, ‖ξ l‖ ≤ ∑ _l : ι, (1 : ℝ) := Finset.sum_le_sum fun l _ => ((hξ l).trans_le hρ1).le
        _ = Fintype.card ι := by simp
    calc R * S₂ ≤ R * Fintype.card ι := mul_le_mul_of_nonneg_left h1 hR0
      _ = (Fintype.card ι : ℝ) * R := mul_comm _ _
      _ ≤ S := hcard
  have hR33 : R ^ 33 * S₂ ≤ S * Real.sqrt Q := by
    have a1 : ∑ l, R ^ 32 * ‖ξ l‖ ≤ Fintype.card ι * Real.sqrt Q := by
      calc ∑ l, R ^ 32 * ‖ξ l‖ ≤ ∑ _l : ι, Real.sqrt Q := Finset.sum_le_sum fun l _ => hroot l
        _ = Fintype.card ι * Real.sqrt Q := by simp
    have a2 : R ^ 33 * S₂ = R * ∑ l, R ^ 32 * ‖ξ l‖ := by
      rw [hS₂, ← Finset.mul_sum]
      ring
    rw [a2]
    have a3 := Real.sqrt_nonneg Q
    calc R * ∑ l, R ^ 32 * ‖ξ l‖ ≤ R * (Fintype.card ι * Real.sqrt Q) := mul_le_mul_of_nonneg_left a1 hR0
      _ = ((Fintype.card ι : ℝ) * R) * Real.sqrt Q := by ring
      _ ≤ S * Real.sqrt Q := mul_le_mul_of_nonneg_right hcard a3
  have hp33 : 0 ≤ R ^ 33 := pow_nonneg hR0 _
  have hR33₁ : R ^ 33 * S₁ ≤ S * Real.sqrt Q :=
    (mul_le_mul_of_nonneg_left h12 hp33).trans hR33
  have hS0 : 0 ≤ S := by linarith only [hS1]
  have hSS : (R ^ 33 * S₁) * (R ^ 33 * S₂) ≤ S ^ 2 * Q := by
    have a3 := Real.sqrt_nonneg Q
    calc (R ^ 33 * S₁) * (R ^ 33 * S₂) ≤ (S * Real.sqrt Q) * (S * Real.sqrt Q) :=
          mul_le_mul hR33₁ hR33 (mul_nonneg hp33 h₂) (mul_nonneg hS0 a3)
      _ = S ^ 2 * (Real.sqrt Q * Real.sqrt Q) := by ring
      _ = S ^ 2 * Q := by rw [Real.mul_self_sqrt hQ0]
  have hRS₁ : R * S₁ ≤ S := (mul_le_mul_of_nonneg_left h12 hR0).trans hRS₂
  have hp1 : 0 ≤ 36 * C * S * R := by positivity
  have hp2 : 0 ≤ 18 * C * S ^ 2 * R := by positivity
  have hp3 : 0 ≤ 3 * S * R := by positivity
  have hp4 : 0 ≤ 3 * R := by positivity
  have hMe : (36 * C * S + 18 * C * S ^ 2 + 3 * S + 3) * R =
      36 * C * S * R + 18 * C * S ^ 2 * R + 3 * S * R + 3 * R := by ring
  have hM₁ : (18 * C * S ^ 2 + 3 * S) * R ≤ 1 := by
    have e : (18 * C * S ^ 2 + 3 * S) * R = 18 * C * S ^ 2 * R + 3 * S * R := by ring
    rw [e]
    linarith only [hRM, hMe, hp1, hp4]
  have hM₂ : (36 * C * S + 3) * R ≤ 1 := by
    have e : (36 * C * S + 3) * R = 36 * C * S * R + 3 * R := by ring
    rw [e]
    linarith only [hRM, hMe, hp2, hp3]
  constructor
  · refine hv.trans ?_
    have e1 : ∑ k ∈ B, ‖ξ k‖ * (B₀ + A * ∑ l, ‖ξ l‖) = S₁ * (B₀ + A * S₂) := by
      rw [hS₁, hS₂, Finset.sum_mul]
    rw [e1]
    have h3 := value_bound_arith hR0 hR1 hCt hC.le hS1 hM₁ hx0.le hQ0 h₁ h₂ hAle hb hRS₁ hSS
    calc x * (S₁ * (B₀ + A * S₂)) + 0 = x * B₀ * S₁ + x * (A * S₁ * S₂) := by ring
      _ ≤ _ := h3
  · intro l
    refine (hgr l).trans ?_
    rw [← hS₁, ← hS₂]
    have hE4 : R ^ 4 ≤ Real.exp (-(2 * κ * blockDist G (bondBlock G (j l)) z)) := by
      rw [hR, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.2 ?_
      have h2 := mul_le_mul_of_nonneg_left (hd l) (by positivity : 0 ≤ 2 * κ)
      push_cast
      nlinarith only [h2]
    have h4 := gradient_bound_arith hR0 hR1 hCt hC.le hS1 hM₂ hx0.le (Real.sqrt_nonneg Q) h₁ h₂ hAle hb hR33₁ hR33 hE4
    refine le_trans ?_ h4
    have hs2 : 0 ≤ x * (A * S₂) := by positivity
    have hs1 : 0 ≤ x * (A * S₁) := by positivity
    have hbb : 0 ≤ x * B₀ := by positivity
    split_ifs
    · linarith only [hs1, hs2, hbb, (by ring : x * (B₀ + A * S₂ + A * S₁) + 0 = x * B₀ + x * (A * S₂) + x * (A * S₁))]
    · linarith only [hs1, hs2, hbb, (by ring : x * (0 + A * S₁) + 0 = x * (A * S₁))]
set_option maxHeartbeats 2000000 in
private theorem pairedPartsCompareSmoothly_of {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {C S h₀ : ℝ} {t : ℕ} {x s : ℝ} {h : LocalFamily} {V : F.GaugeField F.top}
    {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {q : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {j : ι → ↥(chordBonds (finiteCells F))} {j' : ι → ↥(chordBonds (finiteCells F'))} {o : Fin 4 → ℤ}
    (hE : PushforwardFieldProperties) (hLC : ImaginaryCoordinatesIsometric) (hO : TorusOffsetsAboutCell)
    (hX : ExponentDifferenceBound) (hRay : RadialSlopeIntegralContDiffOn)
    (hSh : ChartLipschitz.ChartedFieldLipschitz) (hEn : PairedEnergyBoundsAt T.a T.L T.chainParams C) (hC : 0 < C) (hS1 : 1 ≤ S)
    (hW : ∀ (F : BlockFrame) (n : ℕ), F.blockSide = T.L → 2 ≤ n → (∀ i, F.extent i = n) → ∀ z : F.Cell,
      ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(T.κ / 2 * blockDist F (bondBlock F b) z)) ≤ S)
    (hoddL : Odd T.L) (hL40 : 2 ^ 40 ≤ T.L) (hδ : 0 < T.chainParams.δ₂) (hκ0 : 0 < T.κ)
    (hκ : T.κ ≤ T.chainParams.δ₂ / 2 ^ 16) (hCt : 1 ≤ T.Ct) (hσ0 : 0 < T.σ)
    (hσ1 : T.Ct * T.σ ≤ 1 / (256 * (T.L : ℝ))) (hσ2 : T.σ ≤ T.chainParams.s₀ / 2) (hh0 : 0 < h₀)
    (hh1 : h₀ ≤ T.chainParams.s₀ / 64) (hh2 : h₀ ≤ 1 / (256 * (T.L : ℝ))) (hn64 : 64 ≤ T.n₀) (hy : 1 ≤ T.coupling)
    (hq64 : 64 ≤ T.blockIndex)
    (hRq : ∀ q : ℕ, T.blockIndex ≤ q → Real.exp (-(T.κ * q)) ≤ h₀ ∧
      (36 * C * S + 18 * C * S ^ 2 + 3 * S + 3) * Real.exp (-(T.κ * q)) ≤ 1)
    (hnear : InterpolatedFramesControlledAt T t x)
    (hloc : InterpolatedSlopeLocal s T.a T.chainParams.ρA T.κ T.Ct x (frameRadius x) V V' Y Y' q)
    (st : InterpolatedComparisonSetting T t x s h V V' Y Y' q j j' o) :
    PairedPartsCompareSmoothly T.ballRadius (T.Ct / 3) (Real.exp (-(4 * T.κ * q))) x T.κ j j' (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o)
      (interpolatedSlopePart s T.a T.chainParams.ρA x (frameRadius x) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) V)
      (interpolatedSlopePart s T.a T.chainParams.ρA x (frameRadius x) (Y' + _root_.YangMills.Construction.BlockAverages.siteOfCoords F'.top o) V') := by
  classical
  have hx0 : 0 < x := lt_of_lt_of_le one_pos (hy.trans st.coupling_le)
  obtain ⟨hFL, hFt, nF, hnF, hnF0⟩ := st.top
  obtain ⟨hFL', hFt', nF', hnF', hnF0'⟩ := st.top'
  have hFtt : F'.depth = F.depth := hFt'.trans hFt.symm
  have hLF : Odd F.blockSide := by rw [hFL]; exact hoddL
  have hLF' : Odd F'.blockSide := by rw [hFL']; exact hoddL
  have hLL : F.blockSide = F'.blockSide := hFL.trans hFL'.symm
  have hFc : IsBlockTorus T.L F := ⟨hFL, nF, by omega, hnF⟩
  have hFc' : IsBlockTorus T.L F' := ⟨hFL', nF', by omega, hnF'⟩
  have hq : 64 ≤ q := hq64.trans st.radius_le
  have hs : ∀ i, 2 * q + 2 < F.extent i := fun i => by
    rcases st.agree.1 i with h | h
    · rw [hnF i] at h
      omega
    · exact h
  have hs' : ∀ i, 2 * q + 2 < F'.extent i := fun i => by
    rcases st.agree.2.1 i with h | h
    · rw [hnF' i] at h
      omega
    · exact h
  obtain ⟨c1, _, c3, _, _, _, _, c8, _⟩ := hO F q Y hLF hs
  obtain ⟨c1', _⟩ := hO F' q Y' hLF' hs'
  have ho8 : WithinRadius (q / 8) o := fun l => by
    have h1 := st.offset_le l
    show |o l| ≤ ((q / 8 : ℕ) : ℤ)
    omega
  have hoq : WithinRadius q o := fun l => (ho8 l).trans (by exact_mod_cast Nat.div_le_self q 8)
  have hLC' := hLC
  obtain ⟨_, _, hnorm, _, hadd, hzero, _⟩ := hLC'
  set w : F.Site F.depth → Fin 4 → imaginaryQuaternions := fun y i => interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) (y, i) V with hw
  set w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions :=
    fun y i => interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) (y, i) V' with hw'
  obtain ⟨_, hsm⟩ := hnear.single F V s st.top st.small st.interp_mem.1 st.interp_mem.2
  obtain ⟨_, hsm'⟩ := hnear.single F' V' s st.top' st.small' st.interp_mem.1 st.interp_mem.2
  have hloc2 := hnear.pair F F' V V' Y Y' q s st.top st.top' st.small st.small' st.agree st.interp_mem.1 st.interp_mem.2
  have hcf : IsSmallCurvature (41 / 64 * T.σ) (chartedField w V) := by
    have h1 := hsm.small_curvature
    have e : interpolatedField s T.a T.chainParams.ρA (frameRadius x) V 0 = chartedField w V := by
      show chartedField (shiftCoordinates w 0) V = _
      rw [hzero]
    rwa [e] at h1
  have hcf' : IsSmallCurvature (41 / 64 * T.σ) (chartedField w' V') := by
    have h1 := hsm'.small_curvature
    have e : interpolatedField s T.a T.chainParams.ρA (frameRadius x) V' 0 = chartedField w' V' := by
      show chartedField (shiftCoordinates w' 0) V' = _
      rw [hzero]
    rwa [e] at h1
  obtain ⟨R, hR⟩ : ∃ R, R = Real.exp (-(T.κ * q)) := ⟨_, rfl⟩
  obtain ⟨hRh, hRM⟩ := hRq q st.radius_le
  rw [← hR] at hRh hRM
  obtain ⟨r₂, hr₂⟩ : ∃ r₂, r₂ = q - q / 8 := ⟨_, rfl⟩
  obtain ⟨hhR, hθh, hAle⟩ := exp_radius_bounds (C := C) (L := T.L) (r₂ := r₂) hδ hκ0 hκ hC hL40 hq hr₂ hR
  obtain ⟨hh, hhh⟩ : ∃ hh, hh = Real.exp (-(T.chainParams.δ₂ / 2 ^ 8 * q)) := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = Real.exp (-(T.chainParams.δ₂ / 2 ^ 6 * q)) := ⟨_, rfl⟩
  rw [← hhh, ← hθ] at hθh hAle
  rw [← hhh] at hhR
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hR0 : 0 ≤ R := by rw [hR]; exact (Real.exp_pos _).le
  have hR1 : R ≤ 1 := by
    rw [hR]
    exact Real.exp_le_one_iff.2 (by have := mul_nonneg hκ0.le hq0; linarith only [this])
  have hhpos : 0 < hh := by rw [hhh]; exact Real.exp_pos _
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact (Real.exp_pos _).le
  have hhR1 : hh ≤ R := hhR.trans (pow_le_of_le_one hR0 hR1 (by norm_num))
  have hh1' : hh ≤ 1 := hhR1.trans hR1
  have hθhh : θ ≤ hh := hθh.trans (mul_le_of_le_one_right hhpos.le hh1')
  have hLpos : (0 : ℝ) < T.L := by
    have : 0 < T.L := by omega
    exact_mod_cast this
  have hρe : T.ballRadius = T.σ / 64 := rfl
  have hρ : 0 < T.ballRadius := by rw [hρe]; positivity
  obtain ⟨ρ₂, hρ₂⟩ : ∃ ρ₂, ρ₂ = T.ballRadius + h₀ := ⟨_, rfl⟩
  have hρ₂0 : 0 < ρ₂ := by rw [hρ₂]; exact add_pos hρ hh0
  have hτ0 : 0 ≤ ρ₂ + θ := add_nonneg hρ₂0.le hθ0
  have hσc : T.σ ≤ T.Ct * T.σ := le_mul_of_one_le_left hσ0.le hCt
  have hsum : T.Ct * T.σ + (ρ₂ + θ) ≤ 1 / (64 * (T.L : ℝ)) := by
    have e : 1 / (64 * (T.L : ℝ)) = 4 * (1 / (256 * (T.L : ℝ))) := by
      field_simp
      norm_num
    rw [e, hρ₂, hρe]
    linarith only [hσ1, hσc, hσ0, hh2, hθhh, hhR1, hRh]
  have hcc : 41 / 64 * T.σ + 4 * (ρ₂ + θ) ≤ T.chainParams.s₀ := by
    rw [hρ₂, hρe]
    linarith only [hσ2, hh1, hh0, hθhh, hhR1, hRh, hσ0]
  have hszw : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ T.Ct * T.σ := fun b hb => by
    show ‖interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) (b.1, b.2) V‖ ≤ _
    exact hsm.norm_le b hb
  have hszw' : ∀ b ∈ chordBonds (finiteCells F'), ‖w' b.1 b.2‖ ≤ T.Ct * T.σ := fun b hb => by
    show ‖interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) (b.1, b.2) V'‖ ≤ _
    exact hsm'.norm_le b hb
  have hP : ∀ ξ ∈ openPolyball ι ρ₂, ∀ Δ : StepVariable (finiteCells F), (∀ b, ‖Δ b‖ ≤ θ) →
      IsAdmissibleChartPoint T.L T.chainParams.s₀ (shiftCoordinates (shiftCoordinates w (pushforwardField j ξ)) Δ) V := fun ξ hξ Δ hΔ => by
    rw [hadd]
    refine isAdmissibleChartPoint_of_shift hSh hLC hszw hcf hτ0 hsum hcc fun b => ?_
    show ‖pushforwardField j ξ b + Δ b‖ ≤ _
    exact (norm_add_le _ _).trans (add_le_add (norm_pushforwardField_le hE st.injective hρ₂0.le hξ b) (hΔ b))
  have hP' : ∀ ξ ∈ openPolyball ι ρ₂, IsAdmissibleChartPoint T.L T.chainParams.s₀ (shiftCoordinates w' (pushforwardField j' ξ)) V' := fun ξ hξ =>
    isAdmissibleChartPoint_of_shift hSh hLC hszw' hcf' hτ0 hsum hcc fun b =>
      (norm_pushforwardField_le hE st.injective' hρ₂0.le hξ b).trans (le_add_of_nonneg_right hθ0)
  have hr1 : 1 ≤ r₂ := by omega
  have hrq : r₂ ≤ q := by omega
  have hNear : CoordinatesCloseOnBall T.L Y Y' r₂ θ w w' := by
    intro g u i hg hu hb
    have hu' : u ∈ centredCube F.blockSide := by rw [hFL]; exact hu
    have hb' : IsFineBondWithinRadius Y q g u i := isFineBondInBox_of_withinRadius hO hLF hs (r := r₂) (by omega) le_rfl hg hu' hb
    have hv := hloc2.norm_sub_le g u i hb'
    have e3 : ‖(w (fineBondAt Y g u i).1 i : ℍ[ℝ]) - w' (fineBondAt Y' g u i).1 i‖ =
        ‖interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) (fineBondAt Y g u i) V -
          interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) (fineBondAt Y' g u i) V'‖ := rfl
    rw [e3]
    refine hv.trans ?_
    have hdist : cellSupDist Y (enclosingCell (fineBondAt Y g u i).1) ≤ r₂ := by
      have e := (c1 g u i hu').1
      rw [e, (c3 g (fun l => (hg l).trans (by exact_mod_cast hrq))).2]
      exact sup_natAbs_le_of_withinRadius hg
    have h16 : 16 * cellSupDist Y (enclosingCell (fineBondAt Y g u i).1) + q ≤ 16 * q := by omega
    have h16' : (q : ℝ) / 16 ≤ (q : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y g u i).1) := by
      have h16r : (16 : ℝ) * cellSupDist Y (enclosingCell (fineBondAt Y g u i).1) + q ≤ 16 * q := by exact_mod_cast h16
      linarith only [h16r]
    have hcσ : T.Ct * T.σ ≤ 1 := by
      refine hσ1.trans ?_
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ T.L := by
        have : 1 ≤ T.L := by omega
        exact_mod_cast this
      linarith only [this]
    rw [hθ]
    calc T.Ct * T.σ * Real.exp (-(T.chainParams.δ₂ / 4 * ((q : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y g u i).1))))
        ≤ 1 * Real.exp (-(T.chainParams.δ₂ / 2 ^ 6 * q)) := by
          refine mul_le_mul hcσ (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le zero_le_one
          have := mul_le_mul_of_nonneg_left h16' (by positivity : 0 ≤ T.chainParams.δ₂ / 4)
          have e : T.chainParams.δ₂ / 4 * ((q : ℝ) / 16) = T.chainParams.δ₂ / 2 ^ 6 * q := by ring
          linarith only [this, e]
      _ = _ := one_mul _
  obtain ⟨sm, sm', sl, sec⟩ := hEn F F' w w' V V' Y Y' q r₂ θ ρ₂ ι j j' hFc hFc' hFtt hθ0 hρ₂0 hr1 hrq hs hs'
    st.injective st.injective' st.paired hP hP' (agreeOnBall_mono st.agree hrq) hNear
  have hmono : ∀ ξ ∈ openPolyball ι T.ballRadius, ξ ∈ openPolyball ι ρ₂ := fun ξ hξ b =>
    (hξ b).trans_le (by rw [hρ₂]; exact le_add_of_nonneg_right hh0.le)
  obtain ⟨g, hg⟩ : ∃ g, g = fun ξ => chartedEnergyAt T.a w V (pushforwardField j ξ) := ⟨_, rfl⟩
  obtain ⟨g', hg'⟩ : ∃ g', g' = fun ξ => chartedEnergyAt T.a w' V' (pushforwardField j' ξ) := ⟨_, rfl⟩
  rw [← hg] at sm sl sec
  rw [← hg'] at sm' sl sec
  have sm2 : ContDiffOn ℝ 2 g (openPolyball ι T.ballRadius) := (sm.of_le (by norm_num)).mono hmono
  have sm2' : ContDiffOn ℝ 2 g' (openPolyball ι T.ballRadius) := (sm'.of_le (by norm_num)).mono hmono
  have hpair : ∀ k, ∃ (g₀ u : Fin 4 → ℤ) (i : Fin 4), u ∈ centredCube F.blockSide ∧ WithinRadius q g₀ ∧
      (j k).1 = fineBondAt Y g₀ u i ∧ (j' k).1 = fineBondAt Y' g₀ u i ∧
      enclosingCell (j k).1.1 = Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top g₀ ∧ enclosingCell (j' k).1.1 = Y' + _root_.YangMills.Construction.BlockAverages.siteOfCoords F'.top g₀ := fun k => by
    obtain ⟨g₀, u, i, hu, hg₀, e1, e2⟩ := st.paired k
    refine ⟨g₀, u, i, hu, hg₀, e1, e2, ?_, ?_⟩
    · rw [e1]
      exact (c1 g₀ u i hu).1
    · rw [e2]
      exact (c1' g₀ u i (hLL ▸ hu)).1
  obtain ⟨B, hB⟩ : ∃ B : Finset ι, ∀ k, k ∈ B ↔ enclosingCell (j k).1.1 = Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o :=
    ⟨Finset.univ.filter fun k => enclosingCell (j k).1.1 = Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o, fun k => by simp⟩
  have hB' : ∀ k, k ∈ B ↔ enclosingCell (j' k).1.1 = Y' + _root_.YangMills.Construction.BlockAverages.siteOfCoords F'.top o := fun k => by
    rw [hB]
    obtain ⟨g₀, u, i, hu, hg₀, _, _, d1, d2⟩ := hpair k
    rw [d1, d2]
    constructor
    · intro e
      rw [offset_eq_of_site_eq hO hLF hs hg₀ hoq hu e]
    · intro e
      rw [offset_eq_of_site_eq hO hLF' hs' hg₀ hoq (hLL ▸ hu) e]
  have hBo : ∀ k ∈ B, ∃ (u : Fin 4 → ℤ) (i : Fin 4), u ∈ centredCube F.blockSide ∧
      (j k).1 = fineBondAt Y o u i ∧ (j' k).1 = fineBondAt Y' o u i := fun k hk => by
    obtain ⟨g₀, u, i, hu, hg₀, e1, e2, d1, _⟩ := hpair k
    have := offset_eq_of_site_eq hO hLF hs hg₀ hoq hu (d1.symm.trans ((hB k).1 hk))
    subst this
    exact ⟨u, i, hu, e1, e2⟩
  have h0mem : (0 : BondField ι) ∈ openPolyball ι ρ₂ := fun b => by simpa using hρ₂0
  have hslope0 : ∀ (k : ι) (u₀ : BondVector), chartedSlope T.a w V (j k).1 (toImaginary u₀) = bondPartialDeriv g k 0 u₀ := fun k u₀ => by
    have := (sl 0 h0mem k u₀).1
    rwa [pushforwardField_zero, hzero] at this
  have hslope0' : ∀ (k : ι) (u₀ : BondVector), chartedSlope T.a w' V' (j' k).1 (toImaginary u₀) = bondPartialDeriv g' k 0 u₀ := fun k u₀ => by
    have := (sl 0 h0mem k u₀).2
    rwa [pushforwardField_zero, hzero] at this
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, B₀ = T.Ct * Real.exp (-(2 ^ 8 * T.κ * q)) / x := ⟨_, rfl⟩
  have hexp : Real.exp (-(2 ^ 8 * T.κ * q)) = R ^ 256 := by
    rw [hR, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hB₀0 : 0 ≤ B₀ := by
    rw [hB₀]
    have : 0 < T.Ct := lt_of_lt_of_le one_pos hCt
    positivity
  have hb0 : ∀ k ∈ B, ∀ e, |bondPartialDeriv g' k 0 e - bondPartialDeriv g k 0 e| ≤ B₀ * ‖e‖ := fun k hk e => by
    obtain ⟨u, i, hu, e1, e2⟩ := hBo k hk
    have hb : IsFineBondWithinRadius Y (q / 4) o u i :=
      isFineBondInBox_of_withinRadius hO hLF hs (r := q / 8) (by omega) (by omega) ho8 hu (by rw [← e1]; exact (j k).2)
    have unit : ∀ u₀ : BondVector, ‖u₀‖ = 1 → |bondPartialDeriv g' k 0 u₀ - bondPartialDeriv g k 0 u₀| ≤ B₀ := fun u₀ h1 => by
      have hh' := hloc o u i (toImaginary u₀) hb (by rw [hnorm]; exact h1)
      have a1 := hslope0 k u₀
      have a2 := hslope0' k u₀
      rw [e1] at a1
      rw [e2] at a2
      unfold interpolatedSlope at hh'
      change x * |chartedSlope T.a w V (fineBondAt Y o u i) (toImaginary u₀) -
        chartedSlope T.a w' V' (fineBondAt Y' o u i) (toImaginary u₀)| ≤ _ at hh'
      rw [a1, a2, abs_sub_comm] at hh'
      rw [hB₀, le_div_iff₀ hx0, mul_comm]
      exact hh'
    by_cases he : e = 0
    · subst he
      simp [bondPartialDeriv, bondVariation]
    · have hn : 0 < ‖e‖ := norm_pos_iff.2 he
      have hu1 : ‖(‖e‖⁻¹ • e : BondVector)‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm]
        field_simp
      have he' : e = ‖e‖ • (‖e‖⁻¹ • e : BondVector) := by
        rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      have hu2 := unit _ hu1
      have p1 := bondPartialDeriv_smul g' k 0 ‖e‖ (‖e‖⁻¹ • e)
      have p2 := bondPartialDeriv_smul g k 0 ‖e‖ (‖e‖⁻¹ • e)
      rw [← he'] at p1 p2
      rw [p1, p2, ← mul_sub, abs_mul, abs_of_pos hn, mul_comm]
      exact mul_le_mul_of_nonneg_right hu2 hn.le
  obtain ⟨A, hAd⟩ : ∃ A, A = (2 * (C * (θ + Real.exp (-(T.chainParams.δ₂ * ((T.L : ℝ) * ((r₂ : ℝ) / 2) - 2 * T.L - 1)))))) / hh +
      2 * C * hh := ⟨_, rfl⟩
  rw [← hAd] at hAle
  have hsec : ∀ ξ ∈ openPolyball ι T.ballRadius, ∀ k ∈ B, ∀ (l : ι) (e e' : BondVector),
      |secondDerivAlong g' ξ (bondVariation k e) (bondVariation l e') - secondDerivAlong g ξ (bondVariation k e) (bondVariation l e')| ≤ A * ‖e‖ * ‖e'‖ :=
    fun ξ hξ k hk l e e' => by
    obtain ⟨u, i, hu, e1, e2⟩ := hBo k hk
    have := sec T.ballRadius hh hhpos hρ (by rw [hρ₂]; exact add_le_add_right (hhR1.trans hRh) _) ξ hξ k l o u i e e'
      (isFineBondInBox_of_withinRadius hO hLF hs (r := q / 8) (by omega) (by omega) ho8 hu (by rw [← e1]; exact (j k).2)) e1 e2
    rwa [← hAd] at this
  have hXa := hX ι B T.ballRadius x B₀ A 0 0 g g' (fun _ => 0) (fun _ => 0) hρ hx0.le sm2 sm2' contDiffOn_const
    contDiffOn_const hb0 hsec (fun _ _ => by simp) (fun ξ _ k e _ => by simp [bondPartialDeriv])
  have hsl : ∀ ζ ∈ openPolyball ι T.ballRadius, ∀ (k : ι) (u : BondVector),
      chartedSlope T.a (shiftCoordinates w (pushforwardField j ζ)) V (j k).1 (toImaginary u) = bondPartialDeriv g k ζ u :=
    fun ζ hζ k u => (sl ζ (hmono ζ hζ) k u).1
  have hsl' : ∀ ζ ∈ openPolyball ι T.ballRadius, ∀ (k : ι) (u : BondVector),
      chartedSlope T.a (shiftCoordinates w' (pushforwardField j' ζ)) V' (j' k).1 (toImaginary u) = bondPartialDeriv g' k ζ u :=
    fun ζ hζ k u => (sl ζ (hmono ζ hζ) k u).2
  have heq : ∀ ζ ∈ openPolyball ι T.ballRadius,
      interpolatedSlopePart s T.a T.chainParams.ρA x (frameRadius x) (Y' + _root_.YangMills.Construction.BlockAverages.siteOfCoords F'.top o) V' (pushforwardField j' ζ) -
        interpolatedSlopePart s T.a T.chainParams.ρA x (frameRadius x) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) V (pushforwardField j ζ) =
      (x * radialSlopeIntegral B g' ζ - 0) - (x * radialSlopeIntegral B g ζ - 0) := fun ζ hζ => by
    rw [interpolatedSlopePart_eq hE hLC st.injective' hB' hsl' hζ, interpolatedSlopePart_eq hE hLC st.injective hB hsl hζ]
    simp
  have hD1 : ContDiffOn ℝ 1 (fun ζ => (x * radialSlopeIntegral B g' ζ - 0) - (x * radialSlopeIntegral B g ζ - 0))
      (openPolyball ι T.ballRadius) :=
    ((contDiffOn_const.mul (hRay ι B T.ballRadius g' sm2')).sub contDiffOn_const).sub
      ((contDiffOn_const.mul (hRay ι B T.ballRadius g sm2)).sub contDiffOn_const)
  have hd : ∀ l, blockDist F (bondBlock F (j l)) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) ≤ 2 * q := fun l => by
    obtain ⟨g₀, u, i, hu, hg₀, _, _, d1, _⟩ := hpair l
    have e : bondBlock F (j l) = Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top g₀ := d1
    rw [e]
    have t1 := c8 (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top g₀) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o)
    have a1 := (c3 g₀ hg₀).1
    have a2 := (c3 o hoq).1
    have b1 := sup_natAbs_le_of_withinRadius hg₀
    have b2 := sup_natAbs_le_of_withinRadius hoq
    have : cellSupDist (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top g₀) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) ≤ 2 * q := by omega
    show ((cellSupDist (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top g₀) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) : ℕ) : ℝ) ≤ 2 * q
    exact_mod_cast this
  have hρ1 : T.ballRadius ≤ 1 := by
    have : T.σ ≤ 1 := by
      refine hσc.trans (hσ1.trans ?_)
      rw [div_le_one (by positivity)]
      have h1 : (1 : ℝ) ≤ T.L := by
        have : 1 ≤ T.L := by omega
        exact_mod_cast this
      linarith only [h1]
    rw [hρe]
    linarith only [this, hσ0]
  have hb : x * B₀ ≤ T.Ct * R ^ 256 := by
    rw [hB₀, hexp]
    apply le_of_eq
    field_simp
  have hAnn : 0 ≤ A := by
    rw [hAd]
    have h1 : 0 ≤ θ + Real.exp (-(T.chainParams.δ₂ * ((T.L : ℝ) * ((r₂ : ℝ) / 2) - 2 * T.L - 1))) :=
      add_nonneg hθ0 (Real.exp_pos _).le
    positivity
  have hexp4 : Real.exp (-(4 * T.κ * q)) = R ^ 4 := by
    rw [hR, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp4]
  refine ⟨hD1.congr heq, fun ξ hξ => ?_⟩
  obtain ⟨hv, hgr⟩ := hXa ξ hξ
  obtain ⟨tl1, tl2⟩ := tail_bounds hκ0 hρ1 hR hR0 hR1 hCt hC hS1 hRM hx0 hAle hb hB₀0 hAnn st.injective hd
    (hW F nF hFL (by omega) hnF (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o)) hξ hv hgr
  refine ⟨?_, fun l => ?_⟩
  · rw [heq ξ hξ]
    exact tl1
  · have hopen := _root_.YangMills.Construction.ColdStepAtMirrorFrames.isOpen_openPolyball (ι := ι) T.ballRadius
    have ev : (fun ζ => interpolatedSlopePart s T.a T.chainParams.ρA x (frameRadius x) (Y' + _root_.YangMills.Construction.BlockAverages.siteOfCoords F'.top o) V' (pushforwardField j' ζ) -
          interpolatedSlopePart s T.a T.chainParams.ρA x (frameRadius x) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) V (pushforwardField j ζ)) =ᶠ[nhds ξ]
        fun ζ => (x * radialSlopeIntegral B g' ζ - 0) - (x * radialSlopeIntegral B g ζ - 0) := by
      filter_upwards [hopen.mem_nhds hξ] with ζ hζ using heq ζ hζ
    have hpn : bondGradNorm (fun ζ => interpolatedSlopePart s T.a T.chainParams.ρA x (frameRadius x) (Y' + _root_.YangMills.Construction.BlockAverages.siteOfCoords F'.top o) V' (pushforwardField j' ζ) -
          interpolatedSlopePart s T.a T.chainParams.ρA x (frameRadius x) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) V (pushforwardField j ζ)) l ξ =
        bondGradNorm (fun ζ => (x * radialSlopeIntegral B g' ζ - 0) - (x * radialSlopeIntegral B g ζ - 0)) l ξ := by
      unfold bondGradNorm
      rw [ev.fderiv_eq]
    rw [hpn]
    exact tl2 l
theorem interpolatedSlopesCompareStatement_holds (hStay : interpolatedFramesControlled)
    (hSl : interpolatedSlopeLocalOnTwoTori) (hEn : PairedEnergiesCompare)
    (hX : ExponentDifferenceBound) (hRay : RadialSlopeIntegralContDiffOn)
    (hE : PushforwardFieldProperties) (hLC : ImaginaryCoordinatesIsometric) (hO : TorusOffsetsAboutCell)
    (hW : ExpWeightSumsBounded) (hSh : ChartLipschitz.ChartedFieldLipschitz) (hJ : EventuallyInParametersCombines) :
    interpolatedSlopesCompareStatement := by
  obtain ⟨hJ1, hJ2⟩ := hJ
  have hR : EventuallyInParameters (fun T => (∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFramesControlledAt T t x) →
      (∀ (t : ℕ) (x : ℝ), T.coupling ≤ x →
        ∀ (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) (s : ℝ),
          IsCubicTopTorus T.L t T.n₀ F → IsCubicTopTorus T.L t T.n₀ F' → IsSmallCurvature (5 / 4 * T.σ) V →
          IsSmallCurvature (5 / 4 * T.σ) V' → AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r → 0 ≤ s →
          s ≤ 1 → InterpolatedSlopeLocal s T.a T.chainParams.ρA T.κ T.Ct x (frameRadius x) V V' Y Y' r) →
      InterpolatedSlopesCompareAt T) := by
    intro a ha
    refine ⟨2 ^ 40, fun L hL hL0 c hc => ?_⟩
    obtain ⟨C, hC, hEnC⟩ := hEn a L c ha hL hL0 hc
    obtain ⟨⟨hρ, hρ1, hs₀, hδ₂, hκ₂, hK, hC1, hKk⟩, -⟩ := hc.classical
    have hLpos : (0 : ℝ) < L := by
      have : 0 < L := by omega
      exact_mod_cast this
    refine ⟨1, fun Ct hCt => ⟨c.δ₂ / 2 ^ 16, by positivity, fun κ hκ0 hκ => ⟨1, one_pos, fun η₃ _ _ _ => ?_⟩⟩⟩
    obtain ⟨S₀, hS₀⟩ := hW L (κ / 2) hL (by positivity)
    obtain ⟨S, hSd⟩ : ∃ S, S = max S₀ 1 := ⟨_, rfl⟩
    have hS1 : 1 ≤ S := by rw [hSd]; exact le_max_right _ _
    have hSS₀ : S₀ ≤ S := by rw [hSd]; exact le_max_left _ _
    obtain ⟨h₀, hh₀⟩ : ∃ h₀, h₀ = min (c.s₀ / 64) (1 / (256 * (L : ℝ))) := ⟨_, rfl⟩
    have hh0 : 0 < h₀ := by rw [hh₀]; exact lt_min (by positivity) (by positivity)
    obtain ⟨M, hMd⟩ : ∃ M, M = 36 * C * S + 18 * C * S ^ 2 + 3 * S + 3 := ⟨_, rfl⟩
    have hM0 : 0 < M := by rw [hMd]; positivity
    obtain ⟨τ, hτd⟩ : ∃ τ, τ = min h₀ (1 / M) := ⟨_, rfl⟩
    have hτ0 : 0 < τ := by rw [hτd]; exact lt_min hh0 (by positivity)
    have hN : ∃ N₀ : ℕ, ∀ q : ℕ, N₀ ≤ q → Real.exp (-(κ * q)) ≤ τ := by
      refine ⟨⌈(-Real.log τ) / κ⌉₊, fun q hq => ?_⟩
      have h1 : (-Real.log τ) / κ ≤ q := (Nat.le_ceil _).trans (by exact_mod_cast hq)
      have h2 : -Real.log τ ≤ κ * q := by rwa [div_le_iff₀' hκ0] at h1
      calc Real.exp (-(κ * q)) ≤ Real.exp (Real.log τ) := Real.exp_le_exp.2 (by linarith)
        _ = τ := Real.exp_log hτ0
    obtain ⟨N₀, hN₀⟩ := hN
    have hCt1 : 1 ≤ Ct := hCt
    refine ⟨max N₀ 64, fun nss hnss => ⟨min (c.s₀ / 2) (1 / (256 * L * Ct)), ?_, fun σ hσ hσle p hp =>
      ⟨0, fun Cs _ E hE' => ⟨64, fun n₀ hn₀ => ⟨0, fun CE _ => ⟨1, fun y₁ hy₁ => ?_⟩⟩⟩⟩⟩⟩
    · have : 0 < Ct := by linarith
      exact lt_min (by positivity) (by positivity)
    · intro hnr hlc t x s h F F' V V' Y Y' q ι _ _ j j' o st
      have hCt0 : 0 < Ct := by linarith
      have hσ1 : Ct * σ ≤ 1 / (256 * (L : ℝ)) := by
        have h1 : σ ≤ 1 / (256 * L * Ct) := hσle.trans (min_le_right _ _)
        calc Ct * σ ≤ Ct * (1 / (256 * L * Ct)) := by gcongr
          _ = _ := by field_simp
      refine pairedPartsCompareSmoothly_of (T := ⟨a, L, c, Ct, κ, η₃, nss, σ, p, Cs, E, n₀, CE, y₁⟩) (C := C) (S := S) (h₀ := h₀)
        hE hLC hO hX hRay hSh hEnC hC hS1 (fun G n hG h2 hs z => ((hS₀ G n hG h2 hs z).1).trans hSS₀)
        hL hL0 hδ₂ hκ0 hκ hCt1 hσ hσ1 (hσle.trans (min_le_left _ _)) hh0 ?_ ?_ hn₀ hy₁
        ((le_max_right _ _).trans hnss) ?_ (hnr t x st.coupling_le) ?_ st
      · rw [hh₀]
        exact min_le_left _ _
      · rw [hh₀]
        exact min_le_right _ _
      · intro q' hq'
        have h1 := hN₀ q' ((le_max_left _ _).trans (hnss.trans hq'))
        have h2 : Real.exp (-(κ * q')) ≤ h₀ := h1.trans (by rw [hτd]; exact min_le_left _ _)
        have h3 : Real.exp (-(κ * q')) ≤ 1 / M := h1.trans (by rw [hτd]; exact min_le_right _ _)
        refine ⟨h2, ?_⟩
        rw [← hMd]
        have := (le_div_iff₀ hM0).1 h3
        linarith
      · exact hlc t x st.coupling_le F F' V V' Y Y' q s st.top st.top' st.small st.small' st.agree st.interp_mem.1 st.interp_mem.2
  refine hJ2 _ _ ?_ (hJ1 _ _ (hJ1 _ _ hStay hSl) hR)
  intro T _ h
  exact h.2 h.1.1 h.1.2
end ColdStepAtMirrorFrames
end YangMills.Construction
end
