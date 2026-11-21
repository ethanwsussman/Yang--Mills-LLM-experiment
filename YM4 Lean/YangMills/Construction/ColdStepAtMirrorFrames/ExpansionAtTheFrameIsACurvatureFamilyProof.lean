import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtTheFrameIsACurvatureFamily
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceGoesUpALevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages Filter
namespace YangMills.Construction.ColdStepAtMirrorFrames
private theorem torusStepParameters_admissible (T : ColdStepAtMirrorFrames.StepParameters) [NeZero T.L]
    (g : LumpContours.LumpGrid T.L) (hT : T.IsOrdered)
    (hL : 2 ^ 16 ≤ T.L) (hn₀ : 4096 ≤ T.n₀) : (torusStepParameters T g).Admissible := by
  have hLpos : 0 < T.L := by omega
  have hE : 0 < T.E := by linarith [hT.one_le_E]
  refine ⟨hT.one_le_a, hT.odd_L, hL, hT.σ_pos, by norm_num [torusStepParameters], by norm_num [torusStepParameters],
    by norm_num [torusStepParameters], hT.κ_pos, ?_, hE, hT.one_le_E, ?_, ?_, by norm_num [torusStepParameters],
    by norm_num [torusStepParameters], hn₀, ?_, ?_⟩
  · show 0 < (T.L : ℝ) ^ (1 / 640 : ℝ)
    positivity
  · show 11 * 2 ^ 12 * 0 < T.L
    omega
  · show 0 < T.E / T.η₃
    exact div_pos hE hT.η₃_pos
  · show (1 : ℝ) ≤ ((2 : ℝ) ^ 16) ^ 100
    exact one_le_pow₀ (by norm_num)
  · show 2 ^ 16 ≤ TorusLumps.clusterRange (((2 : ℝ) ^ 16) ^ 100)
    unfold TorusLumps.clusterRange
    have hroot : (((2 : ℝ) ^ 16) ^ 100) ^ ((1 : ℝ) / 100) = (2 : ℝ) ^ 16 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hroot]
    exact show ((2 : ℕ) ^ 16 : ℕ) ≤ ⌈(2 : ℝ) ^ 16⌉₊ from by
      have h := Nat.le_ceil ((2 : ℝ) ^ 16)
      exact_mod_cast h
private theorem isSmallCurvature_mono {F : BlockFrame} {j : ℕ} {a b : ℝ} (h : a ≤ b) {W : F.GaugeField j}
    (hW : IsSmallCurvature a W) : IsSmallCurvature b W := fun p hp => lt_of_lt_of_le (hW p hp) h
private theorem uniformField_isSmallCurvature {F : BlockFrame} {j : ℕ} {s : ℝ} (hs : 0 < s) :
    IsSmallCurvature s (uniformField F j) := by apply _root_.YangMills.SharedProofs.p8038 <;> assumption
private theorem bondDeriv_zero {F : BlockFrame} {j : ℕ} (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (c : Fin 0 → F.Site j × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G W c X = G W := by apply _root_.YangMills.SharedProofs.p8307 <;> assumption
private theorem bondDeriv_sub_const {F : BlockFrame} {j k : ℕ} (hk : k ≠ 0) (G : F.GaugeField j → ℝ) (v : ℝ)
    (W : F.GaugeField j) (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv (fun V => G V - v) W c X = bondDeriv G W c X := by
  unfold bondDeriv
  have hfun : (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W) - v) =
      fun τ => (-v) + G (leftTranslate (bondSpread c X τ) W) := by
    funext τ
    ring
  rw [hfun]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hder : (fun y => fderiv ℝ (fun τ : Fin (m + 1) → ℝ => (-v) + G (leftTranslate (bondSpread c X τ) W)) y) =
      fun y => fderiv ℝ (fun τ : Fin (m + 1) → ℝ => G (leftTranslate (bondSpread c X τ) W)) y :=
    funext fun y => fderiv_const_add (-v)
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right, hder]
abbrev _root_.YangMills.SharedProofs.p20334 := @bondDeriv_sub_const
private theorem isCurvatureFamilyOnMultiples_of_regular (hread : TopFamilyOnTori)
    (T : ColdStepAtMirrorFrames.StepParameters) [NeZero T.L]
    (g : LumpContours.LumpGrid T.L) (hT : T.IsOrdered) (hn₀ : 0 < T.n₀) (htrans : expansionTransportAt T)
    (star : Bool) (t : ℕ) (x : ℝ) (f : LocalFamily) (hx : T.coupling ≤ x)
    (hrow : IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f)
    (hD : IsLocalDensity T.L t T.n₀ (5 / 4 * T.σ) (expansionAtFrameFamily T star x f)) :
    TorusLumps.IsCurvatureFamilyOnMultiples (torusStepParameters T g) 1 T.energyRatio
      (densityOfTopFamily T.L t (expansionAtFrameFamily T star x f)) := by
  set G := expansionAtFrameFamily T star x f with hG
  have hσ : 0 < T.σ := hT.σ_pos
  have hσle : T.σ ≤ 5 / 4 * T.σ := by linarith
  have hE : 0 < T.E := by linarith [hT.one_le_E]
  have hEE : T.E ≤ T.energyRatio := by
    show T.E ≤ T.E / T.η₃
    rw [le_div_iff₀ hT.η₃_pos]
    nlinarith [hT.η₃_le_one]
  have hw : ∀ r : ℝ, 0 < torusDecayFactor T.L T.decayRate r := by
    intro r
    unfold torusDecayFactor
    positivity
  obtain ⟨hS, hdec, _, hcen, _⟩ := hread T.L t T.n₀ T.σ G hn₀
  obtain ⟨_, _, hcmpc, _, _⟩ := hread T.L t T.n₀ T.σ (centredFamily G) hn₀
  have hDσ : IsLocalDensity T.L t T.n₀ T.σ G :=
    ⟨fun F hF Y V hV => hD.smooth F hF Y V (isSmallCurvature_mono hσle hV),
      fun F hF Y V γ hV => hD.gauge_invariant F hF Y V γ (isSmallCurvature_mono hσle hV),
      fun F hF Y h V hV => hD.translation_invariant F hF Y h V (isSmallCurvature_mono hσle hV)⟩
  have hDec : DerivDecay T.L t T.n₀ T.σ G (fun _ n => T.energyRatio / torusDecayFactor T.L T.decayRate n) := by
    intro F hF Y V k c X hV h1 h3 hX
    obtain ⟨hTr, _⟩ := htrans t x f F V hx hrow hF (isSmallCurvature_mono hσle hV) star
    have hball : InBallProduct T.ballRadius (0 : StepVariable (finiteCells F)) := by
      intro b
      have hρ : 0 < T.ballRadius := by
        show 0 < T.σ / 64
        positivity
      simpa using hρ
    rcases (by omega : k ≤ 2 ∨ k = 3) with hk | rfl
    · refine (hTr.lowDeriv Y k c X h1 hk hX).trans ?_
      apply div_le_div_of_nonneg_right _ (hw _).le
      nlinarith
    · refine (hTr.thirdDeriv Y 0 c X hball hX).trans ?_
      apply div_le_div_of_nonneg_right _ (hw _).le
      nlinarith
  have hCmp : IsLocalOnTori T.L t T.n₀ T.σ (centredFamily G)
      (fun r => T.energyRatio / torusDecayFactor T.L T.decayRate r) := by
    intro F F' hF hF' Y Y' V V' r k h X hV hV' hA hk hb hX
    obtain ⟨_, hloc⟩ := htrans t x f F V hx hrow hF (isSmallCurvature_mono hσle hV) star
    have h1 := hloc F' V' Y Y' r hF' (isSmallCurvature_mono hσle hV') hA k h X hk hb hX
    by_cases hk0 : k = 0
    · subst hk0
      obtain ⟨_, hloc₀⟩ := htrans t x f F (uniformField F F.top) hx hrow hF
        (uniformField_isSmallCurvature (by positivity)) star
      have hA₀ : AgreeOnBall (finiteCells F) (uniformField F F.top) (finiteCells F') (uniformField F' F'.top) Y Y' r :=
        ⟨hA.1, hA.2.1, hA.2.2.1, fun _ _ => rfl⟩
      have h2 := hloc₀ F' (uniformField F' F'.top) Y Y' r hF' (uniformField_isSmallCurvature (by positivity)) hA₀
        0 h X hk hb hX
      rw [bondDeriv_zero, bondDeriv_zero] at h1 h2 ⊢
      show |(G F Y V - G F Y (uniformField F F.top)) - (G F' Y' V' - G F' Y' (uniformField F' F'.top))| ≤ _
      have h3 : |(G F Y V - G F Y (uniformField F F.top)) - (G F' Y' V' - G F' Y' (uniformField F' F'.top))| ≤
          |G F Y V - G F' Y' V'| + |G F Y (uniformField F F.top) - G F' Y' (uniformField F' F'.top)| := by
        have hre : (G F Y V - G F Y (uniformField F F.top)) - (G F' Y' V' - G F' Y' (uniformField F' F'.top)) =
            (G F Y V - G F' Y' V') - (G F Y (uniformField F F.top) - G F' Y' (uniformField F' F'.top)) := by ring
        rw [hre]
        exact abs_sub _ _
      refine h3.trans ((add_le_add h1 h2).trans ?_)
      have hwr := hw (r : ℝ)
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hwr.le
      nlinarith
    · have e1 : bondDeriv (centredFamily G F Y) V (bondsAt Y h) X = bondDeriv (G F Y) V (bondsAt Y h) X :=
        bondDeriv_sub_const hk0 (G F Y) _ V _ X
      have e2 : bondDeriv (centredFamily G F' Y') V' (bondsAt Y' h) X = bondDeriv (G F' Y') V' (bondsAt Y' h) X :=
        bondDeriv_sub_const hk0 (G F' Y') _ V' _ X
      rw [e1, e2]
      refine h1.trans ?_
      apply div_le_div_of_nonneg_right _ (hw _).le
      nlinarith
  obtain ⟨s1, s2, s3⟩ := hS hDσ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun n _ hn _ y W hW => s1 n hn y W hW
  · exact fun n _ hn _ y γ W hW => s2 n hn y γ W hW
  · exact fun n _ hn _ y u W hW => s3 n hn y u W hW
  · exact fun n _ hn _ y W hW k c X h1 h3 hX => hdec _ hDec n hn y W hW k c X h1 h3 hX
  · intro n n' _ _ hn hn' _ _ y y' V V' m h1 h2 hV hV' hA k h X hk hbox hX
    have h3 := hcmpc _ hCmp n n' hn hn' y y' V V' m h1 h2 hV hV' hA k h X hk hbox hX
    have hc : ∀ (n : ℕ) [NeZero n] (y : TorusFields.TorusSite n),
        densityOfTopFamily T.L t (centredFamily G) n y = TorusLumps.centered (densityOfTopFamily T.L t G) n y := by
      intro n _ y
      funext V
      exact hcen n y V
    rw [hc, hc] at h3
    exact h3
theorem expansionAtFrameIsCurvatureFamily_of_topFamilyOnTori (hread : TopFamilyOnTori) :
    expansionAtFrameIsCurvatureFamily := by
  intro T _ g hT hL hn₀
  refine ⟨torusStepParameters_admissible T g hT hL hn₀, fun htr star t x f hx hrow hD => ?_⟩
  exact isCurvatureFamilyOnMultiples_of_regular hread T g hT (by omega) htr star t x f hx hrow hD
end YangMills.Construction.ColdStepAtMirrorFrames
end
