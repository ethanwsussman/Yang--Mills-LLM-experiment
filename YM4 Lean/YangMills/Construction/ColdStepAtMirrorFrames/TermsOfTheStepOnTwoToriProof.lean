import YangMills.Construction.ColdStepAtMirrorFrames.CommonBondsOfTwoToriProof
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionsInValueOnTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.GapPartOnTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.HaarPartOnTwoToriProof
import YangMills.Construction.ColdStepAtMirrorFrames.MeansFrozenInValueProofForm
import YangMills.Construction.ColdStepAtMirrorFrames.SlopePartOnTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.TermsOfTheStepOnTwoTori
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace StepTermsOnTwoTori
variable {F F' : BlockFrame}
theorem mem_centredCube_odd (R : ℕ) (h : Fin 4 → ℤ) :
    h ∈ centredCube (2 * R + 1) ↔ ∀ i, |h i| ≤ (R : ℤ) := by apply _root_.YangMills.Construction.HoleSavings.mem_centredCube_odd <;> assumption
theorem siteOfCoords_injective {n : ℕ} (hs : ∀ i, F.extent i = n) {Y : F.Cell} {c c' : Fin 4 → ℤ}
    (h : ∀ i, 2 * |c i - c' i| < n) (he : Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top c = Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top c') :
    c = c' := by apply _root_.YangMills.SharedProofs.p11813 <;> assumption
section ZeroExtension
variable {Λ ι : Type} [Fintype Λ] [DecidableEq Λ] [Fintype ι] [DecidableEq ι] {e : Λ → ι}
theorem zeroExtensionL_apply (he : Function.Injective e) (ζ : BondField Λ) (l : Λ) :
    zeroExtensionL e ζ (e l) = ζ l := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ValueFreezing.zeroExtension_apply_self <;> assumption
theorem zeroExtensionL_of_not_mem_range {b : ι} (hb : b ∉ Set.range e) (ζ : BondField Λ) :
    zeroExtensionL e ζ b = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ValueFreezing.zeroExtension_apply_off <;> assumption
theorem sum_eq_sum_comp_of_injective (he : Function.Injective e) (G : ι → ℝ)
    (h : ∀ b, b ∉ Set.range e → G b = 0) :
    ∑ b, G b = ∑ l, G (e l) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ValueFreezing.sum_eq_sum_comp_of_vanish <;> assumption
end ZeroExtension
theorem cellQuadratic_zeroExtension {lam x : ℝ} {r n : ℕ} {Y₀ : F.Cell}
    (hs : ∀ i, F.extent i = n) (hr : 2 * r + 2 < n) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (e : Λ → ↥(chordBonds (finiteCells F))) (he : Function.Injective e) (off : Λ → Fin 4 → ℤ)
    (hoff : ∀ q, off q ∈ centredCube (2 * (r / 2) + 1))
    (hplace : ∀ q, enclosingCell (e q).1.1 = Y₀ + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top (off q))
    (c : Fin 4 → ℤ) (hc : c ∈ centredCube (2 * (r / 8) + 1)) (ζ : BondField Λ) :
    cellQuadratic lam x (Y₀ + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top c) (zeroExtensionL e ζ) =
      x * lam / 2 * ∑ q, if off q = c then ‖ζ q‖ ^ 2 else 0 := by
  classical
  unfold cellQuadratic
  rw [sum_eq_sum_comp_of_injective he _
    (fun b hb => by simp [zeroExtensionL_of_not_mem_range hb]), Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hiff : enclosingCell (e q).1.1 = Y₀ + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top c ↔ off q = c := by
    rw [hplace]
    constructor
    · intro h
      refine _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepTermsOnTwoTori.siteOfCoords_injective hs (fun i => ?_) h
      have h1 := (mem_centredCube_odd _ _).mp (hoff q) i
      have h2 := (mem_centredCube_odd _ _).mp hc i
      have h3 := abs_sub (off q i) (c i)
      omega
    · intro h
      rw [h]
  by_cases h : off q = c
  · rw [if_pos (hiff.mpr h), if_pos h, zeroExtensionL_apply he]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
    simp
theorem abs_sub_sub_sub_le (a b c a' b' c' : ℝ) :
    |a - b - c - (a' - b' - c')| ≤ |a - a'| + |b - b'| + |c - c'| := by
  have e : a - b - c - (a' - b' - c') = (a - a') - (b - b') - (c - c') := by ring
  rw [e]
  have h1 := abs_sub ((a - a') - (b - b')) (c - c')
  have h2 := abs_sub (a - a') (b - b')
  linarith
theorem add_siteOfCoords_zero (Y : F.Cell) : Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top (fun _ => (0 : ℤ)) = Y := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TorusBonds.add_siteOfCoords_zero <;> assumption
theorem cellExponent_eq {star : Bool} {a ρA x : ℝ} {m : ℕ} (Y : F.Cell) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    cellExponent star a ρA x m Y V η =
      slopeComponent star a ρA x m Y V η - kernelGapComponent star a ρA x m Y V η -
        haarComponent star a ρA m Y V η := rfl
end StepTermsOnTwoTori
open StepTermsOnTwoTori in
theorem stepTermsCloseOnTwoTori_proof (hS : SiteDecomposition) (hCB : commonBondsOfTwoTori)
    (hJ : EventuallyInParametersCombines) (hA : SlopeComponentsCloseOnTwoTori)
    (hB : gapComponentsCloseOnTwoTori) (hC : HaarComponentsCloseEventually)
    (hD : CellExpansionsCloseInValueOnTwoTori) :
    StepTermsCloseOnTwoTori := by
  have hfl : EventuallyInParameters fun T => 0 ≤ T.Ct ∧ 2 ≤ T.n₀ ∧ 1 ≤ T.coupling := by
    intro a _
    exact ⟨0, fun L _ _ c _ => ⟨0, fun Ct hCt => ⟨1, one_pos, fun κ _ _ => ⟨1, one_pos, fun η₃ _ _ _ =>
      ⟨0, fun nss _ => ⟨1, one_pos, fun σ _ _ p _ => ⟨0, fun Cs _ E _ => ⟨2, fun n₀ hn => ⟨0, fun CE _ =>
        ⟨1, fun y hy => ⟨hCt, hn, hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have j := hJ.1 _ _ hA (hJ.1 _ _ hB (hJ.1 _ _ hC (hJ.1 _ _ hD hfl)))
  refine hJ.2 _ _ (fun T hd ⟨pA, pB, pC, pD, hCt, hn₀, hy₁⟩ => ?_) j
  intro t x f F F' V V' Y Y' r star v hy hrow hF hF' hV hV' hag hr hv0 hv1
  have two : AgreeingTopPair T t x V V' Y Y' r := ⟨hy, hF, hF', hV, hV', hag, hr⟩
  obtain ⟨hFL, _, n, hs, hnn⟩ := hF
  obtain ⟨hFL', _, n', hs', hnn'⟩ := hF'
  have hO : Odd T.L := hd.odd_L
  have hOF : Odd F.blockSide := hFL ▸ hO
  have hOF' : Odd F'.blockSide := hFL' ▸ hO
  have hn2 : 2 ≤ n := hn₀.trans hnn
  have hn2' : 2 ≤ n' := hn₀.trans hnn'
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hs]; exact hn2
  have hs2' : ∀ i, 2 ≤ F'.extent i := fun i => by rw [hs']; exact hn2'
  have hrn : 2 * r + 2 < n := by
    rcases hag.1 0 with h | h
    · rw [hs] at h
      omega
    · rwa [hs] at h
  have hrn' : 2 * r + 2 < n' := by
    rcases hag.2.1 0 with h | h
    · rw [hs'] at h
      omega
    · rwa [hs'] at h
  have hcb := (hCB T.L hO).2 F F' Y Y' r n n' hFL hFL' hs hs' hrn hrn'
  have hx0 : 0 ≤ x := by linarith
  have mem₁ : ∀ q : ↥(commonBondOffsets Y Y' (r / 2)),
      q.1.1 ∈ centredCube (2 * (r / 2) + 1) ∧ q.1.2.1 ∈ centredCube F.blockSide := fun q => by
    have := (Finset.mem_filter.mp q.2).1
    simp only [Finset.mem_product, Finset.mem_univ, and_true] at this
    exact this
  have hLL : F.blockSide = F'.blockSide := hFL.trans hFL'.symm
  have place : ∀ q : ↥(commonBondOffsets Y Y' (r / 2)),
      enclosingCell (commonBondLeft Y Y' (r / 2) q).1.1 = Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top q.1.1 :=
    fun q => ((hS F hOF hs2).1 _ _ (mem₁ q).2).1
  have place' : ∀ q : ↥(commonBondOffsets Y Y' (r / 2)),
      enclosingCell (commonBondRight Y Y' (r / 2) q).1.1 = Y' + _root_.YangMills.Construction.BlockAverages.siteOfCoords F'.top q.1.1 :=
    fun q => ((hS F' hOF' hs2').1 _ _ (hLL ▸ (mem₁ q).2)).1
  have sqeq : ∀ (c : ↥(centredCube (2 * (r / 8) + 1))) (ζ : BondField ↥(commonBondOffsets Y Y' (r / 2))),
      cellQuadratic T.chainParams.lam x (offsetCell Y (r / 8) c) (zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ) =
        cellQuadratic T.chainParams.lam x (offsetCell Y' (r / 8) c)
          (zeroExtensionL (commonBondRight Y Y' (r / 2)) ζ) := fun c ζ => by
    change cellQuadratic T.chainParams.lam x (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top c.1) _ =
      cellQuadratic T.chainParams.lam x (Y' + _root_.YangMills.Construction.BlockAverages.siteOfCoords F'.top c.1) _
    rw [cellQuadratic_zeroExtension hs hrn _ hcb.injective_left (fun q => q.1.1)
        (fun q => (mem₁ q).1) place c.1 c.2,
      cellQuadratic_zeroExtension hs' hrn' _ hcb.injective_right (fun q => q.1.1)
        (fun q => (mem₁ q).1) place' c.1 c.2]
  have hA' := pA t x F F' V V' Y Y' r star two
  have hB' := pB t x F F' V V' Y Y' r star two
  have hC' := pC t x F F' V V' Y Y' r star two
  have hD' := pD t x f F F' V V' Y Y' r star two hrow
  set Ee := Real.exp (-(2 * T.κ * r)) with hEe
  have hEe0 : 0 ≤ Ee := (Real.exp_pos _).le
  have hE₃ : 0 ≤ T.energyRatio := by
    have h1 := hd.η₃_pos
    have h2 := hd.one_le_E
    unfold StepParameters.energyRatio
    positivity
  have sq0 : ∀ (c : F.Cell) (η : StepVariable (finiteCells F)),
      0 ≤ x * weightedSqNormAt T.κ (chordBondCell F) (cellDistReal F) c η + 1 := fun c η => by
    have : 0 ≤ weightedSqNormAt T.κ (chordBondCell F) (cellDistReal F) c η :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (by positivity)
    positivity
  have psi : ∀ (c : ↥(centredCube (2 * (r / 8) + 1))),
      ∀ ζ ∈ openPolyball ↥(commonBondOffsets Y Y' (r / 2)) T.ballRadius,
      |cellExponent star T.a T.chainParams.ρA x (frameRadius x) (offsetCell Y (r / 8) c) V
          (zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ) -
        cellExponent star T.a T.chainParams.ρA x (frameRadius x) (offsetCell Y' (r / 8) c) V'
          (zeroExtensionL (commonBondRight Y Y' (r / 2)) ζ)| ≤
      (3 * (T.Ct / 4) * Ee) * (x * weightedSqNormAt T.κ (chordBondCell F) (cellDistReal F)
        (offsetCell Y (r / 8) c) (zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ) + 1) := fun c ζ hζ => by
    rw [cellExponent_eq, cellExponent_eq]
    have a1 := hA' c ζ hζ
    have a2 := hB' c ζ hζ
    have a3 := hC' c ζ hζ
    refine (abs_sub_sub_sub_le _ _ _ _ _ _).trans ?_
    have : 3 * (T.Ct / 4) * Ee = T.Ct / 4 * Ee + T.Ct / 4 * Ee + T.Ct / 4 * Ee := by ring
    rw [this, add_mul, add_mul]
    exact add_le_add (add_le_add a1 a2) a3
  have c₀mem : (fun _ => (0 : ℤ)) ∈ centredCube (2 * (r / 8) + 1) := by
    rw [mem_centredCube_odd]
    intro i
    rw [abs_zero]
    exact Int.natCast_nonneg _
  have hY : offsetCell Y (r / 8) ⟨_, c₀mem⟩ = Y := add_siteOfCoords_zero Y
  have hY' : offsetCell Y' (r / 8) ⟨_, c₀mem⟩ = Y' := add_siteOfCoords_zero Y'
  have hle₁ : 3 * (T.Ct / 4) * Ee ≤ T.Ct * Ee := by nlinarith [mul_nonneg hCt hEe0]
  refine ⟨⟨fun c ζ hζ => ?_, fun ζ hζ => ?_⟩, ⟨fun c ζ hζ => ?_, fun ζ hζ => ?_⟩⟩
  · have a1 := psi c ζ hζ
    have hs0 := sq0 (offsetCell Y (r / 8) c) (zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ)
    rw [sqeq c ζ]
    have e1 : ∀ p p' q : ℝ, v * p + (1 - v) * q - (v * p' + (1 - v) * q) = v * (p - p') :=
      fun _ _ _ => by ring
    rw [e1, abs_mul, abs_of_nonneg hv0]
    calc _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hv1 (abs_nonneg _)
      _ ≤ _ := by
        rw [one_mul]
        exact a1.trans (mul_le_mul_of_nonneg_right hle₁ hs0)
  · have a1 := psi ⟨_, c₀mem⟩ ζ hζ
    have e2 := sqeq ⟨_, c₀mem⟩ ζ
    rw [hY, hY'] at a1 e2
    have hs0 := sq0 Y (zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ)
    rw [e2]
    have e1 : ∀ p p' q : ℝ, p - q - (p' - q) = p - p' := fun _ _ _ => by ring
    rw [e1]
    exact a1.trans (mul_le_mul_of_nonneg_right hle₁ hs0)
  · have a1 := psi c ζ hζ
    have a2 := hD' c ζ hζ
    have hs0 := sq0 (offsetCell Y (r / 8) c) (zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ)
    have e1 : ∀ p p' q q' : ℝ, p - v * q - (p' - v * q') = (p - p') - v * (q - q') :=
      fun _ _ _ _ => by ring
    rw [e1]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hv0]
    have a3 : v * |cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f (offsetCell Y (r / 8) c)
        (zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ) V - cellCentredExpansion star T.a T.chainParams.ρA
        (frameRadius x) f (offsetCell Y' (r / 8) c) (zeroExtensionL (commonBondRight Y Y' (r / 2)) ζ) V'| ≤
        (T.Ct * (1 + T.energyRatio) / 4 * Ee) * (x * weightedSqNormAt T.κ (chordBondCell F) (cellDistReal F)
        (offsetCell Y (r / 8) c) (zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ) + 1) :=
      (mul_le_of_le_one_left (abs_nonneg _) hv1).trans a2
    refine (add_le_add a1 a3).trans ?_
    rw [← add_mul]
    apply mul_le_mul_of_nonneg_right _ hs0
    have h4 : 0 ≤ T.Ct * T.energyRatio * Ee := by positivity
    nlinarith [mul_nonneg hCt hEe0]
  · have a2 := hD' ⟨_, c₀mem⟩ ζ hζ
    rw [hY, hY'] at a2
    have hs0 := sq0 Y (zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ)
    refine a2.trans (mul_le_mul_of_nonneg_right ?_ hs0)
    have h4 : 0 ≤ T.Ct * (1 + T.energyRatio) * Ee := by positivity
    nlinarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
