import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtANearFlatTopProof
import YangMills.Construction.ColdStepAtMirrorFrames.MotionsOfTwoNearCurves
import YangMills.Construction.ColdStepAtMirrorFrames.NearPartsOfTwoTops
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages YangMills.Construction.Estimates
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace NearMotionComponents
theorem expUnit_zero_eq_one : expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
variable {F : BlockFrame}
theorem expUnit_motion_eq (w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (c : Fin 2 → F.Site F.top × Fin 4)
    (X : Fin 2 → imaginaryQuaternions) (τ : Fin 2 → ℝ) (α : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (x : F.Site F.depth) (i : Fin 4)
    (ht : ¬ IsAxialTreeBond (x, i))
    (h : chartedField w' (leftTranslate (bondSpread c X τ) V) = leftTranslate α (chartedField w V)) :
    expUnit (α x i) = expUnit (w' x i) * expUnit (crossingMove c X x i τ) * (expUnit (w x i))⁻¹ := by
  classical
  have h1 := congrFun (congrFun h x) i
  simp only [leftTranslate, chartedField] at h1
  by_cases hc : IsCrossingBond (x, i)
  · simp only [if_pos hc] at h1
    have e : crossingMove c X x i τ = bondSpread c X τ (enclosingCell x) i := by
      simp only [crossingMove]
      rw [if_pos hc]
    rw [e]
    have h2 : expUnit (w' x i) * expUnit (bondSpread c X τ (enclosingCell x) i) = expUnit (α x i) * expUnit (w x i) := by
      have := congrArg (fun g => g * (V (enclosingCell x) i)⁻¹) h1
      simpa [mul_assoc] using this
    rw [h2]
    group
  · have e : crossingMove c X x i τ = 0 := by
      simp only [crossingMove]
      rw [if_neg hc]
    rw [e, expUnit_zero_eq_one, mul_one]
    simp only [if_neg hc, if_neg ht] at h1
    rw [h1]
    group
theorem crossingMove_eq_clm (c : Fin 2 → F.Site F.top × Fin 4) (X : Fin 2 → imaginaryQuaternions)
    (hX : AreUnitVectors X) (x : F.Site F.depth) (i : Fin 4) :
    ∃ Λ : (Fin 2 → ℝ) →L[ℝ] imaginaryQuaternions, crossingMove c X x i = Λ ∧ ∀ l, ‖Λ (Pi.single l 1)‖ ≤ 1 := by
  classical
  by_cases hc : IsCrossingBond (x, i)
  · refine ⟨∑ l, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) l).smulRight
      (if c l = (enclosingCell x, i) then X l else 0), ?_, fun l => ?_⟩
    · funext τ
      simp only [crossingMove, if_pos hc, bondSpread]
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs <;> simp
    · simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
      rw [Finset.sum_eq_single l]
      · simp only [Pi.single_eq_same, one_smul]
        split_ifs
        · exact (hX l).le
        · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
  · refine ⟨0, ?_, fun l => by simp⟩
    funext τ
    simp [crossingMove, if_neg hc]
theorem mixedPartial_single_clm (Λ : (Fin 2 → ℝ) →L[ℝ] imaginaryQuaternions) (l : Fin 2) :
    mixedPartial (⇑Λ) ![l] = Λ (Pi.single l 1) := by
  unfold mixedPartial
  rw [iteratedFDeriv_one_apply, Λ.fderiv]
  rfl
theorem mixedPartial_pair_clm (Λ : (Fin 2 → ℝ) →L[ℝ] imaginaryQuaternions) : mixedPartial (⇑Λ) ![0, 1] = 0 := by
  unfold mixedPartial
  rw [iteratedFDeriv_two_apply]
  have e : fderiv ℝ (⇑Λ) = fun _ => Λ := by
    funext z
    exact Λ.fderiv
  rw [e]
  simp
theorem fderiv_comp_line {E P : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P]
    (φ : P → E) (v : P) (h : DifferentiableAt ℝ φ 0) :
    fderiv ℝ (fun s : Fin 1 → ℝ => φ (s 0 • v)) 0 (Pi.single 0 1) = fderiv ℝ φ 0 v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.fderiv_line <;> assumption
theorem bondSpread_smul_single {j : ℕ} (c : Fin 2 → F.Site j × Fin 4) (X : Fin 2 → imaginaryQuaternions) (l : Fin 2)
    (s : Fin 1 → ℝ) :
    bondSpread c X (s 0 • Pi.single l 1) = bondSpread ![c l] ![X l] s := by
  classical
  funext y i
  have r : bondSpread ![c l] ![X l] s y i = if c l = (y, i) then s 0 • X l else 0 := by
    show (∑ m : Fin 1, if (![c l] : Fin 1 → _) m = (y, i) then s m • (![X l] : Fin 1 → imaginaryQuaternions) m else 0) = _
    rw [Fin.sum_univ_one]
    rfl
  rw [r]
  show (∑ m, if c m = (y, i) then (s 0 • (Pi.single l 1 : Fin 2 → ℝ)) m • X m else 0) = _
  rw [Finset.sum_eq_single l]
  · by_cases e : c l = (y, i) <;> simp [e]
  · intro m _ hm
    by_cases e : c m = (y, i) <;> simp [e, Pi.single_eq_of_ne hm]
  · simp
theorem fderiv_bondSpread_single {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : F.GaugeField F.top → E)
    (V : F.GaugeField F.top) (c : Fin 2 → F.Site F.top × Fin 4) (X : Fin 2 → imaginaryQuaternions) (l : Fin 2)
    (h : DifferentiableAt ℝ (fun τ : Fin 2 → ℝ => G (leftTranslate (bondSpread c X τ) V)) 0) :
    fderiv ℝ (fun τ : Fin 2 → ℝ => G (leftTranslate (bondSpread c X τ) V)) 0 (Pi.single l 1) =
      bondDeriv G V ![c l] ![X l] := by
  unfold bondDeriv
  have h1 : iteratedFDeriv ℝ 1 (fun τ : Fin 1 → ℝ => G (leftTranslate (bondSpread ![c l] ![X l] τ) V)) 0
      (fun l' => Pi.single l' 1) =
      fderiv ℝ (fun τ : Fin 1 → ℝ => G (leftTranslate (bondSpread ![c l] ![X l] τ) V)) 0 (Pi.single 0 1) :=
    iteratedFDeriv_one_apply _
  rw [h1]
  have e : (fun s : Fin 1 → ℝ => G (leftTranslate (bondSpread ![c l] ![X l] s) V)) =
      fun s : Fin 1 → ℝ => (fun τ : Fin 2 → ℝ => G (leftTranslate (bondSpread c X τ) V)) (s 0 • Pi.single l 1) := by
    funext s
    show _ = G (leftTranslate (bondSpread c X (s 0 • Pi.single l 1)) V)
    rw [bondSpread_smul_single]
  rw [e, fderiv_comp_line _ _ h]
theorem mixedPartial_single (p : (Fin 2 → ℝ) → imaginaryQuaternions) (l : Fin 2) :
    mixedPartial p ![l] = fderiv ℝ p 0 (Pi.single l 1) := by
  unfold mixedPartial
  rw [iteratedFDeriv_one_apply]
  rfl
end NearMotionComponents
open NearMotionComponents in
set_option maxHeartbeats 1000000 in
theorem nearMotionComponentsOfTwoTops_proof (hM : ConjugatedCurveDerivStability) :
    NearMotionComponentsOfTwoTops := by
  intro K hK
  obtain ⟨C, hC, hall⟩ := hM K (by linarith)
  refine ⟨C, hC, ?_⟩
  intro F F' w w' V V' c c' X α α' x x' i ε hε hX ht ht' h0 h0' hCa hCa' hw hw' hu hu' hid hid' hv hK1 hK1' hK2 hK2' hd0 hd1 hd2
  have hsp0 : ∀ {G : BlockFrame} (c : Fin 2 → G.Site G.top × Fin 4) (U : G.GaugeField G.top),
      leftTranslate (bondSpread c X 0) U = U := by
    intro G c U
    funext y j
    simp [leftTranslate, bondSpread, expUnit_zero_eq_one]
  obtain ⟨Λ, hΛ, hΛ1⟩ := crossingMove_eq_clm c X hX x i
  set u : (Fin 2 → ℝ) → imaginaryQuaternions := fun τ => w (leftTranslate (bondSpread c X τ) V) x i with hudef
  set u' : (Fin 2 → ℝ) → imaginaryQuaternions := fun τ => w' (leftTranslate (bondSpread c' X τ) V') x' i with hudef'
  have hu0 : u 0 = w V x i := by simp only [hudef, hsp0]
  have hu0' : u' 0 = w' V' x' i := by simp only [hudef', hsp0]
  have hp : ∀ l, mixedPartial u ![l] = bondDeriv (fun U => w U x i) V ![c l] ![X l] := fun l => by
    rw [mixedPartial_single]
    exact fderiv_bondSpread_single (fun U => w U x i) V c X l (hw.differentiableAt (by norm_num))
  have hp' : ∀ l, mixedPartial u' ![l] = bondDeriv (fun U => w' U x' i) V' ![c' l] ![X l] := fun l => by
    rw [mixedPartial_single]
    exact fderiv_bondSpread_single (F := F') (fun U => w' U x' i) V' c' X l (hw'.differentiableAt (by norm_num))
  have hq : mixedPartial u ![0, 1] = bondDeriv (fun U => w U x i) V c X := by
    unfold mixedPartial bondDeriv
    congr 1
    funext m
    fin_cases m <;> rfl
  have hq' : mixedPartial u' ![0, 1] = bondDeriv (fun U => w' U x' i) V' c' X := by
    unfold mixedPartial bondDeriv
    congr 1
    funext m
    fin_cases m <;> rfl
  have hCv : ContDiffAt ℝ 3 (⇑Λ) 0 := Λ.contDiff.contDiffAt
  have hres := hall (fun τ => α τ x i) (fun τ => α' τ x' i) u u' (⇑Λ) ε hε (h0 x i) (h0' x' i) (map_zero Λ) hCa hCa' hw hw' hCv
    (hid.mono fun τ h => by
      have := expUnit_motion_eq (w V) (w (leftTranslate (bondSpread c X τ) V)) V c X τ (α τ) x i ht h
      rw [hu0, ← hΛ]
      exact this)
    (hid'.mono fun τ h => by
      have := expUnit_motion_eq (w' V') (w' (leftTranslate (bondSpread c' X τ) V')) V' c' X τ (α' τ) x' i ht' h
      rw [hu0', ← hΛ, hv]
      exact this)
    (by rw [hu0]; exact hu) (by rw [hu0']; exact hu')
    (fun l => by rw [hp]; exact hK1 l) (fun l => by rw [hp']; exact hK1' l)
    (fun l => by rw [mixedPartial_single_clm]; exact (hΛ1 l).trans hK)
    (by rw [hq]; exact hK2) (by rw [hq']; exact hK2') (by rw [mixedPartial_pair_clm]; simpa using (by linarith : (0 : ℝ) ≤ K))
    (by rw [hu0, hu0']; exact hd0) (fun l => by rw [hp, hp']; exact hd1 l) (by rw [hq, hq']; exact hd2)
  exact hres
end YangMills.Construction.ColdStepAtMirrorFrames
end
