import YangMills.Construction.SummableBoundsOfTheFlow.LeastChartEnergyIsSmoothProof
import YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivativeAlongFieldsProofForm
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheDilation
import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionHasTheConditionsOfThirdOrderProof
import YangMills.Construction.SummableBoundsOfTheFlow.RimMomentsOfALawProof
import Mathlib
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation
namespace YangMills.Construction.Dilation
section Top
variable {F : BlockFrame}
def topTranslated {Zp : Type} (G : Zp → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (p : Zp × (Fin k → ℝ)) : ℝ :=
  G p.1 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X p.2) V)
abbrev basisVectors (k : ℕ) : Fin k → Fin k → ℝ := fun l => Pi.single l 1
def jointLinearMap {l : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F))) (e : Fin l → EuclideanSpace ℝ (Fin 3))
    (k : ℕ) : (Fin (l + k) → ℝ) →L[ℝ] StepVariable (finiteCells F) × (Fin k → ℝ) :=
  ContinuousLinearMap.prod
    (∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (l + k) => ℝ) (Fin.castAdd k i)).smulRight
      (bondVariation (b i) (e i)))
    (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Fin.natAdd l j))
theorem jointDisplacement_eq {l k : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (e : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    jointDisplacement G η V b e c X = fun τ => topTranslated G V c X (jointLinearMap b e k τ + (η, 0)) := by
  funext τ
  simp only [jointDisplacement, topTranslated, jointLinearMap, displacedPoint]
  congr 1
  · simp only [ContinuousLinearMap.prod_apply, Prod.fst_add, sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [bondVariation]
    rw [Pi.single_smul]
  · congr 2
    funext j
    simp
theorem jointLinearMap_single_castAdd {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (e : Fin l → EuclideanSpace ℝ (Fin 3)) (i : Fin l) :
    jointLinearMap b e k (Pi.single (Fin.castAdd k i) 1) = (bondVariation (b i) (e i), 0) := by
  simp only [jointLinearMap, ContinuousLinearMap.prod_apply, sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  refine Prod.ext ?_ ?_
  · simp only
    rw [Finset.sum_eq_single i]
    · simp
    · intro i' _ hne
      have : Fin.castAdd k i' ≠ Fin.castAdd k i := fun h => hne (Fin.castAdd_injective _ _ h)
      simp [Pi.single_apply, this]
    · simp
  · funext j
    have : Fin.natAdd l j ≠ Fin.castAdd k i := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [Pi.single_apply, this]
theorem jointLinearMap_single_natAdd {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (e : Fin l → EuclideanSpace ℝ (Fin 3)) (j : Fin k) :
    jointLinearMap b e k (Pi.single (Fin.natAdd l j) 1) = (0, Pi.single j 1) := by
  simp only [jointLinearMap, ContinuousLinearMap.prod_apply, sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  refine Prod.ext ?_ ?_
  · simp only
    refine Finset.sum_eq_zero fun i _ => ?_
    have : Fin.castAdd k i ≠ Fin.natAdd l j := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [Pi.single_apply, this]
  · funext j'
    by_cases h : j' = j
    · subst h; simp
    · have : Fin.natAdd l j' ≠ Fin.natAdd l j := fun h' => h (Fin.natAdd_injective _ _ h')
      simp [Pi.single_apply, this, h]
theorem jointMixedDeriv_eq_iteratedFDeriv_secondJet {l k : ℕ}
    (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (e : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hf : ContDiffAt ℝ (l + k : ℕ) (topTranslated G V c X) (η, 0)) :
    jointMixedDeriv G η V b e c X =
      iteratedFDeriv ℝ l (secondJet (topTranslated G V c X) 0 (basisVectors k)) η
        fun i => bondVariation (b i) (e i) := by
  have h := iteratedFDeriv_comp_linear_add_eval (jointLinearMap b e k) (η, 0) (x := 0) (f := topTranslated G V c X)
    (by simpa using hf) le_rfl (fun i => Pi.single i 1)
  simp only [jointMixedDeriv]
  rw [jointDisplacement_eq, h]
  simp only [map_zero, zero_add]
  refine (iteratedFDeriv_secondJet (basisVectors k) l (l + k) _ _ η
    ⟨rfl, fun i hi => ?_, fun i hi hk => ?_⟩ hf le_rfl).symm
  · have this : i = Fin.castAdd k ⟨i.val, hi⟩ := Fin.ext rfl
    have h2 := jointLinearMap_single_castAdd (k := k) b e ⟨i.val, hi⟩
    rwa [← this] at h2
  · have this : i = Fin.natAdd l ⟨i.val - l, hk⟩ := Fin.ext (by simp; omega)
    have h2 := jointLinearMap_single_natAdd (l := l) b e ⟨i.val - l, hk⟩
    rwa [← this] at h2
abbrev ChordCoord (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F)) × Fin 3
def chordBasis (α : ChordCoord F) : StepVariable (finiteCells F) :=
  bondVariation α.1 (EuclideanSpace.single α.2 1)
def chordCoord (α : ChordCoord F) : StepVariable (finiteCells F) →L[ℝ] ℝ :=
  (EuclideanSpace.proj α.2).comp (ContinuousLinearMap.proj α.1)
theorem chordCoord_apply (α : ChordCoord F) (ζ : StepVariable (finiteCells F)) :
    chordCoord α ζ = ζ α.1 α.2 := rfl
theorem sum_chordCoord_smul_chordBasis (ζ : StepVariable (finiteCells F)) :
    ζ = ∑ α : ChordCoord F, chordCoord α ζ • chordBasis α := by
  funext b
  ext a
  have h1 : ∀ (b' : ↥(chordBonds (finiteCells F))) (a' : Fin 3),
      ((chordCoord (b', a') ζ • chordBasis (b', a') : StepVariable (finiteCells F)) b) a =
        if b' = b then (if a' = a then ζ b' a' else 0) else 0 := by
    intro b' a'
    simp only [chordCoord_apply, chordBasis, bondVariation, Pi.smul_apply, Pi.single_apply]
    by_cases hb : b = b'
    · subst hb
      by_cases ha : a' = a
      · subst ha; simp
      · simp [ha, EuclideanSpace.single_apply, Ne.symm ha]
    · simp [hb, Ne.symm hb]
  have h2 : (∑ α : ChordCoord F, chordCoord α ζ • chordBasis α) b a =
      ∑ α : ChordCoord F, ((chordCoord α ζ • chordBasis α : StepVariable (finiteCells F)) b) a := by
    simp [Finset.sum_apply]
  rw [h2, Fintype.sum_prod_type]
  simp only [h1]
  simp
def unitI : imaginaryQuaternions := ⟨⟨0, 1, 0, 0⟩, rfl⟩
theorem norm_coe_unitI : ‖(unitI : Quaternion ℝ)‖ = 1 := by apply _root_.YangMills.Construction.ChartedEnergyRegularity.norm_coe_imaginaryUnit <;> assumption
theorem norm_unitI : ‖unitI‖ = 1 := norm_coe_unitI
def doubledIndex (F : BlockFrame) (i : Fin (Fintype.card (ChordCoord F) + Fintype.card (ChordCoord F))) :
    ChordCoord F :=
  (Fintype.equivFin (ChordCoord F)).symm
    (Fin.addCases (motive := fun _ => Fin (Fintype.card (ChordCoord F))) (fun j => j) (fun j => j) i)
def doubledBond (F : BlockFrame) (i : Fin (Fintype.card (ChordCoord F) + Fintype.card (ChordCoord F))) :
    ↥(chordBonds (finiteCells F)) := (doubledIndex F i).1
def doubledUnit (F : BlockFrame) (i : Fin (Fintype.card (ChordCoord F) + Fintype.card (ChordCoord F))) :
    EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (doubledIndex F i).2 1
theorem norm_doubledUnit (F : BlockFrame) (i) : ‖doubledUnit F i‖ = 1 := by
  simp [doubledUnit]
def doubledParams (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) :
    Fin ((Fintype.card (ChordCoord F) + Fintype.card (ChordCoord F)) + (k + n)) → ℝ :=
  Fin.addCases
    (fun a => Fin.addCases (motive := fun _ => ℝ)
      (fun a₁ => chordCoord ((Fintype.equivFin (ChordCoord F)).symm a₁) (p.1 - η)) (fun _ => 0) a)
    (fun d => Fin.addCases (motive := fun _ => ℝ) (fun j => s j * p.2 j) (fun _ => 0) d)
theorem doubledParams_chord (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (a : Fin (Fintype.card (ChordCoord F))) :
    doubledParams F η s n p (Fin.castAdd (k + n) (Fin.castAdd _ a)) =
      chordCoord ((Fintype.equivFin (ChordCoord F)).symm a) (p.1 - η) := by
  simp only [doubledParams, Fin.addCases_left]
theorem doubledParams_spare (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (a : Fin (Fintype.card (ChordCoord F))) :
    doubledParams F η s n p (Fin.castAdd (k + n) (Fin.natAdd _ a)) = 0 := by
  simp only [doubledParams, Fin.addCases_left, Fin.addCases_right]
theorem doubledParams_top (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (j : Fin k) :
    doubledParams F η s n p (Fin.natAdd _ (Fin.castAdd n j)) = s j * p.2 j := by
  simp only [doubledParams, Fin.addCases_left, Fin.addCases_right]
theorem doubledParams_pad (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (j : Fin n) :
    doubledParams F η s n p (Fin.natAdd _ (Fin.natAdd k j)) = 0 := by
  simp only [doubledParams, Fin.addCases_right]
theorem doubledParams_contDiff (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ)
    (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (doubledParams F η s n) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.addCases (fun a => ?_) (fun d => ?_) i
  · refine Fin.addCases (fun a₁ => ?_) (fun a₂ => ?_) a
    · simp only [doubledParams_chord]
      exact (chordCoord _).contDiff.comp (contDiff_fst.sub contDiff_const)
    · simp only [doubledParams_spare]
      exact contDiff_const
  · refine Fin.addCases (fun j => ?_) (fun a₂ => ?_) d
    · simp only [doubledParams_top]
      exact contDiff_const.mul ((contDiff_apply ℝ ℝ j).comp contDiff_snd)
    · simp only [doubledParams_pad]
      exact contDiff_const
theorem doubledParams_base_eq_zero (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ}
    (s : Fin k → ℝ) (n : ℕ) : doubledParams F η s n (η, 0) = 0 := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun d => ?_) i
  · refine Fin.addCases (fun a₁ => ?_) (fun a₂ => ?_) a
    · rw [doubledParams_chord]; simp
    · rw [doubledParams_spare]; rfl
  · refine Fin.addCases (fun j => ?_) (fun a₂ => ?_) d
    · rw [doubledParams_top]; simp
    · rw [doubledParams_pad]; rfl
theorem displacedPoint_doubledParams (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ}
    (s : Fin k → ℝ) (n : ℕ) (p : StepVariable (finiteCells F) × (Fin k → ℝ)) :
    displacedPoint η (doubledBond F) (doubledUnit F)
      (fun i => doubledParams F η s n p (Fin.castAdd (k + n) i)) = p.1 := by
  simp only [displacedPoint]
  rw [Fin.sum_univ_add]
  have h2 : ∑ i, (Pi.single (doubledBond F (Fin.natAdd _ i))
      (doubledParams F η s n p (Fin.castAdd (k + n) (Fin.natAdd _ i)) • doubledUnit F (Fin.natAdd _ i)) :
        StepVariable (finiteCells F)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [doubledParams_spare]
    simp
  rw [h2, add_zero]
  have h1 : ∀ a : Fin (Fintype.card (ChordCoord F)),
      (Pi.single (doubledBond F (Fin.castAdd _ a))
        (doubledParams F η s n p (Fin.castAdd (k + n) (Fin.castAdd _ a)) • doubledUnit F (Fin.castAdd _ a)) :
          StepVariable (finiteCells F)) =
      chordCoord ((Fintype.equivFin (ChordCoord F)).symm a) (p.1 - η) •
        chordBasis ((Fintype.equivFin (ChordCoord F)).symm a) := by
    intro a
    rw [doubledParams_chord]
    simp only [doubledBond, doubledUnit, doubledIndex, Fin.addCases_left, chordBasis, bondVariation]
    rw [Pi.single_smul]
  simp only [h1]
  rw [Equiv.sum_comp (Fintype.equivFin (ChordCoord F)).symm
    (fun α => chordCoord α (p.1 - η) • chordBasis α), ← sum_chordCoord_smul_chordBasis]
  abel
theorem bondSpread_doubledParams (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ)
    (n : ℕ) (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (c : Fin k → F.Site F.top × Fin 4)
    (X X' : Fin k → imaginaryQuaternions) (hX : ∀ j, s j • X' j = X j) (c₀ : F.Site F.top × Fin 4)
    (X₀ : imaginaryQuaternions) :
    ColdStepAtMirrorFrames.bondSpread (Fin.addCases (motive := fun _ => F.Site F.top × Fin 4) c fun _ : Fin n => c₀)
      (Fin.addCases (motive := fun _ => imaginaryQuaternions) X' fun _ : Fin n => X₀)
      (fun i => doubledParams F η s n p (Fin.natAdd _ i)) = ColdStepAtMirrorFrames.bondSpread c X p.2 := by
  funext y i
  simp only [ColdStepAtMirrorFrames.bondSpread]
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_right, doubledParams_pad, zero_smul, ite_self, Finset.sum_const_zero, add_zero,
    Fin.addCases_left, doubledParams_top]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hX j, smul_smul, mul_comm]
theorem topTranslated_contDiffAt {n : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (hG : ∀ (p : ℕ) (c' : Fin p → F.Site F.top × Fin 4) (X' : Fin p → imaginaryQuaternions),
      AreUnitVectors X' → n ≤ p →
      ContDiffAt ℝ n (jointDisplacement G η V (doubledBond F) (doubledUnit F) c' X') 0) :
    ContDiffAt ℝ n (topTranslated G V c X) (η, 0) := by
  classical
  set X' : Fin k → imaginaryQuaternions := fun j => if X j = 0 then unitI else (‖X j‖⁻¹ : ℝ) • X j with hX'
  set s : Fin k → ℝ := fun j => ‖X j‖ with hs
  have hsX : ∀ j, s j • X' j = X j := by
    intro j
    by_cases h : X j = 0
    · simp [hs, hX', h]
    · have h0 : ‖X j‖ ≠ 0 := norm_ne_zero_iff.2 h
      simp only [hs, hX', h, if_false, smul_smul, mul_inv_cancel₀ h0, one_smul]
  have hunit : ∀ j, ‖X' j‖ = 1 := by
    intro j
    by_cases h : X j = 0
    · simp only [hX', h, if_true, norm_unitI]
    · have h0 : ‖X j‖ ≠ 0 := norm_ne_zero_iff.2 h
      simp only [hX', h, if_false, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h0]
  set c₀ : F.Site F.top × Fin 4 := (0, 0)
  set cc := Fin.addCases (motive := fun _ => F.Site F.top × Fin 4) c fun _ : Fin n => c₀ with hcc
  set XX := Fin.addCases (motive := fun _ => imaginaryQuaternions) X' fun _ : Fin n => unitI with hXX
  have hu : AreUnitVectors XX := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [hXX, Fin.addCases_left, hunit]
    · simp only [hXX, Fin.addCases_right, norm_unitI]
  have h1 := hG (k + n) cc XX hu (by omega)
  have h2 : ContDiffAt ℝ n (doubledParams F η s n) (η, 0) :=
    ((doubledParams_contDiff F η s n).of_le (by exact_mod_cast le_top)).contDiffAt
  have h3 : ContDiffAt ℝ n (jointDisplacement G η V (doubledBond F) (doubledUnit F) cc XX)
      (doubledParams F η s n (η, 0)) := by
    rw [doubledParams_base_eq_zero]; exact h1
  have h4 := ContDiffAt.comp (η, (0 : Fin k → ℝ)) h3 h2
  refine h4.congr_of_eventuallyEq (Eventually.of_forall fun p => ?_)
  simp only [Function.comp, jointDisplacement, topTranslated]
  rw [displacedPoint_doubledParams, bondSpread_doubledParams F η s n p c X X' hsX c₀ unitI]
theorem cellSupDist_le_diameter {P : Finset F.Cell} {u v : F.Cell} (hu : u ∈ P) (hv : v ∈ P) :
    cellSupDist u v ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.cellSupDist_le_cellSetDiameter <;> assumption
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
end Top
section Bonds
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def bondProjection (b : ι) : BondField ι →L[ℝ] BondField ι :=
  (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b).comp (ContinuousLinearMap.proj b)
theorem sum_bondVariation (η : BondField ι) : ∑ b, bondVariation b (η b) = η := by
  simp only [bondVariation]
  exact Finset.univ_sum_single η
section Slots
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem apply_sum_first (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) {J : Type} (S : Finset J)
    (f : J → E) (b c : E) : T ![∑ j ∈ S, f j, b, c] = ∑ j ∈ S, T ![f j, b, c] := by
  have h : ∀ a : E, T ![a, b, c] = T.curryLeft a ![b, c] := fun a => rfl
  simp only [h, map_sum, ContinuousMultilinearMap.sum_apply]
theorem apply_sum_second (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) {J : Type} (S : Finset J)
    (f : J → E) (a c : E) : T ![a, ∑ j ∈ S, f j, c] = ∑ j ∈ S, T ![a, f j, c] := by
  have h : ∀ b : E, T ![a, b, c] = (T.curryLeft a).curryLeft b ![c] := fun b => rfl
  simp only [h, map_sum, ContinuousMultilinearMap.sum_apply]
end Slots
theorem abs_trilinear_le (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => BondField ι) ℝ)
    (p q c : BondField ι) (W : ι → ι → ℝ)
    (h : ∀ (b₁ b₂ : ι) (u₁ u₂ : BondVector),
      |T ![bondVariation b₁ u₁, bondVariation b₂ u₂, c]| ≤ W b₁ b₂ * (‖u₁‖ * ‖u₂‖)) :
    |T ![p, q, c]| ≤ ∑ b₁, ∑ b₂, W b₁ b₂ * (‖p b₁‖ * ‖q b₂‖) := by
  have e1 : T ![p, q, c] = ∑ b₁, ∑ b₂, T ![bondVariation b₁ (p b₁), bondVariation b₂ (q b₂), c] := by
    conv_lhs => rw [← sum_bondVariation p, ← sum_bondVariation q]
    rw [apply_sum_first]
    refine Finset.sum_congr rfl fun b₁ _ => ?_
    rw [apply_sum_second]
  rw [e1]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b₁ _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b₂ _ => ?_)
  exact h _ _ _ _
def cubicWeight (y : ℝ) (a b c : ι) (η : BondField ι) : ℝ :=
  (1 + y * ‖η a‖) * (1 + y * ‖η b‖) * (1 + y * ‖η c‖)
theorem continuous_cubicWeight (y : ℝ) (a b c : ι) : Continuous (cubicWeight y a b c) := by
  unfold cubicWeight
  fun_prop
def bondWeightSum (w : ι → ℝ) (y : ℝ) (b : ι) (η : BondField ι) : ℝ :=
  ∑ b₁, ∑ b₂, w b₁ * w b₂ * cubicWeight y b₁ b₂ b η
def remainderMajorant (B : Finset ι) (w : ι → ℝ) (y : ℝ) (η : BondField ι) : ℝ :=
  ∑ b ∈ B, bondWeightSum w y b η
theorem one_le_cubicWeight {y : ℝ} (hy : 0 ≤ y) (a b c : ι) (η : BondField ι) : 1 ≤ cubicWeight y a b c η := by
  have h1 : 1 ≤ 1 + y * ‖η a‖ := by nlinarith [mul_nonneg hy (norm_nonneg (η a))]
  have h2 : 1 ≤ 1 + y * ‖η b‖ := by nlinarith [mul_nonneg hy (norm_nonneg (η b))]
  have h3 : 1 ≤ 1 + y * ‖η c‖ := by nlinarith [mul_nonneg hy (norm_nonneg (η c))]
  unfold cubicWeight
  have h4 : 1 ≤ (1 + y * ‖η a‖) * (1 + y * ‖η b‖) := one_le_mul_of_one_le_of_one_le h1 h2
  exact one_le_mul_of_one_le_of_one_le h4 h3
theorem bondWeightSum_nonneg {w : ι → ℝ} (hw : ∀ b, 0 ≤ w b) {y : ℝ} (hy : 0 ≤ y) (b : ι) (η : BondField ι) :
    0 ≤ bondWeightSum w y b η :=
  Finset.sum_nonneg fun b₁ _ => Finset.sum_nonneg fun b₂ _ =>
    mul_nonneg (mul_nonneg (hw _) (hw _)) (zero_le_one.trans (one_le_cubicWeight hy _ _ _ _))
theorem term_le_bondWeightSum {w : ι → ℝ} (hw : ∀ b, 0 ≤ w b) {y : ℝ} (hy : 0 ≤ y) (b₁ b₂ b : ι)
    (η : BondField ι) : w b₁ * w b₂ * cubicWeight y b₁ b₂ b η ≤ bondWeightSum w y b η := by
  have hn : ∀ c₁ c₂ : ι, 0 ≤ w c₁ * w c₂ * cubicWeight y c₁ c₂ b η := fun c₁ c₂ =>
    mul_nonneg (mul_nonneg (hw _) (hw _)) (zero_le_one.trans (one_le_cubicWeight hy _ _ _ _))
  have h1 := Finset.single_le_sum (f := fun c₂ => w b₁ * w c₂ * cubicWeight y b₁ c₂ b η)
    (fun c₂ _ => hn b₁ c₂) (Finset.mem_univ b₂)
  have h2 := Finset.single_le_sum (f := fun c₁ => ∑ c₂, w c₁ * w c₂ * cubicWeight y c₁ c₂ b η)
    (fun c₁ _ => Finset.sum_nonneg fun c₂ _ => hn c₁ c₂) (Finset.mem_univ b₁)
  exact h1.trans h2
private theorem cube_le_cubicWeight {y a b c : ℝ} (hy : 0 < y) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    y ^ 2 * (a * b * c) ≤ y⁻¹ * ((1 + y * a) * (1 + y * b) * (1 + y * c)) := by
  have e : y ^ 2 * (a * b * c) = y⁻¹ * ((y * a) * (y * b) * (y * c)) := by
    field_simp
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : 0 ≤ y * a := by positivity
  have h2 : 0 ≤ y * b := by positivity
  have h3 : 0 ≤ y * c := by positivity
  have h4 : (y * a) * (y * b) ≤ (1 + y * a) * (1 + y * b) :=
    mul_le_mul (by linarith) (by linarith) h2 (by linarith)
  exact mul_le_mul h4 (by linarith) h3 (by positivity)
private theorem square_le_cubicWeight {y a b c : ℝ} (hy : 0 < y) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    y ^ 2 * (a * b) ≤ (1 + y * a) * (1 + y * b) * (1 + y * c) := by
  have e : y ^ 2 * (a * b) = (y * a) * (y * b) := by ring
  rw [e]
  have h1 : 0 ≤ y * a := by positivity
  have h2 : 0 ≤ y * b := by positivity
  have h3 : 0 ≤ y * c := by positivity
  have h5 : 0 ≤ (1 + y * a) * (1 + y * b) := by positivity
  nlinarith [mul_nonneg h5 h3]
private theorem single_le_cubicWeight {y a b c : ℝ} (hy : 0 < y) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a ≤ y⁻¹ * ((1 + y * a) * (1 + y * b) * (1 + y * c)) := by
  have e : a = y⁻¹ * (y * a) := by field_simp
  have h1 : 0 ≤ y * a := by positivity
  have h2 : 0 ≤ y * b := by positivity
  have h3 : 0 ≤ y * c := by positivity
  have h4 : y * a ≤ (1 + y * a) * (1 + y * b) * (1 + y * c) := by
    have h5 : 1 ≤ (1 + y * b) * (1 + y * c) := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + y * a) (by linarith : 0 ≤ (1 + y * b) * (1 + y * c) - 1)]
  calc a = y⁻¹ * (y * a) := e
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
private theorem double_sum_le {x c : ℝ} {a d : ι → ι → ℝ} (h : ∀ b₁ b₂, x * a b₁ b₂ ≤ c * d b₁ b₂) :
    x * ∑ b₁, ∑ b₂, a b₁ b₂ ≤ c * ∑ b₁, ∑ b₂, d b₁ b₂ := by
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ => h b₁ b₂
theorem remainder_and_fderiv_le_majorant (B : Finset ι) {A : BondField ι → ℝ} {ρ x D E : ℝ} {w g : ι → ℝ}
    (hx : 0 < x) (hD : 0 ≤ D) (hE : 0 ≤ E) (hw : ∀ b, 0 ≤ w b) (hw1 : ∀ b ∈ B, w b = 1)
    (hg : ∀ b, w b ≤ g b) (hg1 : ∀ b ∈ B, 1 ≤ g b)
    (hA : ∀ ζ : BondField ι, (∀ b, ‖ζ b‖ ≤ ρ) → ContDiffAt ℝ (3 : ℕ) A ζ)
    (hK : ∀ ζ : BondField ι, (∀ b, ‖ζ b‖ ≤ ρ) → ∀ (b₁ b₂ : ι), ∀ b₃ ∈ B, ∀ u₁ u₂ u₃ : BondVector,
      |iteratedFDeriv ℝ 3 A ζ ![bondVariation b₁ u₁, bondVariation b₂ u₂, bondVariation b₃ u₃]| ≤
        D * (w b₁ * w b₂ * E) * (‖u₁‖ * ‖u₂‖ * ‖u₃‖))
    (hs : ∀ b ∈ B, ∀ u : BondVector, |fderiv ℝ A 0 (bondVariation b u)| ≤ x⁻¹ * E * ‖u‖)
    {η : BondField ι} (hη : ∀ b, ‖η b‖ ≤ ρ) :
    |x * remainder dilate B bondProjection A η| ≤
      (Real.sqrt x)⁻¹ * ((1 + 3 * D) * E) * remainderMajorant B w (Real.sqrt x) η ∧
    ∀ (b₀ : ι) (u : BondVector), |x * fderiv ℝ (remainder dilate B bondProjection A) η (bondVariation b₀ u)| ≤
      (1 + 5 * D) * E * g b₀ * ‖u‖ * remainderMajorant B w (Real.sqrt x) η := by
  set y := Real.sqrt x with hy
  have hy0 : 0 < y := Real.sqrt_pos.2 hx
  have hyx : y ^ 2 = x := Real.sq_sqrt hx.le
  have hray : ∀ v ∈ Icc (0 : ℝ) 1, ∀ b, ‖(v • η) b‖ ≤ ρ := by
    intro v hv b
    have h1 : ‖(v • η) b‖ = v * ‖η b‖ := by
      simp [norm_smul, abs_of_nonneg hv.1]
    rw [h1]
    have := hη b
    nlinarith [hv.1, hv.2, norm_nonneg (η b)]
  have hAr : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (3 : ℕ) A (v • η) := fun v hv => hA _ (hray v hv)
  have hT : ∀ v ∈ Icc (0 : ℝ) 1, ∀ (p q : BondField ι), ∀ b ∈ B, ∀ e₀ : BondVector,
      |iteratedFDeriv ℝ 3 A (v • η) ![p, q, bondVariation b e₀]| ≤
        ∑ b₁, ∑ b₂, (D * (w b₁ * w b₂ * E) * ‖e₀‖) * (‖p b₁‖ * ‖q b₂‖) := by
    intro v hv p q b hb e₀
    refine abs_trilinear_le _ p q _ _ fun b₁ b₂ u₁ u₂ => ?_
    refine (hK _ (hray v hv) b₁ b₂ b hb u₁ u₂ e₀).trans (le_of_eq ?_)
    ring
  have hww : ∀ b₁ b₂, 0 ≤ w b₁ * w b₂ := fun b₁ b₂ => mul_nonneg (hw _) (hw _)
  have hF0 : ∀ b, 0 ≤ bondWeightSum w y b η := fun b => bondWeightSum_nonneg hw hy0.le b η
  have hF1 : ∀ b ∈ B, 1 ≤ bondWeightSum w y b η := by
    intro b hb
    have h1 := term_le_bondWeightSum hw hy0.le b b b η
    rw [hw1 b hb] at h1
    have h2 := one_le_cubicWeight hy0.le b b b η
    linarith
  refine ⟨?_, fun b₀ u => ?_⟩
  · have h1 := abs_remainder_dilate_le B bondProjection
      (M := fun b => ∑ b₁, ∑ b₂, (D * (w b₁ * w b₂ * E) * ‖η b‖) * (‖η b₁‖ * ‖η b₂‖)) hAr
      fun b hb v hv => hT v hv η η b hb (η b)
    rw [abs_mul, abs_of_pos hx]
    refine (mul_le_mul_of_nonneg_left h1 hx.le).trans ?_
    unfold remainderMajorant
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    beta_reduce
    have t1 : x * |fderiv ℝ A 0 (bondProjection b η)| ≤ y⁻¹ * E * bondWeightSum w y b η := by
      have h2 : x * |fderiv ℝ A 0 (bondProjection b η)| ≤ E * ‖η b‖ := by
        have h3 := mul_le_mul_of_nonneg_left (hs b hb (η b)) hx.le
        refine h3.trans (le_of_eq ?_)
        field_simp
      have h3 := single_le_cubicWeight (c := ‖η b‖) (b := ‖η b‖) hy0 (norm_nonneg (η b)) (norm_nonneg (η b))
        (norm_nonneg (η b))
      have h4 := term_le_bondWeightSum hw hy0.le b b b η
      rw [hw1 b hb, one_mul, one_mul] at h4
      have h5 : ‖η b‖ ≤ y⁻¹ * bondWeightSum w y b η :=
        h3.trans (mul_le_mul_of_nonneg_left h4 (by positivity))
      calc _ ≤ E * ‖η b‖ := h2
        _ ≤ E * (y⁻¹ * bondWeightSum w y b η) := mul_le_mul_of_nonneg_left h5 hE
        _ = _ := by ring
    have t2 : x * (∑ b₁, ∑ b₂, (D * (w b₁ * w b₂ * E) * ‖η b‖) * (‖η b₁‖ * ‖η b₂‖)) ≤
        D * E * y⁻¹ * bondWeightSum w y b η := by
      unfold bondWeightSum
      refine double_sum_le fun b₁ b₂ => ?_
      have h2 := cube_le_cubicWeight hy0 (norm_nonneg (η b₁)) (norm_nonneg (η b₂)) (norm_nonneg (η b))
      rw [hyx] at h2
      have h3 : 0 ≤ D * (w b₁ * w b₂) * E := by have := hww b₁ b₂; positivity
      have h4 := mul_le_mul_of_nonneg_left h2 h3
      unfold cubicWeight
      calc _ = D * (w b₁ * w b₂) * E * (x * (‖η b₁‖ * ‖η b₂‖ * ‖η b‖)) := by ring
        _ ≤ _ := h4
        _ = _ := by ring
    have e3 : y⁻¹ * ((1 + 3 * D) * E) * bondWeightSum w y b η =
        y⁻¹ * E * bondWeightSum w y b η + 3 * (D * E * y⁻¹ * bondWeightSum w y b η) := by ring
    rw [e3, mul_add, mul_left_comm x 3]
    exact add_le_add t1 (mul_le_mul_of_nonneg_left t2 (by norm_num))
  · set u' : BondField ι := bondVariation b₀ u with hu'
    have hub : ∀ b, ‖u' b‖ ≤ (if b = b₀ then ‖u‖ else 0) := by
      intro b
      by_cases h : b = b₀
      · subst h
        simp [hu', bondVariation]
      · simp [hu', bondVariation, h]
    have hg0 : 0 ≤ g b₀ := (hw b₀).trans (hg b₀)
    have h1 := abs_fderiv_remainder_dilate_le B bondProjection (u := u')
      (M₁ := fun b => ∑ b₁, ∑ b₂, (D * (w b₁ * w b₂ * E) * ‖u' b‖) * (‖η b₁‖ * ‖η b₂‖))
      (M₂ := fun b => ∑ b₁, ∑ b₂, (D * (w b₁ * w b₂ * E) * ‖η b‖) * (‖η b₁‖ * ‖u' b₂‖)) hAr
      (fun b hb v hv => hT v hv η η b hb (u' b)) (fun b hb v hv => hT v hv η u' b hb (η b))
    rw [abs_mul, abs_of_pos hx]
    refine (mul_le_mul_of_nonneg_left h1 hx.le).trans ?_
    unfold remainderMajorant
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    have hsel : ‖u' b‖ * bondWeightSum w y b η ≤ g b₀ * ‖u‖ * bondWeightSum w y b η := by
      refine mul_le_mul_of_nonneg_right ?_ (hF0 b)
      by_cases h : b = b₀
      · subst h
        have h2 := hub b
        simp only [if_true] at h2
        have h3 := hg1 b hb
        nlinarith [norm_nonneg u]
      · have h2 := hub b
        simp only [h, if_false] at h2
        have h3 : 0 ≤ g b₀ * ‖u‖ := by positivity
        linarith
    have t1 : x * |fderiv ℝ A 0 (bondProjection b u')| ≤ E * (‖u' b‖ * bondWeightSum w y b η) := by
      have h3 := mul_le_mul_of_nonneg_left (hs b hb (u' b)) hx.le
      have h4 : x * (x⁻¹ * E * ‖u' b‖) = E * ‖u' b‖ := by field_simp
      rw [h4] at h3
      refine h3.trans ?_
      have h5 := hF1 b hb
      have h6 : 0 ≤ E * ‖u' b‖ := by positivity
      nlinarith
    have t2 : x * (∑ b₁, ∑ b₂, (D * (w b₁ * w b₂ * E) * ‖u' b‖) * (‖η b₁‖ * ‖η b₂‖)) ≤
        D * E * (‖u' b‖ * bondWeightSum w y b η) := by
      have e : D * E * (‖u' b‖ * bondWeightSum w y b η) = (D * E * ‖u' b‖) * bondWeightSum w y b η := by ring
      rw [e]
      unfold bondWeightSum
      refine double_sum_le fun b₁ b₂ => ?_
      have h2 := square_le_cubicWeight (c := ‖η b‖) hy0 (norm_nonneg (η b₁)) (norm_nonneg (η b₂))
        (norm_nonneg (η b))
      rw [hyx] at h2
      have h3 : 0 ≤ D * (w b₁ * w b₂) * E * ‖u' b‖ := by have := hww b₁ b₂; positivity
      have h4 := mul_le_mul_of_nonneg_left h2 h3
      unfold cubicWeight
      calc _ = D * (w b₁ * w b₂) * E * ‖u' b‖ * (x * (‖η b₁‖ * ‖η b₂‖)) := by ring
        _ ≤ _ := h4
        _ = _ := by ring
    have hzero : ∀ b₂, b₂ ≠ b₀ → u' b₂ = 0 := fun b₂ h => by simp [hu', bondVariation, h]
    have hu0 : u' b₀ = u := by simp [hu', bondVariation]
    have t3 : x * (∑ b₁, ∑ b₂, (D * (w b₁ * w b₂ * E) * ‖η b‖) * (‖η b₁‖ * ‖u' b₂‖)) ≤
        D * E * (g b₀ * ‖u‖ * bondWeightSum w y b η) := by
      have e1 : ∀ b₁, ∑ b₂, (D * (w b₁ * w b₂ * E) * ‖η b‖) * (‖η b₁‖ * ‖u' b₂‖) =
          (D * (w b₁ * w b₀ * E) * ‖η b‖) * (‖η b₁‖ * ‖u‖) := by
        intro b₁
        rw [Finset.sum_eq_single b₀ (fun b₂ _ h => by simp [hzero b₂ h])
          (fun h => absurd (Finset.mem_univ _) h), hu0]
      simp only [e1]
      have e2 : ∑ b₁, w b₁ * cubicWeight y b₁ b b η ≤ bondWeightSum w y b η := by
        unfold bondWeightSum
        refine Finset.sum_le_sum fun b₁ _ => ?_
        have h2 := Finset.single_le_sum (f := fun b₂ => w b₁ * w b₂ * cubicWeight y b₁ b₂ b η)
          (fun b₂ _ => mul_nonneg (hww _ _) (zero_le_one.trans (one_le_cubicWeight hy0.le _ _ _ _)))
          (Finset.mem_univ b)
        simp only [hw1 b hb, mul_one] at h2
        exact h2
      have e3 : x * ∑ b₁, (D * (w b₁ * w b₀ * E) * ‖η b‖) * (‖η b₁‖ * ‖u‖) ≤
          D * E * (g b₀ * ‖u‖) * ∑ b₁, w b₁ * cubicWeight y b₁ b b η := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_le_sum fun b₁ _ => ?_
        have h2 := square_le_cubicWeight (c := ‖η b‖) hy0 (norm_nonneg (η b₁)) (norm_nonneg (η b))
          (norm_nonneg (η b))
        rw [hyx] at h2
        have h3 : 0 ≤ D * (w b₁ * w b₀) * E * ‖u‖ := by have := hww b₁ b₀; positivity
        have h4 := mul_le_mul_of_nonneg_left h2 h3
        have h5 : 0 ≤ cubicWeight y b₁ b b η := zero_le_one.trans (one_le_cubicWeight hy0.le _ _ _ _)
        have h6 : D * (w b₁ * w b₀) * E * ‖u‖ * cubicWeight y b₁ b b η ≤
            D * (w b₁ * g b₀) * E * ‖u‖ * cubicWeight y b₁ b b η := by
          have h7 : w b₁ * w b₀ ≤ w b₁ * g b₀ := mul_le_mul_of_nonneg_left (hg b₀) (hw b₁)
          gcongr
        unfold cubicWeight at h5 h6 ⊢
        calc _ = D * (w b₁ * w b₀) * E * ‖u‖ * (x * (‖η b₁‖ * ‖η b‖)) := by ring
          _ ≤ _ := h4
          _ ≤ _ := h6
          _ = _ := by ring
      refine e3.trans ?_
      have h8 : 0 ≤ D * E * (g b₀ * ‖u‖) := by positivity
      calc _ ≤ D * E * (g b₀ * ‖u‖) * bondWeightSum w y b η := mul_le_mul_of_nonneg_left e2 h8
        _ = _ := by ring
    set G := g b₀ * ‖u‖ * bondWeightSum w y b η with hG
    have a1 : E * (‖u' b‖ * bondWeightSum w y b η) ≤ E * G := mul_le_mul_of_nonneg_left hsel hE
    have a2 : D * E * (‖u' b‖ * bondWeightSum w y b η) ≤ D * E * G :=
      mul_le_mul_of_nonneg_left hsel (by positivity)
    have e4 : (1 + 5 * D) * E * g b₀ * ‖u‖ * bondWeightSum w y b η = E * G + 5 * (D * E * G) := by
      rw [hG]; ring
    rw [e4]
    beta_reduce
    have e5 : ∀ p q r : ℝ, x * (p + 3 * q + 2 * r) = x * p + 3 * (x * q) + 2 * (x * r) := fun p q r => by ring
    rw [e5]
    linarith
section Moments
variable {ρ : ℝ} {r : ℝ → ℝ} {Ψ : BondField ι → ℝ}
structure IsBallLaw (ρ : ℝ) (r : ℝ → ℝ) (Ψ : BondField ι → ℝ) : Prop where
  density_nonneg : ∀ η, 0 ≤ ballDensity r Ψ η
  integrable : Integrable (ballDensity r Ψ)
  integral_pos : 0 < ∫ η, ballDensity r Ψ η
  eq_zero_outside : ∀ η, ¬ (∀ b, ‖η b‖ < ρ) → ballDensity r Ψ η = 0
theorem isOpen_openBallProduct (ρ : ℝ) : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by apply _root_.YangMills.SharedProofs.p5886 <;> assumption
theorem integrable_mul_density_of_bounded (hL : IsBallLaw ρ r Ψ) {G : BondField ι → ℝ} {R : ℝ}
    (hc : ContinuousOn G {η | ∀ b, ‖η b‖ < ρ}) (hb : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |G η| ≤ R) :
    Integrable fun η => G η * ballDensity r Ψ η := by
  set O : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ} with hO
  have hOm : MeasurableSet O := (isOpen_openBallProduct ρ).measurableSet
  have hG : AEStronglyMeasurable (O.indicator G) volume :=
    (aestronglyMeasurable_indicator_iff hOm).2 (hc.aestronglyMeasurable hOm)
  have hbd : ∀ η, ‖O.indicator G η‖ ≤ |R| := by
    intro η
    by_cases h : η ∈ O
    · rw [indicator_of_mem h, Real.norm_eq_abs]
      exact (hb η h).trans (le_abs_self R)
    · rw [indicator_of_notMem h, norm_zero]
      exact abs_nonneg R
  have h1 := hL.integrable.bdd_mul (c := |R|) hG (Eventually.of_forall hbd)
  refine h1.congr (Eventually.of_forall fun η => ?_)
  by_cases h : η ∈ O
  · simp only [indicator_of_mem h]
  · simp only [indicator_of_notMem h, hL.eq_zero_outside η h, mul_zero, zero_mul]
theorem ballExpectation_mono (hL : IsBallLaw ρ r Ψ) {f g : BondField ι → ℝ}
    (hf : Integrable fun η => f η * ballDensity r Ψ η) (hg : Integrable fun η => g η * ballDensity r Ψ η)
    (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → f η ≤ g η) : ballExpectation r Ψ f ≤ ballExpectation r Ψ g := by
  unfold ballExpectation
  refine div_le_div_of_nonneg_right (integral_mono hf hg fun η => ?_) hL.integral_pos.le
  by_cases hη : ∀ b, ‖η b‖ < ρ
  · exact mul_le_mul_of_nonneg_right (h η hη) (hL.density_nonneg η)
  · simp only [hL.eq_zero_outside η hη, mul_zero, le_refl]
theorem ballExpectation_const (hL : IsBallLaw ρ r Ψ) (c : ℝ) : ballExpectation r Ψ (fun _ => c) = c := by
  unfold ballExpectation
  rw [integral_const_mul]
  exact mul_div_cancel_right₀ c hL.integral_pos.ne'
theorem ballExpectation_add {f g : BondField ι → ℝ} (hL : IsBallLaw ρ r Ψ)
    (hf : Integrable fun η => f η * ballDensity r Ψ η) (hg : Integrable fun η => g η * ballDensity r Ψ η) :
    ballExpectation r Ψ (fun η => f η + g η) = ballExpectation r Ψ f + ballExpectation r Ψ g := by
  unfold ballExpectation
  have e : (fun η => (f η + g η) * ballDensity r Ψ η) =
      fun η => f η * ballDensity r Ψ η + g η * ballDensity r Ψ η := by
    funext η; ring
  rw [e, integral_add hf hg, add_div]
theorem ballExpectation_const_mul (a : ℝ) (f : BondField ι → ℝ) :
    ballExpectation r Ψ (fun η => a * f η) = a * ballExpectation r Ψ f := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative.ballExpectation_const_mul <;> assumption
private theorem one_add_pow_le {z : ℝ} (hz : 0 ≤ z) (n : ℕ) : (1 + z) ^ n ≤ 2 ^ n * (1 + z ^ n) := by apply _root_.YangMills.SharedProofs.p7069 <;> assumption
private theorem pow_le_one_add_sq {z : ℝ} (n : ℕ) (hz : 0 ≤ z) : z ^ n ≤ 1 + z ^ (2 * n) := by
  have e : z ^ (2 * n) = (z ^ n) ^ 2 := by rw [mul_comm, pow_mul]
  rw [e]
  nlinarith [sq_nonneg (z ^ n - 1)]
private theorem mul_three_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b * c ≤ a ^ 3 + b ^ 3 + c ^ 3 := by
  nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc, sq_nonneg (a - b), sq_nonneg (b - c),
    sq_nonneg (a - c), mul_nonneg ha (sq_nonneg (b - c)), mul_nonneg hb (sq_nonneg (a - c)),
    mul_nonneg hc (sq_nonneg (a - b)), mul_nonneg ha (sq_nonneg (a - b)), mul_nonneg hb (sq_nonneg (b - c)),
    mul_nonneg hc (sq_nonneg (a - c))]
private theorem bond_power_le {x y : ℝ} (hy : 0 ≤ y) (hyx : y ^ 2 = x) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    (1 + y * t) ^ n ≤ 2 ^ n * (2 + x ^ n * t ^ (2 * n)) := by
  have h0 : 0 ≤ y * t := by positivity
  have h1 := one_add_pow_le h0 n
  have h2 := pow_le_one_add_sq n h0
  have e : (y * t) ^ (2 * n) = x ^ n * t ^ (2 * n) := by
    rw [mul_pow, pow_mul y, hyx]
  rw [e] at h2
  have h3 : (0 : ℝ) < 2 ^ n := by positivity
  nlinarith
theorem ballExpectation_cubicWeight_pow_le (hL : IsBallLaw ρ r Ψ) {x : ℝ} (hx : 0 < x) (hρ : 0 < ρ)
    {Cq : ℕ → ℝ} (hm : ∀ (n : ℕ) (b : ι), ballExpectation r Ψ (fun η => ‖η b‖ ^ (2 * n)) ≤ Cq n * (x ^ n)⁻¹)
    (a b c : ι) {q : ℕ} (hq : 1 ≤ q) :
    ballExpectation r Ψ (fun η => cubicWeight (Real.sqrt x) a b c η ^ q) ≤ (24 * (2 + |Cq (3 * q)|)) ^ q := by
  set y := Real.sqrt x with hy
  have hy0 : 0 ≤ y := Real.sqrt_nonneg x
  have hyx : y ^ 2 = x := Real.sq_sqrt hx.le
  set n := 3 * q with hn
  have hball : ∀ (G : BondField ι → ℝ) (R : ℝ), Continuous G →
      (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |G η| ≤ R) →
      Integrable fun η => G η * ballDensity r Ψ η := fun G R hG hb =>
    integrable_mul_density_of_bounded hL hG.continuousOn hb
  have hc1 : ∀ e : ι, Integrable fun η : BondField ι => ‖η e‖ ^ (2 * n) * ballDensity r Ψ η := fun e =>
    hball _ (ρ ^ (2 * n)) (by fun_prop) fun η hη => by
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hη e).le _
  set t : ι → BondField ι → ℝ := fun e η => 2 ^ n * (2 + x ^ n * ‖η e‖ ^ (2 * n)) with ht
  have hti : ∀ e, Integrable fun η => t e η * ballDensity r Ψ η := fun e =>
    hball _ (2 ^ n * (2 + x ^ n * ρ ^ (2 * n))) (by simp only [ht]; fun_prop) fun η hη => by
      simp only [ht]
      rw [abs_of_nonneg (by positivity)]
      have := pow_le_pow_left₀ (norm_nonneg _) (hη e).le (2 * n)
      gcongr
  have hmean : ∀ e, ballExpectation r Ψ (t e) ≤ 2 ^ n * (2 + |Cq n|) := by
    intro e
    have e1 : ballExpectation r Ψ (t e) =
        2 ^ n * (2 + x ^ n * ballExpectation r Ψ fun η => ‖η e‖ ^ (2 * n)) := by
      simp only [ht]
      rw [ballExpectation_const_mul, ballExpectation_add hL (by simpa using hL.integrable.const_mul 2) ?_,
        ballExpectation_const hL, ballExpectation_const_mul]
      have := (hc1 e).const_mul (x ^ n)
      refine this.congr (Eventually.of_forall fun η => ?_)
      simp only [mul_assoc]
    rw [e1]
    have hxn : (0 : ℝ) < x ^ n := by positivity
    have h2 : x ^ n * ballExpectation r Ψ (fun η => ‖η e‖ ^ (2 * n)) ≤ Cq n := by
      have h3 := mul_le_mul_of_nonneg_left (hm n e) hxn.le
      have h4 : x ^ n * (Cq n * (x ^ n)⁻¹) = Cq n := by field_simp
      rwa [h4] at h3
    have h5 := le_abs_self (Cq n)
    have h6 : (0 : ℝ) < 2 ^ n := by positivity
    nlinarith
  have hsum : Integrable fun η => (t a η + t b η + t c η) * ballDensity r Ψ η := by
    have := ((hti a).add (hti b)).add (hti c)
    refine this.congr (Eventually.of_forall fun η => ?_)
    simp only [Pi.add_apply]
    ring
  have hleft : Integrable fun η => cubicWeight y a b c η ^ q * ballDensity r Ψ η :=
    hball _ (((1 + y * ρ) ^ 3) ^ q) ((continuous_cubicWeight y a b c).pow q) fun η hη => by
      have h0 : 0 ≤ cubicWeight y a b c η := zero_le_one.trans (one_le_cubicWeight hy0 _ _ _ _)
      rw [abs_of_nonneg (by positivity)]
      refine pow_le_pow_left₀ h0 ?_ q
      have b1 : ∀ e, 1 + y * ‖η e‖ ≤ 1 + y * ρ := fun e => by
        have := mul_le_mul_of_nonneg_left (hη e).le hy0
        linarith
      have b0 : ∀ e, 0 ≤ 1 + y * ‖η e‖ := fun e => by positivity
      unfold cubicWeight
      calc _ ≤ (1 + y * ρ) * (1 + y * ρ) * (1 + y * ρ) :=
            mul_le_mul (mul_le_mul (b1 a) (b1 b) (b0 b) ((b0 a).trans (b1 a))) (b1 c) (b0 c)
              (mul_nonneg ((b0 a).trans (b1 a)) ((b0 a).trans (b1 a)))
        _ = _ := by ring
  have hpt : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → cubicWeight y a b c η ^ q ≤ t a η + t b η + t c η := by
    intro η _
    have h1 : cubicWeight y a b c η ^ q =
        (1 + y * ‖η a‖) ^ q * (1 + y * ‖η b‖) ^ q * (1 + y * ‖η c‖) ^ q := by
      unfold cubicWeight
      rw [mul_pow, mul_pow]
    have h2 := mul_three_le (a := (1 + y * ‖η a‖) ^ q) (b := (1 + y * ‖η b‖) ^ q) (c := (1 + y * ‖η c‖) ^ q)
      (by positivity) (by positivity) (by positivity)
    have e3 : ∀ e, ((1 + y * ‖η e‖) ^ q) ^ 3 ≤ t e η := fun e => by
      rw [← pow_mul, mul_comm q 3]
      exact bond_power_le hy0 hyx _ (norm_nonneg _) n
    rw [h1]
    linarith [e3 a, e3 b, e3 c]
  have h1 := ballExpectation_mono hL hleft hsum hpt
  have e4 : ballExpectation r Ψ (fun η => t a η + t b η + t c η) =
      ballExpectation r Ψ (t a) + ballExpectation r Ψ (t b) + ballExpectation r Ψ (t c) := by
    rw [ballExpectation_add hL ((hti a).add (hti b) |>.congr
        (Eventually.of_forall fun η => by simp only [Pi.add_apply]; ring)) (hti c),
      ballExpectation_add hL (hti a) (hti b)]
  rw [e4] at h1
  have h2 : ballExpectation r Ψ (fun η => cubicWeight y a b c η ^ q) ≤ 3 * (2 ^ n * (2 + |Cq n|)) := by
    linarith [hmean a, hmean b, hmean c]
  refine h2.trans ?_
  have e5 : (24 * (2 + |Cq n|)) ^ q = 3 ^ q * (2 ^ n) * (2 + |Cq n|) ^ q := by
    rw [hn, pow_mul, mul_pow, show (24 : ℝ) = 3 * 2 ^ 3 by norm_num, mul_pow]
  rw [e5]
  have h3 : (3 : ℝ) ≤ 3 ^ q := le_self_pow₀ (by norm_num) (by omega)
  have h4 : 2 + |Cq n| ≤ (2 + |Cq n|) ^ q := le_self_pow₀ (by linarith [abs_nonneg (Cq n)]) (by omega)
  have h5 : (0 : ℝ) < 2 ^ n := by positivity
  have h6 : 0 ≤ 2 + |Cq n| := by positivity
  calc 3 * (2 ^ n * (2 + |Cq n|)) = 3 * 2 ^ n * (2 + |Cq n|) := by ring
    _ ≤ 3 ^ q * 2 ^ n * (2 + |Cq n|) ^ q := by gcongr
theorem momentBound_of_le_weighted_sum (hL : IsBallLaw ρ r Ψ) {J : Type} (S : Finset J) (a : J → ℝ)
    (Pf : J → BondField ι → ℝ) (ha : ∀ j ∈ S, 0 ≤ a j) (hc : ∀ j ∈ S, Continuous (Pf j))
    (h0 : ∀ j ∈ S, ∀ η, 0 ≤ Pf j η)
    (hb : ∀ j ∈ S, ∃ R, ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → Pf j η ≤ R) {G : BondField ι → ℝ}
    (hG : ContinuousOn G {η | ∀ b, ‖η b‖ < ρ}) {q : ℕ} (hq : 1 ≤ q) {M c : ℝ} (hM : 0 ≤ M) (hc0 : 0 ≤ c)
    (hm : ∀ j ∈ S, ballExpectation r Ψ (fun η => Pf j η ^ q) ≤ M ^ q)
    (hbound : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |G η| ≤ c * ∑ j ∈ S, a j * Pf j η) :
    MomentBound r Ψ G q (c * (∑ j ∈ S, a j) * M) := by
  classical
  choose! R hR using hb
  have hRb : ∀ j ∈ S, ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |Pf j η ^ q| ≤ R j ^ q := fun j hj η hη => by
    rw [abs_of_nonneg (pow_nonneg (h0 j hj η) q)]
    exact pow_le_pow_left₀ (h0 j hj η) (hR j hj η hη) q
  have hPfi : ∀ j ∈ S, Integrable fun η => Pf j η ^ q * ballDensity r Ψ η := fun j hj =>
    integrable_mul_density_of_bounded hL ((hc j hj).pow q).continuousOn (hRb j hj)
  have hGq : ContinuousOn (fun η => |G η| ^ q) {η | ∀ b, ‖η b‖ < ρ} := hG.abs.pow q
  have hGb : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |(|G η| ^ q)| ≤ (c * ∑ j ∈ S, a j * R j) ^ q := by
    intro η hη
    rw [abs_of_nonneg (by positivity)]
    refine pow_le_pow_left₀ (abs_nonneg _) ((hbound η hη).trans ?_) q
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) hc0
    exact mul_le_mul_of_nonneg_left (hR j hj η hη) (ha j hj)
  have hGi : Integrable fun η => |G η| ^ q * ballDensity r Ψ η := integrable_mul_density_of_bounded hL hGq hGb
  refine ⟨hGi, ?_⟩
  set s := ∑ j ∈ S, a j with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg ha
  rcases hs0.eq_or_lt with hz | hpos
  · have hz' : ∀ j ∈ S, a j = 0 := (Finset.sum_eq_zero_iff_of_nonneg ha).1 hz.symm
    have hzero : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |G η| ^ q ≤ 0 := by
      intro η hη
      have h1 := hbound η hη
      rw [Finset.sum_eq_zero fun j hj => by rw [hz' j hj, zero_mul], mul_zero] at h1
      have h2 : |G η| = 0 := le_antisymm h1 (abs_nonneg _)
      rw [h2, zero_pow (by omega)]
    have h1 := ballExpectation_mono hL hGi (g := fun _ => 0) (by simp) hzero
    rw [ballExpectation_const hL] at h1
    refine h1.trans ?_
    rw [← hz, mul_zero, zero_mul, zero_pow (by omega)]
  · set f : BondField ι → ℝ := fun η => (c * s) ^ q * ∑ j ∈ S, (a j / s) * Pf j η ^ q with hf
    have hterm : ∀ j ∈ S, Integrable fun η => (a j / s) * Pf j η ^ q * ballDensity r Ψ η := fun j hj => by
      refine ((hPfi j hj).const_mul (a j / s)).congr (Eventually.of_forall fun η => ?_)
      simp only [mul_assoc]
    have hsumi : Integrable fun η => (∑ j ∈ S, (a j / s) * Pf j η ^ q) * ballDensity r Ψ η := by
      have := integrable_finset_sum S hterm
      refine this.congr (Eventually.of_forall fun η => ?_)
      simp only [Finset.sum_mul]
    have hfi : Integrable fun η => f η * ballDensity r Ψ η := by
      refine (hsumi.const_mul ((c * s) ^ q)).congr (Eventually.of_forall fun η => ?_)
      simp only [hf, mul_assoc]
    have hpt : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |G η| ^ q ≤ f η := by
      intro η hη
      have hw : ∑ j ∈ S, a j / s = 1 := by
        rw [← Finset.sum_div, div_self hpos.ne']
      have h1 := Real.pow_arith_mean_le_arith_mean_pow S (fun j => a j / s) (fun j => Pf j η)
        (fun j hj => div_nonneg (ha j hj) hs0) hw (fun j hj => h0 j hj η) q
      have h2 : ∑ j ∈ S, a j * Pf j η = s * ∑ j ∈ S, (a j / s) * Pf j η := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        field_simp
      have h3 := hbound η hη
      rw [h2] at h3
      have h5 : |G η| ^ q ≤ (c * (s * ∑ j ∈ S, (a j / s) * Pf j η)) ^ q :=
        pow_le_pow_left₀ (abs_nonneg _) h3 q
      calc _ ≤ _ := h5
        _ = (c * s) ^ q * (∑ j ∈ S, (a j / s) * Pf j η) ^ q := by rw [← mul_assoc, mul_pow]
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
    refine (ballExpectation_mono hL hGi hfi hpt).trans ?_
    have e1 : ballExpectation r Ψ f =
        (c * s) ^ q * ∑ j ∈ S, (a j / s) * ballExpectation r Ψ fun η => Pf j η ^ q := by
      simp only [hf]
      rw [ballExpectation_const_mul]
      congr 1
      unfold ballExpectation
      simp only [Finset.sum_mul]
      rw [integral_finset_sum S hterm, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e2 : (fun η => a j / s * Pf j η ^ q * ballDensity r Ψ η) =
          fun η => a j / s * (Pf j η ^ q * ballDensity r Ψ η) := by
        funext η; ring
      rw [e2, integral_const_mul, mul_div_assoc]
    rw [e1, mul_pow (c * s) M]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : ∑ j ∈ S, (a j / s) * ballExpectation r Ψ (fun η => Pf j η ^ q) ≤ ∑ j ∈ S, (a j / s) * M ^ q :=
      Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hm j hj) (div_nonneg (ha j hj) hs0)
    refine h1.trans (le_of_eq ?_)
    rw [← Finset.sum_mul, ← Finset.sum_div, div_self hpos.ne', one_mul]
theorem momentBound_of_le_majorant (hL : IsBallLaw ρ r Ψ) {x : ℝ} (hx : 0 < x) (hρ : 0 < ρ) {Cq : ℕ → ℝ}
    (hm : ∀ (n : ℕ) (b : ι), ballExpectation r Ψ (fun η => ‖η b‖ ^ (2 * n)) ≤ Cq n * (x ^ n)⁻¹)
    (B : Finset ι) {w : ι → ℝ} (hw : ∀ b, 0 ≤ w b) {W : ℝ} (hW : ∑ b, w b ≤ W) {G : BondField ι → ℝ}
    (hG : ContinuousOn G {η | ∀ b, ‖η b‖ < ρ}) {q : ℕ} (hq : 1 ≤ q) {c : ℝ} (hc0 : 0 ≤ c)
    (hbound : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |G η| ≤ c * remainderMajorant B w (Real.sqrt x) η) :
    MomentBound r Ψ G q (c * (B.card * W ^ 2) * (24 * (2 + |Cq (3 * q)|))) := by
  set y := Real.sqrt x with hy
  have hy0 : 0 ≤ y := Real.sqrt_nonneg x
  set S : Finset (ι × ι × ι) := B ×ˢ (Finset.univ ×ˢ Finset.univ) with hS
  set a : ι × ι × ι → ℝ := fun j => w j.2.1 * w j.2.2 with ha
  set Pf : ι × ι × ι → BondField ι → ℝ := fun j => cubicWeight y j.2.1 j.2.2 j.1 with hPf
  have hmaj : ∀ η, remainderMajorant B w y η = ∑ j ∈ S, a j * Pf j η := fun η => by
    unfold remainderMajorant bondWeightSum
    rw [hS, Finset.sum_product]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_product]
  have hM : 0 ≤ 24 * (2 + |Cq (3 * q)|) := by positivity
  have h1 := momentBound_of_le_weighted_sum hL S a Pf (fun j _ => mul_nonneg (hw _) (hw _))
    (fun j _ => continuous_cubicWeight y _ _ _)
    (fun j _ η => zero_le_one.trans (one_le_cubicWeight hy0 _ _ _ _))
    (fun j _ => ⟨(1 + y * ρ) ^ 3, fun η hη => by
      have b1 : ∀ e, 1 + y * ‖η e‖ ≤ 1 + y * ρ := fun e => by
        have := mul_le_mul_of_nonneg_left (hη e).le hy0
        linarith
      have b0 : ∀ e, 0 ≤ 1 + y * ‖η e‖ := fun e => by positivity
      simp only [hPf]
      unfold cubicWeight
      calc _ ≤ (1 + y * ρ) * (1 + y * ρ) * (1 + y * ρ) :=
            mul_le_mul (mul_le_mul (b1 j.2.1) (b1 j.2.2) (b0 j.2.2) ((b0 j.2.1).trans (b1 j.2.1))) (b1 j.1)
              (b0 j.1) (mul_nonneg ((b0 j.2.1).trans (b1 j.2.1)) ((b0 j.2.1).trans (b1 j.2.1)))
        _ = _ := by ring⟩)
    hG hq hM hc0 (fun j _ => ballExpectation_cubicWeight_pow_le hL hx hρ hm _ _ _ hq)
    (fun η hη => by rw [← hmaj]; exact hbound η hη)
  have hsum : ∑ j ∈ S, a j ≤ B.card * W ^ 2 := by
    have hW0 : 0 ≤ ∑ b, w b := Finset.sum_nonneg fun b _ => hw b
    have e1 : ∑ j ∈ S, a j = B.card * (∑ b, w b) ^ 2 := by
      rw [hS, Finset.sum_product]
      simp only [ha]
      have : ∀ b ∈ B, ∑ p ∈ (Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset ι), w p.1 * w p.2 =
          (∑ b, w b) ^ 2 := by
        intro b _
        rw [Finset.sum_product, sq, Finset.sum_mul_sum]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
    rw [e1]
    have := pow_le_pow_left₀ hW0 hW 2
    gcongr
  refine ⟨h1.1, h1.2.trans ?_⟩
  refine pow_le_pow_left₀ ?_ ?_ q
  · exact mul_nonneg (mul_nonneg hc0 (Finset.sum_nonneg fun j _ => mul_nonneg (hw _) (hw _))) hM
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hc0) hM
end Moments
end Bonds
end YangMills.Construction.Dilation
end
