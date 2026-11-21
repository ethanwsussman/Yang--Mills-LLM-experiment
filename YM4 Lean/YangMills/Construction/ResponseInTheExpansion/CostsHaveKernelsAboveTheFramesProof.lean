import YangMills.Construction.ColdChainAtEveryLevel.PointsOfAPatchForm
import YangMills.Construction.ColdStepAtMirrorFrames.CellGeometryOfATorus
import YangMills.Construction.ResponseInTheExpansion.CostsHaveKernelsAboveTheFrames
import YangMills.Construction.ResponseInTheExpansion.KernelsOfABlockAboveTheFrames
import YangMills.Construction.ResponseInTheExpansion.KernelsOfTheScoreAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.JointSmoothnessFromMovesProof
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsOfTheGapAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsOfTheHaarDensityAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesInTheLawsBetweenProof
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation WeightedResponses PatchPoints
namespace ResponseInTheExpansion
namespace CostKernelBoundsAux
variable {F : BlockFrame}
private def KernelBound (ρ r : ℝ) (P : Finset F.Cell) (A : ℕ → ℕ → ℝ) (G : AboveFrames F) (V : F.GaugeField F.top) : Prop :=
  ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) →
    ∀ (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
      (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions), 1 ≤ l + j → (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
      HasDecayingKernelAt G (A l j) r P η V b u c X
variable {ρ r : ℝ} {P : Finset F.Cell} {A A' : ℕ → ℕ → ℝ} {G G₁ G₂ : AboveFrames F} {V : F.GaugeField F.top}
private theorem kernelBound_mono (h : ∀ l j, A l j ≤ A' l j) (hk : KernelBound ρ r P A G V) : KernelBound ρ r P A' G V := by
  intro η hη l j b u c X hl hu hX
  obtain ⟨h1, h2⟩ := hk η hη l j b u c X hl hu hX
  exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_right (h l j) (Real.exp_pos _).le)⟩
private theorem kernelBound_add (h₁ : KernelBound ρ r P A G₁ V) (h₂ : KernelBound ρ r P A' G₂ V) :
    KernelBound ρ r P (fun l j => A l j + A' l j) (fun η V' => G₁ η V' + G₂ η V') V := by
  intro η hη l j b u c X hl hu hX
  obtain ⟨a₁, a₂⟩ := h₁ η hη l j b u c X hl hu hX
  obtain ⟨b₁, b₂⟩ := h₂ η hη l j b u c X hl hu hX
  have e : jointDisplacement (fun η V' => G₁ η V' + G₂ η V') η V b u c X =
      jointDisplacement G₁ η V b u c X + jointDisplacement G₂ η V b u c X := rfl
  refine ⟨by rw [e]; exact a₁.add b₁, ?_⟩
  have e2 : jointMixedDeriv (fun η V' => G₁ η V' + G₂ η V') η V b u c X =
      jointMixedDeriv G₁ η V b u c X + jointMixedDeriv G₂ η V b u c X := by
    unfold jointMixedDeriv
    rw [e, iteratedFDeriv_add_apply a₁ b₁]
    rfl
  rw [e2]
  refine (abs_add_le _ _).trans ?_
  rw [add_mul]
  exact add_le_add a₂ b₂
private theorem kernelBound_const_mul (w : ℝ) (hk : KernelBound ρ r P A G V) :
    KernelBound ρ r P (fun l j => |w| * A l j) (fun η V' => w * G η V') V := by
  intro η hη l j b u c X hl hu hX
  obtain ⟨a₁, a₂⟩ := hk η hη l j b u c X hl hu hX
  have e : jointDisplacement (fun η V' => w * G η V') η V b u c X = w • jointDisplacement G η V b u c X := rfl
  refine ⟨by rw [e]; exact a₁.const_smul w, ?_⟩
  have e2 : jointMixedDeriv (fun η V' => w * G η V') η V b u c X = w * jointMixedDeriv G η V b u c X := by
    unfold jointMixedDeriv
    rw [e, iteratedFDeriv_const_smul_apply a₁]
    rfl
  rw [e2, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left a₂ (abs_nonneg _)
private theorem kernelBound_const (k₀ : ℝ) : KernelBound ρ r P (fun _ _ => 0) (fun _ _ => k₀) V := by
  intro η hη l j b u c X hl hu hX
  have hn : l + j ≠ 0 := by omega
  have e : jointDisplacement (fun _ _ => k₀) η V b u c X = fun _ => k₀ := rfl
  refine ⟨by rw [e]; exact contDiffAt_const, ?_⟩
  unfold jointMixedDeriv
  rw [e, iteratedFDeriv_const_of_ne hn]
  simp
private theorem kernelBound_sub_const (k₀ : ℝ) (hk : KernelBound ρ r P A G V) :
    KernelBound ρ r P A (fun η V' => G η V' - k₀) V := by
  have h := kernelBound_add hk (kernelBound_const (ρ := ρ) (r := r) (P := P) (V := V) (-k₀))
  have e : (fun η V' => G η V' + -k₀) = fun η V' => G η V' - k₀ := by
    funext η V'
    ring
  rw [e] at h
  exact kernelBound_mono (fun l j => by simp) h
private theorem kernelBound_sum {ι : Type} (s : Finset ι) (w : ι → ℝ) (H : ι → AboveFrames F)
    (h : ∀ i ∈ s, KernelBound ρ r P A (H i) V) :
    KernelBound ρ r P (fun l j => (∑ i ∈ s, |w i|) * A l j) (fun η V' => ∑ i ∈ s, w i * H i η V') V := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using kernelBound_const (ρ := ρ) (r := r) (P := P) (V := V) (0 : ℝ)
  | insert i s hi ih =>
    have h1 := kernelBound_add (kernelBound_const_mul (w i) (h i (Finset.mem_insert_self _ _)))
      (ih fun i' hi' => h i' (Finset.mem_insert_of_mem hi'))
    have e : (fun η V' => w i * H i η V' + ∑ i ∈ s, w i * H i η V') =
        fun η V' => ∑ i ∈ insert i s, w i * H i η V' := by
      funext η V'
      rw [Finset.sum_insert hi]
    rw [e] at h1
    refine kernelBound_mono (fun l j => ?_) h1
    rw [Finset.sum_insert hi, add_mul]
private theorem kernelBound_sum_one {ι : Type} (s : Finset ι) (H : ι → AboveFrames F)
    (h : ∀ i ∈ s, KernelBound ρ r P A (H i) V) :
    KernelBound ρ r P (fun l j => (s.card : ℝ) * A l j) (fun η V' => ∑ i ∈ s, H i η V') V := by
  have h1 := kernelBound_sum s (fun _ => 1) H h
  simpa using h1
private theorem kernelBound_rate_mono {r' : ℝ} (hr' : 0 ≤ r') (hr : r' ≤ r) (hA : ∀ l j, 0 ≤ A l j)
    (hk : KernelBound ρ r P A G V) : KernelBound ρ r' P A G V := by
  intro η hη l j b u c X hl hu hX
  obtain ⟨h1, h2⟩ := hk η hη l j b u c X hl hu hX
  refine ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg ?_)) (hA l j))⟩
  exact mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)
private theorem cellSupDist_le_diameter {Q : Finset F.Cell} {u v : F.Cell} (hu : u ∈ Q) (hv : v ∈ Q) :
    cellSupDist u v ≤ cellSetDiameter Q := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.cellSupDist_le_cellSetDiameter <;> assumption
private theorem diameter_shift_le {Y y₀ : F.Cell} (hz : ∀ y : F.Cell, cellSupDist y y = 0)
    (hsym : ∀ x y : F.Cell, cellSupDist x y = cellSupDist y x)
    (hd : ∀ v : F.Cell, cellSupDist Y v ≤ cellSupDist y₀ v + 1) (Z₁ Z₂ : Finset F.Cell) :
    cellSetDiameter ({Y} ∪ Z₁ ∪ Z₂) ≤ cellSetDiameter ({y₀} ∪ Z₁ ∪ Z₂) + 2 := by
  classical
  have hone : ∀ v ∈ {Y} ∪ Z₁ ∪ Z₂, v = Y ∨ v ∈ {y₀} ∪ Z₁ ∪ Z₂ := by
    intro v hv
    simp only [Finset.mem_union, Finset.mem_singleton] at hv ⊢
    tauto
  have hy₀ : y₀ ∈ {y₀} ∪ Z₁ ∪ Z₂ := by simp
  have hfar : ∀ v ∈ {Y} ∪ Z₁ ∪ Z₂, cellSupDist Y v ≤ cellSetDiameter ({y₀} ∪ Z₁ ∪ Z₂) + 1 := by
    intro v hv
    rcases hone v hv with rfl | h
    · rw [hz]
      exact Nat.zero_le _
    · exact (hd v).trans (Nat.add_le_add_right (cellSupDist_le_diameter hy₀ h) 1)
  refine Finset.sup_le fun u hu => Finset.sup_le fun v hv => ?_
  rcases hone u hu with rfl | h
  · exact (hfar v hv).trans (by omega)
  · rcases hone v hv with rfl | h'
    · rw [hsym]
      exact (hfar u hu).trans (by omega)
    · exact (cellSupDist_le_diameter h h').trans (by omega)
private theorem kernelBound_shift_anchor {r' : ℝ} {Y y₀ : F.Cell} (hz : ∀ y : F.Cell, cellSupDist y y = 0)
    (hsym : ∀ x y : F.Cell, cellSupDist x y = cellSupDist y x)
    (hd : ∀ v : F.Cell, cellSupDist Y v ≤ cellSupDist y₀ v + 1) (hr' : 0 ≤ r') (hr : r' ≤ r)
    (hA : ∀ l j, 0 ≤ A l j) (hk : KernelBound ρ r {y₀} A G V) :
    KernelBound ρ r' {Y} (fun l j => Real.exp (2 * r') * A l j) G V := by
  intro η hη l j b u c X hl hu hX
  obtain ⟨h1, h2⟩ := hk η hη l j b u c X hl hu hX
  refine ⟨h1, h2.trans ?_⟩
  have hs : (cellSetDiameter ({Y} ∪ chordBondCells b ∪ topBondCells c) : ℝ) ≤
      cellSetDiameter ({y₀} ∪ chordBondCells b ∪ topBondCells c) + 2 := by
    exact_mod_cast diameter_shift_le hz hsym hd _ _
  have h0 : (0 : ℝ) ≤ cellSetDiameter ({y₀} ∪ chordBondCells b ∪ topBondCells c) := Nat.cast_nonneg _
  show A l j * _ ≤ Real.exp (2 * r') * A l j * _
  rw [mul_comm (Real.exp (2 * r')) (A l j), mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hA l j)
  nlinarith [mul_le_mul_of_nonneg_left hs hr', mul_le_mul_of_nonneg_right hr h0]
private def quatI : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
private def unitImaginary : imaginaryQuaternions := ⟨quatI, rfl⟩
private theorem norm_unitImaginary : ‖unitImaginary‖ = 1 := by
  change ‖quatI‖ = 1
  have h : ‖quatI‖ * ‖quatI‖ = 1 := by
    rw [← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    simp [quatI]
  have h0 : 0 ≤ ‖quatI‖ := norm_nonneg _
  nlinarith
open Classical in
private def normalize (X : imaginaryQuaternions) : imaginaryQuaternions :=
  if X = 0 then unitImaginary else ‖X‖⁻¹ • X
private theorem norm_normalize (X : imaginaryQuaternions) : ‖normalize X‖ = 1 := by
  unfold normalize
  split_ifs with h
  · exact norm_unitImaginary
  · rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)
private theorem norm_smul_normalize (X : imaginaryQuaternions) : ‖X‖ • normalize X = X := by
  unfold normalize
  split_ifs with h
  · simp [h]
  · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul]
private def scaleByNorms {k : ℕ} (X : Fin k → imaginaryQuaternions) : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun i => ‖X i‖ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i
private theorem bondSpread_scaleByNorms {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (τ : Fin k → ℝ) :
    ColdStepAtMirrorFrames.bondSpread c X τ =
      ColdStepAtMirrorFrames.bondSpread c (fun l => normalize (X l)) (scaleByNorms X τ) := by
  funext y i
  unfold ColdStepAtMirrorFrames.bondSpread
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · have : scaleByNorms X τ l = ‖X l‖ * τ l := by simp [scaleByNorms]
    rw [this, mul_comm, mul_smul, norm_smul_normalize]
  · rfl
private theorem bondSpread_addCases_zero {j : ℕ} (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions)
    (d : F.Site F.top × Fin 4) (X₀ : imaginaryQuaternions) (τ : Fin j → ℝ) :
    ColdStepAtMirrorFrames.bondSpread (Fin.addCases (motive := fun _ => F.Site F.top × Fin 4) c fun _ : Fin 4 => d)
      (Fin.addCases (motive := fun _ => imaginaryQuaternions) X fun _ : Fin 4 => X₀)
      (Fin.addCases (motive := fun _ => ℝ) τ fun _ : Fin 4 => 0) = ColdStepAtMirrorFrames.bondSpread c X τ := by
  funext y i
  simp only [ColdStepAtMirrorFrames.bondSpread]
  rw [Fin.sum_univ_add]
  simp [Fin.addCases_left, Fin.addCases_right]
private theorem sum_single_coords {ι : Type} [Fintype ι] [DecidableEq ι] (ζ : ι → EuclideanSpace ℝ (Fin 3)) :
    ∑ q : ι × Fin 3, (Pi.single q.1 ((ζ q.1) q.2 • EuclideanSpace.single q.2 (1 : ℝ)) :
      ι → EuclideanSpace ℝ (Fin 3)) = ζ := by apply _root_.YangMills.Construction.Estimates.DisplacementCoordinates.sum_single_coordinates <;> assumption
private theorem contDiffAt_joint_of_unit (hk : KernelBound ρ r P A G V) (j : ℕ) (c : Fin j → F.Site F.top × Fin 4)
    (X : Fin j → imaginaryQuaternions)
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ ≤ ρ) (hX : AreUnitVectors X) :
    ContDiffAt ℝ 4 (fun q : (Fin j → ℝ) × StepVariable (finiteCells F) =>
      G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) (0, η) := by
  classical
  set ι := ↥(chordBonds (finiteCells F)) with hι
  set l := Fintype.card (ι × Fin 3) with hl
  set en : Fin l ≃ ι × Fin 3 := (Fintype.equivFin (ι × Fin 3)).symm with hen
  set b : Fin l → ι := fun i => (en i).1 with hb
  set u : Fin l → EuclideanSpace ℝ (Fin 3) := fun i => EuclideanSpace.single (en i).2 (1 : ℝ) with hu
  have hun : ∀ i, ‖u i‖ = 1 := fun i => by simp [hu]
  set c' : Fin (j + 4) → F.Site F.top × Fin 4 :=
    Fin.addCases (motive := fun _ => F.Site F.top × Fin 4) c fun _ : Fin 4 => (0, 0) with hc'
  set X' : Fin (j + 4) → imaginaryQuaternions :=
    Fin.addCases (motive := fun _ => imaginaryQuaternions) X fun _ : Fin 4 => unitImaginary with hX'd
  have hX' : AreUnitVectors X' := fun i => by
    induction i using Fin.addCases with
    | left i => simpa [hX'd] using hX i
    | right i => simpa [hX'd] using norm_unitImaginary
  have hm0 := (hk η hη l (j + 4) b u c' X' (by omega) hun hX').1
  have hm : ContDiffAt ℝ 4 (jointDisplacement G η V b u c' X') 0 :=
    hm0.of_le (by exact_mod_cast (by omega : 4 ≤ l + (j + 4)))
  set Θ : (Fin j → ℝ) × StepVariable (finiteCells F) →L[ℝ] (Fin (l + (j + 4)) → ℝ) :=
    ContinuousLinearMap.pi fun i => Fin.addCases (motive := fun _ =>
      (Fin j → ℝ) × StepVariable (finiteCells F) →L[ℝ] ℝ)
      (fun a => (EuclideanSpace.proj (en a).2).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => EuclideanSpace ℝ (Fin 3)) (en a).1).comp
          (ContinuousLinearMap.snd ℝ (Fin j → ℝ) (StepVariable (finiteCells F)))))
      (fun a => Fin.addCases (motive := fun _ => (Fin j → ℝ) × StepVariable (finiteCells F) →L[ℝ] ℝ)
        (fun a' => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin j => ℝ) a').comp
          (ContinuousLinearMap.fst ℝ (Fin j → ℝ) (StepVariable (finiteCells F))))
        (fun _ => 0) a) i with hΘ
  have hleft : ∀ (q : (Fin j → ℝ) × StepVariable (finiteCells F)) (a : Fin l),
      Θ q (Fin.castAdd (j + 4) a) = (q.2 (en a).1) (en a).2 := fun q a => by
    simp [hΘ, Fin.addCases_left]
  have hright : ∀ (q : (Fin j → ℝ) × StepVariable (finiteCells F)) (a : Fin (j + 4)),
      Θ q (Fin.natAdd l a) = Fin.addCases (motive := fun _ => ℝ) q.1 (fun _ : Fin 4 => 0) a := fun q a => by
    induction a using Fin.addCases with
    | left a => simp [hΘ, Fin.addCases_left, Fin.addCases_right]
    | right a => simp [hΘ, Fin.addCases_right]
  have hpt : ∀ ζ : StepVariable (finiteCells F), ∑ i, (Pi.single (b i) ((ζ (en i).1) (en i).2 • u i) :
      StepVariable (finiteCells F)) = ζ := fun ζ => by
    have := sum_single_coords (ι := ι) ζ
    rw [← Equiv.sum_comp en] at this
    exact this
  have hmoved : ∀ q : (Fin j → ℝ) × StepVariable (finiteCells F),
      jointDisplacement G η V b u c' X' (Θ (q.1, q.2 - η)) =
        G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V) := fun q => by
    have e1 : (fun i => Θ (q.1, q.2 - η) (Fin.natAdd l i)) =
        Fin.addCases (motive := fun _ => ℝ) q.1 (fun _ : Fin 4 => 0) :=
      funext fun a => hright (q.1, q.2 - η) a
    have hs : ColdStepAtMirrorFrames.bondSpread c' X' (Fin.addCases (motive := fun _ => ℝ) q.1 fun _ : Fin 4 => 0) =
        ColdStepAtMirrorFrames.bondSpread c X q.1 := bondSpread_addCases_zero c X (0, 0) unitImaginary q.1
    simp only [jointDisplacement, displacedPoint, hleft]
    rw [e1, hs, hpt]
    simp
  have hS : ContDiff ℝ 4 (fun q : (Fin j → ℝ) × StepVariable (finiteCells F) => Θ (q.1, q.2 - η)) :=
    Θ.contDiff.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))
  have hz : Θ ((0 : Fin j → ℝ), η - η) = 0 := by
    rw [sub_self]
    exact map_zero Θ
  have := ContDiffAt.comp (g := jointDisplacement G η V b u c' X')
    ((0, η) : (Fin j → ℝ) × StepVariable (finiteCells F)) (by
      change ContDiffAt ℝ 4 _ (Θ ((0 : Fin j → ℝ), η - η))
      rw [hz]
      exact hm) hS.contDiffAt
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
  exact (hmoved q).symm
private theorem contDiffAt_joint (hk : KernelBound ρ r P A G V) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ ≤ ρ) :
    ContDiffAt ℝ 4 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) (0, η) := by
  have h := contDiffAt_joint_of_unit hk k c (fun l => normalize (X l)) η hη fun l => norm_normalize _
  have hL : ContDiff ℝ 4 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => (scaleByNorms X q.1, q.2)) :=
    ((scaleByNorms X).contDiff.comp contDiff_fst).prodMk contDiff_snd
  have := ContDiffAt.comp (g := fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
    G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c (fun l => normalize (X l)) q.1) V))
    ((0, η) : (Fin k → ℝ) × StepVariable (finiteCells F)) (by
      change ContDiffAt ℝ 4 _ (scaleByNorms X 0, η)
      rw [map_zero]
      exact h) hL.contDiffAt
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
  simp only [Function.comp]
  rw [bondSpread_scaleByNorms]
private theorem hasDecayingKernels_of_kernelBound {Y : F.Cell} {B : ℝ} (hk : KernelBound ρ r {Y} A G V)
    (h1 : ∀ k, k ≤ 3 → A 1 k ≤ B) (h2 : A 2 0 ≤ B) : HasDecayingKernels ρ B r Y G V := by
  refine ⟨fun k c X η hη => contDiffAt_joint hk k c X η hη, ?_, ?_⟩
  · intro k c X η b u hk3 hη hu hX
    have h := (hk η hη 1 k ![b] ![u] c X (by omega) (fun i => by
      rw [Subsingleton.elim i 0]
      simpa using hu) hX).2
    exact h.trans (mul_le_mul_of_nonneg_right (h1 k hk3) (Real.exp_pos _).le)
  · intro η b b' u u' hη hu hu'
    have h := (hk η hη 2 0 ![b, b'] ![u, u'] ![] ![] (by omega) (fun i => by
      fin_cases i
      · simpa using hu
      · simpa using hu') (fun i => i.elim0)).2
    have e : topBondCells (![] : Fin 0 → F.Site F.top × Fin 4) = ∅ := by simp [topBondCells]
    rw [e, Finset.union_empty] at h
    exact h.trans (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le)
private theorem jointMixedDeriv_nil (H : AboveFrames F) (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) {k : ℕ}
    (hk : 1 ≤ k) (hk3 : k ≤ 3) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    jointMixedDeriv H η V (![] : Fin 0 → ↥(chordBonds (finiteCells F))) ![] c X = bondDeriv (H η) V c X := by
  interval_cases k <;>
  · have e : jointDisplacement H η V (![] : Fin 0 → ↥(chordBonds (finiteCells F))) ![] c X =
        fun τ => H η (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) := by
      funext τ
      have h1 : displacedPoint η (![] : Fin 0 → ↥(chordBonds (finiteCells F))) ![]
          (fun i => τ (Fin.castAdd _ i)) = η := by simp [displacedPoint]
      have h2 : (fun i => τ (Fin.natAdd 0 i)) = τ := by
        funext i
        congr 1
        exact Fin.ext (by simp)
      simp only [jointDisplacement]
      rw [h1, h2]
    unfold jointMixedDeriv bondDeriv
    rw [e]
private theorem cellSupDist_sub_unitStep_le (Y : F.Cell) (i : Fin 4) : cellSupDist Y (Y - unitStep F.top i) ≤ 1 := by
  refine Finset.sup_le fun l _ => ?_
  have e : Y l - (Y - unitStep F.top i : F.Site F.top) l =
      (((Pi.single i 1 : Fin 4 → ℤ) l : ℤ) : ZMod (F.period F.top l)) := by
    simp [unitStep, siteOfCoords]
  rw [e]
  refine (natAbs_valMinAbs_intCast_le _ _).trans ?_
  by_cases hl : l = i
  · subst hl
    simp
  · simp [Pi.single_eq_of_ne hl]
private theorem eventually_basic_bounds :
    EventuallyInParameters fun T => Odd T.L ∧ 0 < T.κ ∧ 0 < T.σ ∧ 64 ≤ T.n₀ := by
  intro a ha
  refine ⟨0, fun L hL _ c _ => ⟨0, fun Ct _ => ⟨1, one_pos, fun κ hκ _ => ⟨1, one_pos, fun η₃ _ _ _ =>
    ⟨0, fun nss _ => ⟨1, one_pos, fun σ hσ _ p _ => ⟨0, fun Cs _ E _ => ⟨64, fun n₀ hn =>
      ⟨0, fun CE _ => ⟨0, fun y₁ _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  exact ⟨hL, hκ, hσ, hn⟩
private def kernelBoundSum (A : ℕ → ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range 4, (A 1 k + A 0 k) + A 2 0
private theorem kernelBoundSum_nonneg {A : ℕ → ℕ → ℝ} (hA : ∀ l j, 0 < A l j) : 0 ≤ kernelBoundSum A :=
  add_nonneg (Finset.sum_nonneg fun k _ => (add_pos (hA _ _) (hA _ _)).le) (hA _ _).le
private theorem le_kernelSum_two {A : ℕ → ℕ → ℝ} (hA : ∀ l j, 0 < A l j) : A 2 0 ≤ kernelBoundSum A := by
  have : 0 ≤ ∑ k ∈ Finset.range 4, (A 1 k + A 0 k) := Finset.sum_nonneg fun k _ => (add_pos (hA _ _) (hA _ _)).le
  unfold kernelBoundSum
  linarith
private theorem le_kernelSum_one {A : ℕ → ℕ → ℝ} (hA : ∀ l j, 0 < A l j) {k : ℕ} (hk : k ≤ 3) :
    A 1 k + A 0 k ≤ kernelBoundSum A := by
  have h := Finset.single_le_sum (f := fun k => A 1 k + A 0 k) (s := Finset.range 4)
    (fun k _ => (add_pos (hA _ _) (hA _ _)).le) (Finset.mem_range.2 (by omega : k < 4))
  have := hA 2 0
  unfold kernelBoundSum
  linarith
end CostKernelBoundsAux
theorem costKernelBounds_holds (hK : blockKernelBoundsStatement)
    (hS : scoreRemainderKernelBoundsStatement) (hG : gapKernelBounds)
    (hH : haarDensityKernelBounds) (hgeo : CubicTorusCellGeometry)
    (hcov : BlocksCoverLowerLevel) : costKernelBoundsStatement := by
  open CostKernelBoundsAux in
  classical
  obtain ⟨D₁, p₁, gB⟩ := hK
  obtain ⟨D₂, p₂, gS⟩ := hS
  obtain ⟨D₃, p₃, gG⟩ := hG
  obtain ⟨D₄, p₄, gH⟩ := hH
  obtain ⟨C₁, hC₁, hsum⟩ := hgeo.2 1 one_pos
  set Bf : StepParameters → ℝ := fun E => 1 + kernelBoundSum (D₁ E) + Real.exp (2 * (2 ^ 7 * E.κ)) * kernelBoundSum (D₂ E) +
    C₁ * (E.L : ℝ) ^ 4 * kernelBoundSum (D₁ E) + (4 * kernelBoundSum (D₃ E) + C₁ * (E.L : ℝ) ^ 4 * kernelBoundSum (D₄ E)) with hBf
  have hb₁ := fun E => kernelBoundSum_nonneg (p₁ E)
  have hb₂ := fun E => kernelBoundSum_nonneg (p₂ E)
  have hb₃ := fun E => kernelBoundSum_nonneg (p₃ E)
  have hb₄ := fun E => kernelBoundSum_nonneg (p₄ E)
  refine ⟨fun T => Bf (rateParameters T), fun T => ?_, ?_⟩
  · have h₁ := hb₁ (rateParameters T)
    have h₂ := hb₂ (rateParameters T)
    have h₃ := hb₃ (rateParameters T)
    have h₄ := hb₄ (rateParameters T)
    simp only [hBf]
    positivity
  refine EventuallyInParameters.mono (EventuallyInParameters.and eventually_basic_bounds
    (EventuallyInParameters.and gB (EventuallyInParameters.and gS
    (EventuallyInParameters.and gG gH)))) fun T h => ?_
  obtain ⟨⟨hLo, hκ, hσ, hn⟩, gB, gS, gG, gH⟩ := h
  show CostKernelBoundsAt T (Bf (rateParameters T))
  intro t x f F V Y hst
  set E := rateParameters T with hE
  set Q := coldHalfLawAt T x f with hQ
  have hEL : E.L = T.L := rfl
  have hEκ : E.κ = T.κ := rfl
  obtain ⟨hFL, hFt, N, hside, hN₀⟩ := id hst.torus
  have hodd : Odd F.blockSide := hFL ▸ hLo
  have hcub : IsLargeCubicTorus F := ⟨N, hn.trans hN₀, hside⟩
  have hpos : ∀ i, 0 < F.extent i := fun i => by
    rw [hside i]
    omega
  have hall := hcov F hodd hpos
  have hbond : ∀ d : F.Site F.depth × Fin 4, d ∈ fineBonds F := fun d => by
    simp [fineBonds, hall]
  have hg1 := hgeo.1 F hodd hcub
  have hzd : ∀ z : F.Cell, cellSupDist z z = 0 := fun z => by simp [cellSupDist]
  have hsym : ∀ x y : F.Cell, cellSupDist x y = cellSupDist y x := hg1.2.2.1
  have htri : ∀ x y z : F.Cell, cellSupDist x z ≤ cellSupDist x y + cellSupDist y z := hg1.2.2.2.1
  have hs1 := hsum F hodd hcub Y
  rw [hFL] at hs1
  set Nn : ℝ := C₁ * (T.L : ℝ) ^ 4 with hNn
  have hNn0 : 0 ≤ Nn := by positivity
  have count : ∀ S : Finset (F.Site F.depth × Fin 4), (∀ d ∈ S, enclosingCell d.1 = Y) → (S.card : ℝ) ≤ Nn := by
    intro S hS'
    have h1 : ∀ d ∈ S, Real.exp (-(1 * (cellSupDist (enclosingCell d.1) Y : ℝ))) = 1 := fun d hd => by
      rw [hS' d hd, hzd]
      simp
    calc (S.card : ℝ) = ∑ _d ∈ S, (1 : ℝ) := by simp
      _ = ∑ d ∈ S, Real.exp (-(1 * (cellSupDist (enclosingCell d.1) Y : ℝ))) := (Finset.sum_congr rfl h1).symm
      _ ≤ ∑ d ∈ fineBonds F, Real.exp (-(1 * cellSupDist (enclosingCell d.1) Y)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun d _ => hbond d) fun _ _ _ => (Real.exp_pos _).le
      _ ≤ Nn := hs1
  have hρ0 : 0 ≤ T.ballRadius := by
    show 0 ≤ T.σ / 64
    positivity
  have hr₀ : (0 : ℝ) ≤ 2 ^ 7 * T.κ := by positivity
  have hr₁ : (2 : ℝ) ^ 7 * T.κ ≤ 2 ^ 8 * T.κ := by nlinarith
  set Bv : ℝ := Bf E with hBv
  set t₁ := kernelBoundSum (D₁ E)
  set t₂ := Real.exp (2 * (2 ^ 7 * T.κ)) * kernelBoundSum (D₂ E)
  set t₃ := Nn * kernelBoundSum (D₁ E)
  set t₄ := 4 * kernelBoundSum (D₃ E) + Nn * kernelBoundSum (D₄ E)
  have hBsum : Bv = 1 + t₁ + t₂ + t₃ + t₄ := rfl
  have n₁ : 0 ≤ t₁ := hb₁ E
  have n₂ : 0 ≤ t₂ := mul_nonneg (Real.exp_pos _).le (hb₂ E)
  have n₃ : 0 ≤ t₃ := mul_nonneg hNn0 (hb₁ E)
  have n₄ : 0 ≤ t₄ := add_nonneg (mul_nonneg (by norm_num) (hb₃ E)) (mul_nonneg hNn0 (hb₄ E))
  have l₁ : ∀ {A : ℕ → ℕ → ℝ}, (∀ l j, 0 < A l j) → ∀ k, k ≤ 3 → A 1 k ≤ kernelBoundSum A := fun {A} hA k hk => by
    have h := le_kernelSum_one hA hk
    have := hA 0 k
    linarith
  have l₀ : ∀ {A : ℕ → ℕ → ℝ}, (∀ l j, 0 < A l j) → ∀ k, k ≤ 3 → A 0 k ≤ kernelBoundSum A := fun {A} hA k hk => by
    have h := le_kernelSum_one hA hk
    have := hA 1 k
    linarith
  have kCost : KernelBound T.ballRadius (2 ^ 7 * T.κ) {Y} (D₁ E) (Q.blockCost Y) V := fun η hη l j b u c X hl hu hX =>
    (gB x t F V 1 η hst.coupling_le hst.torus hst.small_curvature zero_le_one le_rfl hη l j b u c X hl hu hX).1 Y
  have kScore : ∀ (i : Fin 4) (back : Bool), KernelBound T.ballRadius (2 ^ 7 * T.κ) {Y}
      (fun l j => Real.exp (2 * (2 ^ 7 * T.κ)) * D₂ E l j) (Q.scoreRemainderAt (cellBond Y i back)) V := by
    intro i back
    have h0 : KernelBound T.ballRadius (2 ^ 8 * T.κ) {(cellBond Y i back).1} (D₂ E)
        (Q.scoreRemainderAt (cellBond Y i back)) V :=
      fun η hη l j b u c X hl hu hX =>
        gS x t f F V η hst.coupling_le hst.torus hst.small_curvature hη _ l j b u c X hl hu hX
    refine kernelBound_shift_anchor hzd hsym (fun v => ?_) hr₀ hr₁ (fun l j => (p₂ E l j).le) h0
    have hstep : cellSupDist Y (cellBond Y i back).1 ≤ 1 := by
      cases back with
      | true => exact cellSupDist_sub_unitStep_le Y i
      | false =>
        show cellSupDist Y Y ≤ 1
        rw [hzd]
        omega
    have := htri Y (cellBond Y i back).1 v
    omega
  have kShare : ∀ y : F.Site F.depth, enclosingCell y = Y → KernelBound T.ballRadius (2 ^ 7 * T.κ) {Y} (D₁ E)
      (fun η V' => minimalSiteShare Q.a y (interpolatedField 1 Q.a Q.chartRadius Q.mirrorRadius V' η)) V := by
    intro y hy η hη l j b u c X hl hu hX
    have h := (gB x t F V 1 η hst.coupling_le hst.torus hst.small_curvature zero_le_one le_rfl hη l j b u c X hl hu hX).2 y
    rw [hy] at h
    exact h
  have cardSites : ∀ S : Finset (F.Site F.depth), (∀ y ∈ S, enclosingCell y = Y) → (S.card : ℝ) ≤ Nn := by
    intro S hS'
    have h := count (S.image fun y => (y, (0 : Fin 4))) (fun d hd => by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hd
      exact hS' y hy)
    rwa [Finset.card_image_of_injective _ (fun a b e => (Prod.ext_iff.1 e).1)] at h
  have kGap : ∀ c₀ ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
      KernelBound T.ballRadius (2 ^ 7 * T.κ) {Y} (D₃ E)
      (fun η V' => haarGapExcess Q.a Q.coupling (interpolatedField 1 Q.a Q.chartRadius Q.mirrorRadius V' η) c₀) V := by
    intro c₀ hc
    have h1 : c₀.1 = Y := (Finset.mem_filter.1 hc).2
    have h2 : KernelBound T.ballRadius (2 ^ 8 * T.κ) {Y} (D₃ E) (fun η V' => haarGap (T.a * x *
        ‖contourAverage (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) V' η) c₀‖)) V := by
      intro η hη l j b u c X hl hu hX
      have h := gG x t F V 1 η hst.coupling_le hst.torus hst.small_curvature zero_le_one le_rfl hη c₀ l j b u c X hl hu hX
      rw [h1] at h
      exact h
    exact kernelBound_rate_mono hr₀ hr₁ (fun l j => (p₃ E l j).le) (kernelBound_sub_const _ h2)
  have kHaar : ∀ b₀ ∈ (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = Y),
      KernelBound T.ballRadius (2 ^ 7 * T.κ) {Y} (D₄ E)
        (fun η V' => haarLogRatio (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V' η b₀.1.1 b₀.1.2)) V := by
    intro b₀ hb
    have h1 : enclosingCell b₀.1.1 = Y := (Finset.mem_filter.1 hb).2
    have h2 : KernelBound T.ballRadius (2 ^ 8 * T.κ) {Y} (D₄ E)
        (fun η V' => haarLogRatio (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V' η b₀.1.1 b₀.1.2)) V := by
      intro η hη l j b u c X hl hu hX
      have h := gH x t F V 1 η hst.coupling_le hst.torus hst.small_curvature zero_le_one le_rfl hη b₀ l j b u c X hl hu hX
      rw [h1] at h
      exact h
    exact kernelBound_rate_mono hr₀ hr₁ (fun l j => (p₄ E l j).le) h2
  have cardBonds : (((innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y)).card : ℝ) ≤ 4 := by
    have h : ((innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y)).card ≤
        (Finset.univ : Finset (Fin 4)).card := by
      refine Finset.card_le_card_of_injOn (fun c => c.2) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_
      intro a ha b hb e
      exact Prod.ext (((Finset.mem_filter.1 ha).2).trans ((Finset.mem_filter.1 hb).2).symm) e
    simpa using (by exact_mod_cast h : (((innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y)).card : ℝ) ≤
      ((Finset.univ : Finset (Fin 4)).card : ℝ))
  have cardChart : (((Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) =>
      enclosingCell b.1.1 = Y).card : ℕ) : ℝ) ≤ Nn := by
    have h := count ((Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) =>
        enclosingCell b.1.1 = Y).image Subtype.val)
      (fun d hd => by
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hd
        exact (Finset.mem_filter.1 hy).2)
    rwa [Finset.card_image_of_injective _ Subtype.val_injective] at h
  have kGaps : KernelBound T.ballRadius (2 ^ 7 * T.κ) {Y} (fun l j => 4 * D₃ E l j + Nn * D₄ E l j)
      (Q.blockGapTerms Y) V := by
    have h1 := kernelBound_sum_one _ _ kGap
    have h2 := kernelBound_sum_one _ _ kHaar
    have h3 := kernelBound_add h1 h2
    have e : (fun η V' => (∑ i ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
          haarGapExcess Q.a Q.coupling (interpolatedField 1 Q.a Q.chartRadius Q.mirrorRadius V' η) i) +
        ∑ i ∈ Finset.univ.filter (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = Y),
          haarLogRatio (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V' η i.1.1 i.1.2)) =
        Q.blockGapTerms Y := by
      funext η V'
      simp only [ColdHalfLaw.blockGapTerms, Finset.sum_filter]
    rw [e] at h3
    refine kernelBound_mono (fun l j => ?_) h3
    exact add_le_add (mul_le_mul_of_nonneg_right cardBonds (p₃ E l j).le)
      (mul_le_mul_of_nonneg_right cardChart (p₄ E l j).le)
  refine ⟨hasDecayingKernels_of_kernelBound kCost (fun k hk => ?_) ?_,
    fun i back => hasDecayingKernels_of_kernelBound (kScore i back) (fun k hk => ?_) ?_,
    fun w B' hB' hw => ?_, hasDecayingKernels_of_kernelBound kGaps (fun k hk => ?_) ?_, ?_⟩
  · have := l₁ (p₁ E) k hk
    linarith
  · have := le_kernelSum_two (p₁ E)
    linarith
  · have := mul_le_mul_of_nonneg_left (l₁ (p₂ E) k hk) (Real.exp_pos (2 * (2 ^ 7 * T.κ))).le
    linarith
  · have := mul_le_mul_of_nonneg_left (le_kernelSum_two (p₂ E)) (Real.exp_pos (2 * (2 ^ 7 * T.κ))).le
    linarith
  · have hS' : ∀ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
        KernelBound T.ballRadius (2 ^ 7 * T.κ) {Y} (D₁ E)
        ((fun y η V' => minimalSiteShare Q.a y (interpolatedField 1 Q.a Q.chartRadius Q.mirrorRadius V' η)) y) V :=
      fun y hy => kShare y (Finset.mem_filter.1 hy).2
    have h1 := kernelBound_sum _ w
      (fun y η V' => minimalSiteShare Q.a y (interpolatedField 1 Q.a Q.chartRadius Q.mirrorRadius V' η)) hS'
    have hw' : ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y), |w y| ≤ Nn * B' := by
      refine (Finset.sum_le_card_nsmul _ _ B' fun y _ => hw y).trans ?_
      rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (cardSites _ fun y hy => (Finset.mem_filter.1 hy).2) hB'.le
    have aux : ∀ a, 0 ≤ a → a ≤ t₁ →
        (∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y), |w y|) * a ≤ Bv * B' := by
      intro a h0 ha
      calc _ ≤ (Nn * B') * t₁ := mul_le_mul hw' ha h0 (by positivity)
        _ = t₃ * B' := by ring
        _ ≤ Bv * B' := mul_le_mul_of_nonneg_right (by linarith) hB'.le
    exact hasDecayingKernels_of_kernelBound (G := Q.weightedSiteShares w Y) h1
      (fun k hk => aux _ (p₁ E 1 k).le (l₁ (p₁ E) k hk))
      (aux _ (p₁ E 2 0).le (le_kernelSum_two (p₁ E)))
  · have h1 := mul_le_mul_of_nonneg_left (l₁ (p₃ E) k hk) (by norm_num : (0 : ℝ) ≤ 4)
    have h2 := mul_le_mul_of_nonneg_left (l₁ (p₄ E) k hk) hNn0
    show 4 * D₃ E 1 k + Nn * D₄ E 1 k ≤ Bv
    linarith
  · have h1 := mul_le_mul_of_nonneg_left (le_kernelSum_two (p₃ E)) (by norm_num : (0 : ℝ) ≤ 4)
    have h2 := mul_le_mul_of_nonneg_left (le_kernelSum_two (p₄ E)) hNn0
    show 4 * D₃ E 2 0 + Nn * D₄ E 2 0 ≤ Bv
    linarith
  · intro k c X h1 h3 hX
    have h := (kGaps 0 (fun b => by simpa using hρ0) 0 k ![] ![] c X (by omega) (fun i => i.elim0) hX).2
    rw [jointMixedDeriv_nil _ _ _ h1 h3] at h
    refine h.trans (mul_le_mul ?_ (Real.exp_le_exp.2 (neg_le_neg ?_)) (Real.exp_pos _).le (by linarith))
    · have e1 := mul_le_mul_of_nonneg_left (l₀ (p₃ E) k h3) (by norm_num : (0 : ℝ) ≤ 4)
      have e2 := mul_le_mul_of_nonneg_left (l₀ (p₄ E) k h3) hNn0
      show 4 * D₃ E 0 k + Nn * D₄ E 0 k ≤ Bv
      linarith
    · set Z := ({Y} ∪ chordBondCells (![] : Fin 0 → ↥(chordBonds (finiteCells F))) ∪ topBondCells c : Finset F.Cell)
      have hY : Y ∈ Z := by simp [Z]
      have hc : ∀ l, (c l).1 ∈ Z := fun l => by
        refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨l, Finset.mem_univ _, rfl⟩)
      have hs : bondSpan Y c ≤ cellSetDiameter Z := by
        refine max_le (Finset.sup_le fun l _ => cellSupDist_le_diameter hY (hc l)) (Finset.sup_le fun l _ =>
          Finset.sup_le fun l' _ => cellSupDist_le_diameter (hc l) (hc l'))
      have hs' : (bondSpan Y c : ℝ) ≤ cellSetDiameter Z := by exact_mod_cast hs
      have h0 : (0 : ℝ) ≤ bondSpan Y c := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hs' hr₀, mul_nonneg hκ.le h0]
end ResponseInTheExpansion
end YangMills.Construction
end
