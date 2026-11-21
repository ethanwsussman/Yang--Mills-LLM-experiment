import YangMills.Construction.SummableBoundsOfTheFlow.LeastChartEnergyIsSmoothProof
import YangMills.Construction.ClusterExpansionOfAStep.ChartsOverTheTopOfAStep
import YangMills.Construction.ResponseInTheExpansion.OneStepOfTheMaxwellForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages WeightedResponses TorusFields TorusLumps StepCosts TopLevelSites LatticePaths
namespace ResponseInTheExpansion.SingleColourFields
def colourRotation (s : ℝ) : UnitQuaternion := expUnit (s • unitGenerator)
theorem unitGenerator_re : (unitGenerator : ℍ[ℝ]).re = 0 := rfl
theorem unitGenerator_imI : (unitGenerator : ℍ[ℝ]).imI = 1 := rfl
theorem unitGenerator_imJ : (unitGenerator : ℍ[ℝ]).imJ = 0 := rfl
theorem unitGenerator_imK : (unitGenerator : ℍ[ℝ]).imK = 0 := rfl
def colourPlane (C S : ℝ) : ℍ[ℝ] := (C : ℍ[ℝ]) + S • (unitGenerator : ℍ[ℝ])
@[simp] theorem colourPlane_re (C S : ℝ) : (colourPlane C S).re = C := by simp [colourPlane, unitGenerator_re]
@[simp] theorem colourPlane_imI (C S : ℝ) : (colourPlane C S).imI = S := by simp [colourPlane, unitGenerator_imI]
@[simp] theorem colourPlane_imJ (C S : ℝ) : (colourPlane C S).imJ = 0 := by simp [colourPlane, unitGenerator_imJ]
@[simp] theorem colourPlane_imK (C S : ℝ) : (colourPlane C S).imK = 0 := by simp [colourPlane, unitGenerator_imK]
theorem norm_unitGenerator : ‖(unitGenerator : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.ChartedEnergyRegularity.norm_coe_imaginaryUnit <;> assumption
theorem coe_colourRotation (s : ℝ) :
    ((colourRotation s : UnitQuaternion) : ℍ[ℝ]) = colourPlane (Real.cos s) (Real.sin s) := by
  show NormedSpace.exp (((s • unitGenerator : imaginaryQuaternions)) : ℍ[ℝ]) = _
  rw [exp_imaginary]
  have hn : ‖((s • unitGenerator : imaginaryQuaternions) : ℍ[ℝ])‖ = |s| := by
    rw [Submodule.coe_smul, norm_smul, norm_unitGenerator, mul_one, Real.norm_eq_abs]
  have hk : Real.sin |s| / |s| * s = Real.sin s := by
    rcases eq_or_ne s 0 with rfl | h0
    · simp
    · rcases abs_cases s with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e]
      · field_simp
      · rw [Real.sin_neg]
        field_simp
  rw [hn, Real.cos_abs, Submodule.coe_smul, smul_smul, hk]
  rfl
theorem colourRotation_add (s t : ℝ) : colourRotation (s + t) = colourRotation s * colourRotation t := by
  apply Subtype.ext
  show ((colourRotation (s + t) : UnitQuaternion) : ℍ[ℝ]) =
    ((colourRotation s : UnitQuaternion) : ℍ[ℝ]) * ((colourRotation t : UnitQuaternion) : ℍ[ℝ])
  rw [coe_colourRotation, coe_colourRotation, coe_colourRotation]
  apply Quaternion.ext <;> simp [Real.cos_add, Real.sin_add] <;> ring
theorem colourRotation_zero : colourRotation 0 = 1 := by
  apply Subtype.ext
  show ((colourRotation 0 : UnitQuaternion) : ℍ[ℝ]) = 1
  rw [coe_colourRotation]
  apply Quaternion.ext <;> simp
theorem colourRotation_inv (s : ℝ) : (colourRotation s)⁻¹ = colourRotation (-s) :=
  inv_eq_of_mul_eq_one_right (by rw [← colourRotation_add, add_neg_cancel, colourRotation_zero])
theorem expOfColourForm_apply {m : ℕ} (τ : ℝ) (A : TorusBond m → ℝ) (x : TorusSite m) (i : Fin 4) :
    expOfColourForm τ A x i = colourRotation (τ * A (x, i)) := rfl
def torusStep (N : ℕ) (st : PathStep) : TorusSite N :=
  if st.2 then TorusFields.unitStep N st.1 else - TorusFields.unitStep N st.1
def sumAlongPath {N : ℕ} (θ : TorusBond N → ℝ) : TorusSite N → List PathStep → ℝ
  | _, [] => 0
  | x, st :: r => (if st.2 then θ (x, st.1) else - θ (x - TorusFields.unitStep N st.1, st.1)) +
      sumAlongPath θ (x + torusStep N st) r
section Read
variable {G : BlockFrame} {j N : ℕ} [NeZero N]
theorem pathHolonomy_readAtLevel (hp : ∀ i, G.period j i = N) (τ : ℝ) (A : TorusBond N → ℝ)
    (steps : List PathStep) :
    ∀ x : G.Site j, pathHolonomy (readAtLevel G j (expOfColourForm τ A)) x steps =
      colourRotation (τ * sumAlongPath A (toTorusSite N x) steps) := by
  induction steps with
  | nil =>
    intro x
    simp [pathHolonomy, sumAlongPath, colourRotation_zero]
  | cons st r ih =>
    intro x
    have hv : toTorusSite N (x + stepDisplacement j st) = toTorusSite N x + torusStep N st := by
      obtain ⟨i, b⟩ := st
      cases b
      · simp [stepDisplacement, torusStep, toTorusSite_add hp, toTorusSite_neg hp, toTorusSite_unitStep hp]
      · simp [stepDisplacement, torusStep, toTorusSite_add hp, toTorusSite_unitStep hp]
    have hs : linkValue (readAtLevel G j (expOfColourForm τ A)) x st =
        colourRotation (τ * (if st.2 then A (toTorusSite N x, st.1)
          else - A (toTorusSite N x - TorusFields.unitStep N st.1, st.1))) := by
      obtain ⟨i, b⟩ := st
      cases b
      · have e : toTorusSite N (x - BlockAverages.unitStep j i) =
            toTorusSite N x - TorusFields.unitStep N i := by
          rw [sub_eq_add_neg, toTorusSite_add hp, toTorusSite_neg hp, toTorusSite_unitStep hp, sub_eq_add_neg]
        show (readAtLevel G j (expOfColourForm τ A) (x - BlockAverages.unitStep j i) i)⁻¹ = _
        show (expOfColourForm τ A (toTorusSite N (x - BlockAverages.unitStep j i)) i)⁻¹ = _
        rw [e, expOfColourForm_apply, colourRotation_inv]
        simp
      · show expOfColourForm τ A (toTorusSite N x) i = _
        rw [expOfColourForm_apply]
        simp
    simp only [pathHolonomy]
    rw [ih, hs, hv, ← colourRotation_add]
    congr 1
    simp only [sumAlongPath]
    ring
end Read
def coarseStart {n : ℕ} (L N : ℕ) (x : TorusSite n) : TorusSite N :=
  siteOfInt fun i => (L : ℤ) * ((x i).cast : ℤ)
def contourSum (L : ℕ) {n N : ℕ} (θ : TorusBond N → ℝ) (c : TorusBond n)
    (k : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) : ℝ :=
  sumAlongPath θ (coarseStart L N c.1) (bondContour L k.1 k.2 c.2)
def contourIndex (L : ℕ) : Finset ((Fin 4 → ℤ) × Equiv.Perm (Fin 4)) := centredCube L ×ˢ Finset.univ
def contourWeight (L : ℕ) : ℝ := 1 / (24 * (L : ℝ) ^ 4)
def contourCosMean (L : ℕ) {n N : ℕ} (θ : TorusBond N → ℝ) (c : TorusBond n) (τ : ℝ) : ℝ :=
  ∑ k ∈ contourIndex L, contourWeight L * Real.cos (τ * contourSum L θ c k)
def contourSinMean (L : ℕ) {n N : ℕ} (θ : TorusBond N → ℝ) (c : TorusBond n) (τ : ℝ) : ℝ :=
  ∑ k ∈ contourIndex L, contourWeight L * Real.sin (τ * contourSum L θ c k)
theorem sum_contourWeight {L : ℕ} (hL : Odd L) : ∑ _k ∈ contourIndex L, contourWeight L = 1 := by
  have hL0 : (L : ℝ) ≠ 0 := by
    have : L ≠ 0 := by
      rintro rfl
      simp at hL
    exact_mod_cast this
  rw [Finset.sum_const, contourIndex, Finset.card_product, card_centredCube hL, Finset.card_univ,
    Fintype.card_perm]
  simp [contourWeight, Nat.factorial]
  field_simp
theorem sum_colourPlane {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    ∑ k ∈ s, colourPlane (f k) (g k) = colourPlane (∑ k ∈ s, f k) (∑ k ∈ s, g k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp
    apply Quaternion.ext <;> simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, ih, Finset.sum_insert hi, Finset.sum_insert hi]
    apply Quaternion.ext <;> simp
theorem norm_colourPlane (C S : ℝ) : ‖colourPlane C S‖ = Real.sqrt (C ^ 2 + S ^ 2) := by
  have h := Quaternion.normSq_eq_norm_mul_self (colourPlane C S)
  rw [Quaternion.normSq_def'] at h
  simp only [colourPlane_re, colourPlane_imI, colourPlane_imJ, colourPlane_imK] at h
  have e : C ^ 2 + S ^ 2 + 0 ^ 2 + 0 ^ 2 = C ^ 2 + S ^ 2 := by ring
  rw [e] at h
  rw [h, Real.sqrt_mul_self (norm_nonneg _)]
section Contour
variable {G : BlockFrame} {j N n : ℕ} [NeZero N] [NeZero n]
theorem contourAverage_readAtLevel (hp : ∀ i, G.period j i = N) (hq : ∀ i, G.period (j + 1) i = n) (τ : ℝ)
    (θ : TorusBond N → ℝ) (c : TorusBond n) :
    contourAverage (readAtLevel G j (expOfColourForm τ θ))
        ((torusSiteInFrame G (j + 1) c.1, c.2) : G.Site (j + 1) × Fin 4) =
      colourPlane (contourCosMean G.blockSide θ c τ) (contourSinMean G.blockSide θ c τ) := by
  have hd : toTorusSite N (refineSite (torusSiteInFrame G (j + 1) c.1) : G.Site j) =
      coarseStart G.blockSide N c.1 := by
    unfold refineSite coarseStart
    rw [toTorusSite_siteOfCoords hp]
    congr 1
    funext i
    rw [siteCoords_torusSiteInFrame hq]
  have hh : ∀ h π, ((pathHolonomy (readAtLevel G j (expOfColourForm τ θ))
      (refineSite (torusSiteInFrame G (j + 1) c.1))
      (bondContour G.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]) =
      colourPlane (Real.cos (τ * contourSum G.blockSide θ c (h, π)))
        (Real.sin (τ * contourSum G.blockSide θ c (h, π))) := by
    intro h π
    rw [pathHolonomy_readAtLevel hp, hd, coe_colourRotation]
    rfl
  unfold contourAverage
  simp only [hh]
  rw [← Finset.sum_product' (f := fun h π => colourPlane (Real.cos (τ * contourSum G.blockSide θ c (h, π)))
    (Real.sin (τ * contourSum G.blockSide θ c (h, π))))]
  simp only [Prod.mk.eta]
  rw [sum_colourPlane]
  unfold contourCosMean contourSinMean contourIndex contourWeight
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  apply Quaternion.ext <;> simp
theorem blockFit_readAtLevel (hp : ∀ i, G.period j i = N) (hq : ∀ i, G.period (j + 1) i = n) (τ : ℝ)
    (θ : TorusBond N → ℝ) (B : TorusBond n → ℝ) (c : TorusBond n) :
    blockFit (readAtLevel G j (expOfColourForm τ θ)) (readAtLevel G (j + 1) (expOfColourForm τ B))
        ((torusSiteInFrame G (j + 1) c.1, c.2) : G.Site (j + 1) × Fin 4) =
      Real.sqrt (contourCosMean G.blockSide θ c τ ^ 2 + contourSinMean G.blockSide θ c τ ^ 2) -
        (contourCosMean G.blockSide θ c τ * Real.cos (τ * B c) +
          contourSinMean G.blockSide θ c τ * Real.sin (τ * B c)) := by
  unfold blockFit
  rw [contourAverage_readAtLevel hp hq, norm_colourPlane]
  have hv : readAtLevel G (j + 1) (expOfColourForm τ B) (torusSiteInFrame G (j + 1) c.1) c.2 =
      colourRotation (τ * B c) := by
    rw [readAtLevel_torusSiteInFrame hq]
    rfl
  simp only [hv, colourRotation_inv, coe_colourRotation]
  simp
end Contour
theorem blockFit_nonneg {F : BlockFrame} {j : ℕ} (X : F.GaugeField j) (X' : F.GaugeField (j + 1))
    (c : F.Site (j + 1) × Fin 4) : 0 ≤ blockFit X X' c := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.blockFit_nonneg <;> assumption
end ResponseInTheExpansion.SingleColourFields
end YangMills.Construction
end
