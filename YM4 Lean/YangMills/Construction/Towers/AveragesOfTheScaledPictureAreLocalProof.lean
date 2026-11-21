import YangMills.Construction.Towers.TheFreeOperatorsArePeriodicOperatorsProof
import YangMills.Construction.Averaging.EverySmallRadiusServesProof
import YangMills.Construction.PeriodicOperators.NumbersOfALocalOperatorFunctionProof
import YangMills.Construction.Towers.AveragesOfTheScaledPictureAreLocal
import YangMills.Construction.Towers.KernelsOfTheScaledOperatorsAtEveryComplexConfigurationProof
import YangMills.Construction.Towers.LatticesOfSideInfinityOverAFiniteSide
import YangMills.Construction.Towers.SymbolsOfTheAveragesOnPlaneWavesProof
import YangMills.Construction.Towers.TranslationsAndIsometriesOfATower
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ScaledMeansLocality
open Matrices
open PeriodicOperators
open BackgroundJets (gaugeFieldOfForm)
theorem norm_pauliFamily (a : Fin 3) : ‖ComplexMatrix2.pauliFamily a‖ = 1 := by
  have hs : star (ComplexMatrix2.pauliFamily a) * ComplexMatrix2.pauliFamily a = 1 := by
    rw [Matrix.star_eq_conjTranspose]
    fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [ComplexMatrix2.pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
        OneLoop.pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
  have h := CStarRing.norm_star_mul_self (x := ComplexMatrix2.pauliFamily a)
  rw [hs, CStarRing.norm_one] at h
  nlinarith [norm_nonneg (ComplexMatrix2.pauliFamily a)]
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem real_smul_eq_complex_smul (x : ℝ) (X : ComplexMatrix2) : x • X = (x : ℂ) • X := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
theorem ofPauliCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem norm_ofPauliCoeffs_le {σ : Type} (c : Fin 3 × σ → ℂ) {r : ℝ} (h : ∀ i, ‖c i‖ ≤ r)
    (x : σ) : ‖ofPauliCoeffs c x‖ ≤ 3 * r := by
  unfold ofPauliCoeffs
  calc ‖∑ a, c (a, x) • ComplexMatrix2.pauliFamily a‖
        ≤ ∑ a, ‖c (a, x) • ComplexMatrix2.pauliFamily a‖ := norm_sum_le _ _
    _ = ∑ a, ‖c (a, x)‖ := by simp only [norm_smul, norm_pauliFamily, mul_one]
    _ ≤ ∑ _a : Fin 3, r := Finset.sum_le_sum fun a _ => h _
    _ = 3 * r := by simp
theorem pauliCoeff_real_smul {x : ℝ} (hx : x ≠ 0) (a : Fin 3) (Y : ComplexMatrix2) :
    pauliCoeff a (x • Y) = (x : ℂ) * pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.RescaledKernels.pauliCoeff_real_smul <;> assumption
section Kernels
variable {N N' : Type}
def basisFun (ι : N) : N → ℂ := open Classical in fun x => if x = ι then 1 else 0
theorem basisFun_self (ι : N) : basisFun ι ι = 1 := by simp [basisFun]
theorem basisFun_of_ne {ι x : N} (h : x ≠ ι) : basisFun ι x = 0 := by simp [basisFun, h]
theorem basisFun_comp {s s' : N → N} (h : ∀ x, s' (s x) = x) (h' : ∀ x, s (s' x) = x)
    (ι x : N) : basisFun (s ι) x = basisFun ι (s' x) := by
  by_cases hx : s' x = ι
  · have : x = s ι := by rw [← hx, h']
    rw [this, h, basisFun_self, basisFun_self]
  · have : x ≠ s ι := fun e => hx (by rw [e, h])
    rw [basisFun_of_ne this, basisFun_of_ne hx]
theorem kernel_eq_of_represents {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ}
    (h : Represents T M) (ι' : N') (ι : N) : T ι' ι = M (basisFun ι) ι' := by apply _root_.YangMills.Construction.Tower.FreeOperators.kernel_eq_apply_indicator <;> assumption
theorem map_zero_of_represents {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ}
    (h : Represents T M) (ι' : N') : M 0 ι' = 0 := by
  rw [← (h _).2]
  simp [applyKernel]
end Kernels
section Links
variable {a : ℝ}
theorem isPositivelyOriented_or_opposite (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem not_isPositivelyOriented_opposite (ha : 0 < a) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
end Links
section Forms
variable {L k : ℕ}
theorem finestMesh_pos (hL : 0 < L) : 0 < finestMesh L k := by
  unfold finestMesh meshAt
  exact zpow_pos (by exact_mod_cast hL) _
def pauliForm (ζ : (remainderIndex L k).Carrier → ℂ) : Edge L k 0 → ComplexMatrix2 :=
  (edgePauliCoordinates L k 0).ofCoeffs ζ
theorem pauliForm_of_pos (ζ : (remainderIndex L k).Carrier → ℂ) {b : Edge L k 0}
    (h : b.IsPositivelyOriented) :
    pauliForm ζ b = ∑ a, ζ (a, ⟨b, h⟩) • ComplexMatrix2.pauliFamily a := by
  simp only [pauliForm, edgePauliCoordinates, extendOddly, if_pos h, dif_pos h, ofPauliCoeffs]
theorem pauliForm_of_not_pos (ζ : (remainderIndex L k).Carrier → ℂ) {b : Edge L k 0}
    (h : ¬ b.IsPositivelyOriented) : pauliForm ζ b = -pauliForm ζ b.opposite := by
  have hr : b.opposite.IsPositivelyOriented :=
    (isPositivelyOriented_or_opposite b).resolve_left h
  simp only [pauliForm, edgePauliCoordinates, extendOddly, if_neg h, if_pos hr]
theorem pauliForm_opposite (hη : 0 < finestMesh L k) (ζ : (remainderIndex L k).Carrier → ℂ)
    (b : Edge L k 0) : pauliForm ζ b.opposite = -pauliForm ζ b := by
  by_cases h : b.IsPositivelyOriented
  · exact pauliForm_of_not_pos ζ (not_isPositivelyOriented_opposite hη h)
  · rw [pauliForm_of_not_pos ζ h, neg_neg]
theorem pauliForm_mem (hη : 0 < finestMesh L k) (ζ : (remainderIndex L k).Carrier → ℂ) :
    pauliForm ζ ∈ complexEdgeForms (meshAt L k 0) := by
  refine ⟨fun b hb => ?_, pauliForm_opposite hη ζ⟩
  rw [pauliForm_of_pos ζ hb]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (pauliFamily_mem_traceless a)
theorem pauliForm_add (ζ ζ' : (remainderIndex L k).Carrier → ℂ) :
    pauliForm (ζ + ζ') = pauliForm ζ + pauliForm ζ' := by
  have hp : ∀ (b : Edge L k 0), b.IsPositivelyOriented →
      pauliForm (ζ + ζ') b = pauliForm ζ b + pauliForm ζ' b := by
    intro b h
    simp only [pauliForm_of_pos _ h]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => add_smul _ _ _
  funext b
  by_cases h : b.IsPositivelyOriented
  · exact hp b h
  · have hr : b.opposite.IsPositivelyOriented :=
      (isPositivelyOriented_or_opposite b).resolve_left h
    simp only [Pi.add_apply, pauliForm_of_not_pos _ h, hp _ hr, neg_add]
theorem pauliForm_smul (c : ℂ) (ζ : (remainderIndex L k).Carrier → ℂ) :
    pauliForm (c • ζ) = c • pauliForm ζ := by
  have hp : ∀ (b : Edge L k 0), b.IsPositivelyOriented →
      pauliForm (c • ζ) b = c • pauliForm ζ b := by
    intro b h
    simp only [pauliForm_of_pos _ h, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => mul_smul _ _ _
  funext b
  by_cases h : b.IsPositivelyOriented
  · exact hp b h
  · have hr : b.opposite.IsPositivelyOriented :=
      (isPositivelyOriented_or_opposite b).resolve_left h
    simp only [Pi.smul_apply, pauliForm_of_not_pos _ h, hp _ hr, smul_neg]
theorem pauliForm_eqOn (ζ ζ' : (remainderIndex L k).Carrier → ℂ) {S : Set (Edge L k 0)}
    (hS : ∀ b ∈ S, b.opposite ∈ S)
    (h : ∀ b ∈ S, ∀ (hb : b.IsPositivelyOriented) (a : Fin 3),
      ζ (a, ⟨b, hb⟩) = ζ' (a, ⟨b, hb⟩)) :
    EqOn (pauliForm ζ) (pauliForm ζ') S := by
  have hp : ∀ b ∈ S, b.IsPositivelyOriented → pauliForm ζ b = pauliForm ζ' b := by
    intro b hbS hb
    simp only [pauliForm_of_pos _ hb, h b hbS hb]
  intro b hbS
  by_cases hb : b.IsPositivelyOriented
  · exact hp b hbS hb
  · have hr : b.opposite.IsPositivelyOriented :=
      (isPositivelyOriented_or_opposite b).resolve_left hb
    rw [pauliForm_of_not_pos _ hb, pauliForm_of_not_pos _ hb, hp _ (hS b hbS) hr]
theorem norm_pauliForm_le (ζ : (remainderIndex L k).Carrier → ℂ) {r : ℝ} (h : ∀ κ, ‖ζ κ‖ ≤ r)
    (b : Edge L k 0) : ‖pauliForm ζ b‖ ≤ 3 * r := by
  have hp : ∀ (b : Edge L k 0), b.IsPositivelyOriented → ‖pauliForm ζ b‖ ≤ 3 * r := by
    intro b hb
    rw [pauliForm_of_pos ζ hb]
    exact norm_ofPauliCoeffs_le (σ := PeriodicOperators.PosEdge L k 0) ζ h ⟨b, hb⟩
  by_cases hb : b.IsPositivelyOriented
  · exact hp b hb
  · have hr : b.opposite.IsPositivelyOriented :=
      (isPositivelyOriented_or_opposite b).resolve_left hb
    rw [pauliForm_of_not_pos ζ hb, norm_neg]
    exact hp _ hr
def rescaledForm (ζ : (remainderIndex L k).Carrier → ℂ) : Edge L k 0 → ComplexMatrix2 :=
  (finestMesh L k)⁻¹ • pauliForm ζ
theorem remainderGaugeField_rescaledForm (hη : 0 < finestMesh L k)
    (ζ : (remainderIndex L k).Carrier → ℂ) :
    remainderGaugeField (rescaledForm ζ) = gaugeFieldOfForm L k ζ := by
  unfold remainderGaugeField scaledRemainderForm rescaledForm gaugeFieldOfForm
  rw [smul_smul, mul_inv_cancel₀ hη.ne', one_smul]
  rfl
theorem rescaledForm_eq_smul (ζ : (remainderIndex L k).Carrier → ℂ) :
    rescaledForm ζ = (((finestMesh L k)⁻¹ : ℝ) : ℂ) • pauliForm ζ := by
  funext b
  simp only [rescaledForm, Pi.smul_apply, real_smul_eq_complex_smul]
theorem rescaledForm_mem (hη : 0 < finestMesh L k) (ζ : (remainderIndex L k).Carrier → ℂ) :
    rescaledForm ζ ∈ complexEdgeForms (meshAt L k 0) := by
  rw [rescaledForm_eq_smul]
  exact Submodule.smul_mem _ _ (pauliForm_mem hη ζ)
theorem exists_bound_of_isSupBelow (hη : 0 < finestMesh L k) {ρ : ℝ}
    {ζ : (remainderIndex L k).Carrier → ℂ}
    (h : IsSupBelow (remainderIndex L k) ζ (finestMesh L k * ρ / 3)) :
    ∃ s : ℝ, 0 ≤ s ∧ s < ρ ∧ ∀ b, ‖rescaledForm ζ b‖ ≤ s := by
  obtain ⟨r, hr, hb⟩ := h
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hb (0, Classical.arbitrary _))
  have hi : 0 < (finestMesh L k)⁻¹ := inv_pos.2 hη
  refine ⟨(finestMesh L k)⁻¹ * (3 * r), by positivity, ?_, fun b => ?_⟩
  · have h3 : 3 * r < finestMesh L k * ρ := by linarith
    calc (finestMesh L k)⁻¹ * (3 * r) < (finestMesh L k)⁻¹ * (finestMesh L k * ρ) :=
          mul_lt_mul_of_pos_left h3 hi
      _ = ρ := by field_simp
  · rw [rescaledForm_eq_smul, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hi]
    exact mul_le_mul_of_nonneg_left (norm_pauliForm_le ζ hb b) hi.le
theorem maxOperatorNorm_le_ofReal {ι : Type*} {f : ι → ComplexMatrix2} {s : ℝ}
    (h : ∀ i, ‖f i‖ ≤ s) : maxOperatorNorm f ≤ ENNReal.ofReal s :=
  iSup_le fun i => ENNReal.ofReal_le_ofReal (h i)
theorem rescaledForm_mem_smallFormBall (hη : 0 < finestMesh L k) {ρ : ℝ} (hρ : 0 < ρ)
    {ζ : (remainderIndex L k).Carrier → ℂ}
    (h : IsSupBelow (remainderIndex L k) ζ (finestMesh L k * ρ / 3)) :
    rescaledForm ζ ∈ IteratedSmallFieldMeans.smallFormBall L k ρ ∧
      maxOperatorNorm (rescaledForm ζ) < ENNReal.ofReal ρ := by
  obtain ⟨s, _, hs, hb⟩ := exists_bound_of_isSupBelow hη h
  have h1 : maxOperatorNorm (rescaledForm ζ) ≤ ENNReal.ofReal s := maxOperatorNorm_le_ofReal hb
  have h2 : ENNReal.ofReal s < ENNReal.ofReal ρ := (ENNReal.ofReal_lt_ofReal_iff hρ).2 hs
  exact ⟨⟨rescaledForm_mem hη ζ, h1.trans h2.le⟩, h1.trans_lt h2⟩
theorem maxOperatorNorm_pauliForm_lt (hη : 0 < finestMesh L k) {ρ : ℝ} (hρ : 0 < ρ)
    {ζ : (remainderIndex L k).Carrier → ℂ}
    (h : IsSupBelow (remainderIndex L k) ζ (finestMesh L k * ρ / 3)) :
    maxOperatorNorm (pauliForm ζ) < ENNReal.ofReal (finestMesh L k * ρ) := by
  obtain ⟨r, hr, hb⟩ := h
  have h1 : maxOperatorNorm (pauliForm ζ) ≤ ENNReal.ofReal (3 * r) :=
    maxOperatorNorm_le_ofReal (norm_pauliForm_le ζ hb)
  refine h1.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (mul_pos hη hρ)).2 ?_)
  linarith
end Forms
section Means
variable {L k : ℕ}
open _root_.YangMills.Construction.Tower.FullSpace.IteratedSmallFieldMeans
  (rescaledCovMean FullConditions)
open TorusMetric (euclidNormVec)
theorem Q_represents (hK : ThreeMapKernels.OnFullSpace L k) (hη : 0 < finestMesh L k)
    {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k) :
    Represents (rescaledOperators L k U).Q
      (PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L k 0) (edgePauliCoordinates L k k)
        (rescaledCovMean U)) := by
  have hh := (hK.2.2.2 U hU).1
  have hM : PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L k 0) (edgePauliCoordinates L k k)
        (rescaledCovMean U) =
      ((finestMesh L k : ℝ) : ℂ) • PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L k 0)
        (edgePauliCoordinates L k k) (iterCovariantDeriv L k U k) := by
    funext f ι'
    exact pauliCoeff_real_smul hη.ne' _ _
  have h1 := hh.smul_represents ((finestMesh L k : ℝ) : ℂ)
  rw [← hM] at h1
  exact Classical.epsilon_spec (p := fun T => Represents T (PauliComponentsOfSymmetricKernel.mapOnCoeffs
    (edgePauliCoordinates L k 0) (edgePauliCoordinates L k k) (rescaledCovMean U))) ⟨_, h1⟩
theorem R_represents (hK : ThreeMapKernels.OnFullSpace L k)
    {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k) :
    Represents (rescaledOperators L k U).R
      (PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (Vertex L k 0)) (vertexCoordinate (Vertex L k k))
        (iterAdjointCubeAverage L k U k)) :=
  (hK.2.2.2 U hU).2.represents
theorem Q_apply (hK : ThreeMapKernels.OnFullSpace L k) (hη : 0 < finestMesh L k)
    {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k)
    (ι' : (colourEdges L k k).Carrier) (ι : (colourEdges L k 0).Carrier) :
    (rescaledOperators L k U).Q ι' ι =
      pauliCoeff ι'.1 (rescaledCovMean U (pauliForm (basisFun ι)) ι'.2.1) :=
  kernel_eq_of_represents (Q_represents hK hη hU) ι' ι
theorem R_apply (hK : ThreeMapKernels.OnFullSpace L k)
    {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k)
    (ι' : (colourVertices L k k).Carrier) (ι : (colourVertices L k 0).Carrier) :
    (rescaledOperators L k U).R ι' ι =
      pauliCoeff ι'.1 (iterAdjointCubeAverage L k U k (ofPauliCoeffs (basisFun ι)) ι'.2) :=
  kernel_eq_of_represents (R_represents hK hU) ι' ι
theorem euclid_lt_three_of_adjacentCubes (hZ : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {c : Edge L k k}
    (hc : c.IsPositivelyOriented) {x : InfiniteLattice.AmbientSpace}
    (hx : x ∈ cubeOfOrder L (meshAt L k 0) k c.initial ∪
      cubeOfOrder L (meshAt L k 0) k c.terminal) :
    euclidNormVec (x - (c.initial : InfiniteLattice.AmbientSpace)) < 3 := by
  have hS := (hZ L hL k k k hk le_rfl le_rfl).2.2.2.2.2.1
  have h := hS.sites_near c hc x
  rw [Nat.sub_self] at h
  obtain ⟨ν, hxν, hν⟩ := h hx
  have h1 : meshAt L k k = 1 := by simp [meshAt]
  rw [h1] at hν
  have hco : ∀ ρ, (x - (c.initial : InfiniteLattice.AmbientSpace)) ρ =
      (ν ρ : ℝ) * meshAt L k 0 := by
    intro ρ
    rw [hxν]
    simp [offsetPoint, Finset.sum_apply, Pi.single_apply]
  have hsq : ∀ ρ, (x - (c.initial : InfiniteLattice.AmbientSpace)) ρ ^ 2 < 9 / 4 := by
    intro ρ
    rw [hco]
    have h2 := abs_lt.1 (hν ρ)
    nlinarith [h2.1, h2.2]
  unfold euclidNormVec
  rw [Real.sqrt_lt' (by norm_num)]
  calc ∑ ρ, (x - (c.initial : InfiniteLattice.AmbientSpace)) ρ ^ 2
        < ∑ _ρ : Fin 4, (9 / 4 : ℝ) :=
        Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ _⟩ fun ρ _ => hsq ρ
    _ = 3 ^ 2 := by norm_num
theorem euclid_lt_three_of_cube (hZ : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {y : Vertex L k k}
    {x : InfiniteLattice.AmbientSpace} (hx : x ∈ cubeOfOrder L (meshAt L k 0) k y) :
    euclidNormVec (x - (y : InfiniteLattice.AmbientSpace)) < 3 :=
  euclid_lt_three_of_adjacentCubes hZ hL hk (c := InfiniteLattice.Link.forwardFrom y 0) ⟨0, by
    simp [InfiniteLattice.Link.forwardFrom]⟩ (Or.inl hx)
theorem rescaledForm_eqOn {ζ ζ' : (remainderIndex L k).Carrier → ℂ} {S : Set (Edge L k 0)}
    (h : EqOn (pauliForm ζ) (pauliForm ζ') S) : EqOn (rescaledForm ζ) (rescaledForm ζ') S := by
  intro b hb
  simp only [rescaledForm, Pi.smul_apply, h hb]
theorem ofPauliCoeffs_congr {σ : Type} {c c' : Fin 3 × σ → ℂ} {x : σ}
    (h : ∀ a, c (a, x) = c' (a, x)) : ofPauliCoeffs c x = ofPauliCoeffs c' x := by
  simp only [ofPauliCoeffs, h]
section Requirements
variable {ρ C : ℝ} (hS : FullConditions L k ρ C)
  (hZ : BlockPathContourPivotStatement)
  (hK : ThreeMapKernels.OnFullSpace L k) (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hk : 1 ≤ k) (hη : 0 < finestMesh L k) (hρ : 0 < ρ)
include hS hη hρ in
theorem gaugeFieldOfForm_mem {ζ : (remainderIndex L k).Carrier → ℂ}
    (hζ : IsSupBelow (remainderIndex L k) ζ (finestMesh L k * ρ / 3)) :
    gaugeFieldOfForm L k ζ ∈ smallIterateFields L k := by
  have h := (hS.pointwise _ (rescaledForm_mem_smallFormBall hη hρ hζ).1).mem_smallIterate
  rwa [remainderGaugeField_rescaledForm hη] at h
include hS hZ hK hL hk hη hρ in
theorem Q_eq_zero_of_far {ζ : (remainderIndex L k).Carrier → ℂ}
    (hζ : IsSupBelow (remainderIndex L k) ζ (finestMesh L k * ρ / 3))
    (ι' : (colourEdges L k k).Carrier) (ι : (colourEdges L k 0).Carrier)
    (hfar : ¬ euclidNormVec ((colourEdges L k 0).pos ι - (colourEdges L k k).pos ι') ≤ 3) :
    (rescaledOperators L k (gaugeFieldOfForm L k ζ)).Q ι' ι = 0 := by
  have ha := (rescaledForm_mem_smallFormBall hη hρ hζ).1
  have hU := gaugeFieldOfForm_mem hS hη hρ hζ
  rw [Q_apply hK hη hU]
  have hE : EqOn (pauliForm (basisFun ι)) (pauliForm 0) (edgesOverEdge ι'.2.1) := by
    refine pauliForm_eqOn _ _ (fun b hb => ⟨hb.2, hb.1⟩) fun b hb hp col => ?_
    refine basisFun_of_ne fun he => hfar ?_
    rw [← he]
    exact (euclid_lt_three_of_adjacentCubes hZ hL hk ι'.2.2 hb.1).le
  have h1 := hS.locality.local_Q ι'.2.1 _ ha _ ha _ (pauliForm_mem hη _) _ (pauliForm_mem hη _)
    (fun _ _ => rfl) hE
  rw [remainderGaugeField_rescaledForm hη] at h1
  rw [h1]
  exact map_zero_of_represents (Q_represents hK hη hU) ι'
include hS hZ hK hL hk hη hρ in
theorem Q_congr {ζ ζ' : (remainderIndex L k).Carrier → ℂ}
    (hζ : IsSupBelow (remainderIndex L k) ζ (finestMesh L k * ρ / 3))
    (hζ' : IsSupBelow (remainderIndex L k) ζ' (finestMesh L k * ρ / 3))
    (ι' : (colourEdges L k k).Carrier) (ι : (colourEdges L k 0).Carrier)
    (hag : ∀ κ ∈ nearIndices (remainderIndex L k) ((colourEdges L k k).pos ι') 3,
      ζ κ = ζ' κ) :
    (rescaledOperators L k (gaugeFieldOfForm L k ζ)).Q ι' ι =
      (rescaledOperators L k (gaugeFieldOfForm L k ζ')).Q ι' ι := by
  have ha := (rescaledForm_mem_smallFormBall hη hρ hζ).1
  have ha' := (rescaledForm_mem_smallFormBall hη hρ hζ').1
  rw [Q_apply hK hη (gaugeFieldOfForm_mem hS hη hρ hζ),
    Q_apply hK hη (gaugeFieldOfForm_mem hS hη hρ hζ')]
  have hE : EqOn (rescaledForm ζ) (rescaledForm ζ') (edgesOverEdge ι'.2.1) := by
    refine rescaledForm_eqOn (pauliForm_eqOn _ _ (fun b hb => ⟨hb.2, hb.1⟩) fun b hb hp col => ?_)
    exact hag _ (euclid_lt_three_of_adjacentCubes hZ hL hk ι'.2.2 hb.1).le
  have h1 := hS.locality.local_Q ι'.2.1 _ ha _ ha' _ (pauliForm_mem hη (basisFun ι)) _
    (pauliForm_mem hη (basisFun ι)) hE (fun _ _ => rfl)
  rw [remainderGaugeField_rescaledForm hη, remainderGaugeField_rescaledForm hη] at h1
  rw [h1]
include hS hZ hK hL hk hη hρ in
theorem R_eq_zero_of_far {ζ : (remainderIndex L k).Carrier → ℂ}
    (hζ : IsSupBelow (remainderIndex L k) ζ (finestMesh L k * ρ / 3))
    (ι' : (colourVertices L k k).Carrier) (ι : (colourVertices L k 0).Carrier)
    (hfar : ¬ euclidNormVec ((colourVertices L k 0).pos ι - (colourVertices L k k).pos ι') ≤ 3) :
    (rescaledOperators L k (gaugeFieldOfForm L k ζ)).R ι' ι = 0 := by
  have ha := (rescaledForm_mem_smallFormBall hη hρ hζ).1
  have hU := gaugeFieldOfForm_mem hS hη hρ hζ
  rw [R_apply hK hU]
  have h1 := hS.locality.local_R ι'.2 _ ha _ ha (ofPauliCoeffs (basisFun ι)) (ofPauliCoeffs 0)
    (ofPauliCoeffs_mem _) (ofPauliCoeffs_mem _) (fun x hx => ofPauliCoeffs_congr fun a => ?_)
    (fun _ _ => rfl)
  · rw [remainderGaugeField_rescaledForm hη] at h1
    rw [h1]
    exact map_zero_of_represents (R_represents hK hU) ι'
  · refine basisFun_of_ne fun he => hfar ?_
    rw [← he]
    exact (euclid_lt_three_of_cube hZ hL hk hx).le
include hS hZ hK hL hk hη hρ in
theorem R_congr {ζ ζ' : (remainderIndex L k).Carrier → ℂ}
    (hζ : IsSupBelow (remainderIndex L k) ζ (finestMesh L k * ρ / 3))
    (hζ' : IsSupBelow (remainderIndex L k) ζ' (finestMesh L k * ρ / 3))
    (ι' : (colourVertices L k k).Carrier) (ι : (colourVertices L k 0).Carrier)
    (hag : ∀ κ ∈ nearIndices (remainderIndex L k) ((colourVertices L k k).pos ι') 3,
      ζ κ = ζ' κ) :
    (rescaledOperators L k (gaugeFieldOfForm L k ζ)).R ι' ι =
      (rescaledOperators L k (gaugeFieldOfForm L k ζ')).R ι' ι := by
  have ha := (rescaledForm_mem_smallFormBall hη hρ hζ).1
  have ha' := (rescaledForm_mem_smallFormBall hη hρ hζ').1
  rw [R_apply hK (gaugeFieldOfForm_mem hS hη hρ hζ), R_apply hK (gaugeFieldOfForm_mem hS hη hρ hζ')]
  have hE : EqOn (rescaledForm ζ) (rescaledForm ζ')
      (IteratedSmallFieldMeans.cubeEdges ι'.2) := by
    refine rescaledForm_eqOn (pauliForm_eqOn _ _ (fun b hb => ⟨hb.2, hb.1⟩) fun b hb hp col => ?_)
    exact hag _ (euclid_lt_three_of_cube hZ hL hk hb.1).le
  have h1 := hS.locality.local_R ι'.2 _ ha _ ha' (ofPauliCoeffs (basisFun ι))
    (ofPauliCoeffs (basisFun ι)) (ofPauliCoeffs_mem _) (ofPauliCoeffs_mem _)
    (fun _ _ => rfl) hE
  rw [remainderGaugeField_rescaledForm hη, remainderGaugeField_rescaledForm hη] at h1
  rw [h1]
end Requirements
end Means
section Shifts
open _root_.YangMills.Construction.Tower.FullSpace.Translations (spaceShift)
section OneLattice
variable {a : ℝ} (v : InfiniteLattice.AmbientSpace)
theorem vertexPreimage_eq {x y : InfiniteLattice.LatticePoint a}
    (h : (y : InfiniteLattice.AmbientSpace) = (x : InfiniteLattice.AmbientSpace) + v) :
    vertexPreimage (spaceShift v) y = x := by
  have h1 := Classical.epsilon_spec
    (p := fun x' : InfiniteLattice.LatticePoint a => spaceShift v x' = y) ⟨x, h.symm⟩
  apply Subtype.ext
  have h2 : ((vertexPreimage (spaceShift v) y : InfiniteLattice.LatticePoint a) :
      InfiniteLattice.AmbientSpace) + v = y := h1
  rw [h] at h2
  exact add_right_cancel h2
theorem edgePreimage_eq {b b' : InfiniteLattice.Link a}
    (ht : (b.initial : InfiniteLattice.AmbientSpace) =
      (b'.initial : InfiniteLattice.AmbientSpace) + v)
    (hh : (b.terminal : InfiniteLattice.AmbientSpace) =
      (b'.terminal : InfiniteLattice.AmbientSpace) + v) :
    edgePreimage (spaceShift v) b = b' := by
  have h1 := Classical.epsilon_spec
    (p := fun c : InfiniteLattice.Link a => c.initial = vertexPreimage (spaceShift v) b.initial ∧
      c.terminal = vertexPreimage (spaceShift v) b.terminal)
    ⟨b', (vertexPreimage_eq v ht).symm, (vertexPreimage_eq v hh).symm⟩
  exact InfiniteLattice.Link.ext (h1.1.trans (vertexPreimage_eq v ht))
    (h1.2.trans (vertexPreimage_eq v hh))
theorem isometryOnTangent_apply_of_pos
    (f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace)
    (U B : InfiniteLattice.Link a → ComplexMatrix2) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) (hi : (edgePreimage f b).IsPositivelyOriented) :
    isometryOnTangent f U B b = B (edgePreimage f b) := by
  simp only [isometryOnTangent, extendOddly, if_pos hb, tangentEdgeValue, if_pos hi]
end OneLattice
theorem castVec_neg (n : Fin 4 → ℤ) : castVec (-n) = -castVec n := by apply _root_.YangMills.Construction.Tower.PlaneWaveSmoothingSymbols.castVec_neg <;> assumption
variable {L k j : ℕ}
section EdgeShifts
variable (n : Fin 4 → ℤ)
  (hB : FullLatticeOverTorus.ShiftSurjectiveOnEdges L k j n)
  (hB' : FullLatticeOverTorus.ShiftSurjectiveOnEdges L k j (-n))
include hB in
theorem edgePreimage_shiftEdge (c : PeriodicOperators.PosEdge L k j) :
    edgePreimage (spaceShift (castVec n)) (shiftEdge n c).1 = c.1 :=
  edgePreimage_eq _ (hB.2 c).1 (hB.2 c).2
include hB' in
theorem edgePreimage_of_pos (b : PeriodicOperators.PosEdge L k j) :
    edgePreimage (spaceShift (castVec n)) b.1 = (shiftEdge (-n) b).1 := by
  refine edgePreimage_eq _ ?_ ?_
  · rw [(hB'.2 b).1, castVec_neg]
    simp
  · rw [(hB'.2 b).2, castVec_neg]
    simp
include hB hB' in
theorem shiftEdge_neg_shiftEdge (c : PeriodicOperators.PosEdge L k j) :
    shiftEdge (-n) (shiftEdge n c) = c := by
  apply Subtype.ext
  apply InfiniteLattice.Link.ext
  · apply Subtype.ext
    rw [(hB'.2 _).1, (hB.2 _).1, castVec_neg]
    simp
  · apply Subtype.ext
    rw [(hB'.2 _).2, (hB.2 _).2, castVec_neg]
    simp
include hB hB' in
theorem shiftEdge_shiftEdge_neg (c : PeriodicOperators.PosEdge L k j) :
    shiftEdge n (shiftEdge (-n) c) = c := by
  apply Subtype.ext
  apply InfiniteLattice.Link.ext
  · apply Subtype.ext
    rw [(hB.2 _).1, (hB'.2 _).1, castVec_neg]
    simp
  · apply Subtype.ext
    rw [(hB.2 _).2, (hB'.2 _).2, castVec_neg]
    simp
end EdgeShifts
section VertexShifts
variable (n : Fin 4 → ℤ)
  (hs : FullLatticeOverTorus.ShiftSurjectiveOnVertices L k j n)
  (hs' : FullLatticeOverTorus.ShiftSurjectiveOnVertices L k j (-n))
include hs in
theorem vertexPreimage_vertexImage (x : Vertex L k j) :
    vertexPreimage (spaceShift (castVec n))
      (vertexImage (intShift n) x : Vertex L k j) = x :=
  vertexPreimage_eq _ (hs.2 x)
include hs' in
theorem vertexPreimage_eq_vertexImage_neg (y : Vertex L k j) :
    vertexPreimage (spaceShift (castVec n)) y = vertexImage (intShift (-n)) y := by
  refine vertexPreimage_eq _ ?_
  rw [hs'.2 y, castVec_neg]
  simp
include hs hs' in
theorem vertexImage_neg_vertexImage (x : Vertex L k j) :
    (vertexImage (intShift (-n)) (vertexImage (intShift n) x : Vertex L k j) : Vertex L k j) =
      x := by
  apply Subtype.ext
  rw [hs'.2 _, hs.2 x, castVec_neg]
  simp
include hs hs' in
theorem vertexImage_vertexImage_neg (x : Vertex L k j) :
    (vertexImage (intShift n) (vertexImage (intShift (-n)) x : Vertex L k j) : Vertex L k j) =
      x := by
  apply Subtype.ext
  rw [hs.2 _, hs'.2 x, castVec_neg]
  simp
end VertexShifts
end Shifts
section Covariance
open _root_.YangMills.Construction.Tower.FullSpace.Translations (spaceShift)
open _root_.YangMills.Construction.Tower.FullSpace.IteratedSmallFieldMeans
  (rescaledCovMean FullConditions)
open FullLatticeOverTorus (ShiftSurjectiveOnEdges ShiftSurjectiveOnVertices)
variable {L k : ℕ}
theorem gaugeFieldOfForm_of_pos (ζ : (remainderIndex L k).Carrier → ℂ) {b : Edge L k 0}
    (h : b.IsPositivelyOriented) :
    gaugeFieldOfForm L k ζ b = ComplexMatrix2.matExp (Complex.I • pauliForm ζ b) := by
  simp only [gaugeFieldOfForm, expForm, expTwist, if_pos h, Pi.one_apply, mul_one, pauliForm]
theorem gaugeFieldOfForm_of_not_pos (ζ : (remainderIndex L k).Carrier → ℂ)
    {b : Edge L k 0} (h : ¬ b.IsPositivelyOriented) :
    gaugeFieldOfForm L k ζ b = (ComplexMatrix2.matExp (Complex.I • pauliForm ζ b.opposite))⁻¹ := by
  simp only [gaugeFieldOfForm, expForm, expTwist, if_neg h, Pi.one_apply, mul_one, pauliForm]
theorem gaugeFieldOfForm_shiftField (hη : 0 < finestMesh L k) (n : Fin 4 → ℤ)
    (hB' : ShiftSurjectiveOnEdges L k 0 (-n)) (ζ : (remainderIndex L k).Carrier → ℂ) :
    gaugeFieldOfForm L k (shiftField (remainderIndex L k) n ζ) =
      pushField (spaceShift (castVec n)) (gaugeFieldOfForm L k ζ) := by
  have hF : ∀ (b : Edge L k 0) (h : b.IsPositivelyOriented),
      pauliForm (shiftField (remainderIndex L k) n ζ) b =
        pauliForm ζ (shiftEdge (-n) ⟨b, h⟩).1 := by
    intro b h
    rw [pauliForm_of_pos _ h, pauliForm_of_pos _ (shiftEdge (-n) ⟨b, h⟩).2]
    rfl
  funext b
  by_cases h : b.IsPositivelyOriented
  · have hi : edgePreimage (spaceShift (castVec n)) b = (shiftEdge (-n) ⟨b, h⟩).1 :=
      edgePreimage_of_pos n hB' ⟨b, h⟩
    simp only [pushField]
    rw [hi, gaugeFieldOfForm_of_pos _ h, gaugeFieldOfForm_of_pos _ (shiftEdge _ _).2, hF b h]
  · have hr : b.opposite.IsPositivelyOriented :=
      (isPositivelyOriented_or_opposite b).resolve_left h
    have hi : edgePreimage (spaceShift (castVec n)) b =
        (shiftEdge (-n) ⟨b.opposite, hr⟩).1.opposite := by
      refine edgePreimage_eq _ ?_ ?_
      · change (b.initial : InfiniteLattice.AmbientSpace) =
          ((shiftEdge (-n) ⟨b.opposite, hr⟩).1.terminal : InfiniteLattice.AmbientSpace) + _
        rw [(hB'.2 _).2, castVec_neg]
        exact (neg_add_cancel_right _ _).symm
      · change (b.terminal : InfiniteLattice.AmbientSpace) =
          ((shiftEdge (-n) ⟨b.opposite, hr⟩).1.initial : InfiniteLattice.AmbientSpace) + _
        rw [(hB'.2 _).1, castVec_neg]
        exact (neg_add_cancel_right _ _).symm
    have h2 : ¬ ((shiftEdge (-n) ⟨b.opposite, hr⟩).1.opposite).IsPositivelyOriented :=
      not_isPositivelyOriented_opposite hη (shiftEdge _ _).2
    simp only [pushField]
    rw [hi, gaugeFieldOfForm_of_not_pos _ h, gaugeFieldOfForm_of_not_pos _ h2, hF _ hr]
    rfl
theorem pauliForm_basisFun_translate (n : Fin 4 → ℤ) (hB : ShiftSurjectiveOnEdges L k 0 n)
    (hB' : ShiftSurjectiveOnEdges L k 0 (-n)) (U : Edge L k 0 → ComplexMatrix2)
    (ι : (colourEdges L k 0).Carrier) :
    pauliForm (basisFun ((colourEdges L k 0).translate n ι)) =
      isometryOnTangent (spaceShift (castVec n)) U (pauliForm (basisFun ι)) := by
  have hinv : ∀ x : (colourEdges L k 0).Carrier,
      (colourEdges L k 0).translate (-n) ((colourEdges L k 0).translate n x) = x := fun x =>
    Prod.ext rfl (shiftEdge_neg_shiftEdge n hB hB' x.2)
  have hinv' : ∀ x : (colourEdges L k 0).Carrier,
      (colourEdges L k 0).translate n ((colourEdges L k 0).translate (-n) x) = x := fun x =>
    Prod.ext rfl (shiftEdge_shiftEdge_neg n hB hB' x.2)
  have hp : ∀ (b : Edge L k 0), b.IsPositivelyOriented →
      pauliForm (basisFun ((colourEdges L k 0).translate n ι)) b =
        isometryOnTangent (spaceShift (castVec n)) U (pauliForm (basisFun ι)) b := by
    intro b h
    have hi : edgePreimage (spaceShift (castVec n)) b = (shiftEdge (-n) ⟨b, h⟩).1 :=
      edgePreimage_of_pos n hB' ⟨b, h⟩
    have hi' : (edgePreimage (spaceShift (castVec n)) b).IsPositivelyOriented := by
      rw [hi]
      exact (shiftEdge _ _).2
    rw [isometryOnTangent_apply_of_pos _ _ _ h hi', hi, pauliForm_of_pos _ h,
      pauliForm_of_pos _ (shiftEdge (-n) ⟨b, h⟩).2]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [basisFun_comp hinv hinv' ι (a, ⟨b, h⟩)]
    rfl
  funext b
  by_cases h : b.IsPositivelyOriented
  · exact hp b h
  · have hr : b.opposite.IsPositivelyOriented :=
      (isPositivelyOriented_or_opposite b).resolve_left h
    rw [pauliForm_of_not_pos _ h, hp _ hr]
    simp only [isometryOnTangent, extendOddly, if_neg h, if_pos hr]
theorem ofPauliCoeffs_basisFun_translate (n : Fin 4 → ℤ)
    (hs : ShiftSurjectiveOnVertices L k 0 n) (hs' : ShiftSurjectiveOnVertices L k 0 (-n))
    (ι : (colourVertices L k 0).Carrier) :
    ofPauliCoeffs (basisFun ((colourVertices L k 0).translate n ι)) =
      pushSiteFunction (spaceShift (castVec n)) (ofPauliCoeffs (basisFun ι)) := by
  have hinv : ∀ x : (colourVertices L k 0).Carrier,
      (colourVertices L k 0).translate (-n) ((colourVertices L k 0).translate n x) = x :=
    fun x => Prod.ext rfl (vertexImage_neg_vertexImage n hs hs' x.2)
  have hinv' : ∀ x : (colourVertices L k 0).Carrier,
      (colourVertices L k 0).translate n ((colourVertices L k 0).translate (-n) x) = x :=
    fun x => Prod.ext rfl (vertexImage_vertexImage_neg n hs hs' x.2)
  funext y
  simp only [pushSiteFunction]
  rw [vertexPreimage_eq_vertexImage_neg n hs' y]
  simp only [ofPauliCoeffs]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact congrArg (· • ComplexMatrix2.pauliFamily a) (basisFun_comp hinv hinv' ι (a, y))
section Requirements
variable {ρ C : ℝ} (hS : FullConditions L k ρ C)
  (hK : ThreeMapKernels.OnFullSpace L k) (hη : 0 < finestMesh L k) (hρ : 0 < ρ)
  (hI : CovariantSmoothingProperties.IsometryEquivariance L k k)
  (hT : ∀ N : Fin 4 → ℤ, Translations.ShiftRespectsLevels L k k (castVec N))
theorem isSupBelow_shiftField {F : PeriodicData} {ζ : F.Carrier → ℂ} {r : ℝ}
    (h : IsSupBelow F ζ r) (n : Fin 4 → ℤ) : IsSupBelow F (shiftField F n ζ) r := by
  obtain ⟨s, hs, hb⟩ := h
  exact ⟨s, hs, fun κ => hb _⟩
include hS hK hη hρ hI hT in
theorem Q_translate (hB0 : ∀ N, ShiftSurjectiveOnEdges L k 0 N)
    (hBk : ∀ N, ShiftSurjectiveOnEdges L k k N) {ζ : (remainderIndex L k).Carrier → ℂ}
    (hζ : IsSupBelow (remainderIndex L k) ζ (finestMesh L k * ρ / 3)) (n : Fin 4 → ℤ)
    (ι' : (colourEdges L k k).Carrier) (ι : (colourEdges L k 0).Carrier) :
    (rescaledOperators L k (gaugeFieldOfForm L k (shiftField (remainderIndex L k) n ζ))).Q
        ((colourEdges L k k).translate n ι') ((colourEdges L k 0).translate n ι) =
      (rescaledOperators L k (gaugeFieldOfForm L k ζ)).Q ι' ι := by
  have hU := gaugeFieldOfForm_mem hS hη hρ hζ
  have hU' := gaugeFieldOfForm_mem hS hη hρ (isSupBelow_shiftField hζ n)
  rw [Q_apply hK hη hU', Q_apply hK hη hU]
  have hc := ((hI _ (hT n).1 ((hT n).2.1 k le_rfl) _ hU).2 _
    (pauliForm_mem hη (basisFun ι))).2.1
  simp only [rescaledCovMean, Pi.smul_apply]
  rw [gaugeFieldOfForm_shiftField hη n (hB0 (-n)) ζ,
    pauliForm_basisFun_translate n (hB0 n) (hB0 (-n)) (gaugeFieldOfForm L k ζ) ι, hc]
  have hi := edgePreimage_shiftEdge n (hBk n) ι'.2
  change pauliCoeff ι'.1 (finestMesh L k • isometryOnTangent _ _ _
    (shiftEdge n ι'.2).1) = _
  rw [isometryOnTangent_apply_of_pos _ _ _ (shiftEdge n ι'.2).2 (by rw [hi]; exact ι'.2.2), hi]
include hS hK hη hρ hI hT in
theorem R_translate (hB0 : ∀ N, ShiftSurjectiveOnEdges L k 0 N)
    (hs0 : ∀ N, ShiftSurjectiveOnVertices L k 0 N) (hsk : ∀ N, ShiftSurjectiveOnVertices L k k N)
    {ζ : (remainderIndex L k).Carrier → ℂ}
    (hζ : IsSupBelow (remainderIndex L k) ζ (finestMesh L k * ρ / 3)) (n : Fin 4 → ℤ)
    (ι' : (colourVertices L k k).Carrier) (ι : (colourVertices L k 0).Carrier) :
    (rescaledOperators L k (gaugeFieldOfForm L k (shiftField (remainderIndex L k) n ζ))).R
        ((colourVertices L k k).translate n ι') ((colourVertices L k 0).translate n ι) =
      (rescaledOperators L k (gaugeFieldOfForm L k ζ)).R ι' ι := by
  have hU := gaugeFieldOfForm_mem hS hη hρ hζ
  have hU' := gaugeFieldOfForm_mem hS hη hρ (isSupBelow_shiftField hζ n)
  rw [R_apply hK hU', R_apply hK hU]
  have hc := ((hI _ (hT n).1 ((hT n).2.1 k le_rfl) _ hU).1 _
    (ofPauliCoeffs_mem (basisFun ι))).2
  rw [gaugeFieldOfForm_shiftField hη n (hB0 (-n)) ζ,
    ofPauliCoeffs_basisFun_translate n (hs0 n) (hs0 (-n)) ι, hc]
  change pauliCoeff ι'.1 (iterAdjointCubeAverage L k _ k _
    (vertexPreimage (spaceShift (castVec n)) (vertexImage (intShift n) ι'.2))) = _
  rw [vertexPreimage_vertexImage n (hsk n)]
end Requirements
end Covariance
section Holomorphy
open Coordinates.ComplexCoordinates.PowerSeriesHolomorphy (openPolydisk)
open _root_.YangMills.Construction.Tower.IteratedSmallFieldMeans (HolomorphicInEntries)
open LeftChartFields (scalarCoords)
open Matrices.GroupLieProduct (supBall tupleOfCoords supNorm tracelessPi)
open TorusMetric (euclidNormVec)
theorem isHolomorphicIn_of_linearMap {N M : ℕ}
    (g : Coordinates.ComplexCoordinates N →ₗ[ℂ] Coordinates.ComplexCoordinates M)
    {O : Set (Coordinates.ComplexCoordinates N)} (hO : IsOpen O) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn O g := by apply _root_.YangMills.Construction.Averaging.SmallRadiusProof.isHolomorphicIn_of_linearMap <;> assumption
theorem isOpen_openPolydisk {N : ℕ} (ρ : ℝ) :
    IsOpen (openPolydisk (0 : Coordinates.ComplexCoordinates N) ρ) := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.isOpen_openPolydisk_zero <;> assumption
section Values
variable {F : PeriodicData} {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S)
theorem fieldExtend_apply (z : Coordinates.ComplexCoordinates l) (j : Fin l) :
    fieldExtend e z (e j : F.Carrier) = z j := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.fieldExtend_apply <;> assumption
theorem fieldExtend_of_notMem (z : Coordinates.ComplexCoordinates l) {κ : F.Carrier}
    (hκ : κ ∉ S) : fieldExtend e z κ = 0 :=
  Function.extend_apply' _ _ _ fun ⟨j, hj⟩ => hκ (hj ▸ (e j).2)
theorem fieldExtend_add (z z' : Coordinates.ComplexCoordinates l) :
    fieldExtend e (z + z') = fieldExtend e z + fieldExtend e z' := by
  funext κ
  by_cases hκ : κ ∈ S
  · obtain ⟨j, rfl⟩ : ∃ j, (e j : F.Carrier) = κ := ⟨e.symm ⟨κ, hκ⟩, by simp⟩
    simp only [Pi.add_apply, fieldExtend_apply]
  · simp only [Pi.add_apply, fieldExtend_of_notMem e _ hκ, add_zero]
theorem fieldExtend_smul (c : ℂ) (z : Coordinates.ComplexCoordinates l) :
    fieldExtend e (c • z) = c • fieldExtend e z := by
  funext κ
  by_cases hκ : κ ∈ S
  · obtain ⟨j, rfl⟩ : ∃ j, (e j : F.Carrier) = κ := ⟨e.symm ⟨κ, hκ⟩, by simp⟩
    simp only [Pi.smul_apply, fieldExtend_apply]
  · simp only [Pi.smul_apply, fieldExtend_of_notMem e _ hκ, smul_zero]
theorem isSupBelow_fieldExtend {ρ : ℝ} (hρ : 0 < ρ) {z : Coordinates.ComplexCoordinates l}
    (hz : z ∈ openPolydisk (0 : Coordinates.ComplexCoordinates l) ρ) :
    IsSupBelow F (fieldExtend e z) ρ := by
  have h : ‖z‖ < ρ := (pi_norm_lt_iff hρ).2 fun j => by simpa using hz j
  refine ⟨‖z‖, h, fun κ => ?_⟩
  by_cases hκ : κ ∈ S
  · obtain ⟨j, rfl⟩ : ∃ j, (e j : F.Carrier) = κ := ⟨e.symm ⟨κ, hκ⟩, by simp⟩
    rw [fieldExtend_apply]
    exact norm_le_pi_norm z j
  · rw [fieldExtend_of_notMem e _ hκ, norm_zero]
    exact norm_nonneg z
theorem fieldValues_mem_openPolydisk {ρ : ℝ} {ζ : F.Carrier → ℂ} (h : IsSupBelow F ζ ρ) :
    fieldValues e ζ ∈ openPolydisk (0 : Coordinates.ComplexCoordinates l) ρ := by
  obtain ⟨r, hr, hb⟩ := h
  intro j
  simpa [fieldValues] using (hb _).trans_lt hr
theorem fieldExtend_fieldValues (ζ : F.Carrier → ℂ) {κ : F.Carrier} (hκ : κ ∈ S) :
    fieldExtend e (fieldValues e ζ) κ = ζ κ := by
  obtain ⟨j, rfl⟩ : ∃ j, (e j : F.Carrier) = κ := ⟨e.symm ⟨κ, hκ⟩, by simp⟩
  rw [fieldExtend_apply]
  rfl
end Values
variable {L k : ℕ}
theorem pauliForm_apply_mem (ζ : (remainderIndex L k).Carrier → ℂ) (b : Edge L k 0) :
    pauliForm ζ b ∈ ComplexMatrix2.traceless := by
  have hp : ∀ (b : Edge L k 0), b.IsPositivelyOriented →
      pauliForm ζ b ∈ ComplexMatrix2.traceless := by
    intro b h
    rw [pauliForm_of_pos ζ h]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (pauliFamily_mem_traceless a)
  by_cases h : b.IsPositivelyOriented
  · exact hp b h
  · rw [pauliForm_of_not_pos ζ h]
    exact Submodule.neg_mem _ (hp _ ((isPositivelyOriented_or_opposite b).resolve_left h))
theorem rescaledForm_apply_mem (ζ : (remainderIndex L k).Carrier → ℂ) (b : Edge L k 0) :
    rescaledForm ζ b ∈ ComplexMatrix2.traceless := by
  rw [rescaledForm_eq_smul]
  exact Submodule.smul_mem _ _ (pauliForm_apply_mem ζ b)
theorem rescaledForm_add (ζ ζ' : (remainderIndex L k).Carrier → ℂ) :
    rescaledForm (ζ + ζ') = rescaledForm ζ + rescaledForm ζ' := by
  simp only [rescaledForm, pauliForm_add, smul_add]
theorem rescaledForm_smul (c : ℂ) (ζ : (remainderIndex L k).Carrier → ℂ) :
    rescaledForm (c • ζ) = c • rescaledForm ζ := by
  simp only [rescaledForm_eq_smul, pauliForm_smul]
  exact smul_comm _ _ _
theorem exists_holomorphic_of_local
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hη : 0 < finestMesh L k) {ρ : ℝ} (hρ : 0 < ρ) {S : Set (remainderIndex L k).Carrier}
    (hfin : S.Finite) {v : (Edge L k 0 → ComplexMatrix2) → ℂ}
    (hv : HolomorphicInEntries scalarCoords
      (complexEdgeForms (meshAt L k 0) : Set (Edge L k 0 → ComplexMatrix2)) ρ v)
    {T : ((remainderIndex L k).Carrier → ℂ) → ℂ}
    (hT : ∀ ζ, IsSupBelow (remainderIndex L k) ζ (finestMesh L k * ρ / 3) →
      T ζ = v (rescaledForm ζ))
    (hloc : ∀ ζ ζ', IsSupBelow (remainderIndex L k) ζ (finestMesh L k * ρ / 3) →
      IsSupBelow (remainderIndex L k) ζ' (finestMesh L k * ρ / 3) →
      (∀ κ ∈ S, ζ κ = ζ' κ) → T ζ = T ζ') :
    ∃ (l : ℕ) (e : Fin l ≃ S) (h : Coordinates.ComplexCoordinates l → ℂ),
      Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1)
        (openPolydisk 0 (finestMesh L k * ρ / 3)) (fun z _ => h z) ∧
      ∀ ζ, IsSupBelow (remainderIndex L k) ζ (finestMesh L k * ρ / 3) →
        T ζ = h (fieldValues e ζ) := by
  classical
  obtain ⟨F₀, f, hf, hfv⟩ := hv
  have hρ' : 0 < finestMesh L k * ρ / 3 := by positivity
  have : Finite S := hfin.to_subtype
  let e : Fin (Nat.card S) ≃ S := (Finite.equivFin S).symm
  let Ψ : Coordinates.ComplexCoordinates (Nat.card S) →ₗ[ℂ] (F₀ → ComplexMatrix2.traceless) :=
    { toFun := fun z i => ⟨rescaledForm (fieldExtend e z) i, rescaledForm_apply_mem _ _⟩
      map_add' := fun z z' => by
        funext i
        apply Subtype.ext
        simp only [fieldExtend_add, rescaledForm_add]
        rfl
      map_smul' := fun c z => by
        funext i
        apply Subtype.ext
        simp only [fieldExtend_smul, rescaledForm_smul]
        rfl }
  let b := OneLoop.pauliBasis
  let ν : F₀ ≃ Fin (Fintype.card F₀) := Fintype.equivFin _
  let g : Coordinates.ComplexCoordinates (Nat.card S) →ₗ[ℂ]
      Coordinates.ComplexCoordinates (Fintype.card F₀ * 3) :=
    LinearMap.pi fun idx => (b.coord (finProdFinEquiv.symm idx).2) ∘ₗ
      (LinearMap.proj (ν.symm (finProdFinEquiv.symm idx).1)) ∘ₗ Ψ
  have htuple : ∀ z, tupleOfCoords b ν (g z) =
      fun i : F₀ => rescaledForm (fieldExtend e z) i := by
    intro z
    funext i
    have h1 : ∀ c : Fin 3, g z (finProdFinEquiv (ν i, c)) = b.repr (Ψ z i) c := by
      intro c
      change (b.coord (finProdFinEquiv.symm (finProdFinEquiv (ν i, c))).2)
        (Ψ z (ν.symm (finProdFinEquiv.symm (finProdFinEquiv (ν i, c))).1)) = _
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Module.Basis.coord_apply]
    have h2 : ∑ x, (b.repr (Ψ z i)) x • ((b x : ComplexMatrix2.traceless) : ComplexMatrix2) =
        ((Ψ z i : ComplexMatrix2.traceless) : ComplexMatrix2) := by
      have h3 := congrArg Subtype.val (b.sum_repr (Ψ z i))
      rw [Submodule.coe_sum] at h3
      exact h3
    simp only [tupleOfCoords, Coordinates.ComplexCoordinates.tracelessTuple, h1]
    exact h2
  refine ⟨Nat.card S, e, fun z => f fun i => rescaledForm (fieldExtend e z) i, ?_,
    fun ζ hζ => ?_⟩
  · have h0 := (hf b).2 ν
    have hmaps : MapsTo g (openPolydisk 0 (finestMesh L k * ρ / 3))
        (tupleOfCoords b ν ⁻¹' supBall F₀ ρ) := by
      intro z hz
      obtain ⟨s, hs0, hs, hb⟩ := exists_bound_of_isSupBelow hη (isSupBelow_fieldExtend e hρ' hz)
      change tupleOfCoords b ν (g z) ∈ supBall F₀ ρ
      rw [htuple]
      refine ⟨?_, (Real.iSup_le (fun i => hb _) hs0).trans_lt hs⟩
      rw [← Matrices.GroupLieProduct.coe_tracelessFunctions]
      exact fun i _ => rescaledForm_apply_mem _ _
    have h1 := ((hH.1 _ _ h0.1).1 1 _ h0).2.2.2.1 _ _ g
      (isHolomorphicIn_of_linearMap g (isOpen_openPolydisk _)) hmaps
    convert h1 using 1
    funext z j
    simp only [Function.comp_apply, htuple]
    rfl
  · have hb' : IsSupBelow (remainderIndex L k) (fieldExtend e (fieldValues e ζ))
        (finestMesh L k * ρ / 3) :=
      isSupBelow_fieldExtend e hρ' (fieldValues_mem_openPolydisk e hζ)
    rw [hloc ζ _ hζ hb' fun κ hκ => (fieldExtend_fieldValues e ζ hκ).symm, hT _ hb']
    exact (hfv _ (rescaledForm_mem hη _) (rescaledForm_mem_smallFormBall hη hρ hb').2).symm
theorem nearIndices_finite
    (hP : FullLatticeOverTorus.LocallyFiniteCells L k 0)
    (y : InfiniteLattice.AmbientSpace) {R : ℝ} (hR : 0 ≤ R) :
    (nearIndices (remainderIndex L k) y R).Finite := by
  have hb : Bornology.IsBounded
      {x : InfiniteLattice.AmbientSpace | euclidNormVec (x - y) ≤ R} := by
    refine (Metric.isBounded_closedBall (x := y) (r := R)).subset fun x hx => ?_
    refine Metric.mem_closedBall.2 ((dist_pi_le_iff hR).2 fun μ => ?_)
    refine le_trans ?_ hx
    rw [Real.dist_eq]
    refine Real.abs_le_sqrt ?_
    exact Finset.single_le_sum (f := fun ν => (x - y) ν ^ 2) (fun ν _ => sq_nonneg _)
      (Finset.mem_univ μ)
  refine ((Set.finite_univ (α := Fin 3)).prod (hP _ hb).2.1).subset fun κ hκ => ⟨mem_univ _, hκ⟩
end Holomorphy
theorem meansAreLocal_holds (hK : ThreeMapKernels.Claim)
    (hCov : CovariantSmoothingProperties.Statement)
    (hZ : BlockPathContourPivotStatement)
    (hTr : Translations.TranslationProperties)
    (hP : FullLatticeOverTorus.FullLatticeOverTorusClaim)
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) : MeansAreLocal := by
  intro L hL k hk ρ C hN
  have hρ : 0 < ρ := hN.1
  have hS := (hN.2.2.2 k hk).2
  have hη : 0 < finestMesh L k := finestMesh_pos (by have := hL.2; omega)
  have hK' := (hK L hL k hk).2
  have hI := (((hCov L hL).2 k).2 k le_rfl).2.2
  have hT := (hTr L hL k k le_rfl).2.2.2.1
  have hP0 := hP L hL k 0 (Nat.zero_le _) 1 one_pos
  have hPk := hP L hL k k le_rfl 1 one_pos
  have hB0 := fun N => (hP0.2.2.1 N).2.1
  have hBk := fun N => (hPk.2.2.1 N).2.1
  have hs0 := fun N => (hP0.2.2.1 N).1
  have hsk := fun N => (hPk.2.2.1 N).1
  have hfin := fun y => nearIndices_finite (L := L) (k := k) hP0.2.2.2.1 y (R := 3) (by norm_num)
  have hρ' : 0 < finestMesh L k * ρ / 3 := by positivity
  refine ⟨⟨finestMesh L k * ρ / 3, 3, ⟨hρ', ?_, ?_, ?_⟩, ?_⟩,
    ⟨finestMesh L k * ρ / 3, 3, ⟨hρ', ?_, ?_, ?_⟩, ?_⟩⟩
  · exact fun ζ hζ ι' ι hfar => Q_eq_zero_of_far hS hZ hK' hL hk hη hρ hζ ι' ι hfar
  · intro ι' ι
    exact exists_holomorphic_of_local hH hη hρ (hfin _) (hS.holomorphic.kernel_Q ι' ι)
      (fun ζ _ => by rw [remainderGaugeField_rescaledForm hη])
      (fun ζ ζ' hζ hζ' hag => Q_congr hS hZ hK' hL hk hη hρ hζ hζ' ι' ι hag)
  · exact fun ζ hζ n ι' ι => Q_translate hS hK' hη hρ hI hT hB0 hBk hζ n ι' ι
  · exact fun ζ hζ => maxOperatorNorm_pauliForm_lt hη hρ hζ
  · exact fun ζ hζ ι' ι hfar => R_eq_zero_of_far hS hZ hK' hL hk hη hρ hζ ι' ι hfar
  · intro ι' ι
    exact exists_holomorphic_of_local hH hη hρ (hfin _) (hS.holomorphic.kernel_R ι' ι)
      (fun ζ _ => by rw [remainderGaugeField_rescaledForm hη])
      (fun ζ ζ' hζ hζ' hag => R_congr hS hZ hK' hL hk hη hρ hζ hζ' ι' ι hag)
  · exact fun ζ hζ n ι' ι => R_translate hS hK' hη hρ hI hT hB0 hs0 hsk hζ n ι' ι
  · exact fun ζ hζ => maxOperatorNorm_pauliForm_lt hη hρ hζ
end YangMills.Construction.Tower.FullSpace.ScaledMeansLocality
end
