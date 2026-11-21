import YangMills.Construction.Towers.TheFreeOperatorsArePeriodicOperatorsProof
import YangMills.Construction.PeriodicOperators.ComponentsOfAJetWithBoundedRows
import YangMills.Construction.Towers.AveragesOfTheScaledPictureAreLocalProof
import YangMills.Construction.Towers.BackgroundsCutToBondsNearAPoint
import YangMills.Construction.Towers.BoundOfTheBondAverageJet
import YangMills.Construction.Towers.PropertiesOfTheResponse
import YangMills.Construction.Towers.TheNumbersOfTheStripOfTheFreeOperatorsAreAdmitted
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheScaledPictureAndTheirJets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.EdgeSmoothingJetEstimate
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.BackgroundJets
open YangMills.Construction.Tower.FullSpace.IteratedSmallFieldMeans
open YangMills.Construction.Tower.FullSpace.SubRadiusMeanBounds (fineFieldNorm scaledForm)
open YangMills.Construction.Tower.FullSpace.LocalizedBackgrounds (edgeFibre)
open YangMills.Construction.PeriodicOperators.BoundedExpansionJets (RowLocalized)
open YangMills.Construction.Tower.FullSpace.BackgroundProperties (edgeSmoothingFn)
theorem pauliFamily_mem_traceless (a : Fin 3) :
    Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
section Kernels
variable {N N' : Type}
def basisVec (ι : N) : N → ℂ := open Classical in fun x => if x = ι then 1 else 0
theorem basisVec_self (ι : N) : basisVec ι ι = 1 := by simp [basisVec]
theorem basisVec_of_ne {ι x : N} (h : x ≠ ι) : basisVec ι x = 0 := by simp [basisVec, h]
theorem kernel_apply_eq_of_represents {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ}
    (h : Represents T M) (ι' : N') (ι : N) : T ι' ι = M (basisVec ι) ι' := by apply _root_.YangMills.Construction.Tower.FreeOperators.kernel_eq_apply_indicator <;> assumption
theorem map_zero_of_represents {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ}
    (h : Represents T M) (ι' : N') : M 0 ι' = 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.map_zero_of_represents <;> assumption
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
theorem finestMesh_pos (hL : 0 < L) : 0 < Tower.finestMesh L k := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.finestMesh_pos <;> assumption
def pauliForm (ζ : (Tower.remainderIndex L k).Carrier → ℂ) :
    Tower.FullSpace.Edge L k 0 → Matrices.ComplexMatrix2 :=
  (Tower.FullSpace.edgePauliCoordinates L k 0).ofCoeffs ζ
theorem pauliForm_of_pos (ζ : (Tower.remainderIndex L k).Carrier → ℂ)
    {b : Tower.FullSpace.Edge L k 0} (h : b.IsPositivelyOriented) :
    pauliForm ζ b = ∑ a, ζ (a, ⟨b, h⟩) • Matrices.ComplexMatrix2.pauliFamily a := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.pauliForm_of_pos <;> assumption
theorem pauliForm_of_not_pos (ζ : (Tower.remainderIndex L k).Carrier → ℂ)
    {b : Tower.FullSpace.Edge L k 0} (h : ¬ b.IsPositivelyOriented) :
    pauliForm ζ b = -pauliForm ζ b.opposite := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.pauliForm_of_not_pos <;> assumption
theorem pauliForm_opposite (hη : 0 < Tower.finestMesh L k)
    (ζ : (Tower.remainderIndex L k).Carrier → ℂ) (b : Tower.FullSpace.Edge L k 0) :
    pauliForm ζ b.opposite = -pauliForm ζ b := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.pauliForm_opposite <;> assumption
theorem pauliForm_mem (hη : 0 < Tower.finestMesh L k) (ζ : (Tower.remainderIndex L k).Carrier → ℂ) :
    pauliForm ζ ∈ Tower.FullSpace.complexEdgeForms (Tower.meshAt L k 0) := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.pauliForm_mem <;> assumption
theorem pauliForm_eqOn (ζ ζ' : (Tower.remainderIndex L k).Carrier → ℂ)
    {S : Set (Tower.FullSpace.Edge L k 0)} (hS : ∀ b ∈ S, b.opposite ∈ S)
    (h : ∀ b ∈ S, ∀ (hb : b.IsPositivelyOriented) (a : Fin 3),
      ζ (a, ⟨b, hb⟩) = ζ' (a, ⟨b, hb⟩)) :
    EqOn (pauliForm ζ) (pauliForm ζ') S := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.pauliForm_eqOn <;> assumption
theorem scaledForm_eqOn {ζ ζ' : (Tower.remainderIndex L k).Carrier → ℂ}
    {S : Set (Tower.FullSpace.Edge L k 0)}
    (h : EqOn (pauliForm ζ) (pauliForm ζ') S) : EqOn (scaledForm L k ζ) (scaledForm L k ζ') S := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.rescaledForm_eqOn <;> assumption
theorem expForm_zero :
    Tower.FullSpace.expForm (0 : Tower.FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) = 1 := by
  funext b
  unfold Tower.FullSpace.expForm Tower.FullSpace.expTwist
  by_cases hb : b.IsPositivelyOriented <;> simp [hb]
theorem ofCoeffs_zero : (Tower.FullSpace.edgePauliCoordinates L k 0).ofCoeffs 0 = 0 := by
  funext b
  have hp : ∀ b : Tower.FullSpace.Edge L k 0, b.IsPositivelyOriented → pauliForm 0 b = 0 := by
    intro b hb
    rw [pauliForm_of_pos _ hb]
    refine Finset.sum_eq_zero fun a _ => ?_
    change (0 : ℂ) • Matrices.ComplexMatrix2.pauliFamily a = 0
    exact zero_smul _ _
  by_cases hb : b.IsPositivelyOriented
  · exact hp b hb
  · have hr : b.opposite.IsPositivelyOriented :=
      (isPositivelyOriented_or_opposite b).resolve_left hb
    change pauliForm 0 b = 0
    rw [pauliForm_of_not_pos _ hb, hp _ hr, neg_zero]
theorem gaugeFieldOfForm_zero : gaugeFieldOfForm L k 0 = 1 :=
  (congrArg Tower.FullSpace.expForm ofCoeffs_zero).trans expForm_zero
end Forms
section SeriesExpansions
variable {L k : ℕ} {ρ C : ℝ}
theorem Q_represents (hK : Tower.ThreeMapKernels.OnFullSpace L k) (hη : 0 < Tower.finestMesh L k)
    {U : Tower.FullSpace.Edge L k 0 → Matrices.ComplexMatrix2}
    (hU : U ∈ Tower.FullSpace.smallIterateFields L k) :
    Represents (Tower.FullSpace.rescaledOperators L k U).Q
      (Tower.PauliComponentsOfSymmetricKernel.mapOnCoeffs (Tower.FullSpace.edgePauliCoordinates L k 0)
        (Tower.FullSpace.edgePauliCoordinates L k k) (rescaledCovMean U)) := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.Q_represents <;> assumption
theorem Q_apply (hK : Tower.ThreeMapKernels.OnFullSpace L k) (hη : 0 < Tower.finestMesh L k)
    {U : Tower.FullSpace.Edge L k 0 → Matrices.ComplexMatrix2}
    (hU : U ∈ Tower.FullSpace.smallIterateFields L k)
    (ι' : (colourEdges L k k).Carrier) (ι : (colourEdges L k 0).Carrier) :
    (Tower.FullSpace.rescaledOperators L k U).Q ι' ι =
      Tower.pauliCoeff ι'.1 (rescaledCovMean U (pauliForm (basisVec ι)) ι'.2.1) :=
  kernel_apply_eq_of_represents (Q_represents hK hη hU) ι' ι
def posEdgesOver (c : Tower.FullSpace.Edge L k k) : Set (PosEdge L k 0) :=
  {b | b.1 ∈ Tower.FullSpace.edgesOverEdge c}
theorem edgesOverEdge_opposite (c : Tower.FullSpace.Edge L k k) :
    ∀ b ∈ Tower.FullSpace.edgesOverEdge c, b.opposite ∈ Tower.FullSpace.edgesOverEdge c :=
  fun _ hb => ⟨hb.2, hb.1⟩
variable (hS : FullConditions L k ρ C) (hK : Tower.ThreeMapKernels.OnFullSpace L k)
  (hη : 0 < Tower.finestMesh L k)
  (hsmall : ∀ ζ, IsSupBelow (Tower.remainderIndex L k) ζ (Tower.finestMesh L k * ρ / 3) →
    scaledForm L k ζ ∈ smallFormBall L k ρ ∧
      Tower.FullSpace.remainderGaugeField (scaledForm L k ζ) = gaugeFieldOfForm L k ζ)
include hS hsmall in
theorem gaugeFieldOfForm_mem {ζ : (Tower.remainderIndex L k).Carrier → ℂ}
    (hζ : IsSupBelow (Tower.remainderIndex L k) ζ (Tower.finestMesh L k * ρ / 3)) :
    gaugeFieldOfForm L k ζ ∈ Tower.FullSpace.smallIterateFields L k := by
  obtain ⟨ha, hr⟩ := hsmall ζ hζ
  have h := (hS.pointwise _ ha).mem_smallIterate
  rwa [hr] at h
include hS hK hη hsmall in
theorem Q_eq_zero_of_not_mem {ζ : (Tower.remainderIndex L k).Carrier → ℂ}
    (hζ : IsSupBelow (Tower.remainderIndex L k) ζ (Tower.finestMesh L k * ρ / 3))
    (ι' : (colourEdges L k k).Carrier) (ι : (colourEdges L k 0).Carrier)
    (hoff : ι.2.1 ∉ Tower.FullSpace.edgesOverEdge ι'.2.1) :
    (Tower.FullSpace.rescaledOperators L k (gaugeFieldOfForm L k ζ)).Q ι' ι = 0 := by
  obtain ⟨ha, hr⟩ := hsmall ζ hζ
  have hU := gaugeFieldOfForm_mem hS hsmall hζ
  rw [Q_apply hK hη hU]
  have hE : EqOn (pauliForm (basisVec ι)) (pauliForm 0) (Tower.FullSpace.edgesOverEdge ι'.2.1) := by
    refine pauliForm_eqOn _ _ (edgesOverEdge_opposite _) fun b hb hp col => ?_
    refine basisVec_of_ne fun he => hoff ?_
    rw [← he]
    exact hb
  have h1 := hS.locality.local_Q ι'.2.1 _ ha _ ha _ (pauliForm_mem hη _) _ (pauliForm_mem hη _)
    (fun _ _ => rfl) hE
  rw [hr] at h1
  rw [h1]
  exact map_zero_of_represents (Q_represents hK hη hU) ι'
include hS hK hη hsmall in
theorem Q_eq_of_eqOn {ζ ζ' : (Tower.remainderIndex L k).Carrier → ℂ}
    (hζ : IsSupBelow (Tower.remainderIndex L k) ζ (Tower.finestMesh L k * ρ / 3))
    (hζ' : IsSupBelow (Tower.remainderIndex L k) ζ' (Tower.finestMesh L k * ρ / 3))
    (ι' : (colourEdges L k k).Carrier) (ι : (colourEdges L k 0).Carrier)
    (hag : EqOn ζ ζ' (edgeFibre L k (posEdgesOver ι'.2.1))) :
    (Tower.FullSpace.rescaledOperators L k (gaugeFieldOfForm L k ζ)).Q ι' ι =
      (Tower.FullSpace.rescaledOperators L k (gaugeFieldOfForm L k ζ')).Q ι' ι := by
  obtain ⟨ha, hr⟩ := hsmall ζ hζ
  obtain ⟨ha', hr'⟩ := hsmall ζ' hζ'
  rw [Q_apply hK hη (gaugeFieldOfForm_mem hS hsmall hζ),
    Q_apply hK hη (gaugeFieldOfForm_mem hS hsmall hζ')]
  have hE : EqOn (scaledForm L k ζ) (scaledForm L k ζ') (Tower.FullSpace.edgesOverEdge ι'.2.1) := by
    refine scaledForm_eqOn (pauliForm_eqOn _ _ (edgesOverEdge_opposite _) fun b hb hp col => ?_)
    exact hag (show _ ∈ edgeFibre L k (posEdgesOver ι'.2.1) from hb)
  have h1 := hS.locality.local_Q ι'.2.1 _ ha _ ha' _ (pauliForm_mem hη (basisVec ι)) _
    (pauliForm_mem hη (basisVec ι)) hE (fun _ _ => rfl)
  rw [hr, hr'] at h1
  rw [h1]
end SeriesExpansions
section Over
variable {L k : ℕ}
theorem abs_sub_initial_le (hZ : Tower.BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {c : Tower.FullSpace.Edge L k k}
    (hc : c.IsPositivelyOriented) {x : InfiniteLattice.AmbientSpace}
    (hx : x ∈ Tower.FullSpace.cubeOfOrder L (Tower.meshAt L k 0) k c.initial ∪
      Tower.FullSpace.cubeOfOrder L (Tower.meshAt L k 0) k c.terminal) (μ : Fin 4) :
    |x μ - (c.initial : InfiniteLattice.AmbientSpace) μ| ≤ 3 / 2 := by
  have hS := (hZ L hL k k k hk le_rfl le_rfl).2.2.2.2.2.1
  have h := hS.sites_near c hc x
  rw [Nat.sub_self] at h
  obtain ⟨ν, hxν, hν⟩ := h hx
  have h1 : Tower.meshAt L k k = 1 := by simp [Tower.meshAt]
  rw [h1] at hν
  have hco : (x - (c.initial : InfiniteLattice.AmbientSpace)) μ =
      (ν μ : ℝ) * Tower.meshAt L k 0 := by
    rw [hxν]
    simp [Tower.FullSpace.offsetPoint, Finset.sum_apply, Pi.single_apply]
  have : x μ - (c.initial : InfiniteLattice.AmbientSpace) μ = (ν μ : ℝ) * Tower.meshAt L k 0 := hco
  rw [this]
  have := hν μ
  linarith
theorem posEdgesOver_finite (hZ : Tower.BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {c : Tower.FullSpace.Edge L k k}
    (hc : c.IsPositivelyOriented) :
    (posEdgesOver (L := L) (k := k) c).Finite := by
  have hS := (hZ L hL k k k hk le_rfl le_rfl).2.2.2.2.2.1
  have h := hS.bonds_encard_le c hc
  rw [Nat.sub_self] at h
  have hfin := Set.finite_of_encard_le_coe h
  exact (hfin.preimage Subtype.val_injective.injOn).subset fun b hb => ⟨b.2, hb⟩
theorem encard_posEdgesOver_le (hZ : Tower.BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (ι : (Tower.remainderIndex L k).Carrier) :
    {ι' : (colourEdges L k k).Carrier |
      ι ∈ edgeFibre L k (posEdgesOver ι'.2.1)}.encard ≤ (24 : ℕ) := by
  classical
  have hS := (hZ L hL k k k hk le_rfl le_rfl).2.2.2.2.2.1
  have h8 := hS.encard_le_eight
  rw [Nat.sub_self] at h8
  have h := h8 ι.2.1
  have hfin := Set.finite_of_encard_le_coe h
  set S := hfin.toFinset with hSdef
  have hcard : S.card ≤ 8 := by
    have := hfin.encard_eq_coe_toFinset_card
    rw [this] at h
    exact_mod_cast h
  let g : (colourEdges L k k).Carrier → Fin 3 × Tower.FullSpace.Edge L k k := fun ι' => (ι'.1, ι'.2.1)
  have hg : Function.Injective g := by
    rintro ⟨a, c⟩ ⟨a', c'⟩ he
    simp only [g, Prod.mk.injEq] at he
    exact Prod.ext he.1 (Subtype.ext he.2)
  have hsub : g '' {ι' : (colourEdges L k k).Carrier |
      ι ∈ edgeFibre L k (posEdgesOver ι'.2.1)} ⊆
      ((Finset.univ ×ˢ S : Finset (Fin 3 × Tower.FullSpace.Edge L k k)) : Set _) := by
    rintro _ ⟨ι', hι', rfl⟩
    simp only [Finset.coe_product, Finset.coe_univ, Set.mem_prod, Set.mem_univ, true_and, g]
    simp only [hSdef, Set.Finite.coe_toFinset]
    exact ⟨ι'.2.2, hι'.1, hι'.2⟩
  rw [← hg.encard_image]
  refine (Set.encard_le_encard hsub).trans ?_
  rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_product]
  have : (Finset.univ : Finset (Fin 3)).card * S.card ≤ 24 := by
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  exact_mod_cast this
end Over
theorem sum_abs_im_le {δ : ℝ} {κ : Fin 4 → ℂ} (hκ : κ ∈ imStrip (2 * δ)) :
    ∑ μ, |(κ μ).im| ≤ 8 * δ := by
  have : ∑ μ, |(κ μ).im| ≤ ∑ _μ : Fin 4, 2 * δ := Finset.sum_le_sum fun μ _ => hκ μ
  simpa [Finset.sum_const, Finset.card_univ] using this.trans (by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
    linarith)
section Assembly
variable {L k : ℕ} {ρ C : ℝ}
theorem rowLocalized (hZ : Tower.BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hS : FullConditions L k ρ C)
    (hK : Tower.ThreeMapKernels.OnFullSpace L k) (hη : 0 < Tower.finestMesh L k)
    (hsmall : ∀ ζ, IsSupBelow (Tower.remainderIndex L k) ζ (Tower.finestMesh L k * ρ / 3) →
      scaledForm L k ζ ∈ smallFormBall L k ρ ∧
        Tower.FullSpace.remainderGaugeField (scaledForm L k ζ) = gaugeFieldOfForm L k ζ) :
    RowLocalized (Tower.remainderIndex L k) (colourEdges L k 0) (colourEdges L k k)
      (edgeSmoothingFn L k) (fun ι' => edgeFibre L k (posEdgesOver ι'.2.1))
      (fun ι' => edgeFibre L k (posEdgesOver ι'.2.1)) (Tower.finestMesh L k * ρ / 3) (3 / 2) 24 where
  eq_of_eqOn := fun ι' ι ζ ζ' hζ hζ' he => Q_eq_of_eqOn hS hK hη hsmall hζ hζ' ι' ι he
  eq_zero_of_not_mem := fun ι' ι hι ζ hζ => Q_eq_zero_of_not_mem hS hK hη hsmall hζ ι' ι hι
  finite_support := fun ι' => by
    have h := (Set.finite_univ (α := Fin 3)).prod (posEdgesOver_finite hZ hL hk ι'.2.2)
    exact h.subset fun κ hκ => ⟨Set.mem_univ _, hκ⟩
  pos_near := fun ι' ι hι μ =>
    abs_sub_initial_le hZ hL hk ι'.2.2 (show ι.2.1 ∈ Tower.FullSpace.edgesOverEdge ι'.2.1 from hι).1 μ
  encard_le := fun ι => encard_posEdgesOver_le hZ hL hk ι
end Assembly
theorem edgeSmoothingJetBound_holds (hZ : Tower.BlockPathContourPivotStatement)
    (hK : Tower.ThreeMapKernels.Claim)
    (hit : _root_.YangMills.Construction.Tower.IteratedSmallFieldMeans.IteratedMeansClaim)
    (hop : Tower.FullSpace.ScaledOperatorFunctions.ScaledOperatorFunctionsClaim)
    (hnum : Tower.FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hresp : Tower.ResponseProperties.AllProperties)
    (hG : BoundedExpansionJets.ComponentBounds)
    (hB : Tower.FullSpace.SubRadiusMeanBounds.MeanBoundsBelowRadius)
    (hcut : Tower.FullSpace.LocalizedBackgrounds.LocalizedBackgroundBound) :
    Tower.FullSpace.EdgeSmoothingJetBound := by
  intro L hL
  obtain ⟨-, -, δ₀, hδ₀, C₀, -, hδ, hC₀, hadm⟩ := hnum
  have hw : stripHalfWidth = δ₀ :=
    Part.mem_unique (stripHalfWidth_mem (Part.dom_iff_mem.2 ⟨_, hδ₀⟩)) hδ₀
  have hserve := hit.1 L hL
  obtain ⟨hρ, -, hC1, hall⟩ := id hserve
  set ρ := _root_.YangMills.Construction.Tower.IteratedSmallFieldMeans.smallRadius L with hρdef
  set C := _root_.YangMills.Construction.Tower.IteratedSmallFieldMeans.boundConstant L with hCdef
  have hC : 0 ≤ C := by linarith
  have hbd : Tower.ResponseProperties.ResponseBound
      Tower.ResponseProperties.responseConstant := hresp.2.2.1
  set M : ℝ := max (Real.exp (4 * stripHalfWidth * (3 / 2)) *
    Tower.ResponseProperties.responseConstant) 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  set E : ℝ := Real.exp (3 / 2 * (8 * stripHalfWidth)) with hEdef
  set C1 : ℝ := Real.sqrt ((24 : ℕ) : ℝ) * (C * ρ⁻¹ * M) * E with hC1def
  set C2 : ℝ := Real.sqrt ((24 : ℕ) : ℝ) * (4 * C * ρ⁻¹ ^ 2 * M * M) * E with hC2def
  have hC1' : 0 ≤ C1 := by positivity
  have hC2' : 0 ≤ C2 := by positivity
  have hC0' : 0 ≤ C₀ := by linarith
  refine ⟨C₀ + C1 + C1 + C2, by positivity, fun k hk μPlus μMinus p hp => ?_⟩
  have hη : 0 < Tower.finestMesh L k := finestMesh_pos (by have := hL.2; omega)
  obtain ⟨hnorm, hbelow, hsm, hbQ, -⟩ := hB L hL k hk ρ C hserve
  have hS : FullConditions L k ρ C := (hall k hk).2
  have hKk := (hK L hL k hk).2
  have hsmall : ∀ ζ, IsSupBelow (Tower.remainderIndex L k) ζ (Tower.finestMesh L k * ρ / 3) →
      scaledForm L k ζ ∈ smallFormBall L k ρ ∧
        Tower.FullSpace.remainderGaugeField (scaledForm L k ζ) = gaugeFieldOfForm L k ζ :=
    fun ζ hζ => hsm ζ (hbelow ζ hζ)
  have hOp := (hop.1 L hL k hk).1
  have hF := hOp.periodic.2.1
  have hI' := hOp.periodic.2.2.2.2
  obtain ⟨ρ', R, hm, -⟩ := hOp.Q_local ρ C hserve
  have hT : IsLocalOpFun (Tower.remainderIndex L k) (colourEdges L k 0)
      (colourEdges L k k) (edgeSmoothingFn L k) := ⟨ρ', R, hm⟩
  have hrows := rowLocalized hZ hL hk hS hKk hη hsmall
  have hs : 0 < Tower.finestMesh L k * ρ / 3 := by positivity
  have hneg : -p ∈ momentumPolydisc stripHalfWidth := fun μ => by simpa using hp μ
  have hcutAt : ∀ q ∈ momentumPolydisc stripHalfWidth, ∀ (μ : Fin 4)
      (ι' : (colourEdges L k k).Carrier),
      fineFieldNorm L k ((edgeFibre L k (posEdgesOver ι'.2.1)).indicator
        (phaseField (Tower.remainderIndex L k) q (scaledResponseField L k q μ)
          ((colourEdges L k k).pos ι'))) ≤ ENNReal.ofReal M := by
    intro q hq μ ι'
    refine (hcut L hL k hk q hq μ _ (3 / 2) (by norm_num) _ (fun κ hκ ν => ?_) _ hbd).trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    exact abs_sub_initial_le hZ hL hk ι'.2.2
      (show κ.2.1 ∈ Tower.FullSpace.edgesOverEdge ι'.2.1 from hκ).1 ν
  have hcomp := hG _ _ _ hF hF hI' _ hT (fineFieldNorm L k) ρ C hρ hC hnorm hbQ _ _ _ (3 / 2) 24 hs
    (by norm_num) hrows p (scaledResponseField L k p μPlus) (scaledResponseField L k (-p) μMinus) M hM
    (hcutAt p hp μPlus) (hcutAt (-p) hneg μMinus)
  have hexp : ∀ κ ∈ imStrip (2 * stripHalfWidth),
      Real.exp (3 / 2 * ∑ μ, |(κ μ).im|) ≤ E := fun κ hκ =>
    Real.exp_le_exp.2 (by have := sum_abs_im_le hκ; linarith)
  have hbound1 : ∀ κ ∈ imStrip (2 * stripHalfWidth),
      ENNReal.ofReal (Real.sqrt ((24 : ℕ) : ℝ) * (C * ρ⁻¹ * M) *
        Real.exp (3 / 2 * ∑ μ, |(κ μ).im|)) ≤ ENNReal.ofReal C1 := fun κ hκ =>
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hexp κ hκ) (by positivity))
  have hbound2 : ∀ κ ∈ imStrip (2 * stripHalfWidth),
      ENNReal.ofReal (Real.sqrt ((24 : ℕ) : ℝ) * (4 * C * ρ⁻¹ ^ 2 * M * M) *
        Real.exp (3 / 2 * ∑ μ, |(κ μ).im|)) ≤ ENNReal.ofReal C2 := fun κ hκ =>
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hexp κ hκ) (by positivity))
  have hT0 : coeffZero (Tower.remainderIndex L k) (colourEdges L k 0) (colourEdges L k k)
      (edgeSmoothingFn L k) = Tower.FreeStrip.edgeAvg L k := by
    change (Tower.FullSpace.rescaledOperators L k (gaugeFieldOfForm L k 0)).Q = _
    rw [gaugeFieldOfForm_zero]
    rfl
  have h00 : (⨆ κ ∈ imStrip (2 * stripHalfWidth),
      quotHomNorm ((edgeSmoothingJet L k p μPlus μMinus).f00 κ)) ≤ ENNReal.ofReal C₀ := by
    refine iSup₂_le fun κ hκ => ?_
    have hsym := ((hadm.2.2 L hL k hk).1.edge_avg).2 κ (hw ▸ hκ)
    rw [← hT0] at hsym
    exact hsym
  have h10 : (⨆ κ ∈ stripAddShift stripHalfWidth p,
      quotHomNorm ((edgeSmoothingJet L k p μPlus μMinus).f10 κ)) ≤ ENNReal.ofReal C1 :=
    iSup₂_le fun κ hκ => (hcomp κ).1.trans (hbound1 κ hκ.1)
  have h01 : (⨆ κ ∈ stripSubShift stripHalfWidth p,
      quotHomNorm ((edgeSmoothingJet L k p μPlus μMinus).f01 κ)) ≤ ENNReal.ofReal C1 :=
    iSup₂_le fun κ hκ => (hcomp κ).2.1.trans (hbound1 κ hκ.1)
  have hδpos : 0 < stripHalfWidth := hw ▸ hδ.1
  have h11 : (⨆ κ ∈ realDualPoints,
      quotHomNorm ((edgeSmoothingJet L k p μPlus μMinus).f11 κ)) ≤ ENNReal.ofReal C2 := by
    refine iSup₂_le fun κ hκ => (hcomp κ).2.2.trans (hbound2 κ fun μ => ?_)
    have him : (κ μ).im = 0 := hκ μ
    rw [him, abs_zero]
    positivity
  unfold JetQuad.jetNorm
  calc _ ≤ ENNReal.ofReal C₀ + ENNReal.ofReal C1 + ENNReal.ofReal C1 + ENNReal.ofReal C2 := by
        gcongr
    _ = ENNReal.ofReal (C₀ + C1 + C1 + C2) := by
        rw [ENNReal.ofReal_add (by positivity) hC2', ENNReal.ofReal_add (by positivity) hC1',
          ENNReal.ofReal_add hC0' hC1']
end YangMills.Construction.Tower.FullSpace.EdgeSmoothingJetEstimate
end
