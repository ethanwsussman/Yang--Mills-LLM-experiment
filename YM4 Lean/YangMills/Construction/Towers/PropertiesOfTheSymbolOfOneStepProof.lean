import YangMills.Construction.Towers.FormsOfTheFreeOperatorsInCoefficientsProof
import YangMills.Construction.Towers.CoefficientsOfTheResponseAtAColourProof
import YangMills.Construction.Towers.PropertiesOfTheSymbolOfOneStep
import YangMills.Construction.Towers.SiteAverageOnTheWholeProof
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction.Tower.StepEntryBounds
open Matrices OneLoop Coordinates Conventions
open ResponseProperties (SmallMomentumBehaviour InFundamentalStrip responseSymbolForm euclidNorm)
open PlaneWaves (VertexClass edgeAt fourierCoeff edgeFourierCoeff edgeFieldOfClasses freqBox
  freqWindow mem_freqWindow fourierPhase shiftedFreq)
open PlaneWaveCalculus (posEdgeAt topEdgeComponent expWave)
open BackgroundFieldResponse (responseKernel)
open PeriodicOperators
open PeriodicOperators.Tempered.OneStep
section Holomorphic
variable {N : ℕ}
theorem isHolomorphicIn_scalar_iff (O : Set (ComplexCoordinates N)) (u : ComplexCoordinates N → ℂ) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O (fun z _ => u z) ↔
      IsOpen O ∧ ContinuousOn u O ∧ ∀ a ∈ O, ∀ j : Fin N, ∀ᶠ ζ in 𝓝 (0 : ℂ),
        DifferentiableAt ℂ (fun ζ : ℂ => u (a + ζ • ComplexCoordinates.stdBasisVector j)) ζ := by apply _root_.YangMills.Construction.PeriodicOperators.OpFunComp.isHolomorphicIn_scalar_iff <;> assumption
theorem isHolomorphicIn_scalar_congr {O : Set (ComplexCoordinates N)} {u v : ComplexCoordinates N → ℂ}
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z) (e : EqOn v u O) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => v z := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_congr <;> assumption
theorem isHolomorphicIn_scalar_const_mul {O : Set (ComplexCoordinates N)}
    {u : ComplexCoordinates N → ℂ} (c : ℂ)
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => c * u z := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_const_mul <;> assumption
theorem isHolomorphicIn_scalar_mul {O : Set (ComplexCoordinates N)} {u v : ComplexCoordinates N → ℂ}
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z)
    (h' : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => v z) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z * v z := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_mul <;> assumption
theorem isHolomorphicIn_scalar_sum {J : Type} (s : Finset J) {O : Set (ComplexCoordinates N)}
    (ho : IsOpen O) {u : J → ComplexCoordinates N → ℂ}
    (h : ∀ i ∈ s, ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u i z) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => ∑ i ∈ s, u i z := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_sum <;> assumption
theorem isHolomorphicIn_scalar_of_differentiable {O : Set (ComplexCoordinates N)} (ho : IsOpen O)
    {u : ComplexCoordinates N → ℂ} (hu : Differentiable ℂ u) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z := by
  refine (isHolomorphicIn_scalar_iff O u).2 ⟨ho, hu.continuous.continuousOn, fun a _ j => ?_⟩
  refine Eventually.of_forall fun ζ => ?_
  have hl : Differentiable ℂ fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j := by fun_prop
  exact (hu.comp hl) ζ
end Holomorphic
section Bounded
variable {X J : Type}
def IsBddOn (S : Set X) (u : X → ℂ) : Prop := ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ S, ‖u x‖ ≤ B
theorem IsBddOn.mul {S : Set X} {u v : X → ℂ} (h : IsBddOn S u) (h' : IsBddOn S v) :
    IsBddOn S fun x => u x * v x := by
  obtain ⟨B, hB, hu⟩ := h
  obtain ⟨B', hB', hv⟩ := h'
  refine ⟨B * B', mul_nonneg hB hB', fun x hx => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hu x hx) (hv x hx) (norm_nonneg _) hB
theorem IsBddOn.mono {S S' : Set X} {u : X → ℂ} (h : IsBddOn S u) (hs : S' ⊆ S) :
    IsBddOn S' u := by
  obtain ⟨B, hB, hu⟩ := h
  exact ⟨B, hB, fun x hx => hu x (hs hx)⟩
theorem isBddOn_const (S : Set X) (c : ℂ) : IsBddOn S fun _ => c :=
  ⟨‖c‖, norm_nonneg _, fun _ _ => le_rfl⟩
theorem isBddOn_sum {S : Set X} (s : Finset J) {u : J → X → ℂ}
    (h : ∀ j ∈ s, IsBddOn S (u j)) : IsBddOn S fun x => ∑ j ∈ s, u j x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, fun x _ => by simp⟩
  | insert j s hj ih =>
    obtain ⟨B, hB, hu⟩ := h j (Finset.mem_insert_self j s)
    obtain ⟨B', hB', hv⟩ := ih fun j' hj' => h j' (Finset.mem_insert_of_mem hj')
    refine ⟨B + B', add_nonneg hB hB', fun x hx => ?_⟩
    show ‖∑ j ∈ insert j s, u j x‖ ≤ _
    rw [Finset.sum_insert hj]
    exact (norm_add_le _ _).trans (add_le_add (hu x hx) (hv x hx))
theorem exists_common_bound {S : Set X} (s : Finset J) {u : J → X → ℂ}
    (h : ∀ j ∈ s, IsBddOn S (u j)) : ∃ B : ℝ, 0 ≤ B ∧ ∀ j ∈ s, ∀ x ∈ S, ‖u j x‖ ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, fun j hj => by simp at hj⟩
  | insert j s hj ih =>
    obtain ⟨B, hB, hu⟩ := h j (Finset.mem_insert_self j s)
    obtain ⟨B', hB', hv⟩ := ih fun j' hj' => h j' (Finset.mem_insert_of_mem hj')
    refine ⟨B + B', add_nonneg hB hB', fun j' hj' x hx => ?_⟩
    rcases Finset.mem_insert.1 hj' with rfl | hj''
    · exact (hu x hx).trans (le_add_of_nonneg_right hB')
    · exact (hv j' hj'' x hx).trans (le_add_of_nonneg_left hB)
theorem norm_sum_le_card_mul {s t : Finset J} (hts : t ⊆ s) (f : J → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j ∈ t, ‖f j‖ ≤ c) : ‖∑ j ∈ t, f j‖ ≤ (s.card : ℝ) * c := by
  refine (norm_sum_le_of_le _ h).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hts) hc
end Bounded
theorem pauliCoeff_smul_pauli (c : ℂ) (a b : Fin 3) :
    pauliCoeff b (c • ComplexMatrix2.pauliFamily a) = if b = a then c else 0 := by apply _root_.YangMills.Construction.Tower.FullVertexSmoothing.pauliCoeff_smul_pauliFamily <;> assumption
theorem pauliNorm_smul_pauli (c : ℂ) (a : Fin 3) :
    pauliNorm (c • ComplexMatrix2.pauliFamily a) = ‖c‖ := by
  unfold pauliNorm
  simp only [pauliCoeff_smul_pauli]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp
theorem pauliNorm_le_familyNorm (F : Fin 4 → ComplexMatrix2) (ρ : Fin 4) :
    pauliNorm (F ρ) ≤ pauliFamilyNorm F := by apply _root_.YangMills.Construction.Tower.ResponseBoundProof.pauliNorm_le_familyNorm <;> assumption
theorem norm_le_euclidNorm (p : Fin 4 → ℂ) : ‖p‖ ≤ euclidNorm p := by apply _root_.YangMills.Construction.Tower.TrialResponse.norm_le_euclidNorm <;> assumption
theorem euclidNorm_le_two_mul_norm (p : Fin 4 → ℂ) : euclidNorm p ≤ 2 * ‖p‖ := by
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have h : ∀ ρ ∈ (Finset.univ : Finset (Fin 4)), ‖p ρ‖ ^ 2 ≤ ‖p‖ ^ 2 := fun ρ _ =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm p ρ) 2
  have := Finset.sum_le_card_nsmul _ _ _ h
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  push_cast at this
  nlinarith
theorem euclidNorm_nonneg (p : Fin 4 → ℂ) : 0 ≤ euclidNorm p := Real.sqrt_nonneg _
section Classes
variable {L k : ℕ}
theorem meshAt_self (L k : ℕ) : meshAt L k k = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.meshAt_self <;> assumption
theorem axisStep_injective {a : ℝ} (ha : a ≠ 0) {μ ρ : Fin 4}
    (h : InfiniteLattice.axisStep a μ = InfiniteLattice.axisStep a ρ) : μ = ρ := by apply _root_.YangMills.Construction.Tower.FacesContainingEdge.axisStep_injective <;> assumption
def basisEdgeClass (L k : ℕ) (a : Fin 3) (μ : Fin 4) : (colourEdges L k k).UnitQuot :=
  (colourEdges L k k).mkQuot 1 (a, posEdgeAt L k k 0 μ)
theorem topEdgeComponent_injective (hT : TowerTranslations.Claim)
    (hL : IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {z z' : (colourEdges L k k).UnitQuot → ℂ}
    (h : ∀ ρ, topEdgeComponent L k z ρ = topEdgeComponent L k z' ρ) : z = z' := by apply _root_.YangMills.Construction.Tower.TrialResponse.eq_of_topEdgeComponent <;> assumption
open Classical in
def basisEdgeVector (L k : ℕ) (a : Fin 3) (μ : Fin 4) : (colourEdges L k k).UnitQuot → ℂ :=
  Pi.single (basisEdgeClass L k a μ) 1
theorem topEdgeComponent_basisEdgeVector (hT : TowerTranslations.Claim)
    (hL : IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (a : Fin 3) (μ ρ : Fin 4) :
    topEdgeComponent L k (basisEdgeVector L k a μ) ρ =
      if ρ = μ then ComplexMatrix2.pauliFamily a else 0 := by apply _root_.YangMills.Construction.Tower.ResponseCoefficients.topEdgeComponent_basisVector <;> assumption
end Classes
section Colour
variable {L k : ℕ}
def responseColumn (L k : ℕ) (κ : Fin 4 → ℂ) (β : PosEdge L k 0) (μ : Fin 4) : ℂ :=
  responseSymbolForm L k κ (basisEdgeVector L k 0 μ) ((colourEdges L k 0).mkQuot 1 (0, β))
theorem fourierSymbol_colour_ne (hc : IsColourTrivial (responseKernel L k)) (κ : Fin 4 → ℂ)
    {a a' : Fin 3} (hne : a' ≠ a) (y : PosEdge L k 0) (x : PosEdge L k k) :
    fourierSymbol (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) κ (a', y) (a, x) =
      0 := by apply _root_.YangMills.Construction.Tower.ResponseCoefficients.fourierSymbol_colour_ne <;> assumption
theorem fourierSymbol_colour_eq (hc : IsColourTrivial (responseKernel L k)) (κ : Fin 4 → ℂ)
    (a a' : Fin 3) (y : PosEdge L k 0) (x : PosEdge L k k) :
    fourierSymbol (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) κ (a, y) (a, x) =
      fourierSymbol (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) κ
        (a', y) (a', x) := by apply _root_.YangMills.Construction.Tower.ResponseCoefficients.fourierSymbol_colour_eq <;> assumption
structure PointData (L k : ℕ) (κ : Fin 4 → ℂ) : Prop where
  entry_eq : ∀ ι' ι, carrierEntry
    (symbolHom (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) κ) ι' ι =
      fourierSymbol (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) κ ι' ι
  colour_trivial : IsColourTrivial (responseKernel L k)
theorem responseSymbolForm_basis {κ : Fin 4 → ℂ} (h : PointData L k κ) (a a' : Fin 3) (μ : Fin 4)
    (β : PosEdge L k 0) :
    responseSymbolForm L k κ (basisEdgeVector L k a μ) ((colourEdges L k 0).mkQuot 1 (a', β)) =
      if a' = a then responseColumn L k κ β μ else 0 := by
  have e₁ : ∀ c c' : Fin 3, responseSymbolForm L k κ (basisEdgeVector L k c μ)
      ((colourEdges L k 0).mkQuot 1 (c', β)) =
      fourierSymbol (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) κ (c', β)
        (c, posEdgeAt L k k 0 μ) := fun c c' => h.entry_eq _ _
  split_ifs with hc
  · subst hc
    rw [e₁, responseColumn, e₁, fourierSymbol_colour_eq h.colour_trivial κ a' 0]
  · rw [e₁, fourierSymbol_colour_ne h.colour_trivial κ hc]
theorem edgeFieldOfClasses_basis {κ : Fin 4 → ℂ} (h : PointData L k κ) (a : Fin 3) (μ : Fin 4)
    (β : PosEdge L k 0) :
    edgeFieldOfClasses L k (responseSymbolForm L k κ (basisEdgeVector L k a μ)) β =
      responseColumn L k κ β μ • ComplexMatrix2.pauliFamily a := by
  show ∑ b, responseSymbolForm L k κ (basisEdgeVector L k a μ)
    ((colourEdges L k 0).mkQuot 1 (b, β)) • ComplexMatrix2.pauliFamily b = _
  simp only [responseSymbolForm_basis h, ite_smul, zero_smul]
  simp
end Colour
section Number
variable {L k : ℕ}
theorem finite_vertexClass (hI : TowerIndexSets.Claim) (hL : IsAdmissibleBlockingFactor L) :
    Finite (VertexClass L k) := by apply _root_.YangMills.Construction.Tower.ResponseCoefficients.finite_vertexClass <;> assumption
def responseMode (L k : ℕ) (κ : Fin 4 → ℂ) (ρ μ : Fin 4) (m : Fin 4 → ℤ) : ℂ :=
  ((finestMesh L k ^ 4 : ℝ) : ℂ) * ∑ᶠ c : VertexClass L k,
    fourierPhase m (Quot.out c : FullSpace.Vertex L k 0) *
      responseColumn L k κ (edgeAt L k (Quot.out c) ρ) μ
theorem edgeFourierCoeff_basis (hI : TowerIndexSets.Claim) (hL : IsAdmissibleBlockingFactor L)
    {κ : Fin 4 → ℂ} (h : PointData L k κ) (a : Fin 3) (ρ μ : Fin 4) (m : Fin 4 → ℤ) :
    edgeFourierCoeff L k (responseSymbolForm L k κ (basisEdgeVector L k a μ)) ρ m =
      responseMode L k κ ρ μ m • ComplexMatrix2.pauliFamily a := by
  have := finite_vertexClass (k := k) hI hL
  let _ := Fintype.ofFinite (VertexClass L k)
  unfold edgeFourierCoeff PlaneWaves.fourierCoeff responseMode
  simp only [edgeFieldOfClasses_basis h, finsum_eq_sum_of_fintype, mul_smul, Finset.sum_smul]
theorem responseCoeff_eq_responseMode (hT : TowerTranslations.Claim)
    (hI : TowerIndexSets.Claim) (hL : IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    {κ : Fin 4 → ℂ} (h : PointData L k κ) (ρ μ : Fin 4) (m : Fin 4 → ℤ) :
    responseCoeff L k κ ρ μ m = responseMode L k κ ρ μ m := by
  have hex : ∃ c : ℂ, ∀ (a : Fin 3) (z : (colourEdges L k k).UnitQuot → ℂ),
      (∀ ν, topEdgeComponent L k z ν = if ν = μ then ComplexMatrix2.pauliFamily a else 0) →
        edgeFourierCoeff L k (responseSymbolForm L k κ z) ρ m =
          c • ComplexMatrix2.pauliFamily a := by
    refine ⟨responseMode L k κ ρ μ m, fun a z hz => ?_⟩
    have e : z = basisEdgeVector L k a μ := topEdgeComponent_injective hT hL hk fun ν => by
      rw [hz, topEdgeComponent_basisEdgeVector hT hL hk]
    rw [e]
    exact edgeFourierCoeff_basis hI hL h a ρ μ m
  have hs := Classical.epsilon_spec hex 0 (basisEdgeVector L k 0 μ)
    (topEdgeComponent_basisEdgeVector hT hL hk 0 μ)
  rw [edgeFourierCoeff_basis hI hL h] at hs
  have e := congrArg (pauliCoeff 0) hs
  rw [pauliCoeff_smul_pauli, pauliCoeff_smul_pauli, if_pos rfl, if_pos rfl] at e
  exact e.symm
theorem responseMode_eq_sum [Fintype (VertexClass L k)] (κ : Fin 4 → ℂ) (ρ μ : Fin 4)
    (m : Fin 4 → ℤ) :
    responseMode L k κ ρ μ m = ((finestMesh L k ^ 4 : ℝ) : ℂ) * ∑ c : VertexClass L k,
      fourierPhase m (Quot.out c : FullSpace.Vertex L k 0) *
        responseColumn L k κ (edgeAt L k (Quot.out c) ρ) μ := by
  rw [responseMode, finsum_eq_sum_of_fintype]
theorem responseColumn_holomorphic {O : Set (Fin 4 → ℂ)}
    (hon : ResponseOperators.ResponseSymbolsOn L k O) (β : PosEdge L k 0) (μ : Fin 4) :
    ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) O fun κ _ =>
      responseColumn L k κ β μ :=
  hon.resp_holomorphic.2.2 ((colourEdges L k 0).mkQuot 1 (0, β), basisEdgeClass L k 0 μ)
theorem responseColumn_bdd {O : Set (Fin 4 → ℂ)}
    (hon : ResponseOperators.ResponseSymbolsOn L k O) (β : PosEdge L k 0) (μ : Fin 4) :
    IsBddOn O fun κ => responseColumn L k κ β μ := by
  obtain ⟨C, hC⟩ := hon.resp_bounded
    ((colourEdges L k 0).mkQuot 1 (0, β), basisEdgeClass L k 0 μ)
  exact ⟨|C|, abs_nonneg C, fun κ hκ => (hC κ hκ).trans (le_abs_self C)⟩
theorem responseMode_holomorphic (hI : TowerIndexSets.Claim)
    (hL : IsAdmissibleBlockingFactor L) {O : Set (Fin 4 → ℂ)} (ho : IsOpen O)
    (hon : ResponseOperators.ResponseSymbolsOn L k O) (ρ μ : Fin 4) (m : Fin 4 → ℤ) :
    ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) O fun κ _ =>
      responseMode L k κ ρ μ m := by
  have := finite_vertexClass (k := k) hI hL
  let _ := Fintype.ofFinite (VertexClass L k)
  simp only [responseMode_eq_sum]
  refine isHolomorphicIn_scalar_const_mul _ (isHolomorphicIn_scalar_sum _ ho fun c _ => ?_)
  exact isHolomorphicIn_scalar_const_mul _ (responseColumn_holomorphic hon _ μ)
theorem responseMode_bdd (hI : TowerIndexSets.Claim)
    (hL : IsAdmissibleBlockingFactor L) {O : Set (Fin 4 → ℂ)}
    (hon : ResponseOperators.ResponseSymbolsOn L k O) (ρ μ : Fin 4) (m : Fin 4 → ℤ) :
    IsBddOn O fun κ => responseMode L k κ ρ μ m := by
  have := finite_vertexClass (k := k) hI hL
  let _ := Fintype.ofFinite (VertexClass L k)
  simp only [responseMode_eq_sum]
  refine (isBddOn_const _ _).mul (isBddOn_sum _ fun c _ => ?_)
  exact (isBddOn_const _ _).mul (responseColumn_bdd hon _ μ)
end Number
section Mean
variable {L : ℕ}
theorem inv_finestMesh (hL : 0 < L) (i : ℕ) : (finestMesh L i)⁻¹ = (L : ℝ) ^ i := by
  simp [finestMesh, meshAt, zpow_neg]
theorem card_freqWindow (hL : Odd L) (i : ℕ) : (freqWindow L i).card = L ^ i := by
  obtain ⟨r, hr⟩ := hL.pow (n := i)
  have hpos : 0 < L := hL.pos
  have e : 1 / 2 * ((finestMesh L i)⁻¹ - 1) = (r : ℝ) := by
    rw [inv_finestMesh hpos]
    have : (L : ℝ) ^ i = 2 * r + 1 := by exact_mod_cast hr
    rw [this]
    ring
  have hf : ⌊1 / 2 * ((finestMesh L i)⁻¹ - 1)⌋ = (r : ℤ) := by
    rw [e]
    exact Int.floor_natCast r
  rw [freqWindow, hf, Int.card_Icc, hr]
  omega
theorem card_freqBox (hL : Odd L) (i : ℕ) : (freqBox L i).card = (L ^ i) ^ 4 := by
  rw [freqBox, Fintype.card_piFinset]
  simp [card_freqWindow hL]
theorem zero_mem_freqBox (hL : 0 < L) (i : ℕ) : (0 : Fin 4 → ℤ) ∈ freqBox L i := by
  rw [PlaneWaves.mem_freqBox]
  intro ν
  rw [inv_finestMesh hL]
  have : (1 : ℝ) ≤ (L : ℝ) ^ i := one_le_pow₀ (by exact_mod_cast hL)
  simp only [Pi.zero_apply, Int.cast_zero, abs_zero]
  linarith
theorem stepMean_zero (hL : Odd L) (i : ℕ) (ρ : Fin 4) : stepMean L i ρ 0 = 1 := by
  have hne : (L : ℂ) ≠ 0 := by exact_mod_cast hL.pos.ne'
  have h1 : ∀ y, expWave 0 y = 1 := fun y => by simp [expWave, bilinDot]
  simp only [stepMean, h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    card_freqBox hL]
  push_cast
  rw [inv_mul_eq_div, div_eq_one_iff_eq (pow_ne_zero _ hne)]
  ring
theorem stepMean_differentiable (L i : ℕ) (ρ : Fin 4) :
    Differentiable ℂ (stepMean L i ρ) := by
  unfold stepMean expWave bilinDot
  fun_prop
theorem shiftedFreq_differentiable (m : Fin 4 → ℤ) :
    Differentiable ℂ fun κ : Fin 4 → ℂ => shiftedFreq κ m := by apply _root_.YangMills.Construction.Tower.FreeResolvents.differentiable_shiftedFreq <;> assumption
theorem expWave_bdd (s : ℝ) (m : Fin 4 → ℤ) (y : InfiniteLattice.AmbientSpace) :
    IsBddOn (imStrip s) fun κ => expWave (shiftedFreq κ m) y := by
  refine ⟨Real.exp (|s| * ∑ ν, |y ν|), (Real.exp_pos _).le, fun κ hκ => ?_⟩
  show ‖Complex.exp (Complex.I * bilinDot (shiftedFreq κ m) (toComplexVec y))‖ ≤ _
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  have e : (Complex.I * bilinDot (shiftedFreq κ m) (toComplexVec y)).re =
      -∑ ν, (κ ν).im * y ν := by
    simp [bilinDot, PlaneWaves.shiftedFreq, toComplexVec, Complex.mul_re, Complex.mul_im]
  rw [e, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun ν _ => ?_
  have h₁ : |(κ ν).im| ≤ |s| := (hκ ν).trans (le_abs_self s)
  calc -((κ ν).im * y ν) ≤ |(κ ν).im * y ν| := neg_le_abs _
    _ = |(κ ν).im| * |y ν| := abs_mul _ _
    _ ≤ |s| * |y ν| := mul_le_mul_of_nonneg_right h₁ (abs_nonneg _)
theorem stepMean_bdd (L i : ℕ) (s : ℝ) (ρ : Fin 4) (m : Fin 4 → ℤ) :
    IsBddOn (imStrip s) fun κ => stepMean L i ρ (shiftedFreq κ m) := by
  unfold stepMean
  refine (isBddOn_const _ _).mul (isBddOn_sum _ fun w _ => isBddOn_sum _ fun t _ => ?_)
  exact expWave_bdd s m _
theorem stepMean_sub_one_le (hL : Odd L) (i : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ p in 𝓝 (0 : Fin 4 → ℂ), ∀ ρ,
      ‖stepMean L i ρ p - 1‖ ≤ D * euclidNorm p := by
  have h : ∀ ρ : Fin 4, ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ p in 𝓝 (0 : Fin 4 → ℂ),
      ‖stepMean L i ρ p - 1‖ ≤ D * euclidNorm p := fun ρ => by
    have hO := ((stepMean_differentiable L i ρ) 0).isBigO_sub
    obtain ⟨c, hc, hb⟩ := hO.exists_nonneg
    refine ⟨c, hc, ?_⟩
    filter_upwards [hb.bound] with p hp
    rw [stepMean_zero hL, sub_zero] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left (norm_le_euclidNorm p) hc)
  choose D hD hn using h
  refine ⟨∑ ρ, D ρ, Finset.sum_nonneg fun ρ _ => hD ρ, ?_⟩
  filter_upwards [eventually_all.2 hn] with p hp ρ
  refine (hp ρ).trans (mul_le_mul_of_nonneg_right ?_ (euclidNorm_nonneg p))
  exact Finset.single_le_sum (f := D) (fun ρ _ => hD ρ) (Finset.mem_univ ρ)
end Mean
section Near
variable {L k : ℕ}
theorem topEdgeComponent_basis_eq_smul (hT : TowerTranslations.Claim)
    (hL : IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (μ ρ : Fin 4) :
    topEdgeComponent L k (basisEdgeVector L k 0 μ) ρ =
      kroneckerEntry ρ μ • ComplexMatrix2.pauliFamily 0 := by
  rw [topEdgeComponent_basisEdgeVector hT hL hk]
  by_cases h : ρ = μ <;> simp [kroneckerEntry, h]
theorem pauliFamilyNorm_basis (hT : TowerTranslations.Claim)
    (hL : IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (μ : Fin 4) :
    pauliFamilyNorm (topEdgeComponent L k (basisEdgeVector L k 0 μ)) = 1 := by
  unfold pauliFamilyNorm
  simp only [topEdgeComponent_basis_eq_smul hT hL hk, pauliNorm_smul_pauli]
  rw [Finset.sum_eq_single μ]
  · simp [kroneckerEntry]
  · intro ρ _ hρ
    simp [kroneckerEntry, hρ]
  · simp
theorem responseMode_near_zero (hT : TowerTranslations.Claim)
    (hI : TowerIndexSets.Claim) (hL : IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    {p : Fin 4 → ℂ} (h : PointData L k p) {C : ℝ} (ρ μ : Fin 4)
    (hb : (∀ m ∈ freqBox L k, m ≠ 0 →
        pauliFamilyNorm (fun μ' =>
          edgeFourierCoeff L k (responseSymbolForm L k p (basisEdgeVector L k 0 μ)) μ' m) ≤
          C * (euclidNorm p ^ 2 * pauliFamilyNorm (topEdgeComponent L k (basisEdgeVector L k 0 μ)))) ∧
      pauliFamilyNorm (fun μ' =>
          edgeFourierCoeff L k (responseSymbolForm L k p (basisEdgeVector L k 0 μ)) μ' 0 -
          topEdgeComponent L k (basisEdgeVector L k 0 μ) μ') ≤
        C * (euclidNorm p * pauliFamilyNorm (topEdgeComponent L k (basisEdgeVector L k 0 μ)))) :
    (∀ m ∈ freqBox L k, m ≠ 0 → ‖responseMode L k p ρ μ m‖ ≤ C * euclidNorm p ^ 2) ∧
      ‖responseMode L k p ρ μ 0 - kroneckerEntry ρ μ‖ ≤ C * euclidNorm p := by
  simp only [pauliFamilyNorm_basis hT hL hk, mul_one] at hb
  refine ⟨fun m hm hm0 => ?_, ?_⟩
  · have e : pauliNorm
        (edgeFourierCoeff L k (responseSymbolForm L k p (basisEdgeVector L k 0 μ)) ρ m) ≤ _ :=
      pauliNorm_le_familyNorm
        (fun μ' => edgeFourierCoeff L k (responseSymbolForm L k p (basisEdgeVector L k 0 μ)) μ' m) ρ
    rw [edgeFourierCoeff_basis hI hL h, pauliNorm_smul_pauli] at e
    exact e.trans (hb.1 m hm hm0)
  · have e : pauliNorm
        (edgeFourierCoeff L k (responseSymbolForm L k p (basisEdgeVector L k 0 μ)) ρ 0 -
        topEdgeComponent L k (basisEdgeVector L k 0 μ) ρ) ≤ _ :=
      pauliNorm_le_familyNorm (fun μ' =>
          edgeFourierCoeff L k (responseSymbolForm L k p (basisEdgeVector L k 0 μ)) μ' 0 -
          topEdgeComponent L k (basisEdgeVector L k 0 μ) μ') ρ
    rw [edgeFourierCoeff_basis hI hL h, topEdgeComponent_basis_eq_smul hT hL hk, ← sub_smul,
      pauliNorm_smul_pauli] at e
    exact e.trans hb.2
end Near
theorem stepEntry_congr (L i : ℕ) {m m' : Fin 4 → ℤ} (hc : CongruentMod L m m') (κ : Fin 4 → ℂ)
    (ρ μ : Fin 4) : stepEntry L i m κ ρ μ = stepEntry L i m' κ ρ μ := by
  unfold stepEntry
  refine Finset.sum_congr (Finset.filter_congr fun x _ => ?_) fun _ _ => rfl
  constructor
  · intro h ν
    have e := dvd_add (h ν) (hc ν)
    rwa [sub_add_sub_cancel] at e
  · intro h ν
    have e := dvd_sub (h ν) (hc ν)
    rwa [sub_sub_sub_cancel_right] at e
theorem claim_holds (hR : ResponseOperators.Claim) (hP : ResponseProperties.AllProperties)
    (hQ : StripSymbols.Claim) (hT : TowerTranslations.Claim)
    (hI : TowerIndexSets.Claim) : Claim := by
  intro δ₀ hδ L hL i
  obtain ⟨δ₁, hδ₁, hAt⟩ := hR
  have e₀ : δ₁ = δ₀ := Part.mem_unique hδ₁ hδ
  rw [e₀] at hAt
  have hk : 1 ≤ i + 1 := Nat.succ_pos i
  have ht := hAt L hL (i + 1) hk
  obtain ⟨O, hOo, hsub, hon⟩ := ht.near
  have hBk := (hI L hL (i + 1) (i + 1) le_rfl).2.1
  have hB0 := (hI L hL (i + 1) 0 (Nat.zero_le _)).2.1
  have hpt : ∀ κ ∈ O, PointData L (i + 1) κ := fun κ hκ =>
    ⟨((hQ.2.1 _ _ hBk hB0).2.1 _ κ ht.resp_periodic
      (hon.resp_summable κ hκ)).carrierEntry_symbolHom, ht.resp_real.2⟩
  have heq : ∀ κ ∈ O, ∀ (m' : Fin 4 → ℤ) (ρ μ : Fin 4), stepEntry L i m' κ ρ μ =
      open Classical in
      ∑ m ∈ (freqBox L (i + 1)).filter (fun m => ∀ ν, (L : ℤ) ∣ m ν - m' ν),
        stepMean L i ρ (shiftedFreq κ m) * responseMode L (i + 1) κ ρ μ m := by
    intro κ hκ m' ρ μ
    unfold stepEntry
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [responseCoeff_eq_responseMode hT hI hL hk (hpt κ hκ)]
  obtain ⟨A, hA0, hA⟩ := exists_common_bound (S := imStrip (2 * δ₀))
    (Finset.univ ×ˢ freqBox L (i + 1))
    (u := fun (j : Fin 4 × (Fin 4 → ℤ)) κ => stepMean L i j.1 (shiftedFreq κ j.2))
    fun j _ => stepMean_bdd L i _ j.1 j.2
  obtain ⟨B, hB0', hB⟩ := exists_common_bound (S := imStrip (2 * δ₀))
    ((Finset.univ ×ˢ Finset.univ) ×ˢ freqBox L (i + 1))
    (u := fun (j : (Fin 4 × Fin 4) × (Fin 4 → ℤ)) κ => responseMode L (i + 1) κ j.1.1 j.1.2 j.2)
    fun j _ => (responseMode_bdd hI hL hon j.1.1 j.1.2 j.2).mono hsub
  have hAb : ∀ ρ, ∀ m ∈ freqBox L (i + 1), ∀ κ ∈ imStrip (2 * δ₀),
      ‖stepMean L i ρ (shiftedFreq κ m)‖ ≤ A := fun ρ m hm κ hκ =>
    hA (ρ, m) (Finset.mem_product.2 ⟨Finset.mem_univ _, hm⟩) κ hκ
  have hBb : ∀ ρ μ, ∀ m ∈ freqBox L (i + 1), ∀ κ ∈ imStrip (2 * δ₀),
      ‖responseMode L (i + 1) κ ρ μ m‖ ≤ B := fun ρ μ m hm κ hκ =>
    hB ((ρ, μ), m) (Finset.mem_product.2 ⟨Finset.mem_univ _, hm⟩) κ hκ
  refine ⟨fun m m' hc κ ρ μ => stepEntry_congr L i hc κ ρ μ, ⟨O, hOo, hsub, fun m' ρ μ => ?_⟩,
    ⟨(freqBox L (i + 1)).card * (A * B), fun m' ρ μ κ hκ => ?_⟩, ?_⟩
  · have hsum := isHolomorphicIn_scalar_sum (N := 4)
      (open Classical in (freqBox L (i + 1)).filter (fun m => ∀ ν, (L : ℤ) ∣ m ν - m' ν)) hOo
      (u := fun m κ => stepMean L i ρ (shiftedFreq κ m) * responseMode L (i + 1) κ ρ μ m)
      (fun m _ => isHolomorphicIn_scalar_mul (isHolomorphicIn_scalar_of_differentiable hOo
        ((stepMean_differentiable L i ρ).comp (shiftedFreq_differentiable m)))
        (responseMode_holomorphic hI hL hOo hon ρ μ m))
    exact isHolomorphicIn_scalar_congr hsum fun κ hκ => heq κ hκ m' ρ μ
  · rw [heq κ (hsub hκ)]
    refine norm_sum_le_card_mul (Finset.filter_subset _ _) _ (mul_nonneg hA0 hB0') fun m hm => ?_
    have hm' := Finset.mem_of_mem_filter m hm
    rw [norm_mul]
    exact mul_le_mul (hAb ρ m hm' κ hκ) (hBb ρ μ m hm' κ hκ) (norm_nonneg _) hA0
  · obtain ⟨C₀, N₀, hN₀, hz⟩ := hP.2.2.2 δ₀ hδ L hL (i + 1) hk
    obtain ⟨D, hD, hDn⟩ := stepMean_sub_one_le hL.1 i
    have hball : ∀ᶠ p in 𝓝 (0 : Fin 4 → ℂ), ‖p‖ < 1 := by
      have : Tendsto (fun p : Fin 4 → ℂ => ‖p‖) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_norm (E := Fin 4 → ℂ)).tendsto 0
      exact this.eventually (gt_mem_nhds one_pos)
    set M : ℝ := ((freqBox L (i + 1)).card : ℝ) with hM
    have hM0 : 0 ≤ M := Nat.cast_nonneg _
    set c₁ : ℝ := |C₀| with hc₁
    have hc₀ : 0 ≤ c₁ := abs_nonneg _
    set Q : ℝ := M * (A * c₁) with hQd
    have hQ0 : 0 ≤ Q := mul_nonneg hM0 (mul_nonneg hA0 hc₀)
    refine ⟨Q * 2 + D * B + c₁ + Q, _, (Filter.Eventually.and hN₀ (hball.and hDn)), ?_⟩
    rintro p ⟨hpN, hp1, hpD⟩ hps m' ρ μ
    have hpO := hsub hps
    have hpoint : InFundamentalStrip δ₀ p := by
      refine ⟨hps, fun ρ => ?_⟩
      have h₁ := (Complex.abs_re_le_norm (p ρ)).trans (norm_le_pi_norm p ρ)
      have h₂ := Real.pi_gt_three
      linarith
    obtain ⟨h₁, h₂, _⟩ := hz p hpN hpoint (basisEdgeVector L (i + 1) 0 μ)
    obtain ⟨hn₁, hn₂⟩ := responseMode_near_zero hT hI hL hk (hpt p hpO) ρ μ ⟨h₁, h₂⟩
    set v : ℝ := euclidNorm p with hv
    have hv0 : 0 ≤ v := euclidNorm_nonneg p
    have hv2 : v ≤ 2 := by
      have := euclidNorm_le_two_mul_norm p
      linarith
    have hterm : ∀ m ∈ freqBox L (i + 1), m ≠ 0 →
        ‖stepMean L i ρ (shiftedFreq p m) * responseMode L (i + 1) p ρ μ m‖ ≤
          A * (c₁ * v ^ 2) := by
      intro m hm hm0
      rw [norm_mul]
      refine mul_le_mul (hAb ρ m hm p hps) ?_ (norm_nonneg _) hA0
      exact (hn₁ m hm hm0).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg v))
    have hcard : M * (A * (c₁ * v ^ 2)) = Q * v ^ 2 := by
      rw [hQd]
      ring
    rw [heq p hpO]
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · refine (norm_sum_le_card_mul (s := freqBox L (i + 1)) (c := A * (c₁ * v ^ 2))
        (Finset.filter_subset _ _) _ (mul_nonneg hA0 (mul_nonneg hc₀ (sq_nonneg v)))
        fun m hm => hterm m (Finset.mem_of_mem_filter m hm) fun e => hc fun ν => ?_).trans ?_
      · have h₃ := (Finset.mem_filter.1 hm).2 ν
        rw [e] at h₃
        exact (dvd_sub_comm).1 h₃
      · rw [← hM, hcard]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg v)
        have := mul_nonneg hD hB0'
        linarith
    · classical
      have h0 : (0 : Fin 4 → ℤ) ∈ (freqBox L (i + 1)).filter
          (fun m => ∀ ν, (L : ℤ) ∣ m ν - m' ν) :=
        Finset.mem_filter.2 ⟨zero_mem_freqBox hL.1.pos _, fun ν => (dvd_sub_comm).1 (hc ν)⟩
      rw [← Finset.add_sum_erase _ _ h0]
      have hs0 : shiftedFreq p (0 : Fin 4 → ℤ) = p := by
        funext ν
        simp [PlaneWaves.shiftedFreq]
      rw [hs0]
      have h0f := zero_mem_freqBox hL.1.pos (i + 1)
      have hR := norm_sum_le_card_mul (s := freqBox L (i + 1))
        (t := ((freqBox L (i + 1)).filter (fun m => ∀ ν, (L : ℤ) ∣ m ν - m' ν)).erase 0)
        ((Finset.erase_subset _ _).trans (Finset.filter_subset _ _))
        (fun m => stepMean L i ρ (shiftedFreq p m) * responseMode L (i + 1) p ρ μ m)
        (c := A * (c₁ * v ^ 2)) (mul_nonneg hA0 (mul_nonneg hc₀ (sq_nonneg v)))
        (fun m hm => hterm m (Finset.mem_of_mem_filter m (Finset.mem_of_mem_erase hm))
          (Finset.ne_of_mem_erase hm))
      rw [← hM, hcard] at hR
      set R : ℂ := ∑ m ∈ ((freqBox L (i + 1)).filter
        (fun m => ∀ ν, (L : ℤ) ∣ m ν - m' ν)).erase 0,
          stepMean L i ρ (shiftedFreq p m) * responseMode L (i + 1) p ρ μ m with hRd
      set r₀ : ℂ := responseMode L (i + 1) p ρ μ 0 with hr₀d
      have hr₀ : ‖r₀‖ ≤ B := hBb ρ μ 0 h0f p hps
      have hu : ‖stepMean L i ρ p - 1‖ ≤ D * v := hpD ρ
      have hd : ‖r₀ - kroneckerEntry ρ μ‖ ≤ c₁ * v :=
        hn₂.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hv0)
      have e : stepMean L i ρ p * r₀ + R - kroneckerEntry ρ μ =
          (stepMean L i ρ p - 1) * r₀ + (r₀ - kroneckerEntry ρ μ) + R := by ring
      have hv3 : v ^ 2 ≤ 2 * v := by nlinarith
      have hQv : Q * v ^ 2 ≤ Q * (2 * v) := mul_le_mul_of_nonneg_left hv3 hQ0
      have hm₁ : ‖(stepMean L i ρ p - 1) * r₀‖ ≤ D * v * B := by
        rw [norm_mul]
        exact mul_le_mul hu hr₀ (norm_nonneg _) (mul_nonneg hD hv0)
      rw [e]
      calc ‖(stepMean L i ρ p - 1) * r₀ + (r₀ - kroneckerEntry ρ μ) + R‖
          ≤ ‖(stepMean L i ρ p - 1) * r₀‖ + ‖r₀ - kroneckerEntry ρ μ‖ + ‖R‖ := norm_add₃_le
        _ ≤ D * v * B + c₁ * v + Q * (2 * v) := by linarith
        _ = (Q * 2 + D * B + c₁) * v := by ring
        _ ≤ (Q * 2 + D * B + c₁ + Q) * v :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hQ0) hv0
end YangMills.Construction.Tower.StepEntryBounds
end
