import YangMills.Construction.Towers.FormsOfTheFreeOperatorsInCoefficientsProof
import YangMills.Construction.Towers.CoefficientsOfTheResponseAtAColour
import YangMills.Construction.Towers.TheTrialFormOfTheResponseNearZeroProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ResponseCoefficients
open Tower
open Tower.ResponseProperties (responseSymbolForm)
open Tower.PlaneWaves (VertexClass edgeAt fourierCoeff edgeFourierCoeff edgeFieldOfClasses fourierPhase)
open Tower.PlaneWaveCalculus (posEdgeAt topEdgeComponent)
open Tower.BackgroundFieldResponse (responseKernel)
open PeriodicOperators
open Matrices.ComplexMatrix2 (pauliFamily traceless)
section Classes
variable {L k : ℕ}
theorem meshAt_self (L k : ℕ) : meshAt L k k = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.meshAt_self <;> assumption
theorem axisStep_injective {a : ℝ} (ha : a ≠ 0) {μ ρ : Fin 4}
    (h : InfiniteLattice.axisStep a μ = InfiniteLattice.axisStep a ρ) : μ = ρ := by apply _root_.YangMills.Construction.Tower.FacesContainingEdge.axisStep_injective <;> assumption
def basisClass (L k : ℕ) (a : Fin 3) (μ : Fin 4) : (colourEdges L k k).UnitQuot :=
  (colourEdges L k k).mkQuot 1 (a, posEdgeAt L k k 0 μ)
theorem basisClass_injective (hT : TowerTranslations.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {a a' : Fin 3} {μ μ' : Fin 4}
    (h : basisClass L k a μ = basisClass L k a' μ') : a = a' ∧ μ = μ' := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.unitEdgeClass_injective <;> assumption
theorem topEdgeComponent_apply (L k : ℕ) (z : (colourEdges L k k).UnitQuot → ℂ) (ρ : Fin 4) :
    topEdgeComponent L k z ρ = ∑ a, z (basisClass L k a ρ) • pauliFamily a := rfl
theorem topEdgeComponent_injective (hT : TowerTranslations.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    {z z' : (colourEdges L k k).UnitQuot → ℂ}
    (h : ∀ ρ, topEdgeComponent L k z ρ = topEdgeComponent L k z' ρ) : z = z' := by apply _root_.YangMills.Construction.Tower.TrialResponse.eq_of_topEdgeComponent <;> assumption
open Classical in
def basisVector (L k : ℕ) (a : Fin 3) (μ : Fin 4) : (colourEdges L k k).UnitQuot → ℂ :=
  Pi.single (basisClass L k a μ) 1
theorem topEdgeComponent_basisVector (hT : TowerTranslations.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (a : Fin 3) (μ ρ : Fin 4) :
    topEdgeComponent L k (basisVector L k a μ) ρ = if ρ = μ then pauliFamily a else 0 := by
  classical
  rw [topEdgeComponent_apply]
  by_cases h : ρ = μ
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single a]
    · simp [basisVector]
    · intro b _ hb
      have hne : basisClass L k b ρ ≠ basisClass L k a ρ := fun e =>
        hb (basisClass_injective hT hL hk e).1
      simp [basisVector, hne]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b _ => ?_
    have hne : basisClass L k b ρ ≠ basisClass L k a μ := fun e =>
      h (basisClass_injective hT hL hk e).2
    simp [basisVector, hne]
end Classes
section Colour
variable {L k : ℕ}
def responseColumn (L k : ℕ) (κ : Fin 4 → ℂ) (β : PosEdge L k 0) (μ : Fin 4) : ℂ :=
  responseSymbolForm L k κ (basisVector L k 0 μ) ((colourEdges L k 0).mkQuot 1 (0, β))
theorem fourierSymbol_colour_ne (hc : IsColourTrivial (responseKernel L k)) (κ : Fin 4 → ℂ)
    {a a' : Fin 3} (hne : a' ≠ a) (y : PosEdge L k 0) (x : PosEdge L k k) :
    fourierSymbol (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) κ (a', y) (a, x) =
      0 := by
  unfold fourierSymbol
  refine (tsum_congr fun n => ?_).trans tsum_zero
  show responseKernel L k (a', y) (a, shiftEdge n x) * _ = 0
  rw [hc.1 a a' y _ hne, zero_mul]
theorem fourierSymbol_colour_eq (hc : IsColourTrivial (responseKernel L k)) (κ : Fin 4 → ℂ)
    (a a' : Fin 3) (y : PosEdge L k 0) (x : PosEdge L k k) :
    fourierSymbol (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) κ (a, y) (a, x) =
      fourierSymbol (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) κ
        (a', y) (a', x) := by
  unfold fourierSymbol
  refine tsum_congr fun n => ?_
  show responseKernel L k (a, y) (a, shiftEdge n x) * _ =
    responseKernel L k (a', y) (a', shiftEdge n x) * _
  rw [hc.2 a a' y _]
  rfl
structure PointFacts (L k : ℕ) (κ : Fin 4 → ℂ) : Prop where
  entries : ∀ ι' ι, carrierEntry
    (symbolHom (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) κ) ι' ι =
      fourierSymbol (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) κ ι' ι
  colour : IsColourTrivial (responseKernel L k)
theorem responseSymbolForm_basisVector {κ : Fin 4 → ℂ} (h : PointFacts L k κ) (a a' : Fin 3)
    (μ : Fin 4) (β : PosEdge L k 0) :
    responseSymbolForm L k κ (basisVector L k a μ) ((colourEdges L k 0).mkQuot 1 (a', β)) =
      if a' = a then responseColumn L k κ β μ else 0 := by
  have e₁ : ∀ c c' : Fin 3, responseSymbolForm L k κ (basisVector L k c μ)
      ((colourEdges L k 0).mkQuot 1 (c', β)) =
      fourierSymbol (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) κ (c', β)
        (c, posEdgeAt L k k 0 μ) := fun c c' => h.entries _ _
  split_ifs with hc
  · subst hc
    rw [e₁, responseColumn, e₁, fourierSymbol_colour_eq h.colour κ a' 0]
  · rw [e₁, fourierSymbol_colour_ne h.colour κ hc]
theorem edgeFieldOfClasses_basisVector {κ : Fin 4 → ℂ} (h : PointFacts L k κ) (a : Fin 3)
    (μ : Fin 4) (β : PosEdge L k 0) :
    edgeFieldOfClasses L k (responseSymbolForm L k κ (basisVector L k a μ)) β =
      responseColumn L k κ β μ • pauliFamily a := by
  show ∑ b, responseSymbolForm L k κ (basisVector L k a μ)
    ((colourEdges L k 0).mkQuot 1 (b, β)) • pauliFamily b = _
  simp only [responseSymbolForm_basisVector h, ite_smul, zero_smul]
  simp
end Colour
section Number
variable {L k : ℕ}
theorem finite_vertexClass (hI : TowerIndexSets.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) : Finite (VertexClass L k) := by
  have : Finite (colourVertices L k 0).UnitQuot :=
    (hI L hL k 0 (Nat.zero_le k)).1.finite_quot
  let f : (colourVertices L k 0).UnitQuot → VertexClass L k :=
    Quot.lift (fun ι => Quot.mk _ ι.2) (by
      rintro ⟨a, x⟩ _ ⟨n, rfl⟩
      exact Quot.sound ⟨1 • n, rfl⟩)
  refine Finite.of_surjective f fun c => ?_
  induction c using Quot.ind with
  | mk x => exact ⟨(colourVertices L k 0).mkQuot 1 ((0 : Fin 3), x), rfl⟩
def colourNumber (L k : ℕ) (κ : Fin 4 → ℂ) (ρ μ : Fin 4) (m : Fin 4 → ℤ) : ℂ :=
  ((finestMesh L k ^ 4 : ℝ) : ℂ) * ∑ᶠ c : VertexClass L k,
    fourierPhase m (Quot.out c : FullSpace.Vertex L k 0) *
      responseColumn L k κ (edgeAt L k (Quot.out c) ρ) μ
theorem edgeFourierCoeff_basisVector (hI : TowerIndexSets.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {κ : Fin 4 → ℂ} (h : PointFacts L k κ)
    (a : Fin 3) (ρ μ : Fin 4) (m : Fin 4 → ℤ) :
    edgeFourierCoeff L k (responseSymbolForm L k κ (basisVector L k a μ)) ρ m =
      colourNumber L k κ ρ μ m • pauliFamily a := by
  have := finite_vertexClass (k := k) hI hL
  let _ := Fintype.ofFinite (VertexClass L k)
  unfold edgeFourierCoeff PlaneWaves.fourierCoeff colourNumber
  simp only [edgeFieldOfClasses_basisVector h, finsum_eq_sum_of_fintype, mul_smul,
    Finset.sum_smul]
end Number
theorem colourCoefficientClaim_holds (hR : ResponseOperators.Claim) (hQ : StripSymbols.Claim)
    (hT : TowerTranslations.Claim) (hI : TowerIndexSets.Claim) :
    ColourCoefficientClaim := by
  intro L hL k hk κ ρ μ m a z hformed hz
  obtain ⟨δ₀, _, hAt⟩ := hR
  have ht := hAt L hL k hk
  have hBk := (hI L hL k k le_rfl).2.1
  have hB0 := (hI L hL k 0 (Nat.zero_le k)).2.1
  have hpt : PointFacts L k κ :=
    ⟨((hQ.2.1 _ _ hBk hB0).2.1 _ κ ht.resp_periodic hformed).carrierEntry_symbolHom,
      ht.resp_real.2⟩
  have hex : ∃ c : ℂ, ∀ (a : Fin 3) (z : (colourEdges L k k).UnitQuot → ℂ),
      (∀ ν, topEdgeComponent L k z ν = if ν = μ then pauliFamily a else 0) →
        edgeFourierCoeff L k (responseSymbolForm L k κ z) ρ m = c • pauliFamily a := by
    refine ⟨colourNumber L k κ ρ μ m, fun a z hz => ?_⟩
    have e : z = basisVector L k a μ := topEdgeComponent_injective hT hL hk fun ν => by
      rw [hz, topEdgeComponent_basisVector hT hL hk]
    rw [e]
    exact edgeFourierCoeff_basisVector hI hL hpt a ρ μ m
  exact Classical.epsilon_spec hex a z hz
end YangMills.Construction.Tower.ResponseCoefficients
end
