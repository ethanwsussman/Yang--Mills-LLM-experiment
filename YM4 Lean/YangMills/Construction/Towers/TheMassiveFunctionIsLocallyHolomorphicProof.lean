import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import YangMills.Construction.PeriodicOperators.MatricesOnATorusInCoordinatesProof
import YangMills.Construction.Towers.TheBackgroundNumbersNearZero
import YangMills.Construction.Towers.TheMassiveFunctionAsASumOfSymbols
import YangMills.Construction.Towers.TheMassiveFunctionIsLocallyHolomorphic
import YangMills.Construction.Towers.TheMassiveJetsProof
import YangMills.Construction.Towers.TheMassiveSymbolsAreHolomorphicInTheNumberAndTheMomentum
import Mathlib
set_option autoImplicit false
open Filter Set Topology
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.LocallyHolomorphic
open YangMills.Construction.Coordinates
open YangMills.Construction.Coordinates.ComplexCoordinates
open YangMills.Construction.PeriodicOperators (toComplexVec)
open YangMills.Construction.Tower.FullSpace.BackgroundJets
open YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv (IsHolomorphicScalarIn asLine)
theorem isHolomorphicScalarIn_iff {N : ℕ} {U : Set (ComplexCoordinates N)} {g : ComplexCoordinates N → ℂ} :
    IsHolomorphicScalarIn U g ↔ IsOpen U ∧ ContinuousOn g U ∧ ∀ a ∈ U, ∀ j : Fin N,
      ∀ᶠ ζ in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fun ζ : ℂ => g (a + ζ • stdBasisVector j)) ζ := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.isHolomorphicScalarIn_iff <;> assumption
theorem isHolomorphicScalarIn_const {N : ℕ} {U : Set (ComplexCoordinates N)} (hU : IsOpen U) (c : ℂ) :
    IsHolomorphicScalarIn U fun _ => c := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.holomorphicFnOn_const <;> assumption
theorem IsHolomorphicScalarIn.add' {N : ℕ} {U : Set (ComplexCoordinates N)} {f g : ComplexCoordinates N → ℂ}
    (hf : IsHolomorphicScalarIn U f) (hg : IsHolomorphicScalarIn U g) :
    IsHolomorphicScalarIn U fun x => f x + g x := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.HolomorphicFnOn.add <;> assumption
theorem IsHolomorphicScalarIn.mul' {N : ℕ} {U : Set (ComplexCoordinates N)} {f g : ComplexCoordinates N → ℂ}
    (hf : IsHolomorphicScalarIn U f) (hg : IsHolomorphicScalarIn U g) :
    IsHolomorphicScalarIn U fun x => f x * g x := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.HolomorphicFnOn.mul <;> assumption
theorem isHolomorphicScalarIn_finset_sum {N : ℕ} {ι : Type} {U : Set (ComplexCoordinates N)} (hU : IsOpen U)
    (s : Finset ι) {f : ι → ComplexCoordinates N → ℂ}
    (h : ∀ i ∈ s, IsHolomorphicScalarIn U (f i)) :
    IsHolomorphicScalarIn U fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isHolomorphicScalarIn_const hU 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact IsHolomorphicScalarIn.add' (h i (by simp)) (ih fun j hj => h j (by simp [hj]))
theorem IsHolomorphicScalarIn.comp_lineMap {M N : ℕ} {U : Set (ComplexCoordinates N)}
    {V : Set (ComplexCoordinates M)}
    {g : ComplexCoordinates N → ℂ} (hg : IsHolomorphicScalarIn U g) (hV : IsOpen V)
    {φ : ComplexCoordinates M → ComplexCoordinates N} (hφ : Continuous φ) (hmaps : MapsTo φ V U)
    (hline : ∀ (a : ComplexCoordinates M) (j : Fin M), ∃ (i : Fin N) (c : ℂ), ∀ ζ : ℂ,
      φ (a + ζ • stdBasisVector j) = φ a + (c * ζ) • stdBasisVector i) :
    IsHolomorphicScalarIn V fun x => g (φ x) := by
  rw [isHolomorphicScalarIn_iff] at hg ⊢
  refine ⟨hV, hg.2.1.comp hφ.continuousOn hmaps, fun a ha j => ?_⟩
  obtain ⟨i, c, h⟩ := hline a j
  have ht : Tendsto (fun ζ : ℂ => c * ζ) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun ζ : ℂ => c * ζ := by fun_prop
    simpa using hc.tendsto 0
  filter_upwards [ht.eventually (hg.2.2 (φ a) (hmaps ha) i)] with ζ hζ
  have hfun : (fun ζ : ℂ => g (φ (a + ζ • stdBasisVector j))) =
      (fun ξ : ℂ => g (φ a + ξ • stdBasisVector i)) ∘ fun ζ : ℂ => c * ζ := by
    funext ζ
    simp [h]
  rw [hfun]
  exact DifferentiableAt.comp ζ hζ (by fun_prop)
def momentumPart (x : ComplexCoordinates 5) : ComplexCoordinates 4 := fun μ => x μ.succ
def rescaledShiftedPoint (η : ℝ) (m : Fin 4 → ℤ) (x : ComplexCoordinates 5) : ComplexCoordinates 5 :=
  Fin.cons (α := fun _ => ℂ) ((η : ℂ) ^ 2 * x 0)
    fun μ => (η : ℂ) * PlaneWaves.shiftedFreq (momentumPart x) m μ
@[simp] theorem rescaledShiftedPoint_zero (η : ℝ) (m : Fin 4 → ℤ) (x : ComplexCoordinates 5) :
    rescaledShiftedPoint η m x 0 = (η : ℂ) ^ 2 * x 0 := rfl
@[simp] theorem rescaledShiftedPoint_succ (η : ℝ) (m : Fin 4 → ℤ) (x : ComplexCoordinates 5) (μ : Fin 4) :
    rescaledShiftedPoint η m x μ.succ = (η : ℂ) * PlaneWaves.shiftedFreq (momentumPart x) m μ := rfl
theorem continuous_momentumPart : Continuous momentumPart :=
  continuous_pi fun μ => continuous_apply μ.succ
theorem continuous_rescaledShiftedPoint (η : ℝ) (m : Fin 4 → ℤ) : Continuous (rescaledShiftedPoint η m) := by
  refine continuous_pi fun t => ?_
  refine Fin.cases ?_ (fun μ => ?_) t
  · simp only [rescaledShiftedPoint_zero]
    fun_prop
  · simp only [rescaledShiftedPoint_succ, PlaneWaves.shiftedFreq, momentumPart]
    fun_prop
theorem momentumPart_line (a : ComplexCoordinates 5) (j : Fin 5) :
    ∃ (i : Fin 4) (c : ℂ), ∀ ζ : ℂ,
      momentumPart (a + ζ • stdBasisVector j) = momentumPart a + (c * ζ) • stdBasisVector i := by
  refine Fin.cases ?_ (fun i => ?_) j
  · refine ⟨0, 0, fun ζ => ?_⟩
    funext μ
    simp [momentumPart, stdBasisVector, Fin.succ_ne_zero]
  · refine ⟨i, 1, fun ζ => ?_⟩
    funext μ
    simp [momentumPart, stdBasisVector, Pi.single_apply]
theorem neg_momentumPart_line (a : ComplexCoordinates 5) (j : Fin 5) :
    ∃ (i : Fin 4) (c : ℂ), ∀ ζ : ℂ,
      -momentumPart (a + ζ • stdBasisVector j) = -momentumPart a + (c * ζ) • stdBasisVector i := by
  obtain ⟨i, c, h⟩ := momentumPart_line a j
  refine ⟨i, -c, fun ζ => ?_⟩
  rw [h, neg_add, neg_mul, neg_smul]
theorem rescaledShiftedPoint_line (η : ℝ) (m : Fin 4 → ℤ) (a : ComplexCoordinates 5) (j : Fin 5) :
    ∃ (i : Fin 5) (c : ℂ), ∀ ζ : ℂ,
      rescaledShiftedPoint η m (a + ζ • stdBasisVector j) =
        rescaledShiftedPoint η m a + (c * ζ) • stdBasisVector i := by
  refine Fin.cases ?_ (fun i => ?_) j
  · refine ⟨0, (η : ℂ) ^ 2, fun ζ => ?_⟩
    funext t
    refine Fin.cases ?_ (fun μ => ?_) t
    · simp [stdBasisVector]
      ring
    · simp [PlaneWaves.shiftedFreq, momentumPart, stdBasisVector, Fin.succ_ne_zero]
  · refine ⟨i.succ, (η : ℂ), fun ζ => ?_⟩
    funext t
    refine Fin.cases ?_ (fun μ => ?_) t
    · simp [stdBasisVector, (Fin.succ_ne_zero i).symm]
    · by_cases hμ : μ = i
      · subst hμ
        simp [PlaneWaves.shiftedFreq, momentumPart, stdBasisVector]
        ring
      · simp [PlaneWaves.shiftedFreq, momentumPart, stdBasisVector, hμ]
theorem finestMesh_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) :
    0 < finestMesh L k := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.MassJets.finestMesh_pos <;> assumption
def symbolSumExtension (L k : ℕ) (F : (Fin 4 → ℤ) → Fin 4 → Fin 4 → ComplexCoordinates 5 → ℂ)
    (x : ComplexCoordinates 5) : ℂ :=
  (((finestMesh L k : ℝ) : ℂ) ^ 2)⁻¹ *
    ∑ m ∈ PlaneWaves.freqBox L k, ∑ ρ : Fin 4, ∑ σ : Fin 4,
      F m ρ σ (rescaledShiftedPoint (finestMesh L k) m x) *
        backgroundCoeff L k (momentumPart x) 0 ρ m *
        backgroundCoeff L k (-momentumPart x) 1 σ (-m)
theorem claim_of_symbolSum (hSum : SymbolExpansion.MassiveLogFnAsSymbolSum)
    (hSym : MassiveLogDet.SymbolHolomorphy)
    (hNear : BackgroundCoeffsNearZero.Claim) : MassiveOpFunctions.LocallyHolomorphic.Claim := by
  intro L hL k hk z₀ hz₀
  have hη : 0 < finestMesh L k := finestMesh_pos hL k
  obtain ⟨B, hBo, hB0, -, -, hBh, -⟩ := hNear L hL k hk
  have hsym := fun (m : Fin 4 → ℤ) (ρ σ : Fin 4) =>
    hSym L hL ρ σ (finestMesh L k ^ 2 * z₀) (by positivity)
      (fun μ => finestMesh L k * (2 * Real.pi * (m μ : ℝ)))
  choose Us hx F hF hFr using hsym
  have hUs : ∀ m ρ σ, IsOpen (Us m ρ σ) := fun m ρ σ => (isHolomorphicScalarIn_iff.1 (hF m ρ σ)).1
  let U : Set (ComplexCoordinates 5) :=
    (⋂ m ∈ PlaneWaves.freqBox L k, ⋂ ρ : Fin 4, ⋂ σ : Fin 4,
      rescaledShiftedPoint (finestMesh L k) m ⁻¹' Us m ρ σ) ∩
      (momentumPart ⁻¹' B ∩ (fun x => -momentumPart x) ⁻¹' B)
  have hU : IsOpen U := by
    refine IsOpen.inter ?_ (IsOpen.inter (hBo.preimage continuous_momentumPart)
      (hBo.preimage continuous_momentumPart.neg))
    exact isOpen_biInter_finset fun m _ => isOpen_iInter_of_finite fun ρ =>
      isOpen_iInter_of_finite fun σ => (hUs m ρ σ).preimage (continuous_rescaledShiftedPoint _ m)
  have hUsym : ∀ x ∈ U, ∀ m ∈ PlaneWaves.freqBox L k, ∀ ρ σ,
      rescaledShiftedPoint (finestMesh L k) m x ∈ Us m ρ σ := by
    intro x hx' m hm ρ σ
    have h := hx'.1
    simp only [mem_iInter, mem_preimage] at h
    exact h m hm ρ σ
  let x₀ : ComplexCoordinates 5 := Fin.cons (α := fun _ => ℂ) (z₀ : ℂ) fun _ => 0
  have hx₀0 : x₀ 0 = (z₀ : ℂ) := rfl
  have hx₀s : ∀ i : Fin 4, x₀ i.succ = 0 := fun _ => rfl
  have hx₀m : momentumPart x₀ = 0 := by
    funext μ
    exact hx₀s μ
  refine ⟨U, ⟨x₀, ?_, hx₀0, hx₀s⟩, symbolSumExtension L k F, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp only [mem_iInter, mem_preimage]
      intro m _ ρ σ
      obtain ⟨v, hv, hv0, hvs⟩ := hx m ρ σ
      have : rescaledShiftedPoint (finestMesh L k) m x₀ = v := by
        funext t
        refine Fin.cases ?_ (fun μ => ?_) t
        · simp [hv0, hx₀0]
        · simp [hvs, hx₀m, PlaneWaves.shiftedFreq, toComplexVec]
      rw [this]
      exact hv
    · simpa [mem_preimage, hx₀m] using hB0
    · simpa [mem_preimage, hx₀m] using hB0
  · refine IsHolomorphicScalarIn.mul' (isHolomorphicScalarIn_const hU _) ?_
    refine isHolomorphicScalarIn_finset_sum hU _ fun m hm => ?_
    refine isHolomorphicScalarIn_finset_sum hU _ fun ρ _ => ?_
    refine isHolomorphicScalarIn_finset_sum hU _ fun σ _ => ?_
    have hm' : -m ∈ PlaneWaves.freqBox L k := by
      rw [PlaneWaves.mem_freqBox] at hm ⊢
      intro ν
      simpa using hm ν
    refine IsHolomorphicScalarIn.mul' (IsHolomorphicScalarIn.mul' ?_ ?_) ?_
    · exact IsHolomorphicScalarIn.comp_lineMap (hF m ρ σ) hU (continuous_rescaledShiftedPoint _ m)
        (fun x hx' => hUsym x hx' m hm ρ σ) (rescaledShiftedPoint_line _ m)
    · exact IsHolomorphicScalarIn.comp_lineMap (hBh 0 ρ m hm) hU continuous_momentumPart
        (fun x hx' => hx'.2.1) momentumPart_line
    · exact IsHolomorphicScalarIn.comp_lineMap (hBh 1 σ (-m) hm') hU continuous_momentumPart.neg
        (fun x hx' => hx'.2.2) neg_momentumPart_line
  · intro x hxU hxR hxz hxδ
    let p : InfiniteLattice.AmbientSpace := fun μ => (x μ.succ).re
    have hp : toComplexVec p = momentumPart x := by
      funext μ
      exact Complex.ext (by simp [toComplexVec, p, momentumPart])
        (by simp [toComplexVec, momentumPart, hxR μ.succ])
    have hmem : toComplexVec p ∈ momentumPolydisc (massWidth (x 0).re) := by
      rw [hp]
      exact fun μ => (hxδ μ).le
    have hs := hSum L hL k hk (x 0).re hxz p hmem 0 1
    rw [hp] at hs
    change _ = massiveLogFn L k (momentumPart x) 0 1 (x 0).re
    rw [hs]
    unfold symbolSumExtension
    congr 1
    refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun ρ _ =>
      Finset.sum_congr rfl fun σ _ => ?_
    have hpt : rescaledShiftedPoint (finestMesh L k) m x ∈ realLocus 5 := by
      intro t
      refine Fin.cases ?_ (fun μ => ?_) t
      · simp [← Complex.ofReal_pow, hxR 0]
      · have := hxR μ.succ
        simp [PlaneWaves.shiftedFreq, momentumPart, this]
    have hre : (rescaledShiftedPoint (finestMesh L k) m x 0).re = finestMesh L k ^ 2 * (x 0).re := by
      simp [← Complex.ofReal_pow]
    have hv := hFr m ρ σ _ (hUsym x hxU m hm ρ σ) hpt (by rw [hre]; positivity)
    rw [hv, hre]
    rfl
end YangMills.Construction.Tower.MassiveOpFunctions.LocallyHolomorphic
end
