import YangMills.Construction.Matrices.ConjugationInvariantForms
import YangMills.Construction.Towers.PropertiesOfTheBackgroundsProof
import YangMills.Construction.Towers.TheBackgroundFieldAmongTheTriples
import YangMills.Construction.Towers.TheResponseSymbolNearTheStrip
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.BackgroundTriple
open PeriodicOperators
open PeriodicOperators.LogDetSecondDerivs (descendField)
open BackgroundFieldResponse (responseKernel)
open ResponseSymbolNearStrip (IsTracelessTuple)
theorem waveAmplitude_blochWave (I : PeriodicData) (κ : Fin 4 → ℂ) (φ : I.UnitQuot → ℂ) :
    waveAmplitude I κ (blochWave I κ φ) = φ := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.waveAmplitude_blochWave <;> assumption
theorem blochWave_smul (I : PeriodicData) (κ : Fin 4 → ℂ) (c : ℂ) (φ : I.UnitQuot → ℂ) :
    blochWave I κ (c • φ) = c • blochWave I κ φ := by
  funext ι
  simp only [blochWave, Pi.smul_apply, smul_eq_mul]
  ring
theorem finestMesh_ne_zero {L k : ℕ} (hL : 0 < L) : ((finestMesh L k : ℝ) : ℂ) ≠ 0 := by
  have h : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.2 hL
  exact Complex.ofReal_ne_zero.2 (zpow_pos h _).ne'
theorem axisPauliElement_isTraceless (μ : Fin 4) : IsTracelessTuple (axisPauliElement μ 2) := by
  intro ρ
  unfold axisPauliElement
  by_cases h : ρ = μ
  · subst h
    simpa using Matrices.ConjugationInvariants.pauliFamily_mem_traceless 2
  · simp [Pi.single_eq_of_ne h]
theorem eq_smul_waveAmplitude_of_blochWave_eq {I : PeriodicData} {κ : Fin 4 → ℂ} {c : ℂ}
    (hc : c ≠ 0) {f : I.Carrier → ℂ} {a : I.UnitQuot → ℂ} (h : blochWave I κ a = c • f) :
    a = c • waveAmplitude I κ f := by
  have e : f = blochWave I κ (c⁻¹ • a) := by
    rw [blochWave_smul, h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [e, waveAmplitude_blochWave, smul_smul, mul_inv_cancel₀ hc, one_smul]
theorem backgroundIndex_isIndexEmbedding (L k : ℕ) (hL : 0 < L) :
    IsIndexEmbedding (backgroundIndex L k hL) where
  injective := fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.1 h).2
  map_translate := fun _ _ => rfl
  pos_map := fun _ => rfl
theorem not_exists_backgroundIndex_eq {L k : ℕ} {hL : 0 < L} {x : (fieldPeriodicData L k hL).Carrier}
    (hx : x.1 ≠ LocalKernels.FieldComponent.background) :
    ¬∃ ι, backgroundIndex L k hL ι = x := by
  rintro ⟨ι, rfl⟩
  exact hx rfl
theorem tripleIndexFunction_eq_extendByZero (L k : ℕ) (hL : 0 < L)
    (a : (colourEdges L k 0).UnitQuot → ℂ) :
    tripleIndexFunction L k hL a 0 0 =
      PeriodicOperators.extendByZero (backgroundIndex L k hL)
        fun ι => a ((remainderIndex L k).mkQuot 1 ι) := by
  funext x
  obtain ⟨place, ι⟩ := x
  unfold PeriodicOperators.extendByZero
  cases place with
  | background =>
    exact ((backgroundIndex_isIndexEmbedding L k hL).injective.extend_apply
      (fun ι => a ((remainderIndex L k).mkQuot 1 ι)) 0 ι).symm
  | source =>
    exact (Function.extend_apply' (fun ι => a ((remainderIndex L k).mkQuot 1 ι))
      (0 : (fieldPeriodicData L k hL).Carrier → ℂ) _
      (not_exists_backgroundIndex_eq (x := ⟨.source, ι⟩) fun h =>
      nomatch (show LocalKernels.FieldComponent.source = .background from h))).symm
  | coarse =>
    exact (Function.extend_apply' (fun ι => a ((remainderIndex L k).mkQuot 1 ι))
      (0 : (fieldPeriodicData L k hL).Carrier → ℂ) _
      (not_exists_backgroundIndex_eq (x := ⟨.coarse, ι⟩) fun h =>
      nomatch (show LocalKernels.FieldComponent.coarse = .background from h))).symm
theorem extendsByZero_of_responseSymbol
    (hS : ResponseSymbolNearStrip.ResponseSymbolHolomorphicNearStrip) : ExtendsByZero := by
  intro L hL hs k hk
  refine ⟨backgroundIndex_isIndexEmbedding L k hL, fun q hq μ => ?_⟩
  obtain ⟨δ₀, hδ, hN⟩ := hS
  obtain ⟨O, -, hO, hon⟩ := hN L hL hs k hk
  have e : stripHalfWidth = δ₀ :=
    Part.mem_unique (stripHalfWidth_mem (Part.dom_iff_mem.2 ⟨_, hδ⟩)) hδ
  have hqS : q ∈ imStrip (2 * δ₀) := by
    intro ν
    have h₁ : ‖q ν‖ ≤ δ₀ := e ▸ hq ν
    have h₂ : |(q ν).im| ≤ ‖q ν‖ := Complex.abs_im_le_norm _
    have h₃ : 0 ≤ δ₀ := (norm_nonneg _).trans h₁
    linarith
  have hwave := (hon.background_wave q (hO hqS) _ (axisPauliElement_isTraceless μ)).2
  have ha := eq_smul_waveAmplitude_of_blochWave_eq (finestMesh_ne_zero hL) hwave
  have hb : backgroundResponseSymbol L k q (axisPauliElement μ 2) = scaledResponseField L k q μ := ha
  rw [tripleAmplitude, tripleIndexFunction_eq_extendByZero, hb]
  rfl
end YangMills.Construction.Tower.FullSpace.BackgroundJets.BackgroundTriple
end
