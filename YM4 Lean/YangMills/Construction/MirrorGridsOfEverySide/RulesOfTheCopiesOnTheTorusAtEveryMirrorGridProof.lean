import YangMills.Construction.ChessboardTori.MirrorPeriodicWeightsAsCellFunctionsProof
import YangMills.Construction.MirrorGridsOfEverySide.ActionOnTheCellAlgebrasOfTheTorusAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.GroupOnTheCellsOfTheTorusAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.RulesOfTheCopiesOnTheTorusAtEveryMirrorGrid
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open ChessboardTori (ReflectionGrid)
namespace MirrorGridsAllSides
namespace TransportLaws
variable {D : GridSetup} {g : ReflectionGrid D}
theorem signedConj_signedConj_mul (σ τ : ℤˣ) (z : ℂ) :
    Conventions.signedConj σ (Conventions.signedConj τ z) = Conventions.signedConj (σ * τ) z := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionPeriodicWeightsAsCellFunctions.signedConj_signedConj <;> assumption
theorem signedConj_add (σ : ℤˣ) (z w : ℂ) :
    Conventions.signedConj σ (z + w) = Conventions.signedConj σ z + Conventions.signedConj σ w := by
  rcases Int.units_eq_one_or σ with rfl | rfl <;> simp [Conventions.signedConj]
theorem signedConj_mul (σ : ℤˣ) (z w : ℂ) :
    Conventions.signedConj σ (z * w) = Conventions.signedConj σ z * Conventions.signedConj σ w := by
  rcases Int.units_eq_one_or σ with rfl | rfl <;> simp [Conventions.signedConj]
theorem signedConj_starRingEnd (σ : ℤˣ) (z : ℂ) :
    Conventions.signedConj σ (starRingEnd ℂ z) = starRingEnd ℂ (Conventions.signedConj σ z) := by
  rcases Int.units_eq_one_or σ with rfl | rfl <;> simp [Conventions.signedConj]
theorem inducedTorusMaps_isGroup (hG : TorusGroupActsOnCells g) :
    id ∈ g.inducedTorusMaps ∧
      (∀ r ∈ g.inducedTorusMaps, ∀ s ∈ g.inducedTorusMaps, r ∘ s ∈ g.inducedTorusMaps) ∧
      ∀ r ∈ g.inducedTorusMaps, ∃ s ∈ g.inducedTorusMaps, s ∘ r = id ∧ r ∘ s = id := by
  obtain ⟨H, hH⟩ := hG.2.2.1
  have mem : ∀ e ∈ H, (e : D.Torus → D.Torus) ∈ g.inducedTorusMaps := fun e he => by
    rw [← hH]
    exact ⟨e, he, rfl⟩
  have ex : ∀ r ∈ g.inducedTorusMaps, ∃ e ∈ H, (e : D.Torus → D.Torus) = r := by
    intro r hr
    rw [← hH] at hr
    obtain ⟨e, he, rfl⟩ := hr
    exact ⟨e, he, rfl⟩
  refine ⟨mem 1 H.one_mem, ?_, ?_⟩
  · intro r hr s hs
    obtain ⟨e, he, rfl⟩ := ex r hr
    obtain ⟨f, hf, rfl⟩ := ex s hs
    exact mem (e * f) (H.mul_mem he hf)
  · intro r hr
    obtain ⟨e, he, rfl⟩ := ex r hr
    refine ⟨_, mem e⁻¹ (H.inv_mem he), ?_, ?_⟩
    · funext x
      simp
    · funext x
      simp
theorem eq_of_image_cell_eq (hG : TorusGroupActsOnCells g) {C : Set D.Torus}
    (hC : C ∈ g.torusCellSet) {r s : D.Torus → D.Torus} (hr : r ∈ g.inducedTorusMaps)
    (hs : s ∈ g.inducedTorusMaps) (h : r '' C = s '' C) : r = s := by
  obtain ⟨hid, hmul, hinv⟩ := inducedTorusMaps_isGroup hG
  obtain ⟨t, ht, hts, hst⟩ := hinv s hs
  have himg : (t ∘ r) '' C = C := by
    rw [image_comp, h, ← image_comp, hts, image_id]
  have hone : t ∘ r = id :=
    (hG.2.2.2.2.2.1 C hC C hC).unique ⟨hmul t ht r hr, himg⟩ ⟨hid, image_id C⟩
  calc r = (s ∘ t) ∘ r := by rw [hst]; rfl
    _ = s ∘ (t ∘ r) := rfl
    _ = s := by rw [hone]; rfl
theorem torusCarrier_eq_of_image (hG : TorusGroupActsOnCells g) {C C' : Set D.Torus}
    (hC : C ∈ g.torusCellSet) {r : D.Torus → D.Torus} (hr : r ∈ g.inducedTorusMaps)
    (h : r '' C = C') : g.torusCarrier C C' = r := by
  have hs := Classical.epsilon_spec (p := fun s : D.Torus → D.Torus =>
    s ∈ g.inducedTorusMaps ∧ s '' C = C') ⟨r, hr, h⟩
  exact eq_of_image_cell_eq hG hC hs.1 hr (hs.2.trans h.symm)
theorem torusCarrier_mem_and_image (hG : TorusGroupActsOnCells g) {C C' : Set D.Torus}
    (hC : C ∈ g.torusCellSet) (hC' : C' ∈ g.torusCellSet) :
    g.torusCarrier C C' ∈ g.inducedTorusMaps ∧ g.torusCarrier C C' '' C = C' :=
  Classical.epsilon_spec (p := fun s : D.Torus → D.Torus =>
    s ∈ g.inducedTorusMaps ∧ s '' C = C') (hG.2.2.2.2.2.1 C hC C' hC').exists
theorem torusTransport_comp (hG : TorusGroupActsOnCells g)
    (hA : TorusActsOnCellObservables g) {r s : D.Torus → D.Torus}
    (hr : r ∈ g.inducedTorusMaps) (hs : s ∈ g.inducedTorusMaps)
    (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    EqOn (g.torusTransport s (g.torusTransport r F)) (g.torusTransport (s ∘ r) F) D.torusFields := by
  intro U hU
  have h := hA.1 s hs r hr F hU
  have hsgn := hG.2.2.2.2.1 s hs r hr
  change Conventions.signedConj (g.torusSign s) (Conventions.signedConj (g.torusSign r)
      (D.pullbackObservable s (D.pullbackObservable r F) U)) =
    Conventions.signedConj (g.torusSign (s ∘ r)) (D.pullbackObservable (s ∘ r) F U)
  rw [signedConj_signedConj_mul, hsgn, h]
theorem torusTransport_id (hG : TorusGroupActsOnCells g)
    (hA : TorusActsOnCellObservables g) {C : Set D.Torus} (hC : C ∈ g.torusCellSet)
    {F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ} (hF : F ∈ g.torusCellObservables C) :
    EqOn (g.torusTransport id F) F D.torusFields := by
  obtain ⟨hid, -, -⟩ := inducedTorusMaps_isGroup hG
  have hsgn : g.torusSign id = 1 := by
    have h := hG.2.2.2.2.1 id hid id hid
    rw [Function.id_comp] at h
    exact left_eq_mul.mp h
  have hsurj := (hA.2 id hid C hC).1
  rw [image_id] at hsurj
  rw [← hsurj] at hF
  obtain ⟨F₀, -, rfl⟩ := hF
  intro U hU
  have h := hA.1 id hid id hid F₀ hU
  rw [Function.id_comp] at h
  change Conventions.signedConj (g.torusSign id)
      (D.pullbackObservable id (D.pullbackObservable id F₀) U) =
    D.pullbackObservable id F₀ U
  rw [hsgn, ← h]
  simp [Conventions.signedConj]
theorem signedConjFun_mem {C : Set D.Torus} (σ : ℤˣ)
    {F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ} (hF : F ∈ g.torusCellObservables C) :
    Conventions.signedConjFun σ F ∈ g.torusCellObservables C := by
  obtain ⟨f, hf, ⟨c, hc⟩, hU⟩ := hF
  rcases Int.units_eq_one_or σ with rfl | rfl
  · refine ⟨f, hf, ⟨c, hc⟩, fun U => ?_⟩
    simp [Conventions.signedConjFun, Conventions.signedConj, hU]
  · refine ⟨fun u => starRingEnd ℂ (f u), Complex.continuous_conj.measurable.comp hf,
      ⟨c, fun u => by simpa using hc u⟩, fun U => ?_⟩
    simp [Conventions.signedConjFun, Conventions.signedConj, hU]
theorem torusTransportTo_trans (hG : TorusGroupActsOnCells g)
    (hA : TorusActsOnCellObservables g) {C C' C'' : Set D.Torus}
    (hC : C ∈ g.torusCellSet) (hC' : C' ∈ g.torusCellSet) (hC'' : C'' ∈ g.torusCellSet)
    (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    EqOn (g.torusTransportTo C' C'' (g.torusTransportTo C C' F)) (g.torusTransportTo C C'' F)
      D.torusFields := by
  obtain ⟨-, hmul, -⟩ := inducedTorusMaps_isGroup hG
  obtain ⟨hr, hri⟩ := torusCarrier_mem_and_image hG hC hC'
  obtain ⟨hs, hsi⟩ := torusCarrier_mem_and_image hG hC' hC''
  have hcar : g.torusCarrier C C'' = g.torusCarrier C' C'' ∘ g.torusCarrier C C' :=
    torusCarrier_eq_of_image hG hC (hmul _ hs _ hr) (by rw [image_comp, hri, hsi])
  simp only [ChessboardTori.ReflectionGrid.torusTransportTo]
  rw [hcar]
  exact torusTransport_comp hG hA hr hs F
theorem transportLaws_of_group_of_action (hG : TorusGroupActsOnCells g)
    (hA : TorusActsOnCellObservables g) : TorusTransportLaws g := by
  obtain ⟨hid, hmul, -⟩ := inducedTorusMaps_isGroup hG
  intro C hC C' hC' C'' hC'' F hF
  obtain ⟨hr, hri⟩ := torusCarrier_mem_and_image hG hC hC'
  refine ⟨?_, ?_, torusTransportTo_trans hG hA hC hC' hC'' F, ?_, ?_, ?_, ?_, ?_⟩
  · have hT : D.pullbackObservable (g.torusCarrier C C') F ∈
        g.torusCellObservables (g.torusCarrier C C' '' C) := by
      rw [← (hA.2 _ hr C hC).1]
      exact ⟨F, hF, rfl⟩
    rw [hri] at hT
    exact signedConjFun_mem _ hT
  · have hcar : g.torusCarrier C C = id := torusCarrier_eq_of_image hG hC hid (image_id C)
    simp only [ChessboardTori.ReflectionGrid.torusTransportTo]
    rw [hcar]
    exact torusTransport_id hG hA hC hF
  · intro r' hr'
    have hcar : g.torusCarrier C (r' '' C') = r' ∘ g.torusCarrier C C' :=
      torusCarrier_eq_of_image hG hC (hmul _ hr' _ hr) (by rw [image_comp, hri])
    intro U hU
    have h := torusTransport_comp hG hA hr hr' F hU
    simp only [ChessboardTori.ReflectionGrid.torusTransportTo]
    rw [hcar]
    exact h.symm
  · intro F' _
    constructor
    · intro U _
      simp only [ChessboardTori.ReflectionGrid.torusTransportTo,
        ChessboardTori.ReflectionGrid.torusTransport]
      simp [Conventions.signedConjFun, ChessboardTori.ChessboardSetup.pullbackObservable,
        signedConj_add]
    · intro U _
      simp only [ChessboardTori.ReflectionGrid.torusTransportTo,
        ChessboardTori.ReflectionGrid.torusTransport]
      simp [Conventions.signedConjFun, ChessboardTori.ChessboardSetup.pullbackObservable,
        signedConj_mul]
  · intro U _
    simp only [ChessboardTori.ReflectionGrid.torusTransportTo,
      ChessboardTori.ReflectionGrid.torusTransport]
    simp [Conventions.signedConjFun, ChessboardTori.ChessboardSetup.pullbackObservable, conjFun,
      signedConj_starRingEnd]
  · intro r' hr' c U _
    have hcar : g.torusCarrier C (r' '' C) = r' := torusCarrier_eq_of_image hG hC hr' rfl
    simp only [ChessboardTori.ReflectionGrid.torusTransportTo,
      ChessboardTori.ReflectionGrid.torusTransport]
    rw [hcar]
    simp [Conventions.signedConjFun, ChessboardTori.ChessboardSetup.pullbackObservable,
      signedConj_mul]
  · intro U hU
    simp only [ChessboardTori.ReflectionGrid.cellProduct]
    exact finprod_mem_congr rfl fun C₁ hC₁ =>
      torusTransportTo_trans hG hA hC hC' hC₁ F hU
end TransportLaws
theorem torusTransportLawsEveryGrid_of_group_of_action
    (h₁ : AllGridsTorusGroupActsOnCells)
    (h₂ : AllGridsTorusActOnCellObservables) :
    TorusTransportLawsEveryGrid := by
  intro D g hg hℓ
  exact TransportLaws.transportLaws_of_group_of_action (h₁ D g hg hℓ) (h₂ D g hg hℓ)
end MirrorGridsAllSides
end YangMills.Construction
end
