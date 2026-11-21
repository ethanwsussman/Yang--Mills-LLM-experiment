import YangMills.Construction.Matrices.RestrictionsSumsAndCoordinatesOfRealAnalyticMapsProof
import YangMills.Construction.PeriodicOperators.SumsAndMultiplesOfJets
import Mathlib
set_option autoImplicit false
open Set Filter
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetAddSMul
open JetDomains
open JetQuad (IsJet)
section Coordinates
variable {n n' : ℕ} {V W W' : Set (Coordinates.ComplexCoordinates n)}
  {u v : Coordinates.ComplexCoordinates n → Coordinates.ComplexCoordinates n'}
private theorem isHolomorphicIn_mono (hV : IsOpen V) (hVW : V ⊆ W)
    (hu : Coordinates.ComplexCoordinates.IsHolomorphicIn W u) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn V u :=
  ⟨hV, hu.2.1.mono hVW, fun x hx i => hu.2.2 x (hVW hx) i⟩
private theorem isHolomorphicIn_add (hu : Coordinates.ComplexCoordinates.IsHolomorphicIn W u)
    (hv : Coordinates.ComplexCoordinates.IsHolomorphicIn W v) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn W fun z => u z + v z := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.Subspaces.LocalAnalyticity.isHolomorphicIn_add <;> assumption
private theorem isHolomorphicIn_const_smul (a : ℂ)
    (hu : Coordinates.ComplexCoordinates.IsHolomorphicIn W u) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn W fun z => a • u z := by
  refine ⟨hu.1, hu.2.1.const_smul a, fun x hx i => ?_⟩
  filter_upwards [hu.2.2 x hx i] with w hw₁
  exact hw₁.const_smul a
end Coordinates
variable {Q Q' : PeriodicData}
private theorem entriesHolomorphicOn_add {V E E' : Set (Fin 4 → ℂ)} {M M' : (Fin 4 → ℂ) → QuotHom Q Q'}
    (hV : IsOpen V) (hE : V ⊆ E) (hE' : V ⊆ E') (hM : EntriesHolomorphicOn E M)
    (hM' : EntriesHolomorphicOn E' M') : EntriesHolomorphicOn V (M + M') := fun k' k =>
  isHolomorphicIn_add (isHolomorphicIn_mono hV hE (hM k' k)) (isHolomorphicIn_mono hV hE' (hM' k' k))
private theorem entriesHolomorphicOn_smul (b : ℂ) {E : Set (Fin 4 → ℂ)} {M : (Fin 4 → ℂ) → QuotHom Q Q'}
    (hM : EntriesHolomorphicOn E M) : EntriesHolomorphicOn E (b • M) := fun k' k =>
  isHolomorphicIn_const_smul b (hM k' k)
private theorem isHolomorphicNbhd_add {E : Set (Fin 4 → ℂ)} {M M' : (Fin 4 → ℂ) → QuotHom Q Q'}
    (hM : IsHolomorphicNbhd E M) (hM' : IsHolomorphicNbhd E M') : IsHolomorphicNbhd E (M + M') := by
  obtain ⟨W, hW, hEW, hMW⟩ := hM
  obtain ⟨W', hW', hEW', hMW'⟩ := hM'
  exact ⟨W ∩ W', hW.inter hW', subset_inter hEW hEW',
    entriesHolomorphicOn_add (hW.inter hW') inter_subset_left inter_subset_right hMW hMW'⟩
private theorem isHolomorphicNbhd_smul (b : ℂ) {E : Set (Fin 4 → ℂ)} {M : (Fin 4 → ℂ) → QuotHom Q Q'}
    (hM : IsHolomorphicNbhd E M) : IsHolomorphicNbhd E (b • M) := by
  obtain ⟨W, hW, hEW, hMW⟩ := hM
  exact ⟨W, hW, hEW, entriesHolomorphicOn_smul b hMW⟩
private theorem isQuasiPeriodic_add {E : Set (Fin 4 → ℂ)} {M M' : (Fin 4 → ℂ) → QuotHom Q Q'}
    (hM : IsQuasiPeriodic E M) (hM' : IsQuasiPeriodic E M') : IsQuasiPeriodic E (M + M') := by
  intro t m hm
  simp only [Pi.add_apply, hM t m hm, hM' t m hm]
  ext g
  simp
private theorem isQuasiPeriodic_smul (b : ℂ) {E : Set (Fin 4 → ℂ)} {M : (Fin 4 → ℂ) → QuotHom Q Q'}
    (hM : IsQuasiPeriodic E M) : IsQuasiPeriodic E (b • M) := by
  intro t m hm
  simp only [Pi.smul_apply, hM t m hm]
  ext g
  simp
theorem claim_holds : Claim := by
  intro Q Q' _ _ w p _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B _ _ D D' hD hD' hA hB
    have k00 := hD.isOpen00.inter hD'.isOpen00
    have k10 := hD.isOpen10.inter hD'.isOpen10
    have k01 := hD.isOpen01.inter hD'.isOpen01
    have k11 := hD.isOpen11.inter hD'.isOpen11
    refine ⟨⟨D.dom00 ∩ D'.dom00, D.dom10 ∩ D'.dom10, D.dom01 ∩ D'.dom01, D.dom11 ∩ D'.dom11⟩,
      ⟨k00, k10, k01, k11, subset_inter hD.strip_subset hD'.strip_subset,
        subset_inter hD.addShift_subset hD'.addShift_subset,
        subset_inter hD.subShift_subset hD'.subShift_subset,
        subset_inter hD.real_subset hD'.real_subset⟩,
      ⟨Subset.rfl, Subset.rfl, Subset.rfl, Subset.rfl⟩,
      entriesHolomorphicOn_add k00 inter_subset_left inter_subset_right hA.1 hB.1,
      entriesHolomorphicOn_add k10 inter_subset_left inter_subset_right hA.2.1 hB.2.1,
      entriesHolomorphicOn_add k01 inter_subset_left inter_subset_right hA.2.2.1 hB.2.2.1,
      entriesHolomorphicOn_add k11 inter_subset_left inter_subset_right hA.2.2.2 hB.2.2.2⟩
  · intro A B hA hB
    exact ⟨hA.pos_width, hA.mem_imStrip, isHolomorphicNbhd_add hA.holo_f00 hB.holo_f00,
      isHolomorphicNbhd_add hA.holo_f10 hB.holo_f10,
      isHolomorphicNbhd_add hA.holo_f01 hB.holo_f01,
      isHolomorphicNbhd_add hA.holo_f11 hB.holo_f11,
      isQuasiPeriodic_add hA.quasiPeriodic_f00 hB.quasiPeriodic_f00,
      isQuasiPeriodic_add hA.quasiPeriodic_f10 hB.quasiPeriodic_f10,
      isQuasiPeriodic_add hA.quasiPeriodic_f01 hB.quasiPeriodic_f01,
      isQuasiPeriodic_add hA.quasiPeriodic_f11 hB.quasiPeriodic_f11⟩
  · intro b A _ D hD hA
    exact ⟨D, hD, ⟨Subset.rfl, Subset.rfl, Subset.rfl, Subset.rfl⟩, entriesHolomorphicOn_smul b hA.1,
      entriesHolomorphicOn_smul b hA.2.1, entriesHolomorphicOn_smul b hA.2.2.1,
      entriesHolomorphicOn_smul b hA.2.2.2⟩
  · intro b A hA
    exact ⟨hA.pos_width, hA.mem_imStrip, isHolomorphicNbhd_smul b hA.holo_f00,
      isHolomorphicNbhd_smul b hA.holo_f10, isHolomorphicNbhd_smul b hA.holo_f01,
      isHolomorphicNbhd_smul b hA.holo_f11, isQuasiPeriodic_smul b hA.quasiPeriodic_f00,
      isQuasiPeriodic_smul b hA.quasiPeriodic_f10, isQuasiPeriodic_smul b hA.quasiPeriodic_f01,
      isQuasiPeriodic_smul b hA.quasiPeriodic_f11⟩
end YangMills.Construction.PeriodicOperators.JetAddSMul
end
