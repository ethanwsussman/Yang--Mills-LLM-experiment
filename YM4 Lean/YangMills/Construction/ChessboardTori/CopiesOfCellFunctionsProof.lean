import YangMills.Construction.ChessboardTori.ChessboardSeminormsOnATorusProof
import YangMills.Construction.ChessboardTori.CopiesOfCellFunctions
import YangMills.Construction.ChessboardTori.GroupCoordinateByCoordinate
import YangMills.Construction.ChessboardTori.GroupOfAGridAndCopiesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace CellFunctionCopies
theorem signedConj_add (σ : ℤˣ) (z w : ℂ) :
    Conventions.signedConj σ (z + w) = Conventions.signedConj σ z + Conventions.signedConj σ w := by apply _root_.YangMills.Construction.MirrorGridsAllSides.TransportLaws.signedConj_add <;> assumption
theorem signedConj_mul (σ : ℤˣ) (z w : ℂ) :
    Conventions.signedConj σ (z * w) = Conventions.signedConj σ z * Conventions.signedConj σ w := by apply _root_.YangMills.Construction.MirrorGridsAllSides.TransportLaws.signedConj_mul <;> assumption
theorem signedConj_starRingEnd (σ : ℤˣ) (z : ℂ) :
    Conventions.signedConj σ (starRingEnd ℂ z) = starRingEnd ℂ (Conventions.signedConj σ z) := by apply _root_.YangMills.Construction.MirrorGridsAllSides.TransportLaws.signedConj_starRingEnd <;> assumption
theorem signedConj_one (σ : ℤˣ) : Conventions.signedConj σ 1 = 1 := by apply _root_.YangMills.Construction.ChessboardTori.TorusChessboardSeminorms.signedConj_one <;> assumption
theorem signedConj_signedConj (σ τ : ℤˣ) (z : ℂ) :
    Conventions.signedConj σ (Conventions.signedConj τ z) = Conventions.signedConj (σ * τ) z := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionPeriodicWeightsAsCellFunctions.signedConj_signedConj <;> assumption
variable {D : ChessboardSetup} (g : ReflectionGrid D)
theorem continuous_of_isProductOfCoordMaps {f : AmbientSpace → AmbientSpace}
    (hf : g.IsProductOfCoordMaps f) : Continuous f := by
  refine continuous_pi fun ν => ?_
  rcases hf ν with ⟨t, ht⟩ | ⟨k, hk⟩
  · have e : (fun y : AmbientSpace => f y ν) =
        fun y => (y ν - g.origin ν) + 2 * t * g.cellSide + g.origin ν := by
      funext y
      have := ht y
      simp only [ReflectionGrid.coordShift] at this
      linarith
    rw [e]
    fun_prop
  · have e : (fun y : AmbientSpace => f y ν) =
        fun y => 2 * k * g.cellSide - (y ν - g.origin ν) + g.origin ν := by
      funext y
      have := hk y
      simp only [ReflectionGrid.coordReflect] at this
      linarith
    rw [e]
    fun_prop
variable {g}
theorem image_interior_eq (hG : g.ReflectionGroupCoordForm) (ρ : g.reflectionGroup)
    (A : Set AmbientSpace) :
    (ρ.1 : AmbientSpace → AmbientSpace) '' interior A =
      interior ((ρ.1 : AmbientSpace → AmbientSpace) '' A) := by
  let e : AmbientSpace ≃ₜ AmbientSpace :=
    { toEquiv := ρ.1
      continuous_toFun := continuous_of_isProductOfCoordMaps g (hG.1 ρ.1 ρ.2)
      continuous_invFun := continuous_of_isProductOfCoordMaps g (hG.1 _ (inv_mem ρ.2)) }
  exact e.image_interior A
theorem linkMap_mem (hG : g.ReflectionGroupCoordForm) (ρ : g.reflectionGroup)
    {A B : Set AmbientSpace} (hAB : (ρ.1 : AmbientSpace → AmbientSpace) '' A = B)
    {e : D.Link} (he : e ∈ ReflectionGrid.interiorLinks (D := D) A) :
    (g.toLatticeSym ρ).linkMap e ∈ ReflectionGrid.interiorLinks (D := D) B := by
  have him : (ρ.1 : AmbientSpace → AmbientSpace) '' interior A = interior B := by
    rw [← hAB]
    exact image_interior_eq hG ρ A
  constructor
  · change (ρ.1 : AmbientSpace → AmbientSpace) (e.initial : AmbientSpace) ∈ interior B
    rw [← him]
    exact mem_image_of_mem _ he.1
  · change (ρ.1 : AmbientSpace → AmbientSpace) (e.terminal : AmbientSpace) ∈ interior B
    rw [← him]
    exact mem_image_of_mem _ he.2
theorem mover_eq (hG : g.ReflectionGroupCoordForm) {A B : Set AmbientSpace}
    (hA : A ∈ g.cellSet) (hB : B ∈ g.cellSet) (ρ : g.reflectionGroup)
    (hρ : (ρ.1 : AmbientSpace → AmbientSpace) '' A = B) :
    g.mover A B = ρ := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionGroupAndTransport.mover_eq <;> assumption
theorem orientationSign_one (hG : g.ReflectionGroupCoordForm) :
    orientationSign ((1 : Equiv.Perm AmbientSpace) : AmbientSpace → AmbientSpace) = 1 := by
  have h := hG.2.2.2.1 1 g.reflectionGroup.one_mem 1 g.reflectionGroup.one_mem
  rw [mul_one] at h
  rcases Int.units_eq_one_or
      (orientationSign ((1 : Equiv.Perm AmbientSpace) : AmbientSpace → AmbientSpace)) with e | e
  · exact e
  · rw [e] at h
    simp at h
theorem pullbackField_one (U : D.GaugeField) :
    (g.toLatticeSym 1).pullbackField U = U := by
  apply Subtype.ext
  funext e
  change U.1 ((g.toLatticeSym 1).linkMap e) = U.1 e
  congr 1
theorem pullbackField_mul (σ ρ : g.reflectionGroup) (U : D.GaugeField) :
    (g.toLatticeSym (σ * ρ)).pullbackField U =
      (g.toLatticeSym ρ).pullbackField ((g.toLatticeSym σ).pullbackField U) := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionGroupAndTransport.pullbackField_toLatticeSym_mul <;> assumption
theorem transport_apply (ρ : g.reflectionGroup) (F : D.GaugeField → ℂ) (U : D.GaugeField) :
    g.transport ρ F U =
      Conventions.signedConj (orientationSign ρ.1) (F ((g.toLatticeSym ρ).pullbackField U)) :=
  rfl
theorem transport_mem (hG : g.ReflectionGroupCoordForm) (ρ : g.reflectionGroup)
    {A B : Set AmbientSpace} (hAB : (ρ.1 : AmbientSpace → AmbientSpace) '' A = B)
    {F : D.GaugeField → ℂ} (hF : F ∈ ReflectionGrid.cellObservables (D := D) A) :
    g.transport ρ F ∈ ReflectionGrid.cellObservables (D := D) B := by
  obtain ⟨φ, hφ, ⟨C, hC⟩, rfl⟩ := hF
  let relabel : (ReflectionGrid.interiorLinks (D := D) B → Conventions.StandingParameters.gaugeGroup) →
      (ReflectionGrid.interiorLinks (D := D) A → Conventions.StandingParameters.gaugeGroup) :=
    fun u e => u ⟨(g.toLatticeSym ρ).linkMap e.1, linkMap_mem hG ρ hAB e.2⟩
  have hrelabel : Measurable relabel :=
    measurable_pi_lambda _ fun e => measurable_pi_apply _
  refine ⟨fun u => Conventions.signedConj (orientationSign ρ.1) (φ (relabel u)), ?_,
    ⟨C, fun u => ?_⟩, ?_⟩
  · have hφr : Measurable fun u => φ (relabel u) := hφ.comp hrelabel
    by_cases hs : orientationSign ρ.1 = 1
    · simpa [Conventions.signedConj, hs] using hφr
    · simp only [Conventions.signedConj, if_neg hs]
      exact Complex.continuous_conj.measurable.comp hφr
  · have := hC (relabel u)
    by_cases hs : orientationSign ρ.1 = 1
    · simpa [Conventions.signedConj, hs] using this
    · simpa [Conventions.signedConj, if_neg hs] using this
  · rfl
theorem statement_holds (h : ReflectionGroupCoordinates.Statement) :
    CellFunctionCopies.Statement := by
  intro D g A hA B hB C hC ρ hρ F hF F' _ c
  have hG : g.ReflectionGroupCoordForm := h D g
  have hm : g.mover A B = ρ := mover_eq hG hA hB ρ hρ
  have hone : g.mover A A = 1 := mover_eq hG hA hA 1 (by simp)
  obtain ⟨σ, hσ⟩ := (hG.2.2.2.2.2.2.1 B hB C hC).exists
  have hm' : g.mover B C = σ := mover_eq hG hB hC σ hσ
  have hm'' : g.mover A C = σ * ρ :=
    mover_eq hG hA hC (σ * ρ) (by
      change ((σ.1 * ρ.1 : Equiv.Perm AmbientSpace) : AmbientSpace → AmbientSpace) '' A = C
      rw [Equiv.Perm.coe_mul, image_comp, hρ, hσ])
  simp only [ReflectionGrid.transportTo, hm, hone, hm', hm'']
  refine ⟨transport_mem hG ρ hρ hF, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext U
    rw [transport_apply, pullbackField_one]
    change Conventions.signedConj
      (orientationSign ((1 : Equiv.Perm AmbientSpace) : AmbientSpace → AmbientSpace)) (F U) = F U
    rw [orientationSign_one hG]
    simp [Conventions.signedConj]
  · funext U
    simp only [transport_apply]
    rw [signedConj_signedConj, pullbackField_mul, ← hG.2.2.2.1 σ.1 σ.2 ρ.1 ρ.2]
    rfl
  · funext U
    simp only [transport_apply, signedConj_starRingEnd]
  · funext U
    simp only [transport_apply, Pi.mul_apply, signedConj_mul]
  · funext U
    simp only [transport_apply, Pi.add_apply, signedConj_add]
  · funext U
    simp only [transport_apply, signedConj_mul]
  · funext U
    simp only [transport_apply, Pi.one_apply, signedConj_one]
end CellFunctionCopies
end YangMills.Construction.ChessboardTori
end
