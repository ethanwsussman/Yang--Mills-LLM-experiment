import YangMills.Construction.PeriodicOperators.SecondDifferentialsOfLogarithmsOfDeterminantsProof
import YangMills.Construction.PeriodicOperators.TheSecondDifferentialOnATorusByTraces
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Coordinates.ComplexCoordinates.PowerSeriesHolomorphy (openPolydisk)
namespace PeriodicOperators.LogDetTraces
open LogDetSecondDerivs
theorem isOpen_openPolydisk_and_zero_mem {N : ℕ} {r : ℝ} (hr : 0 < r) :
    IsOpen (openPolydisk (0 : Coordinates.ComplexCoordinates N) r) ∧
      (0 : Coordinates.ComplexCoordinates N) ∈ openPolydisk (0 : Coordinates.ComplexCoordinates N) r := by apply _root_.YangMills.Construction.PeriodicOperators.LogDetSecondDerivs.isOpen_openPolydisk_and_zero_mem <;> assumption
theorem claim_holds (hLD : LogDetOfMaps.Claim)
    (hTM : TorusMatrixCoordinates.Claim)
    (hQT : Quotients.QuotientTransposeNorm) : Claim := by
  intro F I hF hI T ρ R hLoc s hs h4 hu N e ζ ζ'
  obtain ⟨hl1, hl2, hl3, hsym, hcoord⟩ := hTM F I hF hI T ρ R hLoc s hs h4
  obtain ⟨hHol, hExp, -⟩ := hcoord N e
  have : Finite (I.QuotMod s) := (hQT I I hI hI s hs).1.2.1
  obtain ⟨hO, h0⟩ := isOpen_openPolydisk_and_zero_mem (N := N) hLoc.radius_pos
  have main := hLD (I.QuotMod s) N (openPolydisk 0 ρ)
    (fun z => LogDetSecondDerivs.quotOperator F I T s (ofCoords e z))
    (fun k => periodicCoeffOneMatrix F I T s (ofCoords e k))
    (fun k h => periodicCoeffTwoMatrix F I T s (ofCoords e k) (ofCoords e h))
    hO h0 hHol hu
    ⟨fun x y => hl1.map_add _ _, fun c x => hl1.map_smul c _⟩
    (fun h => ⟨fun x y => (hl2 _).map_add _ _, fun c x => (hl2 _).map_smul c _⟩)
    (fun k => ⟨fun x y => (hl3 _).map_add _ _, fun c x => (hl3 _).map_smul c _⟩)
    (fun k h => hsym _ _) hExp
  have hf : ∀ ξ : F.QuotMod s → ℂ, ofCoords e (toCoords e ξ) = ξ := by
    intro ξ
    funext c
    simp [ofCoords, toCoords]
  have key := main.2 (toCoords e ζ) (toCoords e ζ')
  simp only [hf] at key
  exact key
end PeriodicOperators.LogDetTraces
end YangMills.Construction
end
