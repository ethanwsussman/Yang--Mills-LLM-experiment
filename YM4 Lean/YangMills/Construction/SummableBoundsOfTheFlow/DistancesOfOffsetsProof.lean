import YangMills.Construction.SummableBoundsOfTheFlow.DistancesOfOffsets
import YangMills.Construction.SummableBoundsOfTheFlow.SitesOfACellAreFewProofForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace Estimates
namespace CellOffsets
variable {F : BlockFrame}
theorem period_top (i : Fin 4) : F.period F.top i = F.extent i := by simp [BlockFrame.period]
theorem valMinAbs_intCast_of_bounds {n : ℕ} [NeZero n] (a : ℤ) (h₁ : -(n : ℤ) < a * 2) (h₂ : a * 2 ≤ n) :
    ((a : ZMod n)).valMinAbs = a :=
  (ZMod.valMinAbs_spec _ _).2 ⟨rfl, h₁, h₂⟩
theorem enclosingCell_centre_add (hodd : Odd F.blockSide) (z : F.Cell) (v : Fin 4 → ℤ)
    (hv : v ∈ centredCube F.blockSide) :
    enclosingCell (cellCentre F.depth z + siteOfCoords F.depth v : F.Site F.depth) = z := by apply _root_.YangMills.Construction.CellCounting.enclosingCell_cellCentre_add <;> assumption
end CellOffsets
open CellOffsets in
theorem cellOffsetStatement_holds : cellOffsetStatement := by
  intro F hodd hext
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Y h o k ho
    exact enclosingCell_centre_add hodd _ o ho
  · intro Y z
    funext l
    have hne : (F.period F.top l) ≠ 0 := by rw [period_top]; have := hext l; omega
    have : NeZero (F.period F.top l) := ⟨hne⟩
    simp [siteOfCoords, Estimates.cellOffset]
  · intro Y z i
    unfold Estimates.cellOffset cellSupDist
    exact Finset.le_sup (f := fun i => ((z i - Y i).valMinAbs).natAbs) (Finset.mem_univ i)
  · intro q hq Y a b ha hb
    have key : ∀ (c : Fin 4 → ℤ) (l : Fin 4), 2 * |c l| ≤ (2 * q + 2 : ℕ) →
        (((c l : ℤ) : ZMod (F.period F.top l))).valMinAbs = c l := by
      intro c l hc
      have hne : (F.period F.top l) ≠ 0 := by rw [period_top]; have := hext l; omega
      have : NeZero (F.period F.top l) := ⟨hne⟩
      have hper' : ((F.period F.top l : ℕ) : ℤ) = (F.extent l : ℤ) := by rw [period_top]
      have hlt : ((2 * q + 2 : ℕ) : ℤ) < (F.extent l : ℤ) := by exact_mod_cast hq l
      have h₁ := abs_le.1 (le_refl |c l|)
      refine valMinAbs_intCast_of_bounds _ ?_ ?_
      · rw [hper']; linarith [h₁.1]
      · rw [hper']; linarith [h₁.2]
    constructor
    · funext l
      have e : (Y + siteOfCoords F.top a - Y : F.Cell) l = ((a l : ℤ) : ZMod (F.period F.top l)) := by
        simp [siteOfCoords]
      unfold Estimates.cellOffset
      rw [e]
      refine key a l ?_
      have := ha l
      push_cast
      linarith
    · unfold cellSupDist
      refine congrArg (fun f : Fin 4 → ℕ => Finset.univ.sup f) ?_
      funext l
      have e : (Y + siteOfCoords F.top a : F.Cell) l - (Y + siteOfCoords F.top b : F.Cell) l =
          (((a - b) l : ℤ) : ZMod (F.period F.top l)) := by
        simp [siteOfCoords]
      rw [e, key (a - b) l ?_]
      · rfl
      · have h₁ := ha l
        have h₂ := hb l
        simp only [Pi.sub_apply]
        have h₃ : |a l - b l| ≤ |a l| + |b l| := abs_sub _ _
        push_cast
        linarith
end Estimates
end YangMills.Construction
end
