import YangMills.Construction.ClusterExpansionOfAStep.MirrorOfABox
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorAgreesOnItsBox
import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace ReflectionOnBox
theorem reflectCoord_eq (m : ℕ) (c : ℤ) : reflectCoord m c =
    if -(m : ℤ) ≤ c ∧ c ≤ m then c else if 0 < c then 2 * (m : ℤ) - c else -(2 * (m : ℤ)) - c := by apply _root_.YangMills.Construction.TorusMirror.triangleFold_eq_ite <;> assumption
theorem period_reflectedFrame (m : ℕ) (l : Fin 4) :
    (reflectedFrame F m).period (reflectedFrame F m).top l = 4 * m := by
  simp [BlockFrame.period, reflectedFrame]
theorem mem_finiteCells (hs : ∀ i, 0 < F.extent i) (z : F.Cell) : z ∈ finiteCells F := by apply _root_.YangMills.Construction.FrameTorusAction.mem_finiteCells <;> assumption
theorem valMinAbs_intCast {m : ℕ} (hm : 0 < m) (u : ℤ) (l : Fin 4) (h1 : -(2 * (m : ℤ)) < u) (h2 : u ≤ 2 * m) :
    ((u : ZMod ((reflectedFrame F m).period (reflectedFrame F m).top l))).valMinAbs = u := by
  have hN := period_reflectedFrame (F := F) m l
  have : NeZero ((reflectedFrame F m).period (reflectedFrame F m).top l) := ⟨by rw [hN]; omega⟩
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  rw [hN]
  simp only [Set.mem_Ioc]
  push_cast
  omega
end ReflectionOnBox
open ReflectionOnBox in
theorem reflectedFieldAgreesOnBox : ReflectedFieldAgreesOnBox := by
  intro F m y V hm hs
  have hm0 : 0 < m := by omega
  refine ⟨fun i => Or.inr (hs i), fun i => Or.inr ?_, fun h _ => ?_, fun b hb => ?_⟩
  · change 2 * m + 2 < 4 * m
    omega
  · have h1 : ∀ z : F.Cell, z ∈ finiteCells F := mem_finiteCells fun i => by
      have := hs i
      omega
    have h2 : ∀ z : (reflectedFrame F m).Cell, z ∈ finiteCells (reflectedFrame F m) := mem_finiteCells fun i => by
      change 0 < 4 * m
      omega
    exact ⟨fun _ => h2 _, fun _ => h1 _⟩
  · obtain ⟨z, hz⟩ : ∃ z : (reflectedFrame F m).Cell, z = 0 + siteOfCoords (reflectedFrame F m).top b.1 := ⟨_, rfl⟩
    rw [← hz]
    have hv : ∀ l, (z l).valMinAbs = b.1 l := by
      intro l
      have a := abs_le.mp (hb.1 l)
      rw [hz, zero_add]
      exact valMinAbs_intCast hm0 (b.1 l) l (by omega) (by omega)
    have hfix : ∀ c : ℤ, -(m : ℤ) ≤ c → c ≤ m → reflectCoord m c = c := by
      intro c h1 h2
      rw [reflectCoord_eq, if_pos ⟨h1, h2⟩]
    have e1 : (fun l => reflectCoord m (z l).valMinAbs) = b.1 := by
      funext l
      have a := abs_le.mp (hb.1 l)
      rw [hv, hfix _ a.1 a.2]
    have e2 : ∀ l, reflectCoord m ((z l).valMinAbs + (Pi.single b.2 1 : Fin 4 → ℤ) l) =
        b.1 l + (Pi.single b.2 1 : Fin 4 → ℤ) l := by
      intro l
      have a := abs_le.mp (hb.2 l)
      rw [hv]
      simp only [Pi.add_apply] at a
      rw [hfix _ a.1 a.2]
    simp only [reflectedField]
    rw [if_pos]
    · rw [e1]
    · rw [e2, congrFun e1 b.2]
      simp
end ColdStepAtMirrorFrames
end YangMills.Construction
end
