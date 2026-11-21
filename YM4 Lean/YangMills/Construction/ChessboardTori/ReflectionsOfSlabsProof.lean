import YangMills.Construction.ChessboardTori.ReflectionsOfSlabs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori.SlabReflections
theorem inducesMap_unique {D : ChessboardSetup} (P : PeriodSubgroup D) {r : D.LatticeSym}
    {θ θ' : P.TorusSpace → P.TorusSpace} (h : P.InducesMap r θ) (h' : P.InducesMap r θ') :
    θ = θ' := by
  funext u
  obtain ⟨x, rfl⟩ := BoxTorus.projection_surjective P.sideLengths u
  exact (congrFun h x).symm.trans (congrFun h' x)
theorem proof (h : SlabSymmetries.Statement) : Statement := by
  intro D T _ m hm k θ hθ
  obtain ⟨hInd, -, -, -, -, -, hPoint, -, hFun, hW⟩ := h D T m hm (k : ZMod (m : ℕ))
  have e : θ = T.slabFlip m (k : ZMod (m : ℕ)) := inducesMap_unique _ hθ (hInd k rfl)
  subst e
  have hk : ((k + 1 : ℤ) : ZMod (m : ℕ)) = (k : ZMod (m : ℕ)) + 1 := by push_cast; rfl
  rw [hk]
  refine ⟨hPoint, fun Φ hΦ => (hFun Φ hΦ).1, ?_⟩
  have hw := (hW (fun _ => 0) ⟨0, fun _ => by simp⟩).2 (fun _ _ => by simp)
  rw [T.slabBoltzmann_zero, T.slabBoltzmann_zero] at hw
  exact hw.symm
end YangMills.Construction.ChessboardTori.SlabReflections
end
