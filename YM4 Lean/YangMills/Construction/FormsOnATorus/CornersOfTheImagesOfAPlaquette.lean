import YangMills.Construction.FormsOnATorus.MirrorsOfCells
import YangMills.Construction.HoleBesideASecondHole.CarriedSitesAndPaths
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusFields
variable {n : ℕ}
theorem cellReflection_mapPlaquette (c : ℕ) (u k : Fin 4 → ℤ) (x : TorusSite n) {μ ν : Fin 4} (h : μ < ν) :
    (cellReflection c u k).mapPlaquette (x, μ, ν) = ((cellReflection c u k).imageCorner x μ ν, μ, ν) := by
  unfold TorusIsometry.mapPlaquette
  exact if_pos h
theorem cellReflection_mapSite [NeZero n] (c : ℕ) (x : TorusSite n) (k : Fin 4 → ℤ) :
    (cellReflection c (integerCoords x) k).mapSite x = siteOfInt fun i => integerCoords x i + c * k i := by
  funext i
  have hx : x i = ((integerCoords x i : ℤ) : ZMod n) := by simp [integerCoords]
  simp only [TorusIsometry.mapSite, cellReflection, siteOfInt, Equiv.Perm.coe_one, id]
  rw [hx]
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id, integerCoords]
  ring
theorem reflectedPlaquette_vertex_near_centre [NeZero n] (c : ℕ) (x : TorusSite n) (μ ν : Fin 4) (hμν : μ < ν)
    (k : Fin 4 → ℤ) {z : TorusSite n}
    (hz : z ∈ plaquetteVertices ((cellReflection c (integerCoords x) k).mapPlaquette (x, μ, ν)).1
      ((cellReflection c (integerCoords x) k).mapPlaquette (x, μ, ν)).2.1
      ((cellReflection c (integerCoords x) k).mapPlaquette (x, μ, ν)).2.2) :
    ∃ d : Fin 4 → ℤ, (∀ i, |d i| ≤ 1) ∧ z = siteOfInt fun i => integerCoords x i + c * k i + d i := by
  set g := cellReflection c (integerCoords x) k with hg
  have hdir : ∀ i, g.imageAxis i = i := fun i => rfl
  have hsite : g.mapSite x = siteOfInt fun i => integerCoords x i + c * k i := cellReflection_mapSite c x k
  have hplaq : g.mapPlaquette (x, μ, ν) = (g.imageCorner x μ ν, μ, ν) := cellReflection_mapPlaquette c _ k x hμν
  rw [hplaq] at hz
  simp only at hz
  obtain ⟨a, ha, hbase⟩ : ∃ a : Fin 4 → ℤ, (a = 0 ∨ a = Pi.single μ (-1)) ∧
      g.mapSite x - (if g.axisSign (g.imageAxis μ) = 1 then 0 else unitStep n (g.imageAxis μ)) = g.mapSite x + siteOfInt a := by
    by_cases h : g.axisSign (g.imageAxis μ) = 1
    · exact ⟨0, Or.inl rfl, by rw [if_pos h]; funext i; simp [siteOfInt]⟩
    · refine ⟨Pi.single μ (-1), Or.inr rfl, ?_⟩
      rw [if_neg h, hdir, FrameTransfer.torusUnitStep_eq_siteOfInt, sub_eq_add_neg]
      congr 1
      funext i
      by_cases hi : i = μ
      · subst hi; simp [siteOfInt]
      · simp [siteOfInt, hi]
  obtain ⟨b, hb, hbase'⟩ : ∃ b : Fin 4 → ℤ, (b = 0 ∨ b = Pi.single ν (-1)) ∧
      g.imageCorner x μ ν = g.mapSite x + siteOfInt a + siteOfInt b := by
    by_cases h : g.axisSign (g.imageAxis ν) = 1
    · refine ⟨0, Or.inl rfl, ?_⟩
      unfold TorusIsometry.imageCorner
      rw [hbase, if_pos h]
      funext i
      simp [siteOfInt]
    · refine ⟨Pi.single ν (-1), Or.inr rfl, ?_⟩
      unfold TorusIsometry.imageCorner
      rw [hbase, if_neg h, hdir, FrameTransfer.torusUnitStep_eq_siteOfInt, sub_eq_add_neg]
      congr 1
      funext i
      by_cases hi : i = ν
      · subst hi; simp [siteOfInt]
      · simp [siteOfInt, hi]
  have hne : μ ≠ ν := hμν.ne
  have key : ∀ (e f : ℤ), (e = 0 ∨ e = 1) → (f = 0 ∨ f = 1) →
      z = g.imageCorner x μ ν + siteOfInt (Pi.single μ e) + siteOfInt (Pi.single ν f) →
      ∃ d : Fin 4 → ℤ, (∀ i, |d i| ≤ 1) ∧ z = siteOfInt fun i => integerCoords x i + c * k i + d i := by
    intro e f he hf hz'
    refine ⟨a + b + Pi.single μ e + Pi.single ν f, fun i => ?_, ?_⟩
    · by_cases h1 : i = μ
      · subst h1
        have hb0 : b i = 0 := by
          rcases hb with rfl | rfl
          · rfl
          · simp [Pi.single_eq_of_ne hne]
        have hf0 : (Pi.single ν f : Fin 4 → ℤ) i = 0 := Pi.single_eq_of_ne hne _
        simp only [Pi.add_apply, hb0, hf0, Pi.single_eq_same]
        rcases ha with rfl | rfl <;> rcases he with rfl | rfl <;> simp
      · by_cases h2 : i = ν
        · subst h2
          have ha0 : a i = 0 := by
            rcases ha with rfl | rfl
            · rfl
            · simp [Pi.single_eq_of_ne h1]
          have he0 : (Pi.single μ e : Fin 4 → ℤ) i = 0 := Pi.single_eq_of_ne h1 _
          simp only [Pi.add_apply, ha0, he0, Pi.single_eq_same]
          rcases hb with rfl | rfl <;> rcases hf with rfl | rfl <;> simp
        · have ha0 : a i = 0 := by
            rcases ha with rfl | rfl
            · rfl
            · simp [Pi.single_eq_of_ne h1]
          have hb0 : b i = 0 := by
            rcases hb with rfl | rfl
            · rfl
            · simp [Pi.single_eq_of_ne h2]
          simp [ha0, hb0, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
    · rw [hz', hbase', hsite]
      funext i
      simp only [siteOfInt, Pi.add_apply]
      push_cast
      ring
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
  have e0 : (siteOfInt (Pi.single μ (0 : ℤ)) : TorusSite n) = 0 := by funext i; simp [siteOfInt]
  have f0 : (siteOfInt (Pi.single ν (0 : ℤ)) : TorusSite n) = 0 := by funext i; simp [siteOfInt]
  rcases hz with rfl | rfl | rfl | rfl
  · exact key 0 0 (Or.inl rfl) (Or.inl rfl) (by rw [e0, f0]; simp)
  · exact key 1 0 (Or.inr rfl) (Or.inl rfl) (by rw [f0, FrameTransfer.torusUnitStep_eq_siteOfInt]; simp)
  · exact key 0 1 (Or.inl rfl) (Or.inr rfl) (by rw [e0, FrameTransfer.torusUnitStep_eq_siteOfInt]; simp)
  · exact key 1 1 (Or.inr rfl) (Or.inr rfl)
      (by rw [FrameTransfer.torusUnitStep_eq_siteOfInt, FrameTransfer.torusUnitStep_eq_siteOfInt])
end YangMills.Construction.TorusFields
end
