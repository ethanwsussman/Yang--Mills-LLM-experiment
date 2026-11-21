import YangMills.Construction.SummableBoundsOfTheFlow.MixturesOfTwoLevels
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.TwoLevelMixtures
def imagUnit : Fin 3 → imaginaryQuaternions :=
  ![⟨⟨0, 1, 0, 0⟩, rfl⟩, ⟨⟨0, 0, 1, 0⟩, rfl⟩, ⟨⟨0, 0, 0, 1⟩, rfl⟩]
def imagCoord (a : Fin 3) : imaginaryQuaternions →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => ![(u : ℍ[ℝ]).imI, (u : ℍ[ℝ]).imJ, (u : ℍ[ℝ]).imK] a
      map_add' := fun x y => by fin_cases a <;> rfl
      map_smul' := fun r x => by fin_cases a <;> rfl }
theorem sum_imagCoord_smul (u : imaginaryQuaternions) : ∑ a, imagCoord a u • imagUnit a = u := by
  have h0 : (u : ℍ[ℝ]).re = 0 := u.2
  have e0 : imagCoord 0 u = (u : ℍ[ℝ]).imI := rfl
  have e1 : imagCoord 1 u = (u : ℍ[ℝ]).imJ := rfl
  have e2 : imagCoord 2 u = (u : ℍ[ℝ]).imK := rfl
  rw [Fin.sum_univ_three, e0, e1, e2]
  apply Subtype.ext
  ext
  · show (u : ℍ[ℝ]).imI * 0 + (u : ℍ[ℝ]).imJ * 0 + (u : ℍ[ℝ]).imK * 0 = (u : ℍ[ℝ]).re
    rw [h0]; ring
  · show (u : ℍ[ℝ]).imI * 1 + (u : ℍ[ℝ]).imJ * 0 + (u : ℍ[ℝ]).imK * 0 = (u : ℍ[ℝ]).imI
    ring
  · show (u : ℍ[ℝ]).imI * 0 + (u : ℍ[ℝ]).imJ * 1 + (u : ℍ[ℝ]).imK * 0 = (u : ℍ[ℝ]).imJ
    ring
  · show (u : ℍ[ℝ]).imI * 0 + (u : ℍ[ℝ]).imJ * 0 + (u : ℍ[ℝ]).imK * 1 = (u : ℍ[ℝ]).imK
    ring
theorem imagCoord_imagUnit (a a' : Fin 3) : imagCoord a (imagUnit a') = if a = a' then 1 else 0 := by
  fin_cases a <;> fin_cases a' <;> simp [imagCoord, imagUnit]
theorem analyticAt_of_finite_restrictions {β E : Type} [Fintype β] [DecidableEq β] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (G : (β → imaginaryQuaternions) → E)
    (h : ∀ (k : ℕ) (c : Fin k → β) (X : Fin k → imaginaryQuaternions),
      AnalyticAt ℝ (fun σ : Fin k → ℝ => G fun b => ∑ l, if c l = b then σ l • X l else 0) 0) :
    AnalyticAt ℝ G 0 := by
  set e := (Fintype.equivFin (β × Fin 3)).symm with he
  set Λ : (β → imaginaryQuaternions) →L[ℝ] (Fin (Fintype.card (β × Fin 3)) → ℝ) :=
    ContinuousLinearMap.pi fun l => (imagCoord (e l).2).comp (ContinuousLinearMap.proj (e l).1) with hΛ
  have hkey : ∀ u : β → imaginaryQuaternions,
      (fun b => ∑ l, if (e l).1 = b then Λ u l • imagUnit (e l).2 else 0) = u := by
    intro u
    funext b
    have h1 : ∑ l, (if (e l).1 = b then Λ u l • imagUnit (e l).2 else 0) =
        ∑ q : β × Fin 3, if q.1 = b then imagCoord q.2 (u q.1) • imagUnit q.2 else 0 :=
      e.sum_comp fun q => if q.1 = b then imagCoord q.2 (u q.1) • imagUnit q.2 else 0
    rw [h1, Fintype.sum_prod_type, Finset.sum_eq_single b (fun x _ hx => by simp [hx]) (by simp)]
    simp only [if_true]
    exact sum_imagCoord_smul _
  have h1 := h _ (fun l => (e l).1) (fun l => imagUnit (e l).2)
  have h2 : G = (fun σ : Fin (Fintype.card (β × Fin 3)) → ℝ =>
      G fun b => ∑ l, if (e l).1 = b then σ l • imagUnit (e l).2 else 0) ∘ Λ := by
    funext u
    show G u = G _
    rw [hkey]
  rw [h2]
  refine AnalyticAt.comp ?_ (Λ.analyticAt _)
  rw [map_zero]
  exact h1
section
variable {n : ℕ}
def expField (v : TorusBond n → imaginaryQuaternions) : TorusField n := fun x i => expUnit (v (x, i))
def interpEnergyLog [NeZero n] (a : ℝ) (L t : ℕ) (θ : ℝ) [NeZero L]
    (p : (TorusBond (n * L) → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions)) : ℝ :=
  interpChartEnergy a L t θ p.1 (expField p.2)
end
def InterpEnergyAnalytic : Prop :=
  EventuallyOrdered fun T => ∀ [NeZero T.L], ∀ (t n : ℕ) [NeZero n] (θ : ℝ), 64 ≤ n →
    AnalyticAt ℝ (interpEnergyLog (n := n) T.a T.L t θ) 0
end YangMills.Construction.TwoLevelMixtures
end
