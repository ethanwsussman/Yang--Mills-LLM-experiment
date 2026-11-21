import YangMills.Construction.Geometry.FourVectorBasics
import YangMills.Construction.LatticeForms.LatticeCoordinatesOfALevel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice.VectorClasses
open YangMills.Construction.PeriodicLattice.ShortDistanceTwoPoint
open YangMills.Construction.PeriodicLattice.DiscreteTorusData
abbrev TorusClasses (n : ℕ) : Type := IntegerTorus n
variable {n : ℕ}
theorem zmodClass_eq_zmodClass_iff (N N' : Fin 4 → ℤ) :
    zmodClass n N = zmodClass n N' ↔ ∃ w : Fin 4 → ℤ, N' = N + (n : ℤ) • w := by
  constructor
  · intro h
    have hd : ∀ μ, (n : ℤ) ∣ N' μ - N μ := fun μ =>
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (congrFun h μ)
    choose w hw using hd
    refine ⟨w, funext fun μ => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hw μ]
  · rintro ⟨w, rfl⟩
    funext μ
    simp [zmodClass]
def residueCube (n : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Ico 0 (n : ℤ)
theorem residueLift_mem_residueCube [NeZero n] (ξ : TorusClasses n) : residueLift ξ ∈ residueCube n := by
  refine Fintype.mem_piFinset.2 fun μ => Finset.mem_Ico.2 ⟨?_, ?_⟩
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_lt.2 (ZMod.val_lt (ξ μ))
theorem residueLift_zmodClass [NeZero n] {N : Fin 4 → ℤ} (hN : N ∈ residueCube n) :
    residueLift (zmodClass n N) = N := by
  funext μ
  have h := Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hN μ)
  simp only [residueLift, zmodClass, ZMod.val_intCast]
  exact Int.emod_eq_of_lt h.1 h.2
abbrev IsClassFunction (n : ℕ) (f : (Fin 4 → ℤ) → ℂ) : Prop := IsPeriodicModulo n f
def evalAtClass (f : (Fin 4 → ℤ) → ℂ) (ξ : TorusClasses n) : ℂ := f (residueLift ξ)
theorem evalAtClass_zmodClass [NeZero n] {f : (Fin 4 → ℤ) → ℂ} (hf : IsClassFunction n f)
    (N : Fin 4 → ℤ) : evalAtClass f (zmodClass n N) = f N := by
  obtain ⟨w, hw⟩ := (zmodClass_eq_zmodClass_iff (residueLift (zmodClass n N)) N).1 (zmodClass_residueLift _)
  have h := hf (residueLift (zmodClass n N)) w
  rw [← hw] at h
  exact h.symm
def classSum (n : ℕ) [NeZero n] (f : (Fin 4 → ℤ) → ℂ) : ℂ :=
  torusSum (evalAtClass (n := n) f)
theorem classSum_eq_sum_residueCube [NeZero n] (f : (Fin 4 → ℤ) → ℂ) :
    classSum n f = ∑ N ∈ residueCube n, f N :=
  Finset.sum_bij' (fun ξ _ => residueLift ξ) (fun N _ => zmodClass n N)
    (fun ξ _ => residueLift_mem_residueCube ξ) (fun _ _ => Finset.mem_univ _)
    (fun ξ _ => zmodClass_residueLift ξ) (fun _ hN => residueLift_zmodClass hN) (fun _ _ => rfl)
def greenOnVectors (n : ℕ) : (Fin 4 → ℤ) → ℂ := periodicExtension (latticeGreenFunction n)
theorem greenOnVectors_apply [NeZero n] (N : Fin 4 → ℤ) :
    greenOnVectors n N =
      (1 / (n : ℂ) ^ 4) * ∑ᶠ k ∈ momentumSet n \ {0}, expWave k N / (laplacianSymbol k : ℂ) := by
  simp only [greenOnVectors, periodicExtension, latticeGreenFunction]
  congr 1
  exact finsum_mem_congr rfl fun k hk => by rw [expWaveOnTorus_zmodClass hk.1]
theorem continuumGreenFunction_eq (u : Fin 4 → ℝ) :
    continuumGreenFunction u =
      1 / (4 * Real.pi ^ 2 * YangMills.Construction.FourVector.euclidNorm u ^ 2) := by
  rw [YangMills.Construction.FourVector.euclidNorm_eq_euclidNormVec]
  rfl
end YangMills.Construction.PeriodicLattice.VectorClasses
end
