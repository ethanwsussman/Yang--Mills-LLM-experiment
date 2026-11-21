import YangMills.Construction.ReflectionPositiveLimits.LAdicDataAreLatticeDataOfFineLattices
import YangMills.Construction.ReflectionPositivity.NestedLatticesAdicPointsAndMirrors
import YangMills.Construction.ReflectionPositivity.OneLatticeAtEverySpacing
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity
open YangMills.Construction.PeriodicLattice (adicGridPoints meshSize)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (MirrorPair)
namespace FineLatticeAdicData
theorem scaledLatticesMonotone {L : ℕ} (hL : 13 ≤ L) : ScaledLatticesMonotone L := by
  intro K₁ K₂ hle x hx
  obtain ⟨n, hn⟩ : ∃ n : Fin 4 → ℤ, ∀ μ, x μ = (n μ : ℝ) * meshSize L ((K₁ : ℕ) : ℤ) := hx
  have hL0 : (L : ℝ) ≠ 0 := by
    have h13 : (13 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (show (K₁ : ℕ) ≤ (K₂ : ℕ) from hle)
  refine ⟨fun μ => n μ * (L : ℤ) ^ e, fun μ => ?_⟩
  rw [hn μ]
  simp only [meshSize, he]
  push_cast
  rw [neg_add, zpow_add₀ hL0, zpow_neg (L : ℝ) (e : ℤ), zpow_natCast (L : ℝ) e]
  field_simp
theorem exists_int_mul_meshSize_of_mem {L : ℕ} {K : ℕ+ → ℕ+}
    (hK : AdicLattices.AdicPointsEventuallyOnLattice L K) {d : ℝ}
    (hd : d ∈ adicGridPoints L) :
    ∃ j₀ : ℕ+, ∀ j, j₀ ≤ j → ∃ m : ℤ, d = (m : ℝ) * meshSize L ((K j : ℕ) : ℤ) := by
  obtain ⟨j₀, hj⟩ := hK (fun _ => d) fun _ => hd
  refine ⟨j₀, fun j hle => ?_⟩
  obtain ⟨n, hn⟩ : ∃ n : Fin 4 → ℤ, ∀ μ, d = (n μ : ℝ) * meshSize L ((K j : ℕ) : ℤ) := hj j hle
  exact ⟨n 0, hn 0⟩
theorem reflectPt_eq_reflect {a : ℝ} (M : NormalMirror) (P : MirrorPair a)
    (hn : P.normal = M.normal) (hc : P.height = M.offset) : M.reflectPt = P.reflect.toFun := by
  funext x
  rw [LatticeAtSpacing.reflect_apply, NormalMirror.reflectPt, euclidNormVec_sq, hn, hc]
  have e : ∀ y : Space, euclidInner M.normal y = M.normal ⬝ᵥ y := fun _ => rfl
  rw [e, e]
  congr 2
  ring
theorem mirrorPairPreservesLattice : MirrorPairPreservesLattice :=
  fun _ _ P => P.reflect.image_eq
theorem adicMirrorEventuallyLatticeMirror {L : ℕ} {K : ℕ+ → ℕ+}
    (hK : AdicLattices.AdicPointsEventuallyOnLattice L K) :
    AdicMirrorEventuallyLatticeMirror L K := by
  have himage : ∀ (M : NormalMirror) (j : ℕ+), M.IsMirrorPlaneAt (meshSize L ((K j : ℕ) : ℤ)) →
      M.reflectPt '' (scaledLattice L (K j) : Set Space) = scaledLattice L (K j) := by
    rintro M j ⟨P, hn, hc⟩
    rw [reflectPt_eq_reflect M P hn hc]
    exact P.reflect.image_eq
  intro M hM
  rcases hM with ⟨⟨μ, hμ⟩, d, hd, hc⟩ | ⟨⟨μ, c, hne, hn⟩, hc⟩
  · obtain ⟨j₀, hj⟩ := exists_int_mul_meshSize_of_mem hK hd
    refine ⟨j₀, fun j hle => ?_⟩
    obtain ⟨m, hm⟩ := hj j hle
    have hplane : M.IsMirrorPlaneAt (meshSize L ((K j : ℕ) : ℤ)) :=
      ⟨⟨M.normal, M.offset, Or.inl ⟨⟨μ, hμ⟩, m, by rw [hc, hm]; ring⟩⟩, rfl, rfl⟩
    exact ⟨hplane, himage M j hplane⟩
  · obtain ⟨j₀, hj⟩ := exists_int_mul_meshSize_of_mem hK hc
    refine ⟨j₀, fun j hle => ?_⟩
    obtain ⟨m, hm⟩ := hj j hle
    have hplane : M.IsMirrorPlaneAt (meshSize L ((K j : ℕ) : ℤ)) :=
      ⟨⟨M.normal, M.offset, Or.inr ⟨⟨μ, c, hne, hn⟩, m, hm⟩⟩, rfl, rfl⟩
    exact ⟨hplane, himage M j hplane⟩
theorem adicDataLatticeData_of_assertion (hA : AdicLattices.Assertion) : AdicDataLatticeData := by
  intro L hL K hK
  obtain ⟨-, hUnion, ⟨hGroup, hDense, -, -⟩, hPoints, hTimes, -, -, -⟩ := hA L hL.2 K hK
  exact ⟨⟨hGroup, hDense, hUnion⟩, scaledLatticesMonotone hL.2, hPoints, hTimes,
    adicMirrorEventuallyLatticeMirror hPoints, mirrorPairPreservesLattice⟩
end FineLatticeAdicData
end YangMills.Construction.ReflectionPositivity
