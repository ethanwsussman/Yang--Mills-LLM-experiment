import YangMills.Construction.Towers.ChargedSymbolAtFluxZeroProof
import YangMills.Construction.Towers.CoefficientsOfASymbol
import YangMills.Construction.Towers.StarProductWithAConstantMatrix
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.OneLoopNotation
open YangMills.Construction.InfiniteLattice (AmbientSpace)
noncomputable section
namespace YangMills.Construction.Tower
open MagneticWeyl
private theorem fourierChar_zero_left (q : AmbientSpace) : fourierChar 0 q = 1 := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.FluxZero.fourierChar_zero <;> assumption
open MagneticWeyl
private theorem opNormValue_zero_matrix {N' N'' : ℕ} [NeZero N'] [NeZero N''] :
    Matrices.RectangularMatrix.opNormValue (0 : Matrix (Fin N') (Fin N'') ℂ) = 0 := by
  simp [Matrices.RectangularMatrix.opNormValue, OneLoopNotation.opNormOf]
private theorem fourierCoeff_const (h : FourierCoeffsOfSymbol) {N' N'' : ℕ} [NeZero N']
    [NeZero N''] (c : Matrix (Fin N') (Fin N'') ℂ) :
    fourierCoeff (fun _ : AmbientSpace => c) = Pi.single 0 c := by
  have hs : HasFourierExpansion (Pi.single 0 c : (Fin 4 → ℤ) → Matrix (Fin N') (Fin N'') ℂ)
      (fun _ : AmbientSpace => c) := fun q => by
    have hq := hasSum_single (f := fun n : Fin 4 → ℤ => fourierChar n q •
      (Pi.single 0 c : (Fin 4 → ℤ) → Matrix (Fin N') (Fin N'') ℂ) n) 0
      (fun n hn => by simp [Pi.single_eq_of_ne hn])
    simpa [fourierChar_zero_left] using hq
  have hsum : Summable fun n => Matrices.RectangularMatrix.opNormValue
      ((Pi.single 0 c : (Fin 4 → ℤ) → Matrix (Fin N') (Fin N'') ℂ) n) :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => by
      rw [Pi.single_eq_of_ne (by simpa using hn), opNormValue_zero_matrix]
  exact (((h N' N'' _).1 ⟨_, hs, hsum⟩).2.2 _ hs hsum).symm
private theorem symplecticForm_zero_right (n : Fin 4 → ℤ) : symplecticForm n 0 = 0 := by
  simp [symplecticForm]
private theorem symplecticForm_zero_left (n : Fin 4 → ℤ) : symplecticForm 0 n = 0 := by
  simp [symplecticForm]
private theorem moyalCoeff_const_right (h : FourierCoeffsOfSymbol) (φ : ℝ)
    {N' N'' M : ℕ} [NeZero N''] [NeZero M] (f : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ)
    (c : Matrix (Fin N'') (Fin M) ℂ) (n : Fin 4 → ℤ) :
    moyalCoeff φ f (fun _ => c) n = fourierCoeff f n * c := by
  rw [moyalCoeff, fourierCoeff_const h,
    tsum_eq_single (⟨(n, 0), add_zero n⟩ : {p : (Fin 4 → ℤ) × (Fin 4 → ℤ) // p.1 + p.2 = n})]
  · simp [symplecticForm_zero_right]
  · rintro ⟨⟨m, k⟩, hp⟩ hne
    have hk : k ≠ 0 := by
      rintro rfl
      apply hne
      have hm : m = n := by simpa using hp
      subst hm
      rfl
    simp [Pi.single_eq_of_ne hk]
private theorem moyalCoeff_const_left (h : FourierCoeffsOfSymbol) (φ : ℝ)
    {N' N'' M : ℕ} [NeZero N'] [NeZero M] (f : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ)
    (c : Matrix (Fin M) (Fin N') ℂ) (n : Fin 4 → ℤ) :
    moyalCoeff φ (fun _ => c) f n = c * fourierCoeff f n := by
  rw [moyalCoeff, fourierCoeff_const h,
    tsum_eq_single (⟨(0, n), zero_add n⟩ : {p : (Fin 4 → ℤ) × (Fin 4 → ℤ) // p.1 + p.2 = n})]
  · simp [symplecticForm_zero_left]
  · rintro ⟨⟨k, m⟩, hp⟩ hne
    have hk : k ≠ 0 := by
      rintro rfl
      apply hne
      have hm : m = n := by simpa using hp
      subst hm
      rfl
    simp [Pi.single_eq_of_ne hk]
theorem moyalProductWithConstant_holds (h : FourierCoeffsOfSymbol) :
    MoyalProductWithConstant := by
  intro φ N' N'' _ _ f hf M _
  have hsum : HasFourierExpansion (fourierCoeff f) f := ((h N' N'' f).1 ((h N' N'' f).2 hf).1).1
  refine ⟨fun c => funext fun q => ?_, fun c => funext fun q => ?_⟩
  · have hr : HasSum (fun n => fourierChar n q • (fourierCoeff f n * c)) (f q * c) := by
      have hmap := (hsum q).map
        ({ toFun := fun x => x * c, map_zero' := Matrix.zero_mul c,
           map_add' := fun x y => Matrix.add_mul x y c } :
          Matrix (Fin N') (Fin N'') ℂ →+ Matrix (Fin N') (Fin M) ℂ)
        (continuous_id.matrix_mul continuous_const)
      simpa [Function.comp_def, Matrix.smul_mul] using hmap
    simp only [moyalProduct, moyalCoeff_const_right h]
    exact hr.tsum_eq
  · have hl : HasSum (fun n => fourierChar n q • (c * fourierCoeff f n)) (c * f q) := by
      have hmap := (hsum q).map
        ({ toFun := fun x => c * x, map_zero' := Matrix.mul_zero c,
           map_add' := fun x y => Matrix.mul_add c x y } :
          Matrix (Fin N') (Fin N'') ℂ →+ Matrix (Fin M) (Fin N'') ℂ)
        (continuous_const.matrix_mul continuous_id)
      simpa [Function.comp_def, Matrix.mul_smul] using hmap
    simp only [moyalProduct, moyalCoeff_const_left h]
    exact hl.tsum_eq
end YangMills.Construction.Tower
end
