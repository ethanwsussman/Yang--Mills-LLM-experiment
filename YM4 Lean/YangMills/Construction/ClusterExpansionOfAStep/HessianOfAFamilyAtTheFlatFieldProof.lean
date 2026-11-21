import YangMills.Construction.ClusterExpansionOfAStep.HessianOfAFamilyAtTheFlatField
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction.FlatHessian
open BlockAverages TorusFields TorusLumps
variable {n : ℕ}
private def imagJ : imaginaryQuaternions := ⟨⟨0, 0, 1, 0⟩, rfl⟩
private def imagK : imaginaryQuaternions := ⟨⟨0, 0, 0, 1⟩, rfl⟩
private theorem imag_decomp (X : imaginaryQuaternions) :
    X = ((X : ℍ[ℝ]).imI) • quaternionI + ((X : ℍ[ℝ]).imJ) • imagJ + ((X : ℍ[ℝ]).imK) • imagK := by
  apply Subtype.ext
  have hre : (X : ℍ[ℝ]).re = 0 := X.2
  ext
  · show (X : ℍ[ℝ]).re = (X : ℍ[ℝ]).imI * 0 + (X : ℍ[ℝ]).imJ * 0 + (X : ℍ[ℝ]).imK * 0
    simp [hre]
  · show (X : ℍ[ℝ]).imI = (X : ℍ[ℝ]).imI * 1 + (X : ℍ[ℝ]).imJ * 0 + (X : ℍ[ℝ]).imK * 0
    simp
  · show (X : ℍ[ℝ]).imJ = (X : ℍ[ℝ]).imI * 0 + (X : ℍ[ℝ]).imJ * 1 + (X : ℍ[ℝ]).imK * 0
    simp
  · show (X : ℍ[ℝ]).imK = (X : ℍ[ℝ]).imI * 0 + (X : ℍ[ℝ]).imJ * 0 + (X : ℍ[ℝ]).imK * 1
    simp
private def secondDeriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → ℝ) (u v : E) : ℝ :=
  fderiv ℝ (fderiv ℝ Φ) 0 u v
private theorem secondDeriv_comp {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (Φ : F → ℝ) (L : E →L[ℝ] F) (hΦ : ContDiffAt ℝ 3 Φ 0) (u v : E) :
    secondDeriv (fun s => Φ (L s)) u v = secondDeriv Φ (L u) (L v) := by
  have hev : ∀ᶠ z in 𝓝 (0 : F), DifferentiableAt ℝ Φ z :=
    (hΦ.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
  have hL0 : Tendsto L (𝓝 0) (𝓝 0) := by
    simpa using L.continuous.tendsto 0
  have hev' : ∀ᶠ s in 𝓝 (0 : E), DifferentiableAt ℝ Φ (L s) := hL0.eventually hev
  have h1 : fderiv ℝ (fun s => Φ (L s)) =ᶠ[𝓝 0] fun s => (fderiv ℝ Φ (L s)).comp L := by
    refine hev'.mono fun s hs => ?_
    have := (hs.hasFDerivAt.comp s L.hasFDerivAt).fderiv
    simpa [Function.comp_def] using this
  have hd : DifferentiableAt ℝ (fderiv ℝ Φ) 0 :=
    (hΦ.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hd' : HasFDerivAt (fun s => fderiv ℝ Φ (L s)) ((fderiv ℝ (fderiv ℝ Φ) 0).comp L) (0 : E) := by
    have h2 : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) 0) (L 0) := by
      simpa using hd.hasFDerivAt
    exact h2.comp (0 : E) L.hasFDerivAt
  have h3 := (hd'.clm_comp (hasFDerivAt_const L (0 : E))).fderiv
  simp only [secondDeriv]
  rw [h1.fderiv_eq, h3]
  simp
private theorem secondDeriv_symm {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → ℝ)
    (hΦ : ContDiffAt ℝ 3 Φ 0) (u v : E) : secondDeriv Φ u v = secondDeriv Φ v u := by
  have : IsSymmSndFDerivAt ℝ Φ 0 := hΦ.isSymmSndFDerivAt (by simp; norm_num)
  exact this.eq u v
private theorem mixedDeriv_eq_fderiv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : TorusField n → E)
    (W : TorusField n) (c : Fin 2 → TorusBond n) (X : Fin 2 → imaginaryQuaternions) :
    mixedDeriv G W c X = fderiv ℝ (fderiv ℝ fun s : Fin 2 → ℝ => G (perturb c X s W)) 0 (Pi.single 0 1) (Pi.single 1 1) := by
  simp only [mixedDeriv, iteratedFDeriv_two_apply]
private theorem smul_decomp (s : ℝ) (X : imaginaryQuaternions) :
    s • X = (s * (X : ℍ[ℝ]).imI) • quaternionI + (s * (X : ℍ[ℝ]).imJ) • imagJ + (s * (X : ℍ[ℝ]).imK) • imagK := by
  conv_lhs => rw [imag_decomp X]
  simp only [smul_add, smul_smul]
private def bondsSix (b b' : TorusBond n) : Fin 6 → TorusBond n := ![b, b, b, b', b', b']
private def basisSix : Fin 6 → imaginaryQuaternions := ![quaternionI, imagJ, imagK, quaternionI, imagJ, imagK]
private def leftCoords (X : imaginaryQuaternions) : Fin 6 → ℝ := ![(X : ℍ[ℝ]).imI, (X : ℍ[ℝ]).imJ, (X : ℍ[ℝ]).imK, 0, 0, 0]
private def rightCoords (X : imaginaryQuaternions) : Fin 6 → ℝ := ![0, 0, 0, (X : ℍ[ℝ]).imI, (X : ℍ[ℝ]).imJ, (X : ℍ[ℝ]).imK]
private def coordMap (X X' : imaginaryQuaternions) : (Fin 2 → ℝ) →L[ℝ] (Fin 6 → ℝ) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).smulRight (leftCoords X) +
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).smulRight (rightCoords X')
private theorem perturb_coordMap (b b' : TorusBond n) (X X' : imaginaryQuaternions) (s : Fin 2 → ℝ) (W : TorusField n) :
    perturb ![b, b'] ![X, X'] s W = perturb (bondsSix b b') basisSix (coordMap X X' s) W := by
  funext x i
  simp only [perturb]
  congr 2
  rw [Fin.sum_univ_two, Fin.sum_univ_six]
  simp only [bondsSix, basisSix, coordMap, leftCoords, rightCoords, add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hb : b = (x, i) <;> by_cases hb' : b' = (x, i) <;>
    simp [hb, hb', smul_decomp (s 0) X, smul_decomp (s 1) X'] <;> abel
private theorem coordMap_single_zero (X X' : imaginaryQuaternions) : coordMap X X' (Pi.single 0 1) = leftCoords X := by
  simp [coordMap]
private theorem coordMap_single_one (X X' : imaginaryQuaternions) : coordMap X X' (Pi.single 1 1) = rightCoords X' := by
  simp [coordMap]
private def adjoint (g : UnitQuaternion) : imaginaryQuaternions →ₗ[ℝ] imaginaryQuaternions where
  toFun w := ⟨(g : ℍ[ℝ]) * (w : ℍ[ℝ]) * star (g : ℍ[ℝ]), by
    have hw : (w : ℍ[ℝ]).re = 0 := w.2
    show ((g : ℍ[ℝ]) * (w : ℍ[ℝ]) * star (g : ℍ[ℝ])).re = 0
    simp [hw]
    ring⟩
  map_add' a b := by
    apply Subtype.ext
    simp [mul_add, add_mul]
  map_smul' c a := by
    apply Subtype.ext
    simp
private theorem expUnit_adjoint (g : UnitQuaternion) (w : imaginaryQuaternions) :
    expUnit (adjoint g w) = g * expUnit w * g⁻¹ := by
  let +nondep : NormedAlgebra ℚ ℍ[ℝ] := .restrictScalars ℚ ℝ ℍ[ℝ]
  apply Subtype.ext
  exact NormedSpace.exp_units_conj (Unitary.toUnits g) (w : ℍ[ℝ])
private theorem gaugeTransform_perturb {k : ℕ} (g : UnitQuaternion) (c : Fin k → TorusBond n)
    (Y : Fin k → imaginaryQuaternions) (s : Fin k → ℝ) :
    gaugeTransform (fun _ => g) (perturb c Y s (trivialField n)) =
      perturb c (fun l => adjoint g (Y l)) s (trivialField n) := by
  funext x i
  simp only [TorusFields.gaugeTransform, perturb, trivialField, mul_one]
  rw [← expUnit_adjoint, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
private theorem continuous_expUnit : Continuous expUnit := by apply _root_.YangMills.Construction.TorusFields.continuous_expUnit <;> assumption
private theorem eventually_isCold_perturb [NeZero n] {k : ℕ} (c : Fin k → TorusBond n)
    (Y : Fin k → imaginaryQuaternions) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ s in 𝓝 (0 : Fin k → ℝ), IsCold t (perturb c Y s (trivialField n)) := by
  have hb : ∀ x i, Continuous fun s : Fin k → ℝ => perturb c Y s (trivialField n) x i := by
    intro x i
    refine (continuous_expUnit.comp (continuous_finsetSum _ fun l _ => ?_)).mul continuous_const
    split_ifs
    · exact (continuous_apply l).smul continuous_const
    · exact continuous_const
  refine eventually_all.2 fun x => eventually_all.2 fun μ => eventually_all.2 fun ν => ?_
  by_cases hμν : μ < ν
  · have hc : Continuous fun s : Fin k → ℝ => curvature (perturb c Y s (trivialField n)) x μ ν := by
      have hp : Continuous fun s : Fin k → ℝ => holonomy (perturb c Y s (trivialField n)) x μ ν :=
        (((hb _ _).mul (hb _ _)).mul (hb _ _).inv).mul (hb _ _).inv
      exact ((continuous_subtype_val.comp hp).sub continuous_const).norm
    have h0 : curvature (perturb c Y 0 (trivialField n)) x μ ν = 0 := by
      have hm : perturb c Y 0 (trivialField n) = trivialField n := by
        funext x i
        have e : expUnit (0 : imaginaryQuaternions) = 1 := by
          apply Subtype.ext
          simp [expUnit]
        simp [perturb, trivialField, e]
      rw [hm]
      simp [curvature, holonomy, trivialField]
    have hlim := hc.tendsto 0
    rw [h0] at hlim
    exact (hlim.eventually_lt_const ht).mono fun s hs _ => hs
  · exact Eventually.of_forall fun s h => absurd h hμν
abbrev _root_.YangMills.SharedProofs.p58478 := @eventually_isCold_perturb
private theorem isCold_trivialField {t : ℝ} (ht : 0 < t) : IsCold t (trivialField n) := by apply _root_.YangMills.Construction.AbelianSecondOrder.isCold_trivialField <;> assumption
private def unitOfNormSqOne (q : ℍ[ℝ]) (hq : Quaternion.normSq q = 1) : UnitQuaternion :=
  ⟨q, by
    rw [Unitary.mem_iff]
    constructor
    · rw [Quaternion.star_mul_self, hq]
      simp
    · rw [Quaternion.self_mul_star, hq]
      simp⟩
private def unitAlongI : UnitQuaternion := unitOfNormSqOne ⟨0, 1, 0, 0⟩ ((Quaternion.normSq_def' _).trans (by
  show (0 : ℝ) ^ 2 + 1 ^ 2 + 0 ^ 2 + 0 ^ 2 = 1
  norm_num))
private def unitAlongJ : UnitQuaternion := unitOfNormSqOne ⟨0, 0, 1, 0⟩ ((Quaternion.normSq_def' _).trans (by
  show (0 : ℝ) ^ 2 + 0 ^ 2 + 1 ^ 2 + 0 ^ 2 = 1
  norm_num))
private def cyclicUnit : UnitQuaternion := unitOfNormSqOne ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩ ((Quaternion.normSq_def' _).trans (by
  show ((1 : ℝ) / 2) ^ 2 + (1 / 2) ^ 2 + (1 / 2) ^ 2 + (1 / 2) ^ 2 = 1
  norm_num))
private theorem imag_ext {X Y : imaginaryQuaternions} (h1 : (X : ℍ[ℝ]).imI = (Y : ℍ[ℝ]).imI)
    (h2 : (X : ℍ[ℝ]).imJ = (Y : ℍ[ℝ]).imJ) (h3 : (X : ℍ[ℝ]).imK = (Y : ℍ[ℝ]).imK) : X = Y := by
  rw [imag_decomp X, imag_decomp Y, h1, h2, h3]
private theorem adjoint_imI (g : UnitQuaternion) (w : imaginaryQuaternions) :
    ((adjoint g w : imaginaryQuaternions) : ℍ[ℝ]).imI = ((g : ℍ[ℝ]) * (w : ℍ[ℝ]) * star (g : ℍ[ℝ])).imI := rfl
private theorem adjoint_imJ (g : UnitQuaternion) (w : imaginaryQuaternions) :
    ((adjoint g w : imaginaryQuaternions) : ℍ[ℝ]).imJ = ((g : ℍ[ℝ]) * (w : ℍ[ℝ]) * star (g : ℍ[ℝ])).imJ := rfl
private theorem adjoint_imK (g : UnitQuaternion) (w : imaginaryQuaternions) :
    ((adjoint g w : imaginaryQuaternions) : ℍ[ℝ]).imK = ((g : ℍ[ℝ]) * (w : ℍ[ℝ]) * star (g : ℍ[ℝ])).imK := rfl
private theorem conj_components (q w : ℍ[ℝ]) (a b c d x y z : ℝ) (h1 : q.re = a) (h2 : q.imI = b) (h3 : q.imJ = c)
    (h4 : q.imK = d) (h5 : w.re = 0) (h6 : w.imI = x) (h7 : w.imJ = y) (h8 : w.imK = z) :
    (q * w * star q).imI = (a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2) * x + 2 * (b * c - a * d) * y + 2 * (b * d + a * c) * z ∧
    (q * w * star q).imJ = 2 * (b * c + a * d) * x + (a ^ 2 - b ^ 2 + c ^ 2 - d ^ 2) * y + 2 * (c * d - a * b) * z ∧
    (q * w * star q).imK = 2 * (b * d - a * c) * x + 2 * (c * d + a * b) * y + (a ^ 2 - b ^ 2 - c ^ 2 + d ^ 2) * z := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.conj_components <;> assumption
private theorem neg_imI' (X : imaginaryQuaternions) : ((-X : imaginaryQuaternions) : ℍ[ℝ]).imI = - (X : ℍ[ℝ]).imI := rfl
private theorem neg_imJ' (X : imaginaryQuaternions) : ((-X : imaginaryQuaternions) : ℍ[ℝ]).imJ = - (X : ℍ[ℝ]).imJ := rfl
private theorem neg_imK' (X : imaginaryQuaternions) : ((-X : imaginaryQuaternions) : ℍ[ℝ]).imK = - (X : ℍ[ℝ]).imK := rfl
private theorem adjoint_eq_of_components (g : UnitQuaternion) (w v : imaginaryQuaternions)
    (a b c d x y z x' y' z' : ℝ) (h1 : (g : ℍ[ℝ]).re = a)
    (h2 : (g : ℍ[ℝ]).imI = b) (h3 : (g : ℍ[ℝ]).imJ = c) (h4 : (g : ℍ[ℝ]).imK = d) (h6 : (w : ℍ[ℝ]).imI = x)
    (h7 : (w : ℍ[ℝ]).imJ = y) (h8 : (w : ℍ[ℝ]).imK = z) (k1 : (v : ℍ[ℝ]).imI = x') (k2 : (v : ℍ[ℝ]).imJ = y')
    (k3 : (v : ℍ[ℝ]).imK = z')
    (e1 : (a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2) * x + 2 * (b * c - a * d) * y + 2 * (b * d + a * c) * z = x')
    (e2 : 2 * (b * c + a * d) * x + (a ^ 2 - b ^ 2 + c ^ 2 - d ^ 2) * y + 2 * (c * d - a * b) * z = y')
    (e3 : 2 * (b * d - a * c) * x + 2 * (c * d + a * b) * y + (a ^ 2 - b ^ 2 - c ^ 2 + d ^ 2) * z = z') :
    adjoint g w = v := by
  obtain ⟨c1, c2, c3⟩ := conj_components (g : ℍ[ℝ]) (w : ℍ[ℝ]) a b c d x y z h1 h2 h3 h4 w.2 h6 h7 h8
  apply imag_ext
  · rw [adjoint_imI, c1, e1, k1]
  · rw [adjoint_imJ, c2, e2, k2]
  · rw [adjoint_imK, c3, e3, k3]
private theorem adjoint_unitAlongI_i : adjoint unitAlongI quaternionI = quaternionI :=
  adjoint_eq_of_components _ _ _ 0 1 0 0 1 0 0 1 0 0 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by norm_num) (by norm_num) (by norm_num)
private theorem adjoint_unitAlongI_j : adjoint unitAlongI imagJ = - imagJ :=
  adjoint_eq_of_components _ _ _ 0 1 0 0 0 1 0 0 (-1) 0 rfl rfl rfl rfl rfl rfl rfl (by rw [neg_imI']; norm_num [imagJ])
    (by rw [neg_imJ']; rfl) (by rw [neg_imK']; norm_num [imagJ]) (by norm_num) (by norm_num) (by norm_num)
private theorem adjoint_unitAlongI_k : adjoint unitAlongI imagK = - imagK :=
  adjoint_eq_of_components _ _ _ 0 1 0 0 0 0 1 0 0 (-1) rfl rfl rfl rfl rfl rfl rfl (by rw [neg_imI']; norm_num [imagK])
    (by rw [neg_imJ']; norm_num [imagK]) (by rw [neg_imK']; rfl) (by norm_num) (by norm_num) (by norm_num)
private theorem adjoint_unitAlongJ_j : adjoint unitAlongJ imagJ = imagJ :=
  adjoint_eq_of_components _ _ _ 0 0 1 0 0 1 0 0 1 0 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by norm_num) (by norm_num) (by norm_num)
private theorem adjoint_unitAlongJ_k : adjoint unitAlongJ imagK = - imagK :=
  adjoint_eq_of_components _ _ _ 0 0 1 0 0 0 1 0 0 (-1) rfl rfl rfl rfl rfl rfl rfl (by rw [neg_imI']; norm_num [imagK])
    (by rw [neg_imJ']; norm_num [imagK]) (by rw [neg_imK']; rfl) (by norm_num) (by norm_num) (by norm_num)
private theorem adjoint_cyclicUnit_i : adjoint cyclicUnit quaternionI = imagJ :=
  adjoint_eq_of_components _ _ _ (1/2) (1/2) (1/2) (1/2) 1 0 0 0 1 0 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by norm_num) (by norm_num) (by norm_num)
private theorem adjoint_cyclicUnit_j : adjoint cyclicUnit imagJ = imagK :=
  adjoint_eq_of_components _ _ _ (1/2) (1/2) (1/2) (1/2) 0 1 0 0 0 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by norm_num) (by norm_num) (by norm_num)
private theorem leftCoords_decomp (X : imaginaryQuaternions) :
    leftCoords X = (X : ℍ[ℝ]).imI • leftCoords quaternionI + (X : ℍ[ℝ]).imJ • leftCoords imagJ +
      (X : ℍ[ℝ]).imK • leftCoords imagK := by
  have i1 : (quaternionI : ℍ[ℝ]).imI = 1 := rfl
  have i2 : (quaternionI : ℍ[ℝ]).imJ = 0 := rfl
  have i3 : (quaternionI : ℍ[ℝ]).imK = 0 := rfl
  have j1 : (imagJ : ℍ[ℝ]).imI = 0 := rfl
  have j2 : (imagJ : ℍ[ℝ]).imJ = 1 := rfl
  have j3 : (imagJ : ℍ[ℝ]).imK = 0 := rfl
  have k1 : (imagK : ℍ[ℝ]).imI = 0 := rfl
  have k2 : (imagK : ℍ[ℝ]).imJ = 0 := rfl
  have k3 : (imagK : ℍ[ℝ]).imK = 1 := rfl
  funext l
  fin_cases l <;> simp [leftCoords, i1, i2, i3, j1, j2, j3, k1, k2, k3]
private theorem rightCoords_decomp (X : imaginaryQuaternions) :
    rightCoords X = (X : ℍ[ℝ]).imI • rightCoords quaternionI + (X : ℍ[ℝ]).imJ • rightCoords imagJ +
      (X : ℍ[ℝ]).imK • rightCoords imagK := by
  have i1 : (quaternionI : ℍ[ℝ]).imI = 1 := rfl
  have i2 : (quaternionI : ℍ[ℝ]).imJ = 0 := rfl
  have i3 : (quaternionI : ℍ[ℝ]).imK = 0 := rfl
  have j1 : (imagJ : ℍ[ℝ]).imI = 0 := rfl
  have j2 : (imagJ : ℍ[ℝ]).imJ = 1 := rfl
  have j3 : (imagJ : ℍ[ℝ]).imK = 0 := rfl
  have k1 : (imagK : ℍ[ℝ]).imI = 0 := rfl
  have k2 : (imagK : ℍ[ℝ]).imJ = 0 := rfl
  have k3 : (imagK : ℍ[ℝ]).imK = 1 := rfl
  funext l
  fin_cases l <;> simp [rightCoords, i1, i2, i3, j1, j2, j3, k1, k2, k3]
private theorem leftCoords_neg (X : imaginaryQuaternions) : leftCoords (-X) = - leftCoords X := by
  funext l
  fin_cases l <;> simp [leftCoords]
private theorem rightCoords_neg (X : imaginaryQuaternions) : rightCoords (-X) = - rightCoords X := by
  funext l
  fin_cases l <;> simp [rightCoords]
private def swapTwo : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).smulRight (Pi.single 0 1) +
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).smulRight (Pi.single 1 1)
private theorem perturb_swapTwo (b b' : TorusBond n) (X X' : imaginaryQuaternions) (s : Fin 2 → ℝ) (W : TorusField n) :
    perturb ![b', b] ![X', X] s W = perturb ![b, b'] ![X, X'] (swapTwo s) W := by
  funext x i
  simp only [perturb]
  congr 2
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp [swapTwo, add_comm]
  by_cases hb' : b' = (x, i) <;> simp [hb']
theorem hessianAtTrivialField : HessianAtTrivialFieldStatement := by
  intro ℓ hfit C h hh n _ hn y b b'
  have hcold : IsCold ℓ.threshold (trivialField n) := isCold_trivialField hfit.σ_pos
  have hC3 := hh.smooth n hn y (trivialField n) hcold
  set Φ : (Fin 6 → ℝ) → ℝ := fun τ => h n y (perturb (bondsSix b b') basisSix τ (trivialField n)) with hΦdef
  have hΦ : ContDiffAt ℝ 3 Φ 0 := hC3 6 (bondsSix b b') basisSix
  have hD : ∀ X X' : imaginaryQuaternions, mixedDeriv (h n y) (trivialField n) ![b, b'] ![X, X'] =
      secondDeriv Φ (leftCoords X) (rightCoords X') := by
    intro X X'
    rw [mixedDeriv_eq_fderiv]
    have e : (fun s : Fin 2 → ℝ => h n y (perturb ![b, b'] ![X, X'] s (trivialField n))) =
        fun s => Φ (coordMap X X' s) := by
      funext s
      rw [perturb_coordMap]
    rw [e]
    have := secondDeriv_comp Φ (coordMap X X') hΦ (Pi.single 0 1) (Pi.single 1 1)
    rwa [coordMap_single_zero, coordMap_single_one] at this
  have hconj : ∀ (g : UnitQuaternion) (X X' : imaginaryQuaternions),
      mixedDeriv (h n y) (trivialField n) ![b, b'] ![adjoint g X, adjoint g X'] =
      mixedDeriv (h n y) (trivialField n) ![b, b'] ![X, X'] := by
    intro g X X'
    simp only [mixedDeriv]
    have e : (fun s : Fin 2 → ℝ => h n y (perturb ![b, b'] ![adjoint g X, adjoint g X'] s (trivialField n))) =ᶠ[𝓝 0]
        fun s => h n y (perturb ![b, b'] ![X, X'] s (trivialField n)) := by
      refine (eventually_isCold_perturb ![b, b'] ![X, X'] hfit.σ_pos).mono fun s hs => ?_
      have e2 := hh.gauge n hn y (fun _ => g) _ hs
      rw [gaugeTransform_perturb] at e2
      have e3 : (fun l => adjoint g (![X, X'] l)) = ![adjoint g X, adjoint g X'] := by
        funext l
        fin_cases l <;> rfl
      rw [e3] at e2
      exact e2
    have e4 := (Filter.EventuallyEq.iteratedFDeriv ℝ e 2).self_of_nhds
    rw [e4]
  set D : imaginaryQuaternions → imaginaryQuaternions → ℝ :=
    fun X X' => mixedDeriv (h n y) (trivialField n) ![b, b'] ![X, X'] with hDdef
  have hnegR : ∀ X X', D X (-X') = - D X X' := by
    intro X X'
    simp only [hDdef, hD, rightCoords_neg, secondDeriv, map_neg]
  have hnegL : ∀ X X', D (-X) X' = - D X X' := by
    intro X X'
    simp only [hDdef, hD, leftCoords_neg, secondDeriv, map_neg, neg_apply]
  have m12 : D quaternionI imagJ = 0 := by
    have := hconj unitAlongI quaternionI imagJ
    rw [adjoint_unitAlongI_i, adjoint_unitAlongI_j] at this
    have h2 := hnegR quaternionI imagJ
    simp only [hDdef] at h2
    linarith
  have m13 : D quaternionI imagK = 0 := by
    have := hconj unitAlongI quaternionI imagK
    rw [adjoint_unitAlongI_i, adjoint_unitAlongI_k] at this
    have h2 := hnegR quaternionI imagK
    simp only [hDdef] at h2
    linarith
  have m21 : D imagJ quaternionI = 0 := by
    have := hconj unitAlongI imagJ quaternionI
    rw [adjoint_unitAlongI_i, adjoint_unitAlongI_j] at this
    have h2 := hnegL imagJ quaternionI
    simp only [hDdef] at h2
    linarith
  have m31 : D imagK quaternionI = 0 := by
    have := hconj unitAlongI imagK quaternionI
    rw [adjoint_unitAlongI_i, adjoint_unitAlongI_k] at this
    have h2 := hnegL imagK quaternionI
    simp only [hDdef] at h2
    linarith
  have m23 : D imagJ imagK = 0 := by
    have := hconj unitAlongJ imagJ imagK
    rw [adjoint_unitAlongJ_j, adjoint_unitAlongJ_k] at this
    have h2 := hnegR imagJ imagK
    simp only [hDdef] at h2
    linarith
  have m32 : D imagK imagJ = 0 := by
    have := hconj unitAlongJ imagK imagJ
    rw [adjoint_unitAlongJ_j, adjoint_unitAlongJ_k] at this
    have h2 := hnegL imagK imagJ
    simp only [hDdef] at h2
    linarith
  have m22 : D imagJ imagJ = D quaternionI quaternionI := by
    have := hconj cyclicUnit quaternionI quaternionI
    rwa [adjoint_cyclicUnit_i] at this
  have m33 : D imagK imagK = D imagJ imagJ := by
    have := hconj cyclicUnit imagJ imagJ
    rwa [adjoint_cyclicUnit_j] at this
  refine ⟨fun X X' => ?_, ?_⟩
  · have hexp : D X X' = (X : ℍ[ℝ]).imI * (X' : ℍ[ℝ]).imI * D quaternionI quaternionI +
        (X : ℍ[ℝ]).imI * (X' : ℍ[ℝ]).imJ * D quaternionI imagJ + (X : ℍ[ℝ]).imI * (X' : ℍ[ℝ]).imK * D quaternionI imagK +
        (X : ℍ[ℝ]).imJ * (X' : ℍ[ℝ]).imI * D imagJ quaternionI + (X : ℍ[ℝ]).imJ * (X' : ℍ[ℝ]).imJ * D imagJ imagJ +
        (X : ℍ[ℝ]).imJ * (X' : ℍ[ℝ]).imK * D imagJ imagK + (X : ℍ[ℝ]).imK * (X' : ℍ[ℝ]).imI * D imagK quaternionI +
        (X : ℍ[ℝ]).imK * (X' : ℍ[ℝ]).imJ * D imagK imagJ + (X : ℍ[ℝ]).imK * (X' : ℍ[ℝ]).imK * D imagK imagK := by
      simp only [hDdef, hD, secondDeriv]
      rw [leftCoords_decomp X, rightCoords_decomp X']
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      ring
    have hin : inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) = (X : ℍ[ℝ]).imI * (X' : ℍ[ℝ]).imI +
        (X : ℍ[ℝ]).imJ * (X' : ℍ[ℝ]).imJ + (X : ℍ[ℝ]).imK * (X' : ℍ[ℝ]).imK := by
      have hre : (X : ℍ[ℝ]).re = 0 := X.2
      have hre' : (X' : ℍ[ℝ]).re = 0 := X'.2
      rw [Quaternion.inner_def]
      simp [hre, hre']
    show D X X' = _ * D quaternionI quaternionI
    rw [hexp, m12, m13, m21, m31, m23, m32, m33, m22, hin]
    ring
  · have hF : ContDiffAt ℝ 3
        (fun s : Fin 2 → ℝ => h n y (perturb ![b, b'] ![quaternionI, quaternionI] s (trivialField n))) 0 :=
      hC3 2 ![b, b'] ![quaternionI, quaternionI]
    rw [mixedDeriv_eq_fderiv, mixedDeriv_eq_fderiv]
    have e : (fun s : Fin 2 → ℝ => h n y (perturb ![b', b] ![quaternionI, quaternionI] s (trivialField n))) =
        fun s => (fun s' : Fin 2 → ℝ => h n y (perturb ![b, b'] ![quaternionI, quaternionI] s' (trivialField n)))
          (swapTwo s) := by
      funext s
      rw [perturb_swapTwo]
    rw [e]
    have h1 := secondDeriv_comp
      (fun s' : Fin 2 → ℝ => h n y (perturb ![b, b'] ![quaternionI, quaternionI] s' (trivialField n))) swapTwo hF
      (Pi.single 0 1) (Pi.single 1 1)
    have s0 : swapTwo (Pi.single 0 1) = Pi.single 1 1 := by simp [swapTwo]
    have s1 : swapTwo (Pi.single 1 1) = Pi.single 0 1 := by simp [swapTwo]
    rw [s0, s1] at h1
    have h2 := secondDeriv_symm _ hF (Pi.single 1 1 : Fin 2 → ℝ) (Pi.single 0 1)
    simp only [secondDeriv] at h1 h2
    rw [h1, h2]
end YangMills.Construction.FlatHessian
end
