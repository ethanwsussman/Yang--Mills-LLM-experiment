import YangMills.Construction.ColdChainAtEveryLevel.LocalFormOfTheLinesProof
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdStepAtMirrorFrames.SumOfADecayOverTheCellsProof
import YangMills.Construction.QuaternionicWilsonModel.TheFlowRepresentsTheMixedMomentProof
import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import YangMills.Construction.RunningCouplingSlope.CoefficientOfALocalDensity
import YangMills.Construction.RunningCouplingSlope.SumOfADecayOnATorus
import YangMills.Construction.SummableBoundsOfTheFlow.OneNumberOfOneTotalProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
open scoped Topology Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.SlopeCoefficient YangMills.Construction.RunningCouplingSlope Filter
namespace YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient
section Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem eventually_differentiableAt_of_contDiffAt_two {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    ∀ᶠ A in 𝓝 (0 : E), DifferentiableAt ℝ f A :=
  (hf.eventually (by simp)).mono fun A hA => hA.differentiableAt (by simp)
theorem differentiableAt_fderiv_of_contDiffAt_two {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    DifferentiableAt ℝ (fderiv ℝ f) 0 :=
  (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
theorem secondDeriv_comp_clm {Ψ : F → ℝ} (hΨ : ContDiffAt ℝ 2 Ψ 0) (L : E →L[ℝ] F) (u v : E) :
    fderiv ℝ (fderiv ℝ (Ψ ∘ L)) 0 u v = fderiv ℝ (fderiv ℝ Ψ) 0 (L u) (L v) := by
  have hL0 : Tendsto L (𝓝 0) (𝓝 (0 : F)) := by
    simpa using L.continuous.tendsto 0
  have hev : fderiv ℝ (Ψ ∘ L) =ᶠ[𝓝 0] fun y => (fderiv ℝ Ψ (L y)).comp L := by
    filter_upwards [hL0.eventually (eventually_differentiableAt_of_contDiffAt_two hΨ)] with y hy
    rw [fderiv_comp y hy L.differentiableAt, L.fderiv]
  rw [hev.fderiv_eq]
  have h1 : HasFDerivAt (fun y => fderiv ℝ Ψ (L y)) ((fderiv ℝ (fderiv ℝ Ψ) 0).comp L) 0 := by
    have h : HasFDerivAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) 0) (L 0) := by
      rw [map_zero]
      exact (differentiableAt_fderiv_of_contDiffAt_two hΨ).hasFDerivAt
    exact h.comp (0 : E) L.hasFDerivAt
  have h2 := ((ContinuousLinearMap.compL ℝ E F ℝ).flip L).hasFDerivAt.comp (0 : E) h1
  have h3 : (fun y => (fderiv ℝ Ψ (L y)).comp L) =
      ((ContinuousLinearMap.compL ℝ E F ℝ).flip L) ∘ fun y => fderiv ℝ Ψ (L y) := by
    funext y
    simp
  rw [h3, h2.fderiv]
  simp
theorem secondDeriv_add {f g : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 2 g 0) (u v : E) :
    fderiv ℝ (fderiv ℝ fun θ => f θ + g θ) 0 u v =
      fderiv ℝ (fderiv ℝ f) 0 u v + fderiv ℝ (fderiv ℝ g) 0 u v := by
  have hev : fderiv ℝ (fun θ => f θ + g θ) =ᶠ[𝓝 0] fun θ => fderiv ℝ f θ + fderiv ℝ g θ := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt_two hf,
      eventually_differentiableAt_of_contDiffAt_two hg] with A ha hb
    exact fderiv_fun_add ha hb
  rw [hev.fderiv_eq, fderiv_fun_add (differentiableAt_fderiv_of_contDiffAt_two hf)
    (differentiableAt_fderiv_of_contDiffAt_two hg)]
  rfl
theorem fderiv_sub_const_fun (f : E → ℝ) (c : ℝ) :
    fderiv ℝ (fun θ => f θ - c) = fderiv ℝ f := by
  funext x
  simp [fderiv_sub_const]
theorem secondDeriv_sum {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) 0) (u v : E) :
    fderiv ℝ (fderiv ℝ fun θ => ∑ i ∈ s, f i θ) 0 u v =
      ∑ i ∈ s, fderiv ℝ (fderiv ℝ (f i)) 0 u v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h : (fun θ : E => ∑ i ∈ (∅ : Finset ι), f i θ) = fun _ => 0 := by
      funext θ
      simp
    rw [h]
    simp
  | insert a s ha ih =>
    have h1 : (fun θ => ∑ i ∈ insert a s, f i θ) = fun θ => f a θ + ∑ i ∈ s, f i θ := by
      funext θ
      rw [Finset.sum_insert ha]
    have hs : ContDiffAt ℝ 2 (fun θ => ∑ i ∈ s, f i θ) 0 :=
      ContDiffAt.sum fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [h1, secondDeriv_add (hf a (Finset.mem_insert_self a s)) hs,
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi), Finset.sum_insert ha]
end Calculus
section Group
theorem continuous_expUnit : Continuous expUnit := by apply _root_.YangMills.Construction.TorusFields.continuous_expUnit <;> assumption
theorem expUnit_zero : expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
def imaginaryJ : imaginaryQuaternions := ⟨⟨0, 0, 1, 0⟩, rfl⟩
def imaginaryK : imaginaryQuaternions := ⟨⟨0, 0, 0, 1⟩, rfl⟩
theorem imaginary_decomp (X : imaginaryQuaternions) :
    X = ((X : ℍ[ℝ]).imI) • quaternionI + ((X : ℍ[ℝ]).imJ) • imaginaryJ + ((X : ℍ[ℝ]).imK) • imaginaryK := by
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
def conjAction (g : UnitQuaternion) : imaginaryQuaternions →ₗ[ℝ] imaginaryQuaternions where
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
theorem expUnit_conjAction (g : UnitQuaternion) (w : imaginaryQuaternions) :
    expUnit (conjAction g w) = g * expUnit w * g⁻¹ := by
  let +nondep : NormedAlgebra ℚ ℍ[ℝ] := .restrictScalars ℚ ℝ ℍ[ℝ]
  apply Subtype.ext
  exact NormedSpace.exp_units_conj (Unitary.toUnits g) (w : ℍ[ℝ])
def unitOfNormSqOne (q : ℍ[ℝ]) (hq : Quaternion.normSq q = 1) : UnitQuaternion :=
  ⟨q, by
    rw [Unitary.mem_iff]
    constructor
    · rw [Quaternion.star_mul_self, hq]
      simp
    · rw [Quaternion.self_mul_star, hq]
      simp⟩
def rotI : UnitQuaternion := unitOfNormSqOne ⟨0, 1, 0, 0⟩ ((Quaternion.normSq_def' _).trans (by
  show (0 : ℝ) ^ 2 + 1 ^ 2 + 0 ^ 2 + 0 ^ 2 = 1
  norm_num))
def rotJ : UnitQuaternion := unitOfNormSqOne ⟨0, 0, 1, 0⟩ ((Quaternion.normSq_def' _).trans (by
  show (0 : ℝ) ^ 2 + 0 ^ 2 + 1 ^ 2 + 0 ^ 2 = 1
  norm_num))
def rotDiag : UnitQuaternion := unitOfNormSqOne ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩ ((Quaternion.normSq_def' _).trans (by
  show ((1 : ℝ) / 2) ^ 2 + (1 / 2) ^ 2 + (1 / 2) ^ 2 + (1 / 2) ^ 2 = 1
  norm_num))
theorem imaginary_ext {X Y : imaginaryQuaternions} (h1 : (X : ℍ[ℝ]).imI = (Y : ℍ[ℝ]).imI)
    (h2 : (X : ℍ[ℝ]).imJ = (Y : ℍ[ℝ]).imJ)
    (h3 : (X : ℍ[ℝ]).imK = (Y : ℍ[ℝ]).imK) : X = Y := by
  rw [imaginary_decomp X, imaginary_decomp Y, h1, h2, h3]
theorem conjAction_imI (g : UnitQuaternion) (w : imaginaryQuaternions) :
    ((conjAction g w : imaginaryQuaternions) : ℍ[ℝ]).imI =
    ((g : ℍ[ℝ]) * (w : ℍ[ℝ]) * star (g : ℍ[ℝ])).imI := rfl
theorem conjAction_imJ (g : UnitQuaternion) (w : imaginaryQuaternions) :
    ((conjAction g w : imaginaryQuaternions) : ℍ[ℝ]).imJ =
    ((g : ℍ[ℝ]) * (w : ℍ[ℝ]) * star (g : ℍ[ℝ])).imJ := rfl
theorem conjAction_imK (g : UnitQuaternion) (w : imaginaryQuaternions) :
    ((conjAction g w : imaginaryQuaternions) : ℍ[ℝ]).imK =
    ((g : ℍ[ℝ]) * (w : ℍ[ℝ]) * star (g : ℍ[ℝ])).imK := rfl
theorem conj_components (q w : ℍ[ℝ]) (a b c d x y z : ℝ) (h1 : q.re = a) (h2 : q.imI = b) (h3 : q.imJ = c)
    (h4 : q.imK = d) (h5 : w.re = 0) (h6 : w.imI = x) (h7 : w.imJ = y) (h8 : w.imK = z) :
    (q * w * star q).imI = (a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2) * x + 2 * (b * c - a * d) * y + 2 * (b * d + a * c) * z ∧
    (q * w * star q).imJ = 2 * (b * c + a * d) * x + (a ^ 2 - b ^ 2 + c ^ 2 - d ^ 2) * y + 2 * (c * d - a * b) * z ∧
    (q * w * star q).imK = 2 * (b * d - a * c) * x + 2 * (c * d + a * b) * y + (a ^ 2 - b ^ 2 - c ^ 2 + d ^ 2) * z := by
  subst h1 h2 h3 h4 h6 h7 h8
  refine ⟨?_, ?_, ?_⟩ <;> simp [h5] <;> ring
theorem imaginary_neg_imI (X : imaginaryQuaternions) :
    ((-X : imaginaryQuaternions) : ℍ[ℝ]).imI = - (X : ℍ[ℝ]).imI := rfl
theorem imaginary_neg_imJ (X : imaginaryQuaternions) :
    ((-X : imaginaryQuaternions) : ℍ[ℝ]).imJ = - (X : ℍ[ℝ]).imJ := rfl
theorem imaginary_neg_imK (X : imaginaryQuaternions) :
    ((-X : imaginaryQuaternions) : ℍ[ℝ]).imK = - (X : ℍ[ℝ]).imK := rfl
theorem conjAction_eq_of_components (g : UnitQuaternion) (w v : imaginaryQuaternions)
    (a b c d x y z x' y' z' : ℝ) (h1 : (g : ℍ[ℝ]).re = a)
    (h2 : (g : ℍ[ℝ]).imI = b) (h3 : (g : ℍ[ℝ]).imJ = c) (h4 : (g : ℍ[ℝ]).imK = d) (h6 : (w : ℍ[ℝ]).imI = x)
    (h7 : (w : ℍ[ℝ]).imJ = y) (h8 : (w : ℍ[ℝ]).imK = z) (k1 : (v : ℍ[ℝ]).imI = x') (k2 : (v : ℍ[ℝ]).imJ = y')
    (k3 : (v : ℍ[ℝ]).imK = z')
    (e1 : (a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2) * x + 2 * (b * c - a * d) * y + 2 * (b * d + a * c) * z = x')
    (e2 : 2 * (b * c + a * d) * x + (a ^ 2 - b ^ 2 + c ^ 2 - d ^ 2) * y + 2 * (c * d - a * b) * z = y')
    (e3 : 2 * (b * d - a * c) * x + 2 * (c * d + a * b) * y + (a ^ 2 - b ^ 2 - c ^ 2 + d ^ 2) * z = z') :
    conjAction g w = v := by
  obtain ⟨c1, c2, c3⟩ := conj_components (g : ℍ[ℝ]) (w : ℍ[ℝ]) a b c d x y z h1 h2 h3 h4 w.2 h6 h7 h8
  apply imaginary_ext
  · rw [conjAction_imI, c1, e1, k1]
  · rw [conjAction_imJ, c2, e2, k2]
  · rw [conjAction_imK, c3, e3, k3]
theorem conjAction_rotI_I : conjAction rotI quaternionI = quaternionI :=
  conjAction_eq_of_components _ _ _ 0 1 0 0 1 0 0 1 0 0 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by norm_num) (by norm_num) (by norm_num)
theorem conjAction_rotI_J : conjAction rotI imaginaryJ = - imaginaryJ :=
  conjAction_eq_of_components _ _ _ 0 1 0 0 0 1 0 0 (-1) 0 rfl rfl rfl rfl rfl rfl rfl
    (by rw [imaginary_neg_imI]; norm_num [imaginaryJ])
    (by rw [imaginary_neg_imJ]; rfl) (by rw [imaginary_neg_imK]; norm_num [imaginaryJ])
    (by norm_num) (by norm_num) (by norm_num)
theorem conjAction_rotI_K : conjAction rotI imaginaryK = - imaginaryK :=
  conjAction_eq_of_components _ _ _ 0 1 0 0 0 0 1 0 0 (-1) rfl rfl rfl rfl rfl rfl rfl
    (by rw [imaginary_neg_imI]; norm_num [imaginaryK])
    (by rw [imaginary_neg_imJ]; norm_num [imaginaryK]) (by rw [imaginary_neg_imK]; rfl)
    (by norm_num) (by norm_num) (by norm_num)
theorem conjAction_rotJ_J : conjAction rotJ imaginaryJ = imaginaryJ :=
  conjAction_eq_of_components _ _ _ 0 0 1 0 0 1 0 0 1 0 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by norm_num) (by norm_num) (by norm_num)
theorem conjAction_rotJ_K : conjAction rotJ imaginaryK = - imaginaryK :=
  conjAction_eq_of_components _ _ _ 0 0 1 0 0 0 1 0 0 (-1) rfl rfl rfl rfl rfl rfl rfl
    (by rw [imaginary_neg_imI]; norm_num [imaginaryK])
    (by rw [imaginary_neg_imJ]; norm_num [imaginaryK]) (by rw [imaginary_neg_imK]; rfl)
    (by norm_num) (by norm_num) (by norm_num)
theorem conjAction_rotDiag_I : conjAction rotDiag quaternionI = imaginaryJ :=
  conjAction_eq_of_components _ _ _ (1/2) (1/2) (1/2) (1/2) 1 0 0 0 1 0 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by norm_num) (by norm_num) (by norm_num)
theorem conjAction_rotDiag_J : conjAction rotDiag imaginaryJ = imaginaryK :=
  conjAction_eq_of_components _ _ _ (1/2) (1/2) (1/2) (1/2) 0 1 0 0 0 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by norm_num) (by norm_num) (by norm_num)
theorem inner_imaginary (X X' : imaginaryQuaternions) : inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) =
    (X : ℍ[ℝ]).imI * (X' : ℍ[ℝ]).imI + (X : ℍ[ℝ]).imJ * (X' : ℍ[ℝ]).imJ +
      (X : ℍ[ℝ]).imK * (X' : ℍ[ℝ]).imK := by
  have h1 : (X : ℍ[ℝ]).re = 0 := X.2
  have h2 : (X' : ℍ[ℝ]).re = 0 := X'.2
  rw [Quaternion.inner_def]
  simp [h1, h2]
theorem bilin_eq_inner_mul_of_conj_invariant
    (B : imaginaryQuaternions →ₗ[ℝ] imaginaryQuaternions →ₗ[ℝ] ℝ)
    (hB : ∀ (g : UnitQuaternion) (X X' : imaginaryQuaternions), B (conjAction g X) (conjAction g X') = B X X')
    (X X' : imaginaryQuaternions) :
    B X X' = inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) * B quaternionI quaternionI := by
  have hIJ : B quaternionI imaginaryJ = 0 := by
    have h := hB rotI quaternionI imaginaryJ
    rw [conjAction_rotI_I, conjAction_rotI_J, map_neg] at h
    linarith
  have hIK : B quaternionI imaginaryK = 0 := by
    have h := hB rotI quaternionI imaginaryK
    rw [conjAction_rotI_I, conjAction_rotI_K, map_neg] at h
    linarith
  have hJI : B imaginaryJ quaternionI = 0 := by
    have h := hB rotI imaginaryJ quaternionI
    rw [conjAction_rotI_I, conjAction_rotI_J, map_neg, LinearMap.neg_apply] at h
    linarith
  have hKI : B imaginaryK quaternionI = 0 := by
    have h := hB rotI imaginaryK quaternionI
    rw [conjAction_rotI_I, conjAction_rotI_K, map_neg, LinearMap.neg_apply] at h
    linarith
  have hJK : B imaginaryJ imaginaryK = 0 := by
    have h := hB rotJ imaginaryJ imaginaryK
    rw [conjAction_rotJ_J, conjAction_rotJ_K, map_neg] at h
    linarith
  have hKJ : B imaginaryK imaginaryJ = 0 := by
    have h := hB rotJ imaginaryK imaginaryJ
    rw [conjAction_rotJ_J, conjAction_rotJ_K, map_neg, LinearMap.neg_apply] at h
    linarith
  have hJJ : B imaginaryJ imaginaryJ = B quaternionI quaternionI := by
    have h := hB rotDiag quaternionI quaternionI
    rwa [conjAction_rotDiag_I] at h
  have hKK : B imaginaryK imaginaryK = B quaternionI quaternionI := by
    have h := hB rotDiag imaginaryJ imaginaryJ
    rw [conjAction_rotDiag_J] at h
    rw [h, hJJ]
  rw [inner_imaginary]
  conv_lhs => rw [imaginary_decomp X, imaginary_decomp X']
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hIJ, hIK, hJI, hKI,
    hJK, hKJ, hJJ, hKK]
  ring
end Group
section Fields
variable {n : ℕ} [NeZero n]
def expOfCoords (θ : TorusBond n → imaginaryQuaternions) : TorusField n := fun x i => expUnit (θ (x, i))
def coordTotal (H : GaugeTotal) (n : ℕ) [NeZero n] (θ : TorusBond n → imaginaryQuaternions) : ℝ :=
  H n (expOfCoords θ)
def bondDirections {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    (Fin k → ℝ) →L[ℝ] (TorusBond n → imaginaryQuaternions) :=
  ContinuousLinearMap.pi fun b => ∑ l, if c l = b then
    (ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (X l) else 0
theorem bondDirections_apply {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) (b : TorusBond n) :
    bondDirections c X σ b = ∑ l, if c l = b then σ l • X l else 0 := by
  simp only [bondDirections, ContinuousLinearMap.coe_pi', ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
theorem bondDirections_single {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (l : Fin k) :
    bondDirections c X (Pi.single l 1) = Pi.single (c l) (X l) := by
  funext b
  rw [bondDirections_apply, Pi.single_apply, Finset.sum_eq_single l]
  · by_cases h : c l = b
    · simp [h]
    · simp [h, Ne.symm h]
  · intro l' _ hne
    split_ifs <;> simp [hne]
  · simp
theorem perturb_trivialField_eq {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) :
    perturb c X σ (trivialField n) = expOfCoords (bondDirections c X σ) := by
  funext x i
  simp only [perturb, trivialField, expOfCoords, mul_one, bondDirections_apply]
theorem perturb_eq_coordTotal_comp {H : GaugeTotal} {k : ℕ} (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) :
    (fun σ : Fin k → ℝ => H n (perturb c X σ (trivialField n))) = coordTotal H n ∘ bondDirections c X := by
  funext σ
  simp only [Function.comp, coordTotal, perturb_trivialField_eq]
abbrev IsTwiceDiffAlongBonds (H : GaugeTotal) (n : ℕ) : Prop :=
  ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
    ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => H n (perturb c X σ (trivialField n))) 0
def imaginaryBasis : Fin 3 → imaginaryQuaternions := ![quaternionI, imaginaryJ, imaginaryK]
def imaginaryCoords (w : imaginaryQuaternions) : Fin 3 → ℝ := ![(w : ℍ[ℝ]).imI, (w : ℍ[ℝ]).imJ, (w : ℍ[ℝ]).imK]
theorem sum_imaginaryCoords_smul (w : imaginaryQuaternions) :
    ∑ m, imaginaryCoords w m • imaginaryBasis m = w := by
  rw [Fin.sum_univ_three]
  exact (imaginary_decomp w).symm
theorem contDiffAt_coordTotal {H : GaugeTotal} (hs : IsTwiceDiffAlongBonds H n) :
    ContDiffAt ℝ 2 (coordTotal H n) 0 := by
  classical
  let e := Fintype.equivFin (TorusBond n × Fin 3)
  let c : Fin (Fintype.card (TorusBond n × Fin 3)) → TorusBond n := fun l => (e.symm l).1
  let X : Fin (Fintype.card (TorusBond n × Fin 3)) → imaginaryQuaternions := fun l => imaginaryBasis (e.symm l).2
  let π₀ : (TorusBond n → imaginaryQuaternions) →ₗ[ℝ] (Fin (Fintype.card (TorusBond n × Fin 3)) → ℝ) :=
    { toFun := fun θ l => imaginaryCoords (θ (c l)) (e.symm l).2
      map_add' := by
        intro a b
        funext l
        simp only [Pi.add_apply, imaginaryCoords]
        generalize (e.symm l).2 = m
        fin_cases m <;> simp
      map_smul' := by
        intro r a
        funext l
        simp only [Pi.smul_apply, imaginaryCoords, RingHom.id_apply]
        generalize (e.symm l).2 = m
        fin_cases m <;> simp }
  let π : (TorusBond n → imaginaryQuaternions) →L[ℝ] (Fin (Fintype.card (TorusBond n × Fin 3)) → ℝ) :=
    LinearMap.toContinuousLinearMap π₀
  have hid : ∀ θ : TorusBond n → imaginaryQuaternions, bondDirections c X (π θ) = θ := by
    intro θ
    funext b
    rw [bondDirections_apply]
    have h1 : (∑ l, if c l = b then (π θ l) • X l else 0) =
        ∑ p : TorusBond n × Fin 3, if p.1 = b then imaginaryCoords (θ p.1) p.2 • imaginaryBasis p.2 else 0 := by
      refine Fintype.sum_equiv e.symm _ _ fun l => ?_
      rfl
    rw [h1, Fintype.sum_prod_type, Finset.sum_eq_single b]
    · simp [sum_imaginaryCoords_smul]
    · intro b' _ hb
      simp [hb]
    · simp
  have hφ := hs _ c X
  have hcomp : coordTotal H n = (fun σ => H n (perturb c X σ (trivialField n))) ∘ π := by
    funext θ
    simp only [Function.comp, perturb_trivialField_eq, coordTotal, hid]
  rw [hcomp]
  refine ContDiffAt.comp (0 : TorusBond n → imaginaryQuaternions) ?_ π.contDiff.contDiffAt
  simpa using hφ
def hessianCoords (H : GaugeTotal) (n : ℕ) [NeZero n] :
    (TorusBond n → imaginaryQuaternions) →L[ℝ] (TorusBond n → imaginaryQuaternions) →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (coordTotal H n)) 0
theorem mixedDeriv_eq_hessianCoords {H : GaugeTotal} (hs : IsTwiceDiffAlongBonds H n) (c c' : TorusBond n)
    (X X' : imaginaryQuaternions) :
    mixedDeriv (H n) (trivialField n) ![c, c'] ![X, X'] =
      hessianCoords H n (Pi.single c X) (Pi.single c' X') := by
  unfold mixedDeriv
  rw [iteratedFDeriv_two_apply,
    perturb_eq_coordTotal_comp (H := H) (![c, c'] : Fin 2 → TorusBond n) ![X, X'],
    secondDeriv_comp_clm (contDiffAt_coordTotal hs), bondDirections_single, bondDirections_single]
  rfl
theorem continuous_expOfCoords : Continuous (expOfCoords (n := n)) :=
  continuous_pi fun x => continuous_pi fun i => continuous_expUnit.comp (continuous_apply (x, i))
theorem expOfCoords_zero : expOfCoords (n := n) 0 = trivialField n := by
  funext x i
  simp [expOfCoords, trivialField, expUnit_zero]
theorem tendsto_expOfCoords : Tendsto (expOfCoords (n := n)) (𝓝 0) (𝓝 (trivialField n)) := by
  have := (continuous_expOfCoords (n := n)).tendsto 0
  rwa [expOfCoords_zero] at this
def coordShift (u : TorusSite n) :
    (TorusBond n → imaginaryQuaternions) →L[ℝ] (TorusBond n → imaginaryQuaternions) :=
  ContinuousLinearMap.pi fun b => ContinuousLinearMap.proj (b.1 + u, b.2)
theorem coordShift_single (u : TorusSite n) (c : TorusBond n) (X : imaginaryQuaternions) :
    coordShift u (Pi.single c X) = Pi.single (c.1 - u, c.2) X := by
  classical
  funext ⟨x, i⟩
  simp only [coordShift, ContinuousLinearMap.coe_pi', ContinuousLinearMap.proj_apply, Pi.single_apply]
  have : ((x + u, i) = c) ↔ ((x, i) = (c.1 - u, c.2)) := by
    obtain ⟨y, j⟩ := c
    simp [eq_sub_iff_add_eq]
  simp [this]
theorem translate_expOfCoords (u : TorusSite n) (θ : TorusBond n → imaginaryQuaternions) :
    TorusFields.translate u (expOfCoords θ) = expOfCoords (coordShift u θ) := by
  funext x i
  simp [TorusFields.translate, expOfCoords, coordShift]
def coordConj (g : UnitQuaternion) :
    (TorusBond n → imaginaryQuaternions) →L[ℝ] (TorusBond n → imaginaryQuaternions) :=
  ContinuousLinearMap.pi fun b => (LinearMap.toContinuousLinearMap (conjAction g)).comp
    (ContinuousLinearMap.proj b)
theorem coordConj_single (g : UnitQuaternion) (c : TorusBond n) (X : imaginaryQuaternions) :
    coordConj g (Pi.single c X) = Pi.single c (conjAction g X) := by
  classical
  funext b
  by_cases h : b = c
  · subst h
    simp [coordConj]
  · simp [coordConj, Pi.single_apply, h]
theorem gaugeTransform_expOfCoords (g : UnitQuaternion) (θ : TorusBond n → imaginaryQuaternions) :
    TorusFields.gaugeTransform (fun _ => g) (expOfCoords θ) = expOfCoords (coordConj g θ) := by
  funext x i
  simp only [TorusFields.gaugeTransform, expOfCoords, coordConj, ContinuousLinearMap.coe_pi', ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, LinearMap.coe_toContinuousLinearMap', expUnit_conjAction]
theorem hessianCoords_conj {H : GaugeTotal} (ht : IsGaugeTotalAt H n) (g : UnitQuaternion)
    (u v : TorusBond n → imaginaryQuaternions) :
    hessianCoords H n (coordConj g u) (coordConj g v) = hessianCoords H n u v := by
  have hC := contDiffAt_coordTotal (H := H) ht.contDiffAt_perturb
  have hev : coordTotal H n ∘ coordConj g =ᶠ[𝓝 0] coordTotal H n := by
    filter_upwards [tendsto_expOfCoords.eventually (ht.constant_gauge_invariant g)] with θ hθ
    simp only [Function.comp, coordTotal]
    rw [← gaugeTransform_expOfCoords]
    exact hθ
  simp only [hessianCoords]
  rw [← secondDeriv_comp_clm hC (coordConj g) u v, hev.fderiv.fderiv_eq]
def bondPairForm (Q : (TorusBond n → imaginaryQuaternions) →L[ℝ] (TorusBond n → imaginaryQuaternions) →L[ℝ] ℝ)
    (c c' : TorusBond n) :
    imaginaryQuaternions →ₗ[ℝ] imaginaryQuaternions →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun X X' => Q (Pi.single c X) (Pi.single c' X'))
    (fun a b X' => by simp [Pi.single_add])
    (fun r a X' => by simp [Pi.single_smul])
    (fun X a b => by simp [Pi.single_add])
    (fun r X a => by simp [Pi.single_smul])
theorem hessianAtTrivial_eq_inner_mul {H : GaugeTotal} (ht : IsGaugeTotalAt H n) (c c' : TorusBond n)
    (X X' : imaginaryQuaternions) :
    hessianAtTrivial H n c c' X X' =
      inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) * hessianAtTrivial H n c c' quaternionI quaternionI := by
  have h := bilin_eq_inner_mul_of_conj_invariant (bondPairForm (hessianCoords H n) c c') (fun g X X' => by
    have := hessianCoords_conj ht g (Pi.single c X) (Pi.single c' X')
    rw [coordConj_single, coordConj_single] at this
    exact this) X X'
  simp only [hessianAtTrivial]
  rw [mixedDeriv_eq_hessianCoords ht.contDiffAt_perturb, mixedDeriv_eq_hessianCoords ht.contDiffAt_perturb]
  exact h
end Fields
section Sums
theorem summable_pow_natAbs {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun z : ℤ => r ^ z.natAbs := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpDecaySum.summable_geomWeight <;> assumption
theorem summable_prod_pow_natAbs {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun h : Fin 4 → ℤ => ∏ i, r ^ (h i).natAbs := by
  classical
  have hg := summable_pow_natAbs h0 h1
  have hnn : ∀ z : ℤ, 0 ≤ r ^ z.natAbs := fun z => pow_nonneg h0 _
  refine summable_of_sum_le (c := (∑' z : ℤ, r ^ z.natAbs) ^ 4)
    (fun h => Finset.prod_nonneg fun i _ => hnn _) fun s => ?_
  set T : Finset ℤ := s.biUnion fun h => Finset.univ.image h with hT
  have hsub : s ⊆ Fintype.piFinset fun _ : Fin 4 => T := by
    intro h hh
    refine Fintype.mem_piFinset.mpr fun i => ?_
    exact Finset.mem_biUnion.mpr ⟨h, hh, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
  calc ∑ h ∈ s, ∏ i, r ^ (h i).natAbs
      ≤ ∑ h ∈ Fintype.piFinset fun _ : Fin 4 => T, ∏ i, r ^ (h i).natAbs :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun h _ _ =>
          Finset.prod_nonneg fun i _ => hnn _
    _ = ∏ _i : Fin 4, ∑ z ∈ T, r ^ z.natAbs := by
        rw [Finset.prod_univ_sum]
    _ ≤ ∏ _i : Fin 4, ∑' z : ℤ, r ^ z.natAbs := by
        refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun z _ => hnn z) fun i _ => ?_
        exact hg.sum_le_tsum _ fun z _ => hnn z
    _ = _ := by simp
def expPolyWeight (c : ℝ) (h : Fin 4 → ℤ) : ℝ :=
  Real.exp (-(c * offsetNorm h)) * (1 + (offsetNorm h : ℝ)) ^ 4
theorem expPolyWeight_nonneg (c : ℝ) (h : Fin 4 → ℤ) : 0 ≤ expPolyWeight c h := by
  unfold expPolyWeight
  positivity
theorem natAbs_le_offsetNorm (h : Fin 4 → ℤ) (i : Fin 4) : (h i).natAbs ≤ offsetNorm h := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
theorem summable_expPolyWeight {c : ℝ} (hc : 0 < c) : Summable (expPolyWeight c) := by
  set a : ℝ := c / 8 with ha
  have ha0 : 0 < a := by positivity
  set K : ℝ := 1 / a + 1 with hK
  have hK0 : 0 < K := by positivity
  set r : ℝ := Real.exp (-(c / 8)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    linarith [show 0 < c / 8 by positivity]
  refine Summable.of_nonneg_of_le (expPolyWeight_nonneg c) (fun h => ?_)
    ((summable_prod_pow_natAbs hr0 hr1).mul_left (K ^ 4))
  set s : ℝ := (offsetNorm h : ℝ) with hs
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  have h1 : 1 + s ≤ K * Real.exp (a * s) := by
    have h2 : 1 + a * s ≤ Real.exp (a * s) := by
      have := Real.add_one_le_exp (a * s)
      linarith
    have h3 : 1 + s ≤ K * (1 + a * s) := by
      rw [hK]
      have : (1 / a + 1) * (1 + a * s) = 1 / a + 1 + s + a * s := by
        field_simp
        ring
      rw [this]
      have : 0 < 1 / a := by positivity
      nlinarith [mul_nonneg ha0.le hs0]
    exact h3.trans (mul_le_mul_of_nonneg_left h2 hK0.le)
  have h2 : (1 + s) ^ 4 ≤ K ^ 4 * Real.exp (c / 2 * s) := by
    have h3 : (1 + s) ^ 4 ≤ (K * Real.exp (a * s)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) h1 4
    have h4 : (K * Real.exp (a * s)) ^ 4 = K ^ 4 * Real.exp (c / 2 * s) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      rw [ha]
      push_cast
      ring
    linarith
  have h3 : (∑ i, ((h i).natAbs : ℝ)) ≤ 4 * s := by
    have : ∀ i ∈ (Finset.univ : Finset (Fin 4)), ((h i).natAbs : ℝ) ≤ s := fun i _ => by
      rw [hs]
      exact_mod_cast natAbs_le_offsetNorm h i
    simpa using Finset.sum_le_sum this
  have h4 : ∏ i, r ^ (h i).natAbs = Real.exp (-(c / 8) * ∑ i, ((h i).natAbs : ℝ)) := by
    rw [hr, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h4]
  unfold expPolyWeight
  calc Real.exp (-(c * s)) * (1 + s) ^ 4
      ≤ Real.exp (-(c * s)) * (K ^ 4 * Real.exp (c / 2 * s)) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = K ^ 4 * Real.exp (-(c / 2 * s)) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
    _ ≤ K ^ 4 * Real.exp (-(c / 8) * ∑ i, ((h i).natAbs : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        nlinarith
theorem abs_coord_le_offsetNorm (z : Fin 4 → ℤ) (i : Fin 4) : |((z i : ℤ) : ℝ)| ≤ (offsetNorm z : ℝ) := by apply _root_.YangMills.Construction.BlockAverages.abs_coord_le_supNorm <;> assumption
end Sums
section Distances
def siteCoords {n : ℕ} (u : TorusSite n) : Fin 4 → ℤ := fun i => (u i).valMinAbs
variable {n : ℕ} [NeZero n]
theorem siteCoords_injective : Function.Injective (siteCoords (n := n)) := by
  intro u u' h
  funext i
  have := congrFun h i
  simp only [siteCoords] at this
  rw [← ZMod.coe_valMinAbs (u i), this, ZMod.coe_valMinAbs]
theorem supDist_eq (y x : TorusSite n) : supDist y x = offsetNorm (siteCoords (y - x)) := rfl
theorem supDist_comm (x y : TorusSite n) : supDist x y = supDist y x := by apply _root_.YangMills.Construction.TorusFields.supDist_comm <;> assumption
theorem supDist_zero_left (w : TorusSite n) : supDist (0 : TorusSite n) w = offsetNorm (siteCoords w) := by
  rw [supDist_comm, supDist_eq, sub_zero]
theorem siteCoords_siteOfInt {z : Fin 4 → ℤ} (h : 2 * offsetNorm z + 1 < n) :
    siteCoords (siteOfInt z : TorusSite n) = z := by
  funext i
  simp only [siteCoords, siteOfInt]
  have h1 := natAbs_le_offsetNorm z i
  refine (ZMod.valMinAbs_spec _ _).mpr ⟨rfl, ?_, ?_⟩ <;> omega
theorem supDist_triangle (x y z : TorusSite n) : supDist x z ≤ supDist x y + supDist y z := by apply _root_.YangMills.Construction.TorusFields.supDist_triangle <;> assumption
theorem supDist_sub_right (x x' y : TorusSite n) : supDist (x - y) (x' - y) = supDist x x' := by
  simp [supDist_eq]
theorem siteOfInt_add (a b : Fin 4 → ℤ) : (siteOfInt (a + b) : TorusSite n) = siteOfInt a + siteOfInt b := by apply _root_.YangMills.Construction.TorusFields.siteOfInt_add <;> assumption
theorem bondFrom_zero (c : LatticeBond) : bondFrom (0 : TorusSite n) c = (siteOfInt c.1, c.2) := by
  simp [bondFrom]
theorem supDist_le_supportDiam_first (c c' : TorusBond n) :
    supDist (0 : TorusSite n) c.1 ≤ supportDiam (0 : TorusSite n) ![c, c'] :=
  le_max_of_le_left (Finset.le_sup (f := fun l : Fin 2 => supDist (0 : TorusSite n) ((![c, c'] l).1))
    (Finset.mem_univ (0 : Fin 2)))
theorem supDist_le_supportDiam_pair (c c' : TorusBond n) :
    supDist c.1 c'.1 ≤ supportDiam (0 : TorusSite n) ![c, c'] :=
  le_max_of_le_right (le_trans
    (Finset.le_sup (f := fun l' : Fin 2 => supDist ((![c, c'] 0).1) ((![c, c'] l').1))
      (Finset.mem_univ (1 : Fin 2)))
    (Finset.le_sup (f := fun l : Fin 2 => Finset.univ.sup fun l' : Fin 2 =>
      supDist ((![c, c'] l).1) ((![c, c'] l').1)) (Finset.mem_univ (0 : Fin 2))))
end Distances
theorem inner_quaternionI_self : inner ℝ (quaternionI : ℍ[ℝ]) (quaternionI : ℍ[ℝ]) = 1 := by apply _root_.YangMills.DeltaSharedProofs.p500886 <;> assumption
theorem norm_quaternionI : ‖quaternionI‖ = 1 := by apply _root_.YangMills.SharedProofs.p9532 <;> assumption
section Torus
def densityAtOrigin (h : LocalDensity) : GaugeTotal := fun n V => h n 0 V
def originKernel (h : LocalDensity) (n : ℕ) (c c' : TorusBond n) (X X' : imaginaryQuaternions) : ℝ :=
  mixedDeriv (h n 0) (trivialField n) ![c, c'] ![X, X']
variable {n : ℕ} [NeZero n]
theorem hessianAtTrivial_eq_sum_kernel {h : LocalDensity} {H : GaugeTotal}
    (hs : IsTwiceDiffAlongBonds (densityAtOrigin h) n)
    (htr : ∀ y u : TorusSite n, ∀ᶠ V in 𝓝 (trivialField n), h n y (TorusFields.translate u V) = h n (y + u) V)
    (hH : IsTwiceDiffAlongBonds H n) (hden : ∀ᶠ V in 𝓝 (trivialField n), centeredDensityTotal h n V = H n V)
    (c c' : TorusBond n) (X X' : imaginaryQuaternions) :
    hessianAtTrivial H n c c' X X' =
      ∑ y : TorusSite n, originKernel h n (c.1 - y, c.2) (c'.1 - y, c'.2) X X' := by
  have hF : ContDiffAt ℝ 2 (coordTotal (densityAtOrigin h) n) 0 := contDiffAt_coordTotal hs
  have hFy : ∀ y : TorusSite n, ContDiffAt ℝ 2 (coordTotal (densityAtOrigin h) n ∘ coordShift y) 0 :=
    fun y => ContDiffAt.comp (0 : TorusBond n → imaginaryQuaternions) (by simpa using hF)
      (coordShift y).contDiff.contDiffAt
  have hev : coordTotal H n =ᶠ[𝓝 0] fun θ => ∑ y : TorusSite n,
      ((coordTotal (densityAtOrigin h) n ∘ coordShift y) θ - h n y (trivialField n)) := by
    have h1 := (tendsto_expOfCoords (n := n)).eventually hden
    have h2 := (tendsto_expOfCoords (n := n)).eventually (Filter.eventually_all.mpr fun y => htr 0 y)
    filter_upwards [h1, h2] with θ a1 a2
    simp only [coordTotal]
    rw [← a1]
    simp only [centeredDensityTotal, dif_neg (NeZero.ne n)]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [centered, Function.comp, coordTotal, densityAtOrigin, ← translate_expOfCoords, a2 y, zero_add]
  have hq : ∀ u v : TorusBond n → imaginaryQuaternions, hessianCoords H n u v =
      ∑ y : TorusSite n, hessianCoords (densityAtOrigin h) n (coordShift y u) (coordShift y v) := by
    intro u v
    simp only [hessianCoords]
    rw [hev.fderiv.fderiv_eq, secondDeriv_sum Finset.univ
      (fun (y : TorusSite n) θ => (coordTotal (densityAtOrigin h) n ∘ coordShift y) θ - h n y (trivialField n))
      (fun y _ => (hFy y).sub contDiffAt_const)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [fderiv_sub_const_fun, secondDeriv_comp_clm hF]
  simp only [hessianAtTrivial]
  rw [mixedDeriv_eq_hessianCoords hH, hq]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [coordShift_single, coordShift_single]
  exact (mixedDeriv_eq_hessianCoords hs _ _ _ _).symm
theorem hessianAtTrivial_decay {h : LocalDensity} {H : GaugeTotal} {M θ S : ℝ} (hM : 0 ≤ M) (hθ : 0 < θ)
    (hS : ∀ y : TorusSite n, ∑ x : TorusSite n, Real.exp (-(θ / 2 * supDist y x)) ≤ S)
    (hd : ∀ (c c' : TorusBond n) (X X' : imaginaryQuaternions), ‖X‖ = 1 → ‖X'‖ = 1 →
      |originKernel h n c c' X X'| ≤ M * Real.exp (-(θ * supportDiam (0 : TorusSite n) ![c, c'])))
    (hsum : ∀ (c c' : TorusBond n) (X X' : imaginaryQuaternions), hessianAtTrivial H n c c' X X' =
      ∑ y : TorusSite n, originKernel h n (c.1 - y, c.2) (c'.1 - y, c'.2) X X')
    (c c' : TorusBond n) (X X' : imaginaryQuaternions) (hX : ‖X‖ = 1) (hX' : ‖X'‖ = 1) :
    |hessianAtTrivial H n c c' X X'| ≤ M * S * Real.exp (-(θ / 2 * supDist c.1 c'.1)) := by
  rw [hsum]
  have hterm : ∀ y : TorusSite n, |originKernel h n (c.1 - y, c.2) (c'.1 - y, c'.2) X X'| ≤
      M * Real.exp (-(θ / 2 * supDist c.1 c'.1)) * Real.exp (-(θ / 2 * supDist c.1 y)) := by
    intro y
    refine (hd _ _ X X' hX hX').trans ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM
    have h1 : (supDist c.1 c'.1 : ℝ) ≤
        (supportDiam (0 : TorusSite n) ![(c.1 - y, c.2), (c'.1 - y, c'.2)] : ℝ) := by
      have := supDist_le_supportDiam_pair (n := n) (c.1 - y, c.2) (c'.1 - y, c'.2)
      simp only [supDist_sub_right] at this
      exact_mod_cast this
    have h2 : (supDist c.1 y : ℝ) ≤
        (supportDiam (0 : TorusSite n) ![(c.1 - y, c.2), (c'.1 - y, c'.2)] : ℝ) := by
      have h3 := supDist_le_supportDiam_first (n := n) (c.1 - y, c.2) (c'.1 - y, c'.2)
      have h4 : supDist (0 : TorusSite n) (c.1 - y) = supDist c.1 y := by
        rw [supDist_zero_left, supDist_eq]
      simp only [h4] at h3
      exact_mod_cast h3
    nlinarith
  calc |∑ y : TorusSite n, originKernel h n (c.1 - y, c.2) (c'.1 - y, c'.2) X X'|
      ≤ ∑ y : TorusSite n, |originKernel h n (c.1 - y, c.2) (c'.1 - y, c'.2) X X'| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y : TorusSite n, M * Real.exp (-(θ / 2 * supDist c.1 c'.1)) * Real.exp (-(θ / 2 * supDist c.1 y)) :=
        Finset.sum_le_sum fun y _ => hterm y
    _ = M * Real.exp (-(θ / 2 * supDist c.1 c'.1)) * ∑ y : TorusSite n, Real.exp (-(θ / 2 * supDist c.1 y)) := by
        rw [Finset.mul_sum]
    _ ≤ M * Real.exp (-(θ / 2 * supDist c.1 c'.1)) * S :=
        mul_le_mul_of_nonneg_left (hS c.1) (mul_nonneg hM (Real.exp_pos _).le)
    _ = _ := by ring
def latticeKernel (h : LocalDensity) (c c' : LatticeBond) (m : ℕ) (u : Fin 4 → ℤ) : ℝ :=
  Function.extend (siteCoords (n := m))
    (fun w => originKernel h m (siteOfInt c.1 + w, c.2) (siteOfInt c'.1 + w, c'.2) quaternionI quaternionI) 0 u
theorem latticeKernel_siteCoords (h : LocalDensity) (c c' : LatticeBond) (w : TorusSite n) :
    latticeKernel h c c' n (siteCoords w) =
      originKernel h n (siteOfInt c.1 + w, c.2) (siteOfInt c'.1 + w, c'.2) quaternionI quaternionI :=
  siteCoords_injective.extend_apply _ _ _
theorem latticeKernel_of_not_mem_range (h : LocalDensity) (c c' : LatticeBond) {u : Fin 4 → ℤ}
    (hu : ¬ ∃ w : TorusSite n, siteCoords w = u) : latticeKernel h c c' n u = 0 := by
  unfold latticeKernel
  rw [Function.extend_apply' _ _ _ hu]
  rfl
theorem tsum_latticeKernel (h : LocalDensity) (c c' : LatticeBond) :
    ∑' u, latticeKernel h c c' n u =
      ∑ w : TorusSite n, originKernel h n (siteOfInt c.1 + w, c.2) (siteOfInt c'.1 + w, c'.2)
        quaternionI quaternionI := by
  have hsup : Function.support (latticeKernel h c c' n) ⊆ Set.range (siteCoords (n := n)) := by
    intro u hu
    by_contra hc
    exact hu (latticeKernel_of_not_mem_range h c c' hc)
  rw [← siteCoords_injective.tsum_eq hsup, tsum_fintype]
  exact Finset.sum_congr rfl fun w _ => latticeKernel_siteCoords h c c' w
theorem norm_latticeKernel_le {h : LocalDensity} {M θ : ℝ} (hM : 0 ≤ M) (hθ : 0 < θ)
    (hd : ∀ c c' : TorusBond n, |originKernel h n c c' quaternionI quaternionI| ≤
      M * Real.exp (-(θ * supportDiam (0 : TorusSite n) ![c, c']))) (c c' : LatticeBond)
    (hn : 2 * offsetNorm c.1 + 1 < n) (u : Fin 4 → ℤ) :
    ‖latticeKernel h c c' n u‖ ≤ M * Real.exp (θ * offsetNorm c.1) * expPolyWeight θ u := by
  by_cases hu : ∃ w : TorusSite n, siteCoords w = u
  · obtain ⟨w, rfl⟩ := hu
    rw [latticeKernel_siteCoords, Real.norm_eq_abs]
    set sd : ℕ := supportDiam (0 : TorusSite n) ![(siteOfInt c.1 + w, c.2), (siteOfInt c'.1 + w, c'.2)] with hsd
    have h1 : offsetNorm (siteCoords w) ≤ sd + offsetNorm c.1 := by
      have e1 : supDist (0 : TorusSite n) (siteOfInt c.1 + w) ≤ sd :=
        supDist_le_supportDiam_first (n := n) (siteOfInt c.1 + w, c.2) (siteOfInt c'.1 + w, c'.2)
      have e2 := supDist_triangle (0 : TorusSite n) (siteOfInt c.1 + w) w
      have e3 : supDist (siteOfInt c.1 + w) w = offsetNorm c.1 := by
        rw [supDist_eq, add_sub_cancel_right, siteCoords_siteOfInt hn]
      rw [supDist_zero_left w, e3] at e2
      omega
    have h2 : (offsetNorm (siteCoords w) : ℝ) ≤ (sd : ℝ) + (offsetNorm c.1 : ℝ) := by
      exact_mod_cast h1
    have h3 : (1 : ℝ) ≤ (1 + (offsetNorm (siteCoords w) : ℝ)) ^ 4 := one_le_pow₀ (by linarith)
    refine (hd _ _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hM
    unfold expPolyWeight
    calc Real.exp (-(θ * (sd : ℝ)))
        ≤ Real.exp (θ * offsetNorm c.1 + -(θ * (offsetNorm (siteCoords w) : ℝ))) :=
          Real.exp_le_exp.mpr (by nlinarith)
      _ = Real.exp (θ * offsetNorm c.1) * Real.exp (-(θ * (offsetNorm (siteCoords w) : ℝ))) :=
          Real.exp_add _ _
      _ ≤ Real.exp (θ * offsetNorm c.1) * (Real.exp (-(θ * (offsetNorm (siteCoords w) : ℝ))) *
            (1 + (offsetNorm (siteCoords w) : ℝ)) ^ 4) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (Real.exp_pos _).le h3) (Real.exp_pos _).le
  · rw [latticeKernel_of_not_mem_range h c c' hu, norm_zero]
    exact mul_nonneg (mul_nonneg hM (Real.exp_pos _).le) (expPolyWeight_nonneg θ u)
end Torus
theorem claim_of_expDecayTorusSumBounded (hsd : ExpDecayTorusSumBounded) : Claim := by
  intro h H hl ht hden
  obtain ⟨M₀, θ, hθ, hdec⟩ := hl.kernel_decay
  set M : ℝ := |M₀| with hMdef
  have hM : 0 ≤ M := abs_nonneg _
  obtain ⟨S, hS0, hS⟩ := hsd (θ / 2) (half_pos hθ)
  set q : LatticeBond → LatticeBond → ℝ := fun c c' => secondDerivLimit h c c' quaternionI quaternionI with hqdef
  have tend : ∀ c c' : LatticeBond,
      Tendsto (fun m => originKernel h m (bondFrom 0 c) (bondFrom 0 c') quaternionI quaternionI) atTop
        (𝓝 (q c c')) := by
    intro c c'
    obtain ⟨v, hv⟩ := hl.tendsto c c' quaternionI quaternionI
    have : q c c' = v := hv.limUnder_eq
    rw [this]
    exact hv
  have hgood : ∀ᶠ m : ℕ in atTop, 0 < m ∧ IsTwiceDiffAlongBonds (densityAtOrigin h) m ∧
      (∀ y u : TorusSite m, ∀ᶠ V in 𝓝 (trivialField m), h m y (TorusFields.translate u V) = h m (y + u) V) ∧
      IsGaugeTotalAt H m ∧ (∀ᶠ V in 𝓝 (trivialField m), centeredDensityTotal h m V = H m V) ∧
      (∀ (c c' : TorusBond m) (X X' : imaginaryQuaternions), ‖X‖ = 1 → ‖X'‖ = 1 →
        |originKernel h m c c' X X'| ≤
        M * Real.exp (-(θ * supportDiam (0 : TorusSite m) ![c, c']))) := by
    filter_upwards [eventually_gt_atTop 0, hl.contDiffAt, hl.translation_invariant, ht, hden, hdec] with
      m h0 a1 a2 a3 a4 a5
    refine ⟨h0, a1 0, a2, a3, a4, fun c c' X X' hX hX' => ?_⟩
    refine (a5 c c' X X' hX hX').trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
  set K : LatticeBond → LatticeBond → ℝ := fun c c' =>
    ∑' u : Fin 4 → ℤ, q (c.1 + u, c.2) (c'.1 + u, c'.2) with hKdef
  have tendE : ∀ c c' : LatticeBond, Tendsto
      (fun m => hessianAtTrivial H m (bondFrom 0 c) (bondFrom 0 c') quaternionI quaternionI) atTop
        (𝓝 (K c c')) := by
    intro c c'
    have htan : Tendsto (fun m => ∑' u, latticeKernel h c c' m u) atTop (𝓝 (K c c')) := by
      refine tendsto_tsum_of_dominated_convergence
        (bound := fun u => M * Real.exp (θ * offsetNorm c.1) * expPolyWeight θ u)
        ((summable_expPolyWeight hθ).mul_left _) ?_ ?_
      · intro u
        refine (tend (c.1 + u, c.2) (c'.1 + u, c'.2)).congr' ?_
        filter_upwards [hgood, eventually_gt_atTop (2 * offsetNorm u + 1)] with m ⟨h0, _⟩ b1
        haveI : NeZero m := ⟨h0.ne'⟩
        have e1 := latticeKernel_siteCoords h c c' (siteOfInt u : TorusSite m)
        rw [siteCoords_siteOfInt b1] at e1
        rw [e1, bondFrom_zero, bondFrom_zero, siteOfInt_add, siteOfInt_add]
      · filter_upwards [hgood, eventually_gt_atTop (2 * offsetNorm c.1 + 1)] with
          m ⟨h0, _, _, _, _, a5⟩ b1 u
        haveI : NeZero m := ⟨h0.ne'⟩
        exact norm_latticeKernel_le hM hθ (fun c c' => a5 c c' _ _ norm_quaternionI norm_quaternionI) c c' b1 u
    refine htan.congr' ?_
    filter_upwards [hgood] with m ⟨h0, a1, a2, a3, a4, _⟩
    haveI : NeZero m := ⟨h0.ne'⟩
    rw [tsum_latticeKernel, hessianAtTrivial_eq_sum_kernel a1 a2 a3.contDiffAt_perturb a4,
      bondFrom_zero, bondFrom_zero]
    refine Fintype.sum_equiv (Equiv.neg _) _ _ fun w => ?_
    simp [sub_neg_eq_add]
  have hdecay : ∀ᶠ m : ℕ in atTop, ∀ (c c' : TorusBond m) (X X' : imaginaryQuaternions), ‖X‖ = 1 → ‖X'‖ = 1 →
      |hessianAtTrivial H m c c' X X'| ≤ M * S * Real.exp (-(θ / 2 * supDist c.1 c'.1)) := by
    filter_upwards [hgood] with m ⟨h0, a1, a2, a3, a4, a5⟩ c c' X X' hX hX'
    haveI : NeZero m := ⟨h0.ne'⟩
    exact hessianAtTrivial_decay hM hθ (fun y => hS m y) a5
      (hessianAtTrivial_eq_sum_kernel a1 a2 a3.contDiffAt_perturb a4) c c' X X' hX hX'
  have hloc : IsLocalGaugeTotal atTop H K := by
    refine ⟨ht, ⟨M * S, θ / 2, half_pos hθ, hdecay⟩, fun c c' X X' => ?_⟩
    refine ((tendE c c').const_mul _).congr' ?_
    filter_upwards [hgood] with m ⟨h0, _, _, a3, _, _⟩
    haveI : NeZero m := ⟨h0.ne'⟩
    exact (hessianAtTrivial_eq_inner_mul a3 _ _ X X').symm
  have hKb : ∀ z : Fin 4 → ℤ, |K (0, secondAxis) (z, secondAxis)| ≤
      M * S * Real.exp (-(θ / 2 * offsetNorm z)) := by
    intro z
    refine le_of_tendsto (tendE _ _).abs ?_
    filter_upwards [hgood, hdecay, eventually_gt_atTop (2 * offsetNorm z + 1)] with
      m ⟨h0, _⟩ a6 b1
    haveI : NeZero m := ⟨h0.ne'⟩
    have e1 := a6 (bondFrom 0 ((0 : Fin 4 → ℤ), secondAxis)) (bondFrom 0 (z, secondAxis))
      quaternionI quaternionI norm_quaternionI norm_quaternionI
    have h0' : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite m) = 0 := by
      funext i
      simp [siteOfInt]
    rw [bondFrom_zero, bondFrom_zero] at e1 ⊢
    simp only [h0', supDist_zero_left, siteCoords_siteOfInt b1] at e1
    show |hessianAtTrivial H m (siteOfInt (0 : Fin 4 → ℤ), secondAxis) (siteOfInt z, secondAxis)
      quaternionI quaternionI| ≤ _
    rw [h0']
    exact e1
  have hsum : Summable (secondMomentTerm K) := by
    refine Summable.of_norm_bounded ((summable_expPolyWeight (half_pos hθ)).mul_left (M * S)) fun z => ?_
    rw [Real.norm_eq_abs]
    simp only [secondMomentTerm, abs_mul, abs_neg, abs_pow]
    have hb := hKb z
    have hz := abs_coord_le_offsetNorm z 0
    set s : ℝ := (offsetNorm z : ℝ) with hs
    have hs0 : 0 ≤ s := Nat.cast_nonneg _
    have h2 : |((z 0 : ℤ) : ℝ)| ^ 2 ≤ (1 + s) ^ 4 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hz 2
      nlinarith [mul_nonneg hs0 hs0, mul_nonneg (mul_nonneg hs0 hs0) hs0,
        mul_nonneg (mul_nonneg hs0 hs0) (mul_nonneg hs0 hs0)]
    have hhalf : |(1 / 2 : ℝ)| = 1 / 2 := abs_of_pos (by norm_num)
    rw [hhalf]
    have hK0 := abs_nonneg (K (0, secondAxis) (z, secondAxis))
    have hpow0 : 0 ≤ |((z 0 : ℤ) : ℝ)| ^ 2 := by positivity
    unfold expPolyWeight
    rw [← hs]
    calc 1 / 2 * |K (0, secondAxis) (z, secondAxis)| * |((z 0 : ℤ) : ℝ)| ^ 2
        ≤ |K (0, secondAxis) (z, secondAxis)| * |((z 0 : ℤ) : ℝ)| ^ 2 := by nlinarith
      _ ≤ (M * S * Real.exp (-(θ / 2 * s))) * (1 + s) ^ 4 :=
          mul_le_mul hb h2 hpow0 (le_trans hK0 hb)
      _ = _ := by ring
  exact ⟨_, K, hloc, hsum.hasSum⟩
end YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient
end
