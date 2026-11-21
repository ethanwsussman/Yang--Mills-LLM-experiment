import YangMills.Construction.Averaging.EverySmallRadiusServesProof
import Reconstruction.ComplexAnalysis.ProductAndHalfPlaneIdentity
import Reconstruction.MinkowskiSpace.AcrossTheSpacelikePoints
import Reconstruction.MinkowskiSpace.ConeTubeAndLorentzGroupProof
import Reconstruction.MinkowskiSpace.LorentzInvarianceOfTheVacuumFunctions
import Reconstruction.MinkowskiSpace.ProductsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
open Filter Set Matrix
open scoped Topology
noncomputable section
namespace YangMills.Construction.FieldForms.SpacelikeExtension
open Coordinates MinkowskiSpace WightmanTheory MinkowskiSpace.ConeTubeLorentz
variable {b : ℕ}
theorem mem_futureTube_iff {ζ : ComplexVec4} : ζ ∈ futureTube ↔ 0 < tubeGap ζ := Iff.rfl
theorem mem_tubeTuples_iff {ζ : Fin b → ComplexVec4} :
    ζ ∈ tubeTuples b ↔ ∀ k, 0 < tubeGap (ζ k) := by
  simp only [tubeTuples, Set.mem_pi, Set.mem_univ, true_implies, mem_futureTube_iff]
theorem continuous_rePart : Continuous MinkowskiSpace.rePart :=
  continuous_pi fun μ => Complex.continuous_re.comp (continuous_apply μ)
theorem continuous_imPart : Continuous MinkowskiSpace.imPart :=
  continuous_pi fun μ => Complex.continuous_im.comp (continuous_apply μ)
theorem continuous_spaceNorm : Continuous spaceNorm := by apply _root_.YangMills.Construction.MinkowskiSpace.ConeTubeLorentz.continuous_spaceNorm <;> assumption
theorem continuous_spacePart : Continuous (spacePart : RealVec4 → Fin 3 → ℝ) :=
  continuous_pi fun i => continuous_apply i.succ
theorem continuous_tubeGap : Continuous tubeGap :=
  ((continuous_apply 0).comp continuous_imPart).sub
    (continuous_spaceNorm.comp (continuous_spacePart.comp continuous_imPart))
theorem continuous_l1Norm : Continuous l1Norm :=
  (((((continuous_apply 0).comp continuous_rePart).abs).add
    (continuous_spaceNorm.comp (continuous_spacePart.comp continuous_rePart))).add
    (((continuous_apply 0).comp continuous_imPart).abs)).add
    (continuous_spaceNorm.comp (continuous_spacePart.comp continuous_imPart))
theorem isOpen_futureTube : IsOpen futureTube :=
  isOpen_lt continuous_const continuous_tubeGap
theorem isOpen_tubeTuples : IsOpen (tubeTuples b) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_futureTube
theorem spaceNorm_nonneg (v : Fin 3 → ℝ) : 0 ≤ spaceNorm v := Real.sqrt_nonneg _
theorem l1Norm_pos_of_mem_futureTube {ζ : ComplexVec4} (h : ζ ∈ futureTube) : 0 < l1Norm ζ := by
  have h1 : 0 < tubeGap ζ := h
  have h2 := spaceNorm_nonneg (spacePart (MinkowskiSpace.imPart ζ))
  have h3 : 0 < MinkowskiSpace.imPart ζ 0 := by
    unfold tubeGap coneGap at h1
    linarith
  unfold l1Norm
  linarith [abs_nonneg (MinkowskiSpace.rePart ζ 0),
    spaceNorm_nonneg (spacePart (MinkowskiSpace.rePart ζ)),
    le_abs_self (MinkowskiSpace.imPart ζ 0)]
theorem maxBoostAngle_le_one (j : Fin b) (ζ : Fin b → ComplexVec4) :
    maxBoostAngle j ζ ≤ 1 := by
  unfold maxBoostAngle
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl
theorem maxBoostAngle_le_gap_ratio {j k : Fin b} (ζ : Fin b → ComplexVec4) (hk : k ≠ j) :
    maxBoostAngle j ζ ≤ tubeGap (ζ k) / (2 * l1Norm (ζ k)) := by
  have hmem : k ∈ Finset.univ.erase j := Finset.mem_erase.2 ⟨hk, Finset.mem_univ _⟩
  unfold maxBoostAngle
  rw [dif_pos ⟨k, hmem⟩]
  exact (min_le_right _ _).trans (Finset.inf'_le _ hmem)
theorem le_maxBoostAngle {j : Fin b} {ζ : Fin b → ComplexVec4} {a : ℝ} (ha : a ≤ 1)
    (h : ∀ k, k ≠ j → a ≤ tubeGap (ζ k) / (2 * l1Norm (ζ k))) :
    a ≤ maxBoostAngle j ζ := by
  unfold maxBoostAngle
  split_ifs with hne
  · exact le_min ha (Finset.le_inf' _ _ fun k hk => h k (Finset.ne_of_mem_erase hk))
  · exact ha
theorem maxBoostAngle_pos {j : Fin b} {ζ : Fin b → ComplexVec4}
    (h : ζ ∈ spacelikeSlab j) : 0 < maxBoostAngle j ζ := by
  unfold maxBoostAngle
  split_ifs with hne
  · refine lt_min one_pos ((Finset.lt_inf'_iff _).2 fun k hk => ?_)
    have hk' := h.2 k (Finset.ne_of_mem_erase hk)
    exact div_pos hk' (mul_pos two_pos (l1Norm_pos_of_mem_futureTube hk'))
  · exact one_pos
theorem imagTimeShift_zero : imagTimeShift 0 = 0 := by
  funext μ
  simp [imagTimeShift, toComplex]
theorem tubeGap_boost_of_ne (hm : TubeGapUnderImagBoosts) {ζ : ComplexVec4}
    (hζ : ζ ∈ futureTube) (v : unitSphere3) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ha : a ≤ tubeGap ζ / (2 * l1Norm ζ)) :
    tubeGap ζ / 2 ≤ tubeGap (boostMatrix v (Complex.I * (a : ℂ)) *ᵥ ζ) := by
  have h := hm.1 a ha0 ha1 v ζ
  have hn := l1Norm_pos_of_mem_futureTube hζ
  have h2 : a * l1Norm ζ ≤ tubeGap ζ / 2 := by
    rw [le_div_iff₀ (by positivity)] at ha
    linarith
  linarith
theorem tubeGap_boost_shifted (hm : TubeGapUnderImagBoosts) (x : RealVec4) {ε a : ℝ} (hε : 0 ≤ ε)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (v : unitSphere3) :
    tubeGap (boostMatrix v (Complex.I * (a : ℂ)) *ᵥ (toComplex x + imagTimeShift ε)) =
      ε * Real.cos a + Real.sin a * ((v : Fin 3 → ℝ) ⬝ᵥ spacePart x - |x 0|) :=
  (hm.2 x ε a hε ha0 ha1 v).2
theorem tubeGap_boost_real (hm : TubeGapUnderImagBoosts) (x : RealVec4) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (v : unitSphere3) :
    tubeGap (boostMatrix v (Complex.I * (a : ℂ)) *ᵥ toComplex x) =
      Real.sin a * ((v : Fin 3 → ℝ) ⬝ᵥ spacePart x - |x 0|) := by
  have h := tubeGap_boost_shifted hm x le_rfl ha0 ha1 v
  rw [imagTimeShift_zero, add_zero] at h
  simpa using h
theorem slab_eq_toComplex {j : Fin b} {ζ : Fin b → ComplexVec4} (h : ζ ∈ spacelikeSlab j) :
    ζ j = toComplex (MinkowskiSpace.rePart (ζ j)) := by
  obtain ⟨⟨x, _, hxe⟩, _⟩ := h
  rw [← hxe]
  funext μ
  simp [MinkowskiSpace.rePart, toComplex]
theorem slab_time_lt_spaceNorm {j : Fin b} {ζ : Fin b → ComplexVec4} (h : ζ ∈ spacelikeSlab j) :
    |MinkowskiSpace.rePart (ζ j) 0| < spaceNorm (spacePart (MinkowskiSpace.rePart (ζ j))) :=
  (isSpacelikeVec_iff _).1 (rePart_mem_spacelikeSet_of_mem_spacelikeSlab h)
theorem unitDir_dot_spacePart {j : Fin b} {ζ : Fin b → ComplexVec4} (h : ζ ∈ spacelikeSlab j) :
    ((spacelikeUnitDir j ζ h : unitSphere3) : Fin 3 → ℝ) ⬝ᵥ
        spacePart (MinkowskiSpace.rePart (ζ j)) =
      spaceNorm (spacePart (MinkowskiSpace.rePart (ζ j))) := by
  set x := MinkowskiSpace.rePart (ζ j) with hx
  have hN : 0 < spaceNorm (spacePart x) :=
    lt_of_le_of_lt (abs_nonneg _) (slab_time_lt_spaceNorm h)
  have hs : ∑ i, spacePart x i ^ 2 = spaceNorm (spacePart x) ^ 2 :=
    (Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)).symm
  change ∑ i, (spacePart x i / spaceNorm (spacePart x)) * spacePart x i = _
  have h1 : ∀ i, (spacePart x i / spaceNorm (spacePart x)) * spacePart x i =
      spacePart x i ^ 2 / spaceNorm (spacePart x) := fun i => by ring
  simp only [h1]
  rw [← Finset.sum_div, hs]
  field_simp
theorem imagBoost_mem_tubeTuples (hm : TubeGapUnderImagBoosts) {j : Fin b}
    {ζ : Fin b → ComplexVec4} (h : ζ ∈ spacelikeSlab j) (v : unitSphere3)
    (hv : |MinkowskiSpace.rePart (ζ j) 0| <
      (v : Fin 3 → ℝ) ⬝ᵥ spacePart (MinkowskiSpace.rePart (ζ j)))
    {a : ℝ} (ha0 : 0 < a) (ha : a ≤ maxBoostAngle j ζ) :
    imagBoostTuple v a ζ ∈ tubeTuples b := by
  have ha1 := ha.trans (maxBoostAngle_le_one j ζ)
  rw [mem_tubeTuples_iff]
  intro k
  by_cases hk : k = j
  · subst hk
    change 0 < tubeGap (boostMatrix v (Complex.I * (a : ℂ)) *ᵥ ζ k)
    rw [slab_eq_toComplex h, tubeGap_boost_real hm _ ha0.le ha1]
    have hs := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_gt_three])
    have := sub_pos.2 hv
    simpa [MinkowskiSpace.rePart, toComplex] using mul_pos hs this
  · have h1 := h.2 k hk
    have h2 := tubeGap_boost_of_ne hm h1 v ha0.le ha1
      (ha.trans (maxBoostAngle_le_gap_ratio ζ hk))
    have h3 : 0 < tubeGap (ζ k) := h1
    exact lt_of_lt_of_le (by linarith) h2
theorem contDiffOn_mvPolynomial_aeval {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (f : Fin n → ℝ → ℂ)
    (s : Set ℝ) (hf : ∀ i, ContDiffOn ℝ 1 (f i) s) :
    ContDiffOn ℝ 1 (fun t => MvPolynomial.aeval (fun i => f i t) P) s := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiffOn_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (hf i)
def IsConstantAlongLorentzPaths (W : (Fin b → ComplexVec4) → ℂ) : Prop :=
  ∀ (Λ : ℝ → ComplexMat4) (ζ : Fin b → ComplexVec4),
    (∀ t ∈ Set.Icc (0 : ℝ) 1, Λ t ∈ lorentzGroupC) →
    (∀ i j, ContDiffOn ℝ 1 (fun t => Λ t i j) (Set.Icc (0 : ℝ) 1)) →
    (∀ t ∈ Set.Icc (0 : ℝ) 1, mulVecTuple (Λ t) ζ ∈ tubeTuples b) →
      W (mulVecTuple (Λ 1) ζ) = W (mulVecTuple (Λ 0) ζ)
theorem contDiffOn_boostParams (raw : ℝ → Fin 3 → ℝ) (α : ℝ → ℝ) (s : Set ℝ)
    (hs : ∀ i, ContDiffOn ℝ 1 (fun t => raw t i) s) (hα : ContDiffOn ℝ 1 α s) (i : Fin 5) :
    ContDiffOn ℝ 1 (fun t => (![Complex.cosh (Complex.I * (α t : ℂ)),
      Complex.sinh (Complex.I * (α t : ℂ)), ((raw t 0 : ℝ) : ℂ), ((raw t 1 : ℝ) : ℂ),
      ((raw t 2 : ℝ) : ℂ)] : Fin 5 → ℂ) i) s := by
  have hc : ∀ {g : ℝ → ℝ}, ContDiffOn ℝ 1 g s → ContDiffOn ℝ 1 (fun t => ((g t : ℝ) : ℂ)) s :=
    fun hg => Complex.ofRealCLM.contDiff.comp_contDiffOn hg
  have hI : ContDiffOn ℝ 1 (fun t => Complex.I * (α t : ℂ)) s := contDiffOn_const.mul (hc hα)
  fin_cases i
  · exact (Complex.contDiff_cosh.restrict_scalars ℝ).comp_contDiffOn hI
  · exact (Complex.contDiff_sinh.restrict_scalars ℝ).comp_contDiffOn hI
  · exact hc (hs 0)
  · exact hc (hs 1)
  · exact hc (hs 2)
theorem eq_of_boost_path (hB : BoostsAndRotations) {W : (Fin b → ComplexVec4) → ℂ}
    (hP : IsConstantAlongLorentzPaths W) (raw : ℝ → Fin 3 → ℝ) (α : ℝ → ℝ)
    (hraw : ∀ t ∈ Set.Icc (0 : ℝ) 1, raw t ∈ unitSphere3)
    (hs : ∀ i, ContDiffOn ℝ 1 (fun t => raw t i) (Set.Icc (0 : ℝ) 1))
    (hα : ContDiffOn ℝ 1 α (Set.Icc (0 : ℝ) 1)) (ζ : Fin b → ComplexVec4)
    (ht : ∀ (t : ℝ) (h : t ∈ Set.Icc (0 : ℝ) 1),
      mulVecTuple (boostMatrix ⟨raw t, hraw t h⟩ (Complex.I * (α t : ℂ))) ζ ∈ tubeTuples b)
    (v₀ v₁ : unitSphere3) (h0 : raw 0 = v₀) (h1 : raw 1 = v₁) :
    W (mulVecTuple (boostMatrix v₁ (Complex.I * (α 1 : ℂ))) ζ) =
      W (mulVecTuple (boostMatrix v₀ (Complex.I * (α 0 : ℂ))) ζ) := by
  obtain ⟨hL, -, ⟨P, hPoly⟩, -⟩ := hB
  let Λ : ℝ → ComplexMat4 := fun t => Matrix.of fun μ ν =>
    MvPolynomial.aeval (![Complex.cosh (Complex.I * (α t : ℂ)),
      Complex.sinh (Complex.I * (α t : ℂ)), ((raw t 0 : ℝ) : ℂ), ((raw t 1 : ℝ) : ℂ),
      ((raw t 2 : ℝ) : ℂ)] : Fin 5 → ℂ) (P μ ν)
  have hΛ : ∀ (t : ℝ) (h : t ∈ Set.Icc (0 : ℝ) 1),
      Λ t = boostMatrix ⟨raw t, hraw t h⟩ (Complex.I * (α t : ℂ)) := by
    intro t h
    ext μ ν
    exact (hPoly ⟨raw t, hraw t h⟩ _ μ ν).symm
  have m0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have m1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have e0 : Λ 0 = boostMatrix v₀ (Complex.I * (α 0 : ℂ)) := by
    rw [hΛ 0 m0]
    congr 1
    exact Subtype.ext h0
  have e1 : Λ 1 = boostMatrix v₁ (Complex.I * (α 1 : ℂ)) := by
    rw [hΛ 1 m1]
    congr 1
    exact Subtype.ext h1
  rw [← e0, ← e1]
  refine hP Λ ζ (fun t h => ?_) (fun μ ν => ?_) (fun t h => ?_)
  · rw [hΛ t h]
    exact hL _ _
  · exact contDiffOn_mvPolynomial_aeval (P μ ν) _ _ (contDiffOn_boostParams raw α _ hs hα)
  · rw [hΛ t h]
    exact ht t h
def tupleCoords (ζ : Fin b → ComplexVec4) : ComplexCoordinates (b * 4) :=
  fun i => ζ (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
theorem coordsToTuple_tupleCoords (ζ : Fin b → ComplexVec4) :
    coordsToTuple (tupleCoords ζ) = ζ := by
  funext k μ
  simp [coordsToTuple, tupleCoords]
theorem continuous_tupleCoords : Continuous (tupleCoords : (Fin b → ComplexVec4) → _) :=
  continuous_pi fun _ => (continuous_apply _).comp (continuous_apply _)
theorem continuous_coordsToTuple :
    Continuous (coordsToTuple : ComplexCoordinates (b * 4) → Fin b → ComplexVec4) :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_apply _
def tupleCoordsLinear : (Fin b → ComplexVec4) →ₗ[ℂ] ComplexCoordinates (b * 4) where
  toFun := tupleCoords
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def coordsToTupleLinear : ComplexCoordinates (b * 4) →ₗ[ℂ] (Fin b → ComplexVec4) where
  toFun := coordsToTuple
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem isHolomorphicIn_linearMap {N N' : ℕ}
    (L : ComplexCoordinates N →ₗ[ℂ] ComplexCoordinates N')
    {O : Set (ComplexCoordinates N)} (hO : IsOpen O) : ComplexCoordinates.IsHolomorphicIn O L := by apply _root_.YangMills.Construction.Averaging.SmallRadiusProof.isHolomorphicIn_of_linearMap <;> assumption
theorem isHolomorphicIn_comp (hS : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {N N' : ℕ} {O : Set (ComplexCoordinates N)} {O' : Set (ComplexCoordinates N')}
    {f : ComplexCoordinates N → ComplexCoordinates 1} {g : ComplexCoordinates N' → ComplexCoordinates N}
    (hf : ComplexCoordinates.IsHolomorphicIn O f) (hg : ComplexCoordinates.IsHolomorphicIn O' g)
    (hm : MapsTo g O' O) : ComplexCoordinates.IsHolomorphicIn O' (f ∘ g) :=
  ((hS.1 N O hf.1).1 1 f hf).2.2.2.1 N' O' g hg hm
theorem isHolomorphicIn_sub {N : ℕ} {O : Set (ComplexCoordinates N)}
    {f g : ComplexCoordinates N → ComplexCoordinates 1}
    (hf : ComplexCoordinates.IsHolomorphicIn O f) (hg : ComplexCoordinates.IsHolomorphicIn O g) :
    ComplexCoordinates.IsHolomorphicIn O (f - g) := by
  refine ⟨hf.1, hf.2.1.sub hg.2.1, fun a ha i => ?_⟩
  filter_upwards [hf.2.2 a ha i, hg.2.2 a ha i] with ζ h1 h2
  exact h1.sub h2
theorem continuousOn_tubeTuples_of_holomorphic {W : (Fin b → ComplexVec4) → ℂ}
    (hW : IsHolomorphicOnTube W) : ContinuousOn W (tubeTuples b) := by
  have h := hW.2.1
  have h1 : ContinuousOn (fun z => W (coordsToTuple z))
      (coordsToTuple ⁻¹' tubeTuples b) := (continuousOn_pi.1 h) 0
  have h2 := h1.comp (continuous_tupleCoords.continuousOn (s := tubeTuples b))
    (fun ζ hζ => by
      change coordsToTuple (tupleCoords ζ) ∈ tubeTuples b
      rwa [coordsToTuple_tupleCoords])
  refine h2.congr fun ζ _ => ?_
  simp [coordsToTuple_tupleCoords]
theorem isHolomorphicIn_comp_linearMap
    (hS : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {W : (Fin b → ComplexVec4) → ℂ} (hW : IsHolomorphicOnTube W)
    (L : (Fin b → ComplexVec4) →ₗ[ℂ] (Fin b → ComplexVec4)) {U : Set (Fin b → ComplexVec4)}
    (hU : IsOpen U) (hL : ∀ ζ ∈ U, L ζ ∈ tubeTuples b) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) (coordsToTuple ⁻¹' U)
      (fun z _ => W (L (coordsToTuple z))) := by
  have hO : IsOpen (coordsToTuple ⁻¹' U : Set (ComplexCoordinates (b * 4))) :=
    hU.preimage continuous_coordsToTuple
  have hg := isHolomorphicIn_linearMap (tupleCoordsLinear ∘ₗ L ∘ₗ coordsToTupleLinear) hO
  have h := isHolomorphicIn_comp hS hW hg (fun z hz => by
    change coordsToTuple (tupleCoords (L (coordsToTuple z))) ∈ tubeTuples b
    rw [coordsToTuple_tupleCoords]
    exact hL _ hz)
  convert h using 1
  funext z _
  change _ = W (coordsToTuple (tupleCoords (L (coordsToTuple z))))
  rw [coordsToTuple_tupleCoords]
theorem coordinatesProdHomeomorph_symm_eq (a a' : ℕ) (z : ComplexCoordinates (a + a')) :
    (ComplexManifolds.coordinatesProdHomeomorph a a').symm z =
      (fun i => z (Fin.castAdd a' i), fun i => z (Fin.natAdd a i)) := by
  apply (ComplexManifolds.coordinatesProdHomeomorph a a').injective
  rw [Homeomorph.apply_symm_apply]
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · change _ = Equiv.piCongrLeft (fun _ => ℂ) finSumFinEquiv
      (Homeomorph.sumArrowHomeomorphProdArrow.symm _) (finSumFinEquiv (Sum.inl i))
    rw [Equiv.piCongrLeft_apply_apply]
    rfl
  · change _ = Equiv.piCongrLeft (fun _ => ℂ) finSumFinEquiv
      (Homeomorph.sumArrowHomeomorphProdArrow.symm _) (finSumFinEquiv (Sum.inr i))
    rw [Equiv.piCongrLeft_apply_apply]
    rfl
def prodSplitLinear (a a' : ℕ) :
    ComplexCoordinates (a + a') →ₗ[ℂ] ComplexCoordinates a × ComplexCoordinates a' where
  toFun z := (fun i => z (Fin.castAdd a' i), fun i => z (Fin.natAdd a i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem eq_zero_on_convex_of_real_slice
    (hS : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hI : ComplexAnalysis.IdentityTheoremsProdAndUpperHalfPlane)
    {a a' : ℕ} (ha : 1 ≤ a + a') {B : Set (Fin b → ComplexVec4)} (hBo : IsOpen B)
    (hBc : Convex ℝ B) {G : (Fin b → ComplexVec4) → ℂ}
    (hG : ComplexCoordinates.IsHolomorphicIn (N' := 1) (coordsToTuple ⁻¹' B)
      (fun z _ => G (coordsToTuple z)))
    (pr : ComplexCoordinates a × ComplexCoordinates a' →ₗ[ℂ] (Fin b → ComplexVec4))
    (hpr : Function.Surjective pr) (p₀ : ComplexCoordinates a × ComplexCoordinates a')
    (h₀ : pr p₀ ∈ B) (hr : p₀.1 ∈ ComplexCoordinates.realLocus a)
    (hv : ∀ᶠ p in 𝓝 p₀, p.1 ∈ ComplexCoordinates.realLocus a → G (pr p) = 0) :
    ∀ ζ ∈ B, G ζ = 0 := by
  have hc : Continuous pr := pr.continuous_of_finiteDimensional
  have hopen : IsOpen (pr ⁻¹' B) := hBo.preimage hc
  have hconv : Convex ℝ (pr ⁻¹' B) := hBc.linear_preimage (pr.restrictScalars ℝ)
  have hconn : IsConnected (pr ⁻¹' B) := ⟨⟨p₀, h₀⟩, hconv.isPreconnected⟩
  have hhol : ComplexAnalysis.HolomorphicOnCoordinatesProd
      (pr ⁻¹' B) (fun p => G (pr p)) := by
    unfold ComplexAnalysis.HolomorphicOnCoordinatesProd
    have hO : IsOpen (ComplexManifolds.coordinatesProdHomeomorph a a' '' (pr ⁻¹' B)) :=
      (ComplexManifolds.coordinatesProdHomeomorph a a').isOpenMap _ hopen
    have hg := isHolomorphicIn_linearMap (tupleCoordsLinear ∘ₗ pr ∘ₗ prodSplitLinear a a') hO
    have hsplit : ∀ z, prodSplitLinear a a' z =
        (ComplexManifolds.coordinatesProdHomeomorph a a').symm z :=
      fun z => (coordinatesProdHomeomorph_symm_eq a a' z).symm
    have h := isHolomorphicIn_comp hS hG hg (fun z hz => by
      obtain ⟨p, hp, rfl⟩ := hz
      change coordsToTuple (tupleCoords (pr (prodSplitLinear a a' _))) ∈ B
      rw [coordsToTuple_tupleCoords, hsplit, Homeomorph.symm_apply_apply]
      exact hp)
    convert h using 1
    funext z _
    change _ = G (coordsToTuple (tupleCoords (pr (prodSplitLinear a a' z))))
    rw [coordsToTuple_tupleCoords, hsplit]
  intro ζ hζ
  obtain ⟨p, rfl⟩ := hpr ζ
  exact hI.1 a a' ha (pr ⁻¹' B) (fun p => G (pr p)) p₀.1 p₀.2 hopen hconn hhol h₀ hr hv p hζ
theorem eq_zero_of_locally_propagating {T : Type*} [TopologicalSpace T] {M : Set T}
    (hM : IsPreconnected M) {D : T → ℂ}
    (hloc : ∀ p ∈ M, ∃ N ∈ 𝓝 p, ∀ q ∈ N ∩ M, (∀ᶠ x in 𝓝[M] q, D x = 0) → ∀ x ∈ N ∩ M, D x = 0)
    {p₀ : T} (hp₀ : p₀ ∈ M) (h₀ : ∀ᶠ x in 𝓝[M] p₀, D x = 0) :
    ∀ x ∈ M, D x = 0 := by
  have : PreconnectedSpace M := isPreconnected_iff_preconnectedSpace.1 hM
  let S : Set M := {p | ∀ᶠ x in 𝓝[M] (p : T), D x = 0}
  have hev : ∀ p : M, (∀ᶠ x in 𝓝[M] (p : T), D x = 0) ↔ ∀ᶠ x : M in 𝓝 p, D x = 0 :=
    fun p => (eventually_nhds_subtype_iff M p (fun x => D x = 0)).symm
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    exact ((hev p).1 hp).eventually_nhds.mono fun q hq => (hev q).2 hq
  have hclosed : IsClosed S := by
    refine isClosed_of_closure_subset fun p hp => ?_
    obtain ⟨N, hN, hq⟩ := hloc p p.2
    have hN' : (Subtype.val ⁻¹' N : Set M) ∈ 𝓝 p := continuous_subtype_val.continuousAt hN
    obtain ⟨q, hqN, hqS⟩ := mem_closure_iff_nhds.1 hp _ hN'
    have hall := hq q ⟨hqN, q.2⟩ hqS
    refine (hev p).2 ?_
    filter_upwards [hN'] with x hx
    exact hall x ⟨hx, x.2⟩
  have huniv : S = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨p₀, hp₀⟩, h₀⟩
  intro x hx
  have hS : (⟨x, hx⟩ : M) ∈ S := huniv ▸ Set.mem_univ _
  exact (hS.self_of_nhdsWithin hx)
def imagBoostLinear (v : unitSphere3) (a : ℝ) :
    (Fin b → ComplexVec4) →ₗ[ℂ] (Fin b → ComplexVec4) where
  toFun := imagBoostTuple v a
  map_add' ζ ζ' := by
    funext k
    simp [imagBoostTuple, mulVecTuple, Matrix.mulVec_add]
  map_smul' t ζ := by
    funext k
    simp [imagBoostTuple, mulVecTuple, Matrix.mulVec_smul]
theorem continuous_imagBoostTuple (v : unitSphere3) (a : ℝ) :
    Continuous (imagBoostTuple v a : (Fin b → ComplexVec4) → Fin b → ComplexVec4) :=
  (imagBoostLinear v a).continuous_of_finiteDimensional
theorem imagBoostTuple_zero (v : unitSphere3) (ζ : Fin b → ComplexVec4) :
    imagBoostTuple v 0 ζ = ζ := by
  funext k
  change boostMatrix v (Complex.I * ((0 : ℝ) : ℂ)) *ᵥ ζ k = ζ k
  rw [boostMatrix_mulVec]
  simp [boostLinearMap]
def spacelikeContinuation (W : (Fin b → ComplexVec4) → ℂ) (j : Fin b)
    (ζ : Fin b → ComplexVec4) : ℂ :=
  open Classical in
  if h : ζ ∈ spacelikeSlab j then
    W (imagBoostTuple (spacelikeUnitDir j ζ h) (maxBoostAngle j ζ) ζ)
  else 0
theorem spacelikeContinuation_of_mem (W : (Fin b → ComplexVec4) → ℂ) {j : Fin b}
    {ζ : Fin b → ComplexVec4} (h : ζ ∈ spacelikeSlab j) :
    spacelikeContinuation W j ζ =
      W (imagBoostTuple (spacelikeUnitDir j ζ h) (maxBoostAngle j ζ) ζ) :=
  dif_pos h
theorem time_lt_unitDir_dot {j : Fin b} {ζ : Fin b → ComplexVec4} (h : ζ ∈ spacelikeSlab j) :
    |MinkowskiSpace.rePart (ζ j) 0| <
      ((spacelikeUnitDir j ζ h : unitSphere3) : Fin 3 → ℝ) ⬝ᵥ
        spacePart (MinkowskiSpace.rePart (ζ j)) := by
  rw [unitDir_dot_spacePart]
  exact slab_time_lt_spaceNorm h
theorem imagBoost_value_indep_angle (hm : TubeGapUnderImagBoosts) (hB : BoostsAndRotations)
    {W : (Fin b → ComplexVec4) → ℂ} (hP : IsConstantAlongLorentzPaths W) {j : Fin b}
    {ζ : Fin b → ComplexVec4} (h : ζ ∈ spacelikeSlab j) (v : unitSphere3)
    (hv : |MinkowskiSpace.rePart (ζ j) 0| <
      (v : Fin 3 → ℝ) ⬝ᵥ spacePart (MinkowskiSpace.rePart (ζ j)))
    {a a' : ℝ} (ha0 : 0 < a) (ha : a ≤ maxBoostAngle j ζ) (ha0' : 0 < a')
    (ha' : a' ≤ maxBoostAngle j ζ) :
    W (imagBoostTuple v a ζ) = W (imagBoostTuple v a' ζ) := by
  have hpath := eq_of_boost_path hB hP (fun _ => (v : Fin 3 → ℝ))
    (fun t => a' + t * (a - a')) (fun _ _ => v.2) (fun _ => contDiffOn_const) (by fun_prop) ζ
    (fun t ht => by
      have hd : 0 < min a a' := lt_min ha0 ha0'
      have h1 := mul_le_mul_of_nonneg_left (min_le_right a a') (sub_nonneg.2 ht.2)
      have h2 := mul_le_mul_of_nonneg_left (min_le_left a a') ht.1
      have h3 := mul_le_mul_of_nonneg_left ha' (sub_nonneg.2 ht.2)
      have h4 := mul_le_mul_of_nonneg_left ha ht.1
      exact imagBoost_mem_tubeTuples hm h v hv (a := a' + t * (a - a')) (by nlinarith)
        (by nlinarith))
    v v rfl rfl
  simpa [imagBoostTuple] using hpath
theorem imagBoost_mem_and_value (hm : TubeGapUnderImagBoosts) (hB : BoostsAndRotations)
    {W : (Fin b → ComplexVec4) → ℂ} (hP : IsConstantAlongLorentzPaths W) {j : Fin b}
    {ζ : Fin b → ComplexVec4} (h : ζ ∈ spacelikeSlab j) {a : ℝ} (ha0 : 0 < a)
    (ha : a ≤ maxBoostAngle j ζ) :
    imagBoostTuple (spacelikeUnitDir j ζ h) a ζ ∈ tubeTuples b ∧
      W (imagBoostTuple (spacelikeUnitDir j ζ h) a ζ) = spacelikeContinuation W j ζ := by
  refine ⟨imagBoost_mem_tubeTuples hm h _ (time_lt_unitDir_dot h) ha0 ha, ?_⟩
  rw [spacelikeContinuation_of_mem W h]
  exact imagBoost_value_indep_angle hm hB hP h _ (time_lt_unitDir_dot h) ha0 ha
    (maxBoostAngle_pos h) le_rfl
theorem spaceNorm_normalize {m : Fin 3 → ℝ} (hN : 0 < spaceNorm m) :
    spaceNorm (fun i => m i / spaceNorm m) = 1 := by
  have hs : ∑ i, m i ^ 2 = spaceNorm m ^ 2 :=
    (Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)).symm
  have hsum : ∑ i, (m i / spaceNorm m) ^ 2 = 1 := by
    simp only [div_pow]
    rw [← Finset.sum_div, hs]
    exact div_self (pow_ne_zero 2 hN.ne')
  change Real.sqrt (∑ i, (m i / spaceNorm m) ^ 2) = 1
  rw [hsum, Real.sqrt_one]
theorem sum_sq_unitSphere3 (v : unitSphere3) : ∑ i, (v : Fin 3 → ℝ) i ^ 2 = 1 := by
  have h : Real.sqrt (∑ i, (v : Fin 3 → ℝ) i ^ 2) = 1 := v.2
  have h2 := Real.sq_sqrt (show 0 ≤ ∑ i, (v : Fin 3 → ℝ) i ^ 2 from
    Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [h] at h2
  linarith
theorem imagBoost_value_indep_dir (hm : TubeGapUnderImagBoosts) (hB : BoostsAndRotations)
    {W : (Fin b → ComplexVec4) → ℂ} (hP : IsConstantAlongLorentzPaths W) {j : Fin b}
    {ζ : Fin b → ComplexVec4} (h : ζ ∈ spacelikeSlab j) (v₀ v : unitSphere3)
    (hp : |MinkowskiSpace.rePart (ζ j) 0| <
      (v₀ : Fin 3 → ℝ) ⬝ᵥ spacePart (MinkowskiSpace.rePart (ζ j)))
    (hq : |MinkowskiSpace.rePart (ζ j) 0| <
      (v : Fin 3 → ℝ) ⬝ᵥ spacePart (MinkowskiSpace.rePart (ζ j)))
    {a : ℝ} (ha0 : 0 < a) (ha : a ≤ maxBoostAngle j ζ) :
    W (imagBoostTuple v a ζ) = W (imagBoostTuple v₀ a ζ) := by
  set X := spacePart (MinkowskiSpace.rePart (ζ j)) with hX
  set c := |MinkowskiSpace.rePart (ζ j) 0| with hc
  have hc0 : 0 ≤ c := abs_nonneg _
  let m : ℝ → Fin 3 → ℝ := fun t i => (1 - t) * (v₀ : Fin 3 → ℝ) i + t * (v : Fin 3 → ℝ) i
  have hdot : ∀ t, m t ⬝ᵥ X =
      (1 - t) * ((v₀ : Fin 3 → ℝ) ⬝ᵥ X) + t * ((v : Fin 3 → ℝ) ⬝ᵥ X) := by
    intro t
    simp only [dotProduct, Fin.sum_univ_three, m]
    ring
  have hgt : ∀ t ∈ Set.Icc (0 : ℝ) 1, c < m t ⬝ᵥ X := by
    intro t ht
    rw [hdot]
    have hd : 0 < min ((v₀ : Fin 3 → ℝ) ⬝ᵥ X - c) ((v : Fin 3 → ℝ) ⬝ᵥ X - c) :=
      lt_min (sub_pos.2 hp) (sub_pos.2 hq)
    have h1 := mul_le_mul_of_nonneg_left
      (min_le_left ((v₀ : Fin 3 → ℝ) ⬝ᵥ X - c) ((v : Fin 3 → ℝ) ⬝ᵥ X - c)) (sub_nonneg.2 ht.2)
    have h2 := mul_le_mul_of_nonneg_left
      (min_le_right ((v₀ : Fin 3 → ℝ) ⬝ᵥ X - c) ((v : Fin 3 → ℝ) ⬝ᵥ X - c)) ht.1
    nlinarith
  have hsum : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < ∑ i, m t i ^ 2 := by
    intro t ht
    refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) fun h0 => ?_
    have hz : ∀ i, m t i = 0 := fun i =>
      pow_eq_zero_iff (two_ne_zero) |>.1
        ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (m t i)).1 h0.symm i
          (Finset.mem_univ i))
    have hd : m t ⬝ᵥ X = 0 := by
      simp only [dotProduct, hz, zero_mul, Finset.sum_const_zero]
    have := hgt t ht
    linarith
  have hNpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < spaceNorm (m t) :=
    fun t ht => Real.sqrt_pos.2 (hsum t ht)
  have hN1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, spaceNorm (m t) ≤ 1 := by
    intro t ht
    refine Real.sqrt_le_iff.2 ⟨zero_le_one, ?_⟩
    have hi : ∀ i, m t i ^ 2 ≤
        (1 - t) * (v₀ : Fin 3 → ℝ) i ^ 2 + t * (v : Fin 3 → ℝ) i ^ 2 := by
      intro i
      have := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.2 ht.2))
        (sq_nonneg ((v₀ : Fin 3 → ℝ) i - (v : Fin 3 → ℝ) i))
      simp only [m]
      nlinarith
    calc ∑ i, m t i ^ 2
        ≤ ∑ i, ((1 - t) * (v₀ : Fin 3 → ℝ) i ^ 2 + t * (v : Fin 3 → ℝ) i ^ 2) :=
          Finset.sum_le_sum fun i _ => hi i
      _ = 1 ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_sq_unitSphere3,
            sum_sq_unitSphere3]
          ring
  let raw : ℝ → Fin 3 → ℝ := fun t i => m t i / spaceNorm (m t)
  have hraw : ∀ t ∈ Set.Icc (0 : ℝ) 1, raw t ∈ unitSphere3 :=
    fun t ht => spaceNorm_normalize (hNpos t ht)
  have hm0 : m 0 = v₀ := by
    funext i
    simp [m]
  have hm1 : m 1 = v := by
    funext i
    simp [m]
  have hr0 : raw 0 = v₀ := by
    funext i
    change m 0 i / spaceNorm (m 0) = _
    rw [hm0, show spaceNorm (v₀ : Fin 3 → ℝ) = 1 from v₀.2, div_one]
  have hr1 : raw 1 = v := by
    funext i
    change m 1 i / spaceNorm (m 1) = _
    rw [hm1, show spaceNorm (v : Fin 3 → ℝ) = 1 from v.2, div_one]
  have hmS : ∀ i, ContDiffOn ℝ 1 (fun t => m t i) (Set.Icc (0 : ℝ) 1) := by
    intro i
    simp only [m]
    fun_prop
  have hNS : ContDiffOn ℝ 1 (fun t => spaceNorm (m t)) (Set.Icc (0 : ℝ) 1) :=
    ContDiffOn.sqrt (ContDiffOn.sum fun i _ => (hmS i).pow 2) fun t ht => (hsum t ht).ne'
  have hs : ∀ i, ContDiffOn ℝ 1 (fun t => raw t i) (Set.Icc (0 : ℝ) 1) :=
    fun i => (hmS i).div hNS fun t ht => (hNpos t ht).ne'
  have hpath := eq_of_boost_path hB hP raw (fun _ => a) hraw hs contDiffOn_const ζ
    (fun t ht => by
      refine imagBoost_mem_tubeTuples hm h ⟨raw t, hraw t ht⟩ ?_ ha0 ha
      have hrd : raw t ⬝ᵥ X = (m t ⬝ᵥ X) / spaceNorm (m t) := by
        simp only [dotProduct, Fin.sum_univ_three, raw]
        ring
      change c < raw t ⬝ᵥ X
      rw [hrd, lt_div_iff₀ (hNpos t ht)]
      have h1 := mul_le_mul_of_nonneg_left (hN1 t ht) hc0
      have h2 := hgt t ht
      linarith)
    v₀ v hr0 hr1
  exact hpath
theorem continuous_dot_spacePart (v : Fin 3 → ℝ) :
    Continuous fun x : RealVec4 => v ⬝ᵥ spacePart x := by
  change Continuous fun x : RealVec4 => ∑ i, v i * spacePart x i
  exact continuous_finsetSum _ fun i _ =>
    continuous_const.mul ((continuous_apply i).comp continuous_spacePart)
theorem exists_ball_boost_eq_continuation (hm : TubeGapUnderImagBoosts) (hB : BoostsAndRotations)
    {W : (Fin b → ComplexVec4) → ℂ} (hP : IsConstantAlongLorentzPaths W) {j : Fin b}
    {ζ₀ : Fin b → ComplexVec4} (h₀ : ζ₀ ∈ spacelikeSlab j) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ ζ ∈ Metric.ball ζ₀ ρ, imagBoostTuple (spacelikeUnitDir j ζ₀ h₀)
        (maxBoostAngle j ζ₀ / 2) ζ ∈ tubeTuples b) ∧
      ∀ ζ ∈ Metric.ball ζ₀ ρ, ζ ∈ spacelikeSlab j →
        W (imagBoostTuple (spacelikeUnitDir j ζ₀ h₀) (maxBoostAngle j ζ₀ / 2) ζ) =
          spacelikeContinuation W j ζ := by
  set v₀ := spacelikeUnitDir j ζ₀ h₀ with hv₀
  set a := maxBoostAngle j ζ₀ / 2 with ha
  have hpos := maxBoostAngle_pos h₀
  have ha0 : 0 < a := by positivity
  have halt : a < maxBoostAngle j ζ₀ := by rw [ha]; linarith
  have ha1 : a ≤ 1 := by linarith [maxBoostAngle_le_one j ζ₀]
  have e1 : ∀ᶠ ζ in 𝓝 ζ₀, imagBoostTuple v₀ a ζ ∈ tubeTuples b :=
    (continuous_imagBoostTuple v₀ a).continuousAt.eventually
      (isOpen_tubeTuples.mem_nhds
        (imagBoost_mem_tubeTuples hm h₀ _ (time_lt_unitDir_dot h₀) ha0 halt.le))
  have e2 : ∀ᶠ ζ in 𝓝 ζ₀, ∀ k, k ≠ j →
      a ≤ tubeGap ((ζ : Fin b → ComplexVec4) k) / (2 * l1Norm (ζ k)) := by
    refine Filter.eventually_all.2 fun k => ?_
    by_cases hk : k = j
    · exact Eventually.of_forall fun ζ hne => absurd hk hne
    · have hk' := h₀.2 k hk
      have hcont : ContinuousAt
          (fun ζ : Fin b → ComplexVec4 => tubeGap (ζ k) / (2 * l1Norm (ζ k))) ζ₀ :=
        ContinuousAt.div
          (continuous_tubeGap.comp (continuous_apply k)).continuousAt
          (continuous_const.mul (continuous_l1Norm.comp (continuous_apply k))).continuousAt
          (mul_pos two_pos (l1Norm_pos_of_mem_futureTube hk')).ne'
      have hlt : a < tubeGap (ζ₀ k) / (2 * l1Norm (ζ₀ k)) :=
        lt_of_lt_of_le halt (maxBoostAngle_le_gap_ratio ζ₀ hk)
      filter_upwards [hcont.eventually (lt_mem_nhds hlt)] with ζ hζ _
      exact hζ.le
  have e3 : ∀ᶠ ζ in 𝓝 ζ₀, |MinkowskiSpace.rePart ((ζ : Fin b → ComplexVec4) j) 0| <
      (v₀ : Fin 3 → ℝ) ⬝ᵥ spacePart (MinkowskiSpace.rePart (ζ j)) := by
    have hcr : Continuous fun ζ : Fin b → ComplexVec4 => MinkowskiSpace.rePart (ζ j) :=
      continuous_rePart.comp (continuous_apply j)
    exact (isOpen_lt ((continuous_apply 0).comp hcr).abs
      ((continuous_dot_spacePart _).comp hcr)).mem_nhds (time_lt_unitDir_dot h₀)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (e1.and (e2.and e3))
  refine ⟨ρ, hρ, fun ζ hζ => (hball ζ hζ).1, fun ζ hζ hM => ?_⟩
  obtain ⟨-, h2, h3⟩ := hball ζ hζ
  have hale : a ≤ maxBoostAngle j ζ := le_maxBoostAngle ha1 h2
  rw [← (imagBoost_mem_and_value hm hB hP hM ha0 hale).2]
  exact (imagBoost_value_indep_dir hm hB hP hM v₀ _ h3 (time_lt_unitDir_dot hM) ha0 hale).symm
theorem tupleBall_subset_ball (ζ₀ : Fin b → ComplexVec4) {r : ℝ} (hr : 0 < r) :
    tupleBall ζ₀ r ⊆ Metric.ball ζ₀ r := by
  intro ζ hζ
  rw [Metric.mem_ball, dist_pi_lt_iff hr]
  intro k
  rw [dist_pi_lt_iff hr]
  intro μ
  rw [dist_eq_norm]
  have h1 : ‖ζ k μ - ζ₀ k μ‖ ^ 2 ≤ ∑ k, ∑ μ, ‖ζ k μ - ζ₀ k μ‖ ^ 2 :=
    (Finset.single_le_sum (f := fun μ => ‖ζ k μ - ζ₀ k μ‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ μ)).trans
      (Finset.single_le_sum (f := fun k => ∑ μ, ‖ζ k μ - ζ₀ k μ‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ k))
  have h2 : ‖ζ k μ - ζ₀ k μ‖ ^ 2 < r ^ 2 := lt_of_le_of_lt h1 hζ
  exact lt_of_pow_lt_pow_left₀ 2 hr.le h2
theorem isOpen_tupleBall (ζ₀ : Fin b → ComplexVec4) (r : ℝ) :
    IsOpen (tupleBall ζ₀ r) := by
  refine isOpen_lt ?_ continuous_const
  exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun μ _ =>
    ((continuous_apply_apply k μ).sub continuous_const).norm.pow 2
theorem exists_local_holomorphic_rep
    (hS : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hm : TubeGapUnderImagBoosts) (hB : BoostsAndRotations)
    {W : (Fin b → ComplexVec4) → ℂ} (hW : IsHolomorphicOnTube W)
    (hP : IsConstantAlongLorentzPaths W)
    {j : Fin b} (ζ₀ : Fin b → ComplexVec4) (h₀ : ζ₀ ∈ spacelikeSlab j) :
    ∃ r : ℝ, 0 < r ∧
      (∀ ζ ∈ tupleBall ζ₀ r,
        imagBoostTuple (spacelikeUnitDir j ζ₀ h₀) (maxBoostAngle j ζ₀ / 2) ζ ∈ tubeTuples b) ∧
      ComplexCoordinates.IsHolomorphicIn (N' := 1) (coordsToTuple ⁻¹' tupleBall ζ₀ r)
        (fun z _ => W (imagBoostTuple (spacelikeUnitDir j ζ₀ h₀) (maxBoostAngle j ζ₀ / 2)
          (coordsToTuple z))) ∧
      ∀ ζ ∈ tupleBall ζ₀ r ∩ spacelikeSlab j,
        W (imagBoostTuple (spacelikeUnitDir j ζ₀ h₀) (maxBoostAngle j ζ₀ / 2) ζ) =
          spacelikeContinuation W j ζ := by
  obtain ⟨ρ, hρ, h1, h2⟩ := exists_ball_boost_eq_continuation hm hB hP h₀
  have hsub := tupleBall_subset_ball ζ₀ hρ
  refine ⟨ρ, hρ, fun ζ hζ => h1 ζ (hsub hζ), ?_, fun ζ hζ => h2 ζ (hsub hζ.1) hζ.2⟩
  exact isHolomorphicIn_comp_linearMap hS hW (imagBoostLinear _ _) (isOpen_tupleBall ζ₀ ρ)
    fun ζ hζ => h1 ζ (hsub hζ)
theorem continuous_imagTimeShift : Continuous imagTimeShift := by
  refine continuous_pi fun μ => ?_
  change Continuous fun a : ℝ => Complex.I * (((a • timeUnit) μ : ℝ) : ℂ)
  exact continuous_const.mul (Complex.continuous_ofReal.comp
    (continuous_id.mul continuous_const))
theorem timeLiftedTuple_zero (j : Fin b) (ζ : Fin b → ComplexVec4) :
    timeLiftedTuple j 0 ζ = ζ := by
  simp [timeLiftedTuple, imagTimeShift_zero]
theorem continuous_timeLiftedTuple (j : Fin b) (ζ : Fin b → ComplexVec4) :
    Continuous fun ε : ℝ => timeLiftedTuple j ε ζ :=
  continuous_const.update j (continuous_const.add continuous_imagTimeShift)
theorem tubeGap_boost_timeLifted (hm : TubeGapUnderImagBoosts) {j : Fin b}
    {ζ : Fin b → ComplexVec4} (h : ζ ∈ spacelikeSlab j) {ε c : ℝ} (hε : 0 ≤ ε) (hc0 : 0 ≤ c)
    (hc : c ≤ maxBoostAngle j ζ) :
    (∀ k, k ≠ j → tubeGap (ζ k) / 2 ≤
      tubeGap (imagBoostTuple (spacelikeUnitDir j ζ h) c (timeLiftedTuple j ε ζ) k)) ∧
    tubeGap (imagBoostTuple (spacelikeUnitDir j ζ h) c (timeLiftedTuple j ε ζ) j) =
      ε * Real.cos c + Real.sin c *
        (spaceNorm (spacePart (MinkowskiSpace.rePart (ζ j))) -
          |MinkowskiSpace.rePart (ζ j) 0|) := by
  have hc1 := hc.trans (maxBoostAngle_le_one j ζ)
  constructor
  · intro k hk
    have hu : timeLiftedTuple j ε ζ k = ζ k := Function.update_of_ne hk _ _
    change _ ≤ tubeGap (boostMatrix _ (Complex.I * (c : ℂ)) *ᵥ timeLiftedTuple j ε ζ k)
    rw [hu]
    exact tubeGap_boost_of_ne hm (h.2 k hk) _ hc0 hc1
      (hc.trans (maxBoostAngle_le_gap_ratio ζ hk))
  · have hu : timeLiftedTuple j ε ζ j =
        toComplex (MinkowskiSpace.rePart (ζ j)) + imagTimeShift ε := by
      simp only [timeLiftedTuple, Function.update_self]
      rw [← slab_eq_toComplex h]
    change tubeGap (boostMatrix _ (Complex.I * (c : ℂ)) *ᵥ timeLiftedTuple j ε ζ j) = _
    rw [hu, tubeGap_boost_shifted hm _ hε hc0 hc1, unitDir_dot_spacePart h]
theorem imagBoost_timeLifted_mem (hm : TubeGapUnderImagBoosts) {j : Fin b}
    {ζ : Fin b → ComplexVec4} (h : ζ ∈ spacelikeSlab j) {ε c : ℝ} (hε : 0 < ε) (hc0 : 0 ≤ c)
    (hc : c ≤ maxBoostAngle j ζ) :
    imagBoostTuple (spacelikeUnitDir j ζ h) c (timeLiftedTuple j ε ζ) ∈ tubeTuples b := by
  have hc1 := hc.trans (maxBoostAngle_le_one j ζ)
  obtain ⟨h1, h2⟩ := tubeGap_boost_timeLifted hm h hε.le hc0 hc
  rw [mem_tubeTuples_iff]
  intro k
  by_cases hk : k = j
  · subst hk
    rw [h2]
    have hcos : 0 < Real.cos c :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩
    have hsin : 0 ≤ Real.sin c :=
      Real.sin_nonneg_of_nonneg_of_le_pi hc0 (by linarith [Real.pi_gt_three])
    have := sub_pos.2 (slab_time_lt_spaceNorm h)
    have h3 := mul_pos hε hcos
    have h4 := mul_nonneg hsin this.le
    linarith
  · have h3 : 0 < tubeGap (ζ k) := h.2 k hk
    exact lt_of_lt_of_le (by linarith) (h1 k hk)
theorem timeLifted_mem_tubeTuples (hm : TubeGapUnderImagBoosts) {j : Fin b}
    {ζ : Fin b → ComplexVec4} (h : ζ ∈ spacelikeSlab j) {ε : ℝ} (hε : 0 < ε) :
    timeLiftedTuple j ε ζ ∈ tubeTuples b := by
  have := imagBoost_timeLifted_mem hm h hε le_rfl (maxBoostAngle_pos h).le
  rwa [imagBoostTuple_zero] at this
theorem value_timeLifted_eq_boost (hm : TubeGapUnderImagBoosts) (hB : BoostsAndRotations)
    {W : (Fin b → ComplexVec4) → ℂ} (hP : IsConstantAlongLorentzPaths W) {j : Fin b}
    {ζ : Fin b → ComplexVec4} (h : ζ ∈ spacelikeSlab j) {ε : ℝ} (hε : 0 < ε) :
    W (timeLiftedTuple j ε ζ) =
      W (imagBoostTuple (spacelikeUnitDir j ζ h) (maxBoostAngle j ζ)
        (timeLiftedTuple j ε ζ)) := by
  have hpos := maxBoostAngle_pos h
  have hpath := eq_of_boost_path hB hP
    (fun _ => ((spacelikeUnitDir j ζ h : unitSphere3) : Fin 3 → ℝ))
    (fun t => t * maxBoostAngle j ζ) (fun _ _ => (spacelikeUnitDir j ζ h).2)
    (fun _ => contDiffOn_const) (by fun_prop) (timeLiftedTuple j ε ζ)
    (fun t ht => imagBoost_timeLifted_mem hm h hε (mul_nonneg ht.1 hpos.le)
      (by nlinarith [ht.2]))
    _ _ rfl rfl
  have h0 := imagBoostTuple_zero (spacelikeUnitDir j ζ h) (timeLiftedTuple j ε ζ)
  simp only [one_mul, zero_mul] at hpath
  change W (imagBoostTuple _ _ _) = W (imagBoostTuple _ _ _) at hpath
  rw [hpath, h0]
theorem min_one_zpow_neg_anti {d d' : ℝ} (hd' : 0 < d') (hd : d' ≤ d) {q : ℤ} (hq : 0 ≤ q) :
    min 1 d ^ (-q) ≤ min 1 d' ^ (-q) := by
  have h1 : 0 < min 1 d' := lt_min one_pos hd'
  have h2 : min 1 d' ≤ min 1 d := min_le_min le_rfl hd
  lift q to ℕ using hq
  rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast]
  exact inv_anti₀ (pow_pos h1 _) (pow_le_pow_left₀ h1.le h2 _)
theorem timeLifted_tendsto_and_bound (hm : TubeGapUnderImagBoosts) (hB : BoostsAndRotations)
    {W : (Fin b → ComplexVec4) → ℂ} (hW : ContinuousOn W (tubeTuples b))
    (hP : IsConstantAlongLorentzPaths W) {κ : ℝ} {q : ℤ} (hκ : 0 ≤ κ) (hq : 0 ≤ q)
    (hbound : ∀ ζ ∈ tubeTuples b, ‖W ζ‖ ≤ κ * ∏ k, min 1 (tubeGap (ζ k)) ^ (-q))
    (j : Fin b) :
    ∀ ζ ∈ spacelikeSlab j,
      (∀ ε : ℝ, 0 < ε → timeLiftedTuple j ε ζ ∈ tubeTuples b) ∧
      Tendsto (fun ε : ℝ => W (timeLiftedTuple j ε ζ)) (𝓝[>] 0)
        (𝓝 (spacelikeContinuation W j ζ)) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ‖W (timeLiftedTuple j ε ζ)‖ ≤
          κ * min 1 (Real.sin (maxBoostAngle j ζ) *
            (spaceNorm (spacePart (MinkowskiSpace.rePart (ζ j))) -
              |MinkowskiSpace.rePart (ζ j) 0|)) ^ (-q) *
            ∏ k ∈ Finset.univ.erase j, min 1 (tubeGap (ζ k) / 2) ^ (-q) := by
  intro ζ h
  have hpos := maxBoostAngle_pos h
  have hle1 := maxBoostAngle_le_one j ζ
  refine ⟨fun ε hε => timeLifted_mem_tubeTuples hm h hε, ?_, fun ε hε _ => ?_⟩
  · rw [spacelikeContinuation_of_mem W h]
    have hf : Continuous fun ε : ℝ =>
        imagBoostTuple (spacelikeUnitDir j ζ h) (maxBoostAngle j ζ) (timeLiftedTuple j ε ζ) :=
      (continuous_imagBoostTuple _ _).comp (continuous_timeLiftedTuple j ζ)
    have hmem := imagBoost_mem_tubeTuples hm h _ (time_lt_unitDir_dot h) hpos le_rfl
    have hat : ContinuousAt W
        (imagBoostTuple (spacelikeUnitDir j ζ h) (maxBoostAngle j ζ) ζ) :=
      hW.continuousAt (isOpen_tubeTuples.mem_nhds hmem)
    have ht : Tendsto (fun ε : ℝ => W (imagBoostTuple (spacelikeUnitDir j ζ h)
        (maxBoostAngle j ζ) (timeLiftedTuple j ε ζ))) (𝓝 0)
        (𝓝 (W (imagBoostTuple (spacelikeUnitDir j ζ h) (maxBoostAngle j ζ) ζ))) := by
      have h0 := hf.tendsto 0
      simp only [timeLiftedTuple_zero] at h0
      exact hat.tendsto.comp h0
    refine (ht.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (value_timeLifted_eq_boost hm hB hP h hε).symm
  · rw [value_timeLifted_eq_boost hm hB hP h hε]
    set ξ := imagBoostTuple (spacelikeUnitDir j ζ h) (maxBoostAngle j ζ) (timeLiftedTuple j ε ζ)
      with hξ
    obtain ⟨h1, h2⟩ := tubeGap_boost_timeLifted hm h hε.le hpos.le le_rfl
    have hmem : ξ ∈ tubeTuples b := imagBoost_timeLifted_mem hm h hε hpos.le le_rfl
    refine (hbound ξ hmem).trans ?_
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), ← mul_assoc]
    have hsin : 0 < Real.sin (maxBoostAngle j ζ) :=
      Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [Real.pi_gt_three])
    have hcos : 0 ≤ Real.cos (maxBoostAngle j ζ) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩
    have hgap := sub_pos.2 (slab_time_lt_spaceNorm h)
    have hj : min 1 (tubeGap (ξ j)) ^ (-q) ≤
        min 1 (Real.sin (maxBoostAngle j ζ) *
            (spaceNorm (spacePart (MinkowskiSpace.rePart (ζ j))) -
              |MinkowskiSpace.rePart (ζ j) 0|)) ^ (-q) := by
      refine min_one_zpow_neg_anti (mul_pos hsin hgap) ?_ hq
      rw [h2]
      have := mul_nonneg hε.le hcos
      linarith
    have hk : ∏ k ∈ Finset.univ.erase j, min 1 (tubeGap (ξ k)) ^ (-q) ≤
        ∏ k ∈ Finset.univ.erase j, min 1 (tubeGap (ζ k) / 2) ^ (-q) := by
      refine Finset.prod_le_prod (fun k _ => ?_) (fun k hk => ?_)
      · have hk' : 0 < tubeGap (ξ k) := (mem_tubeTuples_iff.1 hmem) k
        exact (zpow_pos (lt_min one_pos hk') _).le
      · have hne := Finset.ne_of_mem_erase hk
        have h3 : 0 < tubeGap (ζ k) := h.2 k hne
        exact min_one_zpow_neg_anti (by positivity) (h1 k hne) hq
    have hp0 : 0 ≤ ∏ k ∈ Finset.univ.erase j, min 1 (tubeGap (ξ k)) ^ (-q) :=
      Finset.prod_nonneg fun k _ =>
        (zpow_pos (lt_min one_pos ((mem_tubeTuples_iff.1 hmem) k)) _).le
    have hj0 : 0 ≤ min 1 (Real.sin (maxBoostAngle j ζ) *
            (spaceNorm (spacePart (MinkowskiSpace.rePart (ζ j))) -
              |MinkowskiSpace.rePart (ζ j) 0|)) ^ (-q) :=
      (zpow_pos (lt_min one_pos (mul_pos hsin hgap)) _).le
    exact mul_le_mul (mul_le_mul_of_nonneg_left hj hκ) hk hp0 (mul_nonneg hκ hj0)
theorem adjacentSwapMap_self (j : Fin b) (ζ : Fin b → ComplexVec4) :
    adjacentSwapMap j ζ j = -ζ j := by
  simp [adjacentSwapMap]
theorem adjacentSwapMap_adjacent {j k : Fin b} (ζ : Fin b → ComplexVec4) (hk : k ≠ j)
    (h : (k : ℕ) + 1 = j ∨ (j : ℕ) + 1 = k) : adjacentSwapMap j ζ k = ζ k + ζ j := by
  simp only [adjacentSwapMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [if_neg hk, if_pos h]
theorem adjacentSwapMap_far {j k : Fin b} (ζ : Fin b → ComplexVec4) (hk : k ≠ j)
    (h : ¬((k : ℕ) + 1 = j ∨ (j : ℕ) + 1 = k)) : adjacentSwapMap j ζ k = ζ k := by
  simp only [adjacentSwapMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [if_neg hk, if_neg h]
theorem adjacentSwapMap_adjacentSwapMap (j : Fin b) (ζ : Fin b → ComplexVec4) :
    adjacentSwapMap j (adjacentSwapMap j ζ) = ζ := by
  funext k
  by_cases hk : k = j
  · subst hk
    rw [adjacentSwapMap_self, adjacentSwapMap_self, neg_neg]
  · by_cases h : (k : ℕ) + 1 = j ∨ (j : ℕ) + 1 = k
    · rw [adjacentSwapMap_adjacent _ hk h, adjacentSwapMap_adjacent _ hk h,
        adjacentSwapMap_self]
      abel
    · rw [adjacentSwapMap_far _ hk h, adjacentSwapMap_far _ hk h]
theorem adjacentSwapMap_bijective (j : Fin b) : Function.Bijective (adjacentSwapMap j) :=
  Function.Involutive.bijective (adjacentSwapMap_adjacentSwapMap j)
theorem adjacentSwapMap_successiveDiffs (j : Fin b) (z : Fin (b + 1) → ComplexVec4) :
    adjacentSwapMap j (successiveDiffs z) =
      successiveDiffs (z ∘ Equiv.swap j.castSucc j.succ) := by
  funext k
  by_cases hk : k = j
  · subst hk
    rw [adjacentSwapMap_self]
    simp [successiveDiffs, Function.comp]
  have hk' : (k : ℕ) ≠ j := fun e => hk (Fin.ext e)
  by_cases h : (k : ℕ) + 1 = j ∨ (j : ℕ) + 1 = k
  · rw [adjacentSwapMap_adjacent _ hk h]
    rcases h with h | h
    · have e : k.succ = j.castSucc := Fin.ext (by simp [h])
      have n1 : k.castSucc ≠ j.castSucc := fun e' => hk' (by simpa using congrArg Fin.val e')
      have n2 : k.castSucc ≠ j.succ := fun e' => by
        have := congrArg Fin.val e'
        simp at this
        omega
      simp only [successiveDiffs, Function.comp, e, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne n1 n2]
      abel
    · have e : k.castSucc = j.succ := Fin.ext (by simp [h])
      have n1 : k.succ ≠ j.castSucc := fun e' => by
        have := congrArg Fin.val e'
        simp at this
        omega
      have n2 : k.succ ≠ j.succ := fun e' => hk' (by simpa using congrArg Fin.val e')
      simp only [successiveDiffs, Function.comp, e, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne n1 n2]
      abel
  · rw [adjacentSwapMap_far _ hk h]
    have n1 : k.succ ≠ j.castSucc := fun e' => by
      have := congrArg Fin.val e'
      simp at this
      omega
    have n2 : k.succ ≠ j.succ := fun e' => hk' (by simpa using congrArg Fin.val e')
    have n3 : k.castSucc ≠ j.castSucc := fun e' => hk' (by simpa using congrArg Fin.val e')
    have n4 : k.castSucc ≠ j.succ := fun e' => by
      have := congrArg Fin.val e'
      simp at this
      omega
    simp only [successiveDiffs, Function.comp, Equiv.swap_apply_of_ne_of_ne n1 n2,
      Equiv.swap_apply_of_ne_of_ne n3 n4]
theorem add_toComplex_mem_futureTube {ζ : ComplexVec4} (h : ζ ∈ futureTube) (x : RealVec4) :
    ζ + toComplex x ∈ futureTube := by
  have him : MinkowskiSpace.imPart (ζ + toComplex x) = MinkowskiSpace.imPart ζ := by
    funext μ
    simp [MinkowskiSpace.imPart, toComplex]
  change MinkowskiSpace.imPart (ζ + toComplex x) ∈ futureCone
  rw [him]
  exact h
theorem adjacentSwapMap_mem_slab {j : Fin b} {ζ : Fin b → ComplexVec4}
    (h : ζ ∈ spacelikeSlab j) : adjacentSwapMap j ζ ∈ spacelikeSlab j := by
  refine ⟨?_, fun k hk => ?_⟩
  · rw [adjacentSwapMap_self]
    obtain ⟨x, hx, hxe⟩ := h.1
    refine ⟨-x, ?_, ?_⟩
    · have hneg : toComplex (-x) = (-1 : ℂ) • toComplex x := by
        funext μ
        simp [toComplex]
      change (minkowskiForm (toComplex (-x)) (toComplex (-x))).re < 0
      rw [hneg, minkowskiForm_smul_left, minkowskiForm_smul_right]
      have hx' : (minkowskiForm (toComplex x) (toComplex x)).re < 0 := hx
      simpa using hx'
    · rw [← hxe]
      funext μ
      simp [toComplex]
  · by_cases hn : (k : ℕ) + 1 = j ∨ (j : ℕ) + 1 = k
    · rw [adjacentSwapMap_adjacent _ hk hn, slab_eq_toComplex h]
      exact add_toComplex_mem_futureTube (h.2 k hk) _
    · rw [adjacentSwapMap_far _ hk hn]
      exact h.2 k hk
theorem adjacentSwapMap_image_slab (j : Fin b) :
    adjacentSwapMap j '' spacelikeSlab j = spacelikeSlab j := by
  ext ζ
  constructor
  · rintro ⟨ξ, hξ, rfl⟩
    exact adjacentSwapMap_mem_slab hξ
  · intro h
    exact ⟨_, adjacentSwapMap_mem_slab h, adjacentSwapMap_adjacentSwapMap j ζ⟩
theorem continuous_toComplex : Continuous (toComplex : RealVec4 → ComplexVec4) :=
  continuous_pi fun μ => Complex.continuous_ofReal.comp (continuous_apply μ)
theorem isPreconnected_spacelikeSlab (hJ : SpacelikeSetOpenConnected)
    (hT : Convex ℝ futureTube) (j : Fin b) : IsPreconnected (spacelikeSlab j) := by
  have hset : spacelikeSlab j =
      Set.univ.pi fun k => if k = j then toComplex '' spacelikeSet else futureTube := by
    ext ζ
    simp only [spacelikeSlab, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨h1, h2⟩ k
      split_ifs with hk
      · exact hk ▸ h1
      · exact h2 k hk
    · intro h
      refine ⟨by simpa using h j, fun k hk => by simpa [hk] using h k⟩
  rw [hset]
  refine isPreconnected_univ_pi fun k => ?_
  split_ifs
  · exact hJ.2.isPreconnected.image _ continuous_toComplex.continuousOn
  · exact hT.isPreconnected
theorem eventually_mem_slab_of_real (hJ : SpacelikeSetOpenConnected) {j : Fin b}
    {q : Fin b → ComplexVec4} (h : q ∈ spacelikeSlab j) :
    ∀ᶠ ξ in 𝓝 q, (∀ μ, ((ξ : Fin b → ComplexVec4) j μ).im = 0) → ξ ∈ spacelikeSlab j := by
  have e1 : ∀ᶠ ξ in 𝓝 q,
      MinkowskiSpace.rePart ((ξ : Fin b → ComplexVec4) j) ∈ spacelikeSet :=
    (continuous_rePart.comp (continuous_apply j)).continuousAt.eventually
      (hJ.1.mem_nhds (rePart_mem_spacelikeSet_of_mem_spacelikeSlab h))
  have e2 : ∀ᶠ ξ in 𝓝 q, ∀ k, k ≠ j → (ξ : Fin b → ComplexVec4) k ∈ futureTube := by
    refine Filter.eventually_all.2 fun k => ?_
    by_cases hk : k = j
    · exact Eventually.of_forall fun ξ hne => absurd hk hne
    · filter_upwards [(continuous_apply k).continuousAt.eventually
        (isOpen_futureTube.mem_nhds (h.2 k hk))] with ξ hξ _
      exact hξ
  filter_upwards [e1, e2] with ξ h1 h2 hr
  refine ⟨⟨_, h1, ?_⟩, h2⟩
  funext μ
  exact Complex.ext (by simp [MinkowskiSpace.rePart, toComplex]) (by simp [toComplex, hr μ])
theorem exists_ball_diff_eq_boost_diff (hm : TubeGapUnderImagBoosts) (hB : BoostsAndRotations)
    {W : (Fin b → ComplexVec4) → ℂ} (hP : IsConstantAlongLorentzPaths W) {j : Fin b}
    {p : Fin b → ComplexVec4} (h : p ∈ spacelikeSlab j) :
    ∃ (ρ : ℝ) (v v' : unitSphere3) (a a' : ℝ), 0 < ρ ∧
      (∀ ζ ∈ Metric.ball p ρ, imagBoostTuple v a ζ ∈ tubeTuples b ∧
        imagBoostTuple v' a' (adjacentSwapMap j ζ) ∈ tubeTuples b) ∧
      ∀ ζ ∈ Metric.ball p ρ, ζ ∈ spacelikeSlab j →
        W (imagBoostTuple v' a' (adjacentSwapMap j ζ)) - W (imagBoostTuple v a ζ) =
          spacelikeContinuation W j (adjacentSwapMap j ζ) - spacelikeContinuation W j ζ := by
  have h' := adjacentSwapMap_mem_slab h
  obtain ⟨ρ₁, hρ₁, a1, a2⟩ := exists_ball_boost_eq_continuation hm hB hP h
  obtain ⟨ρ₂, hρ₂, b1, b2⟩ := exists_ball_boost_eq_continuation hm hB hP h'
  have hct : Continuous (adjacentSwapMap j) :=
    (adjacentSwapMap j).continuous_of_finiteDimensional
  have e1 : ∀ᶠ ζ in 𝓝 p, ζ ∈ Metric.ball p ρ₁ := Metric.ball_mem_nhds _ hρ₁
  have e2 : ∀ᶠ ζ in 𝓝 p, adjacentSwapMap j ζ ∈ Metric.ball (adjacentSwapMap j p) ρ₂ :=
    hct.continuousAt.eventually (Metric.ball_mem_nhds _ hρ₂)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (e1.and e2)
  refine ⟨ρ, _, _, _, _, hρ, fun ζ hζ => ⟨a1 ζ (hball ζ hζ).1, b1 _ (hball ζ hζ).2⟩,
    fun ζ hζ hM => ?_⟩
  rw [a2 ζ (hball ζ hζ).1 hM, b2 _ (hball ζ hζ).2 (adjacentSwapMap_mem_slab hM)]
theorem isHolomorphicIn_boost_diff
    (hS : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {W : (Fin b → ComplexVec4) → ℂ} (hW : IsHolomorphicOnTube W) {j : Fin b}
    {v v' : unitSphere3} {a a' : ℝ} {U : Set (Fin b → ComplexVec4)} (hU : IsOpen U)
    (ht : ∀ ζ ∈ U, imagBoostTuple v a ζ ∈ tubeTuples b ∧
      imagBoostTuple v' a' (adjacentSwapMap j ζ) ∈ tubeTuples b) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) (coordsToTuple ⁻¹' U)
      (fun z _ => W (imagBoostTuple v' a' (adjacentSwapMap j (coordsToTuple z))) -
        W (imagBoostTuple v a (coordsToTuple z))) :=
  isHolomorphicIn_sub
    (isHolomorphicIn_comp_linearMap hS hW (imagBoostLinear v' a' ∘ₗ adjacentSwapMap j) hU
      fun ζ hζ => (ht ζ hζ).2)
    (isHolomorphicIn_comp_linearMap hS hW (imagBoostLinear v a) hU fun ζ hζ => (ht ζ hζ).1)
def updateSlotLinear (j : Fin b) :
    ComplexCoordinates 4 × ComplexCoordinates (b * 4) →ₗ[ℂ] (Fin b → ComplexVec4) where
  toFun p := Function.update (coordsToTuple p.2) j p.1
  map_add' p p' := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp
    · simp only [Pi.add_apply, Function.update_of_ne hk]
      rfl
  map_smul' t p := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp
    · simp only [Pi.smul_apply, RingHom.id_apply, Function.update_of_ne hk]
      rfl
theorem updateSlotLinear_self (j : Fin b) (ζ : Fin b → ComplexVec4) :
    updateSlotLinear j (ζ j, tupleCoords ζ) = ζ := by
  change Function.update (coordsToTuple (tupleCoords ζ)) j (ζ j) = ζ
  rw [coordsToTuple_tupleCoords, Function.update_eq_self]
theorem eq_zero_on_ball_of_eventually_slab
    (hS : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hI : ComplexAnalysis.IdentityTheoremsProdAndUpperHalfPlane)
    (hJ : SpacelikeSetOpenConnected) {j : Fin b} {p q : Fin b → ComplexVec4} {ρ : ℝ}
    {G : (Fin b → ComplexVec4) → ℂ}
    (hG : ComplexCoordinates.IsHolomorphicIn (N' := 1) (coordsToTuple ⁻¹' Metric.ball p ρ)
      (fun z _ => G (coordsToTuple z)))
    (hq : q ∈ Metric.ball p ρ) (hqM : q ∈ spacelikeSlab j)
    (hv : ∀ᶠ ξ in 𝓝[spacelikeSlab j] q, G ξ = 0) :
    ∀ ζ ∈ Metric.ball p ρ, G ζ = 0 := by
  have hc : Continuous (updateSlotLinear j) :=
    (updateSlotLinear j).continuous_of_finiteDimensional
  have hself := updateSlotLinear_self j q
  have hev : ∀ᶠ ξ in 𝓝 q, (∀ μ, ((ξ : Fin b → ComplexVec4) j μ).im = 0) → G ξ = 0 := by
    filter_upwards [eventually_mem_slab_of_real hJ hqM, eventually_nhdsWithin_iff.1 hv]
      with ξ h1 h2 hr
    exact h2 (h1 hr)
  have hev' := hc.continuousAt (x := (q j, tupleCoords q)) |>.eventually (by rwa [hself])
  refine eq_zero_on_convex_of_real_slice hS hI (a := 4) (a' := b * 4) (by omega)
    Metric.isOpen_ball (convex_ball p ρ) hG (updateSlotLinear j)
    (fun ζ => ⟨_, updateSlotLinear_self j ζ⟩) (q j, tupleCoords q) (by rwa [hself]) ?_ ?_
  · intro μ
    change (q j μ).im = 0
    rw [slab_eq_toComplex hqM]
    simp [toComplex]
  · filter_upwards [hev'] with r hr hreal
    refine hr fun μ => ?_
    have hj : updateSlotLinear j r j = r.1 := by
      change Function.update (coordsToTuple r.2) j r.1 j = r.1
      simp
    rw [hj]
    exact hreal μ
theorem toComplex_mulVec (M : RealMat4) (x : RealVec4) :
    toComplex (M *ᵥ x) = toComplexMatrix M *ᵥ toComplex x := by
  funext μ
  simp [toComplex, toComplexMatrix, Matrix.mulVec, dotProduct]
theorem imagBoostTuple_wickDiffs (hB : BoostsAndRotations) (v : unitSphere3) (a : ℝ)
    (R : Matrix.orthogonalGroup (Fin 4) ℝ) (hR : (R : RealMat4) = imagBoostRotation v a)
    {n : ℕ} (x : TestSpaces.PointTuple (n + 1)) (ς : Equiv.Perm (Fin (n + 1))) :
    imagBoostTuple v a (wickDiffs (x ∘ ς)) =
      wickDiffs (TestSpaces.rotatePermute R ς x) := by
  have hrot := (hB.2.2.2 v a).2
  funext k
  change boostMatrix v (Complex.I * (a : ℂ)) *ᵥ
      (wickMap (toComplex (x (ς k.succ))) -
        wickMap (toComplex (x (ς k.castSucc)))) =
    wickMap (toComplex ((R : RealMat4) *ᵥ x (ς k.succ))) -
      wickMap (toComplex ((R : RealMat4) *ᵥ x (ς k.castSucc)))
  rw [Matrix.mulVec_sub, hrot, hrot, toComplex_mulVec, toComplex_mulVec, hR]
theorem mem_increasingTimes_of_wickDiffs_mem {n : ℕ} {y : TestSpaces.PointTuple (n + 1)}
    (h : wickDiffs y ∈ tubeTuples n) : y ∈ TestSpaces.increasingTimes (n + 1) := by
  change StrictMono (TestSpaces.timeCoord y)
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  have h1 : 0 < tubeGap (wickDiffs y i) := mem_tubeTuples_iff.1 h i
  have h2 : MinkowskiSpace.imPart (wickDiffs y i) 0 =
      y i.succ 3 - y i.castSucc 3 := by
    change ((wickMap (toComplex (y i.succ)) -
      wickMap (toComplex (y i.castSucc))) 0).im = _
    simp [wickMap_apply_zero, toComplex]
  unfold tubeGap coneGap at h1
  rw [h2] at h1
  have h3 := spaceNorm_nonneg (spacePart (MinkowskiSpace.imPart (wickDiffs y i)))
  change y i.castSucc 3 < y i.succ 3
  linarith
def IsEuclidInvariantOnDiffs (W : (Fin b → ComplexVec4) → ℂ) : Prop :=
  ∀ x : TestSpaces.PointTuple (b + 1), x ∈ TestSpaces.increasingTimes (b + 1) →
    ∀ (R : Matrix.orthogonalGroup (Fin 4) ℝ) (ς : Equiv.Perm (Fin (b + 1))),
      TestSpaces.rotatePermute R ς x ∈ TestSpaces.increasingTimes (b + 1) →
        W (wickDiffs (TestSpaces.rotatePermute R ς x)) = W (wickDiffs x)
theorem boost_values_eq_at_wick (hB : BoostsAndRotations)
    {W : (Fin b → ComplexVec4) → ℂ} (hE : IsEuclidInvariantOnDiffs W) (j : Fin b)
    (x : TestSpaces.PointTuple (b + 1)) (v v' : unitSphere3) (a a' : ℝ)
    (h1 : imagBoostTuple v a (wickDiffs x) ∈ tubeTuples b)
    (h2 : imagBoostTuple v' a' (adjacentSwapMap j (wickDiffs x)) ∈ tubeTuples b) :
    W (imagBoostTuple v' a' (adjacentSwapMap j (wickDiffs x))) =
      W (imagBoostTuple v a (wickDiffs x)) := by
  have m1 : imagBoostRotation v a ∈ Matrix.orthogonalGroup (Fin 4) ℝ :=
    (Matrix.mem_specialOrthogonalGroup_iff.1 (hB.2.2.2 v a).1).1
  have m2 : imagBoostRotation v' a' ∈ Matrix.orthogonalGroup (Fin 4) ℝ :=
    (Matrix.mem_specialOrthogonalGroup_iff.1 (hB.2.2.2 v' a').1).1
  let R₁ : Matrix.orthogonalGroup (Fin 4) ℝ := ⟨_, m1⟩
  let R₂ : Matrix.orthogonalGroup (Fin 4) ℝ := ⟨_, m2⟩
  let ς : Equiv.Perm (Fin (b + 1)) := Equiv.swap j.castSucc j.succ
  have e1 : imagBoostTuple v a (wickDiffs x) =
      wickDiffs (TestSpaces.rotatePermute R₁ 1 x) :=
    imagBoostTuple_wickDiffs hB v a R₁ rfl x 1
  have et : adjacentSwapMap j (wickDiffs x) = wickDiffs (x ∘ ς) :=
    adjacentSwapMap_successiveDiffs j _
  have e2 : imagBoostTuple v' a' (adjacentSwapMap j (wickDiffs x)) =
      wickDiffs (TestSpaces.rotatePermute R₂ ς x) := by
    rw [et]
    exact imagBoostTuple_wickDiffs hB v' a' R₂ rfl x ς
  rw [e1] at h1 ⊢
  rw [e2] at h2 ⊢
  have o1 := mem_increasingTimes_of_wickDiffs_mem h1
  have o2 := mem_increasingTimes_of_wickDiffs_mem h2
  have hy : TestSpaces.rotatePermute (R₂ * R₁⁻¹) ς (TestSpaces.rotatePermute R₁ 1 x) =
      TestSpaces.rotatePermute R₂ ς x := by
    funext i
    change ((R₂ * R₁⁻¹ : Matrix.orthogonalGroup (Fin 4) ℝ) : RealMat4) *ᵥ
        ((R₁ : RealMat4) *ᵥ x (ς i)) = (R₂ : RealMat4) *ᵥ x (ς i)
    rw [Matrix.mulVec_mulVec]
    congr 1
    change ((R₂ * R₁⁻¹ * R₁ : Matrix.orthogonalGroup (Fin 4) ℝ) : RealMat4) = _
    rw [inv_mul_cancel_right]
  have h := hE _ o1 (R₂ * R₁⁻¹) ς (by rw [hy]; exact o2)
  rwa [hy] at h
def basePointTuple (j : Fin b) : Fin b → RealVec4 :=
  fun k => if k = j then ![1, 0, 0, 0] else ![0, 0, 0, 1]
theorem basePoint_mem_slab (hF : WickMapFormulas) (j : Fin b) :
    (fun k => wickMap (toComplex (basePointTuple j k))) ∈ spacelikeSlab j := by
  refine ⟨⟨![0, 1, 0, 0], ?_, ?_⟩, fun k hk => ?_⟩
  · refine (isSpacelikeVec_iff _).2 ?_
    simp [spaceNorm, spacePart, Fin.sum_univ_three]
  · funext μ
    fin_cases μ <;> simp [basePointTuple, toComplex, wickMap]
  · refine (hF.2.2.2.2.2.1 _).2 ?_
    simp [basePointTuple, hk]
def wickTupleLinear :
    ComplexCoordinates (b * 4) × ComplexCoordinates 0 →ₗ[ℂ] (Fin b → ComplexVec4) where
  toFun p k := wickMap (coordsToTuple p.1 k)
  map_add' p p' := by
    funext k
    exact map_add wickMap _ _
  map_smul' t p := by
    funext k
    exact map_smul wickMap t _
theorem wickTupleLinear_surjective :
    Function.Surjective (wickTupleLinear : _ →ₗ[ℂ] (Fin b → ComplexVec4)) := by
  intro ζ
  refine ⟨(tupleCoords fun k => wickMap.symm (ζ k), 0), ?_⟩
  funext k
  change wickMap (coordsToTuple (tupleCoords _) k) = _
  rw [coordsToTuple_tupleCoords]
  exact wickMap.apply_symm_apply _
theorem exists_wickDiffs_eq (y : Fin b → RealVec4) :
    ∃ x : TestSpaces.PointTuple (b + 1),
      wickDiffs x = fun k => wickMap (toComplex (y k)) := by
  refine ⟨cumulativeSums (Fin.cons (α := fun _ => Fin 4 → ℝ) 0 y), ?_⟩
  set x := cumulativeSums (Fin.cons (α := fun _ => Fin 4 → ℝ) 0 y) with hx
  funext k
  have hf := congrFun (diffCoords_cumulativeSums (Fin.cons (α := fun _ => Fin 4 → ℝ) 0 y)) k.succ
  simp only [diffCoords, Fin.cons_succ, successiveDiffs, tupleToComplex] at hf
  rw [← hx] at hf
  change wickMap (toComplex (x k.succ)) - wickMap (toComplex (x k.castSucc)) = _
  rw [← map_sub, hf]
theorem eventually_diff_eq_zero_near_basePoint
    (hS : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hI : ComplexAnalysis.IdentityTheoremsProdAndUpperHalfPlane)
    (hm : TubeGapUnderImagBoosts) (hB : BoostsAndRotations)
    (hF : WickMapFormulas)
    {W : (Fin b → ComplexVec4) → ℂ} (hW : IsHolomorphicOnTube W)
    (hP : IsConstantAlongLorentzPaths W)
    (hE : IsEuclidInvariantOnDiffs W) (j : Fin b) :
    ∀ᶠ ξ in 𝓝[spacelikeSlab j] (fun k => wickMap (toComplex (basePointTuple j k))),
      spacelikeContinuation W j (adjacentSwapMap j ξ) - spacelikeContinuation W j ξ = 0 := by
  obtain ⟨ρ, v, v', a, a', hρ, ht, hD⟩ :=
    exists_ball_diff_eq_boost_diff hm hB hP (basePoint_mem_slab hF j)
  have hb : 1 ≤ b * 4 + 0 := by
    have := j.pos
    omega
  have hc : Continuous (wickTupleLinear : _ →ₗ[ℂ] (Fin b → ComplexVec4)) :=
    LinearMap.continuous_of_finiteDimensional _
  have hself : wickTupleLinear ((tupleCoords fun k => toComplex (basePointTuple j k), 0) :
      ComplexCoordinates (b * 4) × ComplexCoordinates 0) =
      fun k => wickMap (toComplex (basePointTuple j k)) := by
    funext k
    change wickMap (coordsToTuple (tupleCoords _) k) = _
    rw [coordsToTuple_tupleCoords]
  have hzero := eq_zero_on_convex_of_real_slice hS hI hb Metric.isOpen_ball (convex_ball _ ρ)
    (G := fun ζ => W (imagBoostTuple v' a' (adjacentSwapMap j ζ)) - W (imagBoostTuple v a ζ))
    (isHolomorphicIn_boost_diff hS hW Metric.isOpen_ball ht) wickTupleLinear
    wickTupleLinear_surjective (tupleCoords fun k => toComplex (basePointTuple j k), 0)
    (by rw [hself]; exact Metric.mem_ball_self hρ)
    (fun i => by simp [tupleCoords, toComplex])
    (by
      have hev := hc.continuousAt
        (x := ((tupleCoords fun k => toComplex (basePointTuple j k), 0) :
          ComplexCoordinates (b * 4) × ComplexCoordinates 0)) |>.eventually
        (by rw [hself]; exact Metric.ball_mem_nhds _ hρ)
      filter_upwards [hev] with r hr hreal
      obtain ⟨x, hx⟩ := exists_wickDiffs_eq
        fun k μ => (coordsToTuple r.1 k μ).re
      have hrx : wickTupleLinear r = wickDiffs x := by
        rw [hx]
        funext k
        change wickMap (coordsToTuple r.1 k) = _
        congr 1
        funext μ
        have him : (coordsToTuple r.1 k μ).im = 0 := hreal (finProdFinEquiv (k, μ))
        exact Complex.ext (by simp [toComplex]) (by simp [toComplex, him])
      have hz := ht _ hr
      rw [hrx] at hz ⊢
      exact sub_eq_zero.2 (boost_values_eq_at_wick hB hE j x v v' a a' hz.1 hz.2))
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds _ hρ] with ξ hξ hM
  rw [← hD ξ hξ hM]
  exact hzero ξ hξ
theorem continuation_adjacentSwap_eq
    (hS : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hI : ComplexAnalysis.IdentityTheoremsProdAndUpperHalfPlane)
    (hm : TubeGapUnderImagBoosts) (hB : BoostsAndRotations)
    (hF : WickMapFormulas) (hJ : SpacelikeSetOpenConnected)
    (hT : Convex ℝ futureTube)
    {W : (Fin b → ComplexVec4) → ℂ} (hW : IsHolomorphicOnTube W)
    (hP : IsConstantAlongLorentzPaths W)
    (hE : IsEuclidInvariantOnDiffs W) (j : Fin b) :
    ∀ ζ ∈ spacelikeSlab j,
      spacelikeContinuation W j (adjacentSwapMap j ζ) = spacelikeContinuation W j ζ := by
  have hall := eq_zero_of_locally_propagating (isPreconnected_spacelikeSlab hJ hT j)
    (D := fun ξ => spacelikeContinuation W j (adjacentSwapMap j ξ) -
      spacelikeContinuation W j ξ) (fun p hp => by
      obtain ⟨ρ, v, v', a, a', hρ, ht, hD⟩ := exists_ball_diff_eq_boost_diff hm hB hP hp
      refine ⟨Metric.ball p ρ, Metric.ball_mem_nhds _ hρ, fun q hq hv ζ hζ => ?_⟩
      have hGv : ∀ᶠ ξ in 𝓝[spacelikeSlab j] q,
          W (imagBoostTuple v' a' (adjacentSwapMap j ξ)) - W (imagBoostTuple v a ξ) = 0 := by
        have hnear : ∀ᶠ ξ in 𝓝[spacelikeSlab j] q, ξ ∈ Metric.ball p ρ :=
          nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hq.1)
        filter_upwards [hv, hnear, self_mem_nhdsWithin] with ξ h1 h2 h3
        rw [hD ξ h2 h3]
        exact h1
      have hz := eq_zero_on_ball_of_eventually_slab hS hI hJ
        (isHolomorphicIn_boost_diff hS hW Metric.isOpen_ball ht) hq.1 hq.2 hGv ζ hζ.1
      rw [← hD ζ hζ.1 hζ.2]
      exact hz)
    (basePoint_mem_slab hF j) (eventually_diff_eq_zero_near_basePoint hS hI hm hB hF hW hP hE j)
  exact fun ζ hζ => sub_eq_zero.1 (hall ζ hζ)
theorem spacelikeExtension_holds (hC : MinkowskiSpace.ConeTubeLorentz.Statement)
    (hI : ComplexAnalysis.IdentityTheoremsProdAndUpperHalfPlane)
    (hL : VacuumLorentzInvariance.Statement) (hP : FieldProductProperties)
    (hS : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    SpacelikeExtension.Statement := by
  intro K _ _ _ E Ω A ℘ C hF hE b j
  obtain ⟨-, hConv, -, hForm, hBoost, hMargin, -, -, -, -, -, hJ⟩ := hC
  have hb : 1 ≤ b := j.pos
  obtain ⟨-, hPath, -⟩ := hL K E Ω A ℘ C hF hE b hb
  obtain ⟨-, -, -, -, -, -, -, hHol, hBd, -, -⟩ := hP K E Ω A ℘ C hF
  have hW : IsHolomorphicOnTube (m := b) (vacuumExpectation E Ω A (b + 1)) := (hHol b).1
  have hEuc : IsEuclidInvariantOnDiffs (b := b) (vacuumExpectation E Ω A (b + 1)) :=
    fun x hx R ς h => hE b x hx R ς h
  have hκ : 0 ≤ ((2 : ℝ) ^ ℘ * C) ^ (b + 1) :=
    pow_nonneg (mul_nonneg (Real.rpow_nonneg zero_le_two _)
      (zero_le_one.trans hF.one_le_const)) _
  have hq : 0 ≤ ceilExponent ℘ (b + 1) :=
    Int.ceil_nonneg (mul_nonneg (Nat.cast_nonneg _) hF.exponent_nonneg)
  refine ⟨adjacentSwapMap_bijective j, adjacentSwapMap_successiveDiffs j, ?_, ?_, ?_,
    adjacentSwapMap_image_slab j, ?_⟩
  · exact fun ζ h a ha0 ha => imagBoost_mem_and_value hMargin hBoost hPath h ha0 ha
  · exact fun ζ₀ h₀ => exists_local_holomorphic_rep hS hMargin hBoost hW hPath ζ₀ h₀
  · exact timeLifted_tendsto_and_bound hMargin hBoost (continuousOn_tubeTuples_of_holomorphic hW)
      hPath hκ hq (hBd (b + 1)).1 j
  · exact continuation_adjacentSwap_eq hS hI hMargin hBoost hForm hJ hConv.2.2.2.2.2.1 hW hPath
      hEuc j
end YangMills.Construction.FieldForms.SpacelikeExtension
end
