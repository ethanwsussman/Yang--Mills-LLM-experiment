import YangMills.Construction.Averaging.AveragingMapRealAnalyticAtSmallRadiiProof
import YangMills.Construction.ClusterExpansion.PolymerSystemOfARegion
import YangMills.Construction.Lattice.ComplexAverageAtAnImageBondProof
import YangMills.Construction.Lattice.DomainsOfTheTwoSchemes
import YangMills.Construction.Lattice.HolomorphyOfBoundedOneStepObjects
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace BoundedStepHolomorphy
open YangMills.Construction.Coordinates YangMills.Construction.Matrices
open YangMills.Construction.Coordinates.ComplexCoordinates YangMills.Construction.Matrices.GroupLieProduct
section MatrixMaps
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
def entriesCLE : ComplexMatrix2 ≃L[ℂ] ComplexCoordinates 4 :=
  LinearEquiv.toContinuousLinearEquiv
    { matrixEquiv with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
theorem differentiableAt_of_isHolomorphicVia (hH : PowerSeriesHolomorphy.Properties)
    {D : Set ComplexMatrix2} {f : ComplexMatrix2 → ComplexMatrix2}
    (hf : IsHolomorphicVia matrixEquiv matrixEquiv D f) {M : ComplexMatrix2} (hM : M ∈ D) :
    DifferentiableAt ℂ f M := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.differentiableAt_of_isHolomorphicVia_matrix <;> assumption
theorem differentiableAt_matExp (hH : PowerSeriesHolomorphy.Properties) {f : E → ComplexMatrix2}
    {w : E} (hf : DifferentiableAt ℂ f w) :
    DifferentiableAt ℂ (fun v => ComplexMatrix2.matExp (f v)) w :=
  (differentiableAt_of_isHolomorphicVia hH hH.2.2.2.2.1 (mem_univ (f w))).comp w hf
theorem differentiableAt_logSeries (hH : PowerSeriesHolomorphy.Properties) {f : E → ComplexMatrix2}
    {w : E} (hf : DifferentiableAt ℂ f w) (hw : ComplexMatrix2.operatorNorm (f w - 1) < 1) :
    DifferentiableAt ℂ (fun v => ComplexMatrix2.logSeries (f v)) w :=
  (differentiableAt_of_isHolomorphicVia hH hH.2.2.2.2.2 (M := f w) hw).comp w hf
theorem differentiableAt_matrix_inv {f : E → ComplexMatrix2} {w : E} (hf : DifferentiableAt ℂ f w)
    (hu : IsUnit (f w)) : DifferentiableAt ℂ (fun v => (f v)⁻¹) w := by
  have h : DifferentiableAt ℂ (Ring.inverse : ComplexMatrix2 → ComplexMatrix2) (f w) :=
    differentiableAt_inverse hu
  have hc := h.comp w hf
  have heq : (Ring.inverse ∘ f) = fun v => (f v)⁻¹ := by
    funext v
    simp [Matrix.nonsing_inv_eq_ringInverse]
  rwa [heq] at hc
theorem differentiableAt_scalar_mul (z : ℂ) {f : E → ComplexMatrix2} {w : E}
    (hf : DifferentiableAt ℂ f w) : DifferentiableAt ℂ (fun v => z • f v) w :=
  hf.const_smul z
theorem isUnit_of_det_eq_one {M : ComplexMatrix2} (h : M.det = 1) : IsUnit M := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.isUnit_of_det_eq_one <;> assumption
end MatrixMaps
section TupleMaps
variable {ι : Type}
theorem supNorm_lt_iff [Finite ι] {s : ℝ} (hs : 0 < s) (A : ι → ComplexMatrix2) :
    supNorm A < s ↔ ∀ i, ComplexMatrix2.operatorNorm (A i) < s := by
  constructor
  · intro h i
    exact lt_of_le_of_lt
      (le_ciSup (Set.finite_range fun i => ComplexMatrix2.operatorNorm (A i)).bddAbove i) h
  · intro h
    rcases isEmpty_or_nonempty ι with he | he
    · simpa [supNorm, Real.iSup_of_isEmpty] using hs
    · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => ComplexMatrix2.operatorNorm (A i))
      rw [supNorm, ← hi]
      exact h i
theorem isSupOpen_supBall [Finite ι] {r : ℝ} (hr : 0 < r) : IsSupOpen (supBall ι r) := by
  refine ⟨fun A hA => hA.1, fun A hA => ⟨r - supNorm A, sub_pos.2 hA.2, fun B hB hBA => ⟨hB, ?_⟩⟩⟩
  rw [supNorm_lt_iff hr]
  intro i
  have h₁ : ComplexMatrix2.operatorNorm (A i) ≤ supNorm A :=
    le_ciSup (Set.finite_range fun i => ComplexMatrix2.operatorNorm (A i)).bddAbove i
  have h₂ : ComplexMatrix2.operatorNorm ((B - A) i) ≤ supNorm (B - A) :=
    le_ciSup (Set.finite_range fun i => ComplexMatrix2.operatorNorm ((B - A) i)).bddAbove i
  have h₃ : ‖B i‖ ≤ ‖A i‖ + ‖(B - A) i‖ := by
    have : B i = A i + (B - A) i := by simp
    rw [this]
    exact norm_add_le _ _
  show ‖B i‖ < r
  linarith
variable [Fintype ι] (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
  (e : ι ≃ Fin (Fintype.card ι))
theorem differentiable_tupleOfCoords (i : ι) :
    Differentiable ℂ fun w : ComplexCoordinates (Fintype.card ι * 3) =>
      tupleOfCoords β e w i := by
  intro w
  unfold tupleOfCoords tracelessTuple
  exact DifferentiableAt.fun_sum fun k _ => (differentiableAt_apply _ _).smul_const _
theorem tupleOfCoords_mem (w : ComplexCoordinates (Fintype.card ι * 3)) (i : ι) :
    tupleOfCoords β e w i ∈ ComplexMatrix2.traceless :=
  Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (β k).2
theorem isOpen_preimage_supBall {r : ℝ} (hr : 0 < r) :
    IsOpen (tupleOfCoords β e ⁻¹' supBall ι r) := by
  have h : tupleOfCoords β e ⁻¹' supBall ι r =
      ⋂ i, {w | ‖tupleOfCoords β e w i‖ < r} := by
    ext w
    simp only [mem_preimage, mem_iInter, mem_ofPred_eq]
    exact ⟨fun hw => (supNorm_lt_iff hr _).1 hw.2,
      fun hw => ⟨fun i => tupleOfCoords_mem β e w i, (supNorm_lt_iff hr _).2 hw⟩⟩
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt (differentiable_tupleOfCoords β e i).continuous.norm continuous_const
variable {β}
theorem isHolomorphicOnTraceless_of_differentiableAt {r : ℝ} (hr : 0 < r)
    {f : (ι → ComplexMatrix2) → ComplexMatrix2}
    (h : ∀ (e : ι ≃ Fin (Fintype.card ι)) (w : ComplexCoordinates (Fintype.card ι * 3)),
      tupleOfCoords β e w ∈ supBall ι r →
        DifferentiableAt ℂ (fun v => f (tupleOfCoords β e v)) w) :
    IsHolomorphicOnTraceless β matrixEquiv (supBall ι r) f := by
  refine ⟨isSupOpen_supBall hr, fun e => ?_⟩
  have hopen := isOpen_preimage_supBall β e hr
  have hd : ∀ w ∈ tupleOfCoords β e ⁻¹' supBall ι r,
      DifferentiableAt ℂ (matrixEquiv ∘ f ∘ tupleOfCoords β e) w := fun w hw =>
    entriesCLE.differentiableAt.comp w (h e w hw)
  refine ⟨hopen, fun w hw => (hd w hw).continuousAt.continuousWithinAt, fun w hw j => ?_⟩
  have hline : Differentiable ℂ fun ζ : ℂ => w + ζ • stdBasisVector j := by fun_prop
  have hev : ∀ᶠ ζ in 𝓝 (0 : ℂ), w + ζ • stdBasisVector j ∈ tupleOfCoords β e ⁻¹' supBall ι r :=
    hline.continuous.continuousAt.eventually_mem (hopen.mem_nhds (by simpa using hw))
  filter_upwards [hev] with ζ hζ
  exact DifferentiableAt.comp (g := matrixEquiv ∘ f ∘ tupleOfCoords β e) ζ (hd _ hζ)
    (hline ζ)
end TupleMaps
section BondMaps
variable {L m K n : ℕ}
def IsSupportedOn (P : SymmetricBondSet L m K n) (U : BondAtLevel L m K n → ComplexMatrix2) : Prop :=
  (∀ b, b ∉ P.bonds → U b = 1) ∧
    ∀ b : BondAtLevel L m K n, ¬ b.IsPositivelyOriented → U b = (U b.opposite)⁻¹
theorem eval_eq_zero_of_not_mem {P : SymmetricBondSet L m K n} (a : LieBondField P)
    {b : BondAtLevel L m K n} (hb : b ∉ P.bonds) : a.eval b = 0 := by
  have hr : b.opposite ∉ P.bonds := fun h => hb (P.opposite_mem _ h)
  unfold LieBondField.eval
  rw [dif_neg fun h => hb h.1, dif_neg fun h => hr h.1]
theorem isSupportedOn_trivial (P : SymmetricBondSet L m K n) :
    IsSupportedOn P trivialGaugeField :=
  ⟨fun _ _ => rfl, fun _ _ => by simp [trivialGaugeField]⟩
theorem isSupportedOn_expTwist {P : SymmetricBondSet L m K n} (a : LieBondField P)
    {U : BondAtLevel L m K n → ComplexMatrix2} (hU : IsSupportedOn P U) :
    IsSupportedOn P (expTwist (fun b => (a.eval b : ComplexMatrix2)) U) := by
  constructor
  · intro b hb
    have hr : b.opposite ∉ P.bonds := fun h => hb (P.opposite_mem _ h)
    unfold expTwist
    split_ifs
    · simp [eval_eq_zero_of_not_mem a hb, hU.1 b hb, NormedSpace.exp_zero]
    · simp [eval_eq_zero_of_not_mem a hr, hU.1 _ hr, NormedSpace.exp_zero]
  · intro b hb
    simp only [expTwist]
    rw [if_neg hb, if_pos (Bond.opposite_isPositivelyOriented hb)]
theorem extendFromPositive_restrictToPositive {P : SymmetricBondSet L m K n}
    {U : BondAtLevel L m K n → ComplexMatrix2} (h : IsSupportedOn P U) :
    extendFromPositive P.bonds (restrictToPositive P.bonds U) = U := by
  funext b
  unfold extendFromPositive restrictToPositive
  split_ifs with h₁ h₂
  · rfl
  · by_cases hp : b.IsPositivelyOriented
    · exact absurd ⟨P.opposite_mem _ h₂.1, hp⟩ h₁
    · exact (h.2 b hp).symm
  · by_cases hb : b ∈ P.bonds
    · have hp : ¬ b.IsPositivelyOriented := fun hp => h₁ ⟨hb, hp⟩
      exact absurd ⟨P.opposite_mem _ hb, Bond.opposite_isPositivelyOriented hp⟩ h₂
    · exact (h.1 b hb).symm
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem differentiableAt_eval {P : SymmetricBondSet L m K n} {g : E → LieBondField P} {w₀ : E}
    (hg : ∀ b, DifferentiableAt ℂ (fun w => ((g w b : ↥ComplexMatrix2.traceless) : ComplexMatrix2)) w₀)
    (b : BondAtLevel L m K n) :
    DifferentiableAt ℂ
      (fun w => (((g w).eval b : ↥ComplexMatrix2.traceless) : ComplexMatrix2)) w₀ := by
  unfold LieBondField.eval
  by_cases h : b ∈ P.bonds ∧ b.IsPositivelyOriented
  · simp only [dif_pos h]
    exact hg ⟨b, h⟩
  · by_cases h' : b.opposite ∈ P.bonds ∧ b.opposite.IsPositivelyOriented
    · simp only [dif_neg h, dif_pos h', NegMemClass.coe_neg]
      exact (hg ⟨b.opposite, h'⟩).fun_neg
    · simp only [dif_neg h, dif_neg h']
      exact differentiableAt_const _
theorem differentiableAt_expTwist (hH : PowerSeriesHolomorphy.Properties)
    {P : SymmetricBondSet L m K n} {g : E → LieBondField P}
    {V : E → BondAtLevel L m K n → ComplexMatrix2} {w₀ : E}
    (hg : ∀ b, DifferentiableAt ℂ (fun w => ((g w b : ↥ComplexMatrix2.traceless) : ComplexMatrix2)) w₀)
    {b : BondAtLevel L m K n} (hb : b.IsPositivelyOriented)
    (hV : DifferentiableAt ℂ (fun w => V w b) w₀) :
    DifferentiableAt ℂ
      (fun w => expTwist (fun b => (((g w).eval b : ↥ComplexMatrix2.traceless) : ComplexMatrix2))
        (V w) b) w₀ := by
  simp only [expTwist, if_pos hb]
  exact (differentiableAt_matExp hH ((differentiableAt_eval hg b).const_smul Complex.I)).fun_mul hV
end BondMaps
section CompositeMaps
variable {L m K n : ℕ} {s : AveragingScheme} {c : BondAtLevel L m K (n + 1)}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem differentiableAt_of_holomorphicOnAveragingDomain
    {Φ : (BondAtLevel L m K n → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : HolomorphicOnAveragingDomain s c Φ) {U : E → BondAtLevel L m K n → ComplexMatrix2} {w₀ : E}
    (hdef : ∀ᶠ w in 𝓝 w₀, IsSchemeAverageDefined s (U w) c)
    (hsupp : ∀ w, IsSupportedOn (doubleBlockSymmetricSet c) (U w))
    (hdiff : ∀ b : BondAtLevel L m K n, b.IsPositivelyOriented →
      DifferentiableAt ℂ (fun w => U w b) w₀) :
    DifferentiableAt ℂ (fun w => Φ (U w)) w₀ ∧ (Φ (U w₀)).det = 1 := by
  obtain ⟨inst, hol⟩ := hΦ.1
  let v : E → PositiveBondOf (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) → ComplexMatrix2 :=
    fun w => restrictToPositive (bondsInDoubleBlock c) (U w)
  have hv : DifferentiableAt ℂ v w₀ := differentiableAt_pi.2 fun b => hdiff b.1 b.2.2
  have hmem : ∀ᶠ w in 𝓝 w₀, v w ∈ restrictToPositive (bondsInDoubleBlock c) ''
      {W | IsSchemeAverageDefined s W c} := hdef.mono fun w hw => ⟨U w, hw, rfl⟩
  have hx := hmem.self_of_nhds
  obtain ⟨F, hF, hFe⟩ := hol.2.2 _ hx
  have htend : Tendsto v (𝓝 w₀) (𝓝[restrictToPositive (bondsInDoubleBlock c) ''
      {W | IsSchemeAverageDefined s W c}] (v w₀)) :=
    tendsto_nhdsWithin_iff.2 ⟨hv.continuousAt, hmem⟩
  have heq := htend.eventually hFe
  have hext : ∀ w, extendFromPositive (bondsInDoubleBlock c) (v w) = U w := fun w =>
    extendFromPositive_restrictToPositive (hsupp w)
  refine ⟨?_, ?_⟩
  · have hG : DifferentiableAt ℂ (fun w => F (v w) ()) w₀ :=
      differentiableAt_pi.1 (hF.differentiableAt.comp w₀ hv) ()
    refine hG.congr_of_eventuallyEq (heq.mono fun w hw => ?_)
    have h := congrFun hw ()
    simp only [hext] at h
    exact h
  · have h : (Φ (extendFromPositive (bondsInDoubleBlock c) (v w₀))).det = 1 :=
      hol.2.1 hx ()
    rwa [hext] at h
theorem differentiableAt_stepQuantities (hH : PowerSeriesHolomorphy.Properties)
    (hdom : (∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
        ∀ x ∈ sitesInBlock (levelDepth K n) y,
          HolomorphicOnAveragingDomain s c fun W => contourHolonomy s W y x) ∧
      HolomorphicOnAveragingDomain s c fun W => schemeBlockAverage s W c)
    (hfin : ∀ y : SiteAtLevel L m K (n + 1),
      (sitesInBlock (levelDepth K n) y : Set (SiteAtLevel L m K n)).Finite)
    {g₀ g : E → LieBondField (doubleBlockSymmetricSet c)} {w₀ : E}
    (hg₀ : ∀ b, DifferentiableAt ℂ
      (fun w => ((g₀ w b : ↥ComplexMatrix2.traceless) : ComplexMatrix2)) w₀)
    (hg : ∀ b, DifferentiableAt ℂ
      (fun w => ((g w b : ↥ComplexMatrix2.traceless) : ComplexMatrix2)) w₀)
    (hB : ∀ᶠ w in 𝓝 w₀, PolydiscBounds s c (g₀ w) (g w)) :
    (∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y,
        DifferentiableAt ℂ
          (fun w => stepLog s c (g w) (expOfBondField c (g₀ w)) y x) w₀) ∧
    (∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      DifferentiableAt ℂ
        (fun w => stepGaugeLogarithm s c (g w) (expOfBondField c (g₀ w)) y) w₀) ∧
    DifferentiableAt ℂ
      (fun w => stepVariable s c (g w) (expOfBondField c (g₀ w))) w₀ ∧
    DifferentiableAt ℂ (fun w => schemeAverageLog s c (g₀ w)) w₀ := by
  have hB₀ := hB.self_of_nhds
  let U₀ : E → BondAtLevel L m K n → ComplexMatrix2 := fun w => expOfBondField c (g₀ w)
  let U₁ : E → BondAtLevel L m K n → ComplexMatrix2 := fun w => twistedConfig c (g w) (U₀ w)
  have hs₀ : ∀ w, IsSupportedOn (doubleBlockSymmetricSet c) (U₀ w) := fun w =>
    isSupportedOn_expTwist (g₀ w) (isSupportedOn_trivial _)
  have hs₁ : ∀ w, IsSupportedOn (doubleBlockSymmetricSet c) (U₁ w) := fun w =>
    isSupportedOn_expTwist (g w) (hs₀ w)
  have hp₀ : ∀ b : BondAtLevel L m K n, b.IsPositivelyOriented →
      DifferentiableAt ℂ (fun w => U₀ w b) w₀ := fun b hb =>
    differentiableAt_expTwist hH hg₀ (V := fun _ => trivialGaugeField) hb
      (differentiableAt_const _)
  have hp₁ : ∀ b : BondAtLevel L m K n, b.IsPositivelyOriented →
      DifferentiableAt ℂ (fun w => U₁ w b) w₀ := fun b hb =>
    differentiableAt_expTwist hH hg (V := U₀) hb (hp₀ b hb)
  have hd₀ : ∀ᶠ w in 𝓝 w₀, IsSchemeAverageDefined s (U₀ w) c :=
    hB.mono fun w h => h.quantities.variable_bound.1.2.2.1
  have hd₁ : ∀ᶠ w in 𝓝 w₀, IsSchemeAverageDefined s (U₁ w) c :=
    hB.mono fun w h => h.quantities.variable_bound.1.2.1
  have hM₀ := differentiableAt_of_holomorphicOnAveragingDomain hdom.2 hd₀ hs₀ hp₀
  have hM₁ := differentiableAt_of_holomorphicOnAveragingDomain hdom.2 hd₁ hs₁ hp₁
  have hξ : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y,
        DifferentiableAt ℂ (fun w => stepLog s c (g w) (U₀ w) y x) w₀ := by
    intro y hy x hx
    have hC₀ := differentiableAt_of_holomorphicOnAveragingDomain (hdom.1 y hy x hx) hd₀ hs₀ hp₀
    have hC₁ := differentiableAt_of_holomorphicOnAveragingDomain (hdom.1 y hy x hx) hd₁ hs₁ hp₁
    have hR : DifferentiableAt ℂ (fun w => stepRatio s c (g w) (U₀ w) y x) w₀ :=
      hC₁.1.fun_mul (differentiableAt_matrix_inv hC₀.1 (isUnit_of_det_eq_one hC₀.2))
    exact differentiableAt_scalar_mul _
      (differentiableAt_logSeries hH hR (hB₀.quantities.log_bound y hy x hx).1.2.2)
  have hV : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      DifferentiableAt ℂ (fun w => stepGauge s c (g w) (U₀ w) y) w₀ := by
    intro y hy
    have hsum : DifferentiableAt ℂ (fun w => ∑ᶠ x ∈ sitesInBlock (levelDepth K n) y,
        stepLog s c (g w) (U₀ w) y x) w₀ := by
      simp only [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
      exact DifferentiableAt.fun_sum fun x hx => hξ y hy x ((hfin y).mem_toFinset.1 hx)
    exact differentiableAt_matExp hH
      (differentiableAt_scalar_mul _ (differentiableAt_scalar_mul _ hsum))
  have hQ : DifferentiableAt ℂ (fun w => stepProduct s c (g w) (U₀ w)) w₀ :=
    (((differentiableAt_matrix_inv (hV _ (mem_insert _ _)) (Matrix.isUnit_exp _)).fun_mul
      hM₁.1).fun_mul (hV _ (mem_insert_of_mem _ rfl))).fun_mul
      (differentiableAt_matrix_inv hM₀.1 (isUnit_of_det_eq_one hM₀.2))
  refine ⟨hξ, fun y hy => ?_, ?_, ?_⟩
  · exact differentiableAt_scalar_mul _
      (differentiableAt_logSeries hH (hV y hy) (hB₀.quantities.gauge_bound y hy).2.1)
  · exact differentiableAt_scalar_mul _
      (differentiableAt_logSeries hH hQ hB₀.quantities.variable_bound.1.2.2.2)
  · exact differentiableAt_scalar_mul _
      (differentiableAt_logSeries hH hM₀.1 hB₀.average_bound.2.1)
theorem tracelessPart_coe {M : ComplexMatrix2} (h : M ∈ ComplexMatrix2.traceless) :
    (tracelessPart M : ComplexMatrix2) = M := by
  unfold tracelessPart
  rw [dif_pos h]
end CompositeMaps
end BoundedStepHolomorphy
open BoundedStepHolomorphy YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct
theorem HolomorphyOfBoundedStepQuantities.holds
    (hH : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hD : AveragingDomainsOpenAndHolomorphic) : HolomorphyOfBoundedStepQuantities := by
  intro L hL r hr m K n hm hn s c hc hB inst β
  have hdom := hD L hL m K n hm hn s c hc
  have hLpos : 0 < L := by
    have := hL.2
    omega
  have hfin : ∀ y : SiteAtLevel L m K (n + 1),
      (sitesInBlock (levelDepth K n) y : Set (SiteAtLevel L m K n)).Finite := fun _ => by
    have := (ClusterExpansion.RegionPolymers.sublattice_finite hLpos m (levelDepth K n)).to_subtype
    exact Set.toFinite _
  have hι : Finite (PositiveBondsOf (doubleBlockSymmetricSet c)) :=
    Finite.of_injective
      (Sum.inl : PositiveBondsOf (doubleBlockSymmetricSet c) → PositiveBondsOf (doubleBlockSymmetricSet c) ⊕
        PositiveBondsOf (doubleBlockSymmetricSet c)) Sum.inl_injective
  have key := fun (e : (PositiveBondsOf (doubleBlockSymmetricSet c) ⊕
      PositiveBondsOf (doubleBlockSymmetricSet c)) ≃ Fin (Fintype.card _)) w
      (hw : tupleOfCoords β e w ∈ supBall _ r) =>
    differentiableAt_stepQuantities hH hdom.2 hfin
      (g₀ := fun v => firstComponent (tupleOfCoords β e v))
      (g := fun v => secondComponent (tupleOfCoords β e v)) (w₀ := w)
      (fun b => (differentiable_tupleOfCoords β e (.inl b) w).congr_of_eventuallyEq
        (Eventually.of_forall fun v => tracelessPart_coe (tupleOfCoords_mem β e v _)))
      (fun b => (differentiable_tupleOfCoords β e (.inr b) w).congr_of_eventuallyEq
        (Eventually.of_forall fun v => tracelessPart_coe (tupleOfCoords_mem β e v _)))
      (((isOpen_preimage_supBall β e hr).eventually_mem hw).mono fun v hv => by
        have hv' := (supNorm_lt_iff hr _).1 hv.2
        refine hB _ _ ((supNorm_lt_iff hr fun b => _).2 fun b => ?_)
          ((supNorm_lt_iff hr fun b => _).2 fun b => ?_)
        · show ‖(tracelessPart (tupleOfCoords β e v (.inl b)) : ComplexMatrix2)‖ < r
          rw [tracelessPart_coe (tupleOfCoords_mem β e v _)]
          exact hv' _
        · show ‖(tracelessPart (tupleOfCoords β e v (.inr b)) : ComplexMatrix2)‖ < r
          rw [tracelessPart_coe (tupleOfCoords_mem β e v _)]
          exact hv' _)
  exact ⟨fun y hy x hx => isHolomorphicOnTraceless_of_differentiableAt hr fun e w hw =>
      (key e w hw).1 y hy x hx,
    fun y hy => isHolomorphicOnTraceless_of_differentiableAt hr fun e w hw =>
      (key e w hw).2.1 y hy,
    isHolomorphicOnTraceless_of_differentiableAt hr fun e w hw => (key e w hw).2.2.1,
    isHolomorphicOnTraceless_of_differentiableAt hr fun e w hw => (key e w hw).2.2.2⟩
end YangMills.Construction.PeriodicLattice
