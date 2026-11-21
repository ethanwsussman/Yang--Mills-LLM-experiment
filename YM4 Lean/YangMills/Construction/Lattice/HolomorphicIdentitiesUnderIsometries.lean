import YangMills.Construction.Lattice.IteratesOfAComplexConfiguration
import YangMills.Construction.Lattice.LiftToLevelOfAConfigurationOnBonds
import YangMills.Construction.Lattice.SetsOfBondsOfASequenceOfRegions
import YangMills.Construction.Lattice.WeightedWilsonActions
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j j' : ℤ}
def plaquetteBoundary (p : Plaquette L m j) : List (Bond L m j) :=
  [Bond.forwardFrom p.origin p.firstAxis,
    Bond.forwardFrom (p.origin + unitStep L m j p.firstAxis) p.secondAxis,
    (Bond.forwardFrom (p.origin + unitStep L m j p.secondAxis) p.firstAxis).opposite,
    (Bond.forwardFrom p.origin p.secondAxis).opposite]
def restrictToBonds (S : Set (Bond L m j)) (U : Bond L m j → Matrices.ComplexMatrix2) :
    ↥S → Matrices.ComplexMatrix2 :=
  fun b => U b
def IsAnalyticOnSupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : Set (Bond L m j → Matrices.ComplexMatrix2)) (S : Set (Bond L m j))
    (D : Set (Bond L m j → Matrices.ComplexMatrix2))
    (f : (Bond L m j → Matrices.ComplexMatrix2) → E) : Prop :=
  ∃ _ : Fintype ↥S, D ⊆ P ∧
    Matrices.ComplexMatrix2.IsRelativelyOpen (restrictToBonds S '' P) (restrictToBonds S '' D) ∧
    ∀ U ∈ D, ∃ F : (↥S → Matrices.ComplexMatrix2) → E, AnalyticAt ℂ F (restrictToBonds S U) ∧
      ∀ᶠ w in 𝓝 (restrictToBonds S U), ∀ W ∈ D, restrictToBonds S W = w → f W = F w
def IsHolomorphicEquation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (σ : FourTorus L m ≃ FourTorus L m) (P : Set (Bond L m j → Matrices.ComplexMatrix2))
    (S : Set (Bond L m j)) (D₁ D₂ : Set (Bond L m j → Matrices.ComplexMatrix2))
    (f₁ f₂ : (Bond L m j → Matrices.ComplexMatrix2) → E) : Prop :=
  IsAnalyticOnSupport P S (D₁ ∩ D₂) f₁ ∧ IsAnalyticOnSupport P S (D₁ ∩ D₂) f₂ ∧
    (∀ U ∈ D₁ ∩ D₂, f₁ U = f₂ U) ∧ (IsTorusTranslation σ → D₁ = D₂)
def IsHolomorphicEquationOnComplexFields {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (σ : FourTorus L m ≃ FourTorus L m) (S : Set (Bond L m j))
    (f₁ f₂ : (Bond L m j → Matrices.ComplexMatrix2) → E) : Prop :=
  IsHolomorphicEquation σ (complexGaugeFields S) S (complexGaugeFields S)
    (complexGaugeFields S) f₁ f₂
def CommutesHolomorphically (σ : FourTorus L m ≃ FourTorus L m) (S : Set (Bond L m j))
    (F : PartialGaugeField L m j → PartialGaugeField L m j') : Prop :=
  ∀ c : Bond L m j',
    IsHolomorphicEquation σ (complexGaugeFields S) S
      {U ∈ complexGaugeFields S |
        bondImage σ c ∈ (F ⟨bondImage σ '' S, transportGaugeField σ U⟩).support}
      {U ∈ complexGaugeFields S | c ∈ (F ⟨S, U⟩).support}
      (fun U => (F ⟨bondImage σ '' S, transportGaugeField σ U⟩).field (bondImage σ c))
      (fun U => transportGaugeField σ (F ⟨S, U⟩).field (bondImage σ c))
def HasEquivariantSupport (σ : FourTorus L m ≃ FourTorus L m) (S : Set (Bond L m j))
    (F : PartialGaugeField L m j → PartialGaugeField L m j') : Prop :=
  ∀ U ∈ complexGaugeFields S,
    (F ⟨bondImage σ '' S, transportGaugeField σ U⟩).support = bondImage σ '' (F ⟨S, U⟩).support
def PreservesComplexHolonomies (σ : FourTorus L m ≃ FourTorus L m) (i : ℤ) : Prop :=
  ∀ j : ℤ, i ≤ j → ∀ S : Set (Bond L m j), IsReversalClosed S →
    ∀ γ : List (Bond L m j), IsBondPath γ → (∀ b ∈ γ, b ∈ S) →
      IsHolomorphicEquationOnComplexFields σ S
        (fun U => pathHolonomy (transportGaugeField σ U) (pathImage σ γ))
        (fun U => pathHolonomy U γ)
def PreservesComplexPlaquetteHolonomies (ε : SignedFrame → Fin 4 → Fin 4 → ℤˣ)
    (σ : FourTorus L m ≃ FourTorus L m) (i : ℤ) : Prop :=
  ∀ j : ℤ, i ≤ j → ∀ p : Plaquette L m j, ∃ γ : List (Bond L m j), γ <:+: plaquetteBoundary p ∧
    ∀ S : Set (Bond L m j), IsReversalClosed S → (∀ b ∈ plaquetteBoundary p, b ∈ S) →
      IsHolomorphicEquationOnComplexFields σ S
        (fun U => plaquetteHolonomy (transportGaugeField σ U) (plaquetteImage σ p))
        (fun U => pathHolonomy U γ *
          plaquetteHolonomy U p ^ ((ε (linearComponent σ) p.firstAxis p.secondAxis : ℤˣ) : ℤ) *
            (pathHolonomy U γ)⁻¹) ∧
      IsHolomorphicEquationOnComplexFields σ S
        (fun U => plaquetteEnergy (transportGaugeField σ U) (plaquetteImage σ p))
        (fun U => plaquetteEnergy U p)
def PreservesComplexEnergies (σ : FourTorus L m ≃ FourTorus L m) (i : ℤ) : Prop :=
  ∀ j : ℤ, i ≤ j →
    (∀ (c : ℤ) (R : Set (FourTorus L m)), i ≤ c → IsPartitionRegion c R →
      IsHolomorphicEquationOnComplexFields σ (bondsInside R : Set (Bond L m j))
        (fun U => interiorEnergy (σ '' R) (transportGaugeField σ U))
        (fun U => interiorEnergy R U)) ∧
    (∀ f : Plaquette L m j → ℂ,
      IsHolomorphicEquationOnComplexFields σ (univ : Set (Bond L m j))
        (fun U => plaquetteWeightedEnergy (transportPlaquetteFunction σ f)
          (transportGaugeField σ U))
        (fun U => plaquetteWeightedEnergy f U)) ∧
    ∀ f : FourTorus L m → ℂ,
      IsHolomorphicEquationOnComplexFields σ (univ : Set (Bond L m j))
        (fun U => barycenterWeightedEnergy (transportTorusFunction σ f) (transportGaugeField σ U))
        (fun U => barycenterWeightedEnergy f U)
def PreservesComplexContourMeans (σ : FourTorus L m ≃ FourTorus L m) (i : ℤ) : Prop :=
  ∀ K k : ℕ, k < K → i ≤ levelDepth K (k + 1) →
    ∀ (y : SiteAtLevel L m K (k + 1)) (x : SiteAtLevel L m K k),
    x ∈ sitesInBlock (levelDepth K k) y →
    (∀ U ∈ complexGaugeFields (bondsInside (unitBlock y) : Set (BondAtLevel L m K k)),
      Matrices.ComplexMatrix2.familyDiameter
          (contourHolonomies (transportGaugeField σ U) (sitePreimage σ.symm y)
            (sitePreimage σ.symm x)) =
        Matrices.ComplexMatrix2.familyDiameter (contourHolonomies U y x)) ∧
    IsHolomorphicEquation σ
      (complexGaugeFields (bondsInside (unitBlock y) : Set (BondAtLevel L m K k)))
      (bondsInside (unitBlock y) : Set (BondAtLevel L m K k))
      {U ∈ complexGaugeFields (bondsInside (unitBlock y) : Set (BondAtLevel L m K k)) |
        Matrices.ComplexMatrix2.familyDiameter
          (contourHolonomies (transportGaugeField σ U) (sitePreimage σ.symm y)
            (sitePreimage σ.symm x)) <
            Averaging.centreOfMassDiameter}
      {U ∈ complexGaugeFields (bondsInside (unitBlock y) : Set (BondAtLevel L m K k)) |
        Matrices.ComplexMatrix2.familyDiameter (contourHolonomies U y x) <
          Averaging.centreOfMassDiameter}
      (fun U => complexMeanContourHolonomy (transportGaugeField σ U) (sitePreimage σ.symm y)
        (sitePreimage σ.symm x))
      (fun U => complexMeanContourHolonomy U y x)
def PreservesComplexBlockAverages (σ : FourTorus L m ≃ FourTorus L m) (i : ℤ) : Prop :=
  ∀ K : ℕ,
    (∀ k : ℕ, k < K → i ≤ levelDepth K (k + 1) → ∀ S : Set (BondAtLevel L m K k),
      IsReversalClosed S →
      CommutesHolomorphically (j' := levelDepth K (k + 1)) σ S complexPartialBlockAverage) ∧
    ∀ n : ℕ, n ≤ K → i ≤ levelDepth K n → ∀ S : Set (BondAtLevel L m K 0), IsReversalClosed S →
      CommutesHolomorphically σ S fun V => complexIteratePartial V.support V.field n
def PreservesComplexLevelLifts (σ : FourTorus L m ≃ FourTorus L m) (i : ℤ) : Prop :=
  ∀ K k n : ℕ, n ≤ k → k ≤ K → i ≤ levelDepth K k → ∀ S : Set (BondAtLevel L m K k),
    IsReversalClosed S →
      CommutesHolomorphically σ S (bareLiftPartial (K := K)) ∧
      HasEquivariantSupport σ S (bareLiftPartial (K := K)) ∧
      CommutesHolomorphically σ S (complexLevelLiftPartial (K := K) n) ∧
      HasEquivariantSupport σ S (complexLevelLiftPartial (K := K) n)
def PreservesComplexDeterminingIterates (σ : FourTorus L m ≃ FourTorus L m) (i : ℤ) : Prop :=
  ∀ (K k : ℕ) (R : ℕ → Set (FourTorus L m)), k ≤ K → IsDeterminingChain K k R →
    (∀ q ≤ k, ∃ a : ℤ, i ≤ a ∧ a ≤ levelDepth K q ∧ IsPartitionRegion a (R q)) →
    ∀ q ∈ determiningBondSet K k R,
      IsHolomorphicEquation σ
        (complexGaugeFields (bondsInside (R 0) : Set (BondAtLevel L m K 0)))
        (bondsInside (R 0) : Set (BondAtLevel L m K 0))
        {U ∈ complexGaugeFields (bondsInside (R 0) : Set (BondAtLevel L m K 0)) |
          ∀ q' ∈ bondSetImage σ (determiningBondSet K k R),
            ComplexIterateDefinedAt (bondsInside (imageChain σ R 0))
              (transportGaugeField σ U) q'.1 q'.2}
        {U ∈ complexGaugeFields (bondsInside (R 0) : Set (BondAtLevel L m K 0)) |
          ∀ q' ∈ determiningBondSet K k R, ComplexIterateDefinedAt (bondsInside (R 0)) U q'.1 q'.2}
        (fun U => complexIterate (bondsInside (imageChain σ R 0))
          (transportGaugeField σ U) q.1 (bondImage σ q.2))
        (fun U => transportGaugeField σ (complexIterate (bondsInside (R 0)) U q.1)
          (bondImage σ q.2))
def PreservesLinearBlockIterates (σ : FourTorus L m ≃ FourTorus L m) (i : ℤ) : Prop :=
  ∀ K k n : ℕ, k + n ≤ K → i ≤ levelDepth K (k + n) → ∀ c : BondAtLevel L m K (k + n),
    IsHolomorphicEquation σ {A | IsBondForm complexLieAlgebra A}
        (univ : Set (BondAtLevel L m K k)) {A | IsBondForm complexLieAlgebra A}
        {A | IsBondForm complexLieAlgebra A}
        (fun A => linearBlockIterateBetween k n (transportForm σ A) (bondImage σ c))
        (fun A => transportForm σ (linearBlockIterateBetween k n A) (bondImage σ c)) ∧
      IsHolomorphicEquation σ {A | IsBondForm complexLieAlgebra A}
        (univ : Set (BondAtLevel L m K k)) {A | IsBondForm complexLieAlgebra A}
        {A | IsBondForm complexLieAlgebra A}
        (fun A => scaledLinearBlockIterateFrom k n (transportForm σ A) (bondImage σ c))
        (fun A => transportForm σ (scaledLinearBlockIterateFrom k n A) (bondImage σ c))
theorem IsHolomorphicOnFields.of_analytic_formula {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {P D : Set (Bond L m j → Matrices.ComplexMatrix2)} {S : Set (Bond L m j)}
    [Fintype ↥S] {f : (Bond L m j → Matrices.ComplexMatrix2) → E}
    (F : (↥S → Matrices.ComplexMatrix2) → E) (hDP : D ⊆ P)
    (hD : Matrices.ComplexMatrix2.IsRelativelyOpen (restrictToBonds S '' P)
      (restrictToBonds S '' D))
    (hF : ∀ U ∈ D, AnalyticAt ℂ F (restrictToBonds S U))
    (hf : ∀ U ∈ D, f U = F (restrictToBonds S U)) : IsAnalyticOnSupport P S D f :=
  ⟨inferInstance, hDP, hD, fun U hU => ⟨F, hF U hU, Filter.Eventually.of_forall
    fun _ W hW hw => hw ▸ hf W hW⟩⟩
theorem IsAnalyticOnSupport.restrict {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P D D' : Set (Bond L m j → Matrices.ComplexMatrix2)} {S : Set (Bond L m j)}
    {f : (Bond L m j → Matrices.ComplexMatrix2) → E}
    (h : IsAnalyticOnSupport P S D f) (hsub : D' ⊆ D)
    (hD' : Matrices.ComplexMatrix2.IsRelativelyOpen (restrictToBonds S '' P)
      (restrictToBonds S '' D')) :
    IsAnalyticOnSupport P S D' f := by
  obtain ⟨inst, hDP, -, hf⟩ := h
  refine ⟨inst, hsub.trans hDP, hD', fun U hU => ?_⟩
  obtain ⟨F, hF, hev⟩ := hf U (hsub hU)
  exact ⟨F, hF, hev.mono fun w hw W hW => hw W (hsub hW)⟩
theorem isRelativelyOpen_self {E : Type} [TopologicalSpace E] (P : Set E) :
    Matrices.ComplexMatrix2.IsRelativelyOpen P P :=
  ⟨univ, isOpen_univ, (univ_inter P).symm⟩
def extendWithIdentity (S : Set (Bond L m j)) (w : ↥S → Matrices.ComplexMatrix2)
    (b : Bond L m j) : Matrices.ComplexMatrix2 :=
  open Classical in
  if h : b ∈ S then w ⟨b, h⟩ else 1
theorem extendByOne_restrictToBonds {S : Set (Bond L m j)}
    (U : Bond L m j → Matrices.ComplexMatrix2) {b : Bond L m j} (hb : b ∈ S) :
    extendWithIdentity S (restrictToBonds S U) b = U b := by
  simp only [extendWithIdentity, dif_pos hb, restrictToBonds]
theorem pathHolonomy_extendByOne {S : Set (Bond L m j)}
    (U : Bond L m j → Matrices.ComplexMatrix2) {γ : List (Bond L m j)} (hγ : ∀ b ∈ γ, b ∈ S) :
    pathHolonomy (extendWithIdentity S (restrictToBonds S U)) γ = pathHolonomy U γ := by
  unfold pathHolonomy
  congr 1
  exact List.map_congr_left fun b hb => extendByOne_restrictToBonds U (hγ b hb)
theorem analyticAt_extendByOne {S : Set (Bond L m j)} [Fintype ↥S] {b : Bond L m j}
    (hb : b ∈ S) (w : ↥S → Matrices.ComplexMatrix2) :
    AnalyticAt ℂ (fun w : ↥S → Matrices.ComplexMatrix2 => extendWithIdentity S w b) w := by
  have h : (fun w : ↥S → Matrices.ComplexMatrix2 => extendWithIdentity S w b) =
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ↥S => Matrices.ComplexMatrix2) ⟨b, hb⟩ := by
    funext w
    simp only [extendWithIdentity, dif_pos hb, ContinuousLinearMap.proj_apply]
  rw [h]
  exact ContinuousLinearMap.analyticAt _ _
theorem analyticAt_pathHolonomy_extendByOne {S : Set (Bond L m j)} [Fintype ↥S]
    {γ : List (Bond L m j)} (hγ : ∀ b ∈ γ, b ∈ S) (w : ↥S → Matrices.ComplexMatrix2) :
    AnalyticAt ℂ
      (fun w : ↥S → Matrices.ComplexMatrix2 => pathHolonomy (extendWithIdentity S w) γ) w := by
  induction γ with
  | nil =>
    simpa [pathHolonomy] using analyticAt_const
  | cons b γ ih =>
    have h := (analyticAt_extendByOne (hγ b List.mem_cons_self) w).mul
      (ih fun c hc => hγ c (List.mem_cons_of_mem b hc))
    simpa [pathHolonomy, Pi.mul_def] using h
theorem analyticAt_inv_of_det_ne_zero {X : Matrices.ComplexMatrix2} (hX : X.det ≠ 0) :
    AnalyticAt ℂ (fun Y : Matrices.ComplexMatrix2 => Y⁻¹) X := by
  have hu : IsUnit X := (Matrix.isUnit_iff_isUnit_det X).2 (isUnit_iff_ne_zero.2 hX)
  obtain ⟨u, rfl⟩ := hu
  have h : (fun Y : Matrices.ComplexMatrix2 => Y⁻¹) = Ring.inverse := by
    funext Y
    exact Matrix.nonsing_inv_eq_ringInverse Y
  rw [h]
  exact analyticAt_inverse u
end YangMills.Construction.PeriodicLattice
