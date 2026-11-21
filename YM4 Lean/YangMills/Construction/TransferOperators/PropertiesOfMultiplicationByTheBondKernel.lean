import YangMills.Construction.TransferOperators.CharacterCoefficientsOfTheOneBondWeight
import YangMills.Construction.TransferOperators.DecayNumbersAdmissiblePairsAndTheOperatorHat
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SpinHarmonics
open Matrices.ComplexMatrix2 TransferOperators
def esupNorm {X : Type*} (H : X → ℂ) : ℝ≥0∞ := ⨆ x, ‖H x‖ₑ
def HasUniformSum {I X : Type*} (T : I → X → ℂ) (S : X → ℂ) : Prop :=
  TendstoUniformly (fun (s : Finset I) x => ∑ i ∈ s, T i x) S atTop
section Components
variable {J : Type} [Finite J]
def isotypicPart (l : J → HalfNatural) (F : HaarL2 J) : (J → specialUnitary) → ℂ :=
  Schatten.kernelApply (haarPi J) (fun p => isotypicKernel l p.1 p.2) F
def isotypicPartSum (l : J → HalfNatural) (F : HaarL2 J) : C(J → specialUnitary, ℂ) :=
  ∑ α ∈ SeveralVariables.indicesWithSpins l,
    (inner ℂ (peterWeylVec α) F : ℂ) • peterWeylFn α
def weightDecayTerm (q : ℕ) (l : J → HalfNatural) : ℝ :=
  (∏ᶠ b, (2 * (l b).toReal + 1)) * ((1 + weightSum l) ^ q)⁻¹
variable (J) in
def weightDecaySum (q : ℕ) : ℝ := ∑' l : J → HalfNatural, weightDecayTerm q l
end Components
def FieldsPreserveProdCoeffSpan (J : Type) [Finite J] : Prop :=
  ∀ (l : J → HalfNatural) (ψ : C(J → specialUnitary, ℂ)), ψ ∈ prodCoeffSpan l →
    (∀ w : List (J × Fin 3), ∃ φ ∈ prodCoeffSpan l, ⇑φ = fieldWord w ψ) ∧
    (∀ (b : J) (u : J → specialUnitary), -∑ ι, rightField b ι (rightField b ι ψ) u =
      (((l b).toReal * ((l b).toReal + 1) : ℝ) : ℂ) * ψ u) ∧
    ‖ψ‖ ≤ (∏ᶠ b, (2 * (l b).toReal + 1)) * ‖toHaarL2 (ψ : (J → specialUnitary) → ℂ)‖ ∧
    ∀ w : List (J × Fin 3), ‖toHaarL2 (fieldWord w ψ)‖ ≤
      (1 + weightSum l) ^ w.length * ‖toHaarL2 (ψ : (J → specialUnitary) → ℂ)‖
def SmoothHasFiniteSobolevDecay (J : Type) [Finite J] : Prop :=
  ∀ F : (J → specialUnitary) → ℂ, F ∈ smoothSet →
    (∀ q, sobolevDecay q (toHaarL2 F) < ∞) ∧
    HasUniformSum (fun l : J → HalfNatural => isotypicPart l (toHaarL2 F)) F
def FiniteSobolevDecayImpliesSmooth (J : Type) [Finite J] : Prop :=
  ∀ F : HaarL2 J, (∀ q, sobolevDecay q F < ∞) →
    (∀ w : List (J × Fin 3), ∑' l : J → HalfNatural,
      esupNorm (fieldWord w (isotypicPart l F)) < ∞) ∧
    ∃ S ∈ (smoothSet : Set ((J → specialUnitary) → ℂ)),
      HasUniformSum (fun l : J → HalfNatural => isotypicPart l F) S ∧
      S =ᵐ[haarPi J] F ∧
      ∀ q, 2 * Nat.card J + 1 ≤ q →
        esupNorm S ≤ ENNReal.ofReal (weightDecaySum J q) * sobolevDecay q F
def WeightDecaySumFinite (J : Type) [Finite J] : Prop :=
  (∀ q, 2 * Nat.card J + 1 ≤ q → Summable (weightDecayTerm q : (J → HalfNatural) → ℝ)) ∧
  ∀ (J' : Type) [Finite J'], Nat.card J' = Nat.card J →
    ∀ q, weightDecaySum J' q = weightDecaySum J q
def mulConst (β : ℝ) {B : Type} (D : B → ℕ) : ℝ :=
  ∏ᶠ b, (2 * (D b : ℝ) + 1) * (besselRatioBound β * (1 + (D b : ℝ))) ^ D b
def derivLossConst (β : ℝ) {B : Type} (D : B → ℕ) (M : ℝ) (q : ℕ) : ℝ :=
  mulConst β D * M * (1 + (degreeTotal D : ℝ) / 2) ^ (q + degreeTotal D)
section Hat
variable {J : Type} [Finite J]
def hatSeriesTerm (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ) (hf : IsRealEntryPolynomial f)
    (F : C(J → specialUnitary, ℂ)) (p : (↥B → HalfNatural) × (↥B → HalfNatural)) :
    C(J → specialUnitary, ℂ) :=
  charCoeffRatio β p.1 p.2 • hatSummand B f hf F p.1 p.2
def hatIsotypicTerm (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (F : C(J → specialUnitary, ℂ)) (lam' lam : J → HalfNatural) : HaarL2 J :=
  charCoeffRatio β (restrictTo B lam) (restrictTo B lam') •
    isotypicProj lam' (toHaarL2 fun u => pullFromPart B f u *
      isotypicPart lam (toHaarL2 (F : (J → specialUnitary) → ℂ)) u)
def hatDoubleTerm (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ) (hf : IsRealEntryPolynomial f)
    (F : C(J → specialUnitary, ℂ)) (lam' lam : J → HalfNatural) : C(J → specialUnitary, ℂ) :=
  charCoeffRatio β (restrictTo B lam) (restrictTo B lam') •
    isotypicPartSum lam' (toHaarL2
      (mulPullback B f hf (isotypicPartSum lam (toHaarL2 (F : (J → specialUnitary) → ℂ))) :
        (J → specialUnitary) → ℂ))
def HatSeriesProperties (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) (D : ↥B → ℕ) (F : C(J → specialUnitary, ℂ)) : Prop :=
  (∀ l' : ↥B → HalfNatural,
    {l : ↥B → HalfNatural | hatSeriesTerm β B f hf F (l, l') ≠ 0}.Finite ∧
    {l : ↥B → HalfNatural | hatSeriesTerm β B f hf F (l, l') ≠ 0}.ncard ≤ ∏ᶠ b, (2 * D b + 1) ∧
    ∀ l : ↥B → HalfNatural, hatSeriesTerm β B f hf F (l, l') ≠ 0 → IsDegreeCompatible D l l') ∧
  (∀ p, (hatSeriesTerm β B f hf F p : (J → specialUnitary) → ℂ) ∈ smoothSet) ∧
  (∀ w : List (J × Fin 3),
    ∑' p, esupNorm (fieldWord w (hatSeriesTerm β B f hf F p)) < ∞) ∧
  Summable (fun p => ‖toHaarL2 (hatSeriesTerm β B f hf F p : (J → specialUnitary) → ℂ)‖) ∧
  HasSum (fun p => toHaarL2 (hatSeriesTerm β B f hf F p : (J → specialUnitary) → ℂ))
    (toHaarL2 (hatSum β B f hf F : (J → specialUnitary) → ℂ)) ∧
  (∀ w : List (J × Fin 3), HasUniformSum
    (fun p => fieldWord w (hatSeriesTerm β B f hf F p))
    (fieldWord w (hatSum β B f hf F))) ∧
  F ∈ hatSummableSet β B f hf ∧
  (hatSum β B f hf F : (J → specialUnitary) → ℂ) ∈ smoothSet ∧
  (∀ q, sobolevDecay q (toHaarL2 (hatSum β B f hf F : (J → specialUnitary) → ℂ)) ≤
    ENNReal.ofReal (derivLossConst β D (esupNorm f).toReal q) *
      sobolevDecay (q + degreeTotal D) (toHaarL2 (F : (J → specialUnitary) → ℂ))) ∧
  ∀ lam' : J → HalfNatural,
    {lam : J → HalfNatural | hatIsotypicTerm β B f F lam' lam ≠ 0}.Finite ∧
    {lam : J → HalfNatural | hatIsotypicTerm β B f F lam' lam ≠ 0}.ncard ≤ ∏ᶠ b, (2 * D b + 1) ∧
    isotypicProj lam' (toHaarL2 (hatSum β B f hf F : (J → specialUnitary) → ℂ)) =
      ∑' lam : J → HalfNatural, hatIsotypicTerm β B f F lam' lam
def fibreAt (B : Set J) (F : C(J → specialUnitary, ℂ)) (z : ↥Bᶜ → specialUnitary) :
    C(↥B → specialUnitary, ℂ) :=
  F.comp ⟨fun v => glue B v z,
    Continuous.comp (g := fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => glue B p.1 p.2)
      (f := fun v : ↥B → specialUnitary => (v, z)) (continuous_glue B)
      (continuous_id.prodMk continuous_const)⟩
def pullFromComplement (B : Set J) (ω : C(↥Bᶜ → specialUnitary, ℂ)) : C(J → specialUnitary, ℂ) :=
  ω.comp ⟨restrictTo Bᶜ, continuous_restrictTo Bᶜ⟩
def precompAlong {J' : Type} (e : J → J') (F : C(J → specialUnitary, ℂ)) :
    C(J' → specialUnitary, ℂ) :=
  F.comp ⟨fun u b => u (e b), continuous_pi fun b => continuous_apply (e b)⟩
omit [Finite J] in
theorem coe_precompAlong_perm (s : Equiv.Perm J) (F : C(J → specialUnitary, ℂ)) :
    (precompAlong s F : (J → specialUnitary) → ℂ) = permuteArgs s F := rfl
def transportAlong {J' : Type} (e : J → J') (B : Set J) (f : (↥B → specialUnitary) → ℂ) :
    (↥(e '' B) → specialUnitary) → ℂ :=
  fun v => f fun b => v ⟨e b, Set.mem_image_of_mem e b.2⟩
def onUnivSubtype (B : Set J) (f : (↥B → specialUnitary) → ℂ) :
    (↥(Set.univ : Set ↥B) → specialUnitary) → ℂ :=
  fun v => f fun b => v ⟨b, Set.mem_univ b⟩
def leftRightTranslate (g g' u : J → specialUnitary) : J → specialUnitary :=
  fun b => g b * u b * (g' b)⁻¹
def HatLinear (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ) (hf : IsRealEntryPolynomial f) :
    Prop :=
  ∀ (a : ℂ) (F H : C(J → specialUnitary, ℂ)), (F : (J → specialUnitary) → ℂ) ∈ smoothSet →
    (H : (J → specialUnitary) → ℂ) ∈ smoothSet →
    hatSum β B f hf (a • F + H) = a • hatSum β B f hf F + hatSum β B f hf H
def HatPreservesReal (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) : Prop :=
  ∀ F : C(J → specialUnitary, ℂ), (F : (J → specialUnitary) → ℂ) ∈ smoothSet →
    (∀ u, (F u).im = 0) → ∀ u, (hatSum β B f hf F u).im = 0
def HatCommutesComplementMul (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) : Prop :=
  ∀ (ω : C(↥Bᶜ → specialUnitary, ℂ)) (F : C(J → specialUnitary, ℂ)),
    (ω : (↥Bᶜ → specialUnitary) → ℂ) ∈ smoothSet →
    (F : (J → specialUnitary) → ℂ) ∈ smoothSet →
    hatSum β B f hf (pullFromComplement B ω * F) =
      pullFromComplement B ω * hatSum β B f hf F
def HatCommutesDisjoint (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) : Prop :=
  ∀ (B' : Set J) (f' : (↥B' → specialUnitary) → ℂ) (hf' : IsRealEntryPolynomial f')
    (F : C(J → specialUnitary, ℂ)),
    B'.Nonempty → Disjoint B' B → (F : (J → specialUnitary) → ℂ) ∈ smoothSet →
    hatSum β B f hf (hatSum β B' f' hf' F) = hatSum β B' f' hf' (hatSum β B f hf F)
def HatFibrewise (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) : Prop :=
  B ≠ Set.univ → ∃ hw : IsRealEntryPolynomial (onUnivSubtype B f),
    ∀ (F : C(J → specialUnitary, ℂ)) (z : ↥Bᶜ → specialUnitary) (v : ↥B → specialUnitary),
      (F : (J → specialUnitary) → ℂ) ∈ smoothSet →
      hatSum β B f hf F (glue B v z) =
        hatSum β Set.univ (onUnivSubtype B f) hw (fibreAt B F z) v
def HatNaturalInjective (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) : Prop :=
  ∀ (J' : Type) [Finite J'] (e : J → J'), Function.Injective e →
    ∃ he : IsRealEntryPolynomial (transportAlong e B f),
      ∀ F : C(J → specialUnitary, ℂ), (F : (J → specialUnitary) → ℂ) ∈ smoothSet →
        hatSum β (e '' B) (transportAlong e B f) he (precompAlong e F) =
          precompAlong e (hatSum β B f hf F)
def HatPreservesBiInvariance (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) : Prop :=
  ∀ (g g' : J → specialUnitary) (F : C(J → specialUnitary, ℂ)),
    (F : (J → specialUnitary) → ℂ) ∈ smoothSet →
    (∀ u, F (leftRightTranslate g g' u) = F u) →
    (∀ u, pullFromPart B f (leftRightTranslate g g' u) = pullFromPart B f u) →
    ∀ u, hatSum β B f hf F (leftRightTranslate g g' u) = hatSum β B f hf F u
def HatEquivariantPerm (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) : Prop :=
  ∀ s : Equiv.Perm J, ∃ hs : IsRealEntryPolynomial (transportAlong s B f),
    ∀ F : C(J → specialUnitary, ℂ), (F : (J → specialUnitary) → ℂ) ∈ smoothSet →
      permuteArgs s (hatSum β B f hf F : (J → specialUnitary) → ℂ) =
        hatSum β (s '' B) (transportAlong s B f) hs (precompAlong s F)
def PolyThroughLinkKernel (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) : Prop :=
  ∀ (F : C(J → specialUnitary, ℂ)) (w : ↥B → specialUnitary) (z : ↥Bᶜ → specialUnitary),
    (F : (J → specialUnitary) → ℂ) ∈ smoothSet →
    f w * ∫ v, linkProductKernel β v w * F (glue B v z) ∂haarPi ↥B =
      ∫ v, linkProductKernel β v w * hatSum β B f hf F (glue B v z) ∂haarPi ↥B
def HatProperties (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) : Prop :=
  HatLinear β B f hf ∧ HatPreservesReal β B f hf ∧
  HatCommutesComplementMul β B f hf ∧ HatCommutesDisjoint β B f hf ∧
  HatFibrewise β B f hf ∧ HatNaturalInjective β B f hf ∧
  HatPreservesBiInvariance β B f hf ∧ HatEquivariantPerm β B f hf ∧
  PolyThroughLinkKernel β B f hf
end Hat
end YangMills.Construction.SpinHarmonics
end
