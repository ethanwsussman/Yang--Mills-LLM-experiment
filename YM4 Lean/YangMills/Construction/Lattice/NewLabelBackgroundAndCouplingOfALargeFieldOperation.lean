import YangMills.Construction.Lattice.NewDomainsOfALargeFieldOperation
import YangMills.Construction.Lattice.PositionDependentCouplings
import YangMills.Construction.Lattice.SmallFieldRegionsOfTheStages
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def fieldProduct {L m K k : ℕ} (V W : BondAtLevel L m K k → Matrices.ComplexMatrix2) :
    BondAtLevel L m K k → Matrices.ComplexMatrix2 :=
  open Classical in
  fun b => if b.IsPositivelyOriented then V b * W b else (V b.opposite * W b.opposite)⁻¹
namespace ScaleLabel
variable {L m K m' k : ℕ} {c : ℕ → ℕ}
def updatedLayer (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (j : ℕ) : Set (BondAtLevel L m K j) :=
  if j < k then
    activeBondsAt K k (S.trimmedDomain r x Q) j ∩
      bondsMeeting (complementRegion (coarseCubeIndex K m' k) (⋃₀ Q))
  else activeBondsAt K k (S.trimmedDomain r x Q) j ∪ bondsMeeting (⋃₀ Q)
def updatedLayerSet (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) : Set (Σ q : ℕ, BondAtLevel L m K q) :=
  {q | q.1 ≤ k ∧ q.2 ∈ S.updatedLayer r x Q q.1}
def boxFieldExtended (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (V' : BondAtLevel L m K k → Matrices.ComplexMatrix2) :
    BondAtLevel L m K k → Matrices.ComplexMatrix2 :=
  open Classical in
  fun b => if b ∈ (bondsMeeting (S.innerBox r x Q) : Set (BondAtLevel L m K k)) then V' b else 1
def updatedDatum (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m)))
    (V : ∀ i : ℕ, BondAtLevel L m K i → Matrices.ComplexMatrix2)
    (V' VΛ : BondAtLevel L m K k → Matrices.ComplexMatrix2) :
    ∀ i : ℕ, BondAtLevel L m K i → Matrices.ComplexMatrix2 :=
  open Classical in
  Function.update V k fun b =>
    if b ∈ (bondsMeeting (⋃₀ Q) : Set (BondAtLevel L m K k)) then
      fieldProduct (S.boxFieldExtended r x Q V') VΛ b
    else V k b
def updatedBackground (ε : ℝ) (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m)))
    (V : ∀ i : ℕ, BondAtLevel L m K i → Matrices.ComplexMatrix2)
    (V' VΛ : BondAtLevel L m K k → Matrices.ComplexMatrix2) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  Classical.epsilon fun U => U ∈ regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k
    (S.absorbedDomain r x Q) (S.updatedLayerSet r x Q) (S.updatedDatum r x Q V V' VΛ)
def trimmedSmallField (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (i : ℕ) : Set (FourTorus L m) :=
  S.stageSmallFieldRegion r x Q (Thresholds.delayDepth L r x k) i
def trimmedCoupling (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (y : FourTorus L m) : ℝ :=
  localCoupling K m' (x 0) (fun j => x (j - 1) - x j)
    (fun j => Nat.log L (Thresholds.minBlockSize L r x j)) (S.trimmedSmallField r x Q) k y
def updatedInvSqCoupling (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (y : FourTorus L m) : ℝ :=
  (⋃₀ Q)ᶜ.indicator (fun y => 1 / S.trimmedCoupling r x Q y ^ 2) y +
    (⋃₀ Q).indicator (fun _ => 1 / Thresholds.couplingAt x k ^ 2) y
def updatedCoupling (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (y : FourTorus L m) : ℝ :=
  S.updatedInvSqCoupling r x Q y ^ (-(1 / 2) : ℝ)
def updatedInvCoupling (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (y : FourTorus L m) : ℝ :=
  S.updatedCoupling r x Q y ^ (-2 : ℤ)
def updatedSmallField (S : ScaleLabel L m K m' c k) (Q : Set (Set (FourTorus L m))) (j : ℕ) :
    Set (FourTorus L m) :=
  open Classical in
  if (cubeMeet K (S.largeFieldOrEmpty j) (⋃₀ Q)).Nonempty then S.smallFieldRegionAt j ∪ ⋃₀ Q
  else S.smallFieldRegionAt j
def outputSmallField (S : ScaleLabel L m K m' c k) (Q Y : Set (Set (FourTorus L m))) (j : ℕ) :
    Set (FourTorus L m) :=
  if j = k then regionDiff (coarseCubeIndex K m' k) (S.updatedSmallField Q k) (⋃₀ Y)
  else S.updatedSmallField Q j
def markedSetAt (S : ScaleLabel L m K m' c k) (j : ℕ) : Set (FourTorus L m) :=
  open Classical in
  if h : j ∈ Set.Icc 1 k then (S.atScale ⟨j, h⟩).markedSet else ∅
def updatedMarkedSet (S : ScaleLabel L m K m' c k) (Q : Set (Set (FourTorus L m))) (j : ℕ) :
    Set (FourTorus L m) :=
  ⋃₀ {P | P ∈ partitionCubesIn (scaledCubeIndex K j (c j)) (S.markedSetAt j) ∧ ∀ X ∈ Q, ¬P ⊆ X}
def updatedScaleData (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (j : ℕ) : ScaleData L m :=
  ⟨S.absorbedDomain r x Q j, S.updatedSmallField Q j, S.updatedMarkedSet Q j⟩
def outputScaleData (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q Y : Set (Set (FourTorus L m))) (j : ℕ) : ScaleData L m :=
  ⟨S.absorbedDomain r x Q j, S.outputSmallField Q Y j, S.updatedMarkedSet Q j⟩
def IsUpdatedLabelOf (r : ℕ) (x : ℕ → ℝ) (S S' : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) : Prop :=
  ∀ j : ScaleIndex k, S'.atScale j = S.updatedScaleData r x Q j
def IsOutputLabelOf (r : ℕ) (x : ℕ → ℝ) (S S' : ScaleLabel L m K m' c k)
    (Q Y : Set (Set (FourTorus L m))) : Prop :=
  ∀ j : ScaleIndex k, S'.atScale j = S.outputScaleData r x Q Y j
end ScaleLabel
end YangMills.Construction.PeriodicLattice
