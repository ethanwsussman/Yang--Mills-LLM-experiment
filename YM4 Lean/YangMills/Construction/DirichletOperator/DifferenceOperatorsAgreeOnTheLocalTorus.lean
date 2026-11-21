import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.CubeTorusTransfer
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes.CubeTorus
namespace PartitionCubes.LocalTorusOperators
variable {S : RegionSequence.NestedRegions} {M : ℕ}
structure Match (Q : LevelCube S M) : Prop where
  lap_eq : ∀ f ∈ S.siteFns, VanishesOff (Q.thicken (2 / 3)) f →
    SiteFunctionsMatch Q (dirichletLap f) (latticeLaplacian (restrictSites Q f))
  grad_eq : ∀ f ∈ S.siteFns, VanishesOff (Q.thicken (2 / 3)) f →
    BondFunctionsMatch Q (dDir f) (dTorus (restrictSites Q f))
  grad_adj_eq : ∀ A ∈ S.oneForms, AnchorSupported (Q.thicken (2 / 3)) A →
    SiteFunctionsMatch Q (dDirAdj A) (dTorusAdj (restrictBonds Q A))
  curl_eq : ∀ A ∈ S.oneForms, AnchorSupported (Q.thicken (2 / 3)) A →
    BondFunctionsMatch Q (curlSqDir A) (curlTorusAdj (curlTorus (restrictBonds Q A)))
def Claim : Prop :=
  ∀ (K m M R₁ : ℕ) (S : RegionSequence.NestedRegions), S.IsLevelUnitChain K m M R₁ →
    S.L ^ 5 ≤ M → ∀ Q : LevelCube S M, Q.IsFirstType → Match Q
end PartitionCubes.LocalTorusOperators
end YangMills.Construction
