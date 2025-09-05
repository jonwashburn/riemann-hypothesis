/-!
Non-build tests: check final theorem symbols exist once PRs land.
This file is under `test/` and not part of the `rh` build; it can be used locally.
-/

import rh.Proof.Main

/- If all components are present, the following names should resolve:
 - RH.Proof.Final.RH_xi_from_outer_and_local
 - RH.Proof.Final.RH_xi_from_outer_and_local_oneSafe
 - RH.Proof.Assembly.RH_riemannXi_from_RS_offZeros_oneSafe
 - RH.AcademicFramework.CompletedXi.zero_symmetry_from_fe
 - RH.AcademicFramework.CompletedXi.G_nonzero_on_Ω_away_from_one
 - RH.RS.OuterData
 - RH.RS.Θ_of
 - RH.RS.OffZeros.LocalData
-/

#check RH.Proof.Final.RH_xi_from_outer_and_local
#check RH.Proof.Final.RH_xi_from_outer_and_local_oneSafe
#check RH.Proof.Assembly.RH_riemannXi_from_RS_offZeros_oneSafe
#check RH.AcademicFramework.CompletedXi.zero_symmetry_from_fe
#check RH.AcademicFramework.CompletedXi.G_nonzero_on_Ω_away_from_one
#check RH.RS.OuterData
#check RH.RS.Θ_of
#check RH.RS.OffZeros.LocalData
