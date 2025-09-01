import rh.Cert.KxiPPlus
import rh.Cert.K0PPlus

noncomputable section

namespace RH.AcademicFramework.Certificate

/-! Certificate capabilities availability flags -/

/-- Availability of Kξ analytic bound via closed-strip nonvanishing +
functional-equation factors: defined by existence of `KxiBound` from
`RH.Cert.KxiPPlus.exists_KxiBound_if_factors`. Downstream tracks only
need the existence form. -/
def KxiAvailable : Prop := ∃ Kξ : ℝ, RH.Cert.KxiBound Kξ

/-- Availability of the arithmetic tail nonnegativity `K0 ≥ 0` from the proved lemma. -/
def K0Available : Prop := RH.Cert.K0Available

/-- Readiness flag for certificate chain hooks. -/
def Ready : Prop :=
  KxiAvailable ∧ K0Available ∧ RH.Cert.CertificateReady

/-- From a functional-equation closed-strip factors witness, we get
`KxiAvailable` via the existential `∃ Kξ, KxiBound Kξ`. -/
theorem KxiAvailable_of_factors
    (h : ∃ fac : RH.Cert.FunctionalEquationStripFactors, True) :
    KxiAvailable := by
  exact RH.Cert.exists_KxiBound_if_factors h

/-- If `K0Available` holds and a factors witness exists, the certificate
track is ready (modulo the `CertificateReady` flag exposed by `rh/Cert`). -/
theorem Ready_of_factors
    (hK0 : K0Available)
    (hfac : ∃ fac : RH.Cert.FunctionalEquationStripFactors, True)
    (hCert : RH.Cert.CertificateReady) : Ready := by
  refine And.intro ?hKxi (And.intro hK0 hCert)
  exact KxiAvailable_of_factors hfac

end RH.AcademicFramework.Certificate
