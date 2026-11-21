import Compaction.AllOddMinusCertificateClosed
import Compaction.OddMinusBudgetBound
import Compaction.OddMinusVVle
import Compaction.JointWindowWithoutMinus
import Compaction.ArchiveDyadicClosed
import Compaction.PrincipalDyadicClosed
import Compaction.Weber
import GenericHostCertificate
import PrincipalNonresonant
import PrincipalCertificate
import PrincipalTwistCertificate
import RegularOneCertificate
import HeightResonantCertificate
import FullPlusCertificate
import Compaction.SelmerAssembly
import Compaction.MixedGrowth
import Compaction.AuxiliaryPrimes
import Compaction.GenericAndExceptional

/-! Coherent aggregation of the checked certificate constructions.

This file does not assert RH or the missing geometric/automorphic input.
The full-plus statement retains its explicit arithmetic counting assumptions.
Root helper import shims all resolve to the canonical Compaction modules.
-/

#print axioms Compaction.AllOddMinusCertificateClosed.exists_uniform_certificates
#print axioms Compaction.JointWindowWithoutMinus.vwin_of_joint
#print axioms Compaction.ArchiveDyadicClosed.windows
#print axioms Compaction.PrincipalDyadicClosed.windows
#print axioms Compaction.Weber.weber
#print axioms CertificateHour.PrincipalNonresonant.gd
#print axioms CertificateHour.PrincipalTwistCertificate.nonresonant_budget
#print axioms CertificateHour.FullPlusCertificate.with_resonant_bound
