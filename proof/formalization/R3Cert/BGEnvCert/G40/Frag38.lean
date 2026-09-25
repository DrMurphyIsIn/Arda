/- Generated: kernel check of cap C = 38. -/
import R3Cert.BGEnvCert.G40.Common
import R3Cert.BGEnvCert.G40.Cap38

namespace R3Cert.EnvCert.G40
open R3Cert.EnvCert

set_option maxRecDepth 100000 in
theorem cap38_ok : capCheck tanTab ldTab phiTab cap38 = true := by decide +kernel

end R3Cert.EnvCert.G40
