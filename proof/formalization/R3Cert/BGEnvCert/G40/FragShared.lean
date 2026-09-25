/- Generated: kernel checks of the shared tables. -/
import R3Cert.BGEnvCert.G40.Common
import R3Cert.BGEnvCert.Spider
import R3Cert.BGEnvCert.Assemble

namespace R3Cert.EnvCert.G40
open R3Cert.EnvCert

set_option maxRecDepth 100000 in
theorem tan_ok : tanOK tanTab 0 HG = true := by decide +kernel

theorem ld_ok : ldOK ldTab DMAX = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem spiders_ok : spidersOK phiTab spTab spM 7 40 = true := by decide +kernel

end R3Cert.EnvCert.G40
