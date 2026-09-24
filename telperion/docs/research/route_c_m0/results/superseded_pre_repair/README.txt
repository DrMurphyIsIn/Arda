SUPERSEDED (2026-09-23, repair of the coverage defect, README section 4.6).
These records were produced by the pre-repair code, whose box balls arb(fl((xa+xb)/2), (xb-xa)/2) could
miss a box endpoint by up to half an ulp, and whose N-segment padding (+-1e-12) vanished below the double
ulp for x > ~8e3.  They are kept only for comparison; they are NOT certificates.  The certified records are
the files one directory up, produced by the repaired code with its coverage audit.
