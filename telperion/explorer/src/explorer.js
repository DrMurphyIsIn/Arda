/* Telperion Registry Explorer: vanilla canvas/SVG, no libraries.
   conjecture1_proved = False. Every number drawn here is a float model. */
(function () {
  "use strict";

  var REG = JSON.parse(document.getElementById("registry-data").textContent);
  var PLOTS = JSON.parse(document.getElementById("plot-data").textContent);
  var ZEROS = PLOTS.zeros.ordinates;          // gamma_1 .. gamma_2000, float model
  var GITHUB = "https://github.com/DrMurphyIsIn/Arda/blob/main/";

  // ------------------------------------------------------------------ theme
  var root = document.documentElement;
  document.getElementById("theme-toggle").addEventListener("click", function () {
    var cur = root.getAttribute("data-theme");
    var prefersDark = window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches;
    var effective = cur || (prefersDark ? "dark" : "light");
    var next = effective === "dark" ? "light" : "dark";
    root.setAttribute("data-theme", next);
    try { localStorage.setItem("telperion-explorer-theme", next); } catch (e) {}
    redrawAll();
  });
  if (window.matchMedia) {
    window.matchMedia("(prefers-color-scheme: dark)").addEventListener("change", function () { redrawAll(); });
  }
  function cssVar(name) {
    return getComputedStyle(root).getPropertyValue(name).trim() || "#888";
  }

  // ------------------------------------------------------------------ tabs
  var tabs = Array.prototype.slice.call(document.querySelectorAll("nav.tabs .tab"));
  var panels = {};
  tabs.forEach(function (t) { panels[t.dataset.panel] = document.getElementById("panel-" + t.dataset.panel); });
  var drawers = {};   // panel -> function drawing its plots (lazy, so hidden canvases are not drawn)
  function selectTab(name, push) {
    if (!panels[name]) name = "qc";
    tabs.forEach(function (t) {
      var on = t.dataset.panel === name;
      t.setAttribute("aria-selected", on ? "true" : "false");
      panels[t.dataset.panel].classList.toggle("active", on);
    });
    if (push) { try { history.replaceState(null, "", "#" + name); } catch (e) {} }
    if (drawers[name]) drawers[name]();
  }
  tabs.forEach(function (t) { t.addEventListener("click", function () { selectTab(t.dataset.panel, true); }); });
  window.addEventListener("hashchange", function () { selectTab(location.hash.replace("#", ""), false); });

  function redrawAll() {
    var active = tabs.filter(function (t) { return t.getAttribute("aria-selected") === "true"; })[0];
    if (active && drawers[active.dataset.panel]) drawers[active.dataset.panel]();
  }

  // ------------------------------------------------------------------ canvas helpers
  function setupCanvas(id) {
    var c = document.getElementById(id);
    var dpr = window.devicePixelRatio || 1;
    var cssW = c.clientWidth || 1000;
    var aspect = c.getAttribute("height") / c.getAttribute("width");
    var cssH = Math.round(cssW * aspect);
    c.width = Math.round(cssW * dpr); c.height = Math.round(cssH * dpr);
    c.style.height = cssH + "px";
    var ctx = c.getContext("2d");
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, cssW, cssH);
    ctx.font = "11px " + cssVar("--mono");
    return { ctx: ctx, W: cssW, H: cssH };
  }
  function fmt(x, d) { return Number(x).toFixed(d === undefined ? 3 : d); }
  function sci(x) {
    if (x === 0) return "0";
    var e = Math.floor(Math.log10(Math.abs(x)));
    if (e > -3 && e < 5) return String(+x.toPrecision(4));
    return (x / Math.pow(10, e)).toFixed(2) + "e" + e;
  }
  // Linear axes with a margin; returns mapping functions and draws frame + ticks.
  function axes(cv, xmin, xmax, ymin, ymax, opts) {
    opts = opts || {};
    var ctx = cv.ctx, ml = opts.ml || 56, mr = opts.mr || 14, mt = opts.mt || 12, mb = opts.mb || 34;
    var W = cv.W, H = cv.H;
    var X = function (x) { return ml + (x - xmin) / (xmax - xmin) * (W - ml - mr); };
    var Y = function (y) { return H - mb - (y - ymin) / (ymax - ymin) * (H - mt - mb); };
    ctx.strokeStyle = cssVar("--line"); ctx.lineWidth = 1;
    ctx.strokeRect(ml, mt, W - ml - mr, H - mt - mb);
    ctx.fillStyle = cssVar("--muted"); ctx.textAlign = "center"; ctx.textBaseline = "top";
    var xt = opts.xticks || niceTicks(xmin, xmax, 8);
    xt.forEach(function (v) {
      if (v < xmin || v > xmax) return;
      var px = X(v);
      ctx.beginPath(); ctx.moveTo(px, H - mb); ctx.lineTo(px, H - mb + 4); ctx.stroke();
      ctx.fillText(opts.xfmt ? opts.xfmt(v) : String(+v.toPrecision(6)), px, H - mb + 6);
    });
    ctx.textAlign = "right"; ctx.textBaseline = "middle";
    var yt = opts.yticks || niceTicks(ymin, ymax, 6);
    yt.forEach(function (v) {
      if (v < ymin || v > ymax) return;
      var py = Y(v);
      ctx.beginPath(); ctx.moveTo(ml - 4, py); ctx.lineTo(ml, py); ctx.stroke();
      ctx.fillText(opts.yfmt ? opts.yfmt(v) : String(+v.toPrecision(4)), ml - 6, py);
    });
    if (opts.xlabel) { ctx.textAlign = "center"; ctx.textBaseline = "bottom"; ctx.fillText(opts.xlabel, ml + (W - ml - mr) / 2, H - 2); }
    if (opts.ylabel) {
      ctx.save(); ctx.translate(12, mt + (H - mt - mb) / 2); ctx.rotate(-Math.PI / 2);
      ctx.textAlign = "center"; ctx.textBaseline = "middle"; ctx.fillText(opts.ylabel, 0, 0); ctx.restore();
    }
    return { X: X, Y: Y, ml: ml, mr: mr, mt: mt, mb: mb };
  }
  function niceTicks(a, b, n) {
    var span = b - a; if (span <= 0) return [a];
    var raw = span / n, mag = Math.pow(10, Math.floor(Math.log10(raw)));
    var step = raw / mag < 1.5 ? mag : raw / mag < 3.5 ? 2 * mag : raw / mag < 7.5 ? 5 * mag : 10 * mag;
    var out = [], v = Math.ceil(a / step) * step;
    for (; v <= b + 1e-9; v += step) out.push(+v.toPrecision(10));
    return out;
  }
  function polyline(ctx, pts, color, width) {
    ctx.strokeStyle = color; ctx.lineWidth = width || 1.5; ctx.beginPath();
    for (var i = 0; i < pts.length; i++) { if (i === 0) ctx.moveTo(pts[i][0], pts[i][1]); else ctx.lineTo(pts[i][0], pts[i][1]); }
    ctx.stroke();
  }

  // ------------------------------------------------------------------ arithmetic helpers
  // von Mangoldt on prime powers up to LIM: array of [n, log p]
  var VM_LIM = 100000;
  var VM = (function () {
    var s = new Uint8Array(VM_LIM + 1), out = [];
    for (var i = 2; i * i <= VM_LIM; i++) if (!s[i]) for (var j = i * i; j <= VM_LIM; j += i) s[j] = 1;
    for (var p = 2; p <= VM_LIM; p++) if (!s[p]) { var lp = Math.log(p); for (var q = p; q <= VM_LIM; q *= p) out.push([q, lp]); }
    out.sort(function (a, b) { return a[0] - b[0]; });
    return out;
  })();

  // ================================================================== ZOO
  (function zooTab() {
    var Z = PLOTS.zoo;
    document.getElementById("zoo-trust").textContent = Z.trust;
    var tbl = document.getElementById("zoo-matrix");
    var detail = document.getElementById("zoo-detail");
    var html = "<thead><tr><th class=\"clause\">clause</th>";
    Z.objects.forEach(function (o) { html += "<th>" + o + "</th>"; });
    html += "</tr></thead><tbody>";
    Z.clauses.forEach(function (cl) {
      html += "<tr><th class=\"clause\">" + cl[1] + "</th>";
      Z.objects.forEach(function (o) {
        var cell = (Z.matrix[o] || {})[cl[0]];
        var v = cell ? cell.verdict : "N/A";
        var cls = v === "N/A" ? "NA" : v;
        html += "<td class=\"v " + cls + "\" data-o=\"" + o + "\" data-c=\"" + cl[0] + "\">" + (v === "CONDITIONAL" ? "COND" : v) + "</td>";
      });
      html += "</tr>";
    });
    tbl.innerHTML = html + "</tbody>";
    function show(td) {
      Array.prototype.forEach.call(tbl.querySelectorAll("td.sel"), function (x) { x.classList.remove("sel"); });
      td.classList.add("sel");
      var cell = Z.matrix[td.dataset.o][td.dataset.c];
      var meta = Z.object_meta[td.dataset.o] || {};
      detail.innerHTML = "<strong>" + td.dataset.o + "</strong> x <strong>" + cell.name + "</strong>: <span class=\"mono\">" + cell.verdict + "</span><br>" +
        escapeHtml(cell.detail) + "<br><span class=\"note\">variants " + cell.variants.join(", ") +
        "; object spectrum = " + meta.spectrum + ", weights = " + meta.weights + ", certified support count = " + meta.density_count +
        ", off-line pairs = " + meta.offline_pairs + ". Trust: " + Z.trust + ".</span>";
    }
    Array.prototype.forEach.call(tbl.querySelectorAll("td.v"), function (td) {
      td.addEventListener("mouseenter", function () { show(td); });
      td.addEventListener("click", function () { show(td); });
    });
    // variant kill table
    var kill = document.getElementById("zoo-kill");
    var variants = Object.keys(Z.variant_kill);
    var kh = "<thead><tr><th class=\"clause\">variant</th>";
    Z.objects.forEach(function (o) { kh += "<th>" + o + "</th>"; });
    kh += "</tr></thead><tbody>";
    variants.forEach(function (v) {
      kh += "<tr><th class=\"clause\">" + v + "</th>";
      Z.objects.forEach(function (o) {
        var k = Z.variant_kill[v][o];
        var txt = k.killed ? "killed: " + k.fails.join(", ") : "survives";
        kh += "<td class=\"v " + (k.killed ? "FAIL" : "PASS") + "\" title=\"" + escapeHtml(txt) + "\">" + (k.killed ? "killed" : "survives") + "</td>";
      });
      kh += "</tr>";
    });
    kill.innerHTML = kh + "</tbody>";
    var notes = document.getElementById("zoo-notes");
    notes.innerHTML = "Recorded findings: " + Z.w3a_notes.concat(Z.a2_findings).map(escapeHtml).join(" ") +
      " Forged-input controls: " + Z.forged_controls.length + " of " + Z.forged_controls.length +
      " flipped a genuine PASS to FAIL, which is the harness's own check of its discriminating power. Governance failures recorded: " + Z.governance_failures.length + ".";

    // comb / diffraction plot
    var Nsl = document.getElementById("comb-N"), Tsl = document.getElementById("comb-T");
    function drawComb() {
      var N = Math.round(Math.pow(10, +Nsl.value)); var T = +Tsl.value;
      document.getElementById("comb-N-val").textContent = "N = " + N;
      document.getElementById("comb-T-val").textContent = "t in [0, " + T + "]";
      var cv = setupCanvas("comb-canvas");
      var terms = VM.filter(function (t) { return t[0] <= N; });
      var M = 1400, xs = [], ys = [], ymin = 0, ymax = 0;
      for (var i = 0; i <= M; i++) {
        var t = T * i / M, s = 0;
        for (var k = 0; k < terms.length; k++) s += terms[k][1] / Math.sqrt(terms[k][0]) * Math.cos(t * Math.log(terms[k][0]));
        xs.push(t); ys.push(-s); if (-s < ymin) ymin = -s; if (-s > ymax) ymax = -s;
      }
      var pad = (ymax - ymin) * 0.08; ymin -= pad; ymax += pad;
      var ax = axes(cv, 0, T, ymin, ymax, { xlabel: "t", ylabel: "diffraction sum" });
      var ctx = cv.ctx;
      ctx.strokeStyle = cssVar("--accent"); ctx.lineWidth = 1; ctx.globalAlpha = 0.6;
      for (var z = 0; z < ZEROS.length && ZEROS[z] <= T; z++) { ctx.beginPath(); ctx.moveTo(ax.X(ZEROS[z]), ax.Y(ymin)); ctx.lineTo(ax.X(ZEROS[z]), ax.Y(ymax)); ctx.stroke(); }
      ctx.globalAlpha = 1;
      var pts = xs.map(function (x, i) { return [ax.X(x), ax.Y(ys[i])]; });
      polyline(ctx, pts, cssVar("--cool"), 1.4);
      var count = 0; for (z = 0; z < ZEROS.length && ZEROS[z] <= T; z++) count++;
      document.getElementById("comb-readout").textContent = terms.length + " prime powers n <= " + N + "; " + count +
        " bundled ordinates below " + T + " (float model). The dips sharpen at the ordinates as N grows; this is the explicit formula seen from the prime side, truncated, and it is a picture, not a certificate.";
      // stem plot
      var sv = setupCanvas("stem-canvas");
      var umax = Math.log(Math.min(N, 3000)) + 0.2;
      var sax = axes(sv, 0, umax, 0, 0.8, { xlabel: "u = log n", ylabel: "Lambda(n)/sqrt(n)", mb: 30 });
      sv.ctx.strokeStyle = cssVar("--cool"); sv.ctx.lineWidth = 1.2;
      for (k = 0; k < terms.length && terms[k][0] <= 3000; k++) {
        var u = Math.log(terms[k][0]), w = terms[k][1] / Math.sqrt(terms[k][0]);
        sv.ctx.beginPath(); sv.ctx.moveTo(sax.X(u), sax.Y(0)); sv.ctx.lineTo(sax.X(u), sax.Y(Math.min(w, 0.8))); sv.ctx.stroke();
      }
    }
    Nsl.addEventListener("input", drawComb); Tsl.addEventListener("input", drawComb);

    // DH plot
    function drawDH() {
      var D = PLOTS.dh, cv = setupCanvas("dh-canvas");
      var ax = axes(cv, 0, 1, 0, D.t_max, { xlabel: "real part beta", ylabel: "ordinate gamma", xticks: [0, 0.25, 0.5, 0.75, 1] });
      var ctx = cv.ctx;
      ctx.strokeStyle = cssVar("--line"); ctx.setLineDash([4, 4]);
      ctx.beginPath(); ctx.moveTo(ax.X(0.5), ax.Y(0)); ctx.lineTo(ax.X(0.5), ax.Y(D.t_max)); ctx.stroke(); ctx.setLineDash([]);
      ctx.fillStyle = cssVar("--faint");
      for (var z = 0; z < ZEROS.length && ZEROS[z] <= D.t_max; z++) { ctx.beginPath(); ctx.arc(ax.X(0.5) - 60, ax.Y(ZEROS[z]), 2, 0, 2 * Math.PI); ctx.fill(); }
      ctx.textAlign = "center"; ctx.textBaseline = "bottom"; ctx.fillText("zeta (shifted left for legibility)", ax.X(0.5) - 60, ax.mt - 1);
      D.zeros.forEach(function (zz) {
        if (zz.on_line) { ctx.fillStyle = cssVar("--cool"); ctx.beginPath(); ctx.arc(ax.X(0.5), ax.Y(zz.gamma), 2.5, 0, 2 * Math.PI); ctx.fill(); }
        else {
          ctx.fillStyle = cssVar("--refuted");
          [zz.beta, 1 - zz.beta].forEach(function (b) { ctx.beginPath(); ctx.arc(ax.X(b), ax.Y(zz.gamma), 4.5, 0, 2 * Math.PI); ctx.fill(); });
          ctx.textAlign = "left"; ctx.textBaseline = "middle"; ctx.fillStyle = cssVar("--ink");
          ctx.fillText("beta = " + fmt(zz.beta, 4) + ", gamma = " + fmt(zz.gamma, 3), ax.X(Math.max(zz.beta, 1 - zz.beta)) + 8, ax.Y(zz.gamma));
        }
      });
      document.getElementById("dh-readout").textContent = D.on_line_count + " on the line and " + D.off_line_count + " off the line up to height " +
        D.t_max + "; count model " + D.density_model_formula + ". Trust: " + D.trust + ". Each off-line zero is drawn with its mirror image under beta -> 1 - beta.";
    }
    drawers.zoo = function () { drawComb(); drawDH(); };
  })();

  // ================================================================== WALL
  (function wallTab() {
    var Wd = PLOTS.wall;
    var Tsel = document.getElementById("wall-T");
    Wd.ladder_heights.forEach(function (h) {
      var o = document.createElement("option"); o.value = h.T; o.textContent = "T = " + sci(h.T); Tsel.appendChild(o);
    });
    function envelopeAt(lam) {
      var g = Wd.envelope; if (lam < g[0].lam || lam > g[g.length - 1].lam) return null;
      for (var i = 1; i < g.length; i++) if (lam <= g[i].lam) {
        var a = g[i - 1], b = g[i], t = (Math.log(lam) - Math.log(a.lam)) / (Math.log(b.lam) - Math.log(a.lam));
        return Math.exp(Math.log(a.envelopeCsharp) * (1 - t) + Math.log(b.envelopeCsharp) * t);
      }
      return null;
    }
    function drawMap() {
      var cv = setupCanvas("wall-canvas"), ctx = cv.ctx;
      var lc0 = 0, lc1 = 12, ll0 = -4, ll1 = 1;   // log10 c, log10 lam
      var ax = axes(cv, lc0, lc1, ll0, ll1, { xlabel: "centre c (log10)", ylabel: "width lam (log10)", xticks: [0, 2, 4, 6, 8, 10, 12], yticks: [-4, -3, -2, -1, 0, 1],
        xfmt: function (v) { return "1e" + v; }, yfmt: function (v) { return "1e" + v; } });
      var T = +Tsel.value, ht = Wd.ladder_heights.filter(function (h) { return h.T === T; })[0];
      // residual background
      ctx.fillStyle = cssVar("--fail"); ctx.fillRect(ax.X(lc0), ax.Y(ll1), ax.X(lc1) - ax.X(lc0), ax.Y(ll0) - ax.Y(ll1));
      // ladder band: lam >= 1 (floor), c <= T
      ctx.fillStyle = cssVar("--cond");
      ctx.fillRect(ax.X(lc0), ax.Y(ll1), ax.X(Math.log10(T)) - ax.X(lc0), ax.Y(Math.log10(Wd.ladder_floor_lam)) - ax.Y(ll1));
      // envelope free region: c >= envelopeCsharp(lam)
      ctx.fillStyle = cssVar("--pass");
      var rows = 300, curve = [];
      for (var i = 0; i <= rows; i++) {
        var ll = ll0 + (ll1 - ll0) * i / rows, lam = Math.pow(10, ll), e = envelopeAt(lam);
        if (e === null) { if (lam < Wd.envelope[0].lam) e = Wd.envelope[0].envelopeCsharp; else continue; }
        var lx = Math.log10(e); if (lx > lc1) continue;
        var y1 = ax.Y(ll), y2 = ax.Y(ll0 + (ll1 - ll0) * (i + 1) / rows);
        ctx.fillRect(ax.X(Math.max(lx, lc0)), y2, ax.X(lc1) - ax.X(Math.max(lx, lc0)), y1 - y2 + 0.5);
        curve.push([ax.X(Math.max(lx, lc0)), ax.Y(ll)]);
      }
      // unconditional strip lam <= 3/2000
      var lamFree = Math.log10(Wd.lam0_free_float);
      ctx.fillRect(ax.X(lc0), ax.Y(lamFree), ax.X(lc1) - ax.X(lc0), ax.Y(ll0) - ax.Y(lamFree));
      polyline(ctx, curve, cssVar("--proved"), 1.5);
      ctx.strokeStyle = cssVar("--proved"); ctx.beginPath(); ctx.moveTo(ax.X(lc0), ax.Y(lamFree)); ctx.lineTo(ax.X(lc1), ax.Y(lamFree)); ctx.stroke();
      ctx.strokeStyle = cssVar("--faint"); ctx.setLineDash([3, 3]); ctx.beginPath(); ctx.moveTo(ax.X(lc0), ax.Y(Math.log10(Wd.lam0_old))); ctx.lineTo(ax.X(lc1), ax.Y(Math.log10(Wd.lam0_old))); ctx.stroke(); ctx.setLineDash([]);
      ctx.fillStyle = cssVar("--ink"); ctx.textAlign = "left"; ctx.textBaseline = "bottom";
      ctx.fillText("lam = 3/2000: free for every c (MM_gaussian_positivity_small_lam_3e3)", ax.X(lc0) + 6, ax.Y(lamFree) - 3);
      ctx.textBaseline = "top"; ctx.fillText("lam = 1e-7, the earlier threshold (MM_gaussian_positivity_small_lam)", ax.X(lc0) + 6, ax.Y(Math.log10(Wd.lam0_old)) + 3);
      ctx.textAlign = "left"; ctx.textBaseline = "middle";
      ctx.fillText("ladder band (conditional on WindowOnLine c D; schematic edges)", ax.X(lc0) + 6, ax.Y(0.55));
      ctx.textAlign = "center";
      ctx.fillText("the residual R: RH", ax.X(Math.log10(T) + 1.4), ax.Y(-0.9));
      ctx.textAlign = "right"; ctx.fillText("free beyond envelopeCsharp(lam)", ax.X(lc1) - 6, ax.Y(-1.6));
      var pa03 = Wd.envelope.filter(function (r) { return r.lam === 0.3; })[0];
      var pa1 = Wd.envelope.filter(function (r) { return r.lam === 1; })[0];
      document.getElementById("wall-readout").textContent = "T = " + sci(T) + ": " + (ht ? ht.status : "") +
        "\nprimeAbs(0.3) = " + fmt(pa03.primeAbs, 2) + ", envelopeCsharp(0.3) = " + sci(pa03.envelopeCsharp) +
        "; primeAbs(1) = " + fmt(pa1.primeAbs, 2) + ", envelopeCsharp(1) = " + sci(pa1.envelopeCsharp) + " (series truncated at n <= " + sci(Wd.prime_table_limit) + ", float)." +
        "\nThe band's true left edge is lamThreshold(c, D, d, delta) >= 1, not 1. " + Wd.trust;
    }
    Tsel.addEventListener("change", drawMap);

    // complex helper for the injected off-line zero: Re[ z^2 exp(-2 lam z^2) ], z = x + i y
    function reTermF(x, y, lam) {
      var re2 = x * x - y * y, im2 = 2 * x * y;              // z^2
      var er = Math.exp(-2 * lam * re2), ang = -2 * lam * im2;  // exp(-2 lam z^2)
      return er * (re2 * Math.cos(ang) - im2 * Math.sin(ang));
    }
    function reTermTheta(x, y, lam) {
      var re2 = x * x - y * y, im2 = 2 * x * y;
      return Math.exp(-2 * lam * re2) * Math.cos(-2 * lam * im2);
    }
    function faceSum(c, lam, kind, inject) {
      var s = 0, g, x;
      var cut = Math.sqrt(40 / (2 * lam));
      for (var j = 0; j < ZEROS.length; j++) {
        g = ZEROS[j]; x = g - c;
        if (Math.abs(x) < cut) s += kind === "F" ? x * x * Math.exp(-2 * lam * x * x) : Math.exp(-2 * lam * x * x);
        x = -g - c;
        if (Math.abs(x) < cut) s += kind === "F" ? x * x * Math.exp(-2 * lam * x * x) : Math.exp(-2 * lam * x * x);
      }
      if (inject) {   // rho = 0.7 + 40 i and its partner 0.3 + 40 i: gamma = 40 -/+ 0.2 i; plus the negatives
        var pts = [[40 - c, -0.2], [40 - c, 0.2], [-40 - c, -0.2], [-40 - c, 0.2]];
        pts.forEach(function (p) { s += kind === "F" ? reTermF(p[0], p[1], lam) : reTermTheta(p[0], p[1], lam); });
      }
      return s;
    }
    var Flam = document.getElementById("F-lam"), Fc = document.getElementById("F-c"), Finj = document.getElementById("F-inject");
    function drawF() {
      var lam = Math.pow(10, +Flam.value), C = +Fc.value, inj = Finj.checked;
      document.getElementById("F-lam-val").textContent = "lam = " + fmt(lam, 4);
      document.getElementById("F-c-val").textContent = "c in [0, " + C + "]";
      var cv = setupCanvas("F-canvas"), M = 1200, xs = [], ys = [], ymin = 0, ymax = 0;
      for (var i = 0; i <= M; i++) { var c = C * i / M, v = faceSum(c, lam, "F", inj); xs.push(c); ys.push(v); if (v < ymin) ymin = v; if (v > ymax) ymax = v; }
      var pad = (ymax - ymin) * 0.08 || 1; ymin -= pad; ymax += pad;
      var ax = axes(cv, 0, C, ymin, ymax, { xlabel: "centre c", ylabel: "F(c, lam)", yfmt: sci });
      var ctx = cv.ctx;
      ctx.strokeStyle = cssVar("--faint"); ctx.beginPath(); ctx.moveTo(ax.X(0), ax.Y(0)); ctx.lineTo(ax.X(C), ax.Y(0)); ctx.stroke();
      polyline(ctx, xs.map(function (x, i) { return [ax.X(x), ax.Y(ys[i])]; }), cssVar("--cool"), 1.4);
      var neg = ys.filter(function (v) { return v < 0; }).length;
      document.getElementById("F-readout").textContent = "min F = " + sci(ymin + pad) + ", max F = " + sci(ymax - pad) +
        (inj ? "; with the fictitious off-line zero the curve dips negative at " + neg + " of " + (M + 1) + " sampled centres" + (neg ? "" : " (none at this width: the dip needs lam of order 1/0.2^2 = 25, beyond this slider)") : "; all bundled zeros are placed on the line, so no negative value is possible here") +
        ". First 2000 ordinates only, float model; terms beyond 40 e-folds dropped.";
    }
    Flam.addEventListener("input", drawF); Fc.addEventListener("input", drawF); Finj.addEventListener("change", drawF);

    var Tlam = document.getElementById("th-lam"), Thalf = document.getElementById("th-half");
    function drawTheta() {
      var lam = Math.pow(10, +Tlam.value), C = 120;
      document.getElementById("th-lam-val").textContent = "lam = " + fmt(lam, 4) + (Thalf.checked ? ", lam/4 = " + fmt(lam / 4, 5) : "");
      var cv = setupCanvas("th-canvas"), M = 1200, xs = [], ys = [], ys2 = [], ymax = 0;
      for (var i = 0; i <= M; i++) {
        var c = C * i / M, v = faceSum(c, lam, "T", false); xs.push(c); ys.push(v); if (v > ymax) ymax = v;
        if (Thalf.checked) { var v2 = faceSum(c, lam / 4, "T", false) * 0.5; ys2.push(v2); if (v2 > ymax) ymax = v2; }
      }
      var ax = axes(cv, 0, C, 0, ymax * 1.08, { xlabel: "centre c", ylabel: "Theta(c, lam)", yfmt: sci });
      polyline(cv.ctx, xs.map(function (x, i) { return [ax.X(x), ax.Y(ys[i])]; }), cssVar("--cool"), 1.4);
      if (Thalf.checked) polyline(cv.ctx, xs.map(function (x, i) { return [ax.X(x), ax.Y(ys2[i])]; }), cssVar("--accent"), 1.4);
      document.getElementById("th-readout").textContent = "Blue: Theta at width lam. Red: sqrt(lam'/lam) Theta(., lam') at lam' = lam/4, i.e. the heat-smoothed copy with the identity's prefactor removed. " +
        "The heat identity says the red curve is the blue one convolved with a Gaussian of variance (lam - lam')/(4 lam lam'). Under RH (all bundled zeros on the line) both are nonnegative. Float model, first 2000 ordinates.";
    }
    Tlam.addEventListener("input", drawTheta); Thalf.addEventListener("change", drawTheta);
    drawers.wall = function () { drawMap(); drawF(); drawTheta(); };
  })();

  // ================================================================== LI FACE
  (function liTab() {
    var L = PLOTS.li;
    function nSmooth(t) { return t / (2 * Math.PI) * Math.log(t / (2 * Math.PI)) - t / (2 * Math.PI) + 7 / 8; }
    var Tstar = (function () { var lo = ZEROS[ZEROS.length - 1] * 0.9, hi = ZEROS[ZEROS.length - 1] * 1.1; for (var i = 0; i < 80; i++) { var m = (lo + hi) / 2; if (nSmooth(m) < ZEROS.length) lo = m; else hi = m; } return (lo + hi) / 2; })();
    function lambda(N) {
      var s = 0;
      for (var j = 0; j < ZEROS.length; j++) { var th = 2 * Math.atan(1 / (2 * ZEROS[j])); s += 2 * (1 - Math.cos(N * th)); }
      // smooth tail: u = 1/t, integrand (1/2pi) log(1/(2 pi u)) 4 sin^2(N atan(u/2)) / u^2, u in (0, 1/T*]
      var K = 400, h = (1 / Tstar) / K, tail = 0;
      for (var k = 0; k <= K; k++) {
        var u = k * h, f;
        if (u === 0) f = 0; else { var sn = Math.sin(N * Math.atan(u / 2)); f = Math.log(1 / (2 * Math.PI * u)) / (2 * Math.PI) * 4 * sn * sn / (u * u); }
        tail += f * (k === 0 || k === K ? 1 : (k % 2 ? 4 : 2));
      }
      return s + tail * h / 3;
    }
    var Nsl = document.getElementById("li-N"), Ssel = document.getElementById("li-scale");
    function drawLi() {
      var Nmax = +Nsl.value, sq = Ssel.value === "sqrt";
      document.getElementById("li-N-val").textContent = "N = 1.." + Nmax;
      var vals = []; for (var N = 1; N <= Nmax; N++) vals.push(lambda(N));
      var tr = function (v) { return sq ? Math.sqrt(Math.max(v, 0)) : v; };
      var ymax = Math.max.apply(null, vals.map(tr)) * 1.08;
      var cv = setupCanvas("li-canvas"), ax = axes(cv, 0.5, Nmax + 0.5, 0, ymax, { xlabel: "N", ylabel: sq ? "sqrt(lambda_N)" : "lambda_N" });
      var ctx = cv.ctx, bw = (ax.X(2) - ax.X(1)) * 0.8;
      vals.forEach(function (v, i) {
        var N = i + 1;
        ctx.fillStyle = N <= 5 ? cssVar("--proved") : N <= 20 ? cssVar("--cool") : cssVar("--faint");
        ctx.fillRect(ax.X(N) - bw / 2, ax.Y(tr(v)), bw, ax.Y(0) - ax.Y(tr(v)));
      });
      ctx.strokeStyle = cssVar("--accent"); ctx.lineWidth = 2;
      L.rungs.forEach(function (r) { if (r.N <= Nmax) { ctx.beginPath(); ctx.moveTo(ax.X(r.N) - bw / 2 - 2, ax.Y(tr(r.hlo_float))); ctx.lineTo(ax.X(r.N) + bw / 2 + 2, ax.Y(tr(r.hlo_float))); ctx.stroke(); } });
      var worst = 0; L.rungs.forEach(function (r) { var d = Math.abs(vals[r.N - 1] - r.hlo_float) / r.hlo_float; if (d > worst) worst = d; });
      document.getElementById("li-readout").textContent = "lambda_1 = " + vals[0].toFixed(9) + " (paired sum over 2000 ordinates + smooth tail from T* = " + fmt(Tstar, 2) + "); " +
        "red ticks are the 20 certified lower bounds hlo from LiPositivity.lean (Arb-conditional); largest relative gap between this float model and a tick: " + sci(worst) + ". " +
        "Nothing here is a kernel value of lambda_N; the kernel facts are the sign statements listed above.";
    }
    Nsl.addEventListener("input", drawLi); Ssel.addEventListener("change", drawLi);
    function drawRate() {
      var cv = setupCanvas("rate-canvas");
      var ax = axes(cv, 0, 13, 0, 14, { xlabel: "verified height T (log10)", ylabel: "rungs bought, n + 1 (log10)", xticks: [0, 2, 4, 6, 8, 10, 12], yticks: [0, 2, 4, 6, 8, 10, 12, 14],
        xfmt: function (v) { return "1e" + v; }, yfmt: function (v) { return "1e" + v; } });
      var p1 = [], p2 = [];
      for (var i = 0; i <= 200; i++) {
        var lt = 13 * i / 200, T = Math.pow(10, lt);
        p1.push([ax.X(lt), ax.Y(Math.log10(3 * Math.PI * T / 2))]);
        if (T > 0.5) p2.push([ax.X(lt), ax.Y(Math.log10(2 * Math.PI * (T - 0.5)))]);
      }
      polyline(cv.ctx, p1, cssVar("--faint"), 1.3); polyline(cv.ctx, p2, cssVar("--cool"), 1.6);
      var ctx = cv.ctx;
      [[4000, "--open", "T = 4000: RH_li_rungs_of_height_4000_sharp (Arb-conditional), n <= 25128"], [3e12, "--draft", "T = 3e12: Platt-Trudgian, literature"]].forEach(function (m) {
        var x = ax.X(Math.log10(m[0])), y = ax.Y(Math.log10(2 * Math.PI * (m[0] - 0.5)));
        ctx.fillStyle = cssVar(m[1]); ctx.beginPath(); ctx.arc(x, y, 5, 0, 2 * Math.PI); ctx.fill();
        ctx.fillStyle = cssVar("--ink"); ctx.textAlign = m[0] > 1e9 ? "right" : "left"; ctx.textBaseline = "bottom"; ctx.fillText(m[2], x + (m[0] > 1e9 ? -8 : 8), y - 6);
      });
      document.getElementById("rate-readout").textContent = "Rungs 0..4 are free of any height hypothesis (RH_li_rungs_lt_five); every other rung is priced in height, and the tail is infinite at every finite T.";
    }
    drawers.li = function () { drawLi(); drawRate(); };
  })();

  // ================================================================== DE BRUIJN-NEWMAN
  // Every curve here is a float model of a stated bound. Blue = kernel-checked in this registry,
  // orange = a model or our own finding, gray = a published result not kernel-checked here.
  (function dbnTab() {
    var D = PLOTS.dbn;
    var byId = {}; REG.nodes.forEach(function (n) { byId[n.id] = n; });
    var thSl = document.getElementById("dbn-theta"), tSl = document.getElementById("dbn-t");
    var y0Sl = document.getElementById("dbn-y0"), pushSl = document.getElementById("dbn-push");
    var bounds = {}; D.bounds.forEach(function (b) { bounds[b.key] = b; });
    function lamOf(theta) { return 2 * (theta - 0.5) * (theta - 0.5); }
    function thetaTxt(th) {
      var named = [[1, "1"], [0.875, "7/8"], [5 / 6, "5/6"], [0.5, "1/2"]];
      for (var i = 0; i < named.length; i++) if (Math.abs(th - named[i][0]) < 0.002) return named[i][1] + " = " + fmt(named[i][0], 4);
      return fmt(th, 4);
    }
    function surfaceRing(ctx, x, y, r, fill) {
      ctx.fillStyle = cssVar("--surface"); ctx.beginPath(); ctx.arc(x, y, r + 2, 0, 2 * Math.PI); ctx.fill();
      ctx.fillStyle = fill; ctx.beginPath(); ctx.arc(x, y, r, 0, 2 * Math.PI); ctx.fill();
    }
    Array.prototype.forEach.call(document.querySelectorAll(".dbn-preset"), function (b) {
      b.addEventListener("click", function () { thSl.value = b.dataset.theta; drawAll(); });
    });

    // ---- (a) the strip in the s-plane
    function drawSplane() {
      var th = +thSl.value, cv = setupCanvas("dbn-splane"), ctx = cv.ctx;
      var ax = axes(cv, -0.15, 1.15, 0, 52, { xlabel: "Re s", ylabel: "Im s", xticks: [0, 0.25, 0.5, 0.75, 1], mb: 32 });
      var top = ax.Y(52), bot = ax.Y(0);
      ctx.fillStyle = cssVar("--sunk"); ctx.fillRect(ax.X(0), top, ax.X(1) - ax.X(0), bot - top);
      ctx.fillStyle = cssVar("--dbn-k-soft");
      ctx.fillRect(ax.X(th), top, ax.X(1) - ax.X(th), bot - top);
      ctx.fillRect(ax.X(0), top, ax.X(1 - th) - ax.X(0), bot - top);
      ctx.strokeStyle = cssVar("--line"); ctx.lineWidth = 1;
      [0, 1].forEach(function (x) { ctx.beginPath(); ctx.moveTo(ax.X(x), top); ctx.lineTo(ax.X(x), bot); ctx.stroke(); });
      ctx.setLineDash([4, 4]); ctx.beginPath(); ctx.moveTo(ax.X(0.5), top); ctx.lineTo(ax.X(0.5), bot); ctx.stroke(); ctx.setLineDash([]);
      ctx.strokeStyle = cssVar("--dbn-k"); ctx.lineWidth = 2;
      [th, 1 - th].forEach(function (x) { ctx.beginPath(); ctx.moveTo(ax.X(x), top); ctx.lineTo(ax.X(x), bot); ctx.stroke(); });
      for (var z = 0; z < ZEROS.length && ZEROS[z] <= 52; z++) surfaceRing(ctx, ax.X(0.5), ax.Y(ZEROS[z]), 4, cssVar("--faint"));
      ctx.fillStyle = cssVar("--ink"); ctx.textBaseline = "top";
      ctx.textAlign = "left"; ctx.fillText("Re s = theta", ax.X(th) + 5, top + 4);
      ctx.textAlign = "right"; ctx.fillText("Re s = 1 - theta", ax.X(1 - th) - 5, top + 4);
      ctx.textAlign = "center"; ctx.textBaseline = "bottom"; ctx.fillStyle = cssVar("--muted");
      if (th - 0.5 > 0.04) ctx.fillText("not excluded", ax.X(0.5), bot - 4);
      else ctx.fillText(th === 0.5 ? "theta = 1/2: only the line is left. That is RH." : "only a thin band is left", ax.X(0.5) + 120, bot - 4);
    }

    // ---- (a) the Lambda number line
    var lineHit = [];
    function drawLine(hoverKey) {
      var th = +thSl.value, lam = lamOf(th), cv = setupCanvas("dbn-line"), ctx = cv.ctx, W = cv.W, H = cv.H;
      var ml = 56, mr = 24, lo = -0.05, hi = 0.55, ay = Math.round(H * 0.42);
      var X = function (v) { return ml + (v - lo) / (hi - lo) * (W - ml - mr); };
      // where Lambda can still be, given the chosen theta and Rodgers-Tao's published Lambda >= 0
      ctx.fillStyle = cssVar("--sunk"); ctx.fillRect(X(0), ay - 10, X(lam) - X(0), 20);
      ctx.strokeStyle = cssVar("--muted"); ctx.lineWidth = 1;
      ctx.beginPath(); ctx.moveTo(X(lo), ay); ctx.lineTo(X(hi), ay); ctx.stroke();
      ctx.fillStyle = cssVar("--muted"); ctx.textAlign = "center"; ctx.textBaseline = "top";
      [0, 0.1, 0.2, 0.3, 0.4, 0.5].forEach(function (v) { ctx.beginPath(); ctx.moveTo(X(v), ay); ctx.lineTo(X(v), ay + 4); ctx.stroke(); });
      ctx.textAlign = "left"; ctx.textBaseline = "middle"; ctx.fillText("Lambda", 4, ay);
      // markers: [key, row (negative = above the axis), colour]
      // [key, row (negative = above the axis), colour, label alignment]: rows chosen so no two labels overlap
      var spec = [["debruijn", -2, "--dbn-k", "right"], ["qrh", -1, "--dbn-k", "left"], ["floor", -2, "--dbn-m", "right"],
                  ["p15", 1, "--faint", "right"], ["pt", 2, "--faint", "right"], ["rt", 3, "--faint", "left"]];
      lineHit = [];
      spec.forEach(function (s) {
        var b = bounds[s[0]], x = X(b.value), row = s[1], col = cssVar(s[2]);
        var ly = ay + row * 26 + (row < 0 ? -6 : 6);
        ctx.strokeStyle = col; ctx.lineWidth = hoverKey === s[0] ? 3 : 2;
        if (b.kind === "published" || b.kind === "published lower bound") ctx.setLineDash([3, 3]);
        ctx.beginPath(); ctx.moveTo(x, ay); ctx.lineTo(x, ly); ctx.stroke(); ctx.setLineDash([]);
        surfaceRing(ctx, x, ay, 4, col);
        var txt = b.exact + "  " + (b.kind === "kernel-checked" ? "kernel-checked" : b.kind === "architecture floor" ? "architecture floor (theta = 5/6)" : b.label.replace(/: Lambda >= 0$/, ", lower bound"));
        if (b.kind === "published") txt = b.exact + "  " + b.label + ", published";
        if (s[0] === "debruijn") txt = "1/2  de Bruijn 1950, kernel-checked";
        if (s[0] === "qrh") txt = "9/32  QRH route, kernel-checked";
        ctx.fillStyle = cssVar("--ink"); ctx.textBaseline = row < 0 ? "bottom" : "top";
        ctx.textAlign = s[3]; var tx = s[3] === "right" ? x - 4 : x + 4;
        ctx.fillText(txt, tx, ly);
        lineHit.push({ key: s[0], x: x });
      });
      // the slider's theta
      var sx = X(lam);
      ctx.fillStyle = cssVar("--ink"); ctx.beginPath(); ctx.moveTo(sx, ay - 3); ctx.lineTo(sx - 6, ay - 15); ctx.lineTo(sx + 6, ay - 15); ctx.closePath(); ctx.fill();
      ctx.textAlign = lam > 0.4 ? "right" : "left"; ctx.textBaseline = "bottom";
      ctx.fillText("theta = " + thetaTxt(th) + " gives Lambda <= " + fmt(lam, 5), lam > 0.4 ? sx - 8 : sx + 8, 14);
      var rd = "theta = " + thetaTxt(th) + ": Delta = 2(theta - 1/2) = " + fmt(2 * (th - 0.5), 4) + ", so every zero of H_0 has |Im z| <= " + fmt(2 * (th - 0.5), 4) +
        ", and every zero of H_t is real for t >= 2(theta - 1/2)^2 = " + fmt(lam, 5) + ".\n";
      if (th === 0.5) rd += "theta = 1/2 is RH itself, and the bound becomes Lambda <= 0.";
      else if (lam > 0.22) rd += "This is weaker than the published 0.22 (Polymath15) and 0.2 (Platt-Trudgian).";
      else if (lam > 0.2) rd += "This would beat Polymath15's published 0.22 but not Platt-Trudgian's 0.2.";
      else rd += "This would beat every published upper bound; no half-plane this far left is known.";
      if (th < 5 / 6 - 1e-9 && th > 0.5) rd += " It is below the sextic-sparsity floor theta = 5/6, so that architecture cannot reach it.";
      rd += "\nOnly theta = 1 (the trivial strip) and theta = 7/8 (OpenAI's QRH) are kernel-checked half-planes in this registry; every other slider position is hypothetical. The gray band is where Lambda can still lie, given the published Lambda >= 0.";
      if (hoverKey) { var hb = bounds[hoverKey]; rd += "\n" + hb.label + ": " + hb.exact + " (" + hb.kind + "). " + hb.where + "."; }
      document.getElementById("dbn-theta-val").textContent = "theta = " + thetaTxt(th);
      document.getElementById("dbn-line-readout").textContent = rd;
    }
    var lineCv = document.getElementById("dbn-line");
    lineCv.addEventListener("pointermove", function (e) {
      var r = lineCv.getBoundingClientRect(), x = e.clientX - r.left, best = null, bd = 14;
      lineHit.forEach(function (h) { var d = Math.abs(h.x - x); if (d < bd) { bd = d; best = h.key; } });
      drawLine(best);
    });
    lineCv.addEventListener("pointerleave", function () { drawLine(null); });

    // ---- (b) the flow
    var X0 = 70;     // the toy pair's real part, between the images of the 4th and 5th zeros
    function toy(t, y0, k) {   // (z - X0)^2 + y0^2 - 2 (1 + k) t = 0
      var q = y0 * y0 - 2 * (1 + k) * t;
      return q >= 0 ? { im: Math.sqrt(q), re: 0 } : { im: 0, re: Math.sqrt(-q) };
    }
    function env(t, Delta) { return Math.sqrt(Math.max(Delta * Delta - 2 * t, 0)); }
    var hoverT = null;
    function drawFlow() {
      var th = +thSl.value, Delta = 2 * (th - 0.5), t = hoverT === null ? +tSl.value : hoverT;
      var f = +y0Sl.value, k = +pushSl.value, y0 = f * Delta, tStar = Delta * Delta / 2;
      document.getElementById("dbn-t-val").textContent = "t = " + fmt(+tSl.value, 4);
      document.getElementById("dbn-y0-val").textContent = fmt(f, 2) + " Delta";
      document.getElementById("dbn-push-val").textContent = k === 0 ? "none (exact quadratic)" : "x " + fmt(1 + k, 2);
      var cv = setupCanvas("dbn-flow"), ctx = cv.ctx;
      var ax = axes(cv, 0, 0.55, 0, 1.08, { xlabel: "time t", ylabel: "|Im z|", xticks: [0, 0.1, 0.2, 0.28125, 0.4, 0.5], xfmt: function (v) { return v === 0.28125 ? "9/32" : String(v); } });
      var M = 400, pk = [], p1 = [], pt = [];
      for (var i = 0; i <= M; i++) {
        var tt = 0.55 * i / M;
        pk.push([ax.X(tt), ax.Y(env(tt, Delta))]); p1.push([ax.X(tt), ax.Y(env(tt, 1))]); pt.push([ax.X(tt), ax.Y(toy(tt, y0, k).im)]);
      }
      ctx.setLineDash([5, 4]); polyline(ctx, p1, cssVar("--faint"), 1.5); ctx.setLineDash([]);
      polyline(ctx, pk, cssVar("--dbn-k"), 2);
      polyline(ctx, pt, cssVar("--dbn-m"), 2);
      // the time all zeros are real
      ctx.strokeStyle = cssVar("--dbn-k"); ctx.lineWidth = 1; ctx.setLineDash([2, 3]);
      ctx.beginPath(); ctx.moveTo(ax.X(tStar), ax.Y(0)); ctx.lineTo(ax.X(tStar), ax.Y(1.08)); ctx.stroke(); ctx.setLineDash([]);
      ctx.fillStyle = cssVar("--ink"); ctx.textAlign = tStar > 0.35 ? "right" : "left"; ctx.textBaseline = "top";
      ctx.fillText("all zeros real from t = 2(theta - 1/2)^2 = " + fmt(tStar, 5), ax.X(tStar) + (tStar > 0.35 ? -6 : 6), ax.Y(1.08) + 4);
      ctx.textAlign = "left"; ctx.textBaseline = "bottom"; ctx.fillStyle = cssVar("--muted");
      ctx.fillText("theta = 1 envelope", ax.X(0.02), ax.Y(env(0.02, 1)) - 4);
      // hairline at the chosen time, with markers
      ctx.strokeStyle = cssVar("--ink"); ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(ax.X(t), ax.Y(0)); ctx.lineTo(ax.X(t), ax.Y(1.08)); ctx.stroke();
      var e = env(t, Delta), ty = toy(t, y0, k);
      surfaceRing(ctx, ax.X(t), ax.Y(e), 4, cssVar("--dbn-k"));
      surfaceRing(ctx, ax.X(t), ax.Y(ty.im), 4, cssVar("--dbn-m"));
      // z-plane snapshot
      var zv = setupCanvas("dbn-zplane"), zc = zv.ctx;
      var zx = axes(zv, 0, 130, -1.08, 1.08, { xlabel: "Re z", ylabel: "Im z", yticks: [-1, -0.5, 0, 0.5, 1], mb: 30 });
      zc.fillStyle = cssVar("--dbn-k-soft"); zc.fillRect(zx.X(0), zx.Y(e), zx.X(130) - zx.X(0), zx.Y(-e) - zx.Y(e));
      zc.strokeStyle = cssVar("--dbn-k"); zc.lineWidth = 2;
      [e, -e].forEach(function (v) { zc.beginPath(); zc.moveTo(zx.X(0), zx.Y(v)); zc.lineTo(zx.X(130), zx.Y(v)); zc.stroke(); });
      zc.strokeStyle = cssVar("--line"); zc.lineWidth = 1; zc.beginPath(); zc.moveTo(zx.X(0), zx.Y(0)); zc.lineTo(zx.X(130), zx.Y(0)); zc.stroke();
      for (var z = 0; z < ZEROS.length && 2 * ZEROS[z] <= 130; z++) surfaceRing(zc, zx.X(2 * ZEROS[z]), zx.Y(0), 4, cssVar("--faint"));
      var pair = ty.im > 0 ? [[X0, ty.im], [X0, -ty.im]] : [[X0 - ty.re, 0], [X0 + ty.re, 0]];
      pair.forEach(function (p) { surfaceRing(zc, zx.X(p[0]), zx.Y(p[1]), 5, cssVar("--dbn-m")); });
      zc.fillStyle = cssVar("--ink"); zc.textAlign = "left"; zc.textBaseline = "bottom";
      zc.fillText("toy pair (model)", zx.X(X0) + 9, zx.Y(Math.max(ty.im, 0)) - 4);
      zc.fillStyle = cssVar("--muted"); zc.textBaseline = "top";
      zc.fillText("z = 2 gamma at t = 0 (float model)", zx.X(2 * ZEROS[0]) - 20, zx.Y(0) + 8);
      zc.textAlign = "right"; zc.textBaseline = "bottom"; zc.fillStyle = cssVar("--ink");
      zc.fillText(e > 0 ? "allowed band |Im z| <= " + fmt(e, 4) : "band closed: every zero is real", zx.X(130) - 6, zx.Y(Math.max(e, 0)) - 4);
      document.getElementById("dbn-flow-readout").textContent = "t = " + fmt(t, 4) + (hoverT === null ? "" : " (hover)") +
        ": envelope |Im z| <= sqrt(max(Delta^2 - 2t, 0)) = " + fmt(e, 4) + " with Delta = " + fmt(Delta, 4) + " from theta = " + thetaTxt(th) +
        ". Toy pair: " + (ty.im > 0 ? "Re z = " + X0 + ", |Im z| = " + fmt(ty.im, 4) : "collided at t = " + fmt(y0 * y0 / (2 * (1 + k)), 4) + "; now two real zeros at Re z = " + X0 + " +/- " + fmt(ty.re, 4)) + ".\n" +
        "With no extra push the toy is the exact flow of the quadratic (z - " + X0 + ")^2 + y0^2 - 2t under the same heat equation dH/dt = -d^2H/dz^2 that H_t satisfies, so it moves at exactly the bound's rate; a push imitates crowding by neighbours. It is a model of the bound, not a zero of zeta. Float model.";
    }
    var flowCv = document.getElementById("dbn-flow");
    flowCv.addEventListener("pointermove", function (e) {
      var r = flowCv.getBoundingClientRect(), x = e.clientX - r.left, ml = 56, mr = 14;
      var t = (x - ml) / (r.width - ml - mr) * 0.55;
      hoverT = t < 0 || t > 0.55 ? null : t; drawFlow();
    });
    flowCv.addEventListener("pointerleave", function () { hoverT = null; drawFlow(); });

    // ---- (c) Lambda_min(X)
    var C = D.lambda_curve, hoverPt = null, ptHit = [];
    function fitAt(X) { return C.fit.a / Math.log(X / (4 * Math.PI)) + C.fit.b; }
    function drawHeight() {
      var cv = setupCanvas("dbn-height"), ctx = cv.ctx;
      var x0 = 4, x1 = 11.3;
      var ax = axes(cv, x0, x1, 0, 0.75, { xlabel: "barrier height X (log10)", ylabel: "Lambda", xticks: [4, 5, 6, 7, 8, 9, 10, 11],
        xfmt: function (v) { return "1e" + v; }, yticks: [0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7] });
      var feas = Math.log10(2 * 6.4e5);
      ctx.fillStyle = cssVar("--sunk"); ctx.fillRect(ax.X(x0) + 1, ax.Y(0.75) + 1, ax.X(feas) - ax.X(x0), ax.Y(0) - ax.Y(0.75) - 2);
      ctx.fillStyle = cssVar("--muted"); ctx.textAlign = "left"; ctx.textBaseline = "bottom";
      ctx.fillText("kernel-feasible heights", ax.X(x0) + 6, ax.Y(0) - 4);
      // kernel-checked lines
      [[9 / 32, "9/32 = 0.28125, kernel-checked (QRH route, every height at once)", [], "left"], [0.5, "1/2, kernel-checked (de Bruijn 1950)", [6, 4], "right"]].forEach(function (l) {
        ctx.strokeStyle = cssVar("--dbn-k"); ctx.lineWidth = 2; ctx.setLineDash(l[2]);
        ctx.beginPath(); ctx.moveTo(ax.X(x0), ax.Y(l[0])); ctx.lineTo(ax.X(x1), ax.Y(l[0])); ctx.stroke(); ctx.setLineDash([]);
        ctx.fillStyle = cssVar("--ink"); ctx.textAlign = l[3]; ctx.textBaseline = "bottom";
        ctx.fillText(l[1], l[3] === "left" ? ax.X(x0) + 6 : ax.X(x1) - 6, ax.Y(l[0]) - 3);
      });
      // the fit
      var pf = [];
      for (var i = 0; i <= 200; i++) { var lx = x0 + (x1 - x0) * i / 200, v = fitAt(Math.pow(10, lx)); if (v <= 0.75) pf.push([ax.X(lx), ax.Y(v)]); }
      ctx.setLineDash([5, 4]); polyline(ctx, pf, cssVar("--muted"), 1.5); ctx.setLineDash([]);
      // height needed for 9/32 (fit)
      var need = Math.log10(C.needed_for_nine_thirtyseconds_X);
      ctx.strokeStyle = cssVar("--muted"); ctx.lineWidth = 1; ctx.setLineDash([2, 3]);
      ctx.beginPath(); ctx.moveTo(ax.X(need), ax.Y(9 / 32)); ctx.lineTo(ax.X(need), ax.Y(0)); ctx.stroke(); ctx.setLineDash([]);
      ctx.fillStyle = cssVar("--muted"); ctx.textAlign = "left"; ctx.textBaseline = "bottom";
      ctx.fillText("X ~ 3.9e8 to match 9/32", ax.X(need) + 5, ax.Y(0.1));
      // the published Polymath15 point
      var pp = C.p15_point, px = ax.X(Math.log10(pp.X)), py = ax.Y(pp.lambda);
      surfaceRing(ctx, px, py, 5, cssVar("--faint"));
      ctx.fillStyle = cssVar("--ink"); ctx.textAlign = "right"; ctx.textBaseline = "top"; ctx.fillText("Polymath15: 0.22 at X ~ 6e10 (published)", px - 8, py + 6);
      // our points
      ptHit = [];
      C.points.forEach(function (p, j) {
        var x = ax.X(Math.log10(p.X)), y = ax.Y(p.lambda);
        surfaceRing(ctx, x, y, hoverPt === j ? 6 : 4.5, cssVar("--dbn-m"));
        ptHit.push({ j: j, x: x, y: y });
      });
      ctx.fillStyle = cssVar("--ink"); ctx.textAlign = "left"; ctx.textBaseline = "bottom";
      var first = C.points[0]; ctx.fillText("Lambda_min(X), floating numerics", ax.X(Math.log10(first.X)) + 8, ax.Y(first.lambda) - 4);
      ptHit.push({ j: "p15", x: px, y: py });
      var rd = C.trust + ". Fit: " + C.fit.formula + ". Source: " + C.source + ".";
      if (hoverPt !== null) {
        if (hoverPt === "p15") rd = pp.label + ": Lambda <= 0.22 at X ~ 6e10, from a large published computation; not kernel-checked here.\n" + rd;
        else { var q = C.points[hoverPt]; rd = "X/2 = " + sci(q.X_half) + " (barrier X = " + sci(q.X) + ", " + q.row + "): Lambda_min = " + q.lambda + " at t0 = " + q.t0 + ", y0 = " + q.y0 + "; fit gives " + fmt(fitAt(q.X), 4) + ".\n" + rd; }
      }
      document.getElementById("dbn-height-readout").textContent = rd;
    }
    var hCv = document.getElementById("dbn-height");
    hCv.addEventListener("pointermove", function (e) {
      var r = hCv.getBoundingClientRect(), x = e.clientX - r.left, y = e.clientY - r.top, best = null, bd = 400;
      ptHit.forEach(function (h) { var d = (h.x - x) * (h.x - x) + (h.y - y) * (h.y - y); if (d < bd) { bd = d; best = h.j; } });
      if (best !== hoverPt) { hoverPt = best; drawHeight(); }
    });
    hCv.addEventListener("pointerleave", function () { hoverPt = null; drawHeight(); });
    (function table() {
      var h = "<thead><tr><th>X/2</th><th>barrier X</th><th>t0</th><th>y0</th><th>Lambda_min (floating)</th><th>row</th></tr></thead><tbody>";
      C.points.forEach(function (p) { h += "<tr><td>" + sci(p.X_half) + "</td><td>" + sci(p.X) + "</td><td>" + p.t0 + "</td><td>" + p.y0 + "</td><td>" + p.lambda + "</td><td>" + escapeHtml(p.row) + "</td></tr>"; });
      h += "<tr><td>" + sci(C.p15_point.X / 2) + "</td><td>" + sci(C.p15_point.X) + "</td><td>0.20</td><td>0.20</td><td>0.22</td><td>" + escapeHtml(C.p15_point.label) + "</td></tr>";
      document.getElementById("dbn-height-table").innerHTML = h + "</tbody>";
    })();

    // ---- (d) the nodes, read from the registry data
    (function nodes() {
      var box = document.getElementById("dbn-nodes"), out = "";
      D.node_ids.forEach(function (id) {
        var n = byId[id]; if (!n) return;
        var pv = n.provenance || {}, comp = pv.comparator;
        var pills = "<span class=\"pill " + n.status + "\">" + n.status + "</span><span class=\"pill tag\">" + escapeHtml(n.kind) + "</span>";
        if (n.readback) pills += "<span class=\"pill tag\">" + escapeHtml(n.readback.independence) + "</span>";
        if (n.conditional) pills += "<span class=\"pill warnp\">conditional: see hypotheses</span>";
        if (id === D.headline_id) pills += "<span class=\"pill tag\">headline: Lambda &le; 9/32</span>";
        var s = "<div class=\"card\"><h4>" + escapeHtml(n.id) + "</h4><div class=\"meta\">" + pills + "</div><div class=\"title\">" + escapeHtml(n.title) + "</div>";
        if (n.proof) s += "<div class=\"meta\">artifact <a href=\"" + escapeHtml(n.proof.artifact_url) + "\">" + escapeHtml(n.proof.artifact) + "</a>" + (n.coverage.jobs.length ? "; compiled by " + escapeHtml(n.coverage.jobs.join(", ")) : "") + "</div>";
        var bits = [];
        if (comp) bits.push("Comparator judge run " + (comp.run_url ? "<a href=\"" + escapeHtml(comp.run_url) + "\">" + escapeHtml(comp.run_id) + "</a>" : escapeHtml(comp.run_id)) + " on " + escapeHtml(comp.date) + ", theorem <code>" + escapeHtml(comp.theorem) + "</code>");
        else bits.push("Comparator judge: not recorded");
        if (n.readback) bits.push("readback by " + escapeHtml(n.readback.auditor) + " on " + escapeHtml(n.readback.date));
        s += "<div class=\"note\">" + bits.join(" &middot; ") + "</div>";
        if (n.statement) s += "<details><summary>statement and hypotheses (verbatim registry statement module)</summary><pre>" + escapeHtml(n.statement) + "</pre></details>";
        out += s + "</div>";
      });
      box.innerHTML = out;
      document.getElementById("dbn-support").innerHTML = "These rest on the dbn island's " + D.support_ids.map(function (id) {
        var n = byId[id]; return "<code>" + escapeHtml(id) + "</code> (" + (n ? n.status + (n.readback ? ", " + escapeHtml(n.readback.independence) : "") : "not in registry") + ")";
      }).join(", ") + ". The flow theorem is <code>" + escapeHtml(D.flow_theorem) + "</code>; <code>H_t</code> is defined in <code>" + escapeHtml(D.definitions) + "</code>.";
      var R = D.release;
      document.getElementById("dbn-repo").href = R.repo;
      document.getElementById("dbn-doi").href = "https://doi.org/" + R.doi_version;
    })();

    function drawAll() { drawSplane(); drawLine(null); drawFlow(); drawHeight(); }
    thSl.addEventListener("input", drawAll);
    [tSl, y0Sl, pushSl].forEach(function (el) { el.addEventListener("input", drawFlow); });
    drawers.dbn = drawAll;
  })();

  // ================================================================== THE ZETA' BOX
  // Blue = kernel-checked, orange = model (the de Bruijn-Newman pair). Every grid drawn here is a float
  // model: mpmath values bundled at build time, or double arithmetic on the exact coefficients of M. The
  // kernel's own numbers (budgets, derivative tests) are the rationals in PLOTS.speiser.exact.
  (function speiserTab() {
    var S = PLOTS.speiser, E = S.exact, Fd = S.float, P = E.params, G = Fd.grid;
    var byId = {}; REG.nodes.forEach(function (n) { byId[n.id] = n; });
    var r = P.r_float, rho = P.rho_float, R = r + rho, F = P.F_float, sig = P.sigma_float;
    var FR = P.F_rho_float;
    var discSl = document.getElementById("sp-disc");

    // ---- colours: a sequential ramp --sunk -> --cool -> --ink, lightness-monotone in both themes
    function rgb(s) {
      s = s.trim();
      if (s[0] === "#") { var h = s.length === 4 ? s.replace(/[0-9a-f]/gi, function (c) { return c + c; }) : s; return [parseInt(h.slice(1, 3), 16), parseInt(h.slice(3, 5), 16), parseInt(h.slice(5, 7), 16)]; }
      var m = s.match(/[\d.]+/g); return m ? [+m[0], +m[1], +m[2]] : [128, 128, 128];
    }
    function ramp() {
      var a = rgb(cssVar("--sunk")), b = rgb(cssVar("--cool")), c = rgb(cssVar("--ink"));
      return function (t) {
        t = t < 0 ? 0 : t > 1 ? 1 : t;
        var p = t < 0.5 ? a : b, q = t < 0.5 ? b : c, u = t < 0.5 ? t * 2 : (t - 0.5) * 2;
        return "rgb(" + Math.round(p[0] + (q[0] - p[0]) * u) + "," + Math.round(p[1] + (q[1] - p[1]) * u) + "," + Math.round(p[2] + (q[2] - p[2]) * u) + ")";
      };
    }
    function ring(ctx, x, y, rad, fill) {
      ctx.fillStyle = cssVar("--surface"); ctx.beginPath(); ctx.arc(x, y, rad + 2, 0, 2 * Math.PI); ctx.fill();
      ctx.fillStyle = fill; ctx.beginPath(); ctx.arc(x, y, rad, 0, 2 * Math.PI); ctx.fill();
    }
    function halo(ctx, text, x, y) {   // a label legible over coloured cells: a surface-coloured pill behind it
      var w = ctx.measureText(text).width + 6, h = 15;
      var x0 = ctx.textAlign === "center" ? x - w / 2 : ctx.textAlign === "right" ? x - w + 3 : x - 3;
      var y0 = ctx.textBaseline === "middle" ? y - h / 2 : ctx.textBaseline === "bottom" ? y - h + 2 : y - 2;
      var fill = ctx.fillStyle; ctx.globalAlpha = 0.85; ctx.fillStyle = cssVar("--surface"); ctx.fillRect(x0, y0, w, h); ctx.globalAlpha = 1;
      ctx.fillStyle = fill; ctx.fillText(text, x, y);
    }
    function circle(ctx, x, y, rad, stroke, width, dash) {
      ctx.strokeStyle = stroke; ctx.lineWidth = width || 1.5; ctx.setLineDash(dash || []);
      ctx.beginPath(); ctx.arc(x, y, rad, 0, 2 * Math.PI); ctx.stroke(); ctx.setLineDash([]);
    }
    // a canvas whose height follows the data (equal-aspect plots), then the shared setup
    function sized(id, aspect) {
      var c = document.getElementById(id), w = +c.getAttribute("width");
      c.setAttribute("height", Math.round(w * aspect)); return setupCanvas(id);
    }
    function inv(cv, ax, xmin, xmax, ymin, ymax) {
      return {
        x: function (px) { return xmin + (px - ax.ml) / (cv.W - ax.ml - ax.mr) * (xmax - xmin); },
        y: function (py) { return ymin + (cv.H - ax.mb - py) / (cv.H - ax.mt - ax.mb) * (ymax - ymin); }
      };
    }
    function pos(cvEl, e) { var b = cvEl.getBoundingClientRect(); return [e.clientX - b.left, e.clientY - b.top]; }

    // ---- the bundled grid of log10 |zeta'| and log10 |zeta| (float model)
    var dRe = (G.re1 - G.re0) / (G.ncols - 1), dIm = (G.im1 - G.im0) / (G.nrows - 1);
    function gridAt(re, im) {
      var i = Math.round((re - G.re0) / dRe), j = Math.round((im - G.im0) / dIm);
      if (i < 0 || i >= G.ncols || j < 0 || j >= G.nrows) return null;
      var k = j * G.ncols + i;
      return { re: G.re0 + i * dRe, im: G.im0 + j * dIm, lz: G.log10_abs_zeta[k] / G.scale, ldz: G.log10_abs_dzeta[k] / G.scale,
               clipped: Math.abs(G.log10_abs_dzeta[k]) >= G.clip || Math.abs(G.log10_abs_zeta[k]) >= G.clip };
    }
    function inBox(re, im) { return re >= 0.25 && re <= 0.375 && im >= 6 && im <= 10; }
    function discOf(re, im, rad) {
      for (var i = 0; i < E.discs.length; i++) { var d = E.discs[i], dx = re - sig, dy = im - d.tc_float; if (dx * dx + dy * dy <= rad * rad) return i; }
      return -1;
    }
    function gridText(g) {
      if (!g) return "";
      return " |zeta'| ~ " + (g.clipped ? "(clipped)" : sci(Math.pow(10, g.ldz))) + ", |zeta| ~ " + (g.clipped ? "(clipped)" : sci(Math.pow(10, g.lz))) + " at the nearest grid point " + fmt(g.re, 4) + " + " + fmt(g.im, 3) + " i (mpmath, float model)";
    }

    // ---- complex polynomials from the exported coefficients (double arithmetic)
    function peval(coef, hre, him) {
      var ar = 0, ai = 0;
      for (var k = coef.length - 1; k >= 0; k--) { var tr = ar * hre - ai * him, ti = ar * him + ai * hre; ar = coef[k][0] + tr; ai = coef[k][1] + ti; }
      return [ar, ai];
    }
    function pderiv(coef) { var out = []; for (var k = 1; k < coef.length; k++) out.push([coef[k][0] * k, coef[k][1] * k]); return out; }
    function pabs(coef, hre, him) { var v = peval(coef, hre, him); return Math.sqrt(v[0] * v[0] + v[1] * v[1]); }
    var MP = E.discs.map(function (d) { return pderiv(d.M_float); });
    var MP_FORGED = pderiv(E.forged_disc0.M_float);

    // ---- (a) statement, axioms and the node card, read from the registry
    (function stepA() {
      var node = byId[S.node_id], L = S.lean;
      document.getElementById("sp-statement").textContent = node && node.statement ? node.statement : "(statement module missing in this checkout)";
      document.getElementById("sp-axioms").textContent = S.axioms;
      var a = document.getElementById("sp-artifact-link"); a.href = L.artifact_url; a.textContent = L.artifact;
      if (!node) { document.getElementById("sp-node").innerHTML = "<div class=\"card\">The registry does not hold " + escapeHtml(S.node_id) + ".</div>"; return; }
      var pv = node.provenance || {}, comp = pv.comparator;
      var pills = "<span class=\"pill " + node.status + "\">" + node.status + "</span><span class=\"pill tag\">" + escapeHtml(node.kind) + "</span><span class=\"pill tag\">" + escapeHtml(node.campaign) + "</span>";
      if (node.readback) pills += "<span class=\"pill tag\">" + escapeHtml(node.readback.independence) + "</span>";
      if (node.proof) pills += "<span class=\"pill tag\">closure_clean " + node.proof.closure_clean + "</span><span class=\"pill " + (node.coverage.label === "module-covered" ? "tag" : "warnp") + "\">CI " + escapeHtml(node.coverage.label) + "</span>";
      var s = "<div class=\"card\"><h4>" + escapeHtml(node.id) + "</h4><div class=\"meta\">" + pills + "</div><div class=\"title\">" + escapeHtml(node.title) + "</div>";
      if (node.proof) s += "<div class=\"meta\">artifact <a href=\"" + escapeHtml(node.proof.artifact_url) + "\">" + escapeHtml(node.proof.artifact) + "</a>" + (node.proof.artifact_exists ? "" : " (missing in this checkout)") + (node.coverage.jobs.length ? "; compiled by " + escapeHtml(node.coverage.jobs.join(", ")) : "") + "</div>";
      var bits = [];
      bits.push(pv.grant ? "grant " + escapeHtml(pv.grant.date) + " (gate " + escapeHtml(pv.grant.gate_version) + ")" : "grant: none recorded");
      bits.push(comp ? "Comparator judge run " + escapeHtml(comp.run_id) + " on " + escapeHtml(comp.date) : "Comparator judge: not recorded");
      if (node.readback) bits.push("readback by " + escapeHtml(node.readback.auditor) + " on " + escapeHtml(node.readback.date) + " (of the statement; no read-back of the artifact is recorded)");
      s += "<div class=\"note\">" + bits.join(" &middot; ") + "</div>";
      if (node.readback) s += "<details><summary>the recorded read-back</summary><div class=\"rb\">" + escapeHtml(node.readback.text) + "</div></details>";
      s += "<div class=\"note\">" + (L.statement_matches_registry ? "The artifact's theorem <code>speiser_box_probe</code> matches the registered statement word for word (compared at build time)." : "WARNING: the artifact's theorem text differs from the registered statement.") + "</div>";
      document.getElementById("sp-node").innerHTML = s + "</div>";
    })();

    // ---- (b) where the box sits
    var planeMap = null;
    function drawPlane(hover) {
      var cv = setupCanvas("sp-plane"), ctx = cv.ctx;
      var x0 = -0.5, x1 = 3, y0 = 0, y1 = 30;
      var ax = axes(cv, x0, x1, y0, y1, { xlabel: "Re s", ylabel: "Im s", xticks: [-0.5, 0, 0.5, 1, 1.5, 2, 2.5, 3], mb: 32 });
      planeMap = { cv: cv, ax: ax, inv: inv(cv, ax, x0, x1, y0, y1) };
      var top = ax.Y(y1), bot = ax.Y(y0);
      ctx.fillStyle = cssVar("--sunk"); ctx.fillRect(ax.X(0), top, ax.X(1) - ax.X(0), bot - top);
      ctx.fillStyle = cssVar("--cool-soft"); ctx.fillRect(ax.X(0), top, ax.X(0.5) - ax.X(0), bot - top);
      ctx.strokeStyle = cssVar("--line"); ctx.lineWidth = 1;
      [0, 1].forEach(function (x) { ctx.beginPath(); ctx.moveTo(ax.X(x), top); ctx.lineTo(ax.X(x), bot); ctx.stroke(); });
      ctx.strokeStyle = cssVar("--faint"); ctx.setLineDash([4, 4]); ctx.beginPath(); ctx.moveTo(ax.X(0.5), top); ctx.lineTo(ax.X(0.5), bot); ctx.stroke(); ctx.setLineDash([]);
      // the box
      ctx.fillStyle = cssVar("--dbn-k-soft"); ctx.fillRect(ax.X(0.25), ax.Y(10), ax.X(0.375) - ax.X(0.25), ax.Y(6) - ax.Y(10));
      ctx.strokeStyle = cssVar("--dbn-k"); ctx.lineWidth = 2; ctx.strokeRect(ax.X(0.25), ax.Y(10), ax.X(0.375) - ax.X(0.25), ax.Y(6) - ax.Y(10));
      // zeros of zeta on the line (bundled ordinates), the pole, the zero of zeta'
      for (var z = 0; z < ZEROS.length && ZEROS[z] <= y1; z++) ring(ctx, ax.X(0.5), ax.Y(ZEROS[z]), 4, cssVar("--faint"));
      ctx.strokeStyle = cssVar("--accent"); ctx.lineWidth = 1.5;
      ctx.beginPath(); ctx.moveTo(ax.X(1) - 5, ax.Y(0) - 5); ctx.lineTo(ax.X(1) + 5, ax.Y(0) + 5); ctx.moveTo(ax.X(1) - 5, ax.Y(0) + 5); ctx.lineTo(ax.X(1) + 5, ax.Y(0) - 5); ctx.stroke();
      Fd.dzeta_zeros.forEach(function (q) { ring(ctx, ax.X(q.re), ax.Y(q.im), 5, cssVar("--dbn-m")); });
      // labels
      ctx.fillStyle = cssVar("--ink"); ctx.textAlign = "left"; ctx.textBaseline = "middle";
      ctx.fillText("the box [1/4, 3/8] x [6, 10]: zeta' has no zero here (kernel)", ax.X(0.375) + 8, ax.Y(8));
      ctx.fillText("zeta zeros 1/2 + i gamma (float model)", ax.X(0.5) + 8, ax.Y(ZEROS[0]));
      Fd.dzeta_zeros.forEach(function (q) { ctx.textAlign = "right"; ctx.fillText("zeta' zero " + fmt(q.re, 3) + " + " + fmt(q.im, 3) + " i (float model)", ax.X(q.re) - 9, ax.Y(q.im)); });
      ctx.textAlign = "left"; ctx.fillStyle = cssVar("--muted"); ctx.fillText("pole s = 1", ax.X(1) + 8, ax.Y(0) - 8);
      ctx.save(); ctx.translate(ax.X(0.25) - 6, ax.Y(19)); ctx.rotate(-Math.PI / 2); ctx.textAlign = "center"; ctx.textBaseline = "bottom";
      ctx.fillText("Speiser's region 0 < Re s < 1/2", 0, 0); ctx.restore();
      ctx.textAlign = "center"; ctx.textBaseline = "top"; ctx.fillText("Re s = 1/2", ax.X(0.5), top + 4);
      var rd = "The box has width 1/8 and height 4; its area is 1/2. Speiser's region is the open half-strip of infinite height. Everything drawn is a float model except the box, whose zeta'-freeness is the kernel theorem speiser_box_probe.";
      if (hover) {
        var g = gridAt(hover[0], hover[1]);
        rd = "s = " + fmt(hover[0], 4) + " + " + fmt(hover[1], 3) + " i" + (inBox(hover[0], hover[1]) ? " (inside the box: zeta'(s) != 0 is a kernel theorem)" : hover[0] > 0 && hover[0] < 0.5 ? " (in Speiser's region, outside the box: nothing is certified here)" : "") + ";" + gridText(g) + "\n" + rd;
      }
      document.getElementById("sp-plane-readout").textContent = rd;
    }
    var planeEl = document.getElementById("sp-plane");
    planeEl.addEventListener("pointermove", function (e) { if (!planeMap) return; var p = pos(planeEl, e); drawPlane([planeMap.inv.x(p[0]), planeMap.inv.y(p[1])]); });
    planeEl.addEventListener("pointerleave", function () { drawPlane(null); });

    // ---- (c) the heat map of log10 |zeta'| with the discs
    var heatMap = null, heatC = document.getElementById("sp-heat-c"), heatW = document.getElementById("sp-heat-w");
    var heatInner = document.getElementById("sp-heat-inner"), heatOuter = document.getElementById("sp-heat-outer");
    var HI_CAP = 2;   // the pole at s = 1 is clipped out of the colour range
    function drawHeat(hover) {
      var w = +heatW.value, tc = +heatC.value;
      var t0 = Math.max(G.im0, Math.min(tc - w / 2, G.im1 - w)), t1 = t0 + w;
      heatC.disabled = w >= 30;
      document.getElementById("sp-heat-c-val").textContent = "Im s in [" + fmt(t0, 2) + ", " + fmt(t1, 2) + "]";
      var el = document.getElementById("sp-heat"), ml = 56, mr = 14, mt = 12, mb = 32;
      var W = el.clientWidth || 1000, scale = (W - ml - mr) / w;
      var aspect = Math.min(1.1, ((G.re1 - G.re0) * scale + mt + mb) / W);
      var cv = sized("sp-heat", aspect), ctx = cv.ctx;
      var ax = axes(cv, t0, t1, G.re0, G.re1, { xlabel: "Im s (height)", ylabel: "Re s", yticks: [0, 0.5, 1, 1.5, 2, 2.5], ml: ml, mr: mr, mt: mt, mb: mb });
      heatMap = { cv: cv, ax: ax, inv: inv(cv, ax, t0, t1, G.re0, G.re1) };
      var col = ramp();
      ctx.save(); ctx.beginPath(); ctx.rect(ax.X(t0), ax.Y(G.re1), ax.X(t1) - ax.X(t0), ax.Y(G.re0) - ax.Y(G.re1)); ctx.clip();
      var j0 = Math.max(0, Math.floor((t0 - G.im0) / dIm) - 1), j1 = Math.min(G.nrows - 1, Math.ceil((t1 - G.im0) / dIm) + 1);
      // the colour range follows the window (the landscape is flat near the box and steep near the pole)
      var LO = Infinity, HI = -Infinity, j, i, v;
      for (j = j0; j <= j1; j++) for (i = 0; i < G.ncols; i++) { v = G.log10_abs_dzeta[j * G.ncols + i] / G.scale; if (v < LO) LO = v; if (v > HI && v < HI_CAP) HI = v; }
      if (!(HI > LO)) { LO = -2; HI = 1; }
      for (j = j0; j <= j1; j++) {
        var im = G.im0 + j * dIm, px = ax.X(im - dIm / 2), pw = ax.X(im + dIm / 2) - px + 0.5;
        for (i = 0; i < G.ncols; i++) {
          var re = G.re0 + i * dRe; v = G.log10_abs_dzeta[j * G.ncols + i] / G.scale;
          ctx.fillStyle = col((v - LO) / (HI - LO));
          var py = ax.Y(re + dRe / 2); ctx.fillRect(px, py, pw, ax.Y(re - dRe / 2) - py + 0.5);
        }
      }
      // overlays: strip edges, critical line, zeros, the box, the discs
      ctx.strokeStyle = cssVar("--faint"); ctx.lineWidth = 1; ctx.setLineDash([4, 4]);
      ctx.beginPath(); ctx.moveTo(ax.X(t0), ax.Y(0.5)); ctx.lineTo(ax.X(t1), ax.Y(0.5)); ctx.stroke(); ctx.setLineDash([]);
      [0, 1].forEach(function (x) { ctx.beginPath(); ctx.moveTo(ax.X(t0), ax.Y(x)); ctx.lineTo(ax.X(t1), ax.Y(x)); ctx.stroke(); });
      for (var z = 0; z < ZEROS.length && ZEROS[z] <= t1; z++) if (ZEROS[z] >= t0) ring(ctx, ax.X(ZEROS[z]), ax.Y(0.5), 3.5, cssVar("--faint"));
      Fd.dzeta_zeros.forEach(function (q) { if (q.im >= t0 && q.im <= t1) ring(ctx, ax.X(q.im), ax.Y(q.re), 4, cssVar("--dbn-m")); });
      ctx.strokeStyle = cssVar("--dbn-k"); ctx.lineWidth = 2; ctx.strokeRect(ax.X(6), ax.Y(0.375), ax.X(10) - ax.X(6), ax.Y(0.25) - ax.Y(0.375));
      E.discs.forEach(function (d) {
        var cx = ax.X(d.tc_float), cy = ax.Y(sig);
        if (heatOuter.checked) circle(ctx, cx, cy, ax.X(d.tc_float + R) - cx, cssVar("--dbn-m"), 1.2, [3, 3]);
        if (heatInner.checked) circle(ctx, cx, cy, ax.X(d.tc_float + r) - cx, cssVar("--dbn-k"), 1.2);
      });
      ctx.restore();
      ctx.fillStyle = cssVar("--ink"); ctx.textAlign = "left"; ctx.textBaseline = "bottom";
      if (t0 <= 10 && t1 >= 6) ctx.fillText("the box", ax.X(Math.max(6, t0)) + 4, ax.Y(0.375 + (w <= 6 ? 0.3 : 0.08)) - 2);
      var rd = "Colour range in this window: log10 |zeta'| from " + fmt(LO, 2) + " (dark) to " + fmt(HI, 2) + " (light), the pole clipped; grid step 1/32 in Re s and 1/8 in Im s; " + Fd.trust + ".";
      if (hover) {
        var g = gridAt(hover[1], hover[0]), din = discOf(hover[1], hover[0], r), dout = discOf(hover[1], hover[0], R);
        rd = "s = " + fmt(hover[1], 4) + " + " + fmt(hover[0], 3) + " i;" + gridText(g) +
          (din >= 0 ? "\ninside inner disc " + din + " (centre 5/16 + " + E.discs[din].tc + " i): |M'| > F certified there" : dout >= 0 ? "\ninside outer disc " + dout + " only: |zeta - M| <= F rho certified there, |M'| not" : "") +
          (inBox(hover[1], hover[0]) ? "; in the box" : "") + "\n" + rd;
      }
      document.getElementById("sp-heat-readout").textContent = rd;
    }
    var heatEl = document.getElementById("sp-heat");
    heatEl.addEventListener("pointermove", function (e) { if (!heatMap) return; var p = pos(heatEl, e); drawHeat([heatMap.inv.x(p[0]), heatMap.inv.y(p[1])]); });
    heatEl.addEventListener("pointerleave", function () { drawHeat(null); });
    [heatC, heatW, heatInner, heatOuter].forEach(function (el) { el.addEventListener("input", function () { drawHeat(null); }); el.addEventListener("change", function () { drawHeat(null); }); });

    // ---- (d) and (f): the two certificate plots for one disc, with the thresholds as parameters
    // mpId: |M'(h)| on the inner disc, red where |M'| <= Ffail.  errId: log10 |zeta - M| on the outer disc
    // (mpmath polar samples), red where the sample exceeds threshold.
    function drawMp(mpId, coef, Ffail) {
      var cv = sized(mpId, 1), ctx = cv.ctx, m = 8, side = Math.min(cv.W, cv.H) - 2 * m, cx = cv.W / 2, cy = cv.H / 2 - 12, sc = side / (2 * r * 1.22);
      var n = 90, cell = 2 * r / n, vmax = 0, vmin = Infinity, vals = [], red = 0, tot = 0;
      for (var a = 0; a < n; a++) for (var b = 0; b < n; b++) {
        var hr = -r + (a + 0.5) * cell, hi = -r + (b + 0.5) * cell;
        if (hr * hr + hi * hi > r * r) { vals.push(-1); continue; }
        var v = pabs(coef, hr, hi); vals.push(v); tot++;
        if (v > vmax) vmax = v; if (v < vmin) vmin = v; if (v <= Ffail) red++;
      }
      var col = ramp(), span = vmax - vmin || 1;
      ctx.save(); ctx.beginPath(); ctx.arc(cx, cy, r * sc, 0, 2 * Math.PI); ctx.clip();
      for (a = 0; a < n; a++) for (b = 0; b < n; b++) {
        var v2 = vals[a * n + b]; if (v2 < 0) continue;
        ctx.fillStyle = v2 <= Ffail ? cssVar("--refuted") : col((v2 - vmin) / span);
        ctx.fillRect(cx + (-r + a * cell) * sc, cy - (-r + (b + 1) * cell) * sc, cell * sc + 0.6, cell * sc + 0.6);
      }
      ctx.restore();
      circle(ctx, cx, cy, r * sc, cssVar("--dbn-k"), 2);
      ring(ctx, cx, cy, 3, cssVar("--ink"));
      ctx.fillStyle = cssVar("--ink"); ctx.textAlign = "left"; ctx.textBaseline = "middle"; halo(ctx, "h = 0 (the centre c)", cx + 8, cy);
      ctx.fillStyle = cssVar("--muted"); ctx.textAlign = "center"; ctx.textBaseline = "bottom"; ctx.fillText("|h| = r", cx, cy - r * sc - 4);
      ctx.textBaseline = "top"; ctx.fillText("colour: |M'| from " + fmt(vmin, 4) + " (dark) to " + fmt(vmax, 4) + " (light)", cx, cy + r * sc + 6);
      ctx.fillText("sampled grid, float; F = " + Ffail, cx, cy + r * sc + 20);
      return { vmax: vmax, vmin: vmin, red: red, tot: tot };
    }
    function drawErr(errId, fd, threshold) {
      var cv = sized(errId, 1), ctx = cv.ctx, m = 8, side = Math.min(cv.W, cv.H) - 2 * m, cx = cv.W / 2, cy = cv.H / 2 - 12, sc = side / (2 * R * 1.22);
      var col = ramp(), red = 0, tot = 0, lt = Math.log10(threshold), eps = 0.006;
      var centre = fd.centre_log10_err / G.scale, ELO = centre, EHI = centre;
      fd.log10_err.forEach(function (q) { q /= G.scale; if (q < ELO) ELO = q; if (q > EHI) EHI = q; });
      var espan = EHI - ELO || 1;
      for (var k = fd.nrad; k >= 1; k--) for (var mm = 0; mm < fd.nang; mm++) {
        var v = fd.log10_err[(k - 1) * fd.nang + mm] / G.scale, a0 = (mm - 0.5) * 2 * Math.PI / fd.nang - eps, a1 = (mm + 0.5) * 2 * Math.PI / fd.nang + eps;
        var r0 = (k - 1) * R / fd.nrad * sc, r1 = k * R / fd.nrad * sc; tot++;
        var bad = v > lt; if (bad) red++;
        ctx.fillStyle = bad ? cssVar("--refuted") : col((v - ELO) / espan);
        ctx.beginPath(); ctx.arc(cx, cy, r1 + 0.6, -a1, -a0, false); ctx.arc(cx, cy, Math.max(r0 - 0.6, 0), -a0, -a1, true); ctx.closePath(); ctx.fill();
      }
      ctx.fillStyle = centre > lt ? cssVar("--refuted") : col((centre - ELO) / espan);
      ctx.beginPath(); ctx.arc(cx, cy, R / fd.nrad * sc * 0.5, 0, 2 * Math.PI); ctx.fill();
      circle(ctx, cx, cy, R * sc, cssVar("--dbn-m"), 2); circle(ctx, cx, cy, r * sc, cssVar("--dbn-k"), 1.5, [4, 3]);
      ctx.fillStyle = cssVar("--muted"); ctx.textAlign = "center"; ctx.textBaseline = "bottom";
      ctx.fillText("|z - c| = r + rho", cx, cy - R * sc - 4); halo(ctx, "|z - c| = r", cx, cy - r * sc - 4);
      ctx.textBaseline = "top"; ctx.fillText("colour: log10 |zeta - M| from " + fmt(ELO, 1) + " (dark) to " + fmt(EHI, 1) + " (light)", cx, cy + R * sc + 6);
      ctx.fillText("boundary max " + sci(fd.boundary_max_err) + " (mpmath, float); threshold " + sci(threshold), cx, cy + R * sc + 20);
      return { red: red, tot: tot };
    }
    function kv(rows) { return rows.map(function (q) { return "<tr><td>" + escapeHtml(q[0]) + "</td><td>" + q[1] + "</td></tr>"; }).join(""); }
    function drawDisc() {
      var i = +discSl.value, d = E.discs[i], fd = Fd.discs[i];
      document.getElementById("sp-disc-val").textContent = "disc " + i + ", centre c = 5/16 + " + d.tc + " i";
      var mp = drawMp("sp-mp", MP[i], F), er = drawErr("sp-err", fd, FR);
      var lower = d.abs_Mp0 - d.r_pnub;
      document.getElementById("sp-disc-table").innerHTML = kv([
        ["centre c", "5/16 + " + escapeHtml(d.tc) + " i = " + fmt(sig, 4) + " + " + fmt(d.tc_float, 2) + " i"],
        ["|M'(0)|  (exact coefficients)", fmt(d.abs_Mp0, 6)],
        ["r ub  (the rest of M' on |h| <= r, bounded coefficient by coefficient)", fmt(d.r_pnub, 6)],
        ["kernel test  (r ub + F)^2 < |M'(0)|^2", "(" + fmt(d.deriv_bound, 6) + ")^2 < (" + fmt(d.abs_Mp0, 6) + ")^2: <strong>true</strong> (check" + i + ", decide +kernel)"],
        ["certified lower bound of |M'| on the disc", "|M'(0)| - r ub = " + fmt(lower, 6) + " > F = " + F],
        ["design margin |M'(0)| - r ub - F  (generator and Lean header)", fmt(d.margin, 4)],
        ["float min |M'(h)| on the disc (browser grid / mpmath grid)", fmt(mp.vmin, 6) + " / " + fmt(fd.inner_min_abs_Mp, 6) + " (float model; above the certified bound, as expected)"],
        ["float min |zeta'(s)| on the disc (mpmath)", fmt(fd.inner_min_abs_dzeta, 6) + " (float model)"],
        ["budget G  (exact rational, the kernel's number)", sci(d.budget_float) + " (" + d.budget_exact.length + "-character rational in explorer_data.json)"],
        ["kernel test  G <= F rho", sci(d.budget_float) + " <= " + sci(FR) + ": <strong>true</strong>"],
        ["float max |zeta - M| on the sampled outer boundary (mpmath)", sci(fd.boundary_max_err) + " (float model; " + fmt(d.budget_float / fd.boundary_max_err, 0) + " times below the certified budget)"],
        ["zeta'(c)  (mpmath)", fmt(fd.dzeta_at_centre[0], 6) + (fd.dzeta_at_centre[1] < 0 ? " - " : " + ") + fmt(Math.abs(fd.dzeta_at_centre[1]), 6) + " i (float model; M'(0) is the kernel's rational approximation of it)"]
      ]);
      document.getElementById("sp-disc-readout").textContent = "Left: " + mp.red + " of " + mp.tot + " sampled cells have |M'| <= F (red). Right: " + er.red + " of " + er.tot + " polar samples exceed F rho (red). " +
        "The certified facts are the two kernel tests in the table; the coloured plots are float pictures of the same quantities. Degree of M: " + P.degree_M + "; N = " + P.N + " Euler-Maclaurin terms; p = " + P.p + ", K = " + P.K + ", J = " + P.J + ".";
    }
    discSl.addEventListener("input", function () { drawDisc(); drawCauchy(); drawNeg(); });

    // ---- (e) the Cauchy estimate, with a draggable point
    var hPt = [0.12, 0.09], dragging = false, cauchyMap = null;
    function drawCauchy() {
      var i = +discSl.value, d = E.discs[i];
      var cv = setupCanvas("sp-cauchy"), ctx = cv.ctx;
      var pad = 0.06, x0 = sig - R - pad, x1 = sig + R + pad, y0 = d.tc_float - R - pad, y1 = d.tc_float + R + pad;
      // equal aspect: the plot square sits on the left, text on the right
      var ml = 56, mb = 32, mt = 12, side = cv.H - mt - mb, mr = cv.W - ml - side;
      if (mr < 14) { mr = 14; side = cv.W - ml - mr; }
      var ax = axes(cv, x0, x1, y0, y1, { xlabel: "Re s", ylabel: "Im s", ml: ml, mr: mr, mt: mt, mb: mb, xticks: [sig - 0.3, sig - 0.15, sig, sig + 0.15, sig + 0.3].map(function (v) { return +v.toFixed(4); }), yticks: [d.tc_float - 0.3, d.tc_float - 0.15, d.tc_float, d.tc_float + 0.15, d.tc_float + 0.3],
        xfmt: function (v) { return fmt(v, 3); }, yfmt: function (v) { return fmt(v, 2); } });
      cauchyMap = { cv: cv, ax: ax, inv: inv(cv, ax, x0, x1, y0, y1) };
      var cx = ax.X(sig), cy = ax.Y(d.tc_float), sc = (ax.X(sig + 1) - cx);
      ctx.fillStyle = cssVar("--sunk"); ctx.beginPath(); ctx.arc(cx, cy, R * sc, 0, 2 * Math.PI); ctx.fill();
      circle(ctx, cx, cy, R * sc, cssVar("--dbn-m"), 2);
      ctx.fillStyle = cssVar("--dbn-k-soft"); ctx.beginPath(); ctx.arc(cx, cy, r * sc, 0, 2 * Math.PI); ctx.fill();
      circle(ctx, cx, cy, r * sc, cssVar("--dbn-k"), 2);
      // the point and its Cauchy circle
      var sx = cx + hPt[0] * sc, sy = cy - hPt[1] * sc;
      ctx.fillStyle = cssVar("--dbn-k-soft"); ctx.beginPath(); ctx.arc(sx, sy, rho * sc, 0, 2 * Math.PI); ctx.fill();
      circle(ctx, sx, sy, rho * sc, cssVar("--ink"), 2);
      ctx.strokeStyle = cssVar("--faint"); ctx.lineWidth = 1; ctx.setLineDash([3, 3]); ctx.beginPath(); ctx.moveTo(cx, cy); ctx.lineTo(sx, sy); ctx.stroke(); ctx.setLineDash([]);
      ring(ctx, cx, cy, 3, cssVar("--muted")); ring(ctx, sx, sy, 5, cssVar("--ink"));
      ctx.fillStyle = cssVar("--ink"); ctx.textAlign = "left"; ctx.textBaseline = "bottom";
      ctx.fillText("s = c + h (drag me)", sx + 8, sy - 6);
      ctx.fillStyle = cssVar("--muted"); ctx.fillText("c", cx + 6, cy - 4);
      ctx.textAlign = "center"; ctx.textBaseline = "top"; ctx.fillText("outer disc, radius r + rho = " + fmt(R, 2), cx, cy + R * sc + 4);
      ctx.textBaseline = "bottom"; ctx.fillText("inner disc, radius r = " + r, cx, cy - r * sc - 4);
      // the chain, on the right
      var habs = Math.sqrt(hPt[0] * hPt[0] + hPt[1] * hPt[1]), mph = pabs(MP[i], hPt[0], hPt[1]), lower = d.abs_Mp0 - d.r_pnub;
      var lines = [
        ["|h| = " + fmt(habs, 4) + " <= r = " + r, "--ink"],
        ["|h| + rho = " + fmt(habs + rho, 4) + " <= r + rho = " + fmt(R, 2) + ": the circle stays in the outer disc", "--ink"],
        ["on it  |zeta - M| <= G = " + sci(d.budget_float) + " <= F rho = " + sci(FR) + "   (kernel)", "--dbn-k"],
        ["Cauchy:  |zeta'(s) - M'(h)| <= G / rho <= F = " + F, "--dbn-k"],
        ["|M'(h)| = " + fmt(mph, 4) + " (float)  >=  |M'(0)| - r ub = " + fmt(lower, 4) + " (kernel)  > F", "--dbn-k"],
        ["so  |zeta'(s)| >= |M'(h)| - F > " + fmt(lower - F, 4) + " > 0", "--ink"]
      ];
      var tx = ax.X(x1) + 18, ty = mt + 24;
      if (cv.W - tx > 220) {
        ctx.textAlign = "left"; ctx.textBaseline = "top";
        lines.forEach(function (l, k) { ctx.fillStyle = cssVar(l[1]); ctx.fillText(l[0], tx, ty + k * 22); });
      }
      document.getElementById("sp-cauchy-readout").textContent = lines.map(function (l) { return l[0]; }).join("\n") +
        "\nDisc " + i + ". The circle picture is exact geometry; G, F rho, F and the lower bound are the kernel's rationals (floats shown); |M'(h)| is a double evaluation of the exact coefficients (float model). zeta is holomorphic on the whole outer disc because its only pole, s = 1, is at height 0.";
    }
    var cauchyEl = document.getElementById("sp-cauchy");
    function setH(e) {
      if (!cauchyMap) return;
      var p = pos(cauchyEl, e), i = +discSl.value, d = E.discs[i];
      var hx = cauchyMap.inv.x(p[0]) - sig, hy = cauchyMap.inv.y(p[1]) - d.tc_float, n = Math.sqrt(hx * hx + hy * hy);
      if (n > r) { hx *= r / n; hy *= r / n; }
      hPt = [hx, hy]; drawCauchy();
    }
    cauchyEl.addEventListener("pointerdown", function (e) { dragging = true; cauchyEl.setPointerCapture && cauchyEl.setPointerCapture(e.pointerId); setH(e); });
    cauchyEl.addEventListener("pointermove", function (e) { if (dragging) setH(e); });
    ["pointerup", "pointercancel", "pointerleave"].forEach(function (ev) { cauchyEl.addEventListener(ev, function () { dragging = false; }); });

    // ---- (f) the negative controls
    var negMode = document.getElementById("sp-neg-mode");
    function drawNeg() {
      var i = +discSl.value, L = S.lean, rd;
      if (negMode.value === "forged") {
        var fg = E.forged_disc0;
        document.getElementById("sp-neg-cap-l").textContent = "|M'(h)| with disc 0's k = 1 accumulator forged so that M'(0) = 0 (float evaluation of the forged rationals)";
        document.getElementById("sp-neg-cap-r").textContent = "|zeta(z) - M(z - c)| on disc 0's outer disc against F rho = 1/2000: the budget still passes";
        var mp = drawMp("sp-neg-mp", MP_FORGED, F), er = drawErr("sp-neg-err", Fd.discs[0], FR);
        rd = "Forged accumulator, disc 0: |M'(0)| = " + sci(fg.abs_Mp0) + " and r ub = " + fmt(fg.r_pnub, 4) + ", so (r ub + F)^2 < |M'(0)|^2 is false and the derivative test fails; " + mp.red + " of " + mp.tot + " sampled cells have |M'| <= F (red, around the centre). " +
          "The budget G = " + sci(fg.budget_float) + " <= F rho still holds (" + er.red + " red samples on the right). Kernel verdict: check0_corrupt = false (decide +kernel). " + fg.what + ".";
      } else {
        var d = E.discs[i], ft = P.F_tiny_rho_float;
        document.getElementById("sp-neg-cap-l").textContent = "|M'(h)| on disc " + i + " against F = 10^-9: the derivative test still passes, trivially";
        document.getElementById("sp-neg-cap-r").textContent = "|zeta(z) - M(z - c)| on disc " + i + " against F rho = 5 x 10^-11: every sample is above it";
        var mp2 = drawMp("sp-neg-mp", MP[i], 1e-9), er2 = drawErr("sp-neg-err", Fd.discs[i], ft);
        rd = "F = 10^-9, disc " + i + ": the budget G = " + sci(d.budget_float) + " is the kernel's own error bound and it exceeds F rho = " + sci(ft) + ", so checkD is false; " + er2.red + " of " + er2.tot + " polar samples are red. " +
          "The derivative test alone would pass (" + mp2.red + " red cells on the left), which is the point: the budget half of the check is what refuses an impossible precision claim. Kernel verdict: check" + i + "_neg = false (decide +kernel); the source quotes check0_neg below, and check1_neg to check7_neg are the same theorem for the other discs.";
      }
      document.getElementById("sp-neg-readout").textContent = rd + " Both refusals are theorems of the artifact and anchors of its axiom guard.";
      document.getElementById("sp-neg-lean").textContent = L.check0_neg + "\n\n" + L.check0_corrupt;
    }
    negMode.addEventListener("change", drawNeg);

    // ---- (g) the guard and the CI step, verbatim
    document.getElementById("sp-guard").textContent = S.lean.guard;
    document.getElementById("sp-ci-workflow").textContent = S.ci.workflow;
    document.getElementById("sp-ci-step").textContent = S.ci.step;

    drawers["zeta-prime"] = function () { drawPlane(null); drawHeat(null); drawDisc(); drawCauchy(); drawNeg(); };
  })();

  // ================================================================== REGISTRY
  (function registryTab() {
    var byId = {}; REG.nodes.forEach(function (n) { byId[n.id] = n; });
    var STATUSES = ["proved", "open", "draft", "refuted", "deprecated"];
    // counts
    var cc = document.getElementById("reg-counts"), h = "";
    REG.campaigns.forEach(function (c) {
      h += "<div class=\"count-card\"><h3>" + c.dir + "</h3><div class=\"note\">" + escapeHtml(c.title) + "</div><div class=\"bar\">";
      STATUSES.forEach(function (s) { h += "<span style=\"width:" + (100 * c.counts[s] / c.n_nodes) + "%;background:var(--" + s + ")\"></span>"; });
      h += "</div><div class=\"nums\">" + STATUSES.map(function (s) { return s + " " + c.counts[s]; }).join(" | ") + " | goal " + c.goal_node + " (" + byId[c.dir + ":" + c.goal_node].status + ")</div>" +
        "<div class=\"nums\">" + escapeHtml(c.toolchain) + "; mathlib " + escapeHtml(c.mathlib_rev) + "</div></div>";
    });
    h += "<div class=\"count-card\"><h3>all campaigns</h3><div class=\"nums\">" + STATUSES.map(function (s) { return s + " " + REG.totals[s]; }).join(" | ") + "</div><div class=\"nums\">conjecture1_proved = false in every manifest</div></div>";
    cc.innerHTML = h;

    // graph
    var gsel = document.getElementById("graph-campaign"), gpo = document.getElementById("graph-proved-only"), gtip = document.getElementById("graph-tip");
    REG.campaigns.forEach(function (c) { var o = document.createElement("option"); o.value = c.dir; o.textContent = c.dir; gsel.appendChild(o); });
    gsel.value = "mirrormere";
    function drawGraph() {
      var camp = gsel.value, provedOnly = gpo.checked;
      var nodes = REG.nodes.filter(function (n) { return n.campaign === camp && (!provedOnly || n.status === "proved"); });
      var ids = {}; nodes.forEach(function (n) { ids[n.id] = true; });
      // external deps drawn as small squares
      var ext = {};
      nodes.forEach(function (n) { n.depends_on.forEach(function (d) { if (!ids[d] && byId[d] && (!provedOnly || byId[d].status === "proved")) ext[d] = byId[d]; }); });
      var all = nodes.concat(Object.keys(ext).map(function (k) { return ext[k]; }));
      var idx = {}; all.forEach(function (n, i) { idx[n.id] = i; });
      var depth = {};
      function dep(id) {
        if (depth[id] !== undefined) return depth[id];
        depth[id] = 0;
        var n = byId[id], d = 0;
        n.depends_on.forEach(function (x) { if (idx[x] !== undefined) d = Math.max(d, dep(x) + 1); });
        depth[id] = d; return d;
      }
      all.forEach(function (n) { dep(n.id); });
      var cols = {}; all.forEach(function (n) { (cols[depth[n.id]] = cols[depth[n.id]] || []).push(n); });
      var ncol = Object.keys(cols).length, maxrows = Math.max.apply(null, Object.keys(cols).map(function (k) { return cols[k].length; }));
      var W = 960, colW = Math.max(150, (W - 60) / Math.max(ncol, 1)), rowH = 26, H = Math.max(120, maxrows * rowH + 40);
      var pos = {};
      Object.keys(cols).sort(function (a, b) { return a - b; }).forEach(function (k) {
        cols[k].sort(function (a, b) { return a.slug < b.slug ? -1 : 1; });
        cols[k].forEach(function (n, i) { pos[n.id] = [30 + k * colW + 8, 20 + (i + 0.5) * (H - 40) / cols[k].length]; });
      });
      var svg = "<svg viewBox=\"0 0 " + (30 + ncol * colW + 30) + " " + H + "\" xmlns=\"http://www.w3.org/2000/svg\">";
      all.forEach(function (n) { n.depends_on.forEach(function (d) { if (pos[d]) svg += "<line x1=\"" + pos[d][0] + "\" y1=\"" + pos[d][1] + "\" x2=\"" + pos[n.id][0] + "\" y2=\"" + pos[n.id][1] + "\"/>"; }); });
      all.forEach(function (n) {
        var p = pos[n.id], isExt = !ids[n.id];
        var label = (isExt ? n.campaign + ":" : "") + n.slug.replace(/^(MM|RH|AND|BG)_/, "");
        svg += (isExt ? "<rect x=\"" + (p[0] - 5) + "\" y=\"" + (p[1] - 5) + "\" width=\"10\" height=\"10\"" : "<circle cx=\"" + p[0] + "\" cy=\"" + p[1] + "\" r=\"6\"") +
          " fill=\"var(--" + n.status + ")\" class=\"" + (n.is_goal ? "goal" : "") + "\" data-id=\"" + n.id + "\"/>" +
          "<text x=\"" + (p[0] + 9) + "\" y=\"" + (p[1] + 3.5) + "\" data-id=\"" + n.id + "\">" + escapeHtml(label) + "</text>";
      });
      svg += "</svg>";
      var box = document.getElementById("graph-svg"); box.innerHTML = svg;
      Array.prototype.forEach.call(box.querySelectorAll("[data-id]"), function (el) {
        el.addEventListener("mouseenter", function () { var n = byId[el.dataset.id]; gtip.innerHTML = "<strong>" + n.id + "</strong> <span class=\"pill " + n.status + "\">" + n.status + "</span> " + n.kind + (n.is_goal ? " (goal)" : "") + ": " + escapeHtml(n.title.slice(0, 260)) + (n.title.length > 260 ? "..." : ""); });
        el.addEventListener("click", function () { showCard(el.dataset.id); });
      });
      var hidden = REG.nodes.filter(function (n) { return n.campaign === camp; }).length - nodes.length;
      gtip.textContent = nodes.length + " nodes shown" + (provedOnly ? ", " + hidden + " non-proved hidden (the goal node is a draft and is among them)" : "") + ". Edges point from a dependency to the node that uses it; squares are nodes of other campaigns. Hover a node.";
    }
    gsel.addEventListener("change", drawGraph); gpo.addEventListener("change", drawGraph);

    // cards
    var csel = document.getElementById("cards-campaign"), cpo = document.getElementById("cards-proved-only"), csearch = document.getElementById("cards-search"), ccount = document.getElementById("cards-count"), cards = document.getElementById("cards");
    REG.campaigns.forEach(function (c) { var o = document.createElement("option"); o.value = c.dir; o.textContent = c.dir; csel.appendChild(o); });
    csel.value = "mirrormere";
    function cardHtml(n) {
      var pills = "<span class=\"pill " + n.status + "\">" + n.status + "</span><span class=\"pill tag\">" + n.kind + "</span><span class=\"pill tag\">" + n.campaign + "</span>";
      if (n.is_goal) pills += "<span class=\"pill tag\">goal node</span>";
      if (n.conditional) pills += "<span class=\"pill warnp\">conditional: see hypotheses</span>";
      if (n.arb) pills += "<span class=\"pill warnp\">Arb-conditional</span>";
      if (n.proof) {
        pills += "<span class=\"pill tag\">closure_clean " + n.proof.closure_clean + "</span>";
        pills += "<span class=\"pill " + (n.coverage.label === "module-covered" ? "tag" : "warnp") + "\">CI " + n.coverage.label + "</span>";
      }
      var s = "<div class=\"card\" id=\"card-" + n.id.replace(":", "-") + "\"><h4>" + n.id + "</h4><div class=\"meta\">" + pills + "</div><div class=\"title\">" + escapeHtml(n.title) + "</div>";
      if (n.proof) s += "<div class=\"meta\">artifact <a href=\"" + n.proof.artifact_url + "\">" + escapeHtml(n.proof.artifact) + "</a>" + (n.proof.artifact_exists ? "" : " (missing in this checkout)") + " via " + n.proof.via + (n.coverage.jobs.length ? "; compiled by " + n.coverage.jobs.join(", ") : "") + "</div>";
      if (n.proof && n.proof.fidelity_note) s += "<div class=\"note\">fidelity note: " + escapeHtml(n.proof.fidelity_note) + "</div>";
      if (n.refutation_statement) s += "<div class=\"note\">refutation: " + escapeHtml(n.refutation_statement) + "</div>";
      if (n.deprecated_reason) s += "<div class=\"note\">deprecated: " + escapeHtml(n.deprecated_reason) + "</div>";
      if (n.depends_on.length) s += "<div class=\"note\">depends on " + n.depends_on.map(function (d) { return "<span class=\"mono\">" + d + "</span>" + (byId[d] ? " (" + byId[d].status + ")" : ""); }).join(", ") + "</div>";
      if (n.statement) s += "<details><summary>statement and hypotheses (verbatim registry statement module)</summary><pre>" + escapeHtml(n.statement) + "</pre></details>";
      else s += "<div class=\"note\">no statement module (goal or draft authored without one)</div>";
      if (n.readback) s += "<details><summary>readback: " + escapeHtml(n.readback.auditor) + " (" + n.readback.date + "), <strong>" + n.readback.independence + "</strong></summary><div class=\"rb\">" + escapeHtml(n.readback.text) + "</div></details>";
      if (n.provenance) {
        var pv = n.provenance, bits = [];
        if (pv.grant) bits.push("grant " + escapeHtml(pv.grant.date) + " (gate " + escapeHtml(pv.grant.gate_version) + ", artifact sha256 " + escapeHtml(pv.grant.artifact_sha256) + "...)");
        else bits.push("grant: legacy (no digest-pinned grant block)");
        if (pv.comparator) bits.push("Comparator judge run " + (pv.comparator.run_url ? "<a href=\"" + escapeHtml(pv.comparator.run_url) + "\">" + escapeHtml(pv.comparator.run_id) + "</a>" : escapeHtml(pv.comparator.run_id)) + " on " + escapeHtml(pv.comparator.date));
        else bits.push("Comparator judge: not recorded");
        if (pv.requires_ci_job) bits.push("requires CI job " + escapeHtml(pv.requires_ci_job) + (pv.ci_record ? " (run " + escapeHtml(pv.ci_record.run_id) + ": " + escapeHtml(pv.ci_record.conclusion) + ")" : " (no record)"));
        s += "<div class=\"prov\">" + bits.join(" &middot; ") + "</div>";
      }
      else s += "<div class=\"note\">no readback recorded</div>";
      return s + "</div>";
    }
    function drawCards() {
      var camp = csel.value, po = cpo.checked, q = csearch.value.trim().toLowerCase();
      var list = REG.nodes.filter(function (n) {
        if (camp !== "all" && n.campaign !== camp) return false;
        if (po && n.status !== "proved") return false;
        if (q && (n.id + " " + n.title + " " + (n.proof ? n.proof.artifact : "")).toLowerCase().indexOf(q) < 0) return false;
        return true;
      });
      list.sort(function (a, b) { var sa = STATUSES.indexOf(a.status), sb = STATUSES.indexOf(b.status); return sa !== sb ? sa - sb : (a.id < b.id ? -1 : 1); });
      cards.innerHTML = list.map(cardHtml).join("");
      ccount.textContent = list.length + " of " + REG.nodes.length + " nodes";
    }
    function showCard(id) {
      var n = byId[id];
      csel.value = n.campaign; if (n.status !== "proved") cpo.checked = false; csearch.value = "";
      drawCards();
      var el = document.getElementById("card-" + id.replace(":", "-"));
      if (el) el.scrollIntoView({ behavior: "smooth", block: "center" });
    }
    csel.addEventListener("change", drawCards); cpo.addEventListener("change", drawCards); csearch.addEventListener("input", drawCards);
    drawers.reg = function () { drawGraph(); drawCards(); };
  })();

  function escapeHtml(s) {
    return String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
  }

  window.addEventListener("resize", function () { clearTimeout(window.__tre); window.__tre = setTimeout(redrawAll, 150); });
  selectTab(location.hash.replace("#", "") || "qc", false);
})();
