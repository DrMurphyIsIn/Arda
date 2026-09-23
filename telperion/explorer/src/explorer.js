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
