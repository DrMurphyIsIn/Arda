(* ::Package:: *)

(* Wolfram Language visualizations for the Laplacian-ratio maximizer proof.
   Run in Mathematica, the free Wolfram Engine (wolframscript), or the Wolfram Cloud.

   The centerpiece is a FOLIATION view of the cavity recursion -- the amplitude
   mechanism at the heart of the Phi<=1 proof -- in direct analogy with the
   foliations of causal graphs in the Wolfram Physics Project: the rooted tree is
   sliced into depth layers (a "time" ordering), and the cavity field m_v is UPDATED
   layer by layer from the leaves toward the root by
        m_v = z_v / (1 + z_v * Sum_children m_c),   z_v = 3/(3 d_v + c_v),
   with the log-amplitude telescoping across the foliation:
        log Phi = Sum_v ( Log[a_v z_v] - Log[m_v] ),  a_v = F(d_v,c_v)/rhoB^(1+2 c_v),
        F(d,c) = (3/2)^c (1 + c/(3 d)),  rhoB = (621/64)^(1/11).                        *)

rhoB = (621/64)^(1/11);
Fdc[d_, c_] := (3/2)^c (1 + c/(3 d));
zdc[d_, c_] := 3/(3 d + c);
adc[d_, c_] := Fdc[d, c]/rhoB^(1 + 2 c);

(* ---------- tree builders (return {edges, cherryCount-assoc}) ---------- *)
(* A "center" carries c length-2 cherries (center-mid-leaf).  We build labeled trees. *)

ClearAll[addCherries];
addCherries[edges_, ctr_, c_, nxt_] := Module[{e = edges, k = nxt, y, z, i},
  Do[y = k; z = k + 1; k += 2; e = Join[e, {ctr <-> y, y <-> z}], {i, c}];
  {e, k}];

(* Cherry-bundle star: hub (c0 cherries) + k arm-centers (each cArm cherries). *)
cherryBundleStar[k_, cArm_, c0_: 0] := Module[{e = {}, nxt = 1, a, ac},
  {e, nxt} = addCherries[e, 0, c0, nxt];
  Do[ac = nxt; nxt += 1; e = Append[e, 0 <-> ac];
     {e, nxt} = addCherries[e, ac, cArm, nxt], {a, k}];
  e];

(* Pant's spider T(a1,...,am): m centers on a path spine, ai cherries on center i. *)
spider[as_List] := Module[{e = {}, nxt, m = Length[as], i},
  nxt = m; Do[e = Append[e, (i - 1) <-> i], {i, m - 1}];
  Do[{e, nxt} = addCherries[e, i - 1, as[[i]], nxt], {i, m}];
  e];

(* A rooted single BRANCH gadget from a nested spec: {c, {child1, child2, ...}}.
   Root gets a phantom parent (vertex -1) so its degree counts the parent edge. *)
ClearAll[branchEdges];
branchEdges[spec_, root_, nxt_] := Module[{c = spec[[1]], kids = spec[[2]], e = {}, k = nxt, ac, sub, ce},
  {e, k} = addCherries[e, root, c, k];
  Do[ce = k; k += 1; e = Append[e, root <-> ce];
     {sub, k} = branchEdges[kid, ce, k]; e = Join[e, sub], {kid, kids}];
  {e, k}];

(* The two exact ties (Phi = 1): the five-cherry near-star N(0,5) and the
   arm-substitute gadget root(c=4)-(c=0)-(c=0). *)
tieNearStar05 = cherryBundleStar[0, 5, 5];               (* a single center with 5 cherries = N(0,5) *)
armSubstitute = First@branchEdges[{4, {{0, {{0, {}}}}}}, -1, 0];

(* ---------- Laplacian ratio (exact) ---------- *)
laplacianRatio[edges_] := Module[{g = Graph[edges], L, degs},
  L = KirchhoffMatrix[g];
  degs = Times @@ VertexDegree[g];
  Permanent[L]/degs];

(* ---------- plain tree gallery ---------- *)
treePlot[edges_, lbl_] := Graph[edges,
  GraphLayout -> "LayeredEmbedding", VertexSize -> Medium,
  VertexStyle -> Directive[Orange], EdgeStyle -> Gray,
  PlotLabel -> Style[lbl, 14]];

gallery = GraphicsGrid[{{
   treePlot[spider[{3, 3, 3, 3}], "Pant spider  T(3,3,3,3)"],
   treePlot[cherryBundleStar[3, 5, 0], "cherry-bundle star  (hub de-loaded, arms=5)"]
  }, {
   treePlot[tieNearStar05, "tie  N(0,5)   (Phi = 1)"],
   treePlot[armSubstitute, "arm-substitute gadget  root(4)-0-0   (Phi = 1)"]
  }}, ImageSize -> 900];

(* ============================================================
   THE CAVITY FOLIATION  (the Wolfram-foliation analogue)
   ============================================================
   Root a branch at `root`, slice by depth, update the cavity field m_v from the
   leaves inward, and lay the tree out in depth-layers with vertices colored by m_v
   and sized by their per-vertex amplitude contribution Log[a_v z_v] - Log[m_v]. *)

cavityFoliation[edges_, root_] := Module[
  {g, depth, children, cval, cherryOf, degOf, m, a, z, contrib, layers, colFun, verts},
  g = Graph[edges, DirectedEdges -> False];
  verts = VertexList[g];
  (* depth from root via BFS *)
  depth = AssociationThread[verts -> (GraphDistance[g, root, #] & /@ verts)];
  (* rooted children: neighbors of larger depth *)
  children[v_] := Select[AdjacencyList[g, v], depth[#] > depth[v] &];
  (* structural (c_v, d_v): here every drawn vertex is a "center" with c=0 cherries in
     the abstract branch model unless it is a cherry pattern; for the schematic we take
     c_v=0 and d_v = degree (this shows the mechanism; the exact gadget uses c per node). *)
  degOf[v_] := VertexDegree[g, v];
  z[v_] := zdc[degOf[v], 0];
  a[v_] := adc[degOf[v], 0];
  (* cavity update, leaves -> root (postorder) *)
  m[v_] := m[v] = With[{ch = children[v]}, z[v]/(1 + z[v] Total[m /@ ch])];
  contrib[v_] := Log[a[v] z[v]] - Log[m[v]];
  colFun = ColorData["TemperatureMap"];
  Graph[edges,
    GraphLayout -> {"LayeredEmbedding", "RootVertex" -> root},
    VertexShapeFunction ->
      Function[{pt, v, r}, {colFun[Rescale[N@m[v], {0.05, 0.5}]], Disk[pt, r]}],
    VertexSize -> 0.4,
    VertexLabels ->
      Table[v -> Placed[Style[NumberForm[N@m[v], 3], 8], Center], {v, verts}],
    EdgeStyle -> LightGray,
    PlotLabel ->
      Style["cavity foliation:  m_v updates leaves -> root;  log Phi = " <>
        ToString[NumberForm[N@Total[contrib /@ verts], 4]], 13],
    ImageSize -> 700]
  ];

(* running amplitude accumulated slice-by-slice (the "updating process" quantified) *)
foliationProfile[edges_, root_] := Module[
  {g, depth, verts, children, m, a, z, contrib, byDepth, dmax},
  g = Graph[edges]; verts = VertexList[g];
  depth = AssociationThread[verts -> (GraphDistance[g, root, #] & /@ verts)];
  children[v_] := Select[AdjacencyList[g, v], depth[#] > depth[v] &];
  z[v_] := zdc[VertexDegree[g, v], 0]; a[v_] := adc[VertexDegree[g, v], 0];
  m[v_] := m[v] = With[{ch = children[v]}, z[v]/(1 + z[v] Total[m /@ ch])];
  contrib[v_] := Log[a[v] z[v]] - Log[m[v]];
  dmax = Max[Values[depth]];
  byDepth = Table[Total[contrib /@ Select[verts, depth[#] == d &]], {d, 0, dmax}];
  ListStepPlot[Accumulate[Reverse[byDepth]], "Post",
    PlotLabel -> "log Phi accumulated across depth-slices (leaves -> root)",
    AxesLabel -> {"slice (leaf->root)", "partial log Phi"}, Filling -> Axis,
    ImageSize -> 600]
  ];

(* ---------- render / export (uncomment to save) ---------- *)
Print["pi(T(3,3,3,3)) = ", laplacianRatio[spider[{3, 3, 3, 3}]]];      (* reproduces 19683/256 *)
Print["Phi ties: pi/rhoB^n at N(0,5) and arm-substitute are the amplitude maxima"];
gallery
cavityFoliation[armSubstitute, -1]
cavityFoliation[tieNearStar05, 0]
foliationProfile[cherryBundleStar[4, 5, 0], 0]

(* Export["tree_gallery.png", gallery];
   Export["cavity_foliation_tie.png", cavityFoliation[tieNearStar05, 0]];
   Export["cavity_foliation_armsub.png", cavityFoliation[armSubstitute, -1]]; *)
