/* =======================================================
 * sketch.js
 * Bijeli Brijeg Isometric 5-layer stack visualization
 * p5.js (WEBGL) + d3.csv()
 *
 * CLICKABLE "Votes" header behavior:
 * - Clicking "Votes" at top:
 *   • Highlights ALL vote dots in orange
 *   • Hides the connector lines (no spaghetti)
 *   • Turns the header button orange
 *   • Does NOT touch the indicator list styling
 *
 * HOVER "Votes" header behavior:
 *   • Temporarily highlights ALL vote dots in orange
 *   • Does NOT hide connector lines
 *
 * LAYER HIGHLIGHT:
 * - Currently selected layer gets a THICK ORANGE OUTLINE
 *   around that layer’s plate in 3D (#ED3C1A)
 *   (no more full orange band overlay)
 *
 * Hover logic:
 * - Hovering an INDICATOR only highlights that indicator (NOT its votes).
 * - Hovering a VOTE DOT highlights only that indicator’s votes.
 * - Hovering the "Votes ###" header highlights all votes.
 * ======================================================= */

/* ---------- CSV paths ---------- */
const CSV_MAIN = "BijeliBrijegP_reduced_mapped_edit.csv";
const CSV_STRUCT = "Layer_Strucutre_new.csv";

/* ---------- Colors / style ---------- */
const CLR_BG = [255, 255, 255];
const CLR_DOTS = [180, 180, 180];
const CLR_PLATES = [210, 210, 210];
const CLR_TILE = [190, 190, 190];
const CLR_ACTIVE = [237, 60, 26]; // #ED3C1A

/* ---------- Layers ---------- */
const LAYERS = [
  { name: "Votes (T only)" }, // 0
  { name: "Indicators" }, // 1
  { name: "Subcategories" }, // 2
  { name: "Categories" }, // 3
  { name: "Dimensions" }, // 4
];

/* ---------- Layout ---------- */
let W = 900,
  H = 650;
const PLATE_W = 220; // X extent
const PLATE_D = 140; // Z extent
const thickness = 3;
const verticalGap = 180;
const SHOW_PLATES = false;
let SHOW_LABELS = true;

/* ---------- Zoom ---------- */
let zoomed = false;
const VIEW_SIZE_BASE = 850;
const VIEW_SIZE_ZOOM = 420;
let scrollY = 0;
const SCROLL_PER_WHEEL = 0.5;

/* ---------- Geometry sizes ---------- */
const DOT_RADIUS_VOTES = 1.7;
const MIN_IND_RADIUS = 1.2;
const ZERO_IND_RADIUS = 0.8;
const POINT_MARGIN = 0.8;
const LIFT_DOTS = 0.8;
const LIFT_TILES = 0.6;

/* ---------- Camera ---------- */
let isoRotX, isoRotY;
let autoRotate = false;

/* ---------- Data containers ---------- */
let hierarchyMap = new Map(); // Map<dim, Map<cat, Set<sub>>>
let subToIndicators = new Map(); // Map<dim||cat||sub -> Set<indicatorKey>>
let catToIndicators = new Map(); // Map<dim||cat     -> Set<indicatorKey>>
let dimToIndicators = new Map(); // Map<dim          -> Set<indicatorKey>>
let mainRows = [];
let dataReady = false;

/* Pretty names */
let indicatorNames = [];
let subcatNames = [];
let catNames = [];
let dimNames = [];
const prettyIndicator = Object.create(null);
const prettySub = Object.create(null);
const prettyCat = Object.create(null);
const prettyDim = Object.create(null);

/* Per-indicator meta */
let indicatorsByKey = Object.create(null);
let indicatorCount = 0;
let totalVotesT = 0;

/* Layout outputs */
let indicatorNodes = []; // {x,z,index,name,radius,votesT,...}
let voteNodes = []; // {x,z,indicatorIndex}
let subcatTiles = null;
let catTiles = null;
let dimTiles = null;

/* Selection & UI state */
let selected = {
  type: null,
  indicators: new Set(),
  subcats: new Set(),
  cats: new Set(),
  dims: new Set(),
  subTriples: new Set(),
};

let lastClicked = null; // tracks last clicked entity
let anchorIndicator = null; // for drawing connector lines from one indicator

/* Hover state */
let hoverHit = null;
let lastHoverHit = null;
let lastSidebarHoverSig = null;

/* Sidebar hover lock */
let sidebarHoverActive = false;

/* NEW: header hover state for Votes */
let hoverVotesHeader = false;

/* Picking offscreen buffer */
let pickGL;
let pickMap = [];

/* Map name -> indicator index */
let nameToIndicatorIndex = new Map();

/* Caps / perf */
const MAX_CIRCLES = 50000;
const MAX_VOTE_LINES = 2000;

/* Totals (split/shared votes) */
let subVoteTotals = new Map(); // sub -> T
let catVoteTotals = new Map(); // cat -> T
let dimVoteTotals = new Map(); // dim -> T
let subVoteTotals3 = new Map(); // dim||cat||sub -> T
let catVoteTotals2 = new Map(); // dim||cat -> T
let subTotalAll = 0,
  catTotalAll = 0,
  dimTotalAll = 0;

/* RAW totals for pills (no fractional split, full indicator vote once per label) */
let subVoteTotalsRaw = new Map();
let catVoteTotalsRaw = new Map();
let dimVoteTotalsRaw = new Map();

/* Parent lookup */
let parentDimOfCat = new Map();

/* ---------- Expand state (chevrons for "show all") ---------- */
let SHOW_ALL_INDS = false;
let SHOW_ALL_SUBS = false;
let SHOW_ALL_CATS = false;
let SHOW_ALL_DIMS = false;

/* How many rows to show when collapsed in pills */
const DEFAULT_VISIBLE_ROWS = 3;

/* ---------- General helpers ---------- */
const KEY_SEP = "||";
const subKey = (dim, cat, sub) => `${dim}${KEY_SEP}${cat}${KEY_SEP}${sub}`;
const catKey = (dim, cat) => `${dim}${KEY_SEP}${cat}`;
const EPS = 1e-9;

function hasSubVotes(dim, cat, sub) {
  const k = subKey(normKey(dim), normKey(cat), normKey(sub));
  return (subVoteTotals3.get(k) || 0) > 0;
}

function hasVotes(map, name) {
  return (map.get(name) || 0) > EPS;
}

function normKey(s) {
  return String(s || "")
    .toLowerCase()
    .normalize("NFD")
    .replace(/\p{Diacritic}/gu, "")
    .replace(/&/g, "and")
    .replace(/[^a-z0-9\s]/g, " ")
    .replace(/\s+/g, " ")
    .trim();
}

function encodeID(id) {
  const n = id + 1;
  return [n & 255, (n >> 8) & 255, (n >> 16) & 255];
}
function decodeID(r, g, b) {
  const n = r + (g << 8) + (b << 16);
  return n === 0 ? -1 : n - 1;
}

function escapeHTML(s) {
  return String(s).replace(
    /[&<>"']/g,
    (m) =>
      ({
        "&": "&amp;",
        "<": "&lt;",
        ">": "&gt;",
        '"': "&quot;",
        "'": "&#39;",
      }[m])
  );
}

function titleCase(s) {
  return String(s || "")
    .replace(/[_\-]+/g, " ")
    .replace(/\s+/g, " ")
    .trim()
    .toLowerCase()
    .replace(/\b\w/g, (c) => c.toUpperCase());
}

function clamp(v, a, b) {
  return Math.max(a, Math.min(b, v));
}

/* ---- Pill visibility helpers ---- */
function _pillsPerRow(containerId) {
  const el = document.getElementById(containerId);
  const w = el ? el.getBoundingClientRect().width : 0;
  const avg = 110; // avg pill width incl. gap
  return Math.max(1, Math.floor(w > 0 ? w / avg : 6));
}
function _limitVisiblePills(items, showAll, containerId) {
  if (showAll) return items;
  const perRow = _pillsPerRow(containerId);
  const quota = perRow * DEFAULT_VISIBLE_ROWS;
  return items.slice(0, quota);
}

function enforceRowLimit(containerEl, showAllFlag) {
  if (!containerEl) return;
  if (showAllFlag) {
    containerEl.querySelectorAll(".pill").forEach((pill) => {
      pill.style.display = "";
    });
    return;
  }

  const maxRows = DEFAULT_VISIBLE_ROWS;
  const pills = Array.from(containerEl.querySelectorAll(".pill"));
  if (!pills.length) return;

  const rowTops = [];

  for (let i = 0; i < pills.length; i++) {
    const pill = pills[i];
    const top = pill.offsetTop;

    let rowIndex = rowTops.findIndex((t) => Math.abs(t - top) < 1);
    if (rowIndex === -1) {
      rowTops.push(top);
    }

    if (rowTops.length > maxRows) {
      for (let j = i; j < pills.length; j++) {
        pills[j].style.display = "none";
      }
      break;
    } else {
      pill.style.display = "";
    }
  }
}

/* ---------- Seeded RNG for stable placement ---------- */
function __mulberry32(a) {
  return function () {
    let t = (a += 0x6d2b79f5);
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
let __rng = null;
function setPlacementSeed(seed) {
  const s = seed >>> 0 || 1;
  __rng = __mulberry32(s);
  randomSeed(s); // also seed p5's random
}
function rand() {
  return __rng ? __rng() : Math.random();
}
function randBetween(min, max) {
  return min + (max - min) * rand();
}
function shuffleSeeded(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(rand() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
}
function stableSeedFromData() {
  const s =
    indicatorNames.join("|") +
    "|" +
    Math.round(totalVotesT) +
    "|" +
    mainRows.length;
  // FNV-1a 32-bit
  let h = 0x811c9dc5;
  for (let i = 0; i < s.length; i++) {
    h ^= s.charCodeAt(i);
    h = Math.imul(h, 0x01000193);
  }
  return h >>> 0;
}

/* ---------- Layer selection helpers ---------- */
function getSelectedLayerIndex() {
  switch (selected?.type) {
    case "vote":
      return 0;
    case "indicator":
      return 1;
    case "subcat":
      return 2;
    case "cat":
      return 3;
    case "dim":
      return 4;
    default:
      if (lastClicked && lastClicked.type === "voteAll") return 0;
      return null;
  }
}

/* ---------- Plate outline helper ---------- */
function outlinePlate(sizeX, sizeZ) {
  push();
  noFill();
  stroke(237, 60, 26); // orange
  strokeWeight(3);
  beginShape();
  vertex(-sizeX, 0, -sizeZ);
  vertex(sizeX, 0, -sizeZ);
  vertex(sizeX, 0, sizeZ);
  vertex(-sizeX, 0, sizeZ);
  endShape(CLOSE);
  pop();
}

// draw thick orange outline around active layer's plate
function drawLayerOutline(layerIndex, halfStack) {
  if (layerIndex == null) return;

  function liftFor(i) {
    return i <= 1 ? thickness / 2 + LIFT_DOTS : thickness / 2 + LIFT_TILES;
  }
  const yWorld = layerIndex * verticalGap - halfStack + liftFor(layerIndex);

  push();
  translate(0, yWorld, 0);
  outlinePlate(PLATE_W / 2, PLATE_D / 2);
  pop();
}

/* ---------- "Select all votes" ---------- */
function selectAllVotes() {
  selected = {
    type: "vote",
    indicators: new Set(),
    subcats: new Set(),
    cats: new Set(),
    dims: new Set(),
    subTriples: new Set(),
  };

  lastClicked = { type: "voteAll" };
  anchorIndicator = null;

  updatePanel();

  const btn = document.getElementById("votesHeaderBtn");
  if (btn) btn.classList.add("active");
}

/* ---------- Clear selection ---------- */
function clearSelectionAndHeader() {
  selected = {
    type: null,
    indicators: new Set(),
    subcats: new Set(),
    cats: new Set(),
    dims: new Set(),
    subTriples: new Set(),
  };
  lastClicked = null;
  anchorIndicator = null;

  const btn = document.getElementById("votesHeaderBtn");
  if (btn) btn.classList.remove("active");

  updatePanel();
}

/* ---------- Hierarchy helpers ---------- */
function buildHierarchyMap(structRows) {
  const map = new Map();
  for (const r of structRows) {
    const dim = normKey(r["Dimension"]);
    const cat = normKey(r["Category"]);
    const sub = normKey(r["Subcategory"]);
    if (!dim || !cat || !sub) continue;
    if (!map.has(dim)) map.set(dim, new Map());
    const cm = map.get(dim);
    if (!cm.has(cat)) cm.set(cat, new Set());
    cm.get(cat).add(sub);
  }
  return map;
}

function buildParentLookups() {
  parentDimOfCat = new Map();
  for (const [dim, catMap] of hierarchyMap.entries()) {
    for (const cat of catMap.keys()) {
      if (!parentDimOfCat.has(cat)) parentDimOfCat.set(cat, dim);
    }
  }
}

/* ---------- Contextual indices ---------- */
function buildContextualIndices(rows) {
  subToIndicators = new Map();
  catToIndicators = new Map();
  dimToIndicators = new Map();

  const addTo = (m, key, indKey) => {
    if (!m.has(key)) m.set(key, new Set());
    m.get(key).add(indKey);
  };

  for (const r of rows) {
    const indEN_raw = getField(r, [
      "Indicator English",
      "Indicator_English",
      "IndicatorEnglish",
      "Indicator EN",
      "Indicator_EN",
      "IndicatorEn",
    ]);
    const indKey = (indEN_raw || "").toLowerCase().trim();
    if (!indKey) continue;

    const paths = [
      {
        dim: normKey(r["Dimension 1"]),
        cat: normKey(r["Category 1"]),
        sub: normKey(r["Subcategory 1"]),
      },
      {
        dim: normKey(r["Dimension 2"]),
        cat: normKey(r["Category 2"]),
        sub: normKey(r["Subcategory 2"]),
      },
    ];
    for (const p of paths) {
      if (!p.dim || !p.cat || !p.sub) continue;
      const catMap = hierarchyMap.get(p.dim);
      if (!catMap) continue;
      const subs = catMap.get(p.cat);
      if (!subs || !subs.has(p.sub)) continue;
      addTo(subToIndicators, subKey(p.dim, p.cat, p.sub), indKey);
      addTo(catToIndicators, catKey(p.dim, p.cat), indKey);
      addTo(dimToIndicators, p.dim, indKey);
    }
  }
}

/* ---------- Pretty labels ---------- */
function rememberPretty(mapObj, lc, original) {
  if (!lc) return;
  if (!mapObj[lc]) mapObj[lc] = String(original || lc);
}

/* ---------- robust field getter from CSV row ---------- */
function getField(row, names) {
  for (const n of names) {
    if (row[n] != null) {
      const s = String(row[n]).trim();
      if (s !== "") return s;
    }
  }
  return "";
}

function toNum(x) {
  const n = +String(x).replace(",", ".");
  return Number.isFinite(n) ? n : 0;
}

/* ---------- Totals ---------- */
function accumulateVotes(rows) {
  subVoteTotals3 = new Map();
  catVoteTotals2 = new Map();
  subVoteTotals = new Map();
  catVoteTotals = new Map();
  dimVoteTotals = new Map();

  subVoteTotalsRaw = new Map();
  catVoteTotalsRaw = new Map();
  dimVoteTotalsRaw = new Map();

  totalVotesT = 0;

  for (const r of rows) {
    const votesT = toNum(r["Votes T"] || r["Votes_T"]);
    if (votesT <= 0) continue;
    totalVotesT += votesT;

    const indKey = normKey(
      getField(r, [
        "Indicator English",
        "Indicator_English",
        "IndicatorEnglish",
        "Indicator EN",
        "Indicator_EN",
      ])
    );
    if (!indKey) continue;

    const paths = [
      {
        dim: normKey(r["Dimension 1"]),
        cat: normKey(r["Category 1"]),
        sub: normKey(r["Subcategory 1"]),
      },
      {
        dim: normKey(r["Dimension 2"]),
        cat: normKey(r["Category 2"]),
        sub: normKey(r["Subcategory 2"]),
      },
    ];

    for (const p of paths) {
      if (!p.dim || !p.cat || !p.sub) continue;

      const sk = subKey(p.dim, p.cat, p.sub);
      const ck = catKey(p.dim, p.cat);
      const dk = p.dim;

      subVoteTotals3.set(sk, (subVoteTotals3.get(sk) || 0) + votesT);
      catVoteTotals2.set(ck, (catVoteTotals2.get(ck) || 0) + votesT);
      subVoteTotals.set(p.sub, (subVoteTotals.get(p.sub) || 0) + votesT);
      catVoteTotals.set(p.cat, (catVoteTotals.get(p.cat) || 0) + votesT);
      dimVoteTotals.set(p.dim, (dimVoteTotals.get(p.dim) || 0) + votesT);
    }
  }

  for (const [sub, t] of subVoteTotals.entries()) subVoteTotalsRaw.set(sub, t);
  for (const [cat, t] of catVoteTotals.entries()) catVoteTotalsRaw.set(cat, t);
  for (const [dim, t] of dimVoteTotals.entries()) dimVoteTotalsRaw.set(dim, t);
}

/* ---------- Placement helpers ---------- */
function placeRandomNonOverlapRect(count, radius, w, d) {
  const pts = [];
  if (count <= 0) return pts;

  const halfW = (w - 2 * radius - 2 * POINT_MARGIN) / 2;
  const halfD = (d - 2 * radius - 2 * POINT_MARGIN) / 2;
  const minD2 = (2 * radius + POINT_MARGIN) ** 2;

  let attempts = 0,
    maxAttempts = count * 400;

  while (pts.length < count && attempts < maxAttempts) {
    attempts++;
    const x = randBetween(-halfW, halfW);
    const z = randBetween(-halfD, halfD);

    let ok = true;
    for (let i = 0; i < pts.length; i++) {
      const dx = x - pts[i].x;
      const dz = z - pts[i].z;
      if (dx * dx + dz * dz < minD2) {
        ok = false;
        break;
      }
    }
    if (ok) pts.push({ x, z });
  }

  if (pts.length < count) {
    const needed = count - pts.length;
    const grid = computeDotPositionsGridRect(needed, w, d, radius);
    for (const p of grid) pts.push(p);
  }
  return pts;
}

function computeDotPositionsGridRect(count, w, d, radius) {
  const pts = [];
  if (count <= 0) return pts;

  const usableW = Math.max(1, w - 2 * radius - 2 * POINT_MARGIN);
  const usableD = Math.max(1, d - 2 * radius - 2 * POINT_MARGIN);

  const aspect = usableW / usableD;
  let cols = Math.max(1, Math.round(Math.sqrt(count * aspect)));
  let rows = Math.max(1, Math.ceil(count / cols));

  const spacingOK = (c, r) => {
    const sx = c > 1 ? usableW / (c - 1) : usableW;
    const sz = r > 1 ? usableD / (r - 1) : usableD;
    return sx >= 2 * radius + POINT_MARGIN && sz >= 2 * radius + POINT_MARGIN;
  };

  while (cols > 1 && !spacingOK(cols, rows)) {
    cols--;
    rows = Math.max(1, Math.ceil(count / cols));
  }

  const xMin = -usableW / 2;
  const zMin = -usableD / 2;

  let placed = 0;
  for (let r = 0; r < rows; r++) {
    const remaining = count - placed;
    const itemsThisRow = Math.min(cols, remaining);
    if (itemsThisRow <= 0) break;

    const stepX = itemsThisRow > 1 ? usableW / (itemsThisRow - 1) : 0;
    const z = rows > 1 ? zMin + (usableD * r) / (rows - 1) : 0;

    for (let c = 0; c < itemsThisRow; c++) {
      const jitterX = (rand() - 0.5) * Math.min(stepX * 0.2, radius);
      const jitterZ = (rand() - 0.5) * Math.min((usableD / rows) * 0.2, radius);
      const x = itemsThisRow > 1 ? xMin + stepX * c + jitterX : 0;
      pts.push({ x, z: z + jitterZ });
      placed++;
    }
  }

  shuffleSeeded(pts);
  return pts;
}

/* Circle packing for indicators (layer 1) */
function placeCirclesVariableRect(radii, w, d) {
  const items = radii.map((r, idx) => ({ r, idx })).sort((a, b) => b.r - a.r);
  const out = new Array(radii.length);
  const halfW = w / 2 - 2;
  const halfD = d / 2 - 2;
  const maxAttemptsPer = 1200;
  const placed = [];

  for (const it of items) {
    let ok = false,
      tries = 0;
    const R = it.r;

    const minX = -halfW + R + POINT_MARGIN;
    const maxX = halfW - R - POINT_MARGIN;
    const minZ = -halfD + R + POINT_MARGIN;
    const maxZ = halfD - R - POINT_MARGIN;

    while (!ok && tries < maxAttemptsPer) {
      tries++;
      const x = randBetween(minX, maxX);
      const z = randBetween(minZ, maxZ);

      ok = true;
      for (const p of placed) {
        const dx = x - p.x;
        const dz = z - p.z;
        const minD = R + p.r + POINT_MARGIN;
        if (dx * dx + dz * dz < minD * minD) {
          ok = false;
          break;
        }
      }

      if (ok) {
        const node = { x, z, r: R, idx: it.idx };
        placed.push(node);
        out[it.idx] = node;
      }
    }

    if (!ok) {
      const node = { x: 0, z: 0, r: R, idx: it.idx };
      placed.push(node);
      out[it.idx] = node;
    }
  }
  return out;
}

/* ---------- Treemap ---------- */
function computeTreemapFromItemsRect(itemsIn, w, d, padding = 0) {
  if (!itemsIn || itemsIn.length === 0) {
    return { items: [], tileW: w, tileH: d };
  }

  const root = d3
    .hierarchy({ children: itemsIn })
    .sum((item) => Math.max(0, item.value))
    .sort((a, b) => b.value - a.value);

  d3.treemap().size([w, d]).paddingInner(padding).round(true)(root);

  const items = root.leaves().map((leaf) => {
    const { x0, y0, x1, y1 } = leaf;
    const tileW = Math.max(1, x1 - x0);
    const tileD = Math.max(1, y1 - y0);
    const cx = -w / 2 + x0 + tileW / 2;
    const cz = -d / 2 + y0 + tileD / 2;
    const data = leaf.data;
    return {
      x: cx,
      z: cz,
      width: tileW,
      depth: tileD,
      pickId: -1,
      key: data.key,
      dim: data.dim,
      cat: data.cat,
      sub: data.sub,
      label: data.label,
      votes: data.value,
    };
  });

  return { items, tileW: w, tileH: d };
}

/* ---------- Parse/aggregate rows + layout ---------- */
function parseAndAggregate(rows) {
  const indSet = new Set();
  indicatorsByKey = Object.create(null);
  totalVotesT = 0;

  subVoteTotals = new Map();
  catVoteTotals = new Map();
  dimVoteTotals = new Map();
  subVoteTotals3 = new Map();
  catVoteTotals2 = new Map();

  rows.forEach((r) => {
    const indEN_raw = getField(r, [
      "Indicator English",
      "Indicator_English",
      "IndicatorEnglish",
      "Indicator EN",
      "Indicator_EN",
      "IndicatorEn",
    ]);
    const indKey = (indEN_raw || "").toLowerCase().trim();
    if (!indKey) return;
    rememberPretty(prettyIndicator, indKey, indEN_raw);

    const sub1_raw = getField(r, [
      "Subcategory 1",
      "Subcategory1",
      "Subcategory_1",
      "subcategory 1",
      "subcategory1",
      "subcategory_1",
      "Subcategory EN",
      "Subcategory English",
    ]);
    const sub2_raw = getField(r, [
      "Subcategory 2",
      "Subcategory2",
      "Subcategory_2",
      "subcategory 2",
      "subcategory2",
      "subcategory_2",
      "Subcategory BS",
      "Subcategory Bosnian",
    ]);

    const cat1_raw = getField(r, [
      "Category 1",
      "Category1",
      "Category_1",
      "category 1",
      "category1",
      "category_1",
    ]);
    const cat2_raw = getField(r, [
      "Category 2",
      "Category2",
      "Category_2",
      "category 2",
      "category2",
      "category_2",
    ]);

    const d1_raw = getField(r, [
      "Dimension 1",
      "dimension 1",
      "Dimension1",
      "dimension1",
      "Dimension_1",
      "dimension_1",
    ]);
    const d2_raw = getField(r, [
      "Dimension 2",
      "dimension 2",
      "Dimension2",
      "dimension2",
      "Dimension_2",
      "dimension_2",
    ]);

    const subs = [sub1_raw, sub2_raw].filter(Boolean).map((s) => {
      const k = normKey(s);
      rememberPretty(prettySub, k, s);
      return k;
    });

    const cats = [cat1_raw, cat2_raw].filter(Boolean).map((s) => {
      const k = normKey(s);
      rememberPretty(prettyCat, k, s);
      return k;
    });

    const dims = [d1_raw, d2_raw].filter(Boolean).map((s) => {
      const k = normKey(s);
      rememberPretty(prettyDim, k, s);
      return k;
    });

    const t = toNum(
      r.T ?? r.t ?? r.Total_T ?? r.total_T ?? r.total ?? r.Total ?? 0
    );
    totalVotesT += t;

    if (!indicatorsByKey[indKey]) {
      indicatorsByKey[indKey] = {
        name: indKey,
        subSet: new Set(),
        catSet: new Set(),
        dimSet: new Set(),
        votesT: 0,
        subToCats: new Map(),
        catToDims: new Map(),
        validTriplesKeys: new Set(),
      };
    }
    const meta = indicatorsByKey[indKey];

    subs.forEach((s) => meta.subSet.add(s));
    cats.forEach((c) => meta.catSet.add(c));
    dims.forEach((d) => meta.dimSet.add(d));
    meta.votesT += t;

    for (const s of subs) {
      if (!meta.subToCats.has(s)) meta.subToCats.set(s, new Set());
      for (const c of cats) meta.subToCats.get(s).add(c);
    }
    for (const c of cats) {
      if (!meta.catToDims.has(c)) meta.catToDims.set(c, new Set());
      for (const d of dims) meta.catToDims.get(c).add(d);
    }

    indSet.add(indKey);

    // Figure out valid (dim,cat,sub) paths
    const triples = [];
    const paths = [
      { dim: normKey(d1_raw), cat: normKey(cat1_raw), sub: normKey(sub1_raw) },
      { dim: normKey(d2_raw), cat: normKey(cat2_raw), sub: normKey(sub2_raw) },
    ];
    for (const p of paths) {
      if (!p.dim || !p.cat || !p.sub) continue;
      const cm = hierarchyMap.get(p.dim);
      if (!cm) continue;
      const ss = cm.get(p.cat);
      if (!ss || !ss.has(p.sub)) continue;
      triples.push(p);
    }

    if (t > 0) {
      if (triples.length > 0) {
        const share = t / triples.length;
        for (const p of triples) {
          const sKey = subKey(p.dim, p.cat, p.sub);
          const cKey = catKey(p.dim, p.cat);

          subVoteTotals3.set(sKey, (subVoteTotals3.get(sKey) || 0) + share);
          catVoteTotals2.set(cKey, (catVoteTotals2.get(cKey) || 0) + share);
          dimVoteTotals.set(p.dim, (dimVoteTotals.get(p.dim) || 0) + share);
          subVoteTotals.set(p.sub, (subVoteTotals.get(p.sub) || 0) + share);
          catVoteTotals.set(p.cat, (catVoteTotals.get(p.cat) || 0) + share);

          meta.validTriplesKeys.add(sKey);
        }
      } else {
        // fallback: credit dims that exist
        const dimsValid = dims.filter((d) => hierarchyMap.has(d));
        if (dimsValid.length > 0) {
          const shareD = t / dimsValid.length;
          for (const d of dimsValid) {
            dimVoteTotals.set(d, (dimVoteTotals.get(d) || 0) + shareD);
          }
        }
      }

      const headVotesEl = document.getElementById("totalVotesHead");
      if (headVotesEl) headVotesEl.textContent = Math.round(totalVotesT);
    }
  });

  // grand totals
  subTotalAll = [...subVoteTotals.values()].reduce((a, b) => a + b, 0);
  catTotalAll = [...catVoteTotals.values()].reduce((a, b) => a + b, 0);
  dimTotalAll = [...dimVoteTotals.values()].reduce((a, b) => a + b, 0);

  const totalEl = document.getElementById("totalVotesHead");
  if (totalEl) totalEl.textContent = Math.round(totalVotesT);

  indicatorNames = [...indSet].sort();

  subcatNames = [...subVoteTotals.entries()]
    .filter(([, v]) => v > EPS)
    .map(([k]) => k)
    .sort();

  catNames = [...catVoteTotals.entries()]
    .filter(([, v]) => v > EPS)
    .map(([k]) => k)
    .sort();

  dimNames = [...dimVoteTotals.entries()]
    .filter(([, v]) => v > EPS)
    .map(([k]) => k)
    .sort();

  indicatorCount = clamp(indicatorNames.length, 0, MAX_CIRCLES);
  totalVotesT = clamp(totalVotesT, 0, MAX_CIRCLES);

  for (const key in indicatorsByKey) {
    const m = indicatorsByKey[key];
    if (m.validTriplesKeys) {
      m.validTriples = [...m.validTriplesKeys].map((k) => {
        const [d, c, s] = k.split(KEY_SEP);
        return { dim: d, cat: c, sub: s, key: k };
      });
    }
  }

  // Raw totals (no fractional split), count each indicator once per label it touches in a VALID triple
  subVoteTotalsRaw = new Map();
  catVoteTotalsRaw = new Map();
  dimVoteTotalsRaw = new Map();

  for (const key in indicatorsByKey) {
    const meta = indicatorsByKey[key];
    const v = meta.votesT || 0;
    if (v <= 0) continue;

    const subsSeen = new Set();
    const catsSeen = new Set();
    const dimsSeen = new Set();

    const triples = meta.validTriples || [];
    for (const t of triples) {
      if (t.sub) subsSeen.add(t.sub);
      if (t.cat) catsSeen.add(t.cat);
      if (t.dim) dimsSeen.add(t.dim);
    }

    for (const s of subsSeen) {
      subVoteTotalsRaw.set(s, (subVoteTotalsRaw.get(s) || 0) + v);
    }
    for (const c of catsSeen) {
      catVoteTotalsRaw.set(c, (catVoteTotalsRaw.get(c) || 0) + v);
    }
    for (const d of dimsSeen) {
      dimVoteTotalsRaw.set(d, (dimVoteTotalsRaw.get(d) || 0) + v);
    }
  }
}

/* ---------- initFromCSV(rows) builds layout ---------- */
function initFromCSV(rows) {
  parseAndAggregate(rows);

  // stable seeded randomness
  setPlacementSeed(stableSeedFromData());

  const aVote = Math.PI * DOT_RADIUS_VOTES * DOT_RADIUS_VOTES;

  // layer 1: indicators as circles
  indicatorNodes = indicatorNames.map((key, i) => {
    const meta = indicatorsByKey[key] || {};
    const theVotes = meta.votesT | 0 || 0;
    const r =
      theVotes > 0
        ? Math.max(MIN_IND_RADIUS, Math.sqrt((theVotes * aVote) / Math.PI))
        : ZERO_IND_RADIUS;
    return {
      x: 0,
      z: 0,
      index: i,
      name: key,
      subSet: meta.subSet || new Set(),
      catSet: meta.catSet || new Set(),
      dimSet: meta.dimSet || new Set(),
      subToCats: meta.subToCats || new Map(),
      catToDims: meta.catToDims || new Map(),
      validTriples: meta.validTriples || [],
      votesT: theVotes,
      radius: r,
      pickId: -1,
    };
  });

  // index lookup name -> node index
  nameToIndicatorIndex = new Map();
  for (const n of indicatorNodes) {
    nameToIndicatorIndex.set(n.name, n.index);
  }

  // pack circles
  const indPositions = placeCirclesVariableRect(
    indicatorNodes.map((n) => n.radius),
    PLATE_W,
    PLATE_D
  );
  for (let i = 0; i < indicatorNodes.length; i++) {
    indicatorNodes[i].x = indPositions[i].x;
    indicatorNodes[i].z = indPositions[i].z;
  }

  // layer 0: votes as small dots
  const votePts = placeRandomNonOverlapRect(
    totalVotesT,
    DOT_RADIUS_VOTES,
    PLATE_W,
    PLATE_D
  );

  voteNodes = [];
  const expanded = [];
  indicatorNodes.forEach((n, idx) => {
    for (let k = 0; k < (n.votesT | 0); k++) expanded.push(idx);
  });
  shuffleSeeded(expanded);

  for (let k = 0; k < votePts.length; k++) {
    const indIdx = k < expanded.length ? expanded[k] : -1;
    voteNodes.push({
      x: votePts[k].x,
      z: votePts[k].z,
      indicatorIndex: indIdx,
      pickId: -1,
    });
  }

  // treemaps for subcat (2), cat (3), dim (4)
  const subItems = [...subVoteTotals3.entries()]
    .filter(([, v]) => v > 0)
    .map(([k, v]) => {
      const [d, c, s] = k.split(KEY_SEP);
      return {
        key: k,
        dim: d,
        cat: c,
        sub: s,
        value: v,
        label: prettySub[s] || titleCase(s),
      };
    });

  const catItems = [...catVoteTotals2.entries()]
    .filter(([, v]) => v > EPS)
    .map(([k, v]) => {
      const [d, c] = k.split(KEY_SEP);
      return {
        key: k,
        dim: d,
        cat: c,
        value: v,
        label: prettyCat[c] || titleCase(c),
      };
    });

  const dimItems = [...dimVoteTotals.entries()]
    .filter(([, v]) => v > EPS)
    .map(([d, v]) => ({
      key: d,
      dim: d,
      value: v,
      label: prettyDim[d] || titleCase(d),
    }));

  subcatTiles = computeTreemapFromItemsRect(subItems, PLATE_W, PLATE_D, 0);
  catTiles = computeTreemapFromItemsRect(catItems, PLATE_W, PLATE_D, 0);
  dimTiles = computeTreemapFromItemsRect(dimItems, PLATE_W, PLATE_D, 0);

  // Build pickMap IDs
  pickMap = [];
  let nextId = 0;

  // votes (layer 0)
  for (let vi = 0; vi < voteNodes.length; vi++) {
    const v = voteNodes[vi];
    v.pickId = nextId;
    pickMap[nextId++] = {
      type: "vote",
      nodeIdx: vi,
      indicatorIndex: v.indicatorIndex,
    };
  }

  // indicators (layer 1)
  for (const n of indicatorNodes) {
    n.pickId = nextId;
    pickMap[nextId++] = { type: "indicator", index: n.index };
  }

  // subcats (layer 2)
  for (const t of subcatTiles.items) {
    t.pickId = nextId;
    pickMap[nextId++] = {
      type: "subcat",
      dim: t.dim,
      cat: t.cat,
      sub: t.sub,
    };
  }

  // cats (layer 3)
  for (const t of catTiles.items) {
    t.pickId = nextId;
    pickMap[nextId++] = { type: "cat", dim: t.dim, cat: t.cat };
  }

  // dims (layer 4)
  for (const t of dimTiles.items) {
    t.pickId = nextId;
    pickMap[nextId++] = { type: "dim", dim: t.dim };
  }

  anchorIndicator = null;
  updatePanel();
}

/* ---------- PICKING ---------- */
function pickAt(px, py) {
  pickGL.push();
  pickGL.clear();
  pickGL.background(0);
  pickGL.noLights();

  // last drawn wins
  if (pickGL._renderer && pickGL._renderer.GL) {
    pickGL._renderer.GL.disable(pickGL._renderer.GL.DEPTH_TEST);
  }

  const viewSizeNow = zoomed ? VIEW_SIZE_ZOOM : VIEW_SIZE_BASE;
  pickGL.ortho(
    -viewSizeNow / 2,
    viewSizeNow / 2,
    -viewSizeNow / 2,
    viewSizeNow / 2,
    0.01,
    5000
  );

  const aspect = W / H;
  pickGL.push();
  if (aspect > 1) pickGL.scale(1 / aspect, 1, 1);
  else if (aspect < 1) pickGL.scale(1, aspect, 1);

  pickGL.rotateX(isoRotX);
  pickGL.rotateY(isoRotY);
  if (zoomed) pickGL.translate(0, -scrollY, 0);

  const halfStack = ((LAYERS.length - 1) * verticalGap) / 2;

  // ----- indicators (layer 1) -----
  {
    const y = 1 * verticalGap - halfStack;
    const lift = thickness / 2 + LIFT_DOTS;
    pickGL.noStroke();
    for (const n of indicatorNodes) {
      const [r, g, b] = encodeID(n.pickId);
      pickGL.push();
      pickGL.translate(n.x, y + lift, n.z);
      pickGL.fill(r, g, b);
      pickGL.cylinder(Math.max(0.5, n.radius), 1, 20, 1, true, true);
      pickGL.pop();
    }
  }

  // ----- subcats (layer 2) -----
  {
    const y = 2 * verticalGap - halfStack;
    const lift = thickness / 2 + LIFT_TILES;
    pickGL.noStroke();
    for (const t of subcatTiles.items) {
      const [r, g, b] = encodeID(t.pickId);
      pickGL.push();
      pickGL.translate(t.x, y + lift, t.z);
      pickGL.fill(r, g, b);
      pickGL.box(Math.max(1, t.width), 1, Math.max(1, t.depth));
      pickGL.pop();
    }
  }

  // ----- cats (layer 3) -----
  {
    const y = 3 * verticalGap - halfStack;
    const lift = thickness / 2 + LIFT_TILES;
    pickGL.noStroke();
    for (const t of catTiles.items) {
      const [r, g, b] = encodeID(t.pickId);
      pickGL.push();
      pickGL.translate(t.x, y + lift, t.z);
      pickGL.fill(r, g, b);
      pickGL.box(Math.max(1, t.width), 1, Math.max(1, t.depth));
      pickGL.pop();
    }
  }

  // ----- dims (layer 4) -----
  {
    const y = 4 * verticalGap - halfStack;
    const lift = thickness / 2 + LIFT_TILES;
    pickGL.noStroke();
    for (const t of dimTiles.items) {
      const [r, g, b] = encodeID(t.pickId);
      pickGL.push();
      pickGL.translate(t.x, y + lift, t.z);
      pickGL.fill(r, g, b);
      pickGL.box(Math.max(1, t.width), 1, Math.max(1, t.depth));
      pickGL.pop();
    }
  }

  // ----- votes (layer 0) ----- (draw last so it wins)
  {
    const y = 0 * verticalGap - halfStack;
    const lift = thickness / 2 + LIFT_DOTS;
    pickGL.noStroke();
    for (const v of voteNodes) {
      const [r, g, b] = encodeID(v.pickId);
      pickGL.push();
      pickGL.translate(v.x, y + lift, v.z);
      pickGL.fill(r, g, b);
      pickGL.cylinder(DOT_RADIUS_VOTES, 1, 16, 1, true, true);
      pickGL.pop();
    }
  }

  pickGL.pop(); // inner push
  pickGL.pop(); // outer push

  // re-enable depth
  if (pickGL._renderer && pickGL._renderer.GL) {
    pickGL._renderer.GL.enable(pickGL._renderer.GL.DEPTH_TEST);
  }

  pickGL.loadPixels();
  const dpr = pickGL.pixelDensity();
  const ix = Math.floor(px * dpr);
  const iy = Math.floor(py * dpr);

  if (
    ix < 0 ||
    iy < 0 ||
    ix >= pickGL.width * dpr ||
    iy >= pickGL.height * dpr
  ) {
    return null;
  }

  const idx = 4 * (iy * pickGL.width * dpr + ix);
  const r = pickGL.pixels[idx] | 0;
  const g = pickGL.pixels[idx + 1] | 0;
  const b = pickGL.pixels[idx + 2] | 0;

  const id = decodeID(r, g, b);
  if (id < 0 || id >= pickMap.length) return null;

  return pickMap[id];
}

/* ---------- Hover stabilization ---------- */
function resolveStableHover(rawHit, prevHit) {
  const prevType = prevHit ? prevHit.type : null;
  const hasActiveSelection = !!(selected && selected.type);

  if (!rawHit) return prevHit ? { ...prevHit } : null;

  if (rawHit.type === "indicator") {
    return { type: "indicator", index: rawHit.index };
  }

  if (rawHit.type === "vote") {
    if (!hasActiveSelection && prevType === "indicator") {
      return prevHit;
    }
    return {
      type: "voteStable",
      indicatorIndex:
        rawHit.indicatorIndex != null ? rawHit.indicatorIndex : -1,
    };
  }

  if (rawHit.type === "subcat") {
    return {
      type: "subcat",
      sub: rawHit.sub,
      cat: rawHit.cat,
      dim: rawHit.dim,
    };
  }
  if (rawHit.type === "cat") {
    return { type: "cat", cat: rawHit.cat, dim: rawHit.dim };
  }
  if (rawHit.type === "dim") {
    return { type: "dim", dim: rawHit.dim };
  }
  return rawHit;
}

updatePanel();

/* ---------- Canvas click handler ---------- */
function onCanvasPressed() {
  if (!dataReady) return;

  const hit = pickAt(mouseX, mouseY);

  if (!hit) {
    clearSelectionAndHeader();
    return;
  }

  selected = computeSelectionFromHit(hit);

  if (hit.type === "indicator") {
    lastClicked = { type: "indicator", key: indicatorNodes[hit.index].name };
  }
  if (hit.type === "subcat") {
    lastClicked = {
      type: "subcat",
      key: hit.sub || hit.name,
      dim: hit.dim,
      cat: hit.cat,
    };
  }
  if (hit.type === "cat") {
    lastClicked = { type: "cat", key: hit.cat || hit.name, dim: hit.dim };
  }
  if (hit.type === "dim") {
    lastClicked = { type: "dim", key: hit.dim || hit.name };
  }

  if (hit.type === "indicator") anchorIndicator = hit.index;
  if (hit.type === "vote" && hit.indicatorIndex >= 0)
    anchorIndicator = hit.indicatorIndex;

  const btn = document.getElementById("votesHeaderBtn");
  if (btn) {
    if (hit.type === "vote") {
      btn.classList.add("active");
      if (!lastClicked || lastClicked.type !== "voteAll") {
        lastClicked = { type: "voteSingle" };
      }
    } else {
      btn.classList.remove("active");
      if (
        lastClicked &&
        (lastClicked.type === "voteAll" || lastClicked.type === "voteSingle")
      ) {
        lastClicked = null;
      }
    }
  }

  updatePanel();
}

/* ---------- Sidebar hover sync (viz -> sidebar) ---------- */
function syncSidebarHover() {
  let sig = "none";
  if (hoverHit) {
    if (hoverHit.type === "voteStable") {
      sig = "voteStable";
    } else if (hoverHit.type === "indicator") {
      sig = `indicator:${hoverHit.index}`;
    } else if (hoverHit.type === "subcat") {
      sig = `subcat:${hoverHit.dim}||${hoverHit.cat}||${hoverHit.sub}`;
    } else if (hoverHit.type === "cat") {
      sig = `cat:${hoverHit.dim}||${hoverHit.cat}`;
    } else if (hoverHit.type === "dim") {
      sig = `dim:${hoverHit.dim}`;
    }
  }

  if (sig === lastSidebarHoverSig) return;
  lastSidebarHoverSig = sig;

  document
    .querySelectorAll(".hoverSync")
    .forEach((el) => el.classList.remove("hoverSync"));

  const votesHdrWrap = document.getElementById("votesHeaderWrap");
  if (votesHdrWrap) votesHdrWrap.classList.remove("hoverSync");

  if (!hoverHit) return;

  if (hoverHit.type === "voteStable") {
    if (votesHdrWrap) votesHdrWrap.classList.add("hoverSync");
    return;
  }

  if (hoverHit.type === "indicator") {
    const indNameLC = indicatorNodes[hoverHit.index].name;
    const rowEl = document.querySelector(
      `.indItem[data-key="${encodeURIComponent(indNameLC)}"]`
    );
    if (rowEl) rowEl.classList.add("hoverSync");
    return;
  }

  if (hoverHit.type === "subcat") {
    const pillEl = document.querySelector(
      `.pill[data-type="sub"][data-key="${encodeURIComponent(hoverHit.sub)}"]`
    );
    if (pillEl) pillEl.classList.add("hoverSync");
    return;
  }

  if (hoverHit.type === "cat") {
    const pillEl = document.querySelector(
      `.pill[data-type="cat"][data-key="${encodeURIComponent(hoverHit.cat)}"]`
    );
    if (pillEl) pillEl.classList.add("hoverSync");
    return;
  }

  if (hoverHit.type === "dim") {
    const pillEl = document.querySelector(
      `.pill[data-type="dim"][data-key="${encodeURIComponent(hoverHit.dim)}"]`
    );
    if (pillEl) pillEl.classList.add("hoverSync");
    return;
  }
}

/* ---------- Subcategory disambiguation ---------- */
function chooseSubTriple(subNameLC) {
  let options = [];
  for (const [k, v] of subVoteTotals3.entries()) {
    if (v <= 0) continue;
    const [d, c, s] = k.split(KEY_SEP);
    if (s !== subNameLC) continue;
    options.push({ dim: d, cat: c, votes: v });
  }
  if (options.length === 0) return null;

  if (selected.cats.size) {
    const f = options.filter((o) => selected.cats.has(o.cat));
    if (f.length) options = f;
  }
  if (selected.dims.size) {
    const f = options.filter((o) => selected.dims.has(o.dim));
    if (f.length) options = f;
  }

  options.sort((a, b) => b.votes - a.votes);
  return options[0];
}

/* =========================
   SELECTION LOGIC
   ========================= */
function computeSelectionFromHit(hit) {
  const out = {
    type: hit.type,
    indicators: new Set(),
    subcats: new Set(),
    cats: new Set(),
    dims: new Set(),
    subTriples: new Set(),
  };

  const filterSetsByVotes = () => {
    out.subcats = new Set(
      [...out.subcats].filter((s) => hasVotes(subVoteTotals, s))
    );
    out.cats = new Set([...out.cats].filter((s) => hasVotes(catVoteTotals, s)));
    out.dims = new Set([...out.dims].filter((s) => hasVotes(dimVoteTotals, s)));
  };

  // indicator or vote dot
  if (hit.type === "indicator" || hit.type === "vote") {
    const idx = hit.type === "indicator" ? hit.index : hit.indicatorIndex;
    if (idx >= 0 && idx < indicatorNodes.length) {
      out.indicators.add(idx);
      const node = indicatorNodes[idx];
      const meta = indicatorsByKey[node.name] || {};
      const triples = meta.validTriples || [];

      for (const t of triples) {
        out.subcats.add(t.sub);
        out.cats.add(t.cat);
        out.dims.add(t.dim);
        out.subTriples.add(subKey(t.dim, t.cat, t.sub));
      }
    }
    filterSetsByVotes();
    return out;
  }

  // subcategory tile
  if (hit.type === "subcat") {
    const subName = normKey(hit.sub || hit.name);
    let dimUse = normKey(hit.dim || "");
    let catUse = normKey(hit.cat || "");

    if (!dimUse || !catUse) {
      const pick = chooseSubTriple(subName);
      if (pick) {
        dimUse = pick.dim;
        catUse = pick.cat;
      }
    }

    out.subcats.add(subName);
    if (catUse) out.cats.add(catUse);
    if (dimUse) out.dims.add(dimUse);

    if (dimUse && catUse) {
      out.subTriples.add(subKey(dimUse, catUse, subName));
      const k3 = subKey(dimUse, catUse, subName);
      const indKeys = subToIndicators.get(k3);
      if (indKeys) {
        for (const ik of indKeys) {
          const idx = nameToIndicatorIndex.get(ik);
          if (idx != null) out.indicators.add(idx);
        }
      }
    }
    return out;
  }

  // category tile
  if (hit.type === "cat") {
    const catName = normKey(hit.cat || hit.name);
    const dimFound = normKey(hit.dim || parentDimOfCat.get(catName) || "");

    if (dimFound) out.dims.add(dimFound);

    const subs = hierarchyMap.get(dimFound)?.get(catName);
    if (subs) {
      for (const s of subs) {
        if (!hasSubVotes(dimFound, catName, s)) continue;
        out.subcats.add(s);
        out.subTriples.add(subKey(dimFound, catName, s));

        const key = subKey(dimFound, catName, s);
        const indKeys = subToIndicators.get(key);
        if (indKeys) {
          for (const k of indKeys) {
            const idx = nameToIndicatorIndex.get(k);
            if (idx != null) out.indicators.add(idx);
          }
        }
      }
    }

    if (out.subcats.size > 0) out.cats.add(catName);
    filterSetsByVotes();
    return out;
  }

  // dimension tile
  if (hit.type === "dim") {
    const dimName = normKey(hit.dim || hit.name);
    out.dims.add(dimName);

    const catMap = hierarchyMap.get(dimName);
    if (catMap) {
      for (const [cat, subs] of catMap.entries()) {
        let catHasVotes = false;
        for (const s of subs) {
          if (hasSubVotes(dimName, cat, s)) {
            catHasVotes = true;
            break;
          }
        }
        if (!catHasVotes) continue;

        out.cats.add(cat);

        for (const s of subs) {
          if (!hasSubVotes(dimName, cat, s)) continue;
          out.subcats.add(s);
          out.subTriples.add(subKey(dimName, cat, s));

          const key = subKey(dimName, cat, s);
          const indKeys = subToIndicators.get(key);
          if (indKeys) {
            for (const k of indKeys) {
              const idx = nameToIndicatorIndex.get(k);
              if (idx != null) out.indicators.add(idx);
            }
          }
        }
      }
    }

    filterSetsByVotes();
    return out;
  }

  return out;
}

/* =========================
   DRAW HELPERS FOR LAYERS
   ========================= */

/* Layer 0: Votes (dots) */
function drawVotesLayer(layerIndex, votes, halfStack, radius) {
  if (!votes || votes.length === 0) return;

  const y = layerIndex * verticalGap - halfStack;
  const lift = thickness / 2 + LIFT_DOTS;

  const globalAllVotesMode = lastClicked && lastClicked.type === "voteAll";
  const hoverAllVotesFromHeader = hoverVotesHeader === true;

  // If hovering a vote dot in canvas, only that indicator’s votes should glow
  let hoveredIndicatorForVotes = -1;
  if (hoverHit && hoverHit.type === "voteStable") {
    hoveredIndicatorForVotes =
      hoverHit.indicatorIndex != null ? hoverHit.indicatorIndex : -1;
  }

  noStroke();
  for (let i = 0; i < votes.length; i++) {
    const v = votes[i];

    let makeOrange = false;

    if (globalAllVotesMode || hoverAllVotesFromHeader) {
      makeOrange = true; // ALL votes orange
    } else if (hoveredIndicatorForVotes >= 0) {
      // Only votes belonging to the hovered indicator are orange
      if (v.indicatorIndex === hoveredIndicatorForVotes) {
        makeOrange = true;
      }
    }

    if (makeOrange) {
      fill(CLR_ACTIVE[0], CLR_ACTIVE[1], CLR_ACTIVE[2], 210);
    } else {
      fill(CLR_DOTS[0], CLR_DOTS[1], CLR_DOTS[2], 220);
    }

    push();
    translate(v.x, y + lift, v.z);
    cylinder(radius, 1, 16, 1, true, true);
    pop();
  }
}

/* Layer 1: Indicators (circles) */
function drawIndicatorsLayer(layerIndex, nodes, halfStack, indicatorSet) {
  if (!nodes || nodes.length === 0) return;

  const y = layerIndex * verticalGap - halfStack;
  const lift = thickness / 2 + LIFT_DOTS;

  const hoveredIndIdx =
    hoverHit && hoverHit.type === "indicator" ? hoverHit.index : -1;

  noStroke();
  for (const n of nodes) {
    const isSelected = indicatorSet && indicatorSet.has(n.index);
    const isHovered = n.index === hoveredIndIdx;

    if (isHovered) {
      fill(CLR_ACTIVE[0], CLR_ACTIVE[1], CLR_ACTIVE[2], 255);
    } else if (isSelected) {
      fill(CLR_ACTIVE[0], CLR_ACTIVE[1], CLR_ACTIVE[2], 230);
    } else {
      fill(160, 160, 160, 220);
    }

    push();
    translate(n.x, y + lift, n.z);
    cylinder(Math.max(0.5, n.radius), 1, 20, 1, true, true);
    pop();
  }
}

/* Layers 2/3/4: Treemap tiles (subcats / cats / dims) */
function drawTreemapLayer(layerIndex, grid, halfStack) {
  if (!grid || !grid.items || grid.items.length === 0) return;

  const y = layerIndex * verticalGap - halfStack;
  const lift = thickness / 2 + LIFT_TILES;

  stroke(237, 60, 26, 140);
  strokeWeight(0.3);

  const hoveredType =
    hoverHit &&
    (hoverHit.type === "subcat" ||
      hoverHit.type === "cat" ||
      hoverHit.type === "dim")
      ? hoverHit.type
      : null;

  function tileIsHovered(t) {
    if (!hoveredType) return false;

    if (t.sub) {
      return (
        hoveredType === "subcat" &&
        hoverHit.sub === t.sub &&
        hoverHit.cat === t.cat &&
        hoverHit.dim === t.dim
      );
    }

    if (t.cat && !t.sub) {
      return (
        hoveredType === "cat" &&
        hoverHit.cat === t.cat &&
        hoverHit.dim === t.dim
      );
    }

    if (t.dim && !t.cat && !t.sub) {
      return hoveredType === "dim" && hoverHit.dim === t.dim;
    }

    return false;
  }

  function tileInSelectionGlobal(t) {
    if (t.sub) {
      const k = subKey(t.dim, t.cat, t.sub);
      return selected.subTriples && selected.subTriples.has(k);
    }
    if (t.cat && !t.sub) {
      return (
        selected.cats &&
        selected.cats.has(t.cat) &&
        selected.dims &&
        selected.dims.has(t.dim)
      );
    }
    if (t.dim && !t.cat && !t.sub) {
      return selected.dims && selected.dims.has(t.dim);
    }
    return false;
  }

  for (const t of grid.items) {
    const hovered = tileIsHovered(t);
    const inSel = tileInSelectionGlobal(t);

    if (hovered) {
      fill(CLR_ACTIVE[0], CLR_ACTIVE[1], CLR_ACTIVE[2], 255);
    } else if (inSel) {
      fill(CLR_ACTIVE[0], CLR_ACTIVE[1], CLR_ACTIVE[2], 210);
    } else {
      fill(CLR_TILE[0], CLR_TILE[1], CLR_TILE[2], 140);
    }

    push();
    translate(t.x, y + lift, t.z);
    box(Math.max(1, t.width), 1, Math.max(1, t.depth));
    pop();
  }
}

/* =========================
   CONNECTION LINES
   ========================= */
function drawConnectionsForSelection(halfStack) {
  if (!dataReady) return;

  // "All votes" clicked → NO spaghetti
  if (lastClicked && lastClicked.type === "voteAll") return;

  const yVotes = 0 * verticalGap - halfStack + (thickness / 2 + LIFT_DOTS);
  const yInd = 1 * verticalGap - halfStack + (thickness / 2 + LIFT_DOTS);
  const ySub = 2 * verticalGap - halfStack + (thickness / 2 + LIFT_TILES);
  const yCat = 3 * verticalGap - halfStack + (thickness / 2 + LIFT_TILES);
  const yDim = 4 * verticalGap - halfStack + (thickness / 2 + LIFT_TILES);

  let indIdxList = [...selected.indicators];
  if (indIdxList.length === 0 && anchorIndicator != null) {
    indIdxList = [anchorIndicator];
  }
  if (indIdxList.length === 0) return;

  const col = CLR_ACTIVE;
  const A = 128;
  const strokeVotes = () => stroke(col[0], col[1], col[2], A + 40);
  const strokeIndSub = () => stroke(col[0], col[1], col[2], A + 20);
  const strokeSubCat = () => stroke(col[0], col[1], col[2], A);
  const strokeCatDim = () => stroke(col[0], col[1], col[2], A);

  for (const i of indIdxList) {
    const ind = indicatorNodes[i];
    if (!ind) continue;
    const meta = indicatorsByKey[ind.name] || {};
    let triples = meta.validTriples || [];

    if (selected.type === "subcat") {
      if (
        lastClicked?.type === "subcat" &&
        lastClicked.cat &&
        lastClicked.dim
      ) {
        triples = triples.filter(
          (t) =>
            t.sub === lastClicked.key &&
            t.cat === lastClicked.cat &&
            t.dim === lastClicked.dim
        );
      } else {
        triples = triples.filter((t) => selected.subcats.has(t.sub));
      }
    } else if (selected.type === "cat") {
      triples = triples.filter((t) => selected.cats.has(t.cat));
    } else if (selected.type === "dim") {
      triples = triples.filter((t) => selected.dims.has(t.dim));
    }

    // Votes → Indicator
    strokeVotes();
    strokeWeight(1.4);
    let drawn = 0;
    for (const v of voteNodes) {
      if (v.indicatorIndex !== i) continue;
      line(v.x, yVotes, v.z, ind.x, yInd, ind.z);
      if (++drawn >= MAX_VOTE_LINES) break;
    }

    // Indicator → Sub
    strokeIndSub();
    strokeWeight(2.0);
    for (const t of triples) {
      const tileSub = subcatTiles.items.find(
        (it) => it.sub === t.sub && it.cat === t.cat && it.dim === t.dim
      );
      if (tileSub) {
        line(ind.x, yInd, ind.z, tileSub.x, ySub, tileSub.z);
      }
    }

    // Sub → Cat
    strokeSubCat();
    strokeWeight(1.7);
    for (const t of triples) {
      const tileSub = subcatTiles.items.find(
        (it) => it.sub === t.sub && it.cat === t.cat && it.dim === t.dim
      );
      const tileCat = catTiles.items.find(
        (it) => it.cat === t.cat && it.dim === t.dim
      );
      if (tileSub && tileCat) {
        line(tileSub.x, ySub, tileSub.z, tileCat.x, yCat, tileCat.z);
      }
    }

    // Cat → Dim
    strokeCatDim();
    strokeWeight(1.5);
    for (const t of triples) {
      const tileCat = catTiles.items.find(
        (it) => it.cat === t.cat && it.dim === t.dim
      );
      const tileDim = dimTiles.items.find((it) => it.dim === t.dim);
      if (tileCat && tileDim) {
        line(tileCat.x, yCat, tileCat.z, tileDim.x, yDim, tileDim.z);
      }
    }
  }
}

/* =========================
   BILLBOARD TEXT
   ========================= */
function drawBillboardText(txt, x, y, z) {
  push();
  translate(x, y, z);
  rotateY(-isoRotY);
  rotateX(-isoRotX);
  stroke(230);
  strokeWeight(3);
  fill(30);
  text(txt, 0, 0);
  pop();
}

/* =========================
   PANEL / SIDEBAR DOM UPDATE
   ========================= */

function getSelectedLayerNameForBadge() {
  if (lastClicked && lastClicked.type === "voteAll") return "Votes";
  if (selected && selected.type === "vote") return "Votes";
  if (selected && selected.type === "indicator") return "Indicators";
  if (selected && selected.type === "subcat") return "Subcategories";
  if (selected && selected.type === "cat") return "Categories";
  if (selected && selected.type === "dim") return "Dimensions";
  return "None";
}

function syncSelectedLayerBadgeCanvas() {
  const el = document.getElementById("selectedLayerValue");
  if (!el) return;
  el.textContent = getSelectedLayerNameForBadge();
}

function updatePanel() {
  const indListEl = document.getElementById("indicatorList");
  const subPillsEl = document.getElementById("subPills");
  const catPillsEl = document.getElementById("catPills");
  const dimPillsEl = document.getElementById("dimPills");

  if (!indListEl) return;

  const indCountEl = document.getElementById("indCount");
  const subCountEl = document.getElementById("subCount");
  const catCountEl = document.getElementById("catCount");
  const dimCountEl = document.getElementById("dimCount");
  if (indCountEl) indCountEl.textContent = "";
  if (subCountEl) subCountEl.textContent = "";
  if (catCountEl) catCountEl.textContent = "";
  if (dimCountEl) dimCountEl.textContent = "";

  const toPretty = (type, lc) => {
    if (type === "ind") return prettyIndicator[lc] || titleCase(lc);
    if (type === "sub") return prettySub[lc] || titleCase(lc);
    if (type === "cat") return prettyCat[lc] || titleCase(lc);
    if (type === "dim") return prettyDim[lc] || titleCase(lc);
    return lc;
  };

  const fmtVotes = (n) => Math.round(n).toLocaleString();

  const affectedSet = new Set(selected.indicators);

  const allInds = indicatorNodes.map((n) => {
    const lc = n.name;
    const votes = n.votesT | 0;
    let state = "dimmed";

    if (affectedSet.has(n.index)) {
      if (
        lastClicked &&
        lastClicked.type === "indicator" &&
        lastClicked.key === lc
      ) {
        state = "selected";
      } else {
        state = "affected";
      }
    }

    return {
      idx: n.index,
      lc,
      label: toPretty("ind", lc),
      votes,
      state,
    };
  });

  const weightState = (s) => (s === "selected" ? 2 : s === "affected" ? 1 : 0);
  allInds.sort(
    (a, b) =>
      weightState(b.state) - weightState(a.state) ||
      b.votes - a.votes ||
      a.label.localeCompare(b.label)
  );

  const MAX_IND_VISIBLE = 5;
  const visibleInds = SHOW_ALL_INDS
    ? allInds
    : allInds.slice(0, MAX_IND_VISIBLE);

  indListEl.innerHTML = visibleInds
    .map(({ lc, label, votes, state }) => {
      const cls =
        state === "selected"
          ? "indItem ind--selected"
          : state === "affected"
          ? "indItem ind--affected"
          : "indItem ind--dimmed";
      return `
      <li class="${cls}" data-key="${encodeURIComponent(lc)}">
        <span class="indLabel">${escapeHTML(label)}</span>
        <span class="indVotes">${votes}</span>
      </li>`;
    })
    .join("");

  const indToggleBtn = document.getElementById("toggleInd");
  const indToggleText = document.getElementById("indToggleText");
  if (indToggleBtn && indToggleText) {
    indToggleBtn.setAttribute("aria-expanded", String(SHOW_ALL_INDS));
    if (allInds.length <= MAX_IND_VISIBLE) {
      indToggleBtn.style.visibility = "hidden";
    } else {
      indToggleBtn.style.visibility = "visible";
      indToggleText.textContent = SHOW_ALL_INDS ? "show less" : "show all";
    }
  }

  // Build pills
  const allSubs = [...subVoteTotals.keys()].filter(
    (k) => (subVoteTotals.get(k) || 0) > 0
  );
  const allCats = [...catVoteTotals.keys()].filter(
    (k) => (catVoteTotals.get(k) || 0) > 0
  );
  const allDims = [...dimVoteTotals.keys()].filter(
    (k) => (dimVoteTotals.get(k) || 0) > 0
  );

  const subsAll = allSubs.map((lc) => ({
    lc,
    pretty: toPretty("sub", lc),
    active: selected.subcats.has(lc),
    count: subVoteTotalsRaw.get(lc) || 0,
  }));
  const catsAll = allCats.map((lc) => ({
    lc,
    pretty: toPretty("cat", lc),
    active: selected.cats.has(lc),
    count: catVoteTotalsRaw.get(lc) || 0,
  }));
  const dimsAll = allDims.map((lc) => ({
    lc,
    pretty: toPretty("dim", lc),
    active: selected.dims.has(lc),
    count: dimVoteTotalsRaw.get(lc) || 0,
  }));

  const sortPill = (a, b) =>
    b.active - a.active || a.pretty.localeCompare(b.pretty);

  subsAll.sort(sortPill);
  catsAll.sort(sortPill);
  dimsAll.sort(sortPill);

  const subsShown = _limitVisiblePills(subsAll, SHOW_ALL_SUBS, "subPills");
  const catsShown = _limitVisiblePills(catsAll, SHOW_ALL_CATS, "catPills");
  const dimsShown = _limitVisiblePills(dimsAll, SHOW_ALL_DIMS, "dimPills");

  const pillHTML = (type, lc, txt, count, active = false) => {
    return `
    <span class="pill ${active ? "active" : ""}"
          data-type="${type}"
          data-key="${encodeURIComponent(lc)}">
      ${escapeHTML(txt)}
      <span class="pillCount">${fmtVotes(count)}</span>
    </span>`;
  };

  if (subPillsEl) {
    subPillsEl.innerHTML = subsShown.length
      ? subsShown
          .map((o) => pillHTML("sub", o.lc, o.pretty, o.count, o.active))
          .join("")
      : '<span class="muted">—</span>';
  }
  if (catPillsEl) {
    catPillsEl.innerHTML = catsShown.length
      ? catsShown
          .map((o) => pillHTML("cat", o.lc, o.pretty, o.count, o.active))
          .join("")
      : '<span class="muted">—</span>';
  }
  if (dimPillsEl) {
    dimPillsEl.innerHTML = dimsShown.length
      ? dimsShown
          .map((o) => pillHTML("dim", o.lc, o.pretty, o.count, o.active))
          .join("")
      : '<span class="muted">—</span>';
  }

  enforceRowLimit(subPillsEl, SHOW_ALL_SUBS);
  enforceRowLimit(catPillsEl, SHOW_ALL_CATS);
  enforceRowLimit(dimPillsEl, SHOW_ALL_DIMS);

  const subToggleBtn = document.getElementById("toggleSub");
  const catToggleBtn = document.getElementById("toggleCat");
  const dimToggleBtn = document.getElementById("toggleDim");

  const subToggleText = document.getElementById("subToggleText");
  const catToggleText = document.getElementById("catToggleText");
  const dimToggleText = document.getElementById("dimToggleText");

  if (subToggleBtn && subToggleText) {
    subToggleBtn.setAttribute("aria-expanded", String(SHOW_ALL_SUBS));
    const needsToggle = subsAll.length > subsShown.length;
    if (!needsToggle && !SHOW_ALL_SUBS) {
      subToggleBtn.style.visibility = "hidden";
    } else {
      subToggleBtn.style.visibility = "visible";
      subToggleText.textContent = SHOW_ALL_SUBS ? "show less" : "show all";
    }
  }

  if (catToggleBtn && catToggleText) {
    catToggleBtn.setAttribute("aria-expanded", String(SHOW_ALL_CATS));
    const needsToggle = catsAll.length > catsShown.length;
    if (!needsToggle && !SHOW_ALL_CATS) {
      catToggleBtn.style.visibility = "hidden";
    } else {
      catToggleBtn.style.visibility = "visible";
      catToggleText.textContent = SHOW_ALL_CATS ? "show less" : "show all";
    }
  }

  if (dimToggleBtn && dimToggleText) {
    dimToggleBtn.setAttribute("aria-expanded", String(SHOW_ALL_DIMS));
    const needsToggle = dimsAll.length > dimsShown.length;
    if (!needsToggle && !SHOW_ALL_DIMS) {
      dimToggleBtn.style.visibility = "hidden";
    } else {
      dimToggleBtn.style.visibility = "visible";
      dimToggleText.textContent = SHOW_ALL_DIMS ? "show less" : "show all";
    }
  }

  // tint panel section that matches active layer
  const indWrap = document.getElementById("indWrap");
  const subsWrap = document.getElementById("subsWrap");
  const catsWrap = document.getElementById("catsWrap");
  const dimsWrap = document.getElementById("dimsWrap");

  [indWrap, subsWrap, catsWrap, dimsWrap].forEach((el) => {
    if (el) el.classList.remove("hl");
  });

  const selIdx = getSelectedLayerIndex();
  if (selIdx === 1 && indWrap) indWrap.classList.add("hl");
  else if (selIdx === 2 && subsWrap) subsWrap.classList.add("hl");
  else if (selIdx === 3 && catsWrap) catsWrap.classList.add("hl");
  else if (selIdx === 4 && dimsWrap) dimsWrap.classList.add("hl");

  if (lastClicked?.type === "indicator") {
    const el = indListEl.querySelector(
      `.indItem[data-key="${encodeURIComponent(lastClicked.key)}"]`
    );
    if (el && el.scrollIntoView) el.scrollIntoView({ block: "nearest" });
  }

  syncSelectedLayerBadgeCanvas();

  const btn = document.getElementById("votesHeaderBtn");
  if (btn) {
    const isVotesMode =
      (lastClicked && lastClicked.type === "voteAll") ||
      (selected && selected.type === "vote");
    if (isVotesMode) btn.classList.add("active");
    else btn.classList.remove("active");
  }

  const wrap = document.getElementById("votesHeaderWrap");
  if (wrap) {
    const isVotesMode =
      (lastClicked && lastClicked.type === "voteAll") ||
      (selected && selected.type === "vote");
    if (isVotesMode) wrap.classList.add("hlHeader");
    else wrap.classList.remove("hlHeader");
  }
}

/* =========================
   p5 LIFECYCLE: setup/draw/resize/etc
   ========================= */

let wrapObserver = null;

function preload() {
  // intentionally empty, we load CSV in setup via d3
}

function setup() {
  const wrap = document.getElementById("p5-wrap");
  const rect = wrap.getBoundingClientRect();
  W = Math.max(640, Math.floor(rect.width));
  H = Math.max(480, Math.floor(rect.height));

  // watch browser resize
  window.addEventListener("resize", () => {
    resizeForWrap();
    updatePanel();
    if (typeof redraw === "function") redraw();
  });

  // canvas
  const cnv = createCanvas(W, H, WEBGL);
  cnv.parent(wrap);
  Object.assign(cnv.elt.style, {
    position: "absolute",
    inset: "0",
    width: "100%",
    height: "100%",
    display: "block",
  });

  // load CSVs then build data/layout
  Promise.all([d3.csv(CSV_MAIN), d3.csv(CSV_STRUCT)])
    .then(([rowsMain, rowsStruct]) => {
      mainRows = rowsMain;
      hierarchyMap = buildHierarchyMap(rowsStruct);
      buildParentLookups();
      buildContextualIndices(mainRows);

      initFromCSV(mainRows);
      dataReady = true;
      updatePanel();
    })
    .catch((err) => {
      console.error("CSV load failed:", err);
      const el = document.getElementById("indicatorList");
      if (el) {
        el.innerHTML = `
          <li class="indItem">
            <span class="indLabel">CSV load failed.</span>
          </li>`;
      }
    });

  noLights();
  setAttributes("alpha", true);
  setAttributes("depth", true);

  // offscreen picking buffer
  pickGL = createGraphics(W, H, WEBGL);
  pickGL.pixelDensity(1);
  pickGL.setAttributes("alpha", false);
  pickGL.setAttributes("depth", true);
  pickGL.noLights();

  // isometric camera
  isoRotX = -radians(35.264);
  isoRotY = radians(45);

  textFont(
    "system-ui, -apple-system, Segoe UI, Roboto, Ubuntu, Cantarell, 'Helvetica Neue', Arial, 'Noto Sans'"
  );
  textSize(14);
  textAlign(CENTER, CENTER);

  // DOM refs
  const byId = (id) => document.getElementById(id);

  /* CLICK HANDLING IN SIDEBAR */
  const panelEl = document.getElementById("panel");

  panelEl.addEventListener(
    "click",
    (e) => {
      // Indicator row
      const row = e.target.closest(".indItem[data-key]");
      if (row) {
        e.preventDefault();
        const keyLC = decodeURIComponent(row.getAttribute("data-key") || "");
        const idx = nameToIndicatorIndex.get(keyLC);
        if (idx != null) {
          lastClicked = { type: "indicator", key: keyLC };
          anchorIndicator = idx;
          selected = computeSelectionFromHit({ type: "indicator", index: idx });
          updatePanel();
        }
        return;
      }

      // Pill click
      const pill = e.target.closest(".pill[data-type][data-key]");
      if (pill) {
        e.preventDefault();
        const typeRaw = pill.getAttribute("data-type") || "";
        const keyLC = decodeURIComponent(pill.getAttribute("data-key") || "");

        const type =
          typeRaw === "sub"
            ? "subcat"
            : typeRaw === "cat"
            ? "cat"
            : typeRaw === "dim"
            ? "dim"
            : typeRaw;

        let hit = null;
        if (type === "subcat") hit = { type: "subcat", name: keyLC };
        else if (type === "cat") hit = { type: "cat", name: keyLC };
        else if (type === "dim") hit = { type: "dim", name: keyLC };
        if (!hit) return;

        if (type === "subcat") {
          const pick = chooseSubTriple(keyLC);
          if (pick) {
            lastClicked = {
              type: "subcat",
              key: keyLC,
              dim: pick.dim,
              cat: pick.cat,
            };
          } else {
            lastClicked = { type: "subcat", key: keyLC };
          }
        } else if (type === "cat") {
          lastClicked = { type: "cat", key: keyLC, dim: undefined };
        } else if (type === "dim") {
          lastClicked = { type: "dim", key: keyLC };
        }

        selected = computeSelectionFromHit(hit);
        updatePanel();
        return;
      }
    },
    true
  );

  /* SIDEBAR HOVER -> FAKE VIZ HOVER */
  panelEl.addEventListener(
    "mouseover",
    (e) => {
      if (!dataReady) return;

      // hover on indicator row
      const row = e.target.closest(".indItem[data-key]");
      if (row) {
        const keyLC = decodeURIComponent(row.getAttribute("data-key") || "");
        const idx = nameToIndicatorIndex.get(keyLC);
        if (idx != null) {
          sidebarHoverActive = true;
          hoverHit = { type: "indicator", index: idx };
          lastHoverHit = hoverHit;
          syncSidebarHover();
          if (typeof redraw === "function") redraw();
        }
        return;
      }

      // hover on pill
      const pill = e.target.closest(".pill[data-type][data-key]");
      if (pill) {
        const typeRaw = pill.getAttribute("data-type") || "";
        const keyLC = decodeURIComponent(pill.getAttribute("data-key") || "");

        if (typeRaw === "sub") {
          const pick = chooseSubTriple(keyLC);
          if (pick) {
            sidebarHoverActive = true;
            hoverHit = {
              type: "subcat",
              sub: keyLC,
              cat: pick.cat,
              dim: pick.dim,
            };
            lastHoverHit = hoverHit;
            syncSidebarHover();
            if (typeof redraw === "function") redraw();
          }
          return;
        }

        if (typeRaw === "cat") {
          const dimGuess = parentDimOfCat.get(keyLC) || "";
          sidebarHoverActive = true;
          hoverHit = { type: "cat", cat: keyLC, dim: dimGuess };
          lastHoverHit = hoverHit;
          syncSidebarHover();
          if (typeof redraw === "function") redraw();
          return;
        }

        if (typeRaw === "dim") {
          sidebarHoverActive = true;
          hoverHit = { type: "dim", dim: keyLC };
          lastHoverHit = hoverHit;
          syncSidebarHover();
          if (typeof redraw === "function") redraw();
          return;
        }
      }
    },
    true
  );

  panelEl.addEventListener(
    "mouseout",
    (e) => {
      const leftRow = e.target.closest(".indItem[data-key]");
      const leftPill = e.target.closest(".pill[data-type][data-key]");

      if (leftRow || leftPill) {
        sidebarHoverActive = false;

        // recalc hover from canvas if mouse is over canvas
        const canvasEl = document
          .getElementById("p5-wrap")
          ?.querySelector("canvas");
        if (canvasEl) {
          const rect2 = canvasEl.getBoundingClientRect();
          const ev = window.event;
          const insideCanvas =
            ev &&
            ev.clientX >= rect2.left &&
            ev.clientX <= rect2.right &&
            ev.clientY >= rect2.top &&
            ev.clientY <= rect2.bottom;

          if (insideCanvas && dataReady) {
            const rawHit = pickAt(mouseX, mouseY) || null;
            const resolved = resolveStableHover(rawHit, hoverHit);
            hoverHit = resolved || null;
            lastHoverHit = hoverHit;
          } else {
            hoverHit = null;
            lastHoverHit = null;
          }
        } else {
          hoverHit = null;
          lastHoverHit = null;
        }

        syncSidebarHover();
        if (typeof redraw === "function") redraw();
      }
    },
    true
  );

  /* SECTION TOGGLE BUTTONS */
  byId("toggleInd").onclick = () => {
    SHOW_ALL_INDS = !SHOW_ALL_INDS;
    byId("toggleInd").setAttribute("aria-expanded", String(SHOW_ALL_INDS));
    updatePanel();
  };
  byId("toggleSub").onclick = () => {
    SHOW_ALL_SUBS = !SHOW_ALL_SUBS;
    byId("toggleSub").setAttribute("aria-expanded", String(SHOW_ALL_SUBS));
    updatePanel();
  };
  byId("toggleCat").onclick = () => {
    SHOW_ALL_CATS = !SHOW_ALL_CATS;
    byId("toggleCat").setAttribute("aria-expanded", String(SHOW_ALL_CATS));
    updatePanel();
  };
  byId("toggleDim").onclick = () => {
    SHOW_ALL_DIMS = !SHOW_ALL_DIMS;
    byId("toggleDim").setAttribute("aria-expanded", String(SHOW_ALL_DIMS));
    updatePanel();
  };

  // init aria-expanded on load
  byId("toggleInd").setAttribute("aria-expanded", String(SHOW_ALL_INDS));
  byId("toggleSub").setAttribute("aria-expanded", String(SHOW_ALL_SUBS));
  byId("toggleCat").setAttribute("aria-expanded", String(SHOW_ALL_CATS));
  byId("toggleDim").setAttribute("aria-expanded", String(SHOW_ALL_DIMS));

  /* CLEAR SELECTION button */
  byId("clearBtn").onclick = () => {
    clearSelectionAndHeader();
  };

  /* PICKING EVENTS (canvas) */
  cnv.mousePressed(onCanvasPressed);
  cnv.mouseMoved = mouseMoved;
  cnv.mouseOut = mouseExited;

  /* ZOOM BUTTON + WHEEL */
  const zoomBtn = document.getElementById("zoomBtn");
  if (zoomBtn) {
    zoomBtn.onclick = () => {
      zoomed = !zoomed;
      zoomBtn.textContent = zoomed ? "Back to full view" : "Zoom";
      scrollY = 0;
    };
  }

  cnv.elt.addEventListener(
    "wheel",
    (e) => {
      if (zoomed) e.preventDefault();
    },
    { passive: false }
  );

  // Clickable "Votes" header button = all votes highlighted mode
  const votesBtn = document.getElementById("votesHeaderBtn");
  if (votesBtn) {
    votesBtn.onclick = () => {
      selectAllVotes();
    };
  }

  // HOVER on the "Votes ###" header → highlight all votes (temporary)
  // HOVER on the "Votes ###" header → pretend we're hovering all votes
  const votesHeaderWrap = document.getElementById("votesHeaderWrap");
  if (votesHeaderWrap) {
    votesHeaderWrap.addEventListener("mouseenter", () => {
      // turn on "all votes hover" mode
      hoverVotesHeader = true;
      sidebarHoverActive = true;

      // fake a hoverHit so the canvas knows to tint ALL vote dots orange
      hoverHit = { type: "voteStable", indicatorIndex: -1 };
      lastHoverHit = hoverHit;

      // make sure the header gets the orange highlight box
      syncSidebarHover();

      if (typeof redraw === "function") redraw();
    });

    votesHeaderWrap.addEventListener("mouseleave", () => {
      hoverVotesHeader = false;
      sidebarHoverActive = false;

      // when we leave the header, we stop forcing that fake hover
      hoverHit = null;
      lastHoverHit = null;

      // remove orange highlight from header in the sidebar
      syncSidebarHover();

      if (typeof redraw === "function") redraw();
    });
  }

  /* RESIZE OBSERVER */
  wrapObserver = new ResizeObserver(() => resizeForWrap());
  wrapObserver.observe(wrap);
}

function windowResized() {
  resizeForWrap();
}

function resizeForWrap() {
  const wrap = document.getElementById("p5-wrap");
  const rect = wrap.getBoundingClientRect();
  const newW = Math.max(640, Math.floor(rect.width));
  const newH = Math.max(480, Math.floor(rect.height));
  if (newW === W && newH === H) return;

  W = newW;
  H = newH;
  resizeCanvas(W, H);

  pickGL = createGraphics(W, H, WEBGL);
  pickGL.pixelDensity(1);
  pickGL.setAttributes("alpha", false);
  pickGL.setAttributes("depth", true);
  pickGL.noLights();

  updatePanel();
}

/* ---------- Wheel scroll while zoomed ---------- */
function mouseWheel(e) {
  if (!zoomed) return;
  const halfStack = ((LAYERS.length - 1) * verticalGap) / 2;
  scrollY = clamp(scrollY + e.deltaY * SCROLL_PER_WHEEL, -halfStack, halfStack);
  return false;
}

/* ---------- Keyboard shortcuts ---------- */
function keyPressed() {
  if (key === "r" || key === "R") {
    autoRotate = !autoRotate;
    return false;
  }
  if (key === "l" || key === "L") {
    SHOW_LABELS = !SHOW_LABELS;
    return false;
  }
  if (keyCode === ESCAPE) {
    clearSelectionAndHeader();
    return false;
  }
}

/* ---------- DRAW LOOP ---------- */
function draw() {
  background(CLR_BG[0], CLR_BG[1], CLR_BG[2]);

  const viewSizeNow = zoomed ? VIEW_SIZE_ZOOM : VIEW_SIZE_BASE;

  ortho(
    -viewSizeNow / 2,
    viewSizeNow / 2,
    -viewSizeNow / 2,
    viewSizeNow / 2,
    0.01,
    5000
  );

  const aspect = W / H;
  push();
  if (aspect > 1) {
    scale(1 / aspect, 1, 1);
  } else if (aspect < 1) {
    scale(1, aspect, 1);
  }

  rotateX(isoRotX);
  rotateY(isoRotY);
  if (autoRotate) rotateY(frameCount * 0.005);

  if (zoomed) translate(0, -scrollY, 0);

  const halfStack = ((LAYERS.length - 1) * verticalGap) / 2;

  if (SHOW_PLATES) {
    const gl = drawingContext;
    if (gl && gl.depthMask) gl.depthMask(false);
    // draw base plates here if desired
    if (gl && gl.depthMask) gl.depthMask(true);
  }

  if (dataReady) {
    // Layer 0: Votes
    drawVotesLayer(0, voteNodes, halfStack, DOT_RADIUS_VOTES);

    // Layer 1: Indicators
    drawIndicatorsLayer(1, indicatorNodes, halfStack, selected.indicators);

    // Layer 2/3/4: Treemaps
    drawTreemapLayer(2, subcatTiles, halfStack);
    drawTreemapLayer(3, catTiles, halfStack);
    drawTreemapLayer(4, dimTiles, halfStack);

    drawConnectionsForSelection(halfStack);

    const selLayerIdx = getSelectedLayerIndex();
    drawLayerOutline(selLayerIdx, halfStack);
  }

  if (SHOW_LABELS) {
    const edge = Math.max(PLATE_W, PLATE_D) / 2 + 6;
    for (let i = 0; i < LAYERS.length; i++) {
      const y = i * verticalGap - halfStack;
      drawBillboardText(LAYERS[i].name, 0, y - thickness / 2 - 10, edge);
    }
  }

  pop();
}

/* ---------- Mouse hover / exit ---------- */
function mouseMoved() {
  if (!dataReady) return false;

  // Canvas hover always updates hoverHit. If header is hovered (hoverVotesHeader),
  // that state is managed separately. Moving in canvas should drop header-hover
  // unless we are actually on vote dots.
  const rawHit = pickAt(mouseX, mouseY) || null;
  const resolved = resolveStableHover(rawHit, hoverHit);

  hoverHit = resolved || null;
  lastHoverHit = hoverHit;

  if (!(hoverHit && hoverHit.type === "voteStable")) {
    hoverVotesHeader = false;
  }

  // We’re in canvas now, so sidebar is no longer owning the hover visuals
  sidebarHoverActive = false;

  syncSidebarHover();
  return false;
}

function mouseExited() {
  hoverHit = null;
  lastHoverHit = null;
  lastSidebarHoverSig = null;

  document
    .querySelectorAll(".hoverSync")
    .forEach((el) => el.classList.remove("hoverSync"));
  const votesHdrWrap = document.getElementById("votesHeaderWrap");
  if (votesHdrWrap) votesHdrWrap.classList.remove("hoverSync");
  hoverVotesHeader = false;
}

// end sketch.js
